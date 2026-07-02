# rustc — IR ladder & borrow checker design

An analysis of `third-party/rust/` (rustc, 2026 master, checkout `2371d697`),
scoped to the two questions that matter for giving a systems language (our
LowIR line, Pancake-style) a borrow checker: **what each intermediate stage
looks like**, and **how borrow-checking information propagates through the
pipeline** — downward into the checker, upward across function boundaries,
and (crucially) where it is deliberately destroyed. Sources: the compiler
crates (`rustc_borrowck`, `rustc_mir_build`, `rustc_mir_transform`,
`rustc_mir_dataflow`, `rustc_middle`) and the in-tree rustc-dev-guide
(`src/doc/rustc-dev-guide/src/borrow-check/`).

The single most important architectural fact, stated up front: **the borrow
checker is a pure, per-function analysis over MIR whose results almost
nothing downstream consumes.** Lifetimes are not "propagated down" — they are
*reconstructed from scratch* at the MIR level, checked, and then erased.
What flows out of borrowck is: pass/fail, inferred hidden types for
`impl Trait`, and residual region constraints promoted to enclosing
functions. Aliasing guarantees used by optimizations come from the *types*
(whose invariants borrowck enforced), never from borrowck's data structures.

## 1. The IR ladder

| IR | types | lifetimes | places | notes |
|---|---|---|---|---|
| **AST** (`rustc_ast`) | syntactic only | names only | — | surface tree, pre-expansion |
| **HIR** (`rustc_hir`) | in side tables | names + elision info | — | desugared (for→loop+match, async→coroutine), incremental-friendly out-of-band storage |
| **THIR** (`rustc_middle::thir`) | inline on every node | none persisted | in patterns | ephemeral, per-body; coercions/autoref explicit; unsafety checked here |
| **MIR Built/Analysis** | inline, `LocalDecl::ty` | fresh `ReVar` (borrowck) | `Place = Local + projections` | CFG; carries borrowck-only constructs |
| **MIR Runtime** | inline | `ReErased` | same | borrowck artifacts deleted; drops elaborated |
| **codegen** | monomorphized | none | byte offsets | `noalias` from types, not borrowck |

Two gradients run down this ladder. *Type information* moves from
side-tables (HIR: `TypeckResults` maps `HirId → Ty`, adjustments, closure
min-captures) to inline (THIR/MIR: every expression/local carries its type).
*Lifetime information* goes from names (AST/HIR) to inference variables
(borrowck-phase MIR) to erased (everything after). HIR type checking runs
region inference internally but **does not persist regions** — the dev-guide
and `typeck_results.rs` are explicit that the table "is not used in codegen
(since regions are erased there)".

MIR itself (`rustc_middle/src/mir/syntax.rs`) is the fully-explicit core:
locals (`_0` = return place), places (base local + projection chain: deref,
field, index, downcast), rvalues (non-nested), statements, and terminators
forming a CFG of basic blocks. It has a **phase/dialect system** (`MirPhase`:
`Built → Analysis(Initial|PostCleanup) → Runtime(Initial|PostCleanup|
Optimized)`) where each phase adds or removes legal constructs — statements
are documented as "disallowed after drop elaboration" etc. This is an IR
*dialect discipline*: one datatype, phase-indexed invariants, enforced by the
MIR validator.

## 2. What flows *into* borrowck (the downward path)

Because HIR typeck throws region inference away, the pipeline must carry
down everything borrowck will need to redo the job at MIR level. Four
channels:

1. **Types themselves** — THIR/MIR types are fully explicit (with regions
   present syntactically but untrusted).
2. **User intent annotations.** Erasing and re-inferring loses what the user
   *wrote* (`let y: &'static u32 = x` must not re-infer a shorter region).
   So typeck saves `CanonicalUserTypeAnnotations` (explicit ascriptions and
   explicit generic args, canonicalized), and MIR building plants
   **`AscribeUserType(place, ty, variance)`** statements that re-impose them
   as subtyping/equality constraints inside borrowck. After borrowck they
   are deleted and `body.user_type_annotations` is cleared.
3. **Borrowck-only MIR constructs**, inserted by MIR building purely to make
   the analysis precise, with no runtime semantics:
   - `FakeRead(cause, place)` — pretend-reads for match scrutinees, `let`
     bindings, guard bindings, index expressions;
   - `PlaceMention` — `let _ = place;` mentions;
   - **fake borrows** (`BorrowKind::Fake`) — protect match scrutinees from
     mutation by guards;
   - **`FalseEdge { real_target, imaginary_target }`** and `FalseUnwind` —
     terminators whose extra edges only borrowck follows, making the CFG
     *pessimistic* so that region inference doesn't exploit match-lowering
     shortcuts;
   - two-phase borrow flags (`MutBorrowKind::TwoPhaseBorrow`), set from
     typeck's autoref decisions, giving `vec.push(vec.len())` a
     reservation/activation split.
4. **Closure capture analysis** (`rustc_hir_typeck/upvar.rs`): min-capture
   sets (which *paths* are captured, by ref/mut/move) computed at HIR typeck
   and used both to build the closure's MIR and to seed borrowck's view of
   upvars (plus THIR-level `fake_reads` for captured places).

The pattern: **the source of truth for borrow checking is the MIR plus a
small set of deliberately planted analysis hints** — not a lifetime-annotated
AST handed down from the front end.

## 3. Inside `rustc_borrowck`: NLL

Entry: the `mir_borrowck(LocalDefId)` query, consuming `mir_promoted` (the
pre-optimization MIR). In this 2026 master the query runs from a
**root context** (`BorrowCheckRootCtxt`) that borrow-checks a typeck root
together with all its nested closures/coroutines, and returns only
`Result<&FxIndexMap<LocalDefId, DefinitionSiteHiddenType>, ErrorGuaranteed>`
— hidden types for `impl Trait`, or an error taint. Everything else is
internal. The phases (dev-guide `borrow-check.md` + code):

1. **Renumber** (`renumber.rs`): clone the MIR and replace *every* region in
   it with a fresh NLL inference variable — regions from HIR typeck are not
   trusted, full stop.
2. **Universal regions** (`universal_regions.rs`): the free regions of the
   *signature* (plus `'static`, plus a synthetic function-body region) become
   "universally quantified" variables; for closures, regions captured from
   the parent enter as extra universals. The signature is the entire
   inter-function interface.
3. **MIR type-check** (`type_check/`): a full re-typecheck of the MIR that
   *generates* outlives constraints (`'a: 'b`), liveness constraints
   (region `R` live at point `P`), and type tests; `AscribeUserType`
   re-injects user intent here.
4. **Liveness** (`type_check/liveness/`): use-liveness and **drop-liveness**
   separately — a dropped value only requires the regions `dropck_outlives`
   says its destructor can observe (`#[may_dangle]` opts out).
5. **Region inference** (`region_infer/`): region values are *sets of
   elements* — CFG points, `end('a)` markers for universal regions,
   placeholders. Constraints are solved by SCC-condensing the outlives graph
   and propagating value sets over the resulting DAG in one topological
   pass. Higher-ranked types (`for<'x>`) are handled with **placeholders and
   universes** (a tree of name scopes; leaking a placeholder into a region
   that can't "see" its universe is an error). **Member constraints**
   (`'m ∈ {'c₁…'cₙ}`) handle `impl Trait` lifetime capture, picking minimal
   choices. Errors = a universal region's value grew beyond what the
   signature declares.
6. **Loans + dataflow**: `BorrowSet` indexes every `Rvalue::Ref` as a loan
   (`BorrowData`: reserve location, activation location, kind, region,
   place); the `Borrows` gen/kill dataflow computes loans-in-scope per
   point (a loan dies when its region is no longer live); `MoveData` builds
   the **move-path tree** (places at field granularity, parent/child
   indexed) feeding `MaybeInitializedPlaces`/`EverInitializedPlaces`.
7. **The final walk**: a results-visitor traverses every statement checking
   each access against loans in scope (`places_conflict.rs` — projection-by-
   projection disjointness with an explicit `Overlap`-monoid design and a
   conservativeness bias per query) and against initialization state
   (use-after-move, partial moves). Two-phase borrows act as shared between
   reservation and activation, mutable after.

**Polonius** (in-tree next-gen, `-Zpolonius=next`): reformulates the loan
analysis as *reachability in a localized constraint graph* — typeck
constraints let loans flow between regions at a point; liveness lets them
flow between points; variance decides edge direction. Same outputs, more
precision (conditional-flow cases NLL rejects), same architecture position.

Design posture worth copying: **soundness and diagnostics are separated** —
the solver is the checker; error *explanation* is a best-effort layer with
its own buffered machinery, and `tainted_by_errors` gates downstream passes
instead of aborting.

## 4. What flows *out* of borrowck

- **Upward (the real propagation):** a closure's unresolvable constraints —
  "region `'1` in my type must outlive `'2`" — cannot be checked locally,
  so they are packaged as `ClosureRegionRequirements` (subjects are types or
  region vids numbered by position in the closure's type) and **re-asserted
  in the parent's** region inference, transitively to the outermost
  function. In this master the propagation happens inside the shared
  `BorrowCheckRootCtxt` (nested bodies checked before parents, requirements
  applied modulo opaques). This is the one place borrowck information
  genuinely travels between bodies — and the interface is still, in essence,
  "a signature plus residual constraints."
- **Sideways:** hidden types for opaque types (`impl Trait`). Only borrowck
  can infer them, because *which region* the hidden type captures is a
  region-inference question (member constraints). This is the query's actual
  return value, consumed by `type_of` on the opaque.
- **Downward: almost nothing, by design.** The single consumption point is
  the `mir_drops_elaborated_and_const_checked` query, which forces
  `mir_borrowck(typeck_root)` and copies the error taint into the body.
  Then, immediately:
  - **`CleanupPostBorrowck`** deletes every analysis-only artifact:
    `FakeRead`, `AscribeUserType`, fake borrows, `PlaceMention`,
    `FalseEdge`/`FalseUnwind` (rewritten to `Goto`), and clears user type
    annotations;
  - **`PostAnalysisNormalize`** erases regions (`ReErased` everywhere) and
    removes `OpaqueCast` projections — from here on "lifetimes do not affect
    semantics" is an invariant, and Runtime-phase MIR types are
    region-free;
  - **drop elaboration** re-runs the *same* `MoveData` +
    `MaybeInitializedPlaces` dataflow (shared `rustc_mir_dataflow`
    framework: an `Analysis` trait over lattice domains, gen/kill, forward/
    backward, fixpoint cursors) to turn maybe-uninitialized `Drop`
    terminators into drop flags and unconditional drops — a semantic
    lowering that *assumes* move checking already passed;
  - the **coroutine transform** uses liveness/storage/borrowed-locals
    dataflow to decide which locals live across `yield` and lays out the
    state machine — relying on borrowck's guarantee that (for movable
    coroutines) no borrows cross suspension points.
  - At **codegen**, `noalias`/`dereferenceable` parameter attributes are
    derived from the monomorphized, region-erased *types* (`&mut T` ⇒
    noalias): the optimizer consumes type-system invariants that borrowck
    *enforced*, not data it *produced*. (`Retag` statements for the
    Stacked/Tree-Borrows aliasing model exist only under Miri flags.)

The query system makes all of this per-`DefId`, memoized, and
red-green-incremental — borrow checking one function never forces
re-checking another unless its signature (or the closure-requirements chain)
changed.

## 5. Takeaways for a borrow checker over LowIR

Framed against our own stack (flat-memory LowIR, borrows at call boundaries
per [MEMORY-BORROWS.md](../MEMORY-BORROWS.md)):

1. **Check on the lowest IR that still knows places.** rustc moved borrow
   checking from HIR-ish lexical scopes to MIR and got NLL almost for free:
   regions become sets of CFG points, and precision falls out of the CFG.
   The dev-guide's phrasing — "the MIR is *far* less complex than the HIR;
   the radical desugaring helps prevent bugs" — is a direct argument for
   checking at LowIR level (structured IL over places), not at any C-like
   surface we might grow.
2. **Reconstruct, don't propagate, inference.** The only lifetime facts that
   cross into the checker are the *signature* (universal regions) and
   *explicit user ascriptions*; everything else is renumbered fresh and
   re-derived by a local type-check of the IR. That keeps the front end
   honest (no trusted inference state travels) and the checker's soundness
   argument self-contained — exactly the property a verified checker wants,
   since the thing to verify is then "MIR typeck + constraint solving," not
   a pipeline of handoffs.
3. **Analysis-only instructions + a phase discipline are cheap and
   powerful.** `FakeRead`/`FalseEdge`/`AscribeUserType` planted at build
   time, phase-indexed validity (`MirPhase`), and a cleanup pass that
   deletes them — a pattern our IL can adopt wholesale (we already have the
   pass/dialect instinct from LOWIR-DESIGN; borrow hints would be one more
   dialect).
4. **Make the checker a pure gate.** Nothing downstream should read the
   checker's data structures; post-check lowering (our drop/free insertion,
   any aliasing-based optimization) should rely on *type-level* invariants
   the checker enforced. rustc even re-runs the same dataflow rather than
   share borrowck's results — recomputation over coupling.
5. **The function boundary is the interface; closures show the escape
   hatch.** Signature-only modularity plus "promote residual constraints to
   the caller" (`ClosureRegionRequirements`) is the complete answer to
   nested/higher-order code. For LowIR (no closures, no function pointers —
   Pancake-like) the signature-only half suffices, which removes most of
   rustc's hard parts: no universes/placeholders (no HRTBs), no member
   constraints (no `impl Trait`), no two-phase borrows (no autoref).
6. **The reusable kernel is small.** Strip rustc's borrowck to what a
   LowIR-scale language needs and it is: a move-path tree over places,
   gen/kill init/liveness dataflow, loans indexed by location with a
   region-liveness kill rule, a projection-wise place-conflict oracle, and
   an SCC outlives solver. Each piece is independently verifiable — and the
   Polonius reformulation (loan reachability over a localized constraint
   graph) may actually be the *cleaner* target for a formal treatment,
   since it is one graph-reachability problem instead of a solver plus a
   scope dataflow.
7. **Two liveness notions matter.** Use-live vs drop-live (`dropck`) is the
   detail everyone forgets; any language where destructors/frees observe
   pointers needs the distinction (our free/drop lowering would too).
