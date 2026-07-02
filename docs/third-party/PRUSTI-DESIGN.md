# Prusti — design choices

An analysis of `third-party/prusti-dev/` (checkout `0d4a8d497`, master):
**Prusti**, ETH Zürich's verifier for Rust built on the **Viper** verification
infrastructure. Prusti is the *oldest* of the Rust verifiers (OOPSLA 2019)
and completes the quadrant our reviews have been circling — four answers to
"what do you do with `&mut` after the borrow checker":

| tool | `&mut` story | backend |
|---|---|---|
| rustc | enforce, then discard | — |
| Verus | linear ghost tokens, first-order heap | in-house SMT encoding |
| Creusot | prophecy pairs, no heap at all | Why3/Coma portfolio |
| **Prusti** | **separation-logic permissions + magic wands** | Viper (Silicon/Carbon) via JVM |

Prusti's founding idea (the "core proof"): **derive the separation-logic
skeleton automatically from Rust's types** — a struct becomes a recursive
Viper predicate over field permissions, borrow ends become permission
returns computed from compiler facts — so that *panic-freedom of well-typed
code verifies with zero annotations*, and user contracts are layered on top
of a memory-safety proof the user never sees. Where Creusot uses the borrow
checker to *escape* separation logic, Prusti uses it to *generate* the
separation logic.

## 1. Pipeline

A rustc plugin (dev-guide `pipeline/`): binary setup (`prusti-rustc` /
`cargo-prusti` / driver) → rustc compilation with two callbacks → encoding →
Viper → report. Notable integration points (`prusti/src/callbacks.rs`):

- like Creusot, it **overrides `mir_borrowck`** to capture
  `BodyWithBorrowckFacts` — but asks for **`PoloniusOutputFacts`** for
  to-be-verified functions (full datalog-style loan facts), stealing
  `mir_promoted` bodies too;
- verification runs `after_analysis`, then stops compilation (unless full
  compilation is requested).

Specs are the third sighting of the now-familiar trick, with its own twist
(`prusti-contracts/prusti-specs/src/rewriter.rs`): each `#[requires]`/
`#[ensures]`/pledge/`#[terminates]` becomes a **synthetic spec function**
(`prusti_pre_item_<fn>_<uuid>`) with the original signature (plus `result`
for postconditions), marked `#[prusti::spec_only]` and cross-referenced by
UUID attributes on the target function; the body is wrapped as
`let _: bool = <expr>;` precisely so rustc's type errors say "expected
`bool`" rather than something confusing. A HIR `SpecCollector` visitor later
reassembles the typed spec map. Specs are therefore fully rustc-typechecked,
like Verus and Creusot — three independent teams converged on "make the host
compiler typecheck the contracts."

## 2. The encoding: types as predicates, values as snapshots

Two parallel encodings of Rust data (dev-guide `encoding/types*.md`):

- **Heap-based**: every variable is a Viper `Ref`; primitives live in value
  fields (`val_int`, …); a struct's type is a **predicate** whose body holds
  permissions to all fields recursively; enums add a discriminant field with
  variant-guarded field permissions; `&mut` is full permission, `&` read
  permission. This is the mutable-state workhorse.
- **Snapshot-based**: each type also gets a Viper **domain** (`Snap$T`) with
  axiomatized constructors — a heap-independent mathematical image of the
  value, used for structural equality (`===`), quantification over
  structures, and pure-function results; `snap$` functions bridge the two,
  and "mirror" domain functions give pure Rust functions lazy axiomatized
  counterparts.

`#[pure]` functions become Viper functions (single expression; loop-less
MIR folded into nested ternaries), callable in specs; non-termination of a
pure function would let you prove `false`, so termination is the user's
obligation. A `purifier` pass additionally turns read-only local refs into
snapshot values to cut permission traffic.

## 3. Fold/unfold: the signature algorithm

Viper predicates are *abstractions*: to touch `x.f.g` you must `unfold` the
predicates from `x` down to the field, and `fold` them back before calling
anything that expects the abstraction. Prusti's core contribution is doing
this **fully automatically** from MIR (`prusti-viper/src/encoder/
foldunfold/`): a symbolic **permission state machine** tracks, per program
point, the set of access and predicate permissions held (`acc`/`pred` maps
with Read/Write amounts, moved-places set, framing stack); each statement's
**required footprint** is computed (`requirements.rs`, `footprint.rs`), and
a solver inserts the fold/unfold sequence to transform the current state
into the required one — including reconciliation at CFG join points and
"unfolding-in" expressions inside `old()` contexts. The dropped-permission
log and read-duplication handling for borrows make the algorithm
intricately stateful; the state consistency invariants (`state.rs`) read
like a small verification project of their own. This is the cost side of
predicate-based memory abstraction, and the strongest argument the survey
offers *against* choosing raw separation logic as an encoding target when a
type discipline could carry the information instead.

## 4. Borrows: Polonius facts, a reborrowing DAG, and magic wands

Prusti consumes the borrow checker at maximum fidelity
(`prusti-interface/src/environment/polonius_info.rs`): Polonius loan facts
are assembled into a **reborrowing DAG** per function — which loans reborrow
which, where each expires (including "zombie" loans for moved references).
The encoder then emits, at each expiry point, the permission bookkeeping
that hands borrowed permissions back up the DAG
(`foldunfold/process_expire_borrows.rs`).

For borrows crossing function boundaries, Prusti's answer to "what can the
caller assume when the returned `&mut` dies" is the **pledge**:
`#[after_expiry(condition)]` and `#[assert_on_expiry(cond, pledge)]`,
encoded as Viper **magic wands** (`current-obligations --* post-expiry
guarantee`) applied at expiry. `before_expiry(*result)` refers to the value
the caller left in the reference. Compare Creusot: `after_expiry(P(^result))`
and prophecy resolution are answering the *same* specification need —
pledges are the separation-logic spelling, prophecies the functional
spelling, of "the final value of a borrow." (The classic example — specifying
`Vec::index_mut`/`peek_mut` so mutations through the returned reference
propagate to the vector's model — appears in the user guide tour.)

Loop encoding computes permission invariants **heuristically** (paths
accessed in the body ∩ initialized before the loop, minimized), backed by a
definitely-initialized analysis; functional loop invariants are user-written
`body_invariant!(…)` statements *inside* the body (placeable after
side-effecting conditions — a nice ergonomic wrinkle vs. header-attached
invariants). The standalone `analysis/` crate provides the dataflow
substrate: a generic fixpoint engine (join/widen lattice trait) with
domains for definitely-initialized, maybe-borrowed, definitely-accessible,
and framing — the same analyses every tool in this survey ends up needing.

## 5. Spec-language surface

Beyond pre/post/pledges: `predicate!{}` (full quantifier syntax, usable
only in specs), `#[extern_spec]` (implicitly-trusted contracts for foreign
code, resolved by writing a stub whose body names the target), **type
models** `#[model]` (ghost model fields for types whose privates are
inaccessible — e.g. modeling `std::slice::Iter` by position/length; with a
documented unsoundness caveat for field-less types), **type-conditional
spec refinement** `#[refine_spec(where T: Eq, [...])]` (behavioral
subtyping keyed on trait bounds — a feature the others lack), ghost types
(`Int`, `Seq`, `Map`, `Ghost<T>`), `prusti_assert!`/`assume!`/`refute!`,
`#[terminates(Int-expr)]` for total-correctness opt-in (default is partial
correctness), and model-derived **counterexamples** surfaced from Silicon.
Closures and specification entailments exist as designed-but-unfinished
features, marked "NOT YET SUPPORTED" in the user guide — the honest frontier
of the prototype. Unsupported constructs degrade via **stub encoders**
(clearly-marked verification gaps rather than crashes).

## 6. Infrastructure

- **Layered, code-generated VIR** (`vir/`, `vir-gen/`): `vir::high` (close
  to MIR, typed, lifetimes explicit) → `typed` (type reduction) → `middle`
  (fold/unfold made explicit) → `low` ("effectively Viper"), with a custom
  generator producing constructors, four visitor/folder variants, and
  inter-layer lowering boilerplate from declarative AST definitions. Two
  encoders coexist: the legacy `polymorphic` VIR path (default) and the
  "new encoder" through the layered VIR (`unsafe_core_proof`, powering
  counterexamples) — a rewrite that visibly never fully landed.
- **Viper over JNI** (`viper/`, `viper-sys/`, `jni-gen/`): an in-process
  JVM, AST built object-by-object through generated JNI wrappers (chosen
  over textual `.vpr` emission for AST-level API and warm-JVM performance),
  backend selectable between **Silicon** (symbolic execution, default) and
  **Carbon** (VC generation). **prusti-server** keeps the JVM warm across
  runs and adds a persistent hash-keyed verification cache — the same
  server/caching instinct as Verus's spinoff provers and Creusot's
  why3find sessions, driven by the JVM's startup cost.
- **`smt-log-analyzer`**: parses Z3 trace logs to count and bound quantifier
  instantiations per quantifier, detect matching loops, and trace triggers —
  the same "E-matching is the scarce resource" tooling posture as Verus's
  profiler, retrofitted onto Viper's two-solver stack.
- Config is a 100+-flag layered system (defaults → env → `Prusti.toml` →
  CLI); tests are compiletest-based, ~520 files across pass/fail/ui with
  four verification modes (incl. overflow on/off and core-proof-only).

TCB: rustc, the spec rewriting + encoder, Viper (Scala) + its solvers
(Z3, and Boogie/Z3 under Carbon), the JVM, every `#[trusted]`/
`#[extern_spec]`/`#[model]`, and the pure-function termination obligations
left to the user. No foundational proof of the encoding exists (unlike
Creusot's RustHornBelt paper backing); soundness rests on the Viper
methodology literature.

## 7. Takeaways

1. **The quadrant is now complete**, and the pattern is stark: all four
   Rust tools *trust the borrow checker*; they differ only in what they
   cash it in for. Permissions-with-wands (Prusti) buys the most faithful
   memory model and zero-annotation panic-freedom, at the price of the
   fold/unfold machine and a heavyweight backend. Prophecies (Creusot) and
   linear tokens (Verus) both dodge that machinery. For LowIR's
   borrow-discipline plans, Prusti is the "what it costs to keep separation
   logic around" data point — our MEMORY-BORROWS choice to keep disjointness
   at *interfaces only* looks even better against it.
2. **Pledges ≈ prophecies**, spelled differently. Any borrow-aware call
   spec language — ours included — needs a construct for "what holds of the
   borrowed-out region when it comes back"; seeing it emerge independently
   as magic wands and as `^result` is strong evidence it belongs in our
   frame-based call specs.
3. **The core-proof idea transfers**: generate the memory-safety skeleton
   of a proof from the type/ownership discipline, and let users only ever
   write functional specs. That's the UX target a LowIR borrow checker
   should enable — the checker's output *is* the core proof.
4. **Fold/unfold automation is a warning label.** Predicate abstraction
   forces a global, stateful, heuristic permission solver into the trusted
   pipeline. If an encoding needs this, the abstraction is probably at the
   wrong level — the same lesson as Verus's "linearity instead of SMT-side
   SL" and Radix's proof-shaped minimalism.
5. **Backend-reuse economics**: Prusti (Viper/JVM/JNI) vs Creusot
   (Why3/text/why3find) vs Verus (in-house) is a clean three-way experiment
   in IVL reuse. The JNI bridge, error back-translation, name mangling, and
   server/cache layers are the hidden invoice of "just target an existing
   IVL" — worth remembering whenever we're tempted by an off-the-shelf VC
   backend for LowIR.
6. Small gems worth stealing regardless: the `let _: bool = expr` trick for
   host-typechecked specs with good errors; type-conditional spec
   refinement; body-internal `body_invariant!`; and stub-encoder graceful
   degradation with explicit verification gaps.
