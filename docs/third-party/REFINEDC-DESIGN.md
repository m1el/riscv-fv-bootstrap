# RefinedC — design choices

An analysis of `third-party/refinedC/` (checkout `9ebb2cd`): **RefinedC**
(MPI-SWS, PLDI 2021), a *foundational and automated* verification framework
for idiomatic C. It occupies a corner none of our previous reviews reached:
Verus/Creusot/Prusti automate but bottom out in trusted SMT encodings;
CompCert/CakeML/bedrock2 are foundational but (except LiveVerif) not
automated for user programs. RefinedC is both: every verification produces a
genuine Coq/Iris proof against an operational C semantics, and the proofs
are found by a *deterministic logic-programming engine* rather than written
by hand. It is also the closest published relative of this repo's
libc-formalization direction ([LIBC-FORMALIZE.md](../LIBC-FORMALIZE.md),
[MEMORY-BORROWS.md](../MEMORY-BORROWS.md)) — a C semantics, an ownership
discipline, and automation, all in one logic.

The architecture is three strictly-layered Coq components plus an OCaml
frontend, with the dependency discipline stated as an invariant in
ARCHITECTURE.md:

```
theories/caesium   C semantics + Iris instantiation   (depends on nothing above)
theories/lithium   proof-search engine                (depends only on lang/base)
theories/typing    the refinement/ownership type system (depends on both)
frontend/          OCaml: C → Caesium + specs + proof scripts
```

## 1. Caesium: the C semantics

A small-step, Iris-instantiated (`EctxiLanguage`) operational semantics for
a C fragment, notable for taking **pointer provenance seriously**:

- **Memory** is a byte heap `gmap addr heap_cell`, each cell carrying an
  allocation id, a data-race lock state, and an `mbyte` ∈ {concrete byte
  with optional provenance, **pointer fragment** (`MPtrFrag l n` — byte n of
  a pointer), poison}. Values are byte lists; a separate allocation table
  tracks start/length/liveness/kind (heap, stack, global) per allocation id.
- **Pointers** are `loc = prov × addr` with `prov ∈ {Null, Alloc (option
  id), FnPtr}` — and the semantics implements the **PNVI/VIP** treatment of
  integer–pointer casts from the Cerberus line of work: casting an integer
  to a pointer reconstructs provenance from the bytes (`mem_cast` is
  literally the VIP paper's `abst`), and a dedicated `CopyAllocId` operation
  grafts one value's address onto another's provenance. There are even test
  examples (`intptr.c`, `tagged_ptr.c`) exercising tagged-pointer idioms.
  This is the reference answer to "what do int↔ptr casts mean" — CompCert,
  by contrast, leaves them essentially undefined.
- **UB is stuckness**; the adequacy theorem turns "well-typed" into "never
  stuck". Allocation failure is deliberately *not* UB (it demonically
  loops), address 0 and the last byte are reserved (NULL, one-past
  pointers).
- **Functions are CFGs** (`gmap label stmt`, goto/switch) — same shape as
  our LowIR — with expressions evaluated by nondeterministic contextual
  stepping; calls allocate stack blocks and substitute locations for
  variables. Concurrency exists at the primitive level only (CAS, plus
  per-byte lock states that make data races UB); alignment enforcement is a
  single build-time config knob (`coq-caesium-config-no-align`).
- Bit-level reasoning is first-class: a bitfield combinator library
  (`bf_slice`/`bf_update`) plus the `bitblast` tactic over stdpp-bitvector.

## 2. The type system: types are Iris predicates, refinements are values

A **semantic type** is a record of Iris predicates: `ty_own β l` (a
location's ownership at mode β) and `ty_own_val v` (a value's typing), plus
operational compatibility data (layouts, memcast behavior) and a **sharing
law** `ty_own Own l ={↑shrN}=∗ ty_own Shr l`. Two ownership modes exist:
`Own` (exclusive; plain points-to) and `Shr` (persistent read-sharing,
implemented as one Iris invariant *per byte* — fine-grained enough that any
type can be shared without a fractional-permission accounting layer).

**Refinements** ride on the `x @ ty` pattern: an `rtype` is a family of
types indexed by a mathematical value — `n @ int i32` ("this i32 *is* n"),
`p @ &own ty` ("this pointer points to p"), a struct refined by a tuple, a
tagged union refined by a Coq inductive (`rc::tagged_union`). The
combinator library covers structs (with explicit padding fields), arrays,
active-union/variant types, `uninit`, singleton value types, **existential
types** (`∃ₜ x. ty x`), **constrained types** (`ty & P`), and — elegantly —
**recursive types as an existential over syntactic approximations**
(`type_fixpoint T x := ∃ ty, ⌜∀ x, ty x ⊑ T ty x⌝ ∗ ty x`), avoiding
guarded recursion in user-facing types. Locks get their own type whose
`Shr` mode wraps the payload in an Iris invariant with an exclusive token.

Function specs quantify refinements universally and existentially:

```
fn(∀ x : A; ty₁, …, tyₙ; Pre) → ∃ y : B, ty_ret; Post
```

**Typing rules are Lithium programs.** Every judgment
(`typed_val_expr`, `typed_place`, `typed_stmt`, `typed_read_end`, …,
`subsume`) is defined so that its proof obligations are goals in Lithium's
grammar, and every typing rule is a *proven-sound lemma* registered as a
typeclass instance (`Definition …_inst := [instance lemma]`). Extending the
type system — the README's headline claim — means proving a new lemma
against the semantic model and registering it; there is no trusted rule
base. The escape hatch in the other direction is that judgments unfold to
raw Iris, so a stuck proof can always be finished in the Iris Proof Mode.
Soundness is one Iris-adequacy corollary (`adequacy.v`): if globals are
initialized and every `main` is well-typed, no thread ever reaches a stuck
(UB) state.

## 3. Lithium: separation logic programming without backtracking

The automation engine is the most transferable artifact. Lithium interprets
goals drawn from a restricted grammar — `∀`, `∃`, `P ∗ T` ("exhale"),
`P -∗ T` ("inhale"), case-splits, `find_in_context`, `subsume`, plus an
escape into arbitrary tactics — with one non-negotiable design constraint:
**determinism, no backtracking**. The interpreter is a plain-Ltac `first
[...]`-ordered step relation (`liStep`); each step either fires a unique
applicable rule or leaves a **stuck goal that is itself the error message**
(readable via a syntax back-translation). The design dividends: predictable
performance, debuggable failures, and extendability without search blowup.

Supporting machinery, all built for that constraint:

- **Extension points are typeclasses**: `FindInContext` (locate a matching
  hypothesis by pattern, priority-ordered), `SimplifyHyp`/`SimplifyGoal`
  (priority-indexed rewriting), `Subsume`/`RelatedTo` (subtyping with
  existential instantiation), `CanSolve` (pure solvers — `lia`, `bitblast` —
  behind a hook).
- **Evar discipline instead of higher-order unification**: existentials are
  managed through linear products (`li_prod`) and instantiated only by
  syntactic unification against a *protected*, opaque hint database;
  uninstantiated evars are re-generalized into fresh `∃`s rather than left
  to Coq's unifier.
- **Side conditions are shelved**, not solved inline (`SHELVED_SIDECOND`):
  the separation-logic skeleton completes first, then pure residue is
  presented to solvers/user — precisely the "leave (pure) side-conditions
  for the user" workflow from the README.
- Performance is engineered at the Ltac level: keyed unification,
  `notypeclasses refine`, proof-state reduction caching, early branch
  pruning ("don't normalize twice"), `simpl never` on arithmetic.

## 4. The frontend and the annotation language

An OCaml frontend built on **Cerberus** (pinned commit) — Cerberus parses
and *elaborates* C to its typed AIL form; RefinedC translates AIL into
three generated Coq artifacts per `.c` file: the **Caesium deep embedding**,
the **spec file**, and **one proof file per function** (a Lithium proof
script), regenerated by `refinedc check` with stale proof files deleted.
Per-function proof files make checking incremental and parallel, and keep
generated and hand-written Coq (side-condition lemmas) cleanly separated.

Annotations are C2X attributes `[[rc::…]]` plus a few magic comments and
macros (`include/refinedc.h`). The vocabulary is a compact spec language:
`parameters`/`args`/`returns`/`requires`/`ensures`/`exists` on functions;
`refined_by`/`field`/`constraints`/`typedef`/`tagged_union` on structs
(struct types become refinement-indexed named types); `inv_vars`/
`constraints`/`exists` on loops (loop invariants are *type contexts*, not
formulas — the loop's variables are given types); quoted Coq (`{…}`) and
Iris (`[…]`) escape everywhere. Crucially there is a **graceful-degradation
ladder** per function: automatic proof → `rc::lemmas` (hint lemmas for side
conditions) → `rc::tactics` (inline Ltac) → `rc::manual_proof` (hand-written
theorem) → `rc::trust_me` (spec assumed) → `rc::skip` (invisible) — a
designed spectrum from fully verified to trusted, per function.

Case studies: ~29 `examples/` programs (memory pools and allocators,
queues, B-trees, binary/quick sort, spinlocks and latches, `container_of`,
tagged pointers/integer-pointer provenance), a 13-step tutorial, and
`linux/` — real (GPL) kernel-derived code: pKVM's early allocator, page
allocator (buddy find), page-table walker, spinlock. Honest limitation
list from the code: no floats, no string/char literals, no function
pointers in the type system, no general atomics (CAS only, SC), bitfields
and VLAs unsupported, nested assignments rejected, and every non-trivial
loop needs annotations.

## 5. Trust story

Foundational core: the typing rules, the automation's every step, and the
final theorem are all checked by Coq against Caesium + Iris — no SMT solver
or IVL in the TCB. What *is* trusted: Coq itself; **the OCaml frontend's
C→Caesium translation** (the one real gap — the deep embedding is trusted
to mean the same as the C source, mitigated by Cerberus's pedigree as a C
semantics elaborator but not proved); Cerberus's parsing/elaboration; and
every `trust_me`/`skip`/`manual_proof`-imported assumption. Caesium itself
is a *model* of C rather than ISO C — its PNVI/VIP choices are argued, not
normative.

## 6. Takeaways

For our tower, RefinedC is less a comparison point than a blueprint:

1. **The three-layer architecture with a dependency invariant** — semantics
   / automation / type system, none knowing about the layers above — is
   exactly the shape our libc effort should take: LowIR+memory model ↔
   Caesium; the `Slice`/`Borrow`/`Wf` layer ↔ `typing`; our tactic kit
   (`clia`, autorewrite discipline) ↔ Lithium. The invariant is what keeps
   the semantics reusable and the automation generic.
2. **Ownership types as semantic predicates + `x @ ty` refinements** show
   the full-strength version of MEMORY-BORROWS.md's boundary borrows: our
   shared-input/unique-output discipline is RefinedC's `Own`/`Shr` restricted
   to call boundaries. The price of the full version is visible too — Iris,
   per-byte sharing invariants, and later-credits-style bookkeeping. The
   boundary-only fragment we chose captures most libc specs at a fraction
   of that cost; RefinedC tells us exactly what we'd buy by upgrading.
3. **Deterministic, no-backtracking proof search with typeclass extension
   points and shelved side conditions** is the automation design to copy —
   including its UX theorem: *the stuck goal is the error message*. A
   Lean-flavored Lithium over our LowIR judgments is a plausible mid-term
   target, and the evar discipline (protected instantiation, linear
   products) answers problems we already hit in Lean (`omega`/
   `Classical.choice` leakage, metavariable surprises).
4. **Foundational + automated is a proven combination.** Every other
   automated tool in this survey trusts an encoder and a solver; RefinedC
   demonstrates you can keep push-button UX while landing every proof in
   the kernel — the standard our tower already holds itself to, extended to
   C-level programs.
5. **Typing rules as registered, proven-sound instances** — an *extensible*
   trusted-rule-free type system — is the right model for growing our
   borrow/spec discipline: new idioms (a new borrow shape, a new slice
   pattern) enter as lemmas against the semantic model, not as axioms or
   checker patches.
6. **The escape-hatch ladder** (`lemmas → tactics → manual_proof → trust_me
   → skip`) is the practical answer to partially-verified codebases; an
   incremental libc verification wants exactly this per-function dial, with
   the trusted tier syntactically loud.
7. **Caesium's PNVI/VIP byte-provenance model** is the reference design if
   our C layer ever needs integer-pointer casts and `container_of`-style
   idioms — and its `mbyte` (byte | pointer fragment | poison) is the same
   trichotomy CompCert's `memval` chose, converged on independently.
