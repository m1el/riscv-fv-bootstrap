# Verus — design choices

An analysis of `third-party/verus/`: **Verus**, the SMT-based verifier for Rust
(checkout at commit `1f4a5b0d4`, toolchain Rust 1.96.0). Verus statically proves
that executable Rust satisfies user-written specifications, with no runtime
checks. Its stated lineage (`source/docs/project-goals.md`) is explicit: a pure
mathematical spec language (Dafny/F*/Coq-style), classical-logic proofs
(Dafny-style), executable code in Rust (Prusti-style), and — the distinctive
bet — **small, SMT-friendly verification conditions** obtained by (a) keeping
the spec language close to Z3's language (Boogie-style) and (b) using
**lightweight linear type checking instead of SMT reasoning for memory and
aliasing** (Cogent / linear-Dafny-style). Equally explicit non-goals: support
all of Rust, verify `unsafe`, verify the verifier, or verify rustc/LLVM.

This document records the design decisions visible in the code and docs, with
rationale where the sources state it. Two overarching themes:

1. **Rent, don't rebuild, the front end**: Verus reuses rustc for parsing, type
   checking, trait resolution, and — most remarkably — borrow checking of
   *ghost* code, forking only two small rustc crates. Rust's ownership system
   is not just tolerated but *load-bearing*: it replaces separation logic.
2. **The SMT encoding is engineered around quantifier instantiation**: nearly
   every non-obvious choice in the back end (Poly boxing, fuel, one-trigger
   inference, type decorations, broadcast groups, pruning, explicit field
   updates) exists to control what Z3's E-matching does or doesn't see.

## 1. Pipeline and crate architecture

From `source/CODE.md`, the pipeline is a chain of IRs, one crate per layer:

```
Rust source ──rustc parse/expand──▶ HIR
    ──rust_verify (only crate touching rustc)──▶ VIR-AST
    ──vir: simplify, mode-check, prune──▶ VIR-SST
    ──vir: sst_to_air──▶ AIR
    ──air──▶ SMT-LIB ──▶ Z3 (or cvc5)
```

- **`rust_verify`** — the rustc driver; the *only* crate allowed to depend on
  rustc internals. HIR→VIR conversion, attributes, erasure, orchestration.
- **`vir`** — Verification IR in two flavors: AST (expressions may contain
  statements, mirroring Rust) and SST (statement-oriented: expressions are
  pure). Mode checking, recursion/termination, triggers, pruning, and the
  SST→AIR lowering all live here.
- **`air`** — Assertion IR: a Boogie-like assert/assume/havoc/assign language
  with its own typechecker, SSA-ification, weakest-precondition lowering, and
  SMT process management. Usable as a standalone tool on textual `.air` files
  (S-expressions) for debugging.
- **`builtin` / `builtin_macros` + forked `syn`** — the surface syntax layer.
- **`vstd`** — the verified/axiomatized standard library, shipped with a
  precompiled `vstd.vir`.
- **`state_machines_macros`** — tokenized (concurrent) state machines.
- **`rustc_mir_build` / `rustc_hir_typeck` forks** — the only forked rustc
  code, for THIR-level ghost erasure (§4).

## 2. Surface syntax: a macro, not a compiler fork

Verus code lives inside `verus! { }` (`builtin_macros/src/syntax.rs`). The
macro parses Verus-extended Rust using a **forked `syn`**
(`dependencies/syn/src/verus.rs` adds `requires`/`ensures`/`decreases` clauses,
`spec|proof|exec fn` modes, `ghost|tracked` data modes, `open|closed|uninterp`
visibility) and rewrites it into *standard* Rust: attributes
(`#[verifier::...]`) plus calls to stub functions in `builtin`
(`requires<A>(_: A)`, `ensures`, `decreases`, `imply`, … with
`unimplemented!()` bodies and `#[rustc_diagnostic_item]` markers).

The payoff of this design is that **rustc itself type-checks and
name-resolves the specifications** — spec expressions are ordinary Rust
expressions as far as rustc is concerned, so Verus gets resolution, inference,
method lookup, and trait dispatch in specs for free, with no compiler fork.
Even logical implication `==>` becomes a call to a `spec` function
`imply(b1, b2)`. Quantifiers are closures (`forall|x: int| ...`), triggers are
`#[trigger]` attributes on subexpressions, and `&&&`/`|||`/`=~=`
(extensional equality) are additional parsed forms. The historical design
discussion in `source/docs/internal/wiki-archive/Notes-on-Rust-ghost-types.md`
shows this was deliberate from the start: translate Verus syntax to Rust
syntactically *before* resolution/type/mode checking, and let the mode checker
only *validate* ghost-block placement, never infer it.

The forks of `syn` and `prettyplease` exist because Verus syntax is not valid
Rust, so stock `syn` would reject it (`CODE.md`).

## 3. The tri-modal core: `spec` / `proof` / `exec`

The mode system (design doc: `source/docs/internal/modes.md`; implementation:
`vir/src/modes.rs`) is Verus's central language-design idea — a refinement of
Dafny's ghost/non-ghost into a lattice `exec ≤ proof ≤ spec` (data may flow
up the lattice, never down). All three differ along *every* axis:

| | spec | proof | exec |
|---|---|---|---|
| compiled | no (erased) | no (erased) | yes |
| borrow-checked | **no** | yes | yes |
| duplicable | always (`Copy`) | linear by default | per its type |
| requires/ensures | none | yes | yes |
| partial ops (`x/0`) | uninterpreted, legal | must prove | must prove (checked) |
| types inhabited | all (adds "bottom") | no | no |

The rationale, per `modes.md`:

- **spec is Boogie/Z3-like, not Dafny-like**: specifications are *not
  themselves verified*. `x / 0` in a spec is uninterpreted rather than an
  error, `assert(1/0 == 1/0)` is valid, and spec code treats all types as
  inhabited via a bottom value (needed so partial functions and arbitrary
  values are expressible). This keeps spec expressions in one-to-one
  correspondence with SMT terms — the "keep the spec language close to the
  solver's language" goal made concrete. The doc carefully enumerates the
  soundness obligations this creates: bottom must not flow into proof/exec
  (hence no subsumption downward), `match` in proofs on spec values of empty
  enums is rejected, datatypes must be well-founded (§7), spec code *must*
  really be erased before rustc optimizes on `!`-freedom, and function/trait
  postconditions may only be assumed for non-spec values (avoiding Dafny's
  uninhabited-trait unsoundness, Dafny issue 851).
- **proof is linear**: proof code *is* borrow-checked, which is what lets a
  `tracked` proof value act as evidence of resource availability — "linear
  logic and separation logic" styles without an SL prover (§9). spec values,
  by contrast, are freely duplicable.
- Arithmetic is mode-dependent (`rust_verify/src/rust_to_vir_expr.rs`): ghost
  code gets mathematical integers (`int`, `nat`, overflow "behavior: Allow"),
  exec code gets checked machine arithmetic (overflow is a verification
  error). Spec/proof functions both require `decreases` for recursion — proofs
  to avoid circular reasoning, spec functions so that they define anything at
  all (`f(i) = f(i)+1` defines no function).

The `Ghost<T>` / `Tracked<T>` wrapper types let exec code carry ghost data;
inside ghost code the wrappers vanish (variables have their natural types).
The wiki note records the explicit lesson from F*'s `erased t`: wrappers are
awkward, so keep them out of spec/proof code entirely and rare in exec code.

## 4. rustc integration: two interleaved compilations, two tiny forks

### Two passes, interleaved for latency

Verus runs rustc **twice** over the same source (`rust_verify/src/driver.rs`,
long design comment): a GHOST pass (macro keeps ghost code; type-check,
mode-check, borrow-check ghost code, run SMT) and an EXEC pass (macro erases
ghost code; ordinary compilation, and rustc's own borrowck for exec code). The
two are *interleaved* rather than sequential, purely for feedback latency:
GHOST runs through verification first, but its borrow-check errors are
*withheld* until EXEC has run, on the theory that rustc's native diagnostics
for exec borrow errors are better; if EXEC is clean, the GHOST borrow errors
are then printed. The comment ends with the roadmap: eventually run rustc only
once.

### Ghost borrow-checking via a forked THIR→MIR lowering

How do you borrow-check code that isn't real Rust (ghost code mixes with exec
code and must be *erased* for compilation)? Verus historically generated a
synthetic Rust program and fed it back through rustc (`lifetime_generate.rs`;
the driver comment still describes this). **This checkout has replaced that
design**: Verus now forks two small rustc crates (`source/rustc_mir_build`,
`source/rustc_hir_typeck`) and injects a *Verus erasure context* into THIR→MIR
lowering (`rustc_mir_build_additional_files/verus.rs`: `VarErasure` /
`NodeErase` / `CallErasure` tables computed by `rust_verify/src/erase.rs`).
The GHOST pass then simply runs the **real `mir_borrowck`** on every
Verus-aware item (`verifier.rs::run_lifetime_checks_on_verus_aware_items`),
with spec-only code already erased from the MIR it sees. So proof/tracked code
is checked by rustc's actual borrow checker, not a reimplementation and not a
shadow program.

A subtle soundness transform rides along:
`verus_time_travel_prevention.rs` (in the fork) prevents "prophetic" spec
snapshots — taking `let ghost s = x;` while `x` is mutably borrowed would
observe the *future* resolved value. The fix is elegant: for each non-ghost
variable `x`, introduce an always-initialized **shadow variable** that spec
snapshots borrow from instead; the ordinary borrow checker then rejects
exactly the prophetic uses ("partially borrow check all spec code" while
still permitting spec reads of *moved* variables).

### Trait-conflict checking by re-asking rustc

Verus's VIR model of trait impls is coarser than rustc's (it drops lifetimes,
and may ignore bounds like `Sized`), so two impls that rustc distinguishes
could coincide in VIR — which would generate contradictory axioms. Rather than
reimplement coherence over VIR, `rust_verify/src/trait_conflicts.rs` (design
comment at top) **generates a synthetic Rust crate** whose types normalize
VIR's view (decorations like `&`, `Rc`, `Ghost` become tag parameters
`C<TypNum::Ref, T>`) and runs *rustc's own coherence checker* on it: a
conflict there means the VIR model is too coarse, and Verus rejects the code.
Deliberately conservative — "better to reject some valid code than generate
unsound axioms."

### Trust boundary attributes

Items are Verus-aware or external (`rust_verify/src/external.rs`):
`#[verifier::external]` (invisible to Verus), `external_body` (signature and
specs trusted, body unverified — the workhorse escape hatch),
`assume_specification` / `external_fn_specification` /
`external_type_specification` / `external_trait_specification` (attach trusted
specs to unmodified external code, including Rust's std). Every one of these
is TCB: the spec is assumed as an axiom.

## 5. VIR: AST vs SST

VIR-AST mirrors Rust's mutually recursive expressions/statements; VIR-SST
(`vir/src/sst.rs`) enforces that **expressions cannot contain statements**,
"designed to make the translation to AIR as straightforward as possible" —
the same pure-expression discipline Radix bakes into its language, here
recovered by a compiler pass (`ast_to_sst.rs`: statement extraction plus
shadowing elimination by unique renaming; a second pass re-generates pure
`Exp::Bind` forms where a statement-free expression is required, e.g. under a
quantifier). Simplification, pruning (§8), mode checking, and well-formedness
all run on the AST before lowering.

## 6. AIR: a Boogie descendant with its own discipline

AIR (`air/src/ast.rs`) is a small assert/assume language: statements are
`Assume`, `Assert(id, message, filter, expr)`, `Assign`, `Havoc`,
`Snapshot(name)` (capture the state of all variables under a name — the
mechanism behind `old()`), `DeadEnd` (verify a sub-statement but discard its
assumptions — used for `assert ... by { }` blocks), `Breakable`/`Break`,
`Block` (sequence), and `Switch` (nondeterministic choice — branch join).
Lowering to SMT is two classic passes:

- **`var_to_const.rs`** — SSA-ification: mutable variables become versioned
  constants `x@0, x@1, …`; `Assign` becomes `Assume (= x@n e)`; at control-flow
  joins each branch assigns up to the **maximum version** so all paths
  converge on one name; snapshots are just maps from variable to version.
- **`block_to_assert.rs`** — weakest precondition: the whole query becomes a
  single assertion, `wp(assume Q, P) = Q ⇒ P`, `wp(assert Q, P) = Q ∧ P`,
  `wp(s₁;s₂, P) = wp(s₁, wp(s₂, P))`, with fresh boolean *labels* standing in
  for the continuation at `Break`/`Switch` joins to avoid exponential
  duplication of `P`.

Other AIR-level choices worth noting:

- **Own typechecker** (`typecheck.rs`), explicitly because "Z3 … type errors
  are uninformative panics" — better diagnostics for a compiler bug class.
- **Error localization via the model**: each assert gets a fresh boolean label
  (`%%location_label%%…`); on `sat`, Verus reads the model, finds which label
  is true, reports that assert as the failure, then *disables that label and
  re-checks* to find further errors (multi-error mode, `smt_verify.rs`).
  Axioms get global labels so failures can say *which precondition* failed.
- **Solver management** (`smt_process.rs`, `context.rs`): Z3 (default) or
  cvc5 over stdin/stdout pipes with reader/writer threads and a `<<DONE>>`
  echo marker; carefully pinned Z3 configuration (`auto_config=false`,
  `smt.mbqi=false` — E-matching only, no model-based quantifier
  instantiation, `smt.arith.nl=false`, eager threshold 100…), which is itself
  a design statement: Verus wants *predictable, trigger-driven* instantiation,
  not solver heuristics. Budgets use Z3's deterministic `rlimit`
  (≈3,000,000/second, `rust_verify/src/verifier.rs`) instead of wall-clock, so
  failures reproduce.
- **Lambdas** (spec closures) are lowered by a **hole-abstraction** trick
  (`closure.rs`): structurally similar lambdas are merged into one shape with
  holes, so the solver can prove lambda equality by proving hole-filling
  equality.
- **Standalone AIR** (`main.rs`): `.air` files in S-expression syntax can be
  run directly against Z3 — the debugging story for the whole back end
  (Verus's `--log-all` dumps VIR/AIR/SMT at each stage).
- An optional **Singular** integration (`singular_manager.rs`, feature-gated)
  pipes `integer_ring` goals to a computer-algebra system instead of Z3 (§9).

## 7. The SMT encoding: everything serves the trigger

This is where Verus's craft concentrates (`vir/src/poly.rs` has the best
rationale comment in the codebase):

- **Poly boxing** (`poly.rs`): SMT has no polymorphism, so values are coerced
  into a universal `Poly` sort via `Box`/`Unbox`, with `has_type` predicates
  recording the payload type. The stated three-way tension: use native
  `Int`/`Bool` sorts where possible (efficiency), avoid `has_type` reasoning
  (efficiency), but **never let a coercion appear inside a quantifier trigger**
  (completeness) — `f(g(a))` must not fail to match trigger `f(Box(x))`
  because of an inserted coercion. Resolution: quantified variables are
  always `Poly` (with `has_type` invariants), monomorphic function parameters
  are native, and variables used only in *arithmetic* trigger positions are
  natively `int` so that `3 * 4` can match `x * y`.
- **Type decorations split from type ids** (`sst_to_air.rs`): `&Rc<Foo<&bool>>`
  is encoded as a decoration tree *separate* from the type tree, so that
  reference/`Rc`/`Ghost` wrappers (which are erased semantically) don't
  multiply quantifier instantiations over types.
- **Fuel** (`vir/src/recursion.rs`, `def.rs`, SCCs via `scc.rs`): recursive
  spec function definitions are guarded by a fuel parameter (`fuel%f`,
  Peano-style `SUCC`/`ZERO`), so the definitional axiom can only unfold a
  bounded number of times — the standard defense against E-matching loops on
  recursive definitions. `reveal`/`opaque` and `#[verifier::opaque]` expose or
  hide definitions per-proof; SCC analysis assigns fuel per recursive group.
  Termination itself is a proof obligation: `decreases` clauses checked
  (`0 ≤ dec' < dec`), with a built-in `height` function ordering datatypes.
- **Datatype well-foundedness** (`recursive_types.rs`): every datatype must
  have a base-case variant — required because spec code treats types as
  inhabited (§3), so the encoding must be able to construct non-bottom default
  values (citing their OOPSLA 2023 formalization).
- **Trigger inference philosophy** (`triggers_auto.rs`, header comment): "be
  cautious" — choose **one best trigger** per quantifier (multiple triggers
  mean more unintended instantiations), by a scoring heuristic (fewer terms,
  shallower, smaller, function calls over field accesses), admitting ties
  only. Users can always override with `#[trigger]`, and `--triggers` modes
  print what was chosen (`ShowTriggers::Selective` by default — nudging users
  to take manual control of surprising cases).
- **Broadcast groups** (`vstd/vstd.rs::group_vstd_default`): quantified lemmas
  (`broadcast proof fn`, with explicit `#[trigger]`) are grouped and
  opt-in/opt-out per proof via `broadcast use` — library-level quantifier
  budget control, the same concern as fuel but for lemmas rather than
  definitions.
- **Pruning** (`vir/src/prune.rs`): before generating a module's queries, the
  crate is pruned to declarations reachable from that module — explicitly "an
  optimization; it should not affect SMT validity," overapproximating
  (generic datatype reached ⇒ all instantiations reached). Less context =
  fewer axioms = fewer instantiation candidates.
- **Explicit field updates**: a record update mentions every unchanged field
  explicitly rather than using an SMT update-function — "deliberately … for
  better quantifier triggering" (`sst_to_air.rs`).
- Loops: invariants + havoc of modified variables + snapshots, i.e. standard
  invariant-cut encoding rather than unrolling; `loop_inference.rs` infers
  `for`-iterator invariants when the iterated expression is loop-invariant.

## 8. Verification management: buckets, spinoff, incrementality

Functions are grouped into **buckets** (`rust_verify/src/buckets.rs`) — by
default one per module, sharing a pruned context and a Z3 process; each bucket
verifies in its own thread. `#[verifier::spinoff_prover]` moves a
heavyweight function into its own bucket/Z3 context, isolating its resource
use and making it individually profilable. Queries use `push`/`pop`
incrementality within a bucket. The quantifier **profiler**
(`air/src/profiler.rs`, `--profile`) parses Z3 trace logs to attribute cost to
quantifiers by qid — closing the loop on §7: when instantiation blows up, the
tooling points at the offending quantifier.

Error quality gets dedicated machinery: `vir/src/expand_errors.rs` re-runs a
failing assertion after *splitting* conjunctions/implications/quantifier
bodies to report which conjunct failed (`--expand-errors`); the
assert-by-compute **interpreter** (`vir/src/interpreter.rs`, a full symbolic
evaluator for VIR with memoization and rlimits) exists so that
concrete/partially-concrete goals (e.g. `fib(20) == 6765`) can be discharged
by computation instead of hopeless quantifier reasoning.

## 9. Memory and concurrency: linearity instead of separation logic

The signature move (per the project goals: "lightweight linear type checking,
rather than SMT solving, to reason about memory and aliasing"):

- **Permission tokens.** `vstd`'s `PCell<V>` (`cell.rs`), `PPtr<V>`
  (`simple_pptr.rs`), and raw pointers (`raw_ptr.rs`) separate the *data
  location* (freely shareable, `Sync`) from a ghost, `tracked`, non-`Copy`
  **`PointsTo` token** carrying the right to read/write/free plus the spec
  value. Aliasing discipline is then enforced by rustc's borrow checker on
  the tokens (§4) — no SL entailment ever reaches Z3; the SMT solver only
  sees first-order facts like `perm.value() == v`. Design details with stated
  rationale: `PCell` identity is a ghost `CellId` rather than an address
  (cells can move); raw-pointer permissions model provenance + address +
  metadata, with `*mut`/`*const` deliberately interchangeable since the
  permission, not the pointer type, carries uniqueness.
- **Invariants** (`vstd/invariant.rs`): `AtomicInvariant` (Sync; open only
  for atomic durations) and `LocalInvariant` (not Sync; open for arbitrary
  durations) store a `tracked` value protected by a predicate fixed at the
  *type* level (an `InvariantPredicate` trait, avoiding recursive-type
  issues). Re-entrancy is prevented by **opening masks** — namespace sets
  checked flow-insensitively (`vir/src/inv_masks.rs`), the same mask
  discipline as Iris, but decided by the type system + simple assertions.
- **Tokenized state machines** (`state_machines_macros`, i.e. VerusSync): a
  concurrent protocol is written once as a guarded-transition state machine;
  the macro *compiles each field into a token type* according to a
  **sharding strategy** (`ast.rs`: `variable`, `option`, `map`, `multiset`,
  `set`, `count`, `bool`, persistent/`Copy` monotonic variants, and `storage_*`
  variants supporting deposit/withdraw/guard for lock-style ownership
  transfer). Transitions become `proof` exchange functions over tokens
  (`vstd/tokens.rs`: `agree`, `join`/`split` for fungible tokens), and the
  macro also generates and checks the inductive-invariant obligations. This is
  a PCM/ghost-state monoid design (Iris-flavored) made ergonomic as a macro,
  with linearity again outsourced to the borrow checker.
- **`&mut` as a first-class type with two-state specs**: this checkout has the
  new `TypX::MutRef` encoding (see `docs/migration-mut-ref.md`), with
  postconditions about mutable borrows written via `old()`/`final()`; bare
  dereference of a `&mut` parameter in an `ensures` is an error demanding
  disambiguation. The prophetic-snapshot hazard this creates in spec code is
  what the shadow-variable transform in §4 closes.

## 10. vstd: an axiomatized, precompiled prelude

- **Spec collections are axiomatic, not constructive**: `Seq`, `Set`, `Map`,
  `Multiset` are `#[verifier::external_body]` structs containing only
  `PhantomData` — the Rust type is a name; the real semantics is a set of
  `uninterp spec fn`s plus broadcast axioms (`seq.rs`, `set.rs`, `map.rs`).
  Comments record the reasoning: `Set` is semantically a predicate
  `A -> bool`, but hiding that behind `external_body` avoids extensional
  equality on function types; `=~=` (`ext_equal`) is a distinct operator so
  that plain `==` stays cheap and extensionality is invoked deliberately
  (with a heuristic in `vir/src/heuristics.rs` auto-upgrading `assert(a == b)`
  to `=~=` where it obviously helps).
- **`std_specs/`**: specifications *assumed* about Rust's standard library
  (Vec, iterators, ranges, …) — pure trusted axioms, the largest soft spot in
  the TCB and clearly flagged as such.
- **Build**: `vstd_build` compiles vstd once and exports `vstd.vir`; user
  crates import the serialized VIR rather than re-verifying the library
  (three feature configurations: core-only, +alloc, +std).

## 11. Trust story (what you must believe)

Assembled from the goals doc and the attribute system: rustc (type and borrow
checker — Verus *relies* on type safety rather than proving it), Z3/cvc5 (and
Singular if used), the Verus pipeline itself (unverified, per non-goals), the
axioms of `vstd` including `std_specs`, every `external_body` body and
`assume_specification` in user code, and the two forked rustc crates plus the
THIR erasure being semantics-preserving for exec code. This is a deliberately
larger TCB than a foundational (Coq/Lean) verifier — traded for automation,
Rust-native ergonomics, and scale.

## 12. Takeaways

Points of contact with this repo's work, and ideas worth stealing:

1. **Outsource the hard static analysis to an existing checker.** Verus gets
   separation-logic-strength aliasing facts from rustc's borrow checker by
   making permissions *values* (`tracked` tokens). Same spirit as our
   borrows-not-blocks LowIR discipline: encode separation in a type/ownership
   layer so the logic layer only sees first-order equalities.
2. **Two IL flavors, pure expressions at the bottom.** VIR-AST → VIR-SST
   (expressions can't contain statements) → WP is the industrial version of
   the same layering Radix hard-codes and our LowIR passes assume.
3. **Quantifier hygiene as an architecture principle.** Fuel, one-trigger
   inference, Poly-vs-native coercion placement, decoration splitting,
   pruning, broadcast groups, `mbqi=false` — Verus treats E-matching as the
   scarce resource and designs every encoding around it. Any future
   SMT-assisted layer of our tower should copy this posture wholesale.
4. **Determinism knobs**: Z3 `rlimit` instead of wall-clock, pinned solver
   config, per-function spinoff contexts — reproducible failures are a
   feature we already value (cf. our clocked semantics).
5. **Escape hatches are first-class**: `by(bit_vector)` (with dual 32/64-bit
   queries when the arch is unspecified), `by(nonlinear_arith)`,
   `by(integer_ring)` via Singular, `by(compute)` via a built-in evaluator —
   rather than one encoding that must handle everything, hard theories get
   dedicated, opt-in solvers scoped to a single assertion.
6. **Honest, mechanized trust boundaries**: everything assumed is marked
   (`external_body`, `assume_specification`, axiom labels in error output),
   which is what makes the large TCB auditable at all.
