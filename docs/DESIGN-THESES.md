# Design theses: toward a verified systems language

Distilled 2026-07 from the [third-party design-review series](README.md#third-party-design-reviews)
(Radix, Verus, CompCert, CakeML+Pancake, bedrock2, rustc, Creusot, Prusti,
RefinedC, Frama-C, lean-mlir, seL4+l4v) and the discussion around it. Ten
theses about how verified programs, compilers, and languages should be
built, ending with the design target they point at. Each thesis cites the
evidence; several carry explicit refinements or counterpoints found during
the survey.

## The theses

### 1. Proof difficulty is a property of how the program was constructed

We do not fight the halting problem or incompleteness; we construct
programs *together with* their proofs, so that program and proof share
structure. The undecidability folklore intrudes in exactly one place —
termination of spec-level functions — and the universal dodge is
fuel/clocks plus partial correctness, which this repo already uses.

*Evidence:* every verified artifact in the survey is co-designed —
seL4's preemption points turn concurrency into bounded sequential
reasoning; bedrock2 bans recursion so stack bounds are a static
computation; Radix's `scope` makes inlining a rule swap; CakeML's clock
makes divergence a fuel limit instead of coinduction
([SEL4-DESIGN](third-party/SEL4-DESIGN.md),
[BEDROCK2-DESIGN](third-party/BEDROCK2-DESIGN.md),
[RADIX-DESIGN](third-party/RADIX-DESIGN.md),
[CAKEML-DESIGN](third-party/CAKEML-DESIGN.md)).

*Refinements:* (a) "constructed together" is a spectrum — derive the
program from the proof (LiveVerif, CakeML's translator), co-annotate
(RefinedC), post-hoc (Alive2 over LLVM) — and post-hoc verification of an
artifact not designed for it is where proofs go to die: rustc's borrow
checker can only ever get a validator, never a proof
([RUSTC-BORROWCK-DESIGN](third-party/RUSTC-BORROWCK-DESIGN.md)).
(b) The thesis extends to lifecycle: proof *maintenance* dominates proof
construction (see thesis 10).

### 2. Factor compilation into (verified engine) × (cheap per-instance obligations)

Many small transformations beat few big ones — but only under a uniform
composition framework, and "small passes" is just one instance of the real
principle. lean-mlir demonstrates the dual factorization: *one* verified
mega-engine (peephole rewriting, `denote_rewritePeepholeAt`) plus hundreds
of tiny per-rule obligations discharged by automation.

*Evidence:* CompCert's ~20 passes under `mkpass`/simulation-diagram
uniformity; CakeML's 12 ILs under one `state_rel`+clock recipe; bedrock2's
`phase_correct` records; lean-mlir's rule library
([COMPCERT-DESIGN](third-party/COMPCERT-DESIGN.md),
[CAKEML-DESIGN](third-party/CAKEML-DESIGN.md),
[LEAN-MLIR-DESIGN](third-party/LEAN-MLIR-DESIGN.md)).

*Caveats:* each intermediate language is itself a spec someone must
maintain — N passes = N semantics = N liabilities; the framework is what
keeps that affordable. Corollary: once verified, re-running a pass is free
(composition), which is how industrial pipelines actually behave (LLVM
runs InstCombine ~8× per -O2). Calibration: LLVM has ~500 registered
passes and ~55k lines in InstCombine alone; verified compilers sit at
1–5% of the pass count and ~0.1% of the pattern count — parity is not the
goal; the factorization is.

### 3. For heuristic algorithms, verify the output checker, not the implementation

Translation validation — an untrusted implementation plus a small verified
per-run checker — is the cheapest proof there is, *when it applies*.

*Evidence:* CompCert's register allocation (untrusted IRC + Rideau–Leroy
checker) and linearization ("any enumeration is fine if every reachable
node appears once"); bedrock2's regalloc checker; seL4's binary
verification (graph-refine); Alive2 as per-run validation for LLVM
([COMPCERT-DESIGN](third-party/COMPCERT-DESIGN.md),
[BEDROCK2-DESIGN](third-party/BEDROCK2-DESIGN.md),
[SEL4-DESIGN](third-party/SEL4-DESIGN.md)).

*Decision criterion:* validate when the algorithm is heuristic and churns
(allocation, scheduling, anything in LLVM); verify the algorithm itself
when it is stable and a checker would not be much simpler — CakeML
deliberately verified its IRC allocator in-logic, proving the other end of
the spectrum is reachable. *Caveats:* (a) a checker yields "this run was
correct", not "the compiler is correct" — a weaker theorem, fine for build
pipelines, different for shipping claims; (b) hard passes need
*witnesses* from the implementation (Crellvm's lesson), and certificate
design is where the effort hides.

### 4. Pass down intent, types, and certificates; recompute analyses

The productive information flow through a pipeline is *declarative*:
types (whose invariants downstream stages cash in — rustc's `noalias`
comes from `&mut`, not from borrowck data), user intent planted as
analysis-only annotations (`AscribeUserType`, `FakeRead` — flowing *down
to* the analysis), certificates where a validator needs them, and
assertion transport (seL4: assertions free at the abstract level become
assumptions below, no re-proof). What flows badly is *analysis state*:
rustc deliberately re-runs the init/liveness dataflow in drop elaboration
rather than consume borrowck's results, and destroys every borrowck
artifact after the check
([RUSTC-BORROWCK-DESIGN](third-party/RUSTC-BORROWCK-DESIGN.md),
[SEL4-DESIGN](third-party/SEL4-DESIGN.md)).

Slogan: **recomputation over coupling; never bind a stage to an upstream
solver's internal state.** Proof-carrying code is the certificate lane of
this thesis, not the whole of it.

### 5. Libc needs aliasing discipline at interfaces; provenance is pay-per-function

Even the simplest libc functions force the issue: `strtoull` borrows
`&mut errno` (thread-local) and a shared input slice, must express
separation, an errno protocol, and unbounded valid-string reads. But the
survey argues against "dead end":

- **Interface-level aliasing discipline is necessary** — every surveyed
  tool converged on it independently: ACSL `\separated`, Verus linear
  tokens, Creusot prophecies, Prusti pledges, bedrock2 `mGive`/`mReceive`,
  RefinedC Own/Shr, our own [MEMORY-BORROWS](MEMORY-BORROWS.md) borrows.
- **Full intra-body borrow checking and byte-level provenance are not
  globally necessary**: Frama-C WP selects a memory model *per function*
  (Hoare for pure code, typed for most, bytes for the nasty corner);
  RefinedC pays for PNVI/VIP provenance only where `container_of`/pointer
  tagging/allocator internals demand it
  ([FRAMAC-DESIGN](third-party/FRAMAC-DESIGN.md),
  [REFINEDC-DESIGN](third-party/REFINEDC-DESIGN.md)).
- **A subset libc is demonstrably feasible** — RefinedC verified real
  allocators and pKVM kernel code; Frama-C's `share/libc` shows the whole
  contract inventory (~100 headers) is finite and field-tested, ready to
  mine rather than invent. The honest blocker list is short: variadics,
  `setjmp`, locales, threads/atomics. Full POSIX is the dead end; the
  subset is the road.

`strtoull` (already the named next step in
[RESUME-LOWIR](archive/RESUME-LOWIR.md)) is the right probe: it exercises borrows,
errno-as-ghost-state, and saturation/overflow contracts without touching
any blocker.

### 6. The design target: the empty cell

We want a language that:

- has roughly the power of C;
- has no GC (and no hidden allocation);
- is easy to reason about formally;
- can express low-level memory access and borrowing — through types or
  proofs;
- carries its proofs down to machine code (a verified compiler, and/or a
  validated translation at the bottom).

The survey's feature matrix says this language **does not exist** — every
component does, but not the composition:

| | C-power, no GC | borrow discipline | program logic | verified to machine code |
|---|---|---|---|---|
| Pancake | ✓ | ✗ | (in progress) | ✓ |
| bedrock2 | ✓ | boundary only (FFI) | ✓ | ✓ |
| Rust + Verus/Creusot | ✓ | ✓ (types) | ✓ | ✗ (trusts rustc+LLVM) |
| RefinedC | ✓ | ✓ (semantic types) | ✓ | ✗ (trusts frontend+gcc) |
| CakeML | ✗ (GC) | ✗ | ✓ (CF) | ✓ |

**(borrow types) × (verified compilation to bytes) is the empty cell.**
And the survey suggests the composition that fills it:

1. **Check borrows as a pure gate over the IR** (rustc's architecture:
   reconstruct from types + planted intent, never propagate analysis
   state) — the checker's kernel is small: move-path tree, init/liveness
   dataflow, loans with a liveness kill rule, a place-conflict oracle, an
   outlives solver — each piece independently verifiable, and without
   closures/HRTBs the hard parts of rustc's version disappear.
2. **Cash the check in for prophecies** (Creusot/RustHorn): checked
   `&mut` becomes a `{current, final}` pair, and verified user code gets
   *first-order, heap-free* VCs — no separation logic in the common case.
   Prusti's fold/unfold machinery is the measured cost of keeping SL
   around instead ([PRUSTI-DESIGN](third-party/PRUSTI-DESIGN.md)).
3. **Compile through a Pancake/bedrock2-style verified backend** — our
   LowIR + `compile_sim` line ([LOWIR-DESIGN](LOWIR-DESIGN.md)) is
   exactly this rung, with `loopLang`-style adapters and CakeML's
   `extend_with_resource_limit` as the honest resource caveat.
4. **Boundary borrows in call specs** (frames; MEMORY-BORROWS) as the
   modular interface, with a RefinedC-style escape-hatch ladder
   (`lemmas → tactics → manual proof → trusted → skip`) for the fringe.

### 7. Design the contract language before the second consumer exists

ACSL's deepest achievement is one spec language with three consumers —
abstract interpretation (Eva), deductive proof (WP), runtime monitoring
(E-ACSL) — plus `assigns \from` functional dependencies and the
`check`/`assert`/`admit` trichotomy
([FRAMAC-DESIGN](third-party/FRAMAC-DESIGN.md)). A spec layer written for
one prover will be rewritten; one written as a *language* (with declared
frame conditions, named clauses, and an assume/verify/verify-only
distinction) gets consumed by fuzzers, provers, and monitors alike.

### 8. Keep a mechanized evidence ledger

Heterogeneous evidence — Lean proofs, Coq ports, QEMU fuzzing, ISA
cross-checks, factored hypotheses — needs Frama-C-grade bookkeeping:
statuses *with hypothesis lists*, consolidation with cycle detection, and
honest verdicts (`Valid_under_hyp`, `Inconsistent`, `*_but_dead` for
vacuous truth). Our TCB.md/RESUME files are this ledger in markdown; at
scale it wants mechanizing ([FRAMAC-DESIGN](third-party/FRAMAC-DESIGN.md)).

### 9. Design the language so its VCs land in decidable fragments

"Easy to reason about" must be operationalized: no UB nooks in the
semantics, and verification conditions that reduce to fragments a
kernel-verified decision procedure eats. lean-mlir's entire proof economy
runs on goals collapsing to `BitVec` formulas for `bv_decide`; Lithium
runs on deterministic, no-backtracking proof search where *the stuck goal
is the error message*; Verus treats E-matching as the scarce resource and
designs every encoding around it
([LEAN-MLIR-DESIGN](third-party/LEAN-MLIR-DESIGN.md),
[REFINEDC-DESIGN](third-party/REFINEDC-DESIGN.md),
[VERUS-DESIGN](third-party/VERUS-DESIGN.md)). Boring proofs are a
language-design deliverable, not an automation afterthought.

### 10. Budget for proof lifecycle, not proof construction

seL4 sustains an 88:1 proof-to-code ratio across 15 years and five
architectures because of machinery, not heroism: `crunch` bulk-generates
invariant-preservation lemmas over the call graph; naming conventions bind
theory names to refinement layers; style rules ban fragile tactics;
a regression DAG gates every change; kernel commits are classified by
proof compatibility ([SEL4-DESIGN](third-party/SEL4-DESIGN.md)). Our
commit-at-green-milestone habit, RESUME handoffs, and gotcha logs are the
embryo of this. A poor-man's `crunch` for Lean — generating "predicate P
is preserved by all N functions" lemma skeletons plus a `wpsimp`-grade
tactic — is the single highest-leverage infrastructure project this
thesis implies.

## Where this repo already stands

The tower is the bottom of the empty-cell composition: verified hex0/hex1
(machine-code level), LowIR with clocked semantics and frame-based call
specs (the backend rung), MEMORY-BORROWS (the interface discipline), and
the libc-formalize survey (the application). What the theses add is the
top: a borrow-checked surface whose checker feeds a prophecy translation,
a contract layer designed for multiple consumers, and the lifecycle
machinery to keep it all alive. `strtoull` remains the immediate probe;
the borrow checker over LowIR is the first genuinely new component.
