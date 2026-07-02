# seL4 & l4v — design choices

An analysis of `third-party/seL4/` (the microkernel, C) and
`third-party/l4v/` (its verification, Isabelle/HOL) — the largest sustained
formal verification effort in existence: **~880k lines of proof across 845
theories** guarding **~10k lines of C**, alive for fifteen-plus years,
covering functional correctness (abstract spec → C), security theorems
(integrity, noninterference), and hooks for binary-level validation. The
genre, for our series: **artifact-first co-design** — the kernel was shaped
around what could be proved, and the proof stack was engineered to survive
the kernel's evolution. Both halves of that sentence carry the lessons.

## 1. The kernel: designed to be provable

(`seL4/`; evidence in `src/`, `config.cmake`, `CAVEATS.md`)

Every headline feature of seL4's design doubles as a proof-obligation
eliminator:

- **Event-based, single kernel stack.** The kernel is a reactive event
  handler (`handleEvent` split per entry cause), not a set of kernel
  threads; there is no in-kernel concurrency in verified configurations.
  Interrupts are disabled during kernel execution, with **explicit
  preemption points** in the few long-running operations (revoke, retype,
  memory zeroing): `preemptionPoint()` polls for pending IRQs only after a
  configured budget of "work units" (`CONFIG_MAX_NUM_WORK_UNITS_PER_
  PREEMPTION`, default 100; reset chunks bounded to 2^8 bytes). Result:
  every kernel entry is a *bounded, sequential* state transformation — the
  proofs never face interleaving, and long operations become resumable
  loops with explicit invariants.
- **No kernel heap.** All kernel objects (TCBs, CNodes, page tables,
  endpoints) are created by *userland* retyping **Untyped memory**
  capabilities (`untyped.c`); the kernel tracks only a free index per
  untyped region. There is no allocator to verify, no out-of-memory paths
  inside the kernel, and memory-exhaustion policy is user-level by
  construction.
- **Capabilities as the sole authority mechanism**, with the derivation
  tree (MDB) as doubly-linked slots carrying revocation flags — revocation
  is a bounded tree traversal, and the security theorems (§5) are stated
  directly over the capability authority graph.
- **Determinism and bounds everywhere**: fixed IRQ array sizes, a retype
  fan-out limit (256), one kernel timer tick, no FPU state in-kernel (lazy
  owner-tracked switching), no floating point, no unbounded loops.
- **Generated, proof-carrying low-level code**: the **bitfield generator**
  consumes `.bf` layout descriptions and emits both the C accessors
  (`static inline CONST/PURE`) *and* Isabelle proofs that they implement
  their specs — hand-written bit-twiddling is designed out of the TCB. The
  kernel builds as a **single translation unit** (`kernel_all.c`)
  specifically so the C parser can consume it.
- **Honesty as a document**: `CAVEATS.md` is a per-architecture matrix of
  exactly which configurations are verified (AArch32 fully incl. security
  theorems; RISCV64 C-level + security; AArch64 integrity-only pending;
  X64 C-level only; SMP and MCS unverified), and which config parameters
  proofs are sensitive to. `CHANGES.md` classifies every kernel change as
  binary-/source-/proof-compatible — co-evolution as process.

## 2. The specification stack

(`l4v/spec/`; seven layers)

```
Abstract spec (ASpec)     nondeterministic monadic operational spec
   ⊒ Design spec (ExecSpec)  GENERATED from the Haskell prototype
   ⊒ C (CSpec)               parsed kernel_all.c in SIMPL
plus: machine interface (axiomatized), capDL (capability-only view),
      sep-abstract (separation-kernel variant, bisimilar), Haskell source
```

- **The Haskell prototype is the design methodology.** The kernel was
  *designed* as a literate-Haskell executable model (`spec/haskell/`,
  organized by subsystem, prose interleaved); a translator
  (`tools/haskell-translator/`, skeleton files mapping Haskell sections to
  Isabelle theories per architecture) generates the design spec. The
  README is blunt: don't read the generated theories, read the Haskell.
  The design document, the prototype, and the middle refinement layer are
  *one artifact*, mechanically kept consistent.
- **The abstract spec** is written in the **nondeterministic state monad**
  `'s ⇒ ('a × 's) set × bool` — result set plus a failure flag —
  with `select`/`⊓` for nondeterminism and `assert` for obligations.
  Kernel objects, capabilities, and the CDT live in a clean HOL data model
  (`Structures_A`); the API is a small event algebra (syscall, interrupt,
  fault, VM fault) entering through one `call_kernel`.
- **The machine boundary is an explicit axiomatization**
  (`spec/machine/`): some operations defined (word load/store), the rest
  deliberately underspecified via `machine_op_lift` over an opaque
  `machine_state_rest` — the hardware model is a visible, auditable seam.
- **The whole system is an automaton** (`ADT_A`): kernel transitions plus
  *nondeterministic user transitions* (user steps constrained only by
  their VM rights), `(user_context × kernel_state) × mode × event`. The
  refinement theorems are subset inclusions between these automata.
- **capDL**, a capability-only abstraction of the state, exists so that
  *system initialization* can be verified against declarative capability
  distributions; **sep-abstract** is a restricted-API variant proved
  bisimilar to the full kernel for separation-kernel deployments.

## 3. The proof stack

(`l4v/proof/`; the numbers: invariants 178k LOC, refine 228k, crefine 346k)

- **Invariants first** (`invariant-abstract/`): a single `invs`
  mega-conjunction (pspace validity, object validity, symmetric
  references, MDB well-formedness, arch invariants…) proved preserved by
  every kernel operation. The workhorse is **crunch** — a command that
  walks the call graph and *bulk-generates* preservation lemmas for a
  predicate across whole subsystems, with escape hatches (`crunch_ignore`,
  extra wp/simp rules). This one tool is why 178k lines of invariant proof
  are maintainable.
- **Refinement via `corres`** (`refine/`): forward simulation between the
  abstract and design monads,

  ```
  corres_underlying srel nf nf' rrel G G' m m' ≡ ∀(s,s')∈srel. …
    ∀(r',t') ∈ fst (m' s'). ∃(r,t) ∈ fst (m s). (t,t')∈srel ∧ rrel r r'
  ```

  — every concrete outcome has a matching abstract outcome — with a
  calculus of split rules, a `corres` proof method, and a later
  guard-strengthening refinement (`corresK`) born of unification pain.
- **C refinement via `ccorres`** (`crefine/`): the same idea against
  Schirmer's SIMPL semantics of the parsed C, with extraction functions
  for return values, an exception-handler stack, and `rf_sr` relating the
  design state to the C heap/globals. Notably the main kernel proofs work
  *directly on SIMPL* (AutoCorres, §4, is used elsewhere).
- **Composition** is automaton inclusion chained by transitivity —
  `ADT_C uop ⊆ ADT_H uop ⊆ ADT_A uop` (`Refine.thy`, `Refine_C.thy`),
  including a separately-verified **fastpath** variant.
- **The assertion-transport discipline** (`docs/haskell-assertions.md`) is
  a quietly brilliant device: an assertion written in the Haskell model is
  a *free assumption* when proving abstract invariants, becomes a *proof
  obligation* in Refine (discharged from those invariants), and is an
  *assumption again* in CRefine — invariant knowledge flows down the
  refinement stack without ever being proved twice.
- **Architecture genericity** is locale engineering: one `Arch` locale,
  `arch_requalify_*` commands controlling namespace exposure, theories
  split into generic + per-arch files selected by `$L4V_ARCH` — five
  architectures sharing one proof skeleton.

## 4. The infrastructure

(`l4v/lib/`, `l4v/tools/`)

- **The monad framework** (now its own `Monads` session): nondet monad,
  Hoare triples `⦃P⦄ f ⦃Q⦄` with the **wp** backward-propagation tactic
  (attribute-indexed rule sets, combinator rules for conjunctive posts,
  `wpc` case-splitter, `wpsimp` fixpoint loop), `no_fail`/`empty_fail` as
  orthogonal predicates, and a **trace monad** variant for rely-guarantee
  concurrency work. This is the ancestral home of the wp-style automation
  half the field (and our own Hoare-style Lean proofs) now takes for
  granted.
- **The C parser** (Norrish): a strict C99 subset (no address-of locals,
  no goto, no side effects in expressions, no function-pointer generality)
  into SIMPL, over **Tuch's typed memory model** (UMM): a byte heap plus a
  heap-type description, with typed views (`lift_t`, `h_val`,
  `h_t_valid`) recovering struct-level reasoning from bytes — the same
  bytes-with-typed-views compromise CompCert and Caesium reached.
- **AutoCorres** (Greenaway): the verified abstraction tower over the
  parser output — SIMPL → L1 (exceptions) → L2 (lambda-lifted monadic) →
  type strengthening → heap abstraction → **word abstraction** (machine
  words to ℤ/ℕ with side conditions) → polish, each phase emitting
  correspondence theorems, composed into one `ac_corres`. The main kernel
  proofs predate it; it's the tool the rest of the ecosystem (and many
  external projects) verify C with.
- **Word_Lib** (the de-facto standard Isabelle machine-word library),
  a separation algebra session, Eisbach method libraries, and a
  Python regression harness (`run_tests`, session DAG, per-test CPU
  timeouts) that is the project's CI backbone.

## 5. The security theorems

(`proof/access-control/`, `proof/infoflow/`)

The survey's only *confidentiality* results. Both are stated over the
abstract spec against a **policy/authority graph** (`PAS`: labels, and
edges like Read/Write/Control/SyncSend), then transferred to C by the
refinement stack:

- **Integrity** (`call_kernel_integrity`): any state mutation performed by
  a kernel call on behalf of a subject stays within the objects the
  authority graph lets that subject affect — "the kernel writes only where
  you had authority to write."
- **Noninterference** (`InfoFlow`, `Noninterference.thy`): classical
  unwinding conditions over inductively-defined `subjectReads` /
  `subjectAffects` closures of the authority graph, state-equivalence
  relations per label, and `reads_respects` per kernel function — yielding
  *intransitive* noninterference (information flows only along policy
  edges). Explicitly out of scope: timing channels — stated as such.

These required the kernel's *scheduling* to be policy-aware (domain
scheduler), and they are what the CAVEATS matrix means by "security
properties" per architecture.

## 6. Binary verification

(`proof/asmrefine/`) The C-to-binary gap is closed by **translation
validation**: `SimplExport` dumps the parsed C semantics into a graph
language (SydTV-GL), an external toolchain (`graph-refine`, with a
HOL4-based decompiler) proves the compiled ARM binary's graph refines it,
and `SimplExportAndRefine` proves in Isabelle that the export is faithful.
The compiler (gcc) is thereby removed from the TCB for supported
configurations — the same prove-the-checker seam as CompCert's validated
passes, applied at the very bottom of someone else's compiler.

## 7. Assumptions

Stated across READMEs/CAVEATS: the Isabelle kernel; fidelity of the C
parser's semantics to the compiler's C (discharged down to binary only
where graph-refine runs); the axiomatized machine interface (TLB/cache
management modeled abstractly, correct-by-assumption); boot/init code
(partially verified via capDL/sys-init); hardware correctness; config
sensitivity of proofs; SMP and MCS configurations unverified (MCS
design-level proofs in progress on its branch); timing channels excluded.

## 8. Takeaways

1. **Co-design is the master lesson.** Every seL4 feature is a proof
   obligation negotiated away: preemption points instead of concurrency,
   untyped retype instead of an allocator, an event kernel instead of
   kernel threads, generated bitfield code instead of hand bit-twiddling.
   Our tower already lives this (hex0's 16-encoding ISA surface, LowIR's
   restrictions); the libc plan should keep choosing *restrict the
   artifact* over *strengthen the logic* — and keep a CAVEATS.md-grade
   statement of exactly which configurations the theorems cover.
2. **An executable design layer between spec and implementation** — the
   Haskell prototype, mechanically translated into the middle refinement
   layer — is the deepest structural idea. Our LowIR sits in that seat;
   seL4 shows the value of making the middle layer *the* design artifact
   and generating, not hand-syncing, its formal image (directly relevant
   to our Lean/Coq dual-development pain).
3. **Assertion transport** (free in invariants → obligation in refinement
   → assumption below) is immediately applicable to our
   `compile_sim`/`core_refines` stack: prove facts once at the top,
   thread them down as assumptions instead of reproving.
4. **crunch is the tool we keep reinventing badly.** Bulk-generating
   "predicate P is preserved by all N functions" lemmas by call-graph
   walk, with a hint/ignore interface — our State-chain invariant
   boilerplate (and its OOM-prone tactic workarounds) is exactly the
   workload it automates. A poor-man's crunch for Lean is a high-value
   infrastructure project.
5. **The corres/ccorres calculus is the industrial form of our refinement
   lemmas** — nf flags, return-value relations, split-rule calculi, and
   the CorresK lesson that *guard strengthening deserves first-class
   support* because unification pain is real. Worth mining before our
   cross-call disjointness / frame-based call specs grow their own
   calculus ad hoc.
6. **Proof engineering is a discipline with artifacts**: naming
   conventions binding theory names to layers (`_A/_H/_AI/_R/_C`), style
   guides that ban `auto` mid-proof, a regression DAG, compatibility
   classification of every artifact change, and an 88:1 proof-to-code
   ratio sustained for 15 years. Our commit-at-green-milestone habit,
   RESUME docs, and gotcha logs are the embryo of this; seL4 is what it
   looks like grown up.
7. **Security theorems ride on the abstract spec** and transfer down for
   free — the strongest argument in the survey for investing in our
   tower's abstract layers: integrity/NI-class properties are proved
   where the state model is clean, never at the C or ISA level.
