# Frama-C — design choices

An analysis of `third-party/frama-c/` (checkout `eb9f7492`, version 34~dev
"Selenium"): **Frama-C**, CEA's industrial platform for C source analysis.
This review is a genre change from the verifiers covered so far: Frama-C is
not one analysis but a **kernel + plugins platform** where heterogeneous
techniques — abstract interpretation (Eva), deductive verification (WP),
runtime monitoring (E-ACSL), slicing, dependency analyses — *collaborate*
over one normalized AST, one specification language (**ACSL**), and one
property-status ledger. It is unabashedly non-foundational (the analyses
are trusted OCaml), but it is the tool that ships in safety-critical
certification pipelines, and it embodies twenty years of answers to "how do
multiple imperfect analyses add up to a verdict." It also contains the most
complete ACSL-specified libc in existence (`share/libc/`) — direct raw
material for our own libc plans.

Three signature designs organize everything: (1) **ACSL as the lingua
franca** — every analysis reads and writes the same annotation language, in
the AST; (2) **the property-status consolidation ledger** — partial results
with explicit hypotheses, combined with cycle detection; (3) **alarms as
annotations** — when one analysis can't prove something, it *emits an ACSL
assertion* for another analysis (or a human) to discharge.

## 1. Kernel: normalized AST, projects, states, emitters

- **AST** (`kernel_internals/typing/cabs2cil`): CIL-derived, aggressively
  normalized — nested calls extracted to temporaries, `&&`/`||`/`?:`
  linearized with explicit sequence points, assignment operators
  decomposed. ACSL annotations are first-class AST citizens, tracked in
  kernel tables (`Annotations`) indexed by **emitter**.
- **Emitters** (`plugin_entry_points/emitter.mli`): every annotation and
  status records *who* produced it, and each emitter declares which
  command-line parameters it depends on, split into
  `correctness_parameters` (change ⇒ results cleared) vs
  `tuning_parameters` (change ⇒ results stay valid, maybe improvable). A
  small design with big consequences: staleness is tracked mechanically.
- **Projects and states** (`libraries/project/`): all global analysis state
  is registered (`State_builder`) with an explicit dependency graph; a
  *project* is a full snapshot of every registered state, and several
  projects coexist (the slicer's output is a new project with a reduced
  AST). Selective invalidation (`State_selection`) clears exactly the
  dependents of what changed; the whole thing serializes for save/load.
  This is the platform answer to "analyses compose and ASTs get
  transformed" — a heavier cousin of rustc's query system, dependency-aware
  but eager and coarse-grained.
- **Machdeps**: target architecture is a data record (sizes, alignments,
  endianness, typedef identities, even `errno` lists) that parameterizes
  parsing and all analyses.

## 2. The property-status consolidation ledger

Frama-C's crown jewel (`kernel_services/ast_data/property_status.ml`).
Every ACSL annotation yields identified properties (`Property.t`:
preconditions per call site, postconditions per behavior, loop invariants,
assigns, reachability, …). Analyses **emit** local statuses — `True`,
`False_if_reachable`, `False_and_reachable`, `Dont_know` — each **with a
list of hypothesis properties** it relied on. Consolidation then computes,
per property:

- `Valid` (all emitters' hypotheses recursively valid) vs
  **`Valid_under_hyp`** (locally proved, hypotheses pending) — the honest
  intermediate that most tools lack;
- `Invalid` vs `Invalid_under_hyp`, `Unknown` with a *pending map* of what
  remains to verify, `Inconsistent` when emitters contradict;
- `*_but_dead` variants when the program point is proved unreachable —
  conclusions that hold vacuously are flagged, not silently counted;
- **cycle detection**: consolidation memoizes over the hypothesis graph and
  refuses circular support, unless an emitter has explicitly registered the
  cycle shape as legal (`legal_dependency_cycle` — e.g., WP's mutual
  function contracts, which are sound by their induction scheme).

This is the mechanized form of "combining partial proofs from different
tools," including the failure modes (circularity, contradiction,
vacuity) that ad-hoc combinations get wrong. The `report/` plugin exports
the consolidated ledger as CSV/JSON for CI gating.

## 3. ACSL

The specification language, as implemented in `cil_types.ml`: function
contracts with **named behaviors** (`assumes`/`requires`/`ensures` +
`complete`/`disjoint` coverage obligations), statement annotations, loop
`invariant`/`assigns`/`variant`, logic functions and predicates (including
**inductive predicates** and `axiomatic` blocks), lemmas, ghost code (a
`vghost` bit on declarations and statements), model fields, `\terminates`
and `decreases`. The memory predicate vocabulary is the most complete of
any surveyed spec language: `\valid`, `\valid_read`, `\initialized`,
`\dangling`, `\separated`, `\fresh`, `\allocable`/`\freeable`,
`\base_addr`/`\offset`/`\block_length`, `\aligned`, `\object_pointer`, with
state labels (`\at(e, L)`, `Pre/Post/Here/LoopEntry/Old`). Two designs
deserve special note:

- **`assigns … \from …`**: frame conditions carry *functional
  dependencies* — not just "what may be written" but "from which inputs."
  This one clause powers Eva's spec-based abstract calls, the From/InOut
  dependency analyses, and taint-style reasoning. Cheap to write, consumed
  by everything.
- **The `assert` / `check` / `admit` trichotomy** (`predicate_kind`):
  `assert` is verified *and* assumed downstream; `check` is verified but
  **never assumed** (pure sanity probe); `admit` is assumed unverified
  (loud axiom). Three-way honesty that our own spec layers should copy.

## 4. Eva: the abstract interpreter

A sound (over-approximating) whole-program value analysis built as a
**product of pluggable domains** (`plugins/eva/`):

- The workhorse **cvalue** domain: values are `Ival` (intervals *with
  congruences*) or base→offset maps (`Location_Bytes`); memory states are
  **offsetmaps** — byte/bit-precise persistent maps from offsets to values
  with repetition, over hash-consed patricia trees. When pointer
  provenance is lost (casts, wild arithmetic), values degrade to a
  **garbled mix** — `Top(bases, origin)`, a set of possible bases *with a
  recorded origin of the imprecision*. An honest bottom for provenance
  chaos, with blame attached.
- Satellite domains (octagons, symbolic locations, equalities, signs,
  bitwise, taint, traces, multidim) cooperate through a shared
  evaluation/reduction protocol in the domain product — each domain narrows
  the others' results via the common value/location interfaces.
- **Alarms**: whenever Eva cannot exclude a UB (overflow, invalid access,
  division, uninitialized read…), it *emits an ACSL assertion* at that
  point with status Unknown (orange) or False (red). That assertion is a
  property like any other — WP can later discharge it, E-ACSL can monitor
  it, a human can review it. This is the producer side of the platform
  economy (the `rte/` plugin is the same idea run eagerly, generating
  guards for WP without running Eva).
- Precision is budgeted explicitly: `slevel`/trace partitioning (how many
  parallel states per point before joining), loop unrolling annotations,
  widening hints; calls are analyzed by inlining with a **memoization
  cache** (`mem_exec`) keyed on the inputs the callee actually reads;
  missing code is summarized from its ACSL `assigns \from` spec; malloc is
  modeled with weak/strong bases via builtins.

## 5. WP: deductive verification with selectable memory models

WP compiles ACSL contracts to verification conditions, with a design
signature no other surveyed tool has: **the memory model is a per-function
choice** (`Factory.ml`): `Hoare` (variables as logic values, no aliasing),
`Typed` (base+offset pointers with per-C-type memory maps and region
separation — assumes no wild int↔pointer casts, in `NoCast`/`Fits` modes),
`Bytes` (byte-level), `Region` (driven by the region analysis plugin), and
`Eva` (importing value-analysis facts) — refined by variable partitioning
(`Raw/Var/Ref/Caveat`). Each model contributes explicit **hypotheses**
(`MemoryContext` separation zones) that surface as assumptions of the
proof, feeding straight into the consolidation ledger. Instead of one
memory model that must fit all code, WP picks the cheapest sound model per
function and *declares its debt*.

Downstream: **QED**, a built-in hash-consed rewriting/simplification engine
that normalizes goals before provers see them (constant folding, term
sharing, literal normalization) — the same "pre-solver hygiene" instinct as
Verus's quantifier discipline; then a Why3-mediated prover portfolio
(Alt-Ergo, Z3, CVC…, plus Coq export), a JSON **proof-script** format for
the interactive TIP editor (tactics like split/induction/rewrite with an
autofocus UI), and a proof cache with replay/update/offline modes for CI.

## 6. The rest of the ecosystem, briefly

**E-ACSL** compiles ACSL annotations into *runtime checks* — memory
predicates like `\valid` become lookups in instrumented shadow-memory
tables. The same contract can thus be verified statically (WP), analyzed
abstractly (Eva), or monitored dynamically — one spec, three consumers,
which is the real payoff of a common annotation language. **Slicing/PDG**
compute program-dependence-graph-based reductions materialized as new
projects. **From/InOut** compute (and cross-check) the `assigns \from`
dependencies via Eva. **Server + Ivette**: the old GTK GUI is replaced by a
headless JSON request protocol (`plugins/server/`) with an Electron/React
front end (`ivette/`) — analysis as a service, UI decoupled. **instantiate**
generates *typed* specializations of `void*` libc contracts (e.g.
`memcpy_int`) so WP's typed memory model can digest them.

## 7. share/libc: the ACSL-specified C library

~100 headers plus ~20 reference implementations, every function carrying a
contract. Representative (`string.h`):

```c
/*@ requires valid_dest: valid_or_empty(dest, n);
  @ requires valid_src: valid_read_or_empty(src, n);
  @ requires separation:
  @   \separated(((char*)dest)+(0..n-1), ((char*)src)+(0..n-1));
  @ assigns ((char*)dest)[0..n-1] \from ((char*)src)[0..n-1];
  @ assigns \result \from dest;
  @ ensures copied_contents: memcmp{Post,Pre}((char*)dest,(char*)src,n) == 0;
  @ ensures result_ptr: \result == dest;  @*/
extern void *memcpy(void *restrict dest, const void *restrict src, size_t n);
```

Conventions worth noting: named requires/ensures clauses (machine-checkable
error references); multi-behavior contracts with `assumes` splits
(`memchr`'s `found`/`not_found`); logic-function mirrors of C functions
(`strlen` the logic function specifies `strlen` the C function); helper
predicates (`valid_or_empty`, `non_escaping`); allocation modeled by a ghost
`__fc_heap_status` plus an `axiomatic dynamic_allocation` block with an
`is_allocable` predicate; `errno` as a ghost variable; reference `.c`
implementations carrying full loop invariants/variants. For our
libc-formalization line this corpus is the most valuable single artifact in
this repo's `third-party/`: a field-tested inventory of *what libc
contracts need to say*, independent of any proof technology (cf. the
survey in [LIBC-FORMALIZE.md](../LIBC-FORMALIZE.md); fv-libc gives
implementations, `share/libc` gives specifications).

## 8. Trust story

Nothing here is foundational: Eva's soundness is careful OCaml engineering
plus literature; WP trusts Why3 and the SMT portfolio (Coq export exists
but is not the default path); E-ACSL trusts its instrumentation; the kernel
trusts CIL normalization. The platform's counterweights are *redundancy*
(different analyses on the same properties), *explicit hypotheses*
(consolidation makes assumptions visible rather than absent), and
industrial validation. It is the opposite bet from RefinedC's — breadth,
automation, and C-as-it-is, versus a machine-checked core on a C subset —
and the two reviews bracket the design space for our libc work.

## 9. Takeaways

1. **The consolidation ledger is the design to steal.** Statuses with
   explicit hypothesis lists, lattice consolidation, cycle detection with
   declared-legal exemptions, `Valid_under_hyp` and `*_but_dead` as
   first-class verdicts. Our tower already combines heterogeneous evidence
   (Lean proofs, Coq ports, QEMU fuzzing, riscv-coq cross-checks,
   factored hypotheses in `core_refines`); today that ledger lives in
   markdown (TCB.md, RESUME files). Frama-C shows what mechanizing it
   looks like — and that vacuity (`_but_dead`) and circularity must be
   handled, not hoped away.
2. **Alarms-as-annotations** — analyses communicating by *writing
   assertions into the program* in a shared spec language — is the cleanest
   decoupling of "find the obligations" from "discharge the obligations"
   in this survey. RTE/Eva produce; WP/E-ACSL/humans consume; the ledger
   keeps score.
3. **`assigns \from`** is a spec construct our libc layer should adopt:
   our borrow discipline gives separation, but *functional dependency*
   ("output bytes come from these input bytes") is orthogonal, cheap to
   state, and powers dependency-style reasoning we'll eventually want.
4. **`check`/`assert`/`admit`** — verify-and-assume vs verify-only vs
   assume-only — is a three-valued annotation discipline strictly better
   than the usual two; trivially adoptable in our spec conventions.
5. **Per-function memory-model selection with declared hypotheses** (WP)
   is the pragmatic middle way between one-true-memory-model and unsound
   simplification — structurally the same move as our factored hypotheses,
   done systematically.
6. **`share/libc` is a mining source**: when we write Lean contracts for
   strlen/memcpy/malloc, the requires/assigns/ensures inventory (including
   the ghost heap-status and errno modeling) is already field-tested here;
   translation beats invention.
7. **One spec language, three consumers** (static AI / deductive / runtime
   monitoring) is ACSL's deepest achievement and the reason the platform
   coheres. Any spec layer we design for LowIR/libc should be written as
   if a second and third consumer will exist.
