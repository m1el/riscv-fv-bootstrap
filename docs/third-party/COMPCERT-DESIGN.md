# CompCert — design choices

An analysis of `third-party/CompCert/`: **CompCert 3.17** (Feb 2026 release,
checkout `d00a4660`), the formally verified C compiler in Coq/Rocq — the field's
reference artifact for what "verified compiler" means. It compiles a large
subset of C99 to ARM/AArch64, PowerPC, RISC-V, and x86, with a machine-checked
proof that the generated assembly behaves as the C semantics prescribes.
(License note: unlike everything else vendored here, CompCert is *not* free
software — the INRIA/AbsInt non-commercial license.)

This document records the design decisions and their stated rationale. Three
overarching themes:

1. **The theorem is shaped around undefined behavior**: correctness is
   *behavior improvement* under a backward simulation — programs with defined
   behavior are preserved exactly; going-wrong programs may be "improved."
   Everything upstream (nondeterministic C semantics, `Vundef`, stuck states)
   and downstream (what the theorem guarantees users) is arranged around this.
2. **One concern per IR**: eleven languages, each rung of the ladder changing
   exactly one thing, each pass proved by a forward simulation chosen from a
   small toolbox of diagram shapes.
3. **Prove the checker, not the heuristic**: wherever cleverness pays
   (register allocation, code layout, inlining decisions), the clever part is
   untrusted OCaml and a small Coq validator certifies each output —
   translation validation as a proof-effort lever.

## 1. The correctness contract

### Behaviors and improvement

A program behavior (`common/Behaviors.v`) is one of `Terminates trace int`,
`Diverges trace` (silent infinite loop after a finite trace), `Reacts traceinf`
(infinite observable trace), or `Goes_wrong trace`. Observables are **traces of
events** (`common/Events.v`): syscalls, volatile loads/stores, annotations —
deliberately *not* memory states or raw pointers, "because these are not
preserved literally during compilation"; event values may mention pointers only
as offsets from *named public globals*.

The compiler's contract (`driver/Compiler.v`, `driver/Complements.v`):

```coq
Theorem transf_c_program_correct: forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).

Theorem transf_c_program_preservation: forall p tp beh,
  ... program_behaves (Asm.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh'
            /\ behavior_improves beh' beh.
```

where `behavior_improves beh1 beh2 := beh1 = beh2 ∨ (beh1 = Goes_wrong t ∧ t
prefix of beh2)`. So: **every behavior of the assembly is a behavior of the C
program, except that a source execution which goes wrong may have been replaced
by anything extending its trace**. For source programs with no undefined
behavior, this collapses to exact behavior preservation
(`transf_c_program_is_refinement`); `Complements.v` accordingly restricts the
"specification preservation" corollary to *safety-enforcing* specifications
(those that exclude `Goes_wrong`). Undefined behavior is not detected or
prevented — it is precisely the license the compiler is given.

### Forward simulations composed, backward simulation delivered

Each pass proves a **forward** simulation (source step ⇒ target steps), which
is much easier than backward because the target of a compiler is *more*
deterministic than the source. `common/Smallstep.v` provides the toolbox: a
generic `fsim_properties` record (match relation indexed by a well-founded
order, so the source may stutter with a decreasing measure) and derived
diagram shapes — lockstep, "plus", "star with measure" — so each pass picks the
weakest diagram it needs. The chain of ~20 forward simulations composes, and
then a single generic theorem flips it: forward simulation + **receptive**
source + **determinate** target ⇒ backward simulation. Receptiveness and
determinacy are per-semantics obligations; external nondeterminism (I/O
results) is quarantined in a coinductive `world` oracle (`Determinism.v`), so
"determinate" means deterministic *given the world*. This
forward-then-flip architecture is the single most reused idea in the
literature (our LowIR `compile_sim` plan in
[LOWIR-DESIGN.md](../LOWIR-DESIGN.md) follows it too).

## 2. C semantics: nondeterminism first, strategy second

CompCert C (`cfrontend/Csem.v`) gives expressions a **nondeterministic
reduction semantics** (Wright–Felleisen contexts) in which binary operands may
reduce in either order — faithfully modeling C's unspecified evaluation order —
and undefined behavior is a **stuck state**. The subtle part (comment at
`Csem.v:403-421`): a program is safe only if *no* interleaving can go wrong, so
the `not_stuck` predicate demands every subexpression in every reduction
context be reducible or a value — `(x=1) + (10/x)` with `x=0` is wrong even
though one order succeeds.

The compiler itself doesn't implement the nondeterministic semantics; it
implements one **strategy** (`Cstrategy.v`): effectful subexpressions first,
leftmost-innermost, simple (pure) subexpressions last, big-step. Two theorems
tie it down: every strategy step is simulated by the nondeterministic
semantics, and — the important direction — if a state is *safe* in the
nondeterministic semantics, the strategy can make progress. Net effect: the
correctness theorem quantifies over the nondeterministic source semantics
(all evaluation orders), while the proof only follows one order. A
whole-program C interpreter (`Cexec.v`, extracted to OCaml) animates the
semantics executably — the semantics is *testable*, which is how CompCert
built confidence that the Coq definition of C means C.

Downstream, `SimplExpr` compiles CompCert C to **Clight**, where expressions
are pure and side effects live only in statements (assignments and calls are
statements; temporaries are distinguished from addressable locals) — the same
pure-expression discipline as VIR-SST and Radix, here established by pass #1
and exploited by everything after. `SimplLocals` then promotes
non-address-taken scalar locals from memory to temporaries — register
promotion done as a *source-to-source* pass where it's easiest to prove.

## 3. The memory model

The most influential single component (`common/Memtype.v`, `Memory.v`,
`Memdata.v`):

- **Blocks, not a flat address space.** An address is `(block, offset)`;
  every allocation gets a fresh block (`nextblock` increments forever, blocks
  are never reused). Separation between allocations is thus *structural* —
  pointer arithmetic cannot walk out of one object into another — which is
  what makes alias reasoning and freshness proofs tractable. (Same trick as
  Radix's never-reuse bump heap, industrial-strength.)
- **Two permissions per byte** (`Cur` and `Max`, ordered `Freeable > Writable
  > Readable > Nonempty`): `Max` only ever decreases over a block's lifetime,
  while `Cur` may be temporarily lowered and restored by external calls — the
  stated design reason is to let external calls model lending/borrowing of
  memory without violating monotone facts the proofs rely on.
- **Bytes are `memval`s**: `Undef`, a concrete `Byte`, or a `Fragment v q i` —
  the i-th byte of value `v`. Pointers stored to memory become fragment
  sequences; `decode_val` reconstructs the pointer only if *all* fragments
  match, otherwise yields `Vundef`. So "reading a pointer as bytes" is
  defined-but-useless rather than an error — bit-level realism where it's
  cheap, abstraction where it matters.
- **`Vundef` is the UB carrier at the value level** (`Values.v`): it inhabits
  every type, and `Val.lessdef` ("less defined than") lets the compiler
  *refine* undefined values to anything. Two relations between memory states
  carry the whole backend proof: **`extends`** (same blocks, target may have
  more permissions and more-defined contents) and **`inject`** (a partial map
  `block → option (block, offset)` letting compilation coalesce, relocate, and
  drop blocks — e.g. spilling locals into a single stack frame). `Mem.inject`
  + `Val.inject` + the no-overlap condition are the vocabulary in which
  Cminorgen, Stacking, and separate compilation are all stated.
- The model is exposed to the proofs as an **axiomatized module type**
  (`Memtype.v`) with `Memory.v` as its realization — passes depend on the
  interface contracts, not the implementation.

## 4. The IR ladder

Eleven languages, each rung changing one thing (`backend/*.v` headers state
this explicitly):

| language | what changes | why this rung exists |
|---|---|---|
| CompCert C | — | full nondeterministic C semantics |
| Clight | expressions pure | side effects sequenced once and for all |
| C#minor | C ops → machine-neutral ops | drop C typing; explicit casts |
| Cminor | locals w/o addresses; explicit stack block | last structured-control language |
| CminorSel | target-specific `Op`/addressing modes | instruction selection via per-target "smart constructors" (`SelectOp.v`), incl. div-by-constant → multiply, 64-bit ops split on 32-bit targets |
| RTL | CFG of three-address code, ∞ pseudo-registers | *the* optimization IR: all dataflow analyses and optimizations happen here |
| LTL | pseudo-regs → machine regs + abstract stack slots; basic blocks | output of register allocation |
| Linear | CFG → instruction list with labels | code layout decided |
| Mach | abstract slots → concrete frame offsets | stack frames built; callee-save protocol proved (`Stacking.v`, `Bounds.v`) |
| Asm (per target) | real ISA, registers as a total map | pseudo-instructions remain, expanded later unverified |

Optimizations (all on RTL): tailcall recognition, inlining (proved correct;
*which* functions to inline is an OCaml oracle), constant propagation +
target-specific strength reduction, CSE by value numbering over extended basic
blocks, bit-level dead-code elimination, unused-global elimination, plus
LTL branch tunneling (union-find over branch chains). All are backed by one
**generic Kildall worklist solver** (`Kildall.v`) over `SEMILATTICE` modules
(`lib/Lattice.v`), instantiated forward (value analysis, `ValueAnalysis.v`,
a real abstract interpreter with ranges/pointer provenance domains) and
backward (liveness, neededness `NeedDomain.v`). Deliberately absent: loop
optimizations, scheduling, vectorization — CompCert optimizes for provability
per watt, and a `Renumber` pass exists solely to restore postorder numbering
so Kildall converges fast.

Two infrastructure idioms recur: monadic translations (RTLgen and Inlining
build CFGs in a state monad whose invariant — nodes only ever added — is what
the simulation proofs lean on), and **bounded iteration** (`lib/Iteration.v`:
fixpoints run under a `10^12` iteration budget returning `option`, explicitly
"to avoid defining painful well-founded orderings" — failure is provable-about
but never observed; our Coq ports fight the same battle).

## 5. Prove the checker, not the heuristic

The signature CompCert methodology, stated crisply in `Linearize.v`:
"a piece of untrusted Caml code implements the … heuristics, and the resulting
[output] is checked for correctness by Coq functions that are proved to be
sound."

- **Register allocation** (`Allocation.v` / `IRC.ml`): iterated register
  coalescing — a serious, mutable, graph-coloring allocator — lives in OCaml.
  Coq validates each output function (Rideau–Leroy checker): the LTL block
  structure must match the RTL instruction shape-for-shape, and a backward
  liveness/equation analysis certifies the assignment. The allocator can be
  arbitrarily clever or buggy; only the checker is trusted, per-run.
- **Linearization** (`Linearize.v` / `Linearizeaux.ml`): trace-picking is
  OCaml; Coq only checks "every reachable node appears exactly once" — the
  comment notes the beauty that correctness needs only this weak property.
- **Switch compilation** (decision trees, `Switch.v`), **inlining policy**,
  **branch prediction** (`RTLgenaux.more_likely`), **if-conversion policy**:
  all OCaml oracles behind Coq `Parameter`s.

The seam is visible in `extraction/extraction.v`: each heuristic is a Coq
`Parameter` realized by `Extract Constant … => "Ocaml.function"`, and the
build fails if any axiom is left unrealized. Command-line optimization flags
enter the *proof* as `Compopts.v` parameters (each optional pass is verified
in both on and off configurations) and are realized as `!Clflags.option_*`
references.

## 6. External calls and volatiles

External functions are axiomatized by an interface of proof obligations
(`Events.v::extcall_properties`): well-typedness, at most one event per call,
cannot create/invalidate blocks, cannot increase `Max` permissions, cannot
write without permission, must commute with `extends` and `inject`, and must
be receptive + determinate over traces. Every compiler pass is proved sound
against *any* external world satisfying these axioms. Volatile accesses are
compiled to events (with the quirk, noted in `SimplExpr.v`, that volatile
struct/bitfield accesses do *not* produce events — matching GCC practice).

## 7. Separate compilation

Since 3.x (following Kang et al., POPL 2016, cited in `Linking.v`), the
correctness theorem is compositional over linking: a `Linker` type class
(`link : A → A → option A` plus a `linkorder` refinement preorder) is defined
for each language, each pass's `match_prog` relation is proved to commute with
linking (`TransfLink`, discharged by type-class machinery in the `mkpass`
chain of `Compiler.v`), and the payoff is:

```coq
Theorem separate_transf_c_program_correct:
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program, link_list asm_units = Some asm_program
    /\ backward_simulation (Csem.semantics c_program) (Asm.semantics asm_program).
```

i.e. compile the units separately with the *same* compiler, link the results,
and whole-program correctness still holds. (Linking with foreign-compiled
code is out of scope — that's the harder "compositional compiler correctness"
problem this design deliberately sidesteps.)

## 8. Trust story

What is verified: every pass from CompCert C AST to Asm AST, the linking
theorem, the memory model, floats (via the vendored **Flocq** IEEE-754
formalization — `lib/Floats.v` bridges bit-level and real-number reasoning,
including verified NaN payload handling), machine integers
(`lib/Integers.v`: `Z` carrying a range proof, modulus `2^wordsize`), and the
**parser automaton** — `cparser/Parser.vy` is Menhir's Coq backend, whose
LR(1) automaton is accompanied by MenhirLib proofs of soundness/completeness
w.r.t. the grammar.

What is trusted (assembled from the repo; cf. our own [TCB.md](../TCB.md)
exercise):

- the C **preprocessor** (external `cpp`), the **lexer** and pre-parser, and —
  the big one — **elaboration** (`cparser/Elab.ml`: typechecking, desugaring,
  initializer normalization; thousands of lines of OCaml producing the AST
  the theorem starts from);
- **`Asmexpand.ml`** (pseudo-instruction expansion, per target) and
  **`PrintAsm.ml`** (assembly text emission) — the theorem ends at the Asm
  AST, not at bytes;
- the external **assembler and linker**;
- the **runtime library** (`runtime/`): hand-written C/asm for 64-bit ops on
  32-bit targets, `va_arg`, etc.;
- Coq's **extraction** to OCaml, the OCaml compiler, and Coq itself
  (`make check-proof` at least re-checks the proofs with `coqchk`);
- the per-run outputs of the OCaml heuristics are *not* trusted (validated),
  but the validators' Coq proofs are part of the checked development.

Also in-tree: `export/` (**clightgen**) prints the Clight AST of a C file as a
Coq term — the bridge by which VST does source-level program verification on
top of CompCert's compiler correctness; and `tools/`, `pg/` etc. for the
two-stage build (check proofs → extract → build `ccomp`).

## 9. Takeaways

CompCert is already the load-bearing precedent for this repo's LowIR
`compile_sim` plan ([LOWIR-DESIGN.md](../LOWIR-DESIGN.md) §4); points worth
holding onto, some reinforcing what Radix/Verus showed:

1. **State the theorem you can afford, precisely.** Behavior improvement +
   safety-enforcing specifications is a carefully drawn boundary around UB —
   the guarantee is strong exactly where the source program is defined.
   The same honesty discipline as Radix's "no progress theorem" note, at 100×
   scale.
2. **Forward-then-flip.** Prove forward simulations per pass (with the
   star/plus/measure toolbox), get the backward simulation once from
   source-receptiveness + target-determinacy. Our determinism lemmas play the
   same structural role.
3. **Translation validation is the cheapest proof there is** for
   heuristic-heavy passes — prove a per-output checker, extract the heuristic
   as an axiom-realized-in-OCaml. Directly applicable whenever our tower
   needs a register allocator or scheduler.
4. **One concern per IR** keeps every simulation proof small; the two
   relations that cross all rungs (`extends`, `inject`) are designed once,
   in the memory model, and reused everywhere.
5. **Executable semantics as a validation tool**: `Cexec.v` (and the whole
   reference-interpreter idea) is how you convince yourself a 10k-line
   semantics of a real language is the *right* semantics — the analogue of
   our QEMU cross-checks and `riscv-coq` agreement proofs (task #7).
6. **Nondeterministic spec, deterministic implementation**: quantify the
   theorem over all evaluation orders, prove via one strategy plus a progress
   theorem. Worth remembering if our C-level layer (libc formalization) ever
   confronts unspecified evaluation order.
