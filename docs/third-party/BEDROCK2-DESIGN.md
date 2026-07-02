# bedrock2 — design choices

An analysis of `third-party/bedrock2/`: MIT PLV's umbrella project (checkout
`db4efdbf`, Rocq-era master) for **verified low-level programming**: a
minimal C-like language embedded in Coq with a separation-logic program
logic, a verified compiler to bare-metal position-independent RISC-V machine
code, a proof that the **Kami 4-stage pipelined processor** implements the
RISC-V spec, and an end-to-end theorem about an IoT lightbulb running on an
FPGA — the only project in our third-party set whose theorem reaches
*hardware*. It also contains **LiveVerif**, a framework for writing C-like
programs interactively inside a Coq proof goal. (Note: this repo already
depends on bedrock2's substrate — `coqutil`, `riscv-coq`, and bedrock2
itself are on our Coq load path, and our MEMORY-BORROWS/LOWIR work is
consciously adjacent.)

Overarching themes:

1. **Omnisemantics everywhere**: one judgment shape — `exec c s P`, "all
   nondeterministic branches from `s` reach `P` and none fail" — serves as
   semantics, program logic backbone, and compiler-proof vehicle.
2. **Minimality as a feature**: one data type (word), no function pointers,
   no recursion, no nonterminating programs except the top-level event loop
   — each restriction is load-bearing (bounded stack, simple logic,
   liveness via one pattern).
3. **Side channels and costs are first-class**: leakage traces and metric
   counters are semantic strata threaded through the *compiler theorem*, not
   an afterthought.

## 1. The language: deliberately tiny

`bedrock2/Syntax.v`: expressions over a single word type (literals, vars,
loads, inline tables, 14 binary ops, ternary `ite`); commands are `set`,
`store`, `stackalloc`, `cond`, `seq`, `while`, `call`, `interact` (FFI).
Functions are `(params, rets, body)` triples — multiple return values, no
nesting. The README states the non-features as policy: **no function
pointers, no recursion** ("we always want to prove that we don't run out of
stack space"), **no nontermination** except the top-level event loop.
`stackalloc` gives block-scoped scratch memory (the callee picks the
address nondeterministically — see `pick_sp` in the compiler proof).
Memory is a partial map `word → byte`; locals are a map `string → word`.
Concrete syntax is Coq custom-entry notation (`func! (x) ~> (r) { … }`), so
programs are Coq terms with C-like faces — no external parser at all.

## 2. Omnisemantics

`bedrock2/Semantics.v` defines big-step `exec : cmd → state → (state → Prop)
→ Prop` in the *omnisemantics* style (the ACM TOPLAS paper is the stated
reference): the judgment carries the postcondition, and asserts that every
nondeterministic branch terminates in it. Two lemmas make it a logic:
`weaken` (postconditions are covariant) and `intersect` (two provable
postconditions imply their conjunction — this is where the "all branches"
reading pays off; an ordinary big-step relation doesn't validate it).
Compared to our functional-big-step/CakeML style, omnisemantics trades an
executable evaluator for built-in ∀-over-nondeterminism — well suited here
because external calls are genuinely nondeterministic and there's no clock.

**External calls** (`interact`): the distinctive `mGive`/`mReceive` design —
the program *splits off* a chunk of memory and hands it to the environment,
which returns result values plus a chunk `mReceive` that is re-joined. The
environment is specified by an abstract `ext_spec : trace → mGive → action →
args → (mReceive → rets → Prop) → Prop` — postcondition-style, like
everything else — with an `ext_spec.ok` interface (unique footprint, weaken,
intersect). I/O is a trace of `((mGive, action, args), (mReceive, rets))`
events. This memory-passing FFI is strictly richer than CakeML's byte-array
oracle: ownership transfer across the boundary is native. (Directly relevant
to how our libc layer should model syscalls/MMIO.)

## 3. The program logic

- **WP as a Gallina function** (`WeakestPrecondition.v`): the VC generator is
  structural recursion over syntax — except `while` and `call`, which
  "fall back" to the inductive `exec` (a fixpoint WP wouldn't terminate).
  Proved both sound and complete w.r.t. `exec`
  (`WeakestPreconditionProperties.v`). So users get a computable VC
  generator, and the meta-theory keeps the inductive semantics as ground
  truth.
- **Specs** are `spec_of name : env → Prop` — predicates over the function
  environment, instantiated with separation-logic pre/posts over memory and
  the I/O trace.
- **Loops** (`Loops.v`): invariant + well-founded measure lemmas, plus
  "tailrec" variants whose invariant is phrased as a *cumulative*
  postcondition with ghost state — the workhorse patterns for systems loops.
- **Separation logic** comes from coqutil (`sep` as map-split); on top:
  `purify` (extract pure facts from sep clauses), the **frame rule proved as
  a theorem about `exec`** (`FrameRule.v` — local reasoning is a lemma, not
  a primitive), and **heaplet-wise hypothesis management**
  (`HeapletwiseHyps.v`): instead of one monolithic `sep`-conjunction
  hypothesis, keep *one hypothesis per heaplet* (`m1 |= P1`, `m2 |= P2`, …)
  with a tree of disjoint unions behind them, and use **ramification**
  (`sep calleePre (wand calleePost callerPost)`) to avoid instantiating
  frame evars prematurely. This is proof-engineering UX built into the
  logic's data representation — the enabling substrate for LiveVerif.

## 4. Leakage and metrics: four semantic strata

The same `exec` is defined four times (`SemanticsRelations.v` embeds them):
plain, **leakage** (`LeakageSemantics.v`: every load/store address, branch
condition, division/shift operand appends a `leakage_event`; ext_spec
extended so externals declare what they leak), **metric**
(`MetricSemantics.v`: instruction/load/store/jump counters with per-construct
cost functions), and both. The point is not source-level reasoning alone:
the **compiler theorem transports them** — each phase's correctness record
carries a leakage-trace *transformer* (`k2' = f k1'`) and a metric
inequality (target-cost delta ≤ source-cost delta). So constant-time
reasoning done at the source (leakage trace independent of secrets) yields a
statement about the machine-code leakage trace, addresses and all. This is
the most worked-out "compiler preserves side-channel discipline" design in
our survey.

## 5. The compiler

Pipeline (`compiler/Pipeline.v`):

```
cmd —FlattenExpr→ FlatImp(string) —UseImmediate→ —DeadCodeElim→
   —RegAlloc→ FlatImp(Z) —Spilling→ FlatImp(Z registers)
   —FlatToRiscv→ list Instruction —instrencode→ bytes
```

- **FlatImp** is the single mid-level IR: statements only, no nested
  expressions, *parameterized by the variable type* — `string` before
  register allocation, `Z` after. One IR datatype, two instantiations —
  a cheaper trick than two languages.
- **Phase framework**: a generic `phase_correct` record (valid-preservation +
  post-preservation with leakage transformer and metric bound) composed by a
  generic fold — CompCert's `mkpass` chain in miniature.
- **Register allocation = unverified allocator + verified checker**
  (`RegAlloc.v`): a greedy live-interval allocator runs untrusted; a checker
  traverses source and target in lockstep maintaining a conservative
  correspondence `list (srcvar × impvar)` (intersection at joins, fuel-bound
  fixpoint at loops). Same "prove the checker" economics as CompCert —
  chosen even in a research-scale compiler.
- **Spilling** (`Spilling.v`): variables ≥ 32 go to a stack frame allocated
  by one `SStackalloc` at function entry; three reserved temporaries load/
  store spilled operands around each use. Because recursion is banned, the
  *total* stack requirement is computed statically per program
  (`req_stack_size`) and becomes a precondition of the correctness theorem —
  the "we never run out of stack" promise made checkable.
- **FlatToRiscv**: per-statement lemmas against the riscv-coq monadic
  semantics, lifted to `runsTo` (nondeterministic multi-step "eventually").
  Code is position-independent (relative jumps; function positions from a
  compile-time map). Encoding reuses riscv-coq's verified
  `encode`/`decode` bijection, and a lemma converts byte-level `ptsto_bytes`
  into an instruction-level `program` separation predicate — bytes in
  memory, not an AST, are what the theorem talks about.
- **MMIO** (`compilerExamples/MMIO.v`): the abstract `ext_spec` and its
  compilation are *parameters* of the whole pipeline (`compile_ext_call`);
  the FE310 instantiation compiles each interaction to exactly one load or
  store instruction. The compiler never knows what I/O means.

**The event-loop top level** (`ToplevelLoop.v`, `CompilerInvariant.v`): a
program is `init` + `loop`, compiled with a preamble that sets the stack
pointer, calls `init`, then enters `call loop; jal -4` forever. Correctness
of this *non-terminating* system is stated as an invariant `ll_inv =
runsToGood_Invariant ll_good`: the machine is always finitely many steps
from a "good" state (loop entry, related to a source state), where the
step count may differ per nondeterministic branch — hence `runsTo` (◊)
rather than `∃ n, steps n`. The proof discipline is establish / preserve /
use. This is the cleanest published pattern for "terminating pieces, forever
system" — directly relevant to a bare-metal hex0-style loop.

## 6. Down to the gates: riscv-coq, Kami, end2end

- **riscv-coq** (dep): the RISC-V spec as a free monad over primitives
  (`getRegister`, `loadWord`, …), mechanically close to MIT's Haskell
  riscv-semantics (some files literally translated); platforms instantiate
  the monad — `MinimalMMIO` gives the small-step omnisemantics used here.
  One ISA spec shared between the compiler proof and the processor proof is
  the whole point.
- **processor/**: proves the **Kami** rv32i 4-stage pipelined processor
  (Kami: a Bluespec-style hardware DSL in Coq; extracts to Bluespec →
  Verilog → FPGA) implements riscv-coq: a `states_related` relation between
  hardware states (program in ROM register file, data memory, pipeline
  bookkeeping) and ISA states, with `kamiStep_sound` allowing *silent* Kami
  steps (pipeline stages, instruction-memory init) that don't correspond to
  ISA steps. Assumptions: MMIO-only externals, no interrupts/CSRs.
- **end2end/**: composes program-logic proof (WP for `init`/`loop` bodies) →
  compiler invariant (`ll_inv`) → Kami refinement into
  `end2end_lightbulb`: *if the compiled bytes sit at ROM address 0 and the
  Kami processor exhibits trace `t`, then `t` corresponds to MMIO events
  forming a prefix of `goodHlTrace`* — the lightbulb spec, written in a
  small trace-predicate combinator language (`+++` sequencing, `|||`
  choice, `^*` iteration): boot sequence, then forever (receive packet and
  toggle light | reject garbage | poll empty). The verified program includes
  the SPI driver and LAN9250 ethernet handling; specs are I/O-trace
  predicates plus separation logic.
- **TCB** of the demo: Coq kernel, the riscv-coq and Kami semantics, and —
  unverified — the Bluespec compiler, Verilog toolchain, FPGA silicon, and
  the ethernet card. Everything from C-like source to ISA behavior is
  theorem-covered; the hardware synthesis chain is not.

There is also an **unverified C export** (`ToCString.v`) that prints
bedrock2 ASTs as portable C (with helper functions to pin down shifts,
division, endianness) — the pragmatic second backend, clearly outside the
theorem.

## 7. LiveVerif: the proof goal as the editor

`LiveVerif/` turns program construction inside-out: instead of writing a
program and verifying it, you *derive* it. `Derive f SuchThat
(fun_correct! f)` opens a goal in which the implementation is an evar; the
user writes C-like statements one at a time inside comment-delimited
notation blocks (`.**/ i = i + 1; /**.`), and each snippet fires the
corresponding WP lemma (`LiveRules.v`), advances the symbolic state, and
extends the evar. The `.v` file itself *reads as a C file* (specs in
`/**# requires … ensures … #**/` blocks; the C text lives in what look like
comments), and the goal always displays remaining-obligations + heaplets —
one hypothesis per heaplet, array slices split and merged by `zify`/
bottom-up-simplification automation; loop measures and ghost state are the
one thing the user must supply. The final theorem lands in ordinary
`WeakestPrecondition.call`, so derived functions feed the verified compiler
unchanged. Examples scale surprisingly far: memset, linked-list reversal,
BST insert/delete with a verified freelist malloc, a 238KB crit-bit tree
development, an e1000 network driver fragment. `LiveVerifEx64` is the same
framework with `Load LiveVerifBitwidth` picking the 64-bit word instance —
the whole framework is bitwidth-generic.

## 8. Takeaways

bedrock2 is the closest neighbor to this repo's own stack (shared substrate,
shared RISC-V target, same "no recursion, bound the stack" instincts). Worth
holding onto:

1. **Omnisemantics is the third semantics style** in our survey (CompCert:
   small-step + simulations; CakeML: functional big-step + clock;
   bedrock2: postcondition-carrying big-step). Its `intersect` property and
   native nondeterminism are the selling points; no executable evaluator is
   the price. For LowIR we chose clocked-functional; omnisemantics is the
   design to revisit if external nondeterminism ever dominates.
2. **The event-loop liveness pattern** (`ll_good` + `runsToGood_Invariant`,
   establish/preserve/use) is the reusable answer to "my verified pieces
   terminate but my system doesn't" — the shape a verified hex0-as-a-service
   or driver loop should take.
3. **mGive/mReceive external calls** — memory ownership transfer in the FFI
   signature itself — is the right model for our syscall/MMIO boundary in
   the libc formalization (cf. MEMORY-BORROWS.md's shared-input/unique-output
   borrows; the rhyme is exact).
4. **Leakage and cost as strata carried through compilation** shows how to
   make constant-time and WCET-ish claims *compiler-transported* rather than
   source-only — the design to copy if our tower ever states timing
   properties.
5. **Heaplet-wise hypotheses + ramification** is separation-logic proof UX
   engineered into data representation; our Slice/Borrow layer automation
   should study it before inventing its own.
6. **LiveVerif** is the most radical authoring UX here — program-by-proof
   with the goal as the editor. Even if we never adopt it, "the artifact
   file doubles as readable C" is a presentation trick worth remembering.
7. The **hardware rung** (Kami) marks where our tower currently stops: our
   TCB ends at the ISA model, exactly where bedrock2's processor proof
   begins. If we ever want to push below the ISA, this is the reference
   architecture — including its honesty that Bluespec→Verilog→FPGA remains
   trusted.
