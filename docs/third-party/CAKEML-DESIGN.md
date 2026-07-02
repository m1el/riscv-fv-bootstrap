# CakeML & Pancake — design choices

An analysis of `third-party/cakeml/`: **CakeML**, the verified compiler for a
substantial subset of Standard ML, developed in **HOL4**, and **Pancake**, the
C-like verified systems-language compiler built from the lower half of the
CakeML backend (checkout `f56a9daba`, 2026-era master). CakeML is CompCert's
methodological counterpart and rival: where CompCert verifies a compiler for
an existing unsafe language down to an assembly AST and extracts to OCaml,
CakeML verifies a compiler for a safe language **down to concrete machine-code
bytes** and produces its own binary **inside the logic** — no extraction, no
trusted pretty-printer, and a self-compiled (bootstrapped) compiler binary
covered by theorem.

Overarching themes:

1. **Functional big-step semantics with a clock, everywhere.** One semantic
   style — a fuel-clocked `evaluate` *function* — is used for the source
   language and every one of ~10 ILs, and every pass is proved by induction
   on `evaluate` rather than by small-step simulation diagrams.
2. **Nothing leaves the logic.** The compiler is a HOL function; the shipped
   binary is obtained by *evaluating that function on itself* in the logic
   (`cv_compute`), so extraction, OCaml, and the assembler are simply not in
   the TCB.
3. **Verify the algorithm, not just the checker.** Where CompCert validates
   untrusted OCaml heuristics per-run, CakeML verifies the register
   allocator, the GC, and the assembler themselves as HOL functions.

## Part I — CakeML

### 1. Semantics: functional big-step with a clock

The source semantics (`semantics/evaluateScript.sml`) is a *function*
`evaluate : decs × state → state × result`, not a relation — the design
argued in the "Functional Big-Step Semantics" paper and repeated at every
level of the compiler. A `clock` in the state is decremented at function
application; hitting zero returns `Rtimeout_error`. Termination of the
definition itself is handled by a `fix_clock` wrapper that makes HOL4's
termination checker accept the recursion, then is cleaned away
(`evaluateScript.sml:10-17`); the key lemma is that evaluation never
increases the clock.

The top-level observational semantics (`semanticsScript.sml`) quantifies
over the clock: a program **Terminates** if some clock suffices, **Diverges**
if every clock times out — with the (possibly infinite) I/O trace defined as
the least upper bound (`lprefix_lub`) of the finite event lists produced at
each clock — and **Fails** on a runtime type error. This is a genuinely
different factoring from CompCert: divergence is not coinductive execution
but a *limit over fuel*, which keeps every proof a plain induction.

Alternative semantics (relational big-step, small-step, interaction trees)
exist in `semantics/alt_semantics/` with equivalence proofs, but the README
notes they are "no longer used in the CakeML development" — kept for external
projects. The functional style won.

### 2. FFI: the oracle

The external world (`semantics/ffi/ffiScript.sml`) is a user-supplied
**oracle**: `oracle : ffiname → 'ffi → bytes → bytes → oracle_result`,
threaded through the state along with the accumulated `io_events` (each event
records the FFI name, immutable args, and mutable byte-array before/after).
The oracle may end execution (`Oracle_final`, e.g. `FFI_failed`).
Nondeterminism of the environment is captured by parameterizing all theorems
over an arbitrary `'ffi` oracle — the analogue of CompCert's axiomatized
external calls, but concrete and executable. Observable behavior = the event
trace, exactly as in CompCert.

### 3. The correctness theorem, with an honest out-of-memory clause

`compiler/proofs/compilerProofScript.sml::compile_correct`: if the compiler
(itself a HOL function from command line + stdin to bytes) succeeds, then for
any machine state `ms` in which the produced code and data are `installed`,

```
machine_sem mc ffi ms ⊆ extend_with_resource_limit behaviours
```

where `behaviours` is the *source* semantics of the program, and
`extend_with_resource_limit` adds one thing: the machine may terminate early
with `Resource_limit_hit` after a *prefix* of a legitimate source trace.
That is the whole caveat — the compiled code either behaves exactly like the
source or runs out of memory and says so. Three notes:

- Parse and type errors are covered too: if compilation fails with
  `ParseError`/`TypeError`, the theorem says the *source semantics* is
  `CannotParse`/`IllTyped` — the front end is inside the theorem.
- `Fail` (undefined behavior) never needs to be "improved" as in CompCert:
  **type soundness** (`semantics/proofs/typeSoundScript.sml::semantics_type_sound`)
  proves well-typed programs never Fail, and the verified type inferencer
  gates compilation. The backend is proved correct for *all* programs
  (untyped ILs); typing only serves to rule out `Fail`.
- A stronger theorem (`compile_correct_safe_for_space`) upgrades ⊆ to = when
  a verified **cost semantics** shows the program fits in the given heap and
  stack (`is_safe_for_space`) — the "space cost semantics" line of work.

The front end is verified where CompCert trusts: the PEG parser is proved
sound *and complete* against the SML grammar
(`compiler/parsing/proofs/parserProofScript.sml`), and the type inferencer is
proved sound (its output type-checks) and complete (typeable programs are
accepted) (`compiler/inference/proofs/`).

### 4. The backend: twelve languages, each dropping one abstraction

The IR ladder (`compiler/backend/README.md`, per-file headers):

| IL | what it drops / gains |
|---|---|
| flatLang | modules gone; globals get slots; constructors become numbers |
| closLang | last language with closures; de Bruijn variables; where closure-call optimization happens (`clos_mti` multi-arg introduction — "vital for good performance", `clos_known` flow analysis + inlining, `clos_call` known-call extraction) |
| BVL | first-order, closed, multi-argument functions in a code table — closure conversion (`clos_to_bvl`) lays out generic-apply + partial-application stubs so curried calls are fast |
| BVI | `Handle` (exceptions) **merged into `Call`** so every function owns exactly one stack frame — "to keep things simple and uniform" (`bviScript.sml:18-27`); big integers split into word-size pieces |
| dataLang | imperative; explicit `MakeSpace` allocation statements that optimizations move and merge to batch allocator calls (`dataLangScript.sml:8-24`) — the hook for the space-cost semantics |
| wordLang | machine words, flat memory, a stack; SSA-style renaming, instruction selection (maximal munch), and register allocation happen here |
| stackLang | registers allocated; stack concrete; GC implementation *injected as stackLang code* (`stack_alloc`) |
| labLang | "soup of goto-like jumps"; target-neutral assembly |
| bytes | `lab_to_target` — the verified assembler |

Design highlights below the data abstraction line:

- **Value representation** (`data_to_word`): configurable pointer tagging
  (`tag_bits`/`len_bits`/`pad_bits`, header layout), small integers unboxed,
  bignums, per-ISA capability flags (`has_div`, `has_fp_ops`, endianness) —
  all in a config record so one proof covers every target.
- **Verified GCs** (`backend/gc/`): a copying collector and a generational
  collector, specified as HOL functions over an *abstract heap* of
  `DataElement`/`ForwardPointer` cells and proved to preserve reachable data;
  `data_to_word` proofs are parameterized by `gc_kind` (None | Simple |
  Generational). The collector that runs is the verified one, compiled into
  the binary as stackLang code — not a trusted runtime.
- **Register allocation is a verified algorithm**: IRC-style graph coloring
  written monadically in HOL (plus a linear-scan alternative), with parallel
  moves per Rideau–Leroy formalized (`backend/reg_alloc/`). Contrast
  CompCert's validate-the-OCaml-oracle. (An unverified SML copy exists in
  `unverified/reg_alloc/` only as a reference.)
- **The assembler is verified** (`lab_to_target`): instruction encoding via
  each target's `enc` function, two-pass label placement, and an iterative
  re-encode-until-offsets-converge loop — proved against per-ISA `asm`
  models (x64, ARMv7/v8, RISC-V, MIPS, ag32). The theorem reaches actual
  bytes in memory, closing the gap CompCert leaves at `PrintAsm.ml`.
- **Runtime code installation**: every IL's state carries a
  `compile_oracle`, so `Install` (used by the verified REPL / `eval`) is in
  the semantics and carried through every pass — a capability CompCert
  doesn't attempt.

The proof pattern at every rung is the same: define `state_rel` between
adjacent ILs (clock equality, code-table relation, oracle synchronization),
induct on `evaluate`. Config validity per target is one predicate
(`backend_config_ok`), and `cv_compute/` splits `asm_conf` out so the whole
backend can be evaluated fast in-logic per target.

### 5. Bootstrapping: the compiler binary is a theorem

The distinctive move (`compiler/bootstrap/`): the compiler is a HOL function;
the **translator** (`translator/`) synthesizes a CakeML program from it along
with a proof the program refines the function; then the compiler-as-HOL-
function is *evaluated in the logic* on that program — today via HOL4's
`cv_compute` fast evaluation (the `cv_translator/` gives compiler passes
`cv`-typed equations; the old `EVAL`-based route was orders of magnitude
slower) — yielding a theorem of the form "these bytes (`cake.S`) are the
output of `compile` on the compiler's own source", which composes with
`compile_correct` into: **this binary is a correct CakeML compiler**
(`x64BootstrapProofScript.sml::cake_compiled_thm`). The unverified
`unverified/sexpr-bootstrap/` path exists only to build a first binary
outside the logic conveniently; the verified claim doesn't depend on it.

### 6. The ecosystem: programs, not just a compiler

- **Translator** (`translator/`): proof-producing synthesis HOL → CakeML
  (`Eval`/`Arrow` refinement judgments), with a **monadic translator** for
  stateful/exceptional HOL functions. Write pure functions, get certified
  code — the workhorse for the compiler's own bootstrap and for most verified
  CakeML applications.
- **CF** (`characteristic/`): Charguéraud-style characteristic formulae — a
  separation logic over the CakeML semantics (`cf_sound` ties the `cf`
  formula generator to `evaluate`) for verifying *handwritten* imperative and
  I/O code, which the translator can't produce.
- **Basis** (`basis/`): verified standard library; I/O is specified against
  a logical **file-system model** (`fsFFI`: inode table, descriptors, plus a
  lazy list of nondeterministic read/write sizes), with `basis_ffi_oracle`
  instantiating the semantics oracle and a small trusted `basis_ffi.c` shim
  realizing it against the OS — that C file is the FFI trust boundary.
- **Candle** (`candle/`): a HOL-Light-style theorem prover written in CakeML
  and proved sound (kernel inference rules valid in set-theoretic semantics),
  with the soundness statement carried to the *compiled binary's I/O events*
  (`candle_soundness` in the bootstrap proofs) — the showcase that end-to-end
  means end-to-end.

TCB of a verified CakeML application: HOL4's kernel, the per-target ISA
model + encoder correctness at the very bottom, the FFI oracle assumptions
(`basis_ffi.c` and the OS behaving like `fsFFI`), and hardware.

## Part II — Pancake

Pancake answers a different question with the same infrastructure: what does
a verified compiler for a **C-like systems language** — device drivers,
seL4-adjacent, no GC — look like if you graft it onto the CakeML backend at
`wordLang`?

### 1. Language design

`panLang` (`pancake/panLangScript.sml`, `semantics/panSemScript.sml`) is an
imperative language of machine words with:

- a **shape** discipline instead of a type system: every variable, global,
  parameter and return carries a shape — `One` (a word), `Comb [shapes]`
  (a struct, by layout), or `Named` (nominal structs, desugared early). The
  semantics checks shapes dynamically (`shape_of` mismatches are `Error`),
  and an *unverified* static checker (`panStaticScript.sml` — scope, shape,
  control-flow, and suspicious-address checks) filters programs up front;
  correctness never depends on it.
- **flat word-addressed memory** `addr → word_lab` with an explicit local
  range `[@base, @top)`; locals are stack-only, globals are carved from the
  top of the heap (`pan_globals`), and there is **no dynamic allocation, no
  GC** (as of April 2026, NEWS.md: the GC is unconditionally compiled out —
  Pancake binaries carry no allocator runtime at all), and no function
  pointers (removed Jan 2025).
- **exceptions with declared shapes**, four call forms (tail / standalone /
  assigning / declaring), `while`/`break`/`continue`, and multi-width memory
  access (8/16/32/word).
- **two escape hatches to the world**: classic `ExtCall` FFI (byte arrays in
  local memory), and — the distinctive feature — **shared-memory
  operations** `ShMemLoad`/`ShMemStore` over a *separate* address domain
  `sh_memaddrs`, semantically modeled as FFI calls (`SharedMem
  MappedRead/MappedWrite`). That gives memory-mapped device registers
  `volatile` semantics for free: as FFI events they are observable, ordered,
  and can never be optimized away or reordered by any verified pass — and
  the events survive to the machine-code theorem. NEWS.md documents the
  motivation directly (device registers; 8/16/32-bit variants "primarily
  intended for reading and writing to device registers").

### 2. The IR ladder into wordLang

```
panLang → pan_simp → pan_structs → pan_globals → pan_to_crep
        → crepLang → crep_to_loop → loopLang → loop_to_word → wordLang
        → (CakeML backend: word_to_stack → stack_to_lab → lab_to_target)
```

Each rung removes one abstraction, Radix/CompCert-style: `pan_simp`
normalizes `Seq` and exposes tail calls; `pan_structs` desugars named to raw
structs; `pan_globals` rewrites globals to loads at `@top − offset`;
**`pan_to_crep`** flattens struct-shaped locals into tuples of word-sized
locals (Crepe = "instructions similar to Pancake, but locals flattened from
struct-layout to word-layout"); **`crep_to_loop`** flattens expressions into
three-address form over numbered locals; **`loop_to_word`** enters wordLang.
`loopLang` (with `loop_call`/`loop_live` optimizations) was created
specifically as the adapter between a structured C-like source and CakeML's
backend — from `wordLang` down, all of CakeML's register allocation,
stack, assembler machinery *and their proofs* are reused unchanged, minus
the GC (the pipeline simply never emits allocation, and the proofs carry a
`no_install_or_no_share_mem`-style discipline for the new shared-memory
instructions instead).

### 3. Semantics and theorem, same mold

Pancake's semantics is the same functional-big-step-with-clock-and-oracle
recipe as CakeML's, and the end-to-end theorem
(`proofs/pan_to_targetProofScript.sml::pan_to_target_compile_semantics`) has
the same shape: given a successful compile, an `installed` machine state, a
correctly laid-out memory (base/top, globals region, shared-memory domain
disjoint from the local heap), and a source semantics that isn't `Fail`,

```
machine_sem mc ffi ms ⊆ extend_with_resource_limit' … {semantics pan_code}
```

— machine code refines Pancake behavior up to resource exhaustion. Since
Pancake has no type-soundness theorem, the `≠ Fail` premise is discharged
per-program (that is what the static checker helps with, informally).

The parser is a PEG over concrete C-like syntax with `/@ … @/` annotation
nodes preserved in the AST (for external tooling); NEWS.md serves as an
explicit, dated design log — rare and valuable in a research artifact.

## Part III — Takeaways

CakeML is the closest methodological relative of this repo's tower (our
clocked functional semantics and `compile_sim` layering already follow the
CompCert/CakeML playbook — see [LOWIR-DESIGN.md](../LOWIR-DESIGN.md)), and
Pancake is the closest *object-level* relative of LowIR. Worth holding:

1. **Functional big-step + clock scales to a real compiler.** Every proof an
   induction on `evaluate`, divergence as a fuel limit (`lprefix_lub`), no
   coinduction, no simulation-diagram zoo. This is our style; CakeML is the
   existence proof at industrial size.
2. **`extend_with_resource_limit` is the honest way to state "correct unless
   OOM"** — and the space-cost semantics shows the caveat can be discharged
   per-program later without changing the main theorem. Directly relevant to
   how we phrase stack/heap bounds in LowIR call specs.
3. **In-logic evaluation beats extraction.** Producing the binary by
   evaluating the compiler in the logic (cv_compute) deletes the
   extraction/OCaml/assembler TCB that CompCert carries. Our Lean-only rule
   plus `vm_compute`-style evaluation is the same instinct; CakeML shows the
   endgame (self-hosting included).
4. **Pancake is the template for a verified systems-language rung**: flat
   word memory with explicit `[@base, @top)`, shapes not types, globals as
   carved memory, no allocation, device I/O as observable FFI events with
   volatile semantics, and an unverified-but-useful static checker kept out
   of the TCB. If our tower ever grows a C-like surface over LowIR, this is
   the design to steal — including `loopLang` as the dedicated adapter IL.
5. **Verified-algorithm vs verified-checker is a spectrum**: CakeML shows
   the far end (verified IRC allocator, verified GC, verified assembler) is
   reachable when the whole development lives in one logic and the
   algorithms are written monadically. Choose per-pass: CompCert-style
   validation when heuristics churn, CakeML-style when the algorithm is
   stable.
6. **A dated NEWS.md design log** (Pancake) is a cheap practice worth
   copying for our own long-running IR work.
