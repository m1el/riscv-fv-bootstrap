# Lean corpus layout — the language tower

Map of `lean/`, organized as a **tower of languages** over a shared spec. Read
top-down: each rung is a language, and each program is proved once per rung it
reaches. One top-level directory per rung, one Lake lib per directory (see
`lean/lakefile.toml`); the disjoint top-level namespaces make every module
belong to exactly one lib.

```
lean/
  Spec/     functional specifications — the refinement targets (rung-independent)
  RawAsm/   bare RV64I model + hex0/hex1 verified at the flat-PC altitude
  LowIR/    structured IL (Core → Ctrl → Prog) + verified compiler + proofs
  LowSSA/   the SSA variant of the Prog IR (experiment)
  {Spec,RawAsm,LowIR,LowSSA}.lean   rung aggregators (Lake roots)
  DumpProgMain.lean                 tool: emits bare/progmain.* (not a lib module)
```

Build a whole rung with `lake build <Spec|RawAsm|LowIR|LowSSA>`, or one module
with `lake build <Module.Name>`. `defaultTargets` is the four rung libs; the
pre-reorg names (`Hex0`, `Hex1`, `LowIRCompile`, `LowIRProgSim`, `LowIRSSA`)
survive as back-compat lib aliases outside `defaultTargets`.

## The rungs

### `Spec/` — the specifications every rung refines against
- [`Spec/Hex0/Spec.lean`](../lean/Spec/Hex0/Spec.lean) — `Hex0.decode`/`coreSpec` (mirrors `coq/Spec.v`); [`Grammar.lean`](../lean/Spec/Hex0/Grammar.lean) — concrete-syntax grammar + error taxonomy.
- [`Spec/Hex1/Spec.lean`](../lean/Spec/Hex1/Spec.lean) — `Hex1.coreSpec1`; [`Grammar.lean`](../lean/Spec/Hex1/Grammar.lean).
- No `Spec/Strlen/`: strlen's spec is the one-liner `firstNulAt` in [`LowIR/Core.lean`](../lean/LowIR/Core.lean), and strlen has no grammar (not a parser).

### `RawAsm/` — bare RV64I, flat-PC proofs
- [`Rv64i.lean`](../lean/RawAsm/Rv64i.lean) — the 16-instruction RV64I machine model (the whole trusted ISA surface; shared by every rung above).
- `Hex0/` — [`Refine.lean`](../lean/RawAsm/Hex0/Refine.lean) (the ~3400-line PC-simulation proof), `Certify`, `Harness`, `Image` (auto-gen from the ELF), `Validate` (executable diff-test).
- `Hex1/` — same shape plus `RefineBase` and `DecodeFacts` (kernel-checked per-instruction decode facts, auto-gen).

### `LowIR/` — the structured IL, its compiler, and its programs
The IL is three stacked layers, each additive over the last:
- [`Core.lean`](../lean/LowIR/Core.lean) — base three-address IL (1:1 with RV64I ops) + clocked big-step semantics.
- [`Ctrl.lean`](../lean/LowIR/Ctrl.lean) — structured non-local control: `block`/`while`/`brkB`/`contL`/`ret` threading an `Outcome`.
- [`Prog.lean`](../lean/LowIR/Prog.lean) — the D7/D8 IR: activation-local calls, per-function stack frames, `ld`/`sd`.

Backend + library:
- [`Compile.lean`](../lean/LowIR/Compile.lean) — verified-target compiler `Prog → RV64I` (memory-locals, -O0); [`CompileTests.lean`](../lean/LowIR/CompileTests.lean) — differential tests (`Prog.exec` vs compiled bytes on `Rv64i.step`); [`Dump.lean`](../lean/LowIR/Dump.lean) — s-expression/asm renderer.
- [`Lib.lean`](../lean/LowIR/Lib.lean) — **the combined function library**: `strlen`, `strtoull`, `hex0`, `hex1` as real `FunDef`s (params/rets/frames) plus a `main` driver that stages each input in its own frame and calls all four. Every function is spec-validated at the IL level.
- [`CtrlFacts.lean`](../lean/LowIR/CtrlFacts.lean) — the shared **Ctrl proof foundation**: generic exec/outcome lemmas (`exec_block_*`/`while_*`/`ret`/`brk`/`cont`/`call`/`mono`). Reused by every Ctrl-level proof (the LowIR analog of [`LowSSA/ExecFacts.lean`](../lean/LowSSA/ExecFacts.lean)).

Programs (one subdir each — see the naming rule below):
- `Hex0/` — `Ctrl`+`CtrlProof` (hex0 on the Ctrl IL) and `Prog`+`ProgProof` (hex0 on the Prog IR).
- `Strlen/` — `Ctrl` (the Ctrl-IL version) and `CoreProof` (correctness of the base-IL strlen from `Core.lean`).
- `Strtoull/` — `Wrapping`+`WrappingProof` (base-10, 64-bit wraparound) and `Conformant`+`ConformantProof` (saturate to `ULLONG_MAX` + `ERANGE`, C/POSIX).
- `Examples/Call.lean` — a worked cross-call disjointness example (illustrative, not part of the pipeline).

The compiler-correctness campaign:
- `ProgSim/` — the `compile_sim`-for-Prog proof (`Defs`, `WordMem`, `ExecFacts`, `SlotFacts`, `MemFacts`, `StmtSim`, `CtrlSim`). Handoff: [RESUME-PROGSIM.md](RESUME-PROGSIM.md).

### `LowSSA/` — the SSA variant of the Prog IR
Single-version (SSA only), so proofs are bare `Proof.lean`:
- [`Core.lean`](../lean/LowSSA/Core.lean) — SSA IR (valued outcomes, block-parameter loops, never/thru typing); `Dump`; [`Lib.lean`](../lean/LowSSA/Lib.lean) — strlen/hex0 ported to SSA; [`ExecFacts.lean`](../lean/LowSSA/ExecFacts.lean) — SSA exec foundation.
- `Hex0/Proof.lean`, `Strlen/Proof.lean` — the ported correctness proofs. See [LOWIR-SSA-EXPERIMENT.md](LOWIR-SSA-EXPERIMENT.md), [RESUME-SSA-HEX0.md](RESUME-SSA-HEX0.md).

## Naming conventions

- **Namespaces are independent of paths.** The reorg moved files but kept the
  internal `namespace` decls, so e.g. `LowSSA/Core.lean` still declares
  `namespace LowIR.SSA` and `RawAsm/Rv64i.lean` declares `namespace Rv64i`. A
  module's *import path* follows its directory; its *namespace* does not.
- **Program proof files** are named `<Variant>Proof.lean` when a program has
  more than one variant, and `Proof.lean` when it has one. The "variant" axis
  differs by program and that is deliberate — it names the real distinction:
  - hex0 (LowIR): the *IR level* — `Ctrl` vs `Prog`.
  - strlen (LowIR): the *IR level* — the base IL (`CoreProof`) vs `Ctrl`.
  - strtoull (LowIR): the *overflow semantics* — `Wrapping` vs `Conformant`.
  - hex0/strlen (LowSSA): one variant each → plain `Proof`.
- **Shared proof foundations** are named `*Facts` / `ExecFacts` and sit at the
  rung's top level (`LowIR/CtrlFacts.lean`, `LowSSA/ExecFacts.lean`), not inside
  any one program's folder.

## See also

- [LOWIR-DESIGN.md](LOWIR-DESIGN.md) — why the IL is shaped this way (structured control, unbounded registers + flat memory, calls/frames, the compiler cut).
- [PROOF.md](PROOF.md) / [TCB.md](TCB.md) — the hex0 refinement methodology and the trusted base.
- [RESUME-PROGSIM.md](RESUME-PROGSIM.md) — the active `compile_sim` handoff.
