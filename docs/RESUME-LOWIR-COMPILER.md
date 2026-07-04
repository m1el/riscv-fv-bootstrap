# RESUME: LowIR compiler implementation (executable, unverified first cut)

## STATUS 2026-07-02: DONE — all tasks landed

Tasks 2/4/5 implemented and green (commits 16b7296 `Prog.lean`, 1be7e63
`Compile.lean`+`CompileTests.lean`): the D7/D8 IR, the memory-locals compiler
to RV64I bytes, and 16 `native_decide` differential theorems. Built by default
via the `LowIRCompile` lib target (`lake build`; rooted at
`LowIR.CompileTests`). Execution details in [PROGRESS.md](PROGRESS.md)
(2026-07-02 entry) — including the halt-address collision the differential
tests caught. The `encode`-coverage eyeball check passed (all 16 constructors,
`LowIR.lean:238`). Remaining (deliberately out of this cut): compiler
verification (`compile_sim` for Prog), definite-assignment optimization,
>imm12 frames, recursion policy C5.

The original handoff below is kept for the design rationale and plan record.

---

Session handoff, 2026-07. The design session (see below) ended with a mandate:
**implement the IR as designed (D7/D8) plus the executable compiler pipeline to
RV64I bytes, validated by differential testing — no formal verification yet.**
Work was interrupted right after the code survey (task 1 of 5); this doc carries
the full plan and every finding needed to resume cold.

## Context: what this session decided (all committed)

- [LOWIR-DESIGN.md](LOWIR-DESIGN.md) gained: **D7** (activation-local calls,
  `Env : Name → FunDef`, arity-indexed `Vect` args/rets, fresh zero-init register
  file + definite-assignment check, NOT SSA), **D8** (per-function `frameSize`,
  semantic program-unwritable `sp : Word` in `St`, frame base bound to a
  designated register, overflow → `none`, ∀-quantified `sp₀` for address
  independence, no `alloca`), **§2b** non-goals table (N1–N12), **§2c** boundary
  catalog (B1–B7), **Ext. 8** (`Stmt.wf` checker incl. `sh < 64`), **Ext. 9**
  (`annot`), **Ext. 10** (expression trees, later), **Ext. 11**
  (unwind-outcomes + stackless coroutines, later), Ext. 1 bumped (`ld/sd`
  compiler-forced), priorities: **Ext. 8 → D7+D8 impl → Ext. 1**.
- [DESIGN-THESES.md](DESIGN-THESES.md): ten theses from the third-party review
  series ([docs/third-party/](third-party/), 12 reviews) — the design rationale
  lives there.

## Survey findings (task 1 — done, one check left)

- **The Rv64i model already has everything the compiler needs.**
  `lean/RawAsm/Rv64i.lean` (210 lines): exactly 16 encodings —
  `addi add sub or slli srli lbu ld sb sd beq blt bge bgeu jal jalr` —
  with `decode`, `step`, `State.{rget,rset,loadByte,storeByte,loadWord,storeWord}`,
  `runFuel`/`stepsToHalt` (total, proof-usable) and `runUntil` (partial,
  validation only). `ld/sd/jal/jalr` were added for hex1. **Task 3 ("extend
  model") is unnecessary — delete it.**
- `lean/LowIR.lean` (395 lines): original IL + `compile : Stmt → List Instr`
  (structured ife/while via `condInstr`/`jal0` relative jumps), **`encode :
  Instr → BitVec 32`** (line 238, "byte-exact inverse of `Rv64i.decode`"),
  `insBytes`/`asmBytes` (little-endian bytes), `Layout` + T1 simulation
  framework (line 325+). *Resume check:* confirm `encode` covers all 16
  constructors (header says yes; not eyeballed).
- `lean/LowIR/Ctrl.lean`: the current Ctrl IL (read in full this session) —
  `Stmt` = skip/seq/addi/add/sub/orr/slli/srli/lbu/sb/ife/while/block/brkB/
  contL/ret/call(g:Stmt); `Outcome` = normal/brk k/cont k/ret; clocked
  `exec : Nat → Stmt → St → Option (St × Outcome)`; `run` catches normal+ret;
  `Cond` = eq/lt/ge/geu (LowIR.lean:43). `lit r v = addi r x0 v12` duplicated
  in 4 files.
- **Build**: `lean/lakefile.toml` — libs `Hex0`, `Hex1`, `LowIR`; toolchain
  `leanprover/lean4:v4.30.0`. ⚠ `lean_lib LowIR` has **no globs** — only the
  root `LowIR.lean` module (and what it imports) is built by `lake build`.
  `LowIR/Ctrl.lean` etc. are NOT imported from the root — same trap as the
  Refine.lean gotcha (see memory): **check new files with `lake env lean
  lean/LowIR/<file>.lean`**, or add `globs`/imports deliberately (decide on
  resume; adding imports to the root pulls proof files into `lake build` —
  maybe wanted, maybe slow).
- No Mathlib/Batteries in this project — plain Lean core. Lean core v4.30 has
  `Vector α n` (`Init.Data.Vector`); if it's awkward, use
  `{ l : List Reg // l.length = n }`.

## The plan (tasks 2, 4, 5 — none started)

### Task 2 — `lean/LowIR/Prog.lean`: the D7/D8 IR core (executable)

New namespace `LowIR.Prog` (do NOT touch `LowIR.Ctrl` — hex0 proofs must stay
green). Contents:

1. `abbrev Name := String`. `Stmt`: all Ctrl constructs **minus** `.call (g)`,
   **plus**:
   - `ld (rd rs : Reg) (imm : BitVec 12)` / `sd (rbase rval : Reg) (imm : BitVec 12)`
     — semantics via `loadWord`/`storeWord` ported from Rv64i (or reuse: `St`
     is LowIR's St, has `mem : Word → Byte`; write `St.loadWord/storeWord`
     mirroring Rv64i's — keep little-endian byte order identical).
   - `annot (a : String)` — `exec = some (s, .normal)` (Ext. 9).
   - `call (argc rvc : Nat) (f : Name) (args : Vector Reg argc) (rets : Vector Reg rvc)`
     — call site carries its own arities (fixed-size by construction); `wf`
     cross-checks against the env's `FunDef`.
2. `structure FunDef where argc rvc : Nat; params : Vector Reg argc;
   rets : Vector Reg rvc; frameSize : Nat; frameReg : Reg; body : Stmt`
   (skip `BorrowSig` — proof-layer, not needed for the compiler cut).
   `abbrev Env := List (Name × FunDef)` (assoc list; lookup by name).
3. `structure St where regs : Reg → Word; mem : Word → Byte; sp : Word`
   — extend, don't reuse, LowIR.St (needs `sp`). `stackLo : Word` as a
   parameter of `exec` (or bundled in an `ExecCtx` with the env).
4. `exec (env) (stackLo) : Nat → Stmt → St → Option (St × Outcome)` — Ctrl's
   equations verbatim for shared constructs; **call**:
   - lookup `f` in env (miss → `none`); require arities match (or let `wf`
     guarantee it and return `none` on mismatch);
   - `if s.sp - frameSize < stackLo → none` (overflow);
   - callee state: `regs := zero-except-params` (params bound to caller's arg
     values), `frameReg := s.sp - frameSize`, `sp := s.sp - frameSize`,
     `mem := s.mem`;
   - run body at `fuel`; accept `.normal`/`.ret` outcomes (brk/cont escaping =
     `none`; `wf` bans them);
   - result: caller's regs updated at `rets` positions with callee's `rets`
     register values, callee's `mem`, **caller's `sp`** (structural restore).
5. `wf (env) (blockD loopD : Nat) : Stmt → Bool`: brk/cont indices in range;
   `sh < 64` on slli/srli; call arities agree with env; (definite assignment:
   can be a second pass `da : Stmt → StateSet → Option StateSet` — optional in
   the first cut, semantics is zero-init deterministic anyway).
6. `run env stackLo fuel f args s` — top-level: call `f` as the entry.
7. `#guard` sanity tests: arithmetic, loop, block/brk, ret, a two-function
   call (callee writes a frame local via `sd frameReg`, returns a value),
   nested call, stack-overflow → none, annot no-op.

### Task 4 — `lean/LowIR/Compile.lean`: Prog → RV64I bytes (unverified)

**Strategy: memory-locals (-O0 style)** — every IL register gets a frame slot;
no register allocation at all. Correctness-first, performance-irrelevant (N9).

- **Frame layout** (per function): `[saved ra][slot for IL reg 0..maxReg][user
  frame frameSize bytes]`, 8-byte slots, `sp`-relative. `maxReg` = max register
  index mentioned in the body (finite scan). Physical register roles (RISC-V):
  `x2=sp` real stack pointer; `x5,x6,x7 (t0,t1,t2)` scratch; `x10..x17
  (a0..a7)` argument/return marshalling; `x1=ra`.
  ⚠ **12-bit immediate limit**: slot offsets and frameSize must fit `imm12`
  (±2048). First cut: assert `8*(maxReg+2)+frameSize < 2000` at compile time
  (return `Option`/`Except` from the compiler); synthesize larger offsets later.
- **Per-statement lowering** (each IL instr → load operands into t0/t1 from
  slots, compute into t0, store to dest slot):
  e.g. `add rd r1 r2` ↦ `ld t0, off(r1)(sp); ld t1, off(r2)(sp);
  add t0,t0,t1; sd t0, off(rd)(sp)`. `ife/while` conds: load a,b into t0,t1,
  `condInstr`-style branch (reuse/adapt `LowIR.condInstr`, `jal0`).
- **Control lowering**: recursive compile with a label environment
  (`breakTargets : List LabelId`, `contTargets : List LabelId`, `retTarget`),
  emitting a symbolic instruction list `List SymInstr` where branches/jumps
  carry label ids; then a **resolve pass** computes byte offsets (two passes:
  positions, then patch — all instructions are fixed 4 bytes, so one pass of
  position computation suffices). `ret` = jump to function epilogue label.
- **Calls**: caller loads arg slots → `a0..a(argc-1)`, `jal ra, f`; callee
  prologue: `addi sp,sp,-frame; sd ra, 0(sp);` store `a*` into param slots,
  zero remaining slots? — **no**: zero-init semantics vs junk registers —
  first cut: explicitly `sd x0` every non-param slot in the prologue (matches
  zero-init exactly, keeps differential tests honest; definite-assignment
  optimization later). Set frameReg slot? frameReg is an IL register: its slot
  gets `sp + userFrameOffset`. Epilogue: load `rets` slots → `a0..`, `ld ra;
  addi sp,sp,+frame; jalr x0, ra, 0`. Caller stores `a*` back to ret slots.
  Caller-saved concerns: **none** — everything lives in slots; only t0/t1/a*
  are live within a single IL statement, never across a call.
- **Whole program**: `compileProg (env) (entry : Name) : Option (List Instr ×
  FnTable)` — concatenate functions, record offsets, patch `jal` targets;
  entry stub: set up `sp` (given as a parameter/register at start), call
  entry, halt (jump-to-self or a designated halt address for `runFuel halt`
  — reuse the T1/Layout halt convention from LowIR.lean:325+).
- Encode with existing `LowIR.encode`/`asmBytes`.

### Task 5 — differential tests (`lean/LowIR/CompileTests.lean`)

For each test program: build initial `Rv64i.State` (code bytes at base, stack
region, input data), `runFuel halt`, compare designated observables (ret-value
registers / memory bytes) against `Prog.exec` results via `#guard` /
`native_decide`. Programs: arith chain; while loop (strlen-style); block/brk
cascade; **two-function call with frame local + `ld/sd` roundtrip**; nested
calls 3 deep; recursion smoke test (fuel-bounded, if allowed by wf — recursion
policy C5 still open, test it anyway executably); stack overflow behavior.
⚠ differential caveat: IL zero-init vs machine — handled by prologue zeroing
(above); `sp₀` in tests: pick a concrete stack top, pass same to both sides.

### Order & discipline

1. Prog.lean green (`lake env lean` it) + #guards → **commit**.
2. Compile.lean skeleton: straight-line arith only, end-to-end differential
   test passing → **commit**.
3. Control flow (ife/while/block/brk/cont/ret) → tests → **commit**.
4. Calls + frames → tests → **commit**.
5. Wire into build (globs or root import — decide), update
   [PROGRESS.md](PROGRESS.md) (reverse-chron log) and this doc's status.

Known Lean gotchas that will bite (from memory/gotcha log): `lake build`
root-module trap (above); avoid `simp [exec] at h` with IH in context
(OOM — use targeted rewrites; irrelevant while proof-free, relevant for
#guard-heavy files only in elaboration time); `native_decide` fine for tests.

## Task-list state at interrupt

1. Survey existing code — **done** (findings above; one `encode`-coverage
   eyeball left). 2. Prog IR — pending. 3. Extend Rv64i — **obsolete, delete**.
4. Compiler pipeline — pending. 5. Differential tests — pending.
