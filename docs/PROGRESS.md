# PROGRESS — LowIR & libc-formalize

## 2026-07-02 (later) — the library on Prog: strlen/strtoull/hex0/hex1 + driver

`lean/LowIR/ProgLib.lean` (commit 8ba9a8f): the four programs as real D7/D8
FUNCTIONS (params/rets/frames) + a `main` driver staging all inputs in its own
frame and calling all of them (8 observables). hex0/strtoull/strlen are ports
of the Ctrl versions; **hex1 is new, written from HEX1.md** — two-phase
scan/emit, rel32 refs, and the 256-entry label table in hex1's OWN frame
(4-byte LE entries = pos+1; 0 = undefined; zeroed by unrolled `sd x0` since
frame memory is not implicitly zero) — the D8 frame design carrying real
weight for the first time. Validation both ways: IL vs specs
(`Hex0.coreSpec` full battery, `Hex1.coreSpec1` 23-case battery + hex0's
battery for the shared-input promise, `strtoullConfSpec` incl. 2⁶⁴
saturation), and differential through the compiler onto `Rv64i.step` bytes
(each function + byte-for-byte output regions + the whole driver). All
green, sorry-free, in the default build. This is the pre-verification
baseline the correctness work will target.

Reverse-chronological execution log for the libc-formalization effort (design doc:
[LIBC-FORMALIZE.md](LIBC-FORMALIZE.md); status: [archive/STATUS.md](archive/STATUS.md) §LowIR).

## 2026-07-02 — D7/D8 compiler cut: Prog IR + executable compiler + differential tests

The [RESUME-LOWIR-COMPILER.md](RESUME-LOWIR-COMPILER.md) mandate, all landed
(commits 16b7296, 1be7e63; build target `LowIRCompile`, in `defaultTargets`):

- **`LowIR/Prog.lean`** — the D7/D8 IR, executable: named activation-local
  calls (fresh zero-init regs, params-only binding, rets-only copyback,
  arity-indexed `Vector`s, `wf`/`wfEnv` Ext. 8), D8 frames (semantic
  unwritable `sp`, `frameEnter` overflow → `none`, `frameReg` binding,
  structural sp restore), `ld`/`sd` (Rv64i byte order), `annot`. 18 `#guard`s
  incl. rec(3000) tripping the overflow check.
- **`LowIR/Compile.lean`** — memory-locals (-O0) compiler to RV64I: frame
  `[ra | slot per IL reg | user frame]`, t0/t1 lowering, SymInstr label
  streams, two-pass layout+resolve (range-checked imm12/B/J), a0..a7 call
  marshalling, prologue `sd x0` zeroing to match IL zero-init exactly.
  Entry stub `jal ra, entry`; halt pc = codeBase+4 backed by a self-loop
  landing pad — **differential testing caught the pad's absence**: the first
  function sat AT the halt address, so entering it silently stopped the
  machine (rec(0) passed by coincidence — the classic reason diff tests
  need non-trivial expected values).
- **`LowIR/CompileTests.lean`** — 16 `native_decide` differential theorems
  (IL `Prog.exec` vs compiled bytes on `Rv64i.step`): arith, bitops,
  whole-program encode/decode round-trip, sumOdd (while+ife+contL),
  findByte (brk-through-loop), nested brkB 1, early ret, memset with
  byte-for-byte data-region comparison, frame-local ld/sd, 2-function and
  3-deep chains, rec(10); + compile-refusal guards (frame > imm12, missing
  entry).

Not in this cut (per plan): verification of the compiler (`compile_sim`-style
theorem for Prog), definite-assignment optimization, >imm12 frame offsets,
recursion policy C5 (executably: it just works on fuel + overflow check).

## Previous turn

Items, in order: (a) `strtoull10_correct` sorry-free · (b) label-based compiler so
`LowIR.Ctrl` programs reach real RV64I bytes · (c) re-prove hex0 on the flat ret-cascade.

- **(a) — DONE.** `strtoull10_correct` proved sorry-free (`CtrlStrtoull10Proof.lean`): the IL
  computes the leading-digit left-fold for all inputs (geu digit loop; body_digit/body_break/
  digit_loop + prelude peel + block-catch). The geu/threshold foundation is reused. Earlier note: The wrapping `strtoull10_correct` proof fought
  signed (`slt`) comparisons under `bv_omega`, so it's scaffolded (`sorry`). Per the
  overflow discussion, built the **conformant `strtoull`** instead (`CtrlStrtoull2.lean`):
  C/POSIX overflow — saturate to ULLONG_MAX + `errno=ERANGE`, returned as `(x12,x14)`
  (no globals). Threshold `0x1999999999999999` built in-prelude; unsigned (`geu`)
  comparisons. **Validated** vs a conformant reference (value+errno, `native_decide`),
  incl. exact 2⁶⁴−1, 2⁶⁴ overflow, 20-nines overflow. The functional *proof* (of either
  version) remains: the tractable path is the **geu-based** digit loop (same shape as
  `strlen_loop` + the accumulator), since `geu`/`ult` are `bv_omega`-friendly.
- **(b), (c)** — not yet started.

## Done

- **Control-flow IL `LowIR.Ctrl`** (`lean/LowIR/Ctrl.lean`) — LowIR extended with
  `block`/`while`/`brkB k`/`contL k`/`ret` and an `Outcome`-threaded clocked big-step
  `exec`. `ret` absolute (caught at the function boundary); `brkB` counts blocks,
  `contL` counts loops (two de Bruijn spaces, CompCert-style). 3 `#guard` sanity checks.
  - **Design decisions** (recorded from the design discussion): unify break with
    block-exit; `continue` the lone loop-targeted exception; `break-loop` unnecessary
    (wrap loop in a block); `ret` kept as its own *absolute* outcome (not encoded as
    `brkB N`) — position-independent, generic at the future call boundary, trivial in
    proofs; the compiler lowers all three to scope-boundary-label jumps.
  - **strlen re-proved** (`CtrlStrlen.lean`, sorry-free). Finding: *no* ergonomic
    change — strlen has no early exits, so the outcome is pure `.normal` plumbing.
  - **hex0 with flat `ret` cascade** (`CtrlHex0.lean`) — errors are `set status; ret`;
    the hex-digit path is a flat `ife guard (err) skip` sequence, replacing the nested
    ifes + `in_idx := in_len` poison hack. Validated vs `Hex0.coreSpec` (17 cases, IL level).
  - **strtoull base-10** (`CtrlStrtoull.lean`) — `block { while(true) { … brkB 0 … } }`
    (break-out-of-loop), `acc*10 = (acc<<3)+(acc<<1)`. Validated vs a Lean reference
    incl. >2³² and 2⁶⁴ wraparound.
  - **break/block proof primitives** (`CtrlStrtoullProof.lean`) — `exec_block_catch`,
    `exec_while_brk`, `exec_seq_brk`, `exec_ret`, … each a one-line `by simp [exec]`.
    **Ergonomics result: the control-flow machinery is nearly free to reason about.**

- **Original LowIR + verified-compile pipeline** (`lean/LowIR.lean`) — structured
  three-address IL, `compile : Stmt → List Rv64i.Instr` (to the 16-instr trusted
  surface), `encode` (byte-exact inverse of `Rv64i.decode`). `strlen` end-to-end on the
  real `Rv64i.step` machine + hex0 ≡ `coreSpec` battery (`native_decide`).
  - **strlen_correct** (`StrlenProof.lean`) — functional correctness for all strings,
    sorry-free, structured induction.
  - **T1 framework** — `Layout`/`Installed`/`Agree`/`NoSelfModify` + `compile_sim`
    (statement; proof deferred per instruction).
  - **hex0_correct** (`Hex0Proof.lean`) — IL ≡ `coreSpec` stated with proof plan (deferred).

- **IL-altitude survey + plan** (`LIBC-FORMALIZE.md` §6) — CompCert/CakeML/Frama-C/
  Tree-Borrows/POSIX; the structured↔flat boundary; LowIR at the Cminor altitude.
