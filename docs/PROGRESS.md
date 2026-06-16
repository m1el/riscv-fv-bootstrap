# PROGRESS — LowIR & libc-formalize

Reverse-chronological execution log for the libc-formalization effort (design doc:
[LIBC-FORMALIZE.md](LIBC-FORMALIZE.md); status: [STATUS.md](STATUS.md) §LowIR).

## In progress (current turn)

Items, in order: (a) `strtoull10_correct` sorry-free · (b) label-based compiler so
`LowIR.Ctrl` programs reach real RV64I bytes · (c) re-prove hex0 on the flat ret-cascade.

- **(a) — pivoted + partly delivered.** The wrapping `strtoull10_correct` proof fought
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
