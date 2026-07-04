# RESUME — proving `compile_sim` for Prog (D7/D8 compiler correctness)

Plan written 2026-07-02, immediately after the executable cut landed. Read with
[LOWIR-DESIGN.md](LOWIR-DESIGN.md) (D7/D8, Ext. 12, §4 pass decomposition),
[PROGRESS.md](PROGRESS.md) (what exists), [archive/RESUME-LOWIR.md](archive/RESUME-LOWIR.md)
(the hex0-era proof toolbox and gotchas — much of it ports).

**Status (updated 2026-07-03).** Phase 0 is essentially done and the relation
skeleton is drafted; the vertical slice is the next go/no-go. Concretely:
- **Phase 0.1 (P1 oracle) — DONE.** `pad : Name → Nat` in `frameEnter`/`exec`/
  `run` (default `fun _ => 0`, everything re-greens); `CompileTests.lean` has
  the `pad = userOff` frame-memory differential tests validating P1. Committed.
- **Phase 0.2 (unfolders) — DONE.** `ProgSim/ExecFacts.lean`: 42 one-layer
  `exec_*` lemmas in `namespace LowIR.Prog`. Committed.
- **Phase 0.3 (execT + erasure) — DONE.** `execT`/`execT_map_exec`/`execT_erase`
  in `ProgSim/Defs.lean`, axioms `[propext, Quot.sound]`. Committed.
- **Defs (§3 statements) — DRAFTED.** `Layout`/`Installed`/`StInv`/`SimPre`/
  `userPad` real, `#guard`'d; `prog_sim` is the standing `sorry` (Phase 4/5/6
  target). `lean_lib LowIRProgSim` (root `LowIR.ProgSim.Defs`) in
  `defaultTargets`, builds in ~2.6 s.
- **Phase 3 (start) — WordMem DONE.** `ProgSim/WordMem.lean`: the 64-bit LE
  load/store algebra (`byte_bit`, `loadWord_storeWord_same` round-trip,
  `storeWord_mem_of_ne`/`_outside`, `loadWord_storeWord_disjoint`), sub-second.
  Committed `f513c27`; **axiom hygiene retrofit** since — `byte_bit`/round-trip
  now `[propext, Quot.sound]` (were pulling `Classical.choice`): the omega-on-
  iff/∧/∨ goals are split to atoms first (`constructor`/`repeat' apply And.intro`
  / `exfalso`), the window tiling is the new explicit constructive `window_tiling`
  (never `omega` on the disjunction), and `by_cases`→`cases Nat.decLe`.
- **Phase 3 (finish) — SlotFacts DONE.** `ProgSim/SlotFacts.lean`: the StInv
  slot algebra, `[propext, Quot.sound]`. Slot arithmetic (`slotOff_add8_le_userOff`,
  `slotOff_disjoint`, `slotAddr_toNat`), slot read/write lifted from WordMem
  (`loadWord_store_slot_same`/`_ne`), blob preservation (`fetch32_pc_congr`,
  `blobAddr_toNat`, `mem_storeWord_off_blob`, `Installed_storeWord_off_blob`),
  and the payoff **`StInv_store_slot`**: a machine slot store mirrors IL `rset r v`,
  preserving all six `StInv` conjuncts. The frame-/blob-placement side conditions
  (`hnw`/`hseg`/`hblob`/`hbd`) are explicit hypotheses here — Phases 4/5 discharge
  them from `SimPre`. Reg binders are `Nat` (a `≤` at type `Reg = abbrev Nat`
  hides from `omega`). In `defaultTargets` (added to `LowIRProgSim` roots).
- **Phase 4.1 vertical slice — GO, straight-line slice COMPLETE.**
  `ProgSim/StmtSim.lean`: `emit` (resolved straight-line lowering, `#guard`'d ==
  real `Compile.lower` of `sub3.body`), `Emitted` (+ append-split),
  `decode_emitted`/`decode_at` (fetch bridge from `Installed`), `stepN`/`stepN_add`,
  the `step_*` one-instruction lemmas, `signExtend_ofNat_lt` (slot immediates,
  `[propext, Quot.sound]` via `toInt_eq_toNat_bmod`), `StInv_congr`/`StInv_scratch`,
  `load_step`, `pc_add4`/`pc_congr`, `StInv_sp_eq`. **`lower_sim`** (the `.normal`
  simulation, fuel induction) now proves the WHOLE straight-line fragment:
  skip, annot, all six arithmetic ops (**addi/add/sub/orr/slli/srli**, every
  register value including 0), and **seq**. The op cases are factored through two
  reusable simulators — `run_load`/`run_store` (uniform over `r=0`; the `rd=0`/`≠0`
  split lives once inside `run_store`) and `single_op_sim`/`two_op_sim` (abstract
  compute `C`/`vC`, each op supplies its `step_*` lemma as `hC`) — all
  `[propext, Quot.sound]`. `seq` chains the fuel `ih` (stepN_add + pc_congr;
  frame side conditions transfer via `StInv_sp_eq`).
- **Phase 4.2 memory ops — DONE (ld/sd/lbu/sb).** New file `ProgSim/MemFacts.lean`
  (the memory analogue of `SlotFacts`, all `[propext, Quot.sound]`): `loadWord_agree`
  / `loadWord_agree_off` (machine load = IL load off `MachPriv` — the P1 address
  equality + byte agreement), `storeWord_mem_agree` (a store writes IDENTICAL bytes
  into IL and machine memory ⇒ pointwise agreement, NO in/out-range split), and the
  payoffs `StInv_storeWord_user`/`StInv_storeByte_user` (a user store off this
  activation's hole ⇒ disjoint from live slots, and off the blob ⇒ `Installed`
  survives). `lower_sim` now has a `MemAccOff` hypothesis (per-statement "accessed
  bytes off `MachPriv`", recursing through `seq` like `exec`; trivial for
  non-memory cases) threaded through `seq`. ld/lbu go via the (mem-generalized)
  `single_op_sim`; sd/sb are two loads then the machine store, with the toNat
  range-disjointness derived from `MemAccOff`'s pointwise form by the constructive
  `range_disjoint_of_bytes`. `#guard`: `emit frameLocal.body` (sd+ld) == real
  lowering.
- **Phase 4.3 control flow — foundation + the three LEAF ops DONE.** All
  `[propext, Quot.sound]`, in `StmtSim.lean`:
  - **machine steps** `step_jal` / `step_beq` / `step_blt` / `step_bge` /
    `step_bgeu` (the `jal x0` and four positive-form branches);
  - **offset arithmetic** `signExtend_ofInt_21` / `_13` (a signed offset
    `δ = target − here` within `resolveOne`'s emit guard sign-extends to itself —
    `toInt = bmod`, `Int.bmod_def; split <;> omega` at the concrete modulus) and
    `jump_lands` (a PC-relative transfer from `codeBase + here` by `δ` lands at
    `codeBase + target`, either direction, wrap-safe);
  - **`jump_sim`** — the leaf unconditional jump: `jal x0, (target − here)`
    preserves `StInv` (jumps don't mutate IL state; `StInv_scratch` on x0) and
    lands at `codeBase + target`;
  - **`ret_sim` / `brkB_sim` / `contL_sim`** — the three leaf control-transfer ops,
    each `jump_sim` + extracting `s' = s` from `exec_ret`/`exec_brkB`/`exec_contL`.
    The resolved `target` (epilogue / k-th break / k-th continue label position) is
    a parameter, supplied later by the label environment / Phase-2 layout.
  `sorry` remains for the COMPOUND control-flow ops (ife/while/block), cref/clen,
  and call.

  **Framework needed for ife/while/block** (next): an *outcome-carrying* `lower_sim`
  generalization — conclusion carries the `Outcome` and lands at
  `codeBase + landPos(outcome)` where `landPos` maps `.normal ↦ fall-through`,
  `.brk k ↦ brkPos[k]`, `.cont k ↦ contPos[k]`, `.ret ↦ epiPos`. It threads a
  label environment `(brkPos contPos : List Nat) (epiPos : Nat)`. Cleanest design:
  parameterize by an abstract label→position map `lpos` with a consistency
  hypothesis (each `.label l` marker sits at `lpos l`; jumps to `l` use offset
  `lpos l − here`), so the simulation proof is decoupled from the layout; Phase 2
  discharges consistency against the real `layout`/`layoutItems`/`resolveOne`.
  `block body` = `emit_cf body (lEnd::brks)` then the 0-byte `lEnd` marker; case on
  body's outcome (a `.brk 0` lands at `lEnd` = fall-through, the block's normal
  continuation; `.brk (k+1)`/`.cont`/`.ret` propagate). `ife`/`while` add the
  conditional branch (`step_beq`… + `evalCond`) selecting then/else or loop
  body/exit, and the back-edge `jmp lTop` (a backward `jump_sim`). All the atoms
  (branch/jump steps, offset arithmetic, `jump_sim`) are already in place.

  **The `while` case — shape confirmed by the SSA §8 rework (2026-07-03).**
  Prog's back-edge re-executes the SAME `.while c a b body` term at `fuel`
  (`exec_while_normal`/`_cont0` in `ProgSim/ExecFacts.lean`; the loop-carried
  values ride the mutable registers), so the `lower_sim_cf` fuel IH applies to
  the back-edge DIRECTLY — the recursive occurrence is the identical
  `Emitted`/`emitCF` instance at the same position, with only the machine's
  backward `jmp lTop` (`jump_sim`) in between. No quantification over a
  family of loop terms is needed. This is exactly the fixed-term shape the SSA
  campaign had to BUY by reworking its `while` to rebind-in-environment
  (`iterWhile`, [RESUME-SSA-HEX0.md](RESUME-SSA-HEX0.md) §8, commit `ef17bbd`)
  — Prog had it from day one, so **no Prog-side semantics change is needed or
  wanted**. Per-case skeleton: guard `run_load`s + `cond_taken`/`_not_taken`
  (as `ife`); guard-false → branch to `lEnd`, `.normal`; guard-true → body IH
  at `fuel−1` with `lTop :: contPos`, `lEnd :: brkPos` (scoping exactly like
  `block`), then a six-way outcome walk: `.normal` → the emitted back-edge
  `jmp lTop` (`jump_sim`) then the fuel IH on the same while; `.cont 0` → the
  body's own lowered jump ALREADY landed at `lTop` (that is `contL_sim`'s
  conclusion), fuel IH directly; `.brk 0` → landed at `lEnd`, `.normal` out;
  `.brk (k+1)`/`.cont (k+1)` shift; `.ret` propagates. The outcome plumbing
  mirrors the six-way match the SSA `iterWhile_mono`/`iterWhile_frame` proofs
  walk — same-term recursion makes the IH application one line in both.
- **Phase 4.3 label-aware emit — DONE + VALIDATED (`CtrlSim.lean`).** `emitCF`
  (`brkPos contPos : List Nat`, `epiPos here : Nat → PStmt → List Instr`): the
  position/label-resolved extension of `emit` to control flow — the concrete stream
  `Compile.lower ▸ layoutItems ▸ resolveOne` emits, every `.jmp`/`.br` a single
  `jal x0`/branch at offset `target − here`, every label 0 bytes. Straight-line
  cases delegate to `emit`; the `ife`/`while` internal offsets are
  position-independent (size-relative via `csize`), only `ret`/`brkB`/`contL`
  targets depend on `here`. `csize` (position-independent instruction count,
  `ife = 4+|t|+|e|`, `while = 5+|b|`) + `emitCF_length : (emitCF …).length = csize`
  (`[propext, Quot.sound]`). **Validated**: `#guard realResolve == emitCF` for
  strlen/strtoull/hex0/hex1 (all control-flow constructs + nestings) — the concrete
  decidable IR↔assembly mapping. This is the emit the outcome-carrying `lower_sim`
  inducts over.
- **Phase 4.3 `lower_sim_cf` (outcome-carrying) — IN PROGRESS (`CtrlSim.lean`).**
  Conclusion carries the `Outcome`: the machine lands at `codeBase + landPos(oc)`
  (`landPos`: normal↦fall-through, brk k↦brkPos[k], cont k↦contPos[k], ret↦epiPos).
  Fuel induction over `emitCF` with the label environment. **Cases DONE:** skip,
  annot, block (IH on body with `lEnd::brkPos`, outcome case-walk), the six arith
  + four mem ops (delegate to `emit`'s `lower_sim`), seq (outcome-threaded), the
  three leaf jumps ret/brkB/contL (`jump_sim`), and **`ife`** — two `run_load`s to
  the branch, `cond_taken`/`cond_not_taken` split on `evalCond`, then/else IHs,
  else-normal extra jal, landings reconciled. Needs a `BranchOk` side condition
  (every ife's `8+4·csize e < 2^12`, the compiler's 13-bit branch-span guard) and
  a `MemAccOff` ife case (both arms access-safe). **Remaining `sorry`:** while
  (fuel-IH back-edge + `contPos` scope), cref, clen, call.
- **Phase 4.1 sub3 corollary — DONE, go/no-go CLOSED (sorry-free).**
  `sub3_body_exec` (IL spec `(a+b)−c` into x10, forward via `exec_*`) +
  `sub3_body_sim`: from a `StInv`-related state with `emit sub3.body` installed,
  the machine runs to a `StInv`-related state for `s'` whose return register holds
  `(a+b)−c`. Proved by driving `add` then `sub` through `two_op_sim` **directly**
  (NOT `lower_sim` — so it is `[propext, Quot.sound]`, not inheriting the
  control-flow `sorry`), chained with `stepN_add`. The IL result reproduces the
  differential oracle `diff_sub3` ([30,12,2] ↦ 40), checked by a `native_decide`
  example. The relation is validated end-to-end against the oracle.
- **NEXT:** Phase 4.3 control flow (ife/while/block/ret/brk/cont — the outcome
  selects a label; needs the `Emitted` label-offset algebra + a `.brk/.cont/.ret`
  outcome-carrying `lower_sim` generalization), cref/clen (`synthConst`), Phase 2
  (AsmFacts: `Emitted L pos (emit stmt)` from the real pipeline), 5 (call),
  6 (prog_sim). A sorry-free frameLocal corollary (mem end-to-end vs the oracle)
  can be done now by driving sd/ld through the simulators directly (as sub3 did).

## 0. Mission and payoff

Prove: **if the D7/D8 IL says a program computes something, the compiled RV64I
bytes compute the same thing on the trusted `Rv64i` model.** This is the T1
of `LowIR.lean:312` re-targeted at the real IR (functions, frames, calls,
const data) — the pass that amortizes the flat-PC simulation cost paid
per-program in `RawAsm/Hex0/Refine.lean` (~3400 lines for ONE program) into ONE
proof reused by every program. After it, a structured-altitude proof like
`strlen_correct` transports to actual bytes by composition, and the ProgLib
functions get machine-level correctness for the price of their (easy)
IL-level proofs.

Ground truth already in hand: 30+ differential theorems + QEMU agree on the
library — the theorem will not be defending a false claim; every lemma has an
executable oracle to test against while it is being stated.

## 1. What exists (frozen inputs to the proof)

- `LowIR/Prog.lean` — `exec (P dbase stackLo) : Nat → Stmt → St → Option (St × Outcome)`,
  `frameEnter`, `run`; data layout **single-sourced with proved correspondence**
  (`dataSegment_at`, `installData_at`, `dataOffsetsFrom_shift`, `_le`, `_fits`) —
  the data half of this campaign is already de-risked.
- `LowIR/Compile.lean` — memory-locals compiler: `lower` (label stacks
  brks/conts/epi), `prologue`/`epilogue`, `synthConst`, `layout`/`layoutItems`
  (`symSize`), `resolveOne` (range-checked), `compileProgT`/`progBytes`,
  entry stub + halt pad. Physical regs: x1=ra, x2=sp, x5/x6=t0/t1, x10..x17=a*.
  The compiler is FROZEN as-is for this campaign (P1 needs no change to it).
- `LowIR/Lib.lean` + `CompileTests.lean` — the programs and the
  differential batteries (the regression oracle for any compiler change).
- Prior art to port: one-layer `exec_*` unfolder lemmas
  (`CtrlStrtoullProof.lean`: `exec_seq_normal`, `exec_block_catch`,
  `exec_while_step/brk`, …), the hex0 step/fetch/frame lemma style
  (`RawAsm/Hex0/Refine.lean`, `LowIR/Hex0/CtrlProof.lean`), `Layout`/`Installed`/`Agree`
  shapes from old T1 (`LowIR.lean:325`). Old T1 `compile_sim` (line 370, the
  original flat IL) stays as a historical statement; **this campaign
  supersedes it — do not prove it**.
- `LowSSA/Core.lean` + `SSAProof/{ExecFacts,StrlenProof,Hex0Proof}.lean` — the
  upstream SSA experiment, since 2026-07-03 on the §8 rebind-in-environment
  `while` semantics (`iterWhile`: fixed loop term, carried values threaded as
  a value list — [RESUME-SSA-HEX0.md](RESUME-SSA-HEX0.md) §8). Not an input
  to `compile_sim` (Prog is the source IR here), but two things transfer:
  (a) its loop-proof pattern — per-head-entry step lemma, existential fuel
  per lemma, `*_mono` reconciliation — is the freshest worked style for the
  Phase-4.3 loop cases; (b) the planned SSA→Prog lowering simulation
  (LOWIR-SSA-EXPERIMENT assessment §1) will consume THIS campaign's theorems
  downstream — see the composability note in §7.

## 2. THE design obstacle, and decision P1 (resolve before any proving)

**Address divergence.** IL frames and machine frames live at different
addresses: the machine frame adds `[ra][slot per IL reg]` overhead, so after
one call the IL's `frameReg` value (= IL `sp`) and the machine's user-frame
base (= machine `sp + userOff`) differ, and diverge cumulatively with call
depth. Any value derived from `frameReg` (hex1's whole label table!) differs
between altitudes. A plain-equality simulation relation is therefore FALSE
for any program that touches its frame, and a CompCert-style memory
injection (per-value address translation) is unsound on our flat `BitVec 64`
words without provenance — you cannot tell a pointer from an integer. That
is the borrow layer's future job, not this cut's.

**Decision P1 — the frame-padding oracle: make the addresses EQUAL by
∀-quantified padding, with the compiler UNCHANGED.**

The key arithmetic fact (verify in the code: `Compile.lean` prologue,
`Prog.frameEnter`): the compiler already places the user frame at the TOP of
the machine frame, so its addresses are `[entry_sp − frameSize, entry_sp)` —
**identical to the IL's frame for the first activation**. Divergence is
purely the cumulative `[ra][slots]` overhead of ancestor activations. So:
extend `frameEnter` with a padding oracle `pad : Name → Nat` (a semantics
parameter alongside `dbase`/`stackLo`, ∀-quantifiable exactly like `sp₀`):

```
frameReg := sp − frameSize                 -- frame position UNCHANGED
sp'      := sp − frameSize − pad f         -- the hole the IL skips over
```

`compile_sim` instantiates `pad f := userOff f = 8*(maxRegF f + 2)`, and
then **IL `sp` = machine `x2` at every moment**, every frame coincides at
every depth, and the pad hole is byte-for-byte the machine's `[ra][slots]`
area. Also instantiate `dbase := fun d => codeBase + segStart + off d`
(`dataOffsetsFrom_shift` says this IS the compiler's table). Consequences:

- Every IL-visible value (registers, frame pointers, cref pointers,
  anything stored) is **numerically identical** on both sides: the relation
  is plain equality. No injection, no provenance, no value translation.
- **Zero compiler/shim/QEMU changes.** The change is confined to the IL
  semantics, and `pad := fun _ => 0` reproduces today's behavior exactly —
  every existing #guard/theorem re-greens with the default.
- The IL's own overflow check (`sp ≥ stackLo + frameSize + pad f`) now
  accounts for the machine's overhead too — the separate "stack budget"
  hypothesis this plan previously needed **disappears**.
- The differential harness gains a new power: instantiating `pad = userOff`
  in the IL side makes frame memory comparable BYTE-FOR-BYTE between
  altitudes (previously only rets/data regions were comparable). Add such
  tests in Phase 0 — they are the executable check of the whole P1 idea.
- IL-level program proofs quantify over `pad` (frames stay disjoint —
  padding only adds separation; frame-local reasoning is frameReg-relative
  and unaffected). ∀-`pad` is also future-proof: a later register allocator
  shrinking `userOff` changes only the instantiation, not program proofs.
- Const-data writes stay COHERENT (same addresses both sides); the
  footprint side condition shrinks to: no store into the code region or
  into the pad holes (the holes are listed by the `CallChain` ghost, §4
  Phase 5).

**Alternatives considered and rejected** (analyses from the 2026-07-02
design discussion — kept because the next reader will re-derive them):

- *Two-stack lowering* (x2 = ra+slots, new x3 mirroring IL sp): achieves the
  same equality but by CHANGING the compiler — burns a register, adds
  2 instrs/function, touches shim/harness/QEMU, and still needs the stack
  budget hypothesis (machine x2 use invisible to the IL check). The padding
  oracle dominates it on every axis; superseded.
- *Memory injection / two-way frame mapping*: needs to translate VALUES,
  not just addresses. σ must commute with `add`/`sub` (pointer arithmetic
  and integer arithmetic are the same instructions) ⇒ σ is a single global
  additive shift — but each activation needs a different shift. Per-value
  relational (CompCert-style) needs to know which words are pointers:
  untyped `BitVec 64` cannot say, and a disjunctive relation can't support
  the load case. Becomes expressible only when BorrowSig/typing lands —
  the right formulation for the TYPED IR above Prog, not for this cut.
- *Block-structured frames in the IL* (St carries a frame list; pointers
  become fat `(frameId, offset)` values — the CakeML stackLang / CompCert
  road): dissolves divergence and makes frames born-disjoint (killing the
  footprint side conditions), but it is a semantics rewrite (values become
  an ADT, every exec equation, program, harness changes), reverses recorded
  decisions D2/D5, narrows expressiveness (int↔ptr punning, byte-copying
  pointers become stuck), and RELOCATES rather than eliminates the
  correspondence work into a flattening/erasure pass of the same difficulty
  class (CakeML `stack_remove`, CompCert stacking). Right shape for the
  typed IR one rung up; wrong trade at the flat bottom rung. This plan
  harvests its benefit as ghost structure only (`CallChain`).
- *Observable-only equivalence*: too weak to compose across calls.

## 3. Theorem statements (write these FIRST, as `sorry`-free defs + sorry'd theorems)

### 3.1 The relation

```
structure Layout where          -- extends old T1's
  codeBase : Word
  instrs   : List Instr         -- = (compileProgT P entry).1
  fnTab    : List (Name × Nat)
  segStart : Nat                -- pad8 (4 * instrs.length)
  data     : Data

Installed L m : Prop            -- code: fetch32 at codeBase+4j decodes to instrs[j]
                                -- data: m.mem (codeBase+segStart+i) = (dataSegment data)[i]
                                -- (data half via dataSegment_at — already proved)

structure Regions where         -- the disjointness bundle (SimPre)
  -- the ONE stack [stackLo, sp₀) is shared (P1: same addresses); machine-
  -- private bytes are the pad holes inside it (listed by CallChain) plus
  -- the blob [codeBase, codeBase+segStart+|segment|); disjoint from every
  -- harness data region

StInv L fd (s : Prog.St) (m : Rv64i.State) : Prop :=
  m.rget 2 = s.sp                         -- the P1 payoff: sp ≡ x2, always
  ∧ (∀ r, 1 ≤ r → r ≤ maxRegF fd → s.rget r = m.loadWord (s.sp + slotOff r))
  ∧ Installed L m
  ∧ (∀ a, ¬ MachPriv a → s.mem a = m.mem a)   -- MachPriv = pad holes ∪ code region
  ∧ (frame-shape facts: alignment, current hole = [s.sp, s.sp + userOff fd), …)
```

### 3.2 The workhorse (statement-level, fuel-indexed)

```
lower_sim :
  exec P dbase stackLo fuel stmt s = some (s', oc) →
  wf P bD lD stmt →
  -- compile-time side: stmt was lowered at position pos with label env
  -- (brks, conts, epi) whose resolved addresses are A(brks[k]) etc.
  Emitted L pos stmt (brks, conts, epi) →
  m.pc = codeBase + pos → StInv L fd s m → Footprint-ok →
  ∃ k m', step^[k] m = m' ∧ StInv L fd s' m' ∧
    m'.pc = match oc with
            | .normal  => codeBase + endPos
            | .brk k   => A (brks[k])
            | .cont k  => A (conts[k])
            | .ret     => A epi
```

The outcome↔label-target correspondence IS the theorem — D3's design
(outcomes compile to jumps to the k-th enclosing label) becomes the
statement. **Induction on `fuel`** (NOT structural on stmt): `while` re-enters
itself and `call` enters another body at `fuel-1`, so the IL clock is the
only well-founded measure. Recursion (policy C5) is handled for free by the
same measure — note this and close C5.

Use `step^[k]` (plain iteration), NOT `runFuel halt` mid-proof — early-halt
checks poison composition. One bridge lemma at the top level converts to
`runFuel (codeBase+4)`.

### 3.3 Function- and program-level

```
call_sim   : marshalling + jal + prologue ⇒ StInv for frameEnter's state;
             body via lower_sim (fuel-1); epilogue + jalr ⇒ caller StInv
             restored, rets copied — mirrors exec's call equation exactly.
prog_sim   : run P … f args = some s'  ∧  SimPre …  →
             ∃ k, machine reaches halt with a0.. = rets values, memory
             agreement off MachPriv.
```

### 3.4 The footprint side condition

The address of an IL store is dynamic; the theorem needs "no store lands in
MachPriv". Do it the reusable way: an instrumented semantics
`execT : … → Option (St × Outcome × List Word)` returning the write
footprint + a (cheap, mechanical) `execT_erase : execT = some (s,o,ws) →
exec = some (s,o)` equivalence. Hypothesis: `ws.all (¬ MachPriv ·)`. This
also yields old T1's `NoSelfModify` for free and is per-program
dischargeable by the borrow-style `Wf` preconditions (hex0 proofs already
discharge exactly this shape via `storeByte_preserves`). Per-program
footprint bounds (e.g. "hex1 writes only [out, out+cap) ∪ its own frame")
become lemmas at the IL altitude — easy there, and they are the *interesting*
memory-safety statements anyway.

## 4. Proof architecture — phases, deliverables, risk

**Phase 0 — P1 + toolkit.** (blocks everything)
1. Implement P1: add the `pad : Name → Nat` oracle to `frameEnter`/`exec`/
   `run` (default `fun _ => 0` — everything existing re-greens unchanged;
   the compiler, shim, and QEMU artifacts are untouched and hereby FROZEN).
   Add the new differential tests with `pad := userOff`-instantiated IL
   runs comparing FRAME memory byte-for-byte — the executable validation of
   the whole P1 idea, before any lemma depends on it. Commit.
2. Port the one-layer unfolder lemmas to Prog: `exec_seq_normal`,
   `exec_block_*`, `exec_while_*`, `exec_call_*`, per-op equations
   (from `CtrlStrtoullProof.lean`, mostly mechanical renames + dbase/env
   params). NEVER `simp [exec] at h` with an IH in context (OOM — see the
   gotcha memory); these lemmas exist to make that unnecessary.
3. `execT` + erasure (§3.4).
   *Risk: low. Size: ~400 lines.*

**Phase 1 — encode/decode generically.** `decode (encode i) = i` per
constructor, ∀ operands in range (rd/rs < 32, sh < 64, imm any). Today this
is only checked per-program by `native_decide`. Two routes: (a) restate
`encode`'s field packing in BitVec form and hit each constructor with
`bv_decide`/`bv_omega` after bounding Nat operands; (b) hand bit-arithmetic
à la `RvCross.v`'s decode half. Try (a) first; budget for (b).
*Risk: MEDIUM (known painful bit-fiddling). Size: ~600 lines. Fully
parallel to Phases 2-3; can start immediately.*

**Phase 2 — the assembler layer (layout/resolve).**
- `symSize`-consistency: `(resolveOne … (pos,si)).length * 4 = symSize si`;
  `progBytes` indexing: instruction j's 4 bytes sit at its `layout` position
  (list-flatten arithmetic, same flavor as the already-proved
  `dataSegment_at` — reuse its induction pattern).
- Label soundness: `fresh` monotonicity ⇒ label nodup ⇒ `lbls.lookup` is THE
  address; every emitted `.br/.jmp/.callf/.cref` resolves to a target that
  is a real position in the stream (br within the function, callf to
  `fnTab`, cref to `segStart + dataOffsetsFrom` — `dataOffsetsFrom_shift`
  closes the loop).
- Immediate roundtrips under the resolve range checks:
  `(BitVec.ofInt 13 δ).signExtend 64 = BitVec.ofInt 64 δ` for
  `-4096 ≤ δ ≤ 4094`, ditto 21-bit; `synthConst_correct` (3 steps compute
  `ofInt v`, |v| < 2²³) and the `cref` 5-step lemma including the
  **jal-pc-read** equation (`jal rd, +4` ⇒ rd := pc+4, pc := pc+4).
- `Installed`-from-`progBytes` + preservation under off-code stores
  (hex0's `code_preserved` pattern).
  *Risk: low-medium, high volume. Size: ~1000 lines.*

**Phase 3 — StInv algebra ("slot facts").** Slot read/write lemmas: store
to slot r updates `loadWord` at r, preserves other slots (8-byte
disjointness arithmetic), preserves `Installed` and off-MachPriv memory;
`rget/rset` ↔ slot-store correspondence incl. the r=0 discard/li-0 cases;
x3 untouched by op lowerings. This is `li_block_frame`-style plumbing —
tedious, well-understood.
*Risk: low. Size: ~600 lines.*

**Phase 4 — `lower_sim`, non-call cases.** The big fuel induction, cases in
this order (each case = commit):
1. skip/annot, ops (arith, shifts) — validates the whole pipeline on
   4-instruction slices. **Do this as the VERTICAL SLICE first**: state
   everything in §3, prove only these cases, leave the rest `sorry`, and
   check a toy end-to-end corollary (sub3-class) against the differential
   oracle. If the relation is wrong, it is wrong HERE, cheaply.
2. IL memory ops (lbu/sb/ld/sd) — first footprint use; address equality is
   the P1 payoff (IL address = machine address, literally).
3. seq (outcome-threading composition), ife (branch resolve + join),
   block/brkB/contL/ret (pure pcOut bookkeeping), while (fuel IH).
4. cref/clen — `synthConst_correct` + `installData_at`/`Installed`-data.
   *Risk: medium. Size: ~1500 lines.*

**Phase 5 — the call case + `call_sim`.** The summit. Sub-lemmas:
- `prologue_sim`: machine prologue from a call-entry state establishes
  `StInv` against `frameEnter`'s IL state — zero-init ↔ `sd x0` zeroing
  (this equation is WHY the prologue zeroes; designed for this moment),
  param parking ↔ `withParams` fold (both last-wins — prove the fold/store
  agreement lemma), frameReg slot := x3.
- `epilogue_sim`: rets → a-regs, ra/x2/x3 restore, jalr lands at call
  site + 4.
- **Stack discipline**: callee's x2 frame and x3 frame are strictly below
  the caller's; callee stores (slots + footprint-checked user stores)
  preserve the CALLER's slots and saved ra. LIFO by D8's structural sp
  restore — state as `CallChain` invariant (list of (raAddr, x2, x3) per
  activation, strictly decreasing, pairwise disjoint). Prior art: CakeML
  stackLang, bedrock2 — but our D7/D8 (no alloca, structural restore,
  activation-local registers) is deliberately the easy case.
- Stack budget: SOLVED by P1 — with `pad = userOff` the IL's own overflow
  check (`sp ≥ stackLo + frameSize + pad f`) already accounts for the
  machine's slot overhead; no separate hypothesis.
  *Risk: HIGH — this is where the unknown unknowns live. Size: ~1500 lines.
  De-risk by proving `prologue_sim`/`epilogue_sim` standalone against the
  differential oracle before touching the induction case.*

**Phase 6 — `prog_sim` + transport demos.** Entry stub step, halt-pad
bridge to `runFuel (codeBase+4)`, observable extraction. Then the payoff
demos: compose with an IL-level `strlenF_correct` (prove it — small, the
Ctrl strlen proof is the template) to get bytes-level strlen correctness;
state the same for hex0F against `Hex0.coreSpec` as the eventual
tower-closing corollary (its IL proof is a separate later campaign —
`CtrlHex0Proof.lean` is the blueprint but on Prog now).
*Risk: low once 5 lands. Size: ~500 lines.*

Total honest estimate: **5–7k lines, dominated by Phases 2/4/5**; comparable
to one hex0-Refine but amortized over every program forever. Lean-first
(this codebase's Lean/Coq experience: invention in Lean ≈ 2× transcription;
no Coq port planned for this layer).

## 5. File & build plan

```
lean/LowIR/ProgSim/ExecFacts.lean    Phase 0.2  (42 exec_* unfolders)        [DONE]
lean/LowIR/ProgSim/Defs.lean         Layout/Installed/StInv/SimPre, execT     [DRAFTED]
                                       + execT_erase (0.3); prog_sim sorry'd
lean/LowIR/ProgSim/WordMem.lean      Phase 3 start (LE load/store algebra)    [DONE]
lean/LowIR/ProgSim/SlotFacts.lean    Phase 3 finish (StInv slot algebra)      [DONE]
lean/LowIR/ProgSim/EncodeFacts.lean  Phase 1
lean/LowIR/ProgSim/AsmFacts.lean     Phase 2
lean/LowIR/ProgSim/StmtSim.lean      Phase 4 (the induction)
lean/LowIR/ProgSim/CallSim.lean      Phase 5
lean/LowIR/ProgSim/Main.lean         Phase 6 (prog_sim + corollaries)
```

The lib root is currently `LowIR.ProgSim.Defs` (not `Main.lean` yet, which
doesn't exist); it transitively pulls ExecFacts + WordMem. Repoint the root to
`Main.lean` when Phase 6 lands.

⚠ Build-root trap: add a `lean_lib LowIRProgSim` with
`roots = ["LowIR.ProgSim.Main"]` to `lakefile.toml` **in the same commit
that creates the first file**, and decide then whether it joins
`defaultTargets` (yes while it elaborates fast; revisit if elaboration
crosses ~1 min). Check individual files with `lake env lean` during work.

## 6. Discipline (from the gotcha memories — they were all paid for)

- One-layer unfolder lemmas instead of `simp [exec]` anywhere an IH is in
  scope (OOM). `autorewrite`-style targeted `rw` chains.
- `omega` on conjunction/iff goals pulls in `Classical.choice` — split
  first if axiom hygiene matters for the final `#print axioms`.
- Commit at every green sub-case (the per-case list in Phase 4 is the
  commit granularity). Keep `#print axioms compile_sim`-style checks in
  Main.lean from day one (target: `[propext, Quot.sound]`).
- Every relation definition gets `#guard`-level executable sanity checks
  against the differential harness states BEFORE any lemma uses it (a
  wrong `StInv` found by a failing `decide` costs minutes; found inside
  Phase 5 it costs weeks).
- The differential suite is the spec oracle: any lemma statement that
  cannot be instantiated on the sub3/caller/recSum states is misstated.

## 7. Open questions (decide during Phase 0, none block the statement work)

1. **pad signature**: `Name → Nat` (per-function, matches the compiler) vs
   a per-activation oracle. Per-function suffices for this compiler; keep
   the simpler form until something forces generality.
2. **fnOk freeze**: unchanged by P1 (`totalFrame ≤ 2000` stands — the pad
   equals `userOff`, already inside `totalFrame`).
3. **Footprint granularity**: global `ws.all (¬ MachPriv ·)` first;
   per-activation refinement only if the caller-slot-preservation proof
   wants it (Phase 5 will tell).
4. **BorrowSig integration**: after this campaign, the borrow layer should
   DISCHARGE footprint hypotheses instead of assuming them — leave hooks
   (footprint as a def, not inlined into the theorem).
5. Whether `exec.induct` (functional induction) beats hand-rolled fuel
   induction — try on the vertical slice; abandon without sentiment if the
   generated motive fights back.
6. **SSA→Prog composability (post-campaign; SSA side unblocked 2026-07-03).**
   The SSA experiment's graduation path lowers SSA→Prog and reuses this
   campaign unchanged (LOWIR-SSA-EXPERIMENT assessment §1 — do not fork the
   compiler). With the §8 `iterWhile` semantics the loop terms are fixed on
   BOTH sides, so the lowering simulation's `while` case becomes a
   per-head-entry correspondence: an SSA `iterWhile` entry (value tuple
   `vals`) ↔ a Prog `while` entry (the lowered `args` registers hold `vals`;
   an SSA `cont 0 [vs]` edge = the parallel copy into them), with
   `iterWhile_mono`/`iterWhile_frame` as the ready-made SSA-side interface —
   under the old rebuild semantics this would have related a *family* of SSA
   terms to one Prog term. Consequence for NOW: keep `lower_sim`/`prog_sim`
   statement shapes friendly to that composition (fuel-indexed,
   outcome-carrying, plain-equality state relation), so SSA→Prog→RV64I chains
   without re-litigating either pass.

## 8. Immediate next actions (cold-start order)

- [x] Phase 0.1: P1 pad oracle in Prog (compiler untouched); re-green with
  `pad 0`; `pad = userOff` frame-memory differential tests. Committed.
- [x] Phase 0.2: 42 one-layer `exec_*` unfolders (`ProgSim/ExecFacts.lean`).
- [x] Phase 0.3: `execT` + `execT_erase` (`ProgSim/Defs.lean`).
- [x] `ProgSim/Defs.lean` §3 statements: real defs `#guard`'d, `prog_sim`
  `sorry`'d, `LowIRProgSim` lib target in `defaultTargets`.
- [x] Phase 3 (start): `ProgSim/WordMem.lean` — LE load/store algebra. `f513c27`.
- [x] **Phase 3 (finish): StInv slot algebra** — `ProgSim/SlotFacts.lean`:
  `rget/rset` ↔ slot-store (`StInv_store_slot`), 8-byte slot disjointness,
  `Installed`/off-MachPriv preservation under a slot store. All `[propext,
  Quot.sound]` (retrofitted the same onto WordMem's `byte_bit`/round-trip).
- [x] **Vertical slice (Phase 4.1) — GO, straight-line slice COMPLETE.**
  `ProgSim/StmtSim.lean`: `emit`/`Emitted`/`lower_sim`; skip, annot, all six
  arithmetic ops (addi/add/sub/orr/slli/srli, every register value) and seq proven
  end-to-end against the machine `step`, factored through `run_load`/`run_store` +
  `single_op_sim`/`two_op_sim`, all `[propext, Quot.sound]` (commits 9329154,
  e688c5a, dade03c).
- [x] Toy sub3 corollary against the differential oracle — DONE, `sorry`-free
  (`sub3_body_sim` via `two_op_sim` directly; oracle value 40 via `native_decide`).
- [x] **Phase 4.2 memory ops — DONE (ld/sd/lbu/sb).** `ProgSim/MemFacts.lean`
  (StInv_store{Word,Byte}_user, loadWord_agree_off, range_disjoint_of_bytes) +
  the four `lower_sim` cases via a `MemAccOff` access side-condition, all
  `[propext, Quot.sound]`. `#guard` on frameLocal.body.
- [x] **Phase 4.3 control-flow foundation + leaf ops — DONE (ret/brkB/contL).**
  `step_{jal,beq,blt,bge,bgeu}`, `signExtend_ofInt_{21,13}`, `jump_lands`,
  `jump_sim`, and `ret_sim`/`brkB_sim`/`contL_sim`, all `[propext, Quot.sound]`.
- [ ] Finish `lower_sim`: the COMPOUND control-flow ops (ife/while/block) via the
  outcome-carrying generalization + label-position map (design in the Phase-4.3
  status entry above), then cref/clen, then call.
- [ ] Then Phases 1/2 (encode/decode, assembler) in parallel-friendly chunks,
  the rest of 4, 5, 6 in order.
