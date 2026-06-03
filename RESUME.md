# RESUME — handoff for task #7 (ISA cross-check vs `riscv-coq`)

Read with `STATUS.md` (state), `CROSSCHECK.md` (the full task-#7 design + per-instruction
mapping), `TCB.md` (trust boundary). This file is the **technical** handoff: the
environment, the gotchas that cost real time, what's proved, and the exact remaining work.

The earlier frontier (closing the last `core_refines` `sorry`/`Admitted`) is **DONE** in
both Lean and Coq — see the git log and `PROOF.md`. The live frontier is now task #7.

## TL;DR of where we are

- **Everything builds green**: `cd coq && make -jN`; `cd lean && lake build`; `cd bare && make run` → `Hello\n`.
- **T1 (decode cross-check) is COMPLETE** — `coq/RvCross.v`, `decode_agrees`. Our
  `Rv64i.decode` is proved equal to `riscv-coq`'s `Decode.decode RV64I` on all 12 forms,
  for every 32-bit word. `Admitted`-free; `Print Assumptions decode_agrees` ⇒ **Closed
  under the global context (ZERO axioms)**. The decoder is no longer in the TCB.
- **T2 (execute/step cross-check) — all reusable infrastructure is proved**, in
  `coq/RvCrossStep.v` (`Admitted`-free): word bridge, fetch bridge, `run1` reduction
  toolkit, bridge relation `Rrel`, bridge corollaries. **Remaining: the 12 per-instruction
  `exec_*` lemmas + `step_agrees` + the transport corollary `core_refines_riscv`.** The
  per-instruction recipe was validated end-to-end in scratch; nothing unsolved remains.
- Work is on branch **`isa-crosscheck-decode`** (4 commits). Not merged to master.

## Build / check

```
export PATH=~/.opam/CP.2025.01.0~8.20~2025.01/bin:$PATH    # has coqc 8.20, NOT on PATH by default
cd coq && make -jN                                          # whole Coq dev incl. RvCross.v + RvCrossStep.v
coqc -q -R . Hex0Coq RvCrossStep.v                          # type-check one file directly (no make)
echo 'Require Import Hex0Coq.RvCross. Print Assumptions decode_agrees.' | coqc-stdin   # axioms
grep -rnE '^\s*(Admitted|admit)' coq/*.v                    # remaining holes (should be none)
```

`opam` is NOT on PATH; the switch is `~/.opam/CP.2025.01.0~8.20~2025.01`. New files must be
added to `coq/_CoqProject` (the Makefile auto-regenerates from it: `rm -f Makefile Makefile.conf`
is unnecessary, `make` rebuilds the rule).

## The oracle (this was the key discovery)

`RESUME` used to say the only ISA oracle was `sail-riscv-lean` (171k LoC, WIP, not
executable). **WRONG / obsolete**: the opam switch already has **`coq-riscv.0.0.5`** (the MIT
`riscv-coq` / riscv-semantics model — the bedrock2/`compiler` spec, `hs-to-coq` from the
official Haskell) + **`coq-coqutil.0.0.6`** + **`bedrock2`**, all in
`~/.opam/.../lib/coq/user-contrib/{riscv,coqutil,bedrock2}/`, on the default load path
(`Require Import riscv.Spec.Decode.` just works). All 12 of our instruction forms exist in
its `InstructionI`. **Do the Coq proof against `riscv-coq`; the Lean side stays
testing-backed (or a separate `sail-riscv-lean` decode-only differential later).**

Key files in the oracle (paths under `…/user-contrib/riscv/`):
- `Spec/Decode.v` — `decode : InstructionSet -> Z -> Instruction`; `Instruction` wraps
  `InstructionI` via `IInstruction`, rejects via `InvalidInstruction (i:Z)`. For `RV64I`
  the result list collapses so a valid `decodeI` ⇒ `IInstruction decodeI`.
- `Spec/ExecuteI.v` — `execute : InstructionI -> p unit`, monadic over `RiscvMachine p t`.
- `Spec/Machine.v` — the `RiscvProgram`/`RiscvMachine` classes (`getRegister/setRegister/
  getPC/setPC/loadByte/storeByte/endCycleNormal/…`).
- `Platform/Minimal.v` — `IsRiscvMachine : RiscvProgram (OState RiscvMachine) word`. `OState
  S A = S -> option A * S`. `setPC` writes **`getNextPc`**, not `getPc`; `endCycleNormal`
  does `pc := nextPc; nextPc := nextPc + 4` (so invariant `nextPc = pc + 4` holds each cycle).
- `Platform/Run.v` — `run1 iset = pc<-getPC; inst<-loadWord Fetch pc; execute (decode iset
  (combine 4 inst));; endCycleNormal`.
- `Platform/RiscvMachine.v` — the state record (`getRegs : map Z word; getPc; getNextPc;
  getMem : map word byte; getXAddrs; getLog`). `loadWord Fetch` fails unless `isXAddr4B`.
- `Utility/MkMachineWidth.v` — `+`=`word.add`, `or`=`word.or`, signed `<`=`word.lts`,
  `ltu`=`word.ltu`, `sll w n`=`word.slu w (of_Z n)`, `ZToReg`/`fromImm`=`word.of_Z`,
  `uInt8ToReg a`=`of_Z (combine 1 a)`, `regToInt8 a`=`split 1 (unsigned a)`, `reg_eqb`=`word.eqb`.

## GOTCHAS that cost real time — do not rediscover

1. **STRICT GOAL SELECTOR.** Importing coqutil/bedrock2 turns on a strict focusing
   discipline: after **every** `destruct`/`split`/`induction` that leaves >1 goal you MUST
   use bullets (`-`/`+`/`*`) or `[ .. | .. ]`. Symptom: `Error: Expected a single focused
   goal but 2 goals are focused`, reported at the *next* tactic. This bit me ~6 times. Write
   bullets from the start.
2. **`cbn`/`simpl` will NOT unfold `combine_deprecated` or `le_combine`** (coqutil Fixpoints).
   For the fetch combine: `rewrite combine_eq` (→ `le_combine (tuple.to_list bs)`), then
   `cbn [HList.tuple.to_list]`, then **`cbv [LittleEndianList.le_combine]`** (cbv, not cbn).
   Note `LittleEndian.combine` is a *notation* for `combine_deprecated`; the constant name is
   `combine_deprecated` (unqualified), `le_combine` is `LittleEndianList.le_combine`.
3. **`run1` / Minimal `OState` reduction recipe** (proved as `run1_fetch`):
   `unfold Run.run1, Machine.getPC, Machine.loadWord, IsRiscvMachine, loadN, fail_if_None.
   cbv [Bind Return OState_Monad get put]. cbn [fst snd].` then `rewrite Hload, HxAddr.` Use
   the **qualified** projection names (`Machine.getPC`, `Machine.loadWord`, `Machine.getRegister`,
   `Machine.setRegister`) — `unfold getPC` (the field) does NOT touch `Machine.getPC` (the
   projection). `get`/`put` are `OStateOperations.{get,put}` (need `Import OStateOperations`).
4. **decode reduction recipe** (T1, in `RvCross.v`): `Opaque bitSlice signExtend Z.shiftl
   Z.lor` so `cbn` reduces only riscv's decode control-flow and leaves operands abstract;
   `rewrite` the control fields (opcode/funct3/funct7) to concrete via `bs_f`; `cbn`; convert
   operands `field`↔`bitSlice` (`bs_f`/`f_bs`) and `sext`↔`signExtend` (`sext_signExtend`,
   range via `range_tac`); close the `lor`-reassociation with **`with_strategy transparent
   [bitSlice] prove_Zeq_bitwise`** (coqutil's bitwise prover; `Opaque` blocks its `unfold
   bitSlice`, hence `with_strategy`).
5. **`field w lo len = bitSlice w lo (lo+len)`** (= our div/mod vs coqutil land/shiftr) via
   `coqutil.Z.BitOps.bitSlice_alt`. `bs_f w a b c : 0<=a -> b=a+c -> 0<=c -> bitSlice w a b =
   field w a c` (the `b=a+c` is discharged by `lia`, normalizing the `lo+len` literal).
6. **`sext k = signExtend k` only on in-range inputs** (`0<=raw<2^k`); the range for
   `lor`/`shiftl` immediates is discharged by `range_tac` (= `repeat first [apply lor_lt |
   apply shiftl_field_lt | apply field_lt]; lia`). The SLLI `shamt≥32` narrowing does **not**
   affect T1 (only the reverse direction).
7. **`Register0` reduces to `0`** (it's effectively `Z0`) — `unfold Register0` fails ("Cannot
   coerce Z0 to evaluable reference"). To discharge the `r = Register0` branch: `exfalso; cbn
   in E; lia`.
8. **Word address arithmetic**: `Require Import bedrock2.ZnWords` and use `ZnWords` to prove
   word identities like `word.add (word.add pc (of_Z 1)) (of_Z 1) = word.add pc (of_Z 2)`.
   For `word.add (of_Z a)(of_Z b) = of_Z (wadd a b)` use `word.unsigned_inj` + `br_add` +
   `Z.add_mod` (proved as `wadd_of_Z`).
9. **`word.of_Z` in a lemma statement needs `(word:=word)`** or elaboration can't infer the
   width (`Could not find an instance for "Interface.word ?width"`).
10. **The `RiscvMachine` record accessors need a `Bitwidth 64` instance** in context: add
    `Context {BW: Bitwidth 64}` (from `coqutil.Word.Bitwidth`).
11. Concrete instantiation (if ever needed instead of the abstract Section context): `riscv.
    Utility.Words64Naive` (word) + `riscv.Utility.DefaultMemImpl64` (Mem) + `coqutil.Map.
    Z_keyed_SortedListMap.Zkeyed_map` (Registers). Verified `run1 RV64I : RiscvMachine ->
    option unit * RiscvMachine` type-checks.

## What's proved (file map)

**`coq/RvCross.v`** (T1, decode):
- bridges `field_bitSlice`, `sext_signExtend`; range toolkit `field_range/field_lt/lor_lt/
  shiftl_field_lt` + `range_tac`; `field_sub0` (subfield-of-zero, for SLLI's funct6/shamtHi
  from funct7=0); `bs_f`/`f_bs`; `embed : Rv64i.Instr -> Decode.Instruction`.
- per-form `decode_addi/slli/add/or/lbu/sb/beq/blt/bge/bgeu/jal/jalr` (each: control rewrite →
  `cbn` → convert → `prove_Zeq_bitwise`).
- `decode_agrees` (opcode/funct dispatch; error leaves ⇒ contradict `i≠Iunknown`).

**`coq/RvCrossStep.v`** (T2 infrastructure):
- helpers `byte_uoz`, `testbit_hi`, `land_lo_hi`.
- `WordBridge` section: `wrap64`, `br_add`, `br_or`, `br_ltu`, `toS_signed`, `br_lts`,
  `wadd_of_Z`.
- `Fetch` section: `fetch_combine` — `combine 4 (load_bytes 4 rm pc) = f0+f1·256+f2·2¹⁶+f3·2²⁴`
  given the 4 map bytes (this is our `fetch32`). THE KEYSTONE.
- `Run1` section: `run1_fetch` (run1 → `execute (decode …)` + `endCycleNormal`), `getReg_red`,
  `setReg_red`, `endcycle_red`.
- `Bridge` section: `RegAgree`, `MemAgree D`, `PcAgree`, `Rrel = RegAgree ∧ MemAgree D ∧
  PcAgree`, `WFfetch`, and `getReg_R` (register read under `RegAgree`, x0-aware).

## The remaining T2 work (the recipe, validated in scratch)

For each instruction, prove `exec_<i> : Rrel s m D -> <fetch-WF> -> Rv64i.decode (fetch32 s) =
I<i> … -> ∃ m', run1 RV64I m = (Some tt, m') ∧ Rrel (Rv64i.step s) m' D`. Recipe:

1. **fetch connection** (shared lemma to write): from `Rrel`+`MemAgree`(4 fetch addrs in D)+
   no-wrap, get `∃ bs, load_bytes 4 (getMem m) (getPc m) = Some bs ∧ combine 4 bs = fetch32 s`.
   Use `fetch_combine` with `f := fun i => s.mem (s.pc + i)`; the address bridge is
   `unsigned (word.add (getPc m) (of_Z i)) = s.pc + i` (i<4, no wrap) via `word.unsigned_add`+
   `unsigned_of_Z`+`mod_small` (or `ZnWords`). `fetch32 s` range `0 ≤ _ < 2^32` from bytes<256.
2. `isXAddr4 → isXAddr4B = true` (need `isXAddr1B` reflect lemma; search `isXAddr1B_holds`/its
   converse in `Platform/RiscvMachine.v`).
3. `run1_fetch` → goal is about `execute (decode RV64I (combine 4 bs)) m`. Rewrite
   `combine 4 bs = fetch32 s`, then `decode_agrees` (T1) ⇒ `decode RV64I (fetch32 s) =
   embed (Rv64i.decode (fetch32 s)) = IInstruction (<ctor> …)` (needs `fetch32 s` in range +
   `≠ Iunknown`, the hypothesis).
4. `Execute.execute (IInstruction c) = ExecuteI.execute c` — `cbn [Execute.execute]`.
   Reduce the `ExecuteI.execute` body (a `Bind` chain) with `getReg_R` (reads) and
   `setReg_red` (writes) + `cbv [Bind Return OState_Monad]`. The written word is
   `word.add (of_Z (rget s rs1)) (of_Z imm)` = `of_Z (wadd …)` by `wadd_of_Z`.
5. `endcycle_red` advances pc.
6. Reassemble `Rrel (step s) m' D`: `RegAgree` via `map.get_put_same`/`get_put_diff`
   (`coqutil.Map.Properties`) + `wadd_of_Z`; `MemAgree` unchanged for non-memory instrs
   (m' mem = m mem); `PcAgree` from `endcycle_red` + `PcAgree m` (pc:=nextPc=pc+4=`wadd s.pc 4`).

Per-instruction specifics (see `CROSSCHECK.md` §4–6):
- **x0 casing**: `getReg_R` handles `rs1=0`. For `rd=0`, `setRegister 0 = Return tt` (no
  change) and `rset s 0` ignores — needs a separate small reduction (`setReg0_red`) and the
  `RegAgree` is trivially preserved.
- **branches** (`beq/blt/bge/bgeu`): no register write; pc = taken? `wadd pc imm` : `pc+4`.
  riscv raises a **misaligned-target exception** if `newPC mod 4 ≠ 0` → precondition "target
  4-aligned" (true for `core`; see §5). Guards bridge via `br_ltu`/`br_lts`/`word.eqb`↔`=`.
- **`lbu`**: `loadByte` reads `getMem` (data addr must be in D); `uInt8ToReg` zero-extends ⇒
  our `mod 256`. Need a `loadByte_red` like `getReg_red`.
- **`sb`**: `storeByte` = `storeN 1` = `putmany_of_tuple` (1-tuple) on `getMem`; updates
  `MemAgree` at the store addr (others preserved via `map.get_put_diff`), needs store addr ∈ D
  and the output-region disjointness (reuse the `Refine.v` geometry). The genuinely new piece.
- **`jal`/`jalr`**: register write (`rd := pc+4`) + pc jump; `jalr` clears bit 0
  (`and _ (lnot 1)` = our `a - a mod 2`); same alignment precondition as branches.

Then **`step_agrees`** = dispatch on `Rv64i.decode (fetch32 s)` to the 12 `exec_*`.

**Transport corollary `core_refines_riscv`** (the real deliverable): frame `step_agrees` as a
forward simulation, induct (like `loop_correct`) to lift the whole run, and compose with the
finished `core_refines` so the *reference model running the real bytes* computes `coreSpec`.
Needs a prologue lemma `init_riscv inp cap` is `Rrel`-related to our `mkInit` (analogue of
`init_loopinv`). See `CROSSCHECK.md` §1 (T2) and the answer recorded there about "use the
reference model instead" = sense (b), transport.

## Lean-side notes (still true, lower priority)

- Lean is 4.30.0 via elan, **no Mathlib**. Banned: `norm_num`, `ring`, `set…with`. Use
  `decide`/`omega`/`simp`/`Nat.le_refl`. `lake build`'s root must import a file or it's skipped
  (`lake env lean Hex0/Foo.lean` to check directly). See `lean-build-root` memory.
- `core_refines` is `sorry`-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- A Lean execute/step cross-check would need `sail-riscv-lean` (171k LoC, WIP) — deferred; the
  Coq cross-check + the existing Lean↔Coq computational cross-validation (`Validate.*`) cover it.
