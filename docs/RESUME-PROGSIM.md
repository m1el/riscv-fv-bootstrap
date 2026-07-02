# RESUME — proving `compile_sim` for Prog (D7/D8 compiler correctness)

Plan written 2026-07-02, immediately after the executable cut landed. Nothing
here is started; this is the handoff for the verification campaign. Read with
[LOWIR-DESIGN.md](LOWIR-DESIGN.md) (D7/D8, Ext. 12, §4 pass decomposition),
[PROGRESS.md](PROGRESS.md) (what exists), [archive/RESUME-LOWIR.md](archive/RESUME-LOWIR.md)
(the hex0-era proof toolbox and gotchas — much of it ports).

## 0. Mission and payoff

Prove: **if the D7/D8 IL says a program computes something, the compiled RV64I
bytes compute the same thing on the trusted `Rv64i` model.** This is the T1
of `LowIR.lean:312` re-targeted at the real IR (functions, frames, calls,
const data) — the pass that amortizes the flat-PC simulation cost paid
per-program in `Hex0/Refine.lean` (~3400 lines for ONE program) into ONE
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
  **x3 is free** (see P1 below — it will be taken).
- `LowIR/ProgLib.lean` + `CompileTests.lean` — the programs and the
  differential batteries (the regression oracle for any compiler change).
- Prior art to port: one-layer `exec_*` unfolder lemmas
  (`CtrlStrtoullProof.lean`: `exec_seq_normal`, `exec_block_catch`,
  `exec_while_step/brk`, …), the hex0 step/fetch/frame lemma style
  (`Hex0/Refine.lean`, `LowIR/CtrlHex0Proof.lean`), `Layout`/`Installed`/`Agree`
  shapes from old T1 (`LowIR.lean:325`). Old T1 `compile_sim` (line 370, the
  original flat IL) stays as a historical statement; **this campaign
  supersedes it — do not prove it**.

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

**Decision P1 — two-stack lowering: make the addresses EQUAL by construction.**
Change the compiler so the machine keeps:

- **x2** = the *machine* stack: `[saved ra][slots]` only
  (`slotArea fd = 8*(maxRegF+2)`), a region the IL cannot name;
- **x3** = the *IL semantic sp*, exactly mirroring D8: prologue
  `addi x3, x3, -frameSize`, `frameReg` slot := x3; epilogue
  `addi x3, x3, +frameSize`. User frames live in the x3 stack at
  **exactly the IL's addresses** (same `sp₀` given to both sides).

Additionally instantiate the IL's `dbase` at composition time as
`fun d => codeBase + segStart + off d` (legitimate — the IL theorem
∀-quantifies `dbase`; `dataOffsetsFrom_shift` says this IS the compiler's
table). Consequences:

- Every IL-visible value (registers, frame pointers, cref pointers, anything
  stored in memory) is **numerically identical** on both sides. The
  simulation relation is plain equality on registers-in-slots and on memory
  outside the machine-private regions. No injection, no provenance.
- Const-data writes stay COHERENT (both sides write the same address), so
  the no-write side condition shrinks to: no store into the code region
  `[codeBase, codeBase+segStart)` or the machine x2-stack region.
- Cost: 2 extra instructions per prologue/epilogue; harness/shim set x3;
  `fnOk` splits into `slotArea ≤ 2000 ∧ frameSize ≤ 2000` (looser than
  today). All differential tests + QEMU must be re-validated after the
  change (mechanical; blob changes).

*Rejected:* memory injection (needs provenance = borrow layer; revisit when
BorrowSig lands); observable-only equivalence (too weak to compose);
address-translating relation chosen per-execution (not stateable).

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
  mstackLo mstackHi : Word      -- x2 stack (machine-private)
  -- disjoint from: blob [codeBase, codeBase+segStart+|segment|),
  -- the IL stack [stackLo, sp₀), and every harness data region

StInv L fd (s : Prog.St) (m : Rv64i.State) : Prop :=
  (∀ r, 1 ≤ r → r ≤ maxRegF fd → s.rget r = m.loadWord (m.rget 2 + slotOff r))
  ∧ m.rget 3 = s.sp                       -- the two-stack payoff
  ∧ Installed L m
  ∧ (∀ a, ¬ MachPriv a → s.mem a = m.mem a)   -- MachPriv = x2 region ∪ code region
  ∧ (frame-shape facts: m.rget 2 in the x2 region, aligned, …)
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

**Phase 0 — freeze the compiler + toolkit.** (blocks everything)
1. Implement P1 (two-stack). Re-green: Prog #guards, all differential
   theorems, QEMU (regen dump; shim sets x3). Commit. The compiler is then
   FROZEN for the campaign — any change re-opens every phase.
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
- Stack budget: machine x2 use = Σ slotArea over the active chain, NOT
  visible to the IL's overflow check. Hypothesis in `SimPre`:
  `activationBound × maxSlotArea ≤ mstack size` with
  `activationBound := fuel` (crude, sound: each activation costs ≥1 fuel).
  Refine later if it pinches.
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
lean/LowIR/ProgSim/Defs.lean       Layout/Installed/Regions/StInv/SimPre, execT
lean/LowIR/ProgSim/EncodeFacts.lean  Phase 1
lean/LowIR/ProgSim/AsmFacts.lean     Phase 2
lean/LowIR/ProgSim/SlotFacts.lean    Phase 3
lean/LowIR/ProgSim/StmtSim.lean      Phase 4 (the induction)
lean/LowIR/ProgSim/CallSim.lean      Phase 5
lean/LowIR/ProgSim/Main.lean         Phase 6 (prog_sim + corollaries)
```

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

1. **x3 choice**: gp is ABI-reserved but we own the whole machine; x3 vs x4
   — pick x3, document in Compile.lean header. Any objection dissolves at
   bare-metal.
2. **fnOk freeze**: split bound (`slotArea ≤ 2000 ∧ frameSize ≤ 2000`) —
   settle exact constants in P1.
3. **Footprint granularity**: global `ws.all (¬ MachPriv ·)` first;
   per-activation refinement only if the caller-slot-preservation proof
   wants it (Phase 5 will tell).
4. **BorrowSig integration**: after this campaign, the borrow layer should
   DISCHARGE footprint hypotheses instead of assuming them — leave hooks
   (footprint as a def, not inlined into the theorem).
5. Whether `exec.induct` (functional induction) beats hand-rolled fuel
   induction — try on the vertical slice; abandon without sentiment if the
   generated motive fights back.

## 8. Immediate next actions (cold-start order)

1. Phase 0.1: implement P1 two-stack lowering; re-green everything; commit.
2. Write `ProgSim/Defs.lean` complete with all §3 statements (`sorry`'d
   theorems, real defs) + lib target; `#guard` the defs on harness states;
   commit.
3. Vertical slice (Phase 4.1 through `prog_sim` for straight-line): the
   go/no-go checkpoint for the whole relation design.
4. Then Phases 1/2/3 in parallel-friendly chunks, 4, 5, 6 in order.
