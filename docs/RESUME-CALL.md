# RESUME-CALL — Phase 5: the `call` case of `lower_sim_cf`

Plan written 2026-07-04, when `call` became the ONLY remaining statement-level
`sorry` (`CtrlSim.lean:886`, in `lean/LowIR/ProgSim/`). Read with
[RESUME-PROGSIM.md](RESUME-PROGSIM.md) (the campaign handoff — §2 P1, §4
Phase 5 sketch, §6 discipline); this doc supersedes that Phase-5 sketch with a
worked design. Everything below is grounded in the code as of commit `5a88ef2`;
line numbers refer to that state.

## 0. Mission

Close `lower_sim_cf`'s `call` case. After it: no statement-level `sorry`
remains; what's left of the campaign is Phases 1/2 (encode/decode + AsmFacts
discharging the flat layout hypotheses) and Phase 6 (`prog_sim`).

**The headline design answer** (asked 2026-07-04: *"can we verify `call`
inductively — using the theorem for the evaluator itself for the call?"*):
**yes, and the proof is already shaped for it.** `exec`'s call equation
(`Prog.lean:222`) runs the callee's body at `fuel` from `fuel+1`:

```lean
match exec P dbase pad stackLo fuel fd.body callee with
```

and `lower_sim_cf` inducts on `fuel` (`CtrlSim.lean:279`), so in the `call`
case the induction hypothesis IS the full simulation theorem at clock `fuel` —
for ANY statement, including the callee's whole body. This is the same move the
`while` case already made (back-edge → fuel IH on the same term), and it
handles **recursive functions for free** (a recursive call is another body
entry at a smaller clock — this is why §3.2 chose fuel over structural
induction, closing policy C5). No new induction principle is needed. What IS
needed: (a) the IH must become *applicable* at a call boundary (§2, C1), and
(b) one genuine invariant repair discovered while writing this plan (§2, C2 —
the dead-hole problem). The rest is prologue/epilogue plumbing.

## 1. Ground truth — exactly what happens at a call (both sides)

### 1.1 IL side (`lean/LowIR/Prog.lean`)

`exec (fuel+1) (.call argc rvc f args rets) s` (line 222):
1. `List.lookup f P.env = some fd'` — else `none`.
2. Arity check `fd'.argc == argc && fd'.rvc == rvc` — else `none`. (The
   `Vector Reg argc` types tie `args`/`params` lengths to the arities — no
   separate length facts needed.)
3. `frameEnter stackLo fd' (pad f) (args.toList.map s.rget) s.mem s.sp`
   (line 143): `none` iff `s.sp.toNat < stackLo.toNat + frameSize' + pad f`
   (so on success the two `BitVec` subtractions below don't wrap and
   `newSp.toNat ≥ stackLo.toNat`). Callee state: fresh zero register file with
   `withParams` (a LAST-WINS left fold of `params.zip argVals`), then
   `frameReg ↦ frameBase` **overriding** any param binding (`if r = frameReg
   then frameBase else withParams r`); `frameBase = sp − frameSize'`;
   `newSp = frameBase − pad f`; caller's memory.
4. `exec fuel fd'.body callee` must give `(s1, .normal)` or `(s1, .ret)`;
   an escaping `.brk`/`.cont` or `none` makes the whole call `none` — so
   under `hexec` only the normal/ret branches are ever live.
5. Result: `((rets.zip retVals).foldl rset {s with mem := s1.mem}, .normal)`
   with `retVals = fd'.rets.toList.map s1.rget` — caller regs + sp
   (structural restore), callee memory, rets copied last-wins.

### 1.2 Machine side (`lean/LowIR/Compile.lean`)

- **Call site** (line 136): `loads ++ [.callf f] ++ stores` —
  `loadSlot args[i] (A i)` for each arg (1 instr each, incl. reg 0 →
  `addi (A i) x0 0`), then `jal RA δ` (`resolveOne` line 277, δ range
  `±2²⁰−2`, `RA := pc+4`), then `storeSlot rets[i] (A i)` (1 instr each,
  **0 for ret reg 0**).
- **Prologue** (line 189): `addi sp sp −totalFrame`; `sd sp ra 0`; park
  params `storeSlot params[i] (A i)` in order (last-wins = the IL fold's
  order; param reg 0 emits nothing; a param equal to `frameReg` is
  overwritten by the frameReg write below — same override order as
  `frameEnter`); `sd sp x0 (slotOff r)` for every
  `r ∈ range(maxRegF+1), r ≠ 0, r ∉ params, r ≠ frameReg` (the IL
  zero-init); if `frameReg ≠ 0`: `addi T0 sp userOff` + `storeSlot frameReg T0`.
  Every slot `1..maxRegF` is written exactly once modulo the last-wins
  overrides — matching `frameEnter`'s register file pointwise.
- **Body**, then 0-byte label `epi`, then **epilogue** (line 203):
  `loadSlot rets[i] (A i)` (rvc instrs), `ld ra sp 0`,
  `addi sp sp totalFrame`, `jalr x0 ra 0`. So
  **`epiPos' = bodyPos + 4·csize(body)`** — `.normal` (fall-through) and
  `.ret` (jump to `epi`) CONVERGE at the epilogue, exactly matching `exec`
  accepting both outcomes.
- **P1 arithmetic**: with `pad f = userOff fd'`, IL
  `newSp = sp − frameSize' − userOff'` = machine `sp − totalFrame'` — sp
  equality at every depth (validated: `CompileTests.p1_chain_userPad`,
  `p1_rec_userPad`).
- **`jalr` semantics** (`RawAsm/Rv64i.lean:189`):
  `pc := (rget rs1 + sext imm) &&& ~~~1` — note the bit-0 clear; we'll need
  return-address evenness (C4, `halign`).

### 1.3 Proof side, current state (`lean/LowIR/ProgSim/`)

- `lower_sim_cf` (`CtrlSim.lean:252`): fuel induction
  `generalizing stmt s s' oc m here brkPos contPos` — **`fd`, `holes`,
  `epiPos` are NOT generalized** (C1).
- `csize`/`emitCF` (`CtrlSim.lean:38/54`) have **no call arm** — both fall to
  the defaults (`(emit s).length` = 0 / `emit s` = `[]`). `emitCF` has no
  function-position context (only `dpos` for data).
- `StInv` (`Defs.lean:373`): memory agreement `∀ a, ¬ MachPriv L holes a →
  s.mem a = m.mem a` — see C2 for why this exact form is FALSE after a call
  returns.
- `MemAccOff` (`StmtSim.lean:752`): `call` falls to the `True` stub — same
  situation `while` was in before `0615725`; it cannot feed the body IH (C6).
- Atoms in hand: `run_load`/`run_store` (T0-based), `run_synth` (already
  generalized to any scratch target WITH a reg-preservation clause,
  `9ec08e5` — the pattern to copy for A-regs), `jump_sim`, `step_jal`
  (any `rd`, so `jal RA` is covered), `StInv_scratch` (any reg ≠ 2 — covers
  RA and all A-regs), `StInv_sp_eq`. **No `step_jalr`** exists anywhere in
  ProgSim.
- Differential anchors: `diff_caller`, `diff_chain3`, `diff_recSum`,
  `p1_chain_userPad` (`CompileTests.lean`) — the oracle states for every
  lemma below.

## 2. Blocking design decisions (settle in this order, before proving)

### C1 — generalize the induction over `fd`, `holes`, `epiPos`

At a call boundary all three change: the callee has its own `FunDef`
(different `maxRegF`/`userOff`), its own epilogue position, empty
`brkPos`/`contPos`, and a holes list with its own hole pushed on top. Add
`fd holes epiPos` to the `generalizing` list at `CtrlSim.lean:279`; Lean
reverts the dependent hypotheses (`hinv hreg hnw hbd hframe hlbl haccess hem`)
into the motive automatically. Purely mechanical; existing cases re-elaborate
with the IH taking three extra arguments (pass the current values).

### C2 — THE invariant repair: dead frame holes break `StInv` (do this first)

**The problem.** During a call the machine dirties the callee's
`[ra][slots]` hole `[sp', sp'+userOff')`. After return that region is DEAD —
it is below the caller's sp, in free stack — and it is NOT in the caller's
`holes` list. But the caller's `StInv` demands `s.mem a = m.mem a` at every
`¬ MachPriv` address, including there. IL memory never wrote it; machine
memory did. **The caller's `StInv` as stated is unrestorable after any
call returns.** (The callee's dead USER frame is fine — both sides wrote it
identically under P1.)

**Rejected fix — grow the holes list through the conclusion**
(`∃ holes' ⊇ holes, StInv … holes' …`): composes through `seq`, but makes
`MemAccOff` unsound as stated — a later statement's accesses are checked
against the ORIGINAL holes, so a load could hit a fresh dead hole where
agreement fails, and `MemAccOff` cannot mention holes it can't see. Fixing
that forces the same existential threading into `MemAccOff` — the complexity
spreads instead of stopping.

**Adopted fix — the free stack below sp is machine-private.** Every dead
hole, forever, lies in `[stackLo, s.sp)` (LIFO + `frameEnter`'s overflow
check keeping `newSp ≥ stackLo`). So:

- `StInv` gains a `stackLo` parameter, and the memory conjunct becomes
  ```
  ∀ a, ¬ MachPriv L holes a →
       ¬ memRange a stackLo (s.sp.toNat − stackLo.toNat) →
       s.mem a = m.mem a
  ```
  This is exactly the coarse observable `prog_sim`/`MachStack` already uses
  at the top level (`Defs.lean:360` anticipated it); the caller's own user
  frame stays INSIDE the agreement domain (it's above sp), so frame
  loads/stores keep working — do NOT be tempted by the coarser "exclude all
  of `[stackLo, sp0)`", which would break own-frame loads.
- `MemAccOff`'s four memory arms strengthen in lockstep: accessed bytes must
  be off `MachPriv` AND off `[stackLo, s.sp)` (each arm already has `s` in
  hand; define `OffPriv L holes stackLo sp a` once and reuse). Real programs
  never access below their own sp (frame-relative or harness buffers), so
  the strengthened hypothesis stays dischargeable at the IL altitude.
- Two small conjuncts join `StInv` in the same surgery (needed by C3's
  disjointness walk): `∀ h ∈ holes, s.sp.toNat ≤ h.1.toNat` (live holes sit
  at-or-above sp — LIFO ordering; trivially preserved within an activation
  since sp is constant, re-established at call/return) and
  `∀ h ∈ holes, h.1.toNat + h.2 ≤ 2 ^ 64` (per-hole no-wrap; today only the
  head hole's no-wrap exists, as the theorem hypothesis `hnw`).

**Retrofit cost**: every existing green case + `SlotFacts`/`MemFacts`
payoff lemmas (`StInv_store_slot`, `StInv_storeWord_user`, `StInv_scratch`,
`StInv_congr`, `StInv_sp_eq`, `run_*`) re-thread two extra conjuncts and one
extra parameter. Wide but mechanical: within an activation sp never moves, so
the new conjuncts are congruence-carried everywhere except the call case
itself. Re-green the whole file set INCLUDING `sub3_body_sim` before touching
any call lemma — this surgery is the Phase-5 analogue of the Phase-4.1
vertical slice.

### C3 — machine-frame preservation must enter the CONCLUSION

The epilogue's `ld ra sp 0` reads the saved return address; the caller's
`StInv` restoration needs the caller's slots intact. Both are
machine-private bytes — `StInv` says NOTHING about them, so the body IH
alone cannot deliver them. Add a conjunct to `lower_sim_cf`'s conclusion
(alongside `StInv` and the pc):

```
FramesPres holes s.sp fd m (stepN k m) :=
  ∀ a, (∃ h ∈ holes, memRange a h.1 h.2) →
       ¬ memRange a (s.sp + 8) (userOff fd − 8) →
       (stepN k m).mem a = m.mem a
```

"hole bytes are preserved except the current activation's own slot window
`[sp+8, sp+userOff)`". Why it self-composes through every case:
- slot stores write `[sp + 8(1+r), +8)`, `r ≥ 1` ⊆ the excluded window;
- user stores are off `MachPriv` ⊇ off all holes (via `MemAccOff`);
- loads/jumps/branches don't write;
- a nested call's machine writes land in the CALLEE's fresh hole and frame —
  disjoint from every hole in `holes` because the callee's whole machine
  frame `[sp − totalFrame', sp)` sits strictly below `sp` while all live
  holes sit at-or-above `sp` (the C2 ordering conjunct; this is where it is
  consumed);
- `seq`/`while` chain it transitively (same window — sp constant).

For the call case it delivers exactly: the callee's body preserves (a) the
callee's own ra slot `[sp', sp'+8)` (in the callee's head hole, OUTSIDE the
callee's slot window which starts at `sp'+8`), and (b) every caller/ancestor
hole byte — slots and saved ra — wholesale (they're in the callee's
`holes'` tail, and the callee's window is disjoint from them).

Retrofit: every case must now also produce this conjunct — mechanical for
non-writing steps (add mem-unchanged clauses to the `step_*`/`run_*`
lemmas), 8-byte disjointness arithmetic for slot stores (already in
`SlotFacts`), `MemAccOff` for user stores. Do it in the SAME pass as C2
(both touch every case; one retrofit, not two).

### C4 — three new flat hypotheses (Phase-2 obligations, like `hdat`/`hdbase`/`hdpos`)

1. **`hpad`** — the P1 instantiation finally enters the statement:
   `∀ f fd', List.lookup f P.env = some fd' → pad f = userOff fd'`.
   Without it the machine's `addi sp sp −totalFrame` and the IL's
   `newSp = sp − frameSize' − pad f` don't meet. (`userPad P.env`
   satisfies it definitionally — `Defs.lean:394`.)
2. **`hfn`** — the function table, tying names to code positions:
   ```
   ∀ f fd', List.lookup f P.env = some fd' → FnEmitted L fnPos f fd'
   ```
   where `FnEmitted` bundles, at `p = fnPos f`:
   `Emitted L p (prologueI fd')`,
   `Emitted L (p + 4·prologueSize fd') (emitCF … [] [] epiPos' bodyPos fd'.body)`
   with `bodyPos = p + 4·prologueSize fd'` and
   `epiPos' = bodyPos + 4·csize fd'.body`,
   `Emitted L epiPos' (epilogueI fd')`, the range facts
   `p < 2²⁰ ∧ epiPos' + 4·epilogueSize fd' < 2²⁰`, `BranchOk fd'.body`, and
   `userOff fd' ≤ 2000` (from `fnOk`'s `totalFrame ≤ 2000`). Everything the
   callee's IH instance needs and the caller can't derive locally lives
   here. `fnPos : Name → Nat` is a new `emitCF` context parameter
   mirroring `dpos` (C5); AsmFacts discharges `hfn` from
   `layout`/`fnTab`/`compileFun` in Phase 2.
3. **`halign`** — `L.codeBase.toNat % 4 = 0` (or `% 2` minimally). The
   epilogue's `jalr` computes `(ra + 0) &&& ~~~1`; the return address
   `codeBase + (callSite + 4·argc + 4)` must have bit 0 clear for the
   land-at lemma. All positions are 4-aligned already (`Emitted`), so
   codeBase alignment is the only missing atom. Trivially true of any real
   `codeBase` (0x80000000).

### C5 — the emit surface: real `call` arms + validation

- `csize` call arm: `argc + 1 + (rets.toList.filter (· ≠ 0)).length`
  (arg loads are ALWAYS 1 instr each, incl. reg 0; ret stores are 0 instrs
  for reg 0 — same `if rd = 0` shape the clen/cref arms already have).
- `emitCF` gains `(fnPos : Name → Nat)` and the arm
  ```
  | here, .call argc rvc f args rets =>
      marshalI args                                   -- argc loads into A i
      ++ [.jal RA (ofInt 21 ((fnPos f : Int) − (here + 4·argc)))]
      ++ retStoresI rets                              -- storeSlot per nonzero ret
  ```
  Signature ripple through `emitCF_length`, `lower_sim_cf`'s statement, and
  every `#guard` — mechanical.
- `prologueI fd`/`epilogueI fd : List Instr` — the RESOLVED prologue/epilogue
  (label-free, so a direct transcription of `Compile.prologue`/`epilogue`
  with `.ins` unwrapped), plus `prologueSize`/`epilogueSize`
  (`epilogueSize = rvc + 3`; `prologueSize = 2 + #{nonzero params} +
  #{zeroed} + (frameReg ≠ 0 ? 2 : 0)` — value-independent, as layout
  requires).
- **Validation before any proof** (§6 discipline): extend `matchesReal` to a
  whole-program `matchesRealProg` that runs the REAL `compileProgT` and
  checks, per function, `prologueI ++ emitCF … ++ epilogueI` against the
  resolved stream at the `fnTab` positions (today's `realResolve` passes
  `fns = []`, so `.callf` can't resolve at all). `#guard` it on `denv`
  (`caller` — args/rets marshalling), `chainEnv` (3-deep nesting), `recSum`
  (recursion), and a `rets`-to-x0 / duplicate-params corner if the library
  lacks one (add a test fn).

### C6 — `MemAccOff` call arm

Mirror the `while` fix (`0615725`) — fuel-structural, quantified over the
dynamic entry:

```
| fuel+1, .call argc rvc f args rets, s =>
    ∀ fd' callee, List.lookup f P.env = some fd' →
      frameEnter stackLo fd' (pad f) (args.toList.map s.rget) s.mem s.sp
        = some callee →
      MemAccOff L ((callee.sp, userOff fd') :: holes) … fuel fd'.body callee
```

The call statement itself touches no IL memory (marshalling is registers;
the rets copy is registers; `frameEnter` keeps the caller's memory), so the
body recursion is the whole arm. Note the EXTENDED holes list — the callee's
accesses must also avoid the caller's hole, which is what makes the caller's
slots survive (C3). The C2 strengthening (off-free-stack) applies inside via
the leaf arms using the callee's own `s.sp`.

## 3. New atoms (all standalone, oracle-checkable before the induction)

| Lemma | Content | Notes |
|---|---|---|
| `step_jalr` | `decode = jalr rd rs1 imm → step m = (m.rset rd (pc+4)).setPc ((rget rs1 + sext imm) &&& ~~~1)` | one-instruction lemma, `StmtSim` style |
| `jalr_lands` | ra = `codeBase + t`, `t` even, imm 0 ⇒ pc' = `codeBase + t` | consumes `halign`; the `&&& ~~~1` no-op |
| `run_loadTo` | `loadSlot r (A i)` → A i holds `s.rget r`, StInv preserved, OTHER A-regs preserved | generalize `run_load` off T0 exactly as `9ec08e5` did `run_synth` |
| `run_storeFrom` | `storeSlot r (A i)` mirrors `rset r (m.rget (A i))` | generalize `run_store`'s source reg |
| `run_marshal` | the argc arg loads: `∀ i < argc, rget (A i) = s.rget args[i]`, StInv preserved, pc `+4·argc` | list induction over `zipIdx`, chaining `run_loadTo`'s preservation clause |
| `run_retstores` | the post-call stores mirror the IL rets fold last-wins | same-order induction; ret reg 0 = 0 instrs vs `rset 0` discard |
| `park_lastwins` | machine sequential `storeSlot params[i] (A i)` = IL `withParams` fold, pointwise on slots | the fold/store agreement lemma the plan flagged in 2026-07-02; duplicates + param-reg-0 + frameReg-override cases here |
| `prologue_sim` | from a call-entry machine state (A-regs = argVals, ra = return addr, StInv for the CALLER): after `prologueSize` steps, `StInv L fd' ((sp', userOff fd') :: holes) stackLo callee m'`, machine ra slot `[sp',+8)` holds the return address, pc at `bodyPos` | consumes `hpad` (sp equality) + `frameEnter`'s success (no-wrap); per-slot case walk: param / frameReg / zeroed |
| `epilogue_sim` | from callee-exit `StInv` + ra-slot fact: `rvc + 3` steps land at return addr, machine sp = caller sp, A-regs = `s1.rget rets'[i]`, caller-hole bytes untouched | uses `step_jalr`/`jalr_lands`; no stores in the epilogue |

De-risk exactly as RESUME-PROGSIM §4 Phase 5 says: prove `prologue_sim` /
`epilogue_sim` standalone and sanity-instantiate on the `diff_caller` /
`diff_chain3` differential states BEFORE the induction case. Optionally
package the whole middle as a standalone `call_sim` taking the body
simulation as an explicit HYPOTHESIS (a "body simulator" parameter), then
instantiate that hypothesis with the fuel IH inside the induction — keeps
the summit lemma testable in isolation.

## 4. The call case, assembled (the six-segment ledger)

In `lower_sim_cf`, `case call argc rvc f args rets`, after `exec_call_*`
unfolders split `hexec` (lookup `some fd'`, arity true, `frameEnter = some
callee`, body result `.normal`/`.ret` — other branches contradict `hexec`):

1. **Marshal** (`4·argc` bytes): `run_marshal` — A-regs = arg values (caller
   StInv slots; arg regs ≤ `maxRegF fd` from `hreg`'s call arm), StInv
   preserved, pc at the `jal`.
2. **`jal RA δ`**: `step_jal` + `jump_lands` — pc = `codeBase + fnPos f`,
   RA = `codeBase + (here + 4·argc + 4)` (the return address), StInv via
   `StInv_scratch` (RA ≠ 2). Range: `here < 2²⁰` from `hbnd`,
   `fnPos f < 2²⁰` from `hfn`.
3. **Prologue**: `prologue_sim` — callee `StInv` at holes
   `(callee.sp, userOff fd') :: holes`, ra slot holds the return address,
   pc = `bodyPos`.
4. **Body — the fuel IH** (the inductive use of the evaluator theorem):
   apply `ih` at `fd := fd'`, `holes := (callee.sp, userOff fd') :: holes`,
   `epiPos := epiPos'`, `brkPos := []`, `contPos := []`, `here := bodyPos`,
   the callee `StInv`, `hexec` = the body run. Landing for BOTH live
   outcomes is `codeBase + epiPos'` (`.normal`: fall-through
   `bodyPos + 4·csize = epiPos'`; `.ret`: `landPos … .ret = epiPos'`) — one
   case split, same continuation. Plus `FramesPres` for the extended holes
   (C3): ra slot + all caller hole bytes intact.
5. **Epilogue**: `epilogue_sim` — machine sp back to `s.sp` (P1: structural
   restore on both sides), A-regs = ret values, pc = return address.
   Intermediate caller `StInv` for `{s with mem := s1.mem}` (regs unchanged):
   sp ✓; slots = pre-call machine bytes (`FramesPres`) = pre-call IL regs ✓;
   `Installed` threaded ✓; memory agreement — for `a ∉ MachPriv holes` and
   `a ≥ s.sp`: `a` is outside the callee hole (below sp) and above
   `callee.sp`, so the callee-exit agreement covers it ✓ (this is where C2
   pays); C2's ordering/no-wrap conjuncts: restore trivially.
6. **Ret-stores** (`4·#{nonzero rets}` bytes): `run_retstores` — the IL fold
   and the machine stores update in lockstep; final pc =
   `codeBase + here + 4·csize(call)` = `landPos … .normal` ✓; outcome is
   `.normal` ✓; `FramesPres` for the CALLER's holes: segments 1–2 write no
   memory, 3–5's writes are in the callee frame (disjoint from caller holes
   by the C2 ordering conjunct), 6 writes the caller's own slot window —
   exactly the exclusion ✓.

### Side-condition propagation to the callee's IH instance

| Hypothesis | Source |
|---|---|
| `hreg` | free: `maxRegS fd'.body ≤ maxRegF fd'` by `maxRegF`'s definition |
| `hnw` | `sp' + userOff' ≤ sp' + totalFrame' = s.sp.toNat ≤ 2⁶⁴` (frameEnter no-wrap + `hpad`) |
| `hbd` | needs the stackLo-based reshape: replace with `(codeBase + blobLen ≤ stackLo ∧ stackLo ≤ sp) ∨ sp + userOff ≤ codeBase`. First disjunct propagates via `frameEnter`'s `newSp ≥ stackLo`; second self-propagates: `sp' + userOff' ≤ s.sp ≤ s.sp + userOff fd ≤ codeBase`. Existing uses derive the old form from either disjunct. **Fold this reshape into the C2 surgery** (same retrofit pass) |
| `haccess` | the C6 `MemAccOff` call arm, instantiated at `fd'`/`callee` |
| `hlbl` | `brkPos = contPos = []` vacuous; `epiPos' < 2²⁰` from `hfn` |
| `hbnd` | `bodyPos + 4·csize fd'.body = epiPos' < 2²⁰` from `hfn` |
| `hbr`, `hframe` | from `hfn` (`BranchOk fd'.body`, `userOff fd' ≤ 2000`) |
| `hem`, `hpc` | `hfn`'s body `Emitted` + segment 3's landing |
| `hinv` | `prologue_sim`'s conclusion |

No `wf` hypothesis is needed anywhere: `exec`'s dynamic checks (lookup,
arity, `frameEnter`) carry everything, and the frameReg-overrides-params
order is IDENTICAL on both sides regardless of well-formedness.

## STATUS (updated 2026-07-04) — W1 + W2 DONE, green + committed

W1, W2a (C2), W2b (C3) landed and green (`lake build LowIRProgSim` clean; the
ONLY `sorry` is the `call` case of `lower_sim_cf`). Commits: `bf83654` (W1),
`d2d5e54` (W2a), `07ab057` (W2b). What the next session inherits — read this
before W4, several details deviate from the pre-implementation sketch below:

- **`fnPos` is a real `emitCF` param** (after `dpos`), threaded through
  `emitCF_length`, `matchesReal`, and all of `lower_sim_cf`. `csize`'s call arm
  is `args.toList.length + 1 + (retStoresI rets.toList).length` (NOT the
  filter form) — keeps `emitCF_length` a one-liner. `marshalI`/`retStoresI`
  (CtrlSim) + `marshalI_length`. `prologueI`/`epilogueI`/`prologueSize`
  (= `.length`)/`epilogueSize` (= `rvc+3`), `matchesRealProg` #guards green.
- **C2 chose a `Layout.stackLo` FIELD, not a threaded parameter** — so all 50
  `StInv L fd holes s m` sites stayed textually unchanged. `OffPriv L holes sp a
  := ¬MachPriv ∧ ¬memRange a L.stackLo (sp−L.stackLo)` (Defs). `StInv` is now an
  **8-conjunct** structure: c4 memory conjunct weakened to `∀ a, OffPriv L holes
  s.sp a → s.mem a = m.mem a`; c7 `∀ h ∈ holes, s.sp.toNat ≤ h.1.toNat`; c8
  `∀ h ∈ holes, h.1.toNat + h.2 ≤ 2^64`. `layoutOf` gained a `stackLo` arg.
  `MemAccOff`'s 4 mem arms use `OffPriv L holes s.sp`. Positional accessors to
  c1–c5 are UNCHANGED (c6 had no positional users); destructures went 6→8.
- **`hbd` was NOT reshaped** (deferred to W7 — its stackLo form is only needed to
  propagate to the callee IH). C4's `hpad`/`hfn`/`halign` NOT added yet.
- **C3 `FramesPres` is a separate 3rd conclusion conjunct** (`∃ k, StInv ∧ pc ∧
  FramesPres holes s.sp fd m (stepN k m)`), NOT woven into StInv — the plan's
  fallback, and it was the right call. `FramesPres`/`_of_mem_eq`/`_trans` in
  Defs; `FramesPres_user_store`/`_storeByte` in MemFacts. Atoms that now emit it:
  `run_store` (4th component), `single_op_sim`/`two_op_sim` (4th), `jump_sim`
  (3rd, + `ret_sim`/`brkB_sim`/`contL_sim` carry it). Every `lower_sim`/`_cf`
  case produces it — so W4+ inherits a stable conclusion.
- **Ready for W4**: the atoms and `prologue_sim`/`epilogue_sim`/call-assembly are
  the remaining work. `step_jalr`/`jalr_lands` (W4) still to write; `A`/`RA`/`SP`
  are opened in CtrlSim; `run_load`/`run_store`/`run_synth` are the generalization
  templates. Do W3 (generalize induction) immediately before W7 (only the call
  case changes `fd`/`holes`/`epiPos`); W4/W5/W6 are standalone and need no
  induction change.

## 5. Work plan (commit-ordered; each step green + committed before the next)

| # | Step | Size | Risk |
|---|---|---|---|
| W1 | ✅ DONE (`bf83654`). C5 defs: `csize`/`emitCF` call arms + `fnPos`, `prologueI`/`epilogueI`/sizes, `matchesRealProg`, `#guard`s on caller/chain/recSum + a corner-case fn. NO proofs | ~200 | low — pure defs, decidably validated |
| W2 | ✅ DONE (`d2d5e54` C2 + `07ab057` C3). C2+C3 surgery: `StInv` (stackLo FIELD, free-stack `OffPriv` domain, ordering + no-wrap conjuncts), `MemAccOff` strengthening, `FramesPres` as a separate ∧ conclusion; re-threaded everything incl. `sub3_body_sim`. `hbd` reshape deferred to W7 | ~500 delta | done — the ∧-at-top FramesPres (not woven into StInv) kept it tractable |
| W3 | C1: add `fd holes epiPos` to `generalizing`; existing cases pass current values to the 3 extra IH args. **Do together with W7** (only the call case needs it) | ~50 delta | low |
| W4 | Atoms: `step_jalr`, `jalr_lands` (+`halign` hyp), `run_loadTo`, `run_storeFrom`, `run_marshal`, `run_retstores`, `park_lastwins` | ~450 | low-medium; copy the `9ec08e5` generalization pattern |
| W5 | `prologue_sim` standalone + oracle instantiation on `diff_caller` state | ~300 | **medium** — the per-slot three-way case walk (param/frameReg/zeroed) with last-wins is the fiddliest lemma of the phase |
| W6 | `epilogue_sim` standalone | ~150 | low |
| W7 | C4 hyps (`hpad`/`hfn`/`halign`) + C6 arm + the call case assembly (§4) | ~300 | medium — pure plumbing if W2–W6 landed as stated |
| W8 | `#print axioms lower_sim_cf` → target `[propext, Quot.sound]` (no `sorryAx` left at statement level); update RESUME-PROGSIM status + [PROGRESS.md](PROGRESS.md); record `hpad`/`hfn`/`halign` as Phase-2 obligations next to `hdat`/`hdbase`/`hdpos` | ~30 | — |

Total ≈ 2000 lines — consistent with RESUME-PROGSIM's Phase-5 estimate.
Axiom discipline as always: split conjunction goals before `omega`
(Classical.choice), one-layer unfolders only (`exec_call_*` exist in
`ExecFacts.lean`), never `simp [exec]` with the IH in context.

## 6. Known adjacent gap (flag, do NOT scope-creep into Phase 5)

`MemAccOff` classifies the whole blob as forbidden — including the DATA
segment. So an IL `lbu` through a `cref` pointer (how programs actually read
their const data) currently has an unsatisfiable side condition, even though
agreement genuinely holds there (`Installed` data half + `installData`).
Nothing in Phase 5 needs it (cref/clen only compute addresses/lengths), but
the Prog-altitude `hex0F_correct` (post-campaign ladder, PROOF-COMPLEXITY §3)
will hit it on its first table lookup. The fix is a read-side carve-out —
`OffPriv ∨ (in the data segment ∧ read-only)` with agreement supplied by the
`Installed` data conjunct — and it touches the same conjuncts as C2, so
whoever does it should re-read the C2 section first. Left OUT of Phase 5
deliberately: the W2 retrofit is already the phase's biggest risk, and
doubling its blast radius to serve a later campaign violates the
vertical-slice discipline that has worked five phases running.

## 7. Cold-start order for the next session

1. Read §1–§2 of this doc; skim `CtrlSim.lean:252-290` (theorem + induction
   header) and the `while` case (the IH-application template).
2. W1 — it's pure definitions and `#guard`s; it cannot go wrong and it
   forces contact with every marshalling corner (reg-0, duplicates).
3. W2 — the surgery. Commit the moment everything re-greens.
4. Then W3…W7 in order, oracle-instantiating each `*_sim` before moving on.
