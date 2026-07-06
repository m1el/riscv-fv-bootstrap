# RESUME-CALL — Phase 5: the `call` case of `lower_sim_cf`

> **✅ COMPLETE (2026-07-05); campaign since fully closed.** The `call` case is
> closed — `lower_sim_cf` has **no statement-level `sorry`** and is
> **axiom-clean**: `#print axioms lower_sim_cf = [propext, Quot.sound]`. All of
> W1–W8 done (see §5). The rest of the `compile_sim` campaign is now also
> done: Phases 1/2 (encode/decode + AsmFacts layout hypotheses) and Phase 6
> (`entry_run_sim`) landed at commit `2a473d0`, so `#print axioms
> LowIR.ProgSim.prog_sim = [propext, Quot.sound]` (see
> [../RESUME-PROGSIM.md](../RESUME-PROGSIM.md) and
> [RESUME-ENTRY.md](RESUME-ENTRY.md)). This doc is an archived design record;
> the sections below describe the Phase-5 plan as executed.

Plan written 2026-07-04, when `call` became the ONLY remaining statement-level
`sorry` (`CtrlSim.lean:886`, in `lean/LowIR/ProgSim/`). Read with
[RESUME-PROGSIM.md](../RESUME-PROGSIM.md) (the campaign handoff — §2 P1, §4
Phase 5 sketch, §6 discipline); this doc supersedes that Phase-5 sketch with a
worked design. Everything below is grounded in the code as of commit `5a88ef2`;
line numbers refer to that state.

## ★ ZERO-INIT DECISION (2026-07-05) — resolves the seg-3 `hmemF` blocker

**The blocker (found while assembling seg 3).** `prologue_sim`'s `hmemF`
requires IL↔machine memory agreement over the callee's `OffPriv` domain, which
INCLUDES the callee's user frame `[s.sp−frameSize, s.sp)`. The committed C2
design (`OffPriv` = off-holes ∧ off free-stack-below-sp, `Defs.lean:377`)
CANNOT supply it, and it is not merely unproven — it is **false**. Minimal
counterexample: `main` calls `foo()` (tiny frame) then `bar()` (64-byte
buffer). `foo`'s prologue writes `foo`'s return address into `[s.sp−16, s.sp)`
on the MACHINE; IL's `frameEnter` writes nothing there. After `foo` returns,
that region is a dead slot-hole holding `foo`'s RA (machine) vs `0` (IL). When
`bar` is entered, `bar`'s user frame `[s.sp−64, s.sp)` CONTAINS `[s.sp−16,
s.sp)`, and `bar`'s prologue zeroes only its slots — so `foo`'s stale RA
survives. `hmemF` demands `machine = IL` there. `foo`'s RA ≠ 0. **False.**

The disagreement is stale slot-bytes from a returned sibling landing inside a
later, larger sibling's frame. It exists whether or not `bar` reads it — so
"functions never read uninit" (a semantic stance we DO adopt) does not make
the two memories equal; it only makes the divergence unobserved. To make c4 a
TRUE proposition on the frame there are exactly two moves: (a) make the bytes
equal — **zero-init**; or (b) exclude them from c4 until written —
write-tracked agreement (a W2-scale core-invariant retrofit + a permanent
per-program obligation). We chose (a): cheaper (~300 mechanical lines vs
~500–700 invariant surgery), lower risk, and it leaves the plain-equality
`StInv` that made W2–W6 tractable UNTOUCHED.

Exit stack state is NOT observed (`prog_sim` agrees only off `[stackLo, sp0)`,
`Defs.lean:466`; the caller's restored c4 excludes `[stackLo, s.sp)`), so no
dead-hole *history* tracking (the rejected "ghost hole-list / CallChain"
option) is needed — that was over-engineering for an unobserved region.

**What zero-init is:** IL `frameEnter` zeroes `[frameBase, frameBase+frameSize)`
in `callee.mem`; the machine prologue gains a zero-frame segment (`sd SP x0` at
offsets `[userOff, totalFrame)`). Then at the callee body both sides read `0`
for any not-yet-written frame byte, agreement holds by construction, and
`prologue_sim`'s `hmemF` weakens to the caller-c4 form (agreement off the whole
callee frame `[callee.sp, s.sp)`, i.e. only `≥ s.sp` — directly the caller's
c4). `pad = fun _ => 0` still reproduces pre-P1 behavior; the differential
oracles are re-validated.

**⚠ STILL OWED — a real `no-read-uninit` proof (deferred, tracked).** Zero-init
DISCHARGES the correctness concern by construction (uninit reads are defined as
`0` on both sides), so it is not a soundness gap. But "functions never read
uninitialized frame memory" remains a genuine memory-safety property we want as
an EXPLICIT theorem/well-formedness obligation, per-program (hex0/hex1/…),
sitting alongside the §3.4 store-footprint machinery in RESUME-PROGSIM (the
`execT` instrumented semantics extended to READS: a run's read-footprint ⊆ its
write-footprint-so-far on the frame). It is the interesting memory-safety
statement anyway. **Not blocking Phase 5; owed as a follow-up.** See
PROOF-COMPLEXITY §3 ladder — slot it there when the borrow/`Wf` layer lands.

**STATUS (2026-07-05) — zero-init IMPLEMENTED + green (commits `ec60b1a`, `53948c9`).**
IL `frameEnter` zeroes the frame (`zeroRange`); `Compile.prologue` emits the
zero-frame segment; `prologueI = prologuePreI ++ frameZeroI`. New sorry-free
atoms: `storeWord_zero_mem_inside` (WordMem), `run_zeroFrame` (CtrlSim).
`prologue_sim` reworked — its interface CHANGED, so seg-3 (below) must adapt:
- `hmemF` WEAKENED to `∀ a, OffPriv … → ¬ memRange a (callee.sp + userOff) frameSize
  → callee.mem a = m.mem a` (agreement OFF the user frame only). Discharge it from
  the caller's c4: off the frame ⇒ `a ≥ s.sp` region ⇒ caller `OffPriv` (needs
  `callee.mem = zeroRange s.mem …` so `callee.mem a = s.mem a` off the frame).
- NEW `hcmemZ : ∀ a, memRange a (callee.sp + userOff) frameSize → callee.mem a = 0`
  — the frame-is-zero fact; derive from `hfe` (`frameEnter`'s `zeroRange`, unfold
  `zeroRange` + the `memRange`↔`frameBase` arithmetic; `frameBase = callee.sp +
  userOff` under P1).
- NEW `hbdcF : … ∨ callee.sp + totalFrame fd ≤ codeBase` (whole-frame off-blob, for
  the frame stores) — from the caller's `hbd` disjunct-2 (`s.sp = callee.sp +
  totalFrame ≤ codeBase`) or disjunct-1 (`codeBase+blob ≤ stackLo ≤ callee.sp`).
- 4th conclusion now preserves off `[callee.sp, totalFrame)` (was `userOff`).
Everything else in the §6 seg-3 recipe stands. **Segs 3–6 remain** (the lone
`sorry`, `CtrlSim.lean` `case call`).

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
- **W4a DONE** (`e0161c3`): `step_jalr` (one-instr lemma, StmtSim) + `run_storeFrom`
  (generalizes `run_store`'s source reg T0→any scratch; `run_store` is now a thin
  T0 wrapper, its 4 callers unchanged). `jalr_lands` (the `&&&~~~1`-is-a-no-op fact
  under alignment) deferred to W6.
- **W4b DONE** (`d7e0e69`): `run_marshalFrom` (CtrlSim, before `lower_sim_cf`) —
  runs `marshalI`'s arg loads by induction on the reg list, A-base generalized;
  each `A (base+j)` ends `= s.rget args[j]`, StInv+mem preserved, regs outside the
  A-window untouched. A-regs (≥10) don't intersect the StInv-constrained x2/slots,
  so loading them preserves StInv.
- **⚠ KEY GOTCHA (cost real time in W4b — read before W4c/W5)**: `Reg := Nat` is an
  `abbrev`, but a **`Reg`-typed (in)equality is invisible to `omega`** — it silently
  drops the goal/hyp as non-arithmetic and reports a spurious counterexample from
  unrelated Nat context hyps. `A i ≠ 2` worked only because `run_load`'s param is
  `t : Nat` (forcing `@Ne Nat`); `A base ≠ A (base+1+j')` is `@Ne Reg` and omega
  ignores it. Fixes that work: `rw [hAb]` to put a literal `10+base : Nat` in the
  goal, or `intro`-the-negation then re-ascribe `have : (10+base : Nat) = … := h;
  omega`. Also: `stepN (1+k) m` unfolds to `stepN k (stepN 1 m)` NOT `stepN k
  (step m)` — carry `h1run : stepN 1 m = step m := rfl` in every rw list.
- **W4c DONE** (`177504e`): `run_storeFrom` gained the reg-preservation conjunct
  `∀ t, (stepN ks m2).rget t = m2.rget t` (4th component; store touches mem+pc only,
  rd=0 is 0 steps) — the `run_store` T0-wrapper projects it away so its 4 callers are
  UNCHANGED. `run_retStoresFrom` (CtrlSim, after `run_marshalFrom`) inducts on
  `(rets, vs)` pairwise: each store is a `run_storeFrom` whose reg-preservation keeps
  the yet-unstored A-values live; result mirrors the IL last-wins fold
  `(rets.zip vs).foldl rset s` exactly (rd=0 ret = 0 instrs vs an invisible `rset 0`,
  which is defeq `s` since `St.rset` guards `if i=0`). FramesPres chains via
  `FramesPres_trans` over the rset-invariant sp (`(s.rset r v).sp = s.sp` by
  `simp [St.rset]`, split on `r=0`). Value hyp bounds on `vs.length` (not
  `rets.length`) to keep `vs[i]` elaboration happy; `rets.length = vs.length` ties them.
  `park_lastwins` folded into W5 (prologue) — it needs the fresh-regfile +
  frameReg-override context, not the return-store context.
- **W4d DONE** (`0045c3c`): `jalr_lands` — `jalr x0 rs1 0` with even `rs1` lands at
  `rs1`'s value. ⚠ **KEY AXIOM GOTCHA (cost real time — read before any BitVec bit-op
  work)**: `BitVec.getLsbD_not` AND `BitVec.toNat_not` AND `Nat.testBit_two_pow_sub_one`
  are ALL **`Classical.choice`-tainted** in this Mathlib-free stdlib — touching `~~~`
  through them contaminates the axiom set (target is `[propext, Quot.sound]`). Also
  `bv_decide` is UNAVAILABLE (needs `Std.Tactic.BVDecide`); `bv_omega` IS available and
  clean but only does linear arith, not `&&&`. The clean recipe used in
  `word_and_not_one` (the `x &&& ~~~1 = x` no-op): keep `~~~1` as the concrete literal
  `BitVec.ofNat 64 (2^64−2)` via **`rfl`** (axiom-free), bit-blast through the CLEAN
  `getLsbD_ofNat`+`getLsbD_and`, and replace `testBit_two_pow_sub_one` with a hand
  induction (`testBit_pow_two_sub_one`, only `testBit_zero`/`testBit_succ`/`omega`).
  `getLsbD0_of_even` bridges `toNat % 2 = 0 → getLsbD 0 = false`. `halign` (codeBase
  alignment feeding the evenness) still a W7 flat hypothesis.
- **W5, W6, W3, C6, C4, exec_call_inv, and call-assembly segs 1–2 all DONE and
  committed** (`a71e29c` W5, `d1ee7dd` W6, `58583fd` exec_call_inv, `fb530e5` W3,
  `223c885` C6, `f538cbd` C4, `caff546` segs 1–2). The lone `sorry` is now
  mid-call-assembly (after seg 2). **Next: segs 3–6 — see §6.** The blocker is
  seg-3/seg-5 memory agreement (the C2 payoff): `prologue_sim`'s `hmemF` needs
  IL↔machine agreement on the user frame `[s.sp−frameSize, s.sp)`, which is inside
  the free stack that StInv c4 excludes. **Study RESUME-PROGSIM §2's memory-agreement
  threading before writing seg 3.** Everything else in segs 3–6 is plumbing with
  sources itemised in §6.
- **W5 GOTCHA (cost real time):** a ∀-quantified lemma's `(l.zipIdx base)`
  instantiated at `base:=0` is a DIFFERENT omega-atom than a literal `l.zipIdx`
  in the same goal — rfl/defeq-equal, but `omega` hashes them apart and splits
  the equation (`i - n ≥ 1`). Fix: `generalize` both length atoms to fresh vars
  before `omega` (see the `prologue_sim` frameReg=0 pc reconciliation).

## 5. Work plan (commit-ordered; each step green + committed before the next)

| # | Step | Size | Risk |
|---|---|---|---|
| W1 | ✅ DONE (`bf83654`). C5 defs: `csize`/`emitCF` call arms + `fnPos`, `prologueI`/`epilogueI`/sizes, `matchesRealProg`, `#guard`s on caller/chain/recSum + a corner-case fn. NO proofs | ~200 | low — pure defs, decidably validated |
| W2 | ✅ DONE (`d2d5e54` C2 + `07ab057` C3). C2+C3 surgery: `StInv` (stackLo FIELD, free-stack `OffPriv` domain, ordering + no-wrap conjuncts), `MemAccOff` strengthening, `FramesPres` as a separate ∧ conclusion; re-threaded everything incl. `sub3_body_sim`. `hbd` reshape deferred to W7 | ~500 delta | done — the ∧-at-top FramesPres (not woven into StInv) kept it tractable |
| W3 | ✅ COMPLETE (`fb530e5`). Added `fd holes epiPos` to `generalizing`; fd/holes/epiPos are inferred at every existing ih-call from hinv/hem, so the only ripple was `hframe` (reverted, appended to all 11 ih-calls) | ~50 delta | done |
| W4 | ✅ COMPLETE. Atoms: `step_jalr`+`run_storeFrom` (W4a `e0161c3`), `run_marshalFrom` (W4b `d7e0e69`), `run_retStoresFrom`+`run_storeFrom` reg-preservation (W4c `177504e`), `jalr_lands`+`word_and_not_one`+`testBit_pow_two_sub_one`+`getLsbD0_of_even` (W4d `0045c3c`). `park_lastwins` → W5; `halign` → W7. `run_loadTo` unneeded (`run_load` already generic over target `t`) | ~450 | done. **Reg-typed ≠ is invisible to omega**; **`~~~`/`not` lemmas are Classical-tainted** — see STATUS |
| W5 | ✅ COMPLETE (`a71e29c`). `prologue_sim` standalone: G0 (sp drop + ra save) → G1 param park (`run_parkParams`/`parkFold`) → G2 zero-init (`run_zeroSlots`) → G3 frameReg (`run_slotStore`). Callee-frame mem obligation carried as entry hyp `hmemF` (W7 discharges). Axiom-clean `[propext, Quot.sound]`. `zipIdx`-atom omega gotcha → `generalize` | ~300 | done — the three-way per-slot walk landed via the segment-runner atoms + `parkFold_mem_indep`/`parkFold_not_mem` |
| W6 | ✅ COMPLETE (`d1ee7dd`). `epilogue_sim` standalone: G1 ret-marshalling (`run_marshalFrom`) → G2 `ld ra` (slot-0 restore, hyp `hraslot`) → G3 `addi sp` (P1 dealloc) → G4 `jalr` (`jalr_lands`, `hraeven`). NO stores ⇒ mem untouched. Axiom-clean `[propext, Quot.sound]` | ~150 | done — the fixed ld/addi/jalr decode_at pc-side closes by rw-rfl (4·1,4·2 reduce) |
| W7 | ✅ **COMPLETE (2026-07-05).** `exec_call_inv` (`58583fd`), C6 MemAccOff call arm (`223c885`), C4 hyps (`f538cbd`), segs 1–2 (`caff546`), **seg 3 prologue** (`0bb8008`), **segs 4–5 body-IH+epilogue** (`c45fe67`), **seg 6 + assembly** (this session). The zero-init `hmemF` blocker cleared: off-frame agreement from caller c4 + callee-hole/free-stack union, all in `L.stackLo`. **No statement-level `sorry` in `lower_sim_cf`.** Added `hstackLo : stackLo = L.stackLo` (needed only for c4). New atoms: `State_loadWord_congr8`/`loadWord_congr_range` (MemFacts), `not_memRange`/`memRange_or_not` (Defs). `set_option maxHeartbeats 400000` for the call case's large defeqs | ~600 | done — segs 3/5 C2 payoff landed as planned |
| W8 | ✅ **DONE.** `#print axioms lower_sim_cf` = `[propext, Quot.sound]` (no `sorryAx`, no `Classical.choice`). Cleaning to target also fixed **pre-existing** Classical taint from the zero-init rework: `storeWord_zero_mem_inside` (`simp`→`simp only`+`rfl`), `run_zeroFrame` (negated-conjunction `omega` + base-case `simpa`), `prologue_sim` (`by_cases` on the instance-less `memRange` → `memRange_or_not`). Flat obligations now on the statement: `hpad`/`hfn`/`halign`/`hstackLo` (Phase-2 discharges alongside `hdat`/`hdbase`/`hdpos`) | ~200 | done |

Total ≈ 2000 lines — consistent with RESUME-PROGSIM's Phase-5 estimate.
Axiom discipline as always: split conjunction goals before `omega`
(Classical.choice), one-layer unfolders only (`exec_call_*` exist in
`ExecFacts.lean`), never `simp [exec]` with the IH in context.

## 6. W7 assembly — remaining segments 3–6 (handoff, 2026-07-04)

The call case in `lower_sim_cf` (CtrlSim.lean, `case call argc rvc f args rets`)
currently ends at a `sorry` after segment 2. State names in scope there:
`gd` (callee FunDef), `callee` (frameEnter entry St), `s1` (body result), `ocb`
(`.normal`/`.ret`), `hlk`/`harity`/`hfe`/`hbody`/`hs'`; `hfnEm`/`hfnBnd`/`hfnBr`/
`hfnTF`/`hfnFS8` (the `hfn f gd hlk` bundle); `hpadf : pad f = userOff gd`;
`hbndArgc : here+4·argc < 2^20`; and the seg-2 outputs `hJalInv` (caller StInv at
`m_jal := step (stepN kMar m)`), `hJalPc` (pc = codeBase+fnPos f), `hJalRA` (RA =
codeBase+(here+4·argc)+4 = the return addr `ra'`), `hJalMem` (= m.mem),
`hMarVal` (A i = s.rget args[i]).

**Seg 3 — prologue** (`prologue_sim` at `fd:=gd`, `holes:=holes`, `m:=m_jal`,
`sp0:=s.sp`, `ra:=ra'`, `callee:=callee`, `argVals:=args.toList.map s.rget`,
`p:=fnPos f`). Extract `callee`'s fields from `hfe`: `rw [hpadf] at hfe;
simp only [frameEnter] at hfe; split at hfe` — overflow branch is `none=some`
(absurd); else `rw [Option.some.injEq] at hfe` gives `{regs,mem:=s.mem,
sp:=(s.sp-ofNat frameSize)-ofNat(userOff gd)} = callee`. From it derive:
`hcsp : callee.sp = s.sp - ofNat(totalFrame gd)` (`rw [←hfe]; simp only
[totalFrame]; bv_omega`); `hcrg` (the `if frameReg … else parkFold …` — `rw
[St.rget, if_neg, ←hfe]` then `rfl`, `parkFold` IS the `withParams` foldl);
`hcmem : callee.mem = s.mem`; and `hbudget : stackLo.toNat+frameSize+userOff gd
≤ s.sp.toNat` (from the `¬(s.sp.toNat < …)` split hyp) — gives `hsp0ge` and
`stackLo ≤ callee.sp` for the hbd propagation. `hem` from `hfnEm` via two
`Emitted_append_left`. `hargs` = `hMarVal` + jal preserves A-regs + `argVals[i]
= s.rget args.toList[i]` (`List.getElem_map`). `hlen`: `gd.params.toList.length
= gd.argc = argc = argVals.length` (Vector, `hgargc`). `hparb`/`hfrb` structural
from `maxRegF gd` (mem_le_foldl_max / Nat.le_max chain). `htf` = `hfnTF`, `hfs8`
= `hfnFS8`. `hsp0align`: caller StInv c6 gives `s.sp.toNat % 8 = 0`.

⚠ **`hmemF` IS THE BLOCKER (the C2 "where it pays" step).** `prologue_sim`'s
`hmemF : ∀ a, OffPriv L ((callee.sp,userOff gd)::holes) callee.sp a →
callee.mem a = m_jal.mem a`. With `callee.mem = s.mem` and `m_jal.mem = m.mem`,
this reduces to `s.mem a = m.mem a` on `OffPriv_callee a`. The caller StInv c4
gives that only on `OffPriv_caller a`, and **OffPriv_callee ⇏ OffPriv_caller**:
the user frame `[s.sp−frameSize, s.sp)` (= `[callee.sp+userOff, s.sp)`, the
frameReg-relative locals, IL-visible so NOT a hole) satisfies OffPriv_callee
(≥ callee.sp, not in the `(callee.sp,userOff gd)` hole) but is inside
`[stackLo, s.sp)` so is EXCLUDED by OffPriv_caller's free-stack conjunct
(`¬memRange a stackLo (s.sp−stackLo)`). So `hmemF` on the user frame needs
`s.mem = m.mem` on a region the caller's invariant says nothing about.
Resolution options to investigate (RESUME-PROGSIM §2 is the source of truth):
(a) the free stack `[stackLo, sp)` agrees IL↔machine at entry because neither
side has written it since `installData` (both start equal) — but StInv c4
deliberately excludes it precisely because nested calls DO write it, so this
needs an *additional* threaded invariant (free-stack agreement above the
current deepest write) or a strengthening of what `lower_sim_cf` carries;
(b) reconsider whether prologue_sim's pushed hole should cover more; (c) a new
flat hypothesis. **Do not guess — study the C2 memory-agreement threading
first.** The same subtlety recurs in seg 5 (RESUME-CALL §4 step 5, "this is
where C2 pays").

**Seg 4 — body IH** (`ih` at `fd:=gd`, `holes:=(callee.sp,userOff gd)::holes`,
`epiPos:=epiPos':=fnPos f+4·prologueSize gd+4·csize gd.body`, `stmt:=gd.body`,
`s:=callee`, `s':=s1`, `oc:=ocb`, `m:=m_pro`, `here:=bodyPos:=fnPos f+
4·prologueSize gd`, `brkPos:=contPos:=[]`). `hexec`=`hbody`. `hinv` from seg 3.
`hem`: `hfnEm` middle via `Emitted_append_left ∘ Emitted_append_right`. `hbd`
(reshaped): disjunct-1 `codeBase+blob ≤ stackLo ∧ stackLo ≤ callee.sp` (from
caller hbd disjunct-1 + `hbudget`); disjunct-2 self-propagates. `haccess`: unfold
the caller's `haccess` (C6 arm) at `hlk`/`hfe` → the callee body's MemAccOff.
`hlbl`=`⟨nil,nil,epiPos'<2^20⟩`, `hbnd`=`epiPos'<2^20`, `hbr`=`hfnBr`,
`hframe`=`userOff gd ≤ totalFrame gd ≤ 2000`, `hhere4`: `bodyPos%4=0` (needs
`prologueSize`, `fnPos f % 4`… — may need `fnPos f % 4 = 0`, consider adding to
`hfn`/`halign`). Landing: `landPos [] [] epiPos' (bodyPos+4·csize gd.body) ocb`
= `epiPos'` for BOTH `.normal` (fall-through = epiPos') and `.ret` (= epiPos') —
one `cases ocb`, same continuation.

**Seg 5 — epilogue** (`epilogue_sim` at `fd:=gd`, `holes:=(callee.sp,userOff
gd)::holes`, `s1:=s1`, `ra:=ra'`, `q:=epiPos'`, `m:=m_body`). `hinv` = seg-4
StInv. `hem`: `hfnEm` tail via `Emitted_append_right`. `hraslot`: the saved ra is
in slot 0 — prologue_sim's `loadWord callee.sp = ra'` PRESERVED through the body
by seg-4 `FramesPres` (slot 0 ⊂ `[sp,sp+8)`); needs `s1.sp = callee.sp` (IL sp is
call-invariant within a body — a StInv-sp lemma). `hraeven`: `ra'.toNat%2=0` from
`halign` (codeBase%4=0) + `here%4=0` (hhere4) + `4·argc+4` even. `hretb`/`hretslot`
structural. `htf`: `totalFrame gd < 2^11` from `hfnTF ≤ 2000`. Output: pc=ra',
sp=`s1.sp+totalFrame gd`=caller `s.sp` (P1), A j = s1.rget gd.rets[j] = retVals[j],
mem = m_body.mem. Same OffPriv-caller reconciliation as seg 3 for the final StInv.

**Seg 6 — ret-stores** (`run_retStoresFrom` at `fd:=fd` (CALLER), `holes:=holes`,
`rets:=rets.toList`, `vs:=retVals`, `base:=0`, `q:=here+4·argc+4`, `s:={s with
mem:=s1.mem}`, `m:=m_epi`). `StInv` for `{s with mem:=s1.mem}`: sp ✓ (caller sp
restored), slots ✓ (FramesPres = pre-call machine bytes = pre-call IL regs),
Installed ✓, memory-agreement = the seg-5 reconciliation. `hem`: `hem` tail
(`retStoresI`) via `Emitted_append_right`. A-reg values from seg 5. Result IL
state = `(rets.zip retVals).foldl rset {s with mem:=s1.mem}` = `s'` (`hs'`, subst).
Final pc = `here+4·(argc+1+retStoresLen)` = `here+4·csize call` = `landPos … .normal`.
FramesPres for the CALLER holes: segs 1–2 no writes, 3–5 write only in the callee
frame (disjoint from caller holes by StInv c7 ordering), 6 writes the caller's own
ret slots.

Total k = `kMar + 1 + kPro + kBod + kEpi + kRet`.

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
