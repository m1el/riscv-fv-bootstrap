# RESUME-ENTRY — Phase 6: `entry_run_sim`, closing the `prog_sim` summit

> **STATUS: COMPLETE (2026-07-06, commit `2a473d0`).** `entry_run_sim` is
> proven (`Main.lean`) and `#print axioms LowIR.ProgSim.prog_sim = [propext,
> Quot.sound]`. The plan below (E1–E8) was executed as written; kept for the
> record and for the reusable NoHalt-retrofit / segment-assembly recipe. Line
> numbers refer to the pre-close `9376818` state.

Plan written 2026-07-06, at commit `9376818`, when `entry_run_sim`
(`Main.lean:62`, sorry at line 82; all files below are in `lean/LowIR/ProgSim/`
unless said otherwise) became the ONLY remaining `sorry` of the `compile_sim`
campaign. Read with
[RESUME-PROGSIM.md](RESUME-PROGSIM.md) (the campaign handoff) and
[RESUME-CALL.md](RESUME-CALL.md) (Phase 5 — the `call` case of `lower_sim_cf`
is the worked template this plan instantiates at the top level). Line numbers
refer to the `9376818` state.

## 0. Mission and current state

Close `entry_run_sim`. After it, `#print axioms prog_sim` = `[propext,
Quot.sound]` and the campaign's headline theorem — the compiled RV64I blob
computes what the D7/D8 IL says — is done.

Already in hand (all axiom-clean):

- `prog_sim` (Main.lean:92) is PROVEN from `entry_run_sim` +
  `runFuel_eq_stepN` (Main.lean:30, proven).
- `run_inv` (ExecFacts.lean:265) — the IL-side inversion: `run = some s'` ⇒
  lookup + `frameEnter … = some st0` + `exec fd.body st0 = some (s', oc)` +
  `oc ∈ {normal, ret}`. NOTE `s'` IS the body's final state (`run` does not
  remarshal rets, Prog.lean:438).
- `lower_sim_cf` (CtrlSim.lean:1449) — statement-level simulation, every
  construct incl. `call`; `prologue_sim` (CtrlSim.lean:972); `epilogue_sim`
  (CtrlSim.lean:1343).
- The Phase-2 discharge layer: `fn_hfn` (LayoutFacts.lean:1246),
  `stub_emitted` (LayoutFacts.lean:1329), `layoutOf_decomp`, `dbaseOf_dposOf`,
  `dposOf_lt`, `codeLen_lt`, `clen_synthOk`, `compileProgT_dataBound`,
  `userPad_eq`, `layoutOf_stackLo`, and `SimPre` (Defs.lean:448) supplying
  `halign`/`hblob`/`hbd`-left/`hdpos`/`hcode`.
- The worked assembly template: `case call` (CtrlSim.lean:2159) — segs 1–6.
  `entry_run_sim` is that assembly MINUS marshalling (args arrive in `a0..` by
  hypothesis), MINUS ret-stores (`run` doesn't remarshal), with `holes = []`
  and the return address = the halt pad `codeBase + 4`.

The plan has three parts, in dependency order: **§2 statement repairs** (the
current statement is unprovable / under-hypothesized in four places), **§3 the
`hne` retrofit** (the one genuine design decision — per-step pc information
does not exist in any current conclusion), **§4 the segment assembly** (pure
plumbing, sources itemized).

## 1. Ground truth — what happens at the top level

Machine side, from `m0` (`pc = codeBase`, `sp = sp0`, `a0.. = args`,
`Installed`, memory = zeros + data off the blob):

1. **Stub `jal ra, entry`** at `codeBase` (`stub_emitted`): pc ↦ `codeBase +
   fnPosOf L entry`, **`ra := codeBase + 4` = `L.haltPc`** — the "caller" the
   entry function returns to is the halt pad itself.
2. **`entry`'s prologue** (`prologue_sim` at `holes := []`, `sp0`, `ra :=
   codeBase+4`): establishes `StInv` for `frameEnter`'s `st0` at holes
   `[(st0.sp, userOff fd)]`, ra saved in slot 0, pc at `bodyPos = fnPosOf L
   entry + 4·prologueSize fd`.
3. **Body** (`lower_sim_cf` on `fd.body`, `brkPos = contPos = []`, `epiPos =
   bodyPos + 4·csize fd.body`): lands at `epiPos` for both live outcomes
   (`run_inv`'s `oc ∈ {normal, ret}`), `StInv` for `s'`, `FramesPres` (slot 0
   — the saved ra — survives the body).
4. **Epilogue** (`epilogue_sim`): rets → `a0..`, sp restored, `jalr` lands at
   `ra = codeBase + 4 = haltPc`. Conclusion 1 (`pc = haltPc`) and 2 (ret regs)
   drop out directly; no seg-6 analogue.
5. **Halt pad** `jal x0, 0` at `codeBase+4` spins (never executed inside `K`).

Conclusion 4 — `hne : ∀ j < K, (stepN j m0).pc ≠ haltPc` — is what feeds
`runFuel_eq_stepN`, and it is the part NO current lemma supports: every `∃ k`
conclusion in the corpus (`lower_sim_cf`, `prologue_sim`, `epilogue_sim`, all
`run_*` atoms) states endpoint facts only. §3 is the fix.

## 2. Statement repairs (S1–S4) — do FIRST, the current statement is not provable

Each is a hypothesis to add to `entry_run_sim` AND `prog_sim` (they share the
signature; `prog_sim` forwards). Re-green the `prog_sim` assembly after.

### S1 — tie `stackLo` to `L.stackLo`

The statement runs the IL at a free `stackLo` but builds the layout at
`L.stackLo` (`hL : layoutOf P entry L.codeBase L.stackLo = some L`), with no
relation between them. `lower_sim_cf` requires `hstackLo : stackLo =
L.stackLo` (its c4/`OffPriv` domain is stated in `L.stackLo`,
Defs.lean:400) — underivable today. Fix: **drop the free parameter — state
`run`/`SimPre`/`MachStack` at `L.stackLo` throughout** (or, minimally, add
`hslo : stackLo = L.stackLo`). Dropping the parameter is cleaner; `prog_sim`'s
public shape stays sensible because `layoutOf` copies `stackLo` verbatim
(`layoutOf_stackLo`, AsmFacts.lean:185).

### S2 — the footprint hypothesis `haccess` is MISSING

`lower_sim_cf` needs `MemAccOff` (StmtSim.lean:867) for the body — the §3.4
per-program footprint side condition. It is not derivable (an IL program that
stores into the blob genuinely breaks the simulation); it MUST be a
hypothesis. `st0` is internal to the proof (produced by `run_inv`), so state
it quantified, mirroring `MemAccOff`'s own call arm (C6):

```lean
(haccess : ∀ st0, frameEnter L.stackLo fd (userPad P.env entry) args
              (installData dataBase P.data (fun _ => 0)) sp0 = some st0 →
    MemAccOff L [(st0.sp, userOff fd)] P (dbaseOf dataBase P.data)
      (userPad P.env) L.stackLo fuel fd.body st0)
```

with `dataBase := L.codeBase + BitVec.ofNat 64 L.segStart` (abbreviate it in
the statement — it already appears twice). Per-program this is dischargeable
at the IL altitude exactly like the hex0 `storeByte_preserves` shape; for the
oracle programs it is `decide`-able.

### S3 — arity: add `hargc : args.length = fd.argc`

`run` (Prog.lean:438) has NO arity check — `frameEnter` zips
`fd.params.toList` with the raw `args`. `prologue_sim`'s `hlen` demands
`params.length = argVals.length`, and the machine parks ALL `argc` params. If
`args.length < fd.argc` the two last-wins folds genuinely diverge on
**duplicate params** (legal — `wfProgram`, Prog.lean:276, forbids only
frameReg-as-param): IL `parkFold [(p,v)]` vs machine `parkFold [(p,v),(p,0)]`.
So the theorem as stated is FALSE without `hargc`. With it, `argVals := args`
instantiates `prologue_sim` directly and `hargs`'s `args.getD i 0` rewrites to
`args[i]`. (Alternative — pad `argVals` and prove a `parkFold`-pad agreement
lemma under a params-nodup assumption — rejected: `wfProgram` doesn't give
nodup, and every real caller passes exact arity anyway.)

### S4 — `BranchOk` for all functions: add `hbr`

`fn_hfn` takes `hbr : ∀ g gd, List.lookup g P.env = some gd → BranchOk
gd.body` as an input (LayoutFacts.lean:1251) — it is not yet derived from the
compiler guard. Add the same hypothesis to `entry_run_sim`/`prog_sim`
(decidable per program, `BranchOk` is structural — CtrlSim.lean:310).
OPTIONAL later upgrade, out of scope here: derive it from `resolveOne`'s
range checks via `compileFun_resolves` and delete the hypothesis everywhere.

Also fold in while touching the signature: `hlk` and `hL` already imply
`compileProgT P entry = some (L.instrs, L.fnTab, dats)` via `layoutOf_decomp`
— no repair needed, just note the extraction order in §4 seg 0.

## 3. THE design piece: the `hne` retrofit ("NoHalt")

### 3.1 Why a retrofit and not a local argument

`hne` needs `pc ≠ codeBase+4` at EVERY step `j < K`. The alternatives:

- **Freeze argument** (no `hne` at all): if pc hits the halt pad early, the
  pad's `jal x0, 0` self-loop freezes the state, so `stepN K = stepN j` and
  `runFuel` agrees anyway. REJECTED: it needs `decode (fetch32 …) = jal0 0`
  at the *intermediate* state `stepN j m0` — i.e. per-step `Installed` — which
  is a retrofit of exactly the same width, delivering strictly less.
- **Per-step pc conjunct** — ADOPTED. Every `∃ k`-shaped lemma additionally
  concludes its intermediate pcs avoid the halt pad. Mechanically identical in
  shape to the C3 `FramesPres` retrofit (RESUME-CALL §2), which this codebase
  has already done once and priced.

### 3.2 The conjunct and its helpers (new, in `Defs.lean` or `StmtSim.lean`)

```lean
def NoHalt (L : Layout) (k : Nat) (m : State) : Prop :=
  ∀ j, j < k → (stepN j m).pc ≠ L.codeBase + 4
```

Strict `j < k`: the endpoint is excluded (each lemma's exact endpoint pc is a
separate conclusion already; only `entry_run_sim`'s FINAL endpoint is the halt
pad). Two helpers do all the composition:

- `pc_ne_halt : 8 ≤ q → q < 2 ^ 20 → L.codeBase + BitVec.ofNat 64 q ≠
  L.codeBase + 4` — cancel the add (`BitVec` add-left-cancel), then `ofNat q =
  ofNat 4 → q = 4` from `q < 2^20 < 2^64`, contradiction with `8 ≤ q`. Also
  the degenerate `L.codeBase ≠ L.codeBase + 4` for step 0 of the stub
  (`(4 : BitVec 64) ≠ 0`).
- `NoHalt_chain : NoHalt L k m → (stepN k m).pc ≠ L.codeBase + 4 →
  NoHalt L k' (stepN k m) → NoHalt L (k + k') m` — via `stepN_add`; the middle
  premise handles the boundary `j = k` and is one `pc_ne_halt` at the caller
  (every boundary pc is a known `codeBase + ofNat q`).

### 3.3 Position lower bounds: where `8 ≤ q` comes from

All function code sits after the 8-byte stub, so every position a running
program visits is `≥ 8` — but the theorems must SEE that:

- `lower_sim_cf` gains hypothesis **`hhere8 : 8 ≤ here`** (sibling of
  `hhere4`). Self-propagates to every sub-position (`here + 4·…`).
- **`LabelsOk` strengthens** (CtrlSim.lean:303): each `p ∈ brkPos/contPos` and
  `epiPos` gets `8 ≤ p ∧ p < 2^20` (jump landings at labels are intermediate
  pcs of the enclosing statement). Construction sites: `block`/`while` push
  positions derived from `here` (≥ 8 by `hhere8`); the `call` case passes
  `[]`/`[]`/`epiPos'` with `epiPos' ≥ fnPos g ≥ 8` (below).
- **`fn_hfn` gains conjunct 7: `8 ≤ fnPosOf L g`** (equivalently a standalone
  `fnPosOf_ge8`). Proof from the existing decomp: `fnPosOf L g =
  4·preF.flatten.length` (`fnPosOf_tie`) and `preF` starts with the resolved
  stub segment, whose flatten has length 2 (`stub_emitted`'s `hflat`
  machinery) ⇒ `≥ 8`. Thread into `hfn`'s statement in `lower_sim_cf` and the
  call case's IH instance.

### 3.4 Retrofit inventory (each lemma: conclusion gains `NoHalt`, plus
`8 ≤ p` / end-bound hypotheses where the lemma doesn't already have them)

Straight-line atoms prove it by enumerating their per-step pcs (which their
proofs already compute explicitly — `hPCld`-style facts) + `pc_ne_halt`;
compound lemmas chain sub-conclusions with `NoHalt_chain`.

| File | Lemmas |
|---|---|
| StmtSim | `run_load`, `run_store`(wrapper), `run_storeFrom`, `single_op_sim`, `two_op_sim`, `jump_sim`, `ret_sim`, `brkB_sim`, `contL_sim`, **`lower_sim`** |
| CtrlSim | `run_synth`, `run_cref`, `run_zeroFrame`, `run_parkParams`, `run_zeroSlots`, `run_slotStore`, `run_marshalFrom`, `run_retStoresFrom`, **`prologue_sim`**, **`epilogue_sim`**, **`lower_sim_cf`** (every case; the fuel IH carries the clause through `seq`/`while`/`call` for free) |

Notes per class:
- **Jump-shaped atoms** (`jump_sim`, `ret/brkB/contL_sim`, the branch steps
  inside `ife`/`while`): `k = 1`, only intermediate pc is the start (`here`) —
  one `pc_ne_halt`. The LANDING is the endpoint (excluded) or, when interior
  to a bigger case, covered by that case's next segment start.
- **`epilogue_sim`** currently takes no position bound at all — gains
  `8 ≤ q` and `q + 4·(rets.length + 3) < 2^20` (callers have both from
  `fn_hfn`).
- **`prologue_sim`** likewise gains `8 ≤ p` (+ its end bound if absent).
- **`lower_sim_cf` `call` case**: chain seg 1 (marshal) · boundary · seg 2
  (jal, start `here + 4·argc`) · boundary at `fnPos f` (`≥ 8` from the new
  conjunct 7) · segs 3–5 · boundary at return address `here + 4·argc + 4 ≥ 8`
  · seg 6.

Convention gotchas (paid for in W4, re-read before starting): `stepN (1+k) m`
unfolds to `stepN k (stepN 1 m)` not `stepN k (step m)` — carry `h1run`;
`Reg`-typed `≠` is invisible to `omega`; split conjunction goals before
`omega` (Classical.choice); `set_option maxHeartbeats 400000` already set for
the call case.

### 3.5 Fallback if the hypothesis ripple annoys

Atoms may instead conclude the hypothesis-free *trace form* — `∀ j ≤ k, ∃ i ≤
len, (stepN j m).pc = L.codeBase + ofNat (p + 4·i)` — and let the enclosing
`lower_sim_cf` case convert via its own `hhere8`/`hbnd`. Fewer signature
changes, slightly more work per case. Decide at E3 (first atom); do not mix
styles within a file.

## 4. The assembly — `entry_run_sim`, segment ledger

After S1–S4, in `Main.lean`. Setup: `obtain` from `run_inv hrun` (`fd₀ st0 oc
…`); `fd₀ = fd` by `hlk` injectivity, subst. Extract `hc : compileProgT P
entry = some (L.instrs, L.fnTab, dats)` from `hL` (`layoutOf_decomp`). Bind
the bundle `hfn := fn_hfn hL hc (codeLen_lt … hpre.blobFits …) hbr`, and
`hpadf : userPad P.env entry = userOff fd := userPad_eq …`. Unfold `hfe`
exactly as CtrlSim.lean:2211–2239 (the template): overflow-negation `hofN :
L.stackLo.toNat + fd.frameSize + userOff fd ≤ sp0.toNat` (after `rw [hpadf]`),
then `hcsp`/`hcspN`/`hcmem`/`hcrg`/`hfbEq` verbatim (with `s.sp := sp0`,
`s.mem := installData dataBase P.data (fun _ => 0)`).

**Seg 0 — the stub `jal`** (template: seg 2 of the call case, CtrlSim
2185–2209). `stub_emitted hL hc` + `decode_at` at `m0` (`hpc : m0.pc =
codeBase = codeBase + ofNat 0`), `step_jal`, `signExtend_ofInt_21` at `δ =
fnPosOf L entry − 0` (range from `hfn`'s `< 2^20` bound), `jump_lands`.
Facts about `m1 := step m0`: pc = `codeBase + ofNat (fnPosOf L entry)`;
`rget RA = codeBase + 4` (= `ra'`, the halt pad); `rget SP = sp0`; `rget (A i)`
unchanged (`rget_rset_ne`, `10 + i ≠ 1`); `mem = m0.mem`; `Installed` via
`Installed_setPc`/`_congr`.

**Seg 1 — prologue** (`prologue_sim` at `fd`, `holes := []`, `m := m1`,
`sp0`, `ra := codeBase + 4`, `callee := st0`, `argVals := args`, `p := fnPosOf
L entry`). Hypothesis sources:

| Hyp | Source |
|---|---|
| `hpc`/`hem` | seg 0 / `hfn` conjunct 1, `Emitted_append_left` ×2 |
| `hinst`,`hsp0`,`hra`,`hargs` | seg-0 facts; `hargs` via S3's `hargc` (`getD → getElem`) |
| `hlen` | `params.length = argc` (Vector) + `hargc` |
| `hparb`/`hfrb` | structural from `maxRegF` (verbatim template 2255–2261) |
| `hcsp`/`hcrg` | the `hfe` unfolding above |
| `hmemF` | SIMPLER than the call case (no tiling): off the user frame `zeroRange` is identity ⇒ `st0.mem a = installData … a`; `m1.mem = m0.mem`; the statement's `hmem` gives agreement for `¬ MachPriv L []`, and `OffPriv L [(st0.sp,…)] …` implies it (fewer holes) |
| `hcmemZ` | `zeroRange` positive branch (template 2296–2303) |
| `htf`/`hfs8` | `hfn` conjuncts 4–5 |
| `hsp0align` | `hpre.spAligned` |
| `hsp0ge` | `hofN` (`totalFrame = userOff + frameSize ≤ sp0` since `stackLo ≥ 0`) |
| `hseg` | `layoutOf` sets `segStart = pad8 (4·len)`; `pad8_ge` |
| `hblob` | `hpre.blobWrap` |
| `hbdc`/`hbdcF` | LEFT disjunct: `hpre.blobBelowStack` + `L.stackLo ≤ st0.sp` (from `hofN` + `hcspN`) |
| `hholes_ord`/`hholes_nw` | vacuous (`holes = []`) |

Output `mPro := stepN kPro m1`: `StInv L fd [(st0.sp, userOff fd)] st0 mPro`,
pc = `codeBase + ofNat (fnPosOf L entry + 4·prologueSize fd)`, `loadWord
st0.sp = codeBase + 4` (the saved ra), mem preserved off `[st0.sp,
totalFrame)`.

**Seg 2 — body** (`lower_sim_cf` at `fd`, `holes := [(st0.sp, userOff fd)]`,
`epiPos := fnPosOf L entry + 4·prologueSize fd + 4·csize fd.body`, `dpos :=
dposOf L`, `fnPos := fnPosOf L`, `here := bodyPos`, `brkPos = contPos = []`,
`fuel`, `stmt := fd.body`, `s := st0`, `s' := s'`, `oc`, `m := mPro`).
Hypothesis sources — this is the whole Phase-2 harvest:

| Hyp | Source |
|---|---|
| `hexec` | `run_inv`'s body run (dbase = `dbaseOf dataBase P.data`) |
| `hinv`/`hpc` | seg 1 |
| `hem` | `hfn` conjunct 1 middle, `Emitted_append_right ∘ Emitted_append_left` (template 2322–2327 incl. the `prologueSize = length` rfl) |
| `hreg` | `maxRegS body ≤ maxRegF` structural |
| `hnw` | `st0.sp + userOff ≤ sp0 ≤ 2^64` |
| `hbd` | left disjunct: `hpre.blobBelowStack` ∧ `L.stackLo ≤ st0.sp` |
| `haccess` | **S2's hypothesis**, applied to `hfe` |
| `hlbl` | `⟨vacuous, vacuous, epiPos ≥ 8 ∧ < 2^20⟩` from `hfn` conjuncts 2/7 |
| `hbnd`/`hbr`/`hframe` | `hfn` conjuncts 2/3/4 |
| `hhere4` | `hfn` conjunct 6 + `prologueSize·4` |
| `hhere8` (new) | `hfn` conjunct 7 |
| `hseg`/`hblob` | as seg 1 |
| `hdat` | `clen_synthOk (compileProgT_dataBound hc)` |
| `hdbase` | `dbaseOf_dposOf` (dataBase matches `layoutOf`'s segStart by construction) |
| `hdpos` | `dposOf_lt hpre.blobFits` (via `SimPre`) |
| `hpad` | `userPad_eq` |
| `halign` | `hpre.codeAligned` |
| `hstackLo` | rfl after S1 |
| `hfn` | `fn_hfn` bundle |

Landing: `cases` the `run_inv` outcome disjunction — `landPos [] [] epiPos
(bodyPos + 4·csize) oc = epiPos` for both `.normal` (fall-through arithmetic)
and `.ret` (template 2348–2350). Output `mBod`: `StInv … s' mBod`, pc at
`epiPos`, `FramesPres [(st0.sp, userOff fd)] st0.sp fd mPro mBod`, `NoHalt`.

**Seg 3 — epilogue** (`epilogue_sim` at `fd`, `holes`, `mE := mBod`, `s1 :=
s'`, `ra := codeBase + 4`, `q := epiPos`).

| Hyp | Source |
|---|---|
| `hinv`/`hpc` | seg 2 |
| `hem` | `hfn` conjunct 1 tail, `Emitted_append_right` + length arithmetic (template 2357–2365) |
| `hraslot` | seg-1 `loadWord st0.sp = codeBase+4`, preserved through the body: `s'.sp = st0.sp` from StInv c5 (head-hole, template `hs1sp` 2353–2356), then the 8-byte `FramesPres` walk + `State_loadWord_congr8` (template 2371–2387, VERBATIM) |
| `hraeven` | `(codeBase+4).toNat % 2 = 0` from `hpre.codeAligned` + no-wrap (`codeBase + blobLen ≤ 2^64`, `blobLen ≥ 8` — the stub is 2 instrs; a tiny `blobLen_ge8` fact from `hc`, or route via `hpre.blobBelowStack` + `stackLo < 2^64` giving `codeBase.toNat + 4 < 2^64` directly) |
| `hretb`/`hretslot` | structural from `maxRegF` |
| `htf` | `hfn` conjunct 4 (`≤ 2000 < 2^11`) |

Output `mEpi`: pc = `codeBase + 4` = `L.haltPc` (**conclusion 1** ✓), `rget SP
= s'.sp + totalFrame`, `rget (A j) = s'.rget fd.rets.toList[j]` (**conclusion
2** ✓ — `rets.toList.length = fd.rvc` ties `getD` to `getElem`), `mem =
mBod.mem`.

**Seg 4 — the two remaining conclusions.**

- **Memory (conclusion 3)**: for `a` off-blob and off-`MachStack L.stackLo
  sp0`: show `OffPriv L [(st0.sp, userOff fd)] s'.sp a` — the hole
  `[st0.sp, st0.sp + userOff)` and the free stack `[L.stackLo, s'.sp)` both sit
  inside `[L.stackLo, sp0)` (`st0.sp = sp0 − totalFrame ≥ L.stackLo`,
  `st0.sp + userOff ≤ sp0`, `s'.sp = st0.sp`) — then StInv c4 at seg 2 gives
  `s'.mem a = mBod.mem a = mEpi.mem a`. Use `not_memRange` to keep `omega` off
  negated conjunctions.
- **`hne` (conclusion 4)**: `K = 1 + kPro + kBod + kEpi`. `NoHalt_chain` the
  four segments: `j = 0` is `codeBase ≠ codeBase + 4` (trivial BitVec);
  boundaries are `pc_ne_halt` at `q ∈ {fnPosOf entry, bodyPos, epiPos}` — all
  `≥ 8` (conjunct 7) and `< 2^20` (conjunct 2).

Nothing else: no seg-6 analogue (conclusion 2 already matches `s'` because
`run` doesn't remarshal — `run_inv`'s design note).

## 5. Work plan (commit-ordered; each step green before the next)

| # | Step | Size | Risk |
|---|---|---|---|
| E1 | S1–S4 statement repairs in `Main.lean` (both theorems); re-green the `prog_sim` assembly | ~60 delta | low |
| E2 | Statement sanity check (§6 discipline): a concrete `example` instantiating the repaired hypotheses on a differential-battery program (`sub3`/`caller`) at `codeBase 0x80000000` — `SimPre` fields, `hargc`, `hbr`, `haccess` all `decide`/`native_decide`-checkable. Nothing constructs `SimPre` today; this is the cheap mis-statement catcher | ~80 | low, high value |
| E3 | `NoHalt` def + `pc_ne_halt` + `NoHalt_chain`; `LabelsOk` ≥8 strengthening; `fn_hfn` conjunct 7 (`8 ≤ fnPosOf`) + discharge; `lower_sim_cf` gains `hhere8` (hypothesis only) | ~150 | low |
| E4 | Retrofit StmtSim atoms + `lower_sim` (10 lemmas, §3.4 list) | ~200 delta | low-med, mechanical |
| E5 | Retrofit CtrlSim atoms + `prologue_sim`/`epilogue_sim` (incl. their new position-bound hyps; callers updated) | ~200 delta | low-med |
| E6 | Retrofit `lower_sim_cf` — conclusion conjunct, all cases; `call` chains six segments + two boundary `pc_ne_halt`s | ~250 delta | MEDIUM — the bulk; commit per case group |
| E7 | `entry_run_sim` assembly, segs 0–4 (§4); `#print axioms prog_sim` = `[propext, Quot.sound]` | ~400 | medium |
| E8 | Docs: PROGRESS entry; flip RESUME-PROGSIM/-CALL/-ENTRY status lines; update memory | ~30 | — |

Total ≈ 1300 lines/delta. E3→E6 must precede E7 (the segments consume the
retrofitted conclusions). E4/E5 can interleave with E6 per-case if preferred,
but keep each commit green (`lake build LowIRProgSim`).

## 6. Discipline (inherited — every item below was paid for once already)

- One-layer unfolders only; NEVER `simp [exec]` with an IH in context (OOM).
- Split conjunction/iff goals before `omega`; `by_cases` on instance-less
  props via `memRange_or_not`; negated `memRange` via `not_memRange`
  (Classical.choice hygiene — target `[propext, Quot.sound]`).
- `Reg`-typed (in)equalities are invisible to `omega` — re-ascribe to `Nat`.
- `stepN (1+k) m = stepN k (stepN 1 m)`, not `stepN k (step m)` — carry
  `h1run : stepN 1 m = step m := rfl`.
- `zipIdx`-instantiated length atoms: `generalize` before `omega`.
- `~~~`/`BitVec.toNat_not`/`getLsbD_not`/`testBit_two_pow_sub_one` are
  Classical-tainted; `bv_decide` unavailable, `bv_omega` fine (linear only).
- Check files with `lake env lean` during work; `lake build` skips nothing
  here (all ProgSim roots are in `defaultTargets`) but is slower.
- Oracle-instantiate every repaired statement before proving into it (E2).

## 7. Cold-start order for the next session

1. Read §2–§4 here; skim `Main.lean` (the statement + the deferred-proof
   docstring), `CtrlSim.lean:2159–2450` (the call case — the template §4
   cites by line), and RESUME-CALL §4/§6 for the segment idiom.
2. E1 + E2 — repairs are small and E2 forces contact with every hypothesis.
3. E3 — the design commit; everything after is mechanical against it.
4. E4–E6 in order, committing per green milestone.
5. E7, then the axiom check, then E8.

Post-campaign (NOT this plan's scope — PROOF-COMPLEXITY §3 ladder): the
transport demo (`strlenF_correct` ∘ `prog_sim`), the Prog frame theorem, the
`MemAccOff` read-side data-segment carve-out (RESUME-CALL §6 flags it; the
Prog-altitude hex0 will need it), the owed `no-read-uninit` theorem, and the
optional S4 upgrade (derive `BranchOk` from the compile guard).
