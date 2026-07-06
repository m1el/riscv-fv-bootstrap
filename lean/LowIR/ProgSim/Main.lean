/-
  LowIR.ProgSim.Main — Phase 6, the `prog_sim` summit.

  Assembles the whole campaign: the compiled RV64I blob computes what the D7/D8
  IL says `entry(args)` computes. The proof decomposes as

    prog_sim  =  entry_run_sim  ∘  runFuel_eq_stepN

  where `entry_run_sim` is the machine run in plain-iteration (`stepN`) form —
  stub `jal` → `entry`'s prologue (`prologue_sim`) → body (`lower_sim_cf`, fed
  `hfn` from `fn_hfn` and the flat obligations from `SimPre` + the layout) →
  epilogue (`epilogue_sim`) → halt — and `runFuel_eq_stepN` bridges plain
  iteration to the halt-checking `runFuel` the statement uses (RESUME-PROGSIM
  §3.2: prove with `step^[k]`, convert at the top).
-/
import LowIR.ProgSim.LayoutFacts

namespace LowIR.ProgSim

open Rv64i (Instr State step Word decode fetch32 runFuel)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (St Program Name FunDef installData frameEnter dbaseOf)
open LowIR.Compile (userOff RA SP A T0 T1 totalFrame maxRegF maxRegS slotOff)
open LowIR.ProgSim.LayoutFacts LowIR.ProgSim.AsmFacts

/-! ## The `stepN` ↔ `runFuel` bridge. -/

/-- If the machine first reaches `halt` at exactly step `K`, plain iteration and
    the halt-checking `runFuel` agree at `K`. (The `hne` clause — `halt` not hit
    before `K` — is what `entry_run_sim` supplies: the only instruction at
    `codeBase+4` is the halt loop, reached solely by `entry`'s final `jalr`.) -/
theorem runFuel_eq_stepN (halt : Word) (K : Nat) (m : State)
    (hne : ∀ j, j < K → (stepN j m).pc ≠ halt) :
    runFuel halt K m = stepN K m := by
  induction K generalizing m with
  | zero => rfl
  | succ K ih =>
      have h0 : m.pc ≠ halt := hne 0 (by omega)
      have hstep : ∀ j, j < K → (stepN j (step m)).pc ≠ halt := fun j hj => by
        rw [← stepN_succ]; exact hne (j + 1) (by omega)
      rw [runFuel, if_neg h0, ih (step m) hstep, stepN_succ]

/-! ## The machine-side summit (`stepN` form). -/

/-- **`entry_run_sim`** — from the initial state, the machine runs the stub
    `jal`, `entry`'s prologue/body/epilogue, and halts at `codeBase+4` with
    `entry`'s returns in `a0..` and memory agreeing off the blob and the stack.
    The final `hne` conjunct records that `halt` is reached ONLY at the end
    (feeding `runFuel_eq_stepN`).

    PROOF DEFERRED — the remaining summit work, all atoms in hand:
    · stub step: `stub_emitted` + `step_jal` (m0 ↦ m1 at `codeBase + fnPos
      entry`, `ra := codeBase+4`, `sp = sp0`, args in `a0..`);
    · `prologue_sim` at m1 (frameEnter unfolded — `hcsp`/`hcrg` from `run_inv`'s
      `st0`, holes `[]`);
    · `lower_sim_cf` on `fd.body` (`hfn` ← `fn_hfn`; `hem` at the prologue end;
      `hdat`/`hdbase`/`hdpos`/`hpad`/`halign`/`hblob`/`hbd` ← `SimPre` + layout);
      `oc ∈ {normal, ret}` (from `run_inv`) both land at `epiPos`;
    · `epilogue_sim` (rets → `a0..`, restore, `jalr` to `ra = codeBase+4`); s' IS
      the body state (`run` doesn't remarshal), so `rget (10+j) = s'.rget rets[j]`
      matches directly;
    · `hne`: `fnPos entry ≥ 8 > 4`, so pc stays `> codeBase+4` until the final
      `jalr`. -/
theorem entry_run_sim
    {P : Program} {entry : Name} {fd : FunDef} {args : List Word}
    {sp0 : Word} {fuel : Nat} {s' : St} {L : Layout} {m0 : State}
    (hlk    : List.lookup entry P.env = some fd)
    (hL     : layoutOf P entry L.codeBase L.stackLo = some L)
    (hpre   : SimPre L L.stackLo sp0)
    (hpc    : m0.pc = L.codeBase)
    (hsp    : m0.rget 2 = sp0)
    (hargc  : args.length = fd.argc)
    (hargs  : ∀ i, i < fd.argc → m0.rget (10 + i) = args.getD i 0)
    (hinst  : Installed L m0)
    (hbr    : ∀ g gd, List.lookup g P.env = some gd → BranchOk gd.body)
    (haccess : ∀ st0,
                frameEnter L.stackLo fd (userPad P.env entry) args
                    (installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0)) sp0
                  = some st0 →
                MemAccOff L [(st0.sp, userOff fd)] P
                  (dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) P.data)
                  (userPad P.env) L.stackLo fuel fd.body st0)
    (hmem   : ∀ a, ¬ MachPriv L [] a →
                installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0) a
                  = m0.mem a)
    (hrun   : LowIR.Prog.run P L.stackLo fuel entry args (fun _ => 0) sp0
                (userPad P.env) (L.codeBase + BitVec.ofNat 64 L.segStart) = some s') :
    ∃ K, (stepN K m0).pc = L.haltPc
       ∧ (∀ j, j < fd.rvc → (stepN K m0).rget (10 + j) = s'.rget (fd.rets.toList.getD j 0))
       ∧ (∀ a, ¬ memRange a L.codeBase L.blobLen → ¬ MachStack L.stackLo sp0 a →
            s'.mem a = (stepN K m0).mem a)
       ∧ (∀ j, j < K → (stepN j m0).pc ≠ L.haltPc) := by
  -- ==== IL-side inversion + layout / hfn harvest ====
  obtain ⟨fd', st0, oc, hlk', hfe, hbodyexec, hoc⟩ := LowIR.Prog.run_inv hrun
  rw [hlk] at hlk'; rw [Option.some.injEq] at hlk'; subst hlk'
  obtain ⟨hcb, hslo, hLdata, hsegStart, dats, hc⟩ := layoutOf_decomp hL
  have hseg : 4 * L.instrs.length ≤ L.segStart := by rw [hsegStart]; exact LowIR.Prog.pad8_ge _
  have hblobW : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64 := by
    have := hpre.blobBelowStack; have := L.stackLo.isLt; omega
  have hfnAll := fn_hfn hL hc (codeLen_lt L hseg hpre.blobFits) hbr
  obtain ⟨hfnEm, hfnBnd, hfnBr, hfnTF, hfnFS8, hfnAlign, hfn8⟩ := hfnAll entry fd hlk
  have hpadf : userPad P.env entry = userOff fd := userPad_eq P.env entry fd hlk
  -- ==== seg 0: the stub `jal RA, entry` at codeBase ====
  have hstub := stub_emitted hL hc
  have hem0 : Emitted L 0 [Instr.jal RA (BitVec.ofInt 21 (fnPosOf L entry : Int))] :=
    Emitted_append_left _ _ _ _ hstub
  have hpc0 : m0.pc = L.codeBase + BitVec.ofNat 64 0 := by rw [hpc]; bv_omega
  have hd0 : decode (fetch32 m0) = Instr.jal RA (BitVec.ofInt 21 (fnPosOf L entry : Int)) := by
    have h := decode_at L m0 m0 0 _ hem0 hinst 0 (by simp) (by rw [hpc0]) rfl
    simpa using h
  have hδlo : -(2 ^ 20 : Int) ≤ (fnPosOf L entry : Int) := by omega
  have hδhi : (fnPosOf L entry : Int) < 2 ^ 20 := by omega
  have hstep0 := step_jal m0 RA _ hd0
  have hm1pc : (step m0).pc = L.codeBase + BitVec.ofNat 64 (fnPosOf L entry) := by
    rw [hstep0, pc_setPc, hpc0, signExtend_ofInt_21 _ hδlo hδhi,
        show ((fnPosOf L entry : Int)) = ((fnPosOf L entry : Int)) - ((0 : Nat) : Int) from by omega,
        jump_lands]
  have hm1ra : (step m0).rget RA = L.codeBase + 4 := by
    rw [hstep0, rget_setPc, rget_rset_self _ RA _ (by decide), hpc]
  have hm1sp : (step m0).rget SP = sp0 := by
    rw [hstep0, rget_setPc, rget_rset_ne _ RA SP _ (by decide)]; exact hsp
  have hm1args : ∀ i, (step m0).rget (A i) = m0.rget (A i) := fun i => by
    rw [hstep0, rget_setPc, rget_rset_ne _ RA (A i) _ (by show 10 + i ≠ 1; omega)]
  have hm1mem : (step m0).mem = m0.mem := by rw [hstep0, mem_setPc, mem_rset]
  have hm1inst : Installed L (step m0) := by
    rw [hstep0]; exact Installed_setPc L _ _ (Installed_congr L m0 _ (by rw [mem_rset]) hinst)
  -- ==== unfold frameEnter to expose st0's fields ====
  have hfe0 := hfe
  rw [hpadf] at hfe
  simp only [LowIR.Prog.frameEnter] at hfe
  split at hfe
  · exact absurd hfe (by simp)
  rename_i hof
  rw [Option.some.injEq] at hfe
  have hofN : L.stackLo.toNat + fd.frameSize + userOff fd ≤ sp0.toNat := by
    simp only [Nat.not_lt] at hof; exact hof
  have htf_eq : totalFrame fd = userOff fd + fd.frameSize := rfl
  have hsp0ge : totalFrame fd ≤ sp0.toNat := by omega
  have hcsp : st0.sp = sp0 - BitVec.ofNat 64 (totalFrame fd) := by
    rw [← hfe]; simp only; rw [htf_eq, ← BitVec.ofNat_add_ofNat]; bv_omega
  have hcspN : st0.sp.toNat = sp0.toNat - totalFrame fd := by rw [hcsp]; bv_omega
  have hcmem : st0.mem = LowIR.Prog.zeroRange
      (installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0))
      (sp0 - BitVec.ofNat 64 fd.frameSize) fd.frameSize := by rw [← hfe]
  have hfbEq : sp0 - BitVec.ofNat 64 fd.frameSize = st0.sp + BitVec.ofNat 64 (userOff fd) := by
    rw [hcsp, htf_eq, ← BitVec.ofNat_add_ofNat]; bv_omega
  have hcrg : ∀ r, 1 ≤ r → st0.rget r
      = if r = fd.frameReg then sp0 - BitVec.ofNat 64 fd.frameSize
        else parkFold (fun _ => 0) (fd.params.toList.zip args) r := by
    intro r hr
    have hr0 : r ≠ 0 := Nat.one_le_iff_ne_zero.mp hr
    rw [← hfe]; simp only [LowIR.Prog.St.rget, if_neg hr0, parkFold]
  -- ==== seg 1: prologue ====
  have hemPro : Emitted L (fnPosOf L entry) (prologueI fd) :=
    Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ hfnEm)
  have hargs' : ∀ i, (hi : i < args.length) → (step m0).rget (A i) = args[i] := by
    intro i hi
    rw [hm1args i, show (A i) = 10 + i from rfl]
    have h := hargs i (by rw [hargc] at hi; exact hi)
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hlen : fd.params.toList.length = args.length := by
    rw [show fd.params.toList.length = fd.argc from by simp, hargc]
  have hparb : ∀ x ∈ fd.params.toList, x ≤ maxRegF fd := fun x hx => by
    have h1 : x ≤ fd.params.toList.foldl max 0 := mem_le_foldl_max x _ _ hx
    simp only [maxRegF]
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  have hfrb : fd.frameReg ≤ maxRegF fd := by
    simp only [maxRegF]; exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have haddr : (st0.sp + BitVec.ofNat 64 (userOff fd)).toNat = st0.sp.toNat + userOff fd := by
    have hsplt : sp0.toNat < 2 ^ 64 := sp0.isLt
    have h1 : st0.sp.toNat + userOff fd < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : userOff fd < 2 ^ 64)]
    omega
  have hmemF : ∀ a, OffPriv L ((st0.sp, userOff fd) :: []) st0.sp a →
      ¬ memRange a (st0.sp + BitVec.ofNat 64 (userOff fd)) fd.frameSize →
      st0.mem a = (step m0).mem a := by
    intro a hoff hnfr
    rw [hcmem]
    have hz : LowIR.Prog.zeroRange
        (installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0))
        (sp0 - BitVec.ofNat 64 fd.frameSize) fd.frameSize a
        = installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0) a := by
      simp only [LowIR.Prog.zeroRange, hfbEq]
      rw [if_neg]; intro hc; exact hnfr ⟨hc.1, hc.2⟩
    rw [hz, hm1mem]
    refine hmem a (fun hmp => hoff.1 ?_)
    rcases hmp with h | ⟨hh, hhm, _⟩
    · exact Or.inl h
    · exact absurd hhm (by simp)
  have hcmemZ : ∀ a, memRange a (st0.sp + BitVec.ofNat 64 (userOff fd)) fd.frameSize →
      st0.mem a = 0 := by
    intro a ha
    have ha' : BitVec.toNat (st0.sp + BitVec.ofNat 64 (userOff fd)) ≤ BitVec.toNat a
        ∧ BitVec.toNat a < BitVec.toNat (st0.sp + BitVec.ofNat 64 (userOff fd)) + fd.frameSize := ha
    rw [hcmem]; simp only [LowIR.Prog.zeroRange, hfbEq]; rw [if_pos ha']
  have hbdc : L.codeBase.toNat + L.blobLen ≤ st0.sp.toNat
      ∨ st0.sp.toNat + userOff fd ≤ L.codeBase.toNat :=
    Or.inl (by have := hpre.blobBelowStack; omega)
  have hbdcF : L.codeBase.toNat + L.blobLen ≤ st0.sp.toNat
      ∨ st0.sp.toNat + totalFrame fd ≤ L.codeBase.toNat :=
    Or.inl (by have := hpre.blobBelowStack; omega)
  obtain ⟨kPro, hProInv, hProPc, hProRA, hProMem, hProNoh⟩ :=
    prologue_sim L fd [] (step m0) sp0 (L.codeBase + 4) st0 args (fnPosOf L entry)
      hm1pc hemPro hm1inst hm1sp hm1ra hargs' hlen hparb hfrb hcsp hcrg hmemF hcmemZ hfnTF hfnFS8
      hpre.spAligned hsp0ge hseg hblobW hbdc hbdcF (by simp) (by simp) hfn8 (by omega)
  -- ==== seg 2: body via lower_sim_cf ====
  have hemBody : Emitted L (fnPosOf L entry + 4 * prologueSize fd)
      (emitCF P.data (dposOf L) (fnPosOf L) [] []
        (fnPosOf L entry + 4 * prologueSize fd + 4 * csize fd.body)
        (fnPosOf L entry + 4 * prologueSize fd) fd.body) := by
    have h := Emitted_append_right _ _ (prologueI fd) _ (Emitted_append_left _ _ _ _ hfnEm)
    rw [show (prologueI fd).length = prologueSize fd from rfl] at h
    exact h
  have hregBody : maxRegS fd.body ≤ maxRegF fd := by simp only [maxRegF]; exact Nat.le_max_left _ _
  have hnwBody : st0.sp.toNat + userOff fd ≤ 2 ^ 64 := by have := sp0.isLt; omega
  have hbdBody : (L.codeBase.toNat + L.blobLen ≤ L.stackLo.toNat ∧ L.stackLo.toNat ≤ st0.sp.toNat)
      ∨ st0.sp.toNat + userOff fd ≤ L.codeBase.toNat :=
    Or.inl ⟨hpre.blobBelowStack, by have := hpre.blobBelowStack; omega⟩
  have haccBody : MemAccOff L ((st0.sp, userOff fd) :: []) P
      (dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) P.data) (userPad P.env) L.stackLo fuel
      fd.body st0 := haccess st0 hfe0
  have hframeBody : userOff fd ≤ 2000 := by have h := hfnTF; simp only [totalFrame] at h; omega
  obtain ⟨kBod, hBodInv, hBodPc, hBodFr, hnohBod⟩ :=
    lower_sim_cf fuel fd.body st0 s' oc (stepN kPro (step m0))
      (fnPosOf L entry + 4 * prologueSize fd) [] []
      hbodyexec hProInv hProPc hemBody hregBody hnwBody hbdBody haccBody
      ⟨by simp, by simp, ⟨by omega, by omega⟩⟩ (by omega) hfnBr hframeBody
      (by omega) (by omega) hseg hblobW
      (clen_synthOk (compileProgT_dataBound hc)) (fun d a h => dbaseOf_dposOf L d a (hLdata.symm ▸ h))
      (fun d => dposOf_lt L hpre.blobFits d) (fun g gd h => userPad_eq P.env g gd h)
      hpre.codeAligned rfl hfnAll
  have hBodPc' : (stepN kBod (stepN kPro (step m0))).pc
      = L.codeBase + BitVec.ofNat 64 (fnPosOf L entry + 4 * prologueSize fd + 4 * csize fd.body) := by
    rw [hBodPc]; rcases hoc with h | h <;> subst h <;> simp only [landPos]
  -- ==== seg 3: epilogue ====
  have huo16 : 16 ≤ userOff fd := by simp only [userOff]; omega
  have hs1sp : s'.sp = st0.sp := by
    have hc5 := hBodInv.2.2.2.2.1
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hc5
    exact hc5.1.symm
  have hemEpi : Emitted L (fnPosOf L entry + 4 * prologueSize fd + 4 * csize fd.body)
      (epilogueI fd) := by
    have h := Emitted_append_right _ _ (prologueI fd ++ emitCF P.data (dposOf L) (fnPosOf L) [] []
        (fnPosOf L entry + 4 * prologueSize fd + 4 * csize fd.body)
        (fnPosOf L entry + 4 * prologueSize fd) fd.body) (epilogueI fd) hfnEm
    rw [List.length_append, emitCF_length, show (prologueI fd).length = prologueSize fd from rfl] at h
    rw [show fnPosOf L entry + 4 * (prologueSize fd + csize fd.body)
          = fnPosOf L entry + 4 * prologueSize fd + 4 * csize fd.body from by omega] at h
    exact h
  have hcadd : ∀ i : Nat, i < 8 → (st0.sp + BitVec.ofNat 64 i).toNat = st0.sp.toNat + i := by
    intro i hi
    have hclt : st0.sp.toNat < 2 ^ 64 := st0.sp.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]; omega
  have hraslot : (stepN kBod (stepN kPro (step m0))).loadWord s'.sp = L.codeBase + 4 := by
    rw [hs1sp]
    have hpres : ∀ i : Nat, i < 8 →
        (stepN kBod (stepN kPro (step m0))).mem (st0.sp + BitVec.ofNat 64 i)
          = (stepN kPro (step m0)).mem (st0.sp + BitVec.ofNat 64 i) := by
      intro i hi
      have haddi := hcadd i hi
      have hmr : memRange (st0.sp + BitVec.ofNat 64 i) st0.sp (userOff fd) :=
        ⟨by rw [haddi]; omega, by rw [haddi]; omega⟩
      exact hBodFr _ ⟨(st0.sp, userOff fd), List.mem_cons_self, hmr⟩ (Or.inl (by rw [haddi]; omega))
    refine (State_loadWord_congr8 _ _ st0.sp
      (by simpa using hpres 0 (by omega)) (by simpa using hpres 1 (by omega))
      (by simpa using hpres 2 (by omega)) (by simpa using hpres 3 (by omega))
      (by simpa using hpres 4 (by omega)) (by simpa using hpres 5 (by omega))
      (by simpa using hpres 6 (by omega)) (by simpa using hpres 7 (by omega))).trans hProRA
  have hretbGd : ∀ x ∈ fd.rets.toList, x ≤ maxRegF fd := fun x hx => by
    have h1 : x ≤ fd.rets.toList.foldl max 0 := mem_le_foldl_max x _ _ hx
    simp only [maxRegF]
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  have hretslotGd : ∀ x ∈ fd.rets.toList, slotOff x < 2 ^ 11 := fun x hx => by
    have := slotOff_add8_le_userOff fd x (hretbGd x hx); omega
  have hraeven : (L.codeBase + 4).toNat % 2 = 0 := by
    rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hpre.codeAligned; omega
  obtain ⟨kEpi, hEpiPc, hEpiSP, hEpiVal, hEpiMem, hEpiNoh⟩ :=
    epilogue_sim L fd ((st0.sp, userOff fd) :: []) (stepN kBod (stepN kPro (step m0))) s'
      (L.codeBase + 4) (fnPosOf L entry + 4 * prologueSize fd + 4 * csize fd.body)
      hBodInv hBodPc' hemEpi hraslot hraeven hretbGd hretslotGd (by simp only [totalFrame]; omega)
      (by omega)
      (by have hv : fd.rets.toList.length = fd.rvc := by simp
          simp only [epilogueSize] at hfnBnd; omega)
  -- ==== the composition + the four conclusions ====
  have hK : stepN (1 + kPro + kBod + kEpi) m0
      = stepN kEpi (stepN kBod (stepN kPro (step m0))) := by
    have e : step m0 = stepN 1 m0 := rfl
    rw [e, stepN_add (1 + kPro + kBod) kEpi, stepN_add (1 + kPro) kBod, stepN_add 1 kPro]
  refine ⟨1 + kPro + kBod + kEpi, ?_, ?_, ?_, ?_⟩
  · rw [hK, hEpiPc]; rfl
  · intro j hj
    rw [hK]
    have hj' : j < fd.rets.toList.length := by
      rw [show fd.rets.toList.length = fd.rvc from by simp]; exact hj
    rw [show (10 + j) = A j from rfl, hEpiVal j hj', List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj', Option.getD_some]
  · -- memory conclusion
    intro a hblob hstk
    rw [hK, hEpiMem]
    have hdisj := not_memRange hstk
    have hstkNat := hpre.stackNonEmpty
    have hoff : OffPriv L ((st0.sp, userOff fd) :: []) s'.sp a := by
      rw [hs1sp]
      refine ⟨fun hmp => ?_, fun hfree => ?_⟩
      · rcases hmp with h | ⟨hh, hhm, hr⟩
        · exact hblob h
        · rcases List.mem_singleton.mp hhm with rfl
          simp only [memRange] at hr; omega
      · simp only [memRange] at hfree; omega
    exact hBodInv.2.2.2.1 a hoff
  · -- hne / NoHalt
    have hnohStub : NoHalt L 1 m0 :=
      NoHalt_cons L 0 m0 (by rw [hpc]; exact codeBase_ne_halt L) (NoHalt_zero L _)
    have hNoH : NoHalt L (1 + kPro + kBod + kEpi) m0 := by
      rw [show 1 + kPro + kBod + kEpi = 1 + (kPro + (kBod + kEpi)) from by omega]
      refine NoHalt_chain L 1 (kPro + (kBod + kEpi)) m0 hnohStub ?_
      refine NoHalt_chain L kPro (kBod + kEpi) (step m0) hProNoh ?_
      exact NoHalt_chain L kBod kEpi (stepN kPro (step m0)) hnohBod hEpiNoh
    intro j hj
    exact hNoH j hj

/-! ## The summit. -/

/-- **`prog_sim`** (RESUME-PROGSIM §3.3) — if the D7/D8 IL says `entry(args)`
    computes `s'` (with the P1 padding `userPad`), the compiled RV64I blob,
    started at `codeBase` with `args` in `a0..` and `sp = sp0`, runs to the halt
    pad in a state whose `a0..` hold `entry`'s returns and whose memory agrees
    with `s'` off the blob and the stack. Assembles `entry_run_sim` with the
    `runFuel_eq_stepN` bridge. -/
theorem prog_sim
    {P : Program} {entry : Name} {fd : FunDef} {args : List Word}
    {sp0 : Word} {fuel : Nat} {s' : St} {L : Layout} {m0 : State}
    (hlk    : List.lookup entry P.env = some fd)
    (hL     : layoutOf P entry L.codeBase L.stackLo = some L)
    (hpre   : SimPre L L.stackLo sp0)
    (hpc    : m0.pc = L.codeBase)
    (hsp    : m0.rget 2 = sp0)
    (hargc  : args.length = fd.argc)
    (hargs  : ∀ i, i < fd.argc → m0.rget (10 + i) = args.getD i 0)
    (hinst  : Installed L m0)
    (hbr    : ∀ g gd, List.lookup g P.env = some gd → BranchOk gd.body)
    (haccess : ∀ st0,
                frameEnter L.stackLo fd (userPad P.env entry) args
                    (installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0)) sp0
                  = some st0 →
                MemAccOff L [(st0.sp, userOff fd)] P
                  (dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) P.data)
                  (userPad P.env) L.stackLo fuel fd.body st0)
    (hmem   : ∀ a, ¬ MachPriv L [] a →
                installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0) a
                  = m0.mem a)
    (hrun   : LowIR.Prog.run P L.stackLo fuel entry args (fun _ => 0) sp0
                (userPad P.env) (L.codeBase + BitVec.ofNat 64 L.segStart) = some s') :
    ∃ k, (runFuel L.haltPc k m0).pc = L.haltPc
       ∧ (∀ j, j < fd.rvc →
            (runFuel L.haltPc k m0).rget (10 + j) = s'.rget (fd.rets.toList.getD j 0))
       ∧ (∀ a, ¬ memRange a L.codeBase L.blobLen → ¬ MachStack L.stackLo sp0 a →
            s'.mem a = (runFuel L.haltPc k m0).mem a) := by
  obtain ⟨K, hHalt, hRets, hMem, hne⟩ :=
    entry_run_sim hlk hL hpre hpc hsp hargc hargs hinst hbr haccess hmem hrun
  have hbridge := runFuel_eq_stepN L.haltPc K m0 hne
  exact ⟨K, by rw [hbridge]; exact hHalt,
             fun j hj => by rw [hbridge]; exact hRets j hj,
             fun a h1 h2 => by rw [hbridge]; exact hMem a h1 h2⟩

/-! ## E2 — statement sanity (RESUME-ENTRY §6).

    The four repaired hypotheses are inhabitable on concrete data — a cheap
    catcher for a mis-stated (unsatisfiable / self-contradictory) statement, since
    nothing else constructs `SimPre`/`haccess` yet. -/
section Sanity
open LowIR.Prog (sub3)

/-- `haccess`'s `MemAccOff` obligation reduces and is trivially dischargeable for a
    body with no memory ops (`sub3 = (a+b)−c`), at any fuel/holes — confirms the
    footprint hypothesis has the right shape and unfolds as intended. -/
example (L : Layout) (holes : List Hole) (P : Program) (dbase : Name → Option Word)
    (pad : Name → Nat) (slo : Word) (fuel : Nat) (st0 : St) :
    MemAccOff L holes P dbase pad slo fuel sub3.body st0 := by
  cases fuel with
  | zero => trivial
  | succ f => simp [sub3, MemAccOff]

/-- `SimPre` is inhabitable: a realistic high code base with a small blob and the
    stack far above (no contradiction among `blobBelowStack`/`stackNonEmpty`/the
    alignment fields). -/
example :
    SimPre { codeBase := 0x80000000, instrs := [], fnTab := [], segStart := 8,
             data := [], stackLo := 0x80100000 } 0x80100000 0x80101000 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

-- The entry layout exists at the same realistic base.
#guard (layoutOf [("sub3", sub3)] "sub3" 0x80000000 0x80100000).isSome

end Sanity

end LowIR.ProgSim
