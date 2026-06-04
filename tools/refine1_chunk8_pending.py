path = '/var/data/bootstrap/lean/Hex1/Refine.lean'
src = open(path).read()
chunk = r'''
/-! ## Pass-1 iteration: comment tokens, assembled. -/

/-- State shape on arrival at pass-2 entry (offset 360): pass 1 scanned the
    whole input cleanly, the table holds the final label map. -/
structure P2Start (inp : List Nat) (cap : Nat) (s : State)
    (labF : Labels) (m : Nat) : Prop where
  wf      : WellFormed1 inp cap
  pc      : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 360)
  code    : CodeLoaded1 s
  a0      : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr
  a1      : s.rget 11 = BitVec.ofNat 64 inp.length
  a2      : s.rget 12 = BitVec.ofNat 64 Image1.outAddr
  a3      : s.rget 13 = BitVec.ofNat 64 cap
  a4      : s.rget 14 = BitVec.ofNat 64 Image1.lblAddr
  ra0     : s.rget 1  = 0
  in_mem  : InputLoaded s inp
  tbl     : TableLoaded s labF
  m_le    : m ≤ cap
  lab_le  : ∀ c p, labF c = some p → p ≤ m
  scan_ok : Hex1.scan1 .High Hex1.noLabels 0 inp = (labF, m, .Ok)

/-- `rest'` is the drop at the bumped index (suffix decomposition). -/
theorem suffix_tail (inp : List Nat) (c : Nat) (rest' : List Nat)
    (hsuf : inp.drop (inp.length - (c :: rest').length) = c :: rest') :
    inp.drop (inp.length - rest'.length) = rest' := suffix_step inp c rest' hsuf

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-1 iteration for a comment token (`#`/`;`): prefix +
    dispatch to 332 + the inner loop. Lands back at the loop head sitting on
    the newline (invariant on a strictly shorter suffix), or at pass-2 entry
    on EOF (the scan is complete and Ok). -/
theorem p1_comment (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos (c :: rest'))
    (hcm : Hex0.isComment c = true) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ rest2, rest2.length < (c :: rest').length ∧
          P1Inv inp cap s' lab pos rest2) ∨
        P2Start inp cap s' lab pos) := by
  have hc : c = 35 ∨ c = 59 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_true, beq_iff_eq] at hcm
    exact hcm
  -- facts about lengths/indices
  have hlen64 : inp.length < 2 ^ 64 := by
    have h1 := inv.wf.in_fits; have h2 := inv.wf.out_fits; have h3 := inv.wf.lbl_fits
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at h1 h2 h3; omega
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons] at h; omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_tail inp c rest' inv.suffix
  -- the index after consuming c
  have hidx1 : inp.length - rest'.length = (inp.length - (c :: rest').length) + 1 := by
    simp only [List.length_cons]; omega
  -- machine: prefix
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p1_prefix inp cap c rest' lab pos s inv
  -- machine: dispatch to 332 (per comment char)
  have hdispatch : ∃ d sd, runFuel 0 d s4 = sd ∧ 0 < d ∧
      sd.pc = BitVec.ofNat 64 (Image1.coreAddr + 332) ∧ sd.mem = s4.mem ∧
      (∀ i, i ≠ 28 → sd.rget i = s4.rget i) := by
    rcases hc with h35 | h59
    · subst h35
      have hb := li_beq_eq s4 52 35 35 (BitVec.ofNat 13 276)
        (BitVec.ofNat 64 (Image1.coreAddr + 332)) hcode4 hpc4 ht2 dec_52 dec_56
        (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
      refine ⟨2, (s4.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 332)), hb, by omega, rfl, rfl, ?_⟩
      intro i hi
      exact li_block_frame _ _ _ i hi
    · subst h59
      have hb1 := li_beq_ne s4 52 35 59 (BitVec.ofNat 13 276) hcode4 hpc4 ht2 dec_52 dec_56
        (by decide) (by decide) (by rw [coreBytes_len]; omega)
      let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 60))
      have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + (52 + 8))) := rfl
      try rw [← hv1] at hb1
      have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode4)
      have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 60) := rfl
      have ht2v1 : v1.rget 7 = BitVec.ofNat 64 59 := by
        rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (7:Nat) ≠ 28)]
        exact ht2
      have hb2 := li_beq_eq v1 60 59 59 (BitVec.ofNat 13 268)
        (BitVec.ofNat 64 (Image1.coreAddr + 332)) hc1 hpc1 ht2v1 dec_60 dec_64
        (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
      refine ⟨4, (v1.rset 28 (BitVec.ofNat 64 59)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 332)), ?_, by omega, rfl, rfl, ?_⟩
      · rw [show (4:Nat) = 2 + 2 from rfl, runFuel_add, hb1, hb2]
      · intro i hi
        rw [li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]
  obtain ⟨d, sd, hrund, hd, hpcd, hmemd, hframed⟩ := hdispatch
  -- inner loop preconditions at sd
  have hcoded : CodeLoaded1 sd := by
    intro i hi
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi
  have h5d : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide), hidx4]
  have h10d : sd.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
    rw [hframed 10 (by decide), hframe4 10 (by decide) (by decide) (by decide) (by decide)]
    exact inv.a0
  have h11d : sd.rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hframed 11 (by decide), hframe4 11 (by decide) (by decide) (by decide) (by decide)]
    exact inv.a1
  have hind : InputLoaded sd inp := by
    intro j hj
    rw [show sd.mem = s4.mem from hmemd, show s4.mem = s.mem from hmem4]
    exact inv.in_mem j hj
  obtain ⟨k, hk⟩ := comment_loop1 inp (inp.length - (inp.length - rest'.length)) sd
    (inp.length - rest'.length) hcoded hpcd h5d h10d h11d hind hlen64 inv.wf.bytes_ok
    (by omega) (by omega)
  -- spec-side: the comment unfold
  have hspec_cm : Hex1.scan1 .High lab pos (c :: rest')
      = Hex1.scan1 .High lab pos (Hex0.skipComment rest') := by
    rw [Hex1.scan1]
    rw [if_pos hcm]
  -- frame from s to the loop result
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  rcases hk with ⟨q, hq1, hq2, hq3, hqskip, hp, h5q, hmemq, hothq⟩ |
                 ⟨hqskip, hp, h5q, hmemq, hothq⟩
  · -- newline found at q: back to the loop head on suffix `drop q`
    rw [hrest'_eq] at hqskip
    have hmemfin : (runFuel 0 k sd).mem = s.mem := by
      rw [hmemq, hmemd, hmem4]
    have hregfin : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
        (runFuel 0 k sd).rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hothq i h5 h7 h28]
      exact hframe_sd i h0 h5 h7 h28
    refine ⟨4 + (d + k), _, by omega,
      by rw [runFuel_add, hrun4, runFuel_add, hrund], Or.inl ⟨inp.drop q, ?_, ?_⟩⟩
    · simp only [List.length_drop, List.length_cons]
      omega
    exact {
      wf := inv.wf
      at_loop := hp
      code := by
        intro i hi
        rw [hmemfin]
        exact inv.code i hi
      a0 := by rw [hregfin 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
      a1 := by rw [hregfin 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
      a2 := by rw [hregfin 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
      a3 := by rw [hregfin 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
      a4 := by rw [hregfin 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
      ra0 := by rw [hregfin 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
      in_mem := by
        intro j hj
        rw [hmemfin]
        exact inv.in_mem j hj
      idx := by
        rw [h5q]
        congr 1
        simp only [List.length_drop]
        omega
      suffix := by
        have : inp.length - (inp.drop q).length = q := by
          simp only [List.length_drop]
          omega
        rw [this]
      outidx := by
        rw [hregfin 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
      pos_le := inv.pos_le
      tbl := by
        intro cc hcc kk hkk
        rw [hmemfin]
        exact inv.tbl cc hcc kk hkk
      lab_le := inv.lab_le
      spec := by
        -- scan1 (drop q) = scan1 (10 :: drop (q+1)) = scan1 (drop (q+1))
        --   = scan1 (skipComment rest') = scan1 (c :: rest') = whole input
        have hdq : inp.drop q = 10 :: inp.drop (q + 1) := by
          rw [List.drop_eq_getElem_cons hq2,
              show inp[q] = inp.getD q 0 from List.getElem_eq_getD 0, hq3]
        rw [hdq]
        rw [show Hex1.scan1 .High lab pos (10 :: inp.drop (q + 1))
            = Hex1.scan1 .High lab pos (inp.drop (q + 1)) from by
          rw [Hex1.scan1]
          rw [if_neg (by decide), if_pos (by decide)]]
        rw [← hqskip, ← hspec_cm]
        exact inv.spec }
  · -- EOF: the scan is complete and Ok → pass-2 entry
    rw [hrest'_eq] at hqskip
    have hscan_done : Hex1.scan1 .High lab pos (c :: rest') = (lab, pos, .Ok) := by
      rw [hspec_cm, hqskip]
      rw [Hex1.scan1]
    have hmemfin : (runFuel 0 k sd).mem = s.mem := by
      rw [hmemq, hmemd, hmem4]
    have hregfin : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
        (runFuel 0 k sd).rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hothq i h5 h7 h28]
      exact hframe_sd i h0 h5 h7 h28
    refine ⟨4 + (d + k), _, by omega,
      by rw [runFuel_add, hrun4, runFuel_add, hrund], Or.inr ?_⟩
    exact {
      wf := inv.wf
      pc := hp
      code := by
        intro i hi
        rw [hmemfin]
        exact inv.code i hi
      a0 := by rw [hregfin 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
      a1 := by rw [hregfin 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
      a2 := by rw [hregfin 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
      a3 := by rw [hregfin 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
      a4 := by rw [hregfin 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
      ra0 := by rw [hregfin 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
      in_mem := by
        intro j hj
        rw [hmemfin]
        exact inv.in_mem j hj
      tbl := by
        intro cc hcc kk hkk
        rw [hmemfin]
        exact inv.tbl cc hcc kk hkk
      m_le := inv.pos_le
      lab_le := inv.lab_le
      scan_ok := by rw [← inv.spec, hscan_done] }
'''
src = src.replace("\nend Hex1.Refine", chunk + "\nend Hex1.Refine")
open(path, 'w').write(src)
print("appended chunk 8")
