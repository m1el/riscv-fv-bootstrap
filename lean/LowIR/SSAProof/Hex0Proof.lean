/-
  LowIR.SSAProof.Hex0Proof — Phases 2–6 of the hex0-on-SSA campaign
  (docs/RESUME-SSA-HEX0.md). Proves `hex0S_correct`: the SSA `hex0S` computes
  `Hex0.coreSpec`. The spec-side layer (pnibR bridges, boundedRun, commentSkip,
  decodeS unfolders, regionBytes, the geu/slt condition lemmas, the borrow
  Slice/Wf layer) imports VERBATIM from `LowIR.CtrlHex0Proof`; only the
  IL-facing pieces are rebuilt on the SSA `exec`.

  STATUS: in progress. Landed so far —
    • Phase 2: `pnibS_eff` — the value-producing nibble `ife` writes `pnibR c`
      into `dst` (all 5 leaves; frame follows separately from `exec_frame`).
  Remaining: prelude / read-char / cond-dispatch (Phase 2 tail), `skipCommentS_eff`
  (Phase 3), `body_step` (Phase 4), `main_loop` (Phase 5), assembly (Phase 6).
-/
import LowIR.SSAProof.ExecFacts
import LowIR.SSALib
import LowIR.CtrlHex0Proof

namespace LowIR.SSA

open LowIR (Cond evalCond)
open Rv64i (Word Byte)
open LowIR.Ctrl.Hex0 (pnibR pnibR_nibble pnibR_eq_255_iff pnibR_lt_16 hexbyte_val
  geuL_true geuL_false slt_true slt_false tn regionBytes boundedRun commentSkip)

variable (env : Env) (sl : Word)

/-! ### Guard evaluation for the pnib byte comparisons (byte vs constant). -/

/-- `geu (byte) (const)` : true iff `const ≤ byte`. -/
theorem geuR_true (c : Byte) (m : Nat) (hm : (BitVec.ofNat 64 m).toNat = m) (h : m ≤ c.toNat) :
    evalCond .geu (c.setWidth 64) (BitVec.ofNat 64 m) = true :=
  LowIR.Ctrl.Strtoull2.geu_true hm h

theorem geuR_false (c : Byte) (m : Nat) (hm : (BitVec.ofNat 64 m).toNat = m) (h : c.toNat < m) :
    evalCond .geu (c.setWidth 64) (BitVec.ofNat 64 m) = false :=
  LowIR.Ctrl.Strtoull2.geu_false hm h

/-! ### `pnibS_eff` — the nibble decode `ife` writes `pnibR c` into `dst`.

    Every guard reads the entry state `s` (the nested `ife`s have no writes
    before the leaf `sub`), so `s.rget src`/consts suffice. The frame (all regs
    outside `{dst,t1,t2}` preserved) follows separately from `exec_frame`. -/

theorem pnibS_eff (s : St) (dst t1 t2 src : Reg) (c : Byte)
    (hsrc : s.rget src = c.setWidth 64)
    (h17 : s.rget 17 = 55) (h20 : s.rget 20 = 48) (h21 : s.rget 21 = 57)
    (h22 : s.rget 22 = 65) (h23 : s.rget 23 = 70)
    (hd0 : dst ≠ 0) (ht1 : t1 ≠ 0) (ht2 : t2 ≠ 0) :
    ∃ s', exec env sl 6 (Lib.pnibS dst t1 t2 src) s = some (s', .normal)
      ∧ s'.rget dst = pnibR c ∧ s'.mem = s.mem := by
  have c48 := LowIR.Ctrl.Hex0.c48
  have c57 := LowIR.Ctrl.Hex0.c57
  have c65 := LowIR.Ctrl.Hex0.c65
  have c70 := LowIR.Ctrl.Hex0.c70
  -- guard equalities (each reads the entry state `s`)
  have G1 (h : 48 ≤ c.toNat) : evalCond .geu (s.rget src) (s.rget 20) = true := by
    rw [hsrc, h20]; exact geuR_true c 48 c48 h
  have G1f (h : c.toNat < 48) : evalCond .geu (s.rget src) (s.rget 20) = false := by
    rw [hsrc, h20]; exact geuR_false c 48 c48 h
  have G2 (h : c.toNat ≤ 57) : evalCond .geu (s.rget 21) (s.rget src) = true := by
    rw [hsrc, h21]; exact geuL_true c 57 c57 h
  have G2f (h : 57 < c.toNat) : evalCond .geu (s.rget 21) (s.rget src) = false := by
    rw [hsrc, h21]; exact geuL_false c 57 c57 h
  have G3 (h : 65 ≤ c.toNat) : evalCond .geu (s.rget src) (s.rget 22) = true := by
    rw [hsrc, h22]; exact geuR_true c 65 c65 h
  have G3f (h : c.toNat < 65) : evalCond .geu (s.rget src) (s.rget 22) = false := by
    rw [hsrc, h22]; exact geuR_false c 65 c65 h
  have G4 (h : c.toNat ≤ 70) : evalCond .geu (s.rget 23) (s.rget src) = true := by
    rw [hsrc, h23]; exact geuL_true c 70 c70 h
  have G4f (h : 70 < c.toNat) : evalCond .geu (s.rget 23) (s.rget src) = false := by
    rw [hsrc, h23]; exact geuL_false c 70 c70 h
  unfold Lib.pnibS
  by_cases hg1 : 48 ≤ c.toNat
  · by_cases hg2 : c.toNat ≤ 57
    · -- '0'..'9': leaf A, dst := c - 48
      have hval : pnibR c = c.setWidth 64 - 48 := by unfold pnibR; rw [if_pos ⟨hg1, hg2⟩]
      have hsub : exec env sl 3 (.sub t1 src 20) s = some (s.rset t1 (c.setWidth 64 - 48), .normal) := by
        rw [show (3:Nat) = 2+1 from rfl, exec_sub, hsrc, h20]
      have hA : exec env sl 4 (.seq (.sub t1 src 20) (.brk 1 [.reg t1])) s
          = some (s.rset t1 (c.setWidth 64 - 48), .brk 1 [c.setWidth 64 - 48]) := by
        rw [show (4:Nat) = 3+1 from rfl, exec_seq_normal (h := hsub), exec_brk]
        simp [rget_rset_eq _ t1 _ ht1]
      refine ⟨(s.rset t1 (c.setWidth 64 - 48)).rset dst (c.setWidth 64 - 48), ?_, ?_, by simp⟩
      · rw [exec_ife_then (hc := G1 hg1), exec_ife_then (hc := G2 hg2), hA,
            catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
      · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
    · -- c > 57
      by_cases hg3 : 65 ≤ c.toNat
      · by_cases hg4 : c.toNat ≤ 70
        · -- 'A'..'F': leaf sub t2, dst := c - 55
          have hval : pnibR c = c.setWidth 64 - 55 := by
            unfold pnibR; rw [if_neg (by omega), if_pos ⟨hg3, hg4⟩]
          have hsub : exec env sl 1 (.sub t2 src 17) s = some (s.rset t2 (c.setWidth 64 - 55), .normal) := by
            rw [show (1:Nat) = 0+1 from rfl, exec_sub, hsrc, h17]
          have hA : exec env sl 2 (.seq (.sub t2 src 17) (.brk 3 [.reg t2])) s
              = some (s.rset t2 (c.setWidth 64 - 55), .brk 3 [c.setWidth 64 - 55]) := by
            rw [show (2:Nat) = 1+1 from rfl, exec_seq_normal (h := hsub), exec_brk]
            simp [rget_rset_eq _ t2 _ ht2]
          refine ⟨(s.rset t2 (c.setWidth 64 - 55)).rset dst (c.setWidth 64 - 55), ?_, ?_, by simp⟩
          · rw [exec_ife_then (hc := G1 hg1), exec_ife_else (hc := G2f (by omega)),
                exec_ife_then (hc := G3 hg3), exec_ife_then (hc := G4 hg4), hA,
                catch0_brkS, catch0_brkS, catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
          · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
        · -- c > 70: brk 3 [255], dst := 255
          have hval : pnibR c = 255 := by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)]
          refine ⟨s.rset dst 255, ?_, ?_, by simp⟩
          · rw [exec_ife_then (hc := G1 hg1), exec_ife_else (hc := G2f (by omega)),
                exec_ife_then (hc := G3 hg3), exec_ife_else (hc := G4f (by omega)), exec_brk,
                catch0_brkS, catch0_brkS, catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
          · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
      · -- 57 < c < 65: brk 2 [255], dst := 255
        have hval : pnibR c = 255 := by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)]
        refine ⟨s.rset dst 255, ?_, ?_, by simp⟩
        · rw [exec_ife_then (hc := G1 hg1), exec_ife_else (hc := G2f (by omega)),
              exec_ife_else (hc := G3f (by omega)), exec_brk,
              catch0_brkS, catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
        · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
  · -- c < 48: ELSE brk 0 [255], dst := 255
    have hval : pnibR c = 255 := by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)]
    refine ⟨s.rset dst 255, ?_, ?_, by simp⟩
    · rw [exec_ife_else (hc := G1f (by omega)), exec_brk, catch0_brk0 _ _ _ (by rfl)]; rfl
    · rw [hval]; simp [rget_rset_eq _ dst _ hd0]

/-! ### `lit` — a single constant load (`v < 2048`, so the 12-bit immediate
    sign-extends to `v`). -/

theorem signExtend_ofNat_small (v : Nat) (hv : v < 2048) :
    (BitVec.ofNat 12 v).signExtend 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have hlt : (BitVec.ofNat 12 v).toNat = v := by rw [BitVec.toNat_ofNat]; omega
  have hmsb : (BitVec.ofNat 12 v).msb = false := by
    rw [BitVec.msb_eq_decide, hlt]; exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, hlt, BitVec.toNat_ofNat]

theorem exec_lit (fuel r v : Nat) (s : St) (hv : v < 2048) :
    exec env sl (fuel+1) (Lib.lit r v) s = some (s.rset r (BitVec.ofNat 64 v), .normal) := by
  unfold Lib.lit
  rw [exec_addi, rget_zero, signExtend_ofNat_small v hv, show (0 : Word) + BitVec.ofNat 64 v
        = BitVec.ofNat 64 v from by bv_omega]

end LowIR.SSA
