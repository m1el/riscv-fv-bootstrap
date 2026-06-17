/-
  Functional correctness of hex0 on the control-flow IL — FOUNDATION.

  This is the largest of the LowIR proofs (hex0's two-state decoder vs `Hex0.coreSpec`).
  Built in pieces; this file starts with the reusable foundation: unsigned condition
  lemmas in both operand orders, and `pnib_correct` (the nibble parser ≡ `Hex0.nibble`).
  The comment-skip loop and the main-loop invariant follow.
-/
import LowIR.CtrlHex0
import LowIR.CtrlStrlen
import LowIR.CtrlStrtoullProof
import LowIR.CtrlStrtoull2Proof
import Hex0.Spec

set_option linter.unusedSimpArgs false

namespace LowIR.Ctrl.Hex0

open LowIR.Ctrl
open Rv64i (Word Byte)

theorem tn (m : Nat) (hm : m < 2^64) : ((BitVec.ofNat 64 m)).toNat = m := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hm

private theorem swb (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega

/-- `geu` with the byte on the LEFT (mirror of `Strtoull2.geu_true/false`). -/
theorem geuL_true (b : Byte) (m : Nat) (hm : (BitVec.ofNat 64 m).toNat = m) (h : b.toNat ≤ m) :
    evalCond .geu (BitVec.ofNat 64 m) (b.setWidth 64) = true := by
  have hult : (BitVec.ofNat 64 m).ult (b.setWidth 64) = false := by
    have e : (BitVec.ofNat 64 m).ult (b.setWidth 64)
        = decide ((BitVec.ofNat 64 m).toNat < (b.setWidth 64).toNat) := rfl
    rw [e, swb, hm]; exact decide_eq_false (by omega)
  simp only [evalCond, hult, Bool.not_false]

theorem geuL_false (b : Byte) (m : Nat) (hm : (BitVec.ofNat 64 m).toNat = m) (h : m < b.toNat) :
    evalCond .geu (BitVec.ofNat 64 m) (b.setWidth 64) = false := by
  have hult : (BitVec.ofNat 64 m).ult (b.setWidth 64) = true := by
    have e : (BitVec.ofNat 64 m).ult (b.setWidth 64)
        = decide ((BitVec.ofNat 64 m).toNat < (b.setWidth 64).toNat) := rfl
    rw [e, swb, hm, decide_eq_true_eq]; omega
  simp only [evalCond, hult]; rfl

/-- Signed `<` on indices = unsigned `<`, since indices are `< 2⁶³`. -/
theorem slt_true {x y : Word} (hx : x.toNat < 2^63) (hy : y.toNat < 2^63) (h : x.toNat < y.toNat) :
    evalCond .lt x y = true := by
  simp only [evalCond]
  rw [show x.slt y = decide (x.toInt < y.toInt) from rfl,
      BitVec.toInt_eq_toNat_of_lt (by omega : 2 * x.toNat < 2^64),
      BitVec.toInt_eq_toNat_of_lt (by omega : 2 * y.toNat < 2^64), decide_eq_true_eq]
  omega

theorem slt_false {x y : Word} (hx : x.toNat < 2^63) (hy : y.toNat < 2^63) (h : y.toNat ≤ x.toNat) :
    evalCond .lt x y = false := by
  simp only [evalCond]
  rw [show x.slt y = decide (x.toInt < y.toInt) from rfl,
      BitVec.toInt_eq_toNat_of_lt (by omega : 2 * x.toNat < 2^64),
      BitVec.toInt_eq_toNat_of_lt (by omega : 2 * y.toNat < 2^64), decide_eq_false_iff_not]
  omega

-- the constant byte codes used by pnib (in BitVec.ofNat form for the geu lemmas)
theorem c48 : (BitVec.ofNat 64 48).toNat = 48 := by decide
theorem c57 : (BitVec.ofNat 64 57).toNat = 57 := by decide
theorem c65 : (BitVec.ofNat 64 65).toNat = 65 := by decide
theorem c70 : (BitVec.ofNat 64 70).toNat = 70 := by decide

/-- The value `pnib` writes: mirrors `Hex0.nibble` with `255` for the `none` case. -/
def pnibR (b : Byte) : Word :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then (b.setWidth 64) - 48
  else if 65 ≤ b.toNat ∧ b.toNat ≤ 70 then (b.setWidth 64) - 55
  else 255

private theorem A_true {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h20 : st.rget 20 = 48)
    (h : 48 ≤ b.toNat) : evalCond .geu (st.rget 7) (st.rget 20) = true := by
  rw [h7, h20]; exact Strtoull2.geu_true c48 h
private theorem A_false {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h20 : st.rget 20 = 48)
    (h : b.toNat < 48) : evalCond .geu (st.rget 7) (st.rget 20) = false := by
  rw [h7, h20]; exact Strtoull2.geu_false c48 h
private theorem B_true {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h21 : st.rget 21 = 57)
    (h : b.toNat ≤ 57) : evalCond .geu (st.rget 21) (st.rget 7) = true := by
  rw [h7, h21]; exact geuL_true b 57 c57 h
private theorem B_false {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h21 : st.rget 21 = 57)
    (h : 57 < b.toNat) : evalCond .geu (st.rget 21) (st.rget 7) = false := by
  rw [h7, h21]; exact geuL_false b 57 c57 h
private theorem C_true {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h22 : st.rget 22 = 65)
    (h : 65 ≤ b.toNat) : evalCond .geu (st.rget 7) (st.rget 22) = true := by
  rw [h7, h22]; exact Strtoull2.geu_true c65 h
private theorem C_false {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h22 : st.rget 22 = 65)
    (h : b.toNat < 65) : evalCond .geu (st.rget 7) (st.rget 22) = false := by
  rw [h7, h22]; exact Strtoull2.geu_false c65 h
private theorem D_true {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h23 : st.rget 23 = 70)
    (h : b.toNat ≤ 70) : evalCond .geu (st.rget 23) (st.rget 7) = true := by
  rw [h7, h23]; exact geuL_true b 70 c70 h
private theorem D_false {st : St} {b : Byte} (h7 : st.rget 7 = b.setWidth 64) (h23 : st.rget 23 = 70)
    (h : 70 < b.toNat) : evalCond .geu (st.rget 23) (st.rget 7) = false := by
  rw [h7, h23]; exact geuL_false b 70 c70 h

private theorem bad_val {st : St} (dst : Reg) :
    st.rset dst (st.rget 0 + (BitVec.ofNat 12 255).signExtend 64) = st.rset dst 255 := by
  rw [rget_zero]; congr 1

/-- `pnib dst 7` computes `pnibR` of the byte in x7. -/
theorem pnib_correct (f : Nat) (st : St) (b : Byte) (dst : Reg)
    (h7 : st.rget 7 = b.setWidth 64)
    (h20 : st.rget 20 = 48) (h21 : st.rget 21 = 57) (h22 : st.rget 22 = 65)
    (h23 : st.rget 23 = 70) (h17 : st.rget 17 = 55) :
    exec (f + 6) (pnib dst 7) st = some (st.rset dst (pnibR b), .normal) := by
  have hd : st.rset dst (st.rget 7 - st.rget 20) = st.rset dst ((b.setWidth 64) - 48) := by rw [h7, h20]
  have hd2 : st.rset dst (st.rget 7 - st.rget 17) = st.rset dst ((b.setWidth 64) - 55) := by rw [h7, h17]
  unfold pnib
  rcases Nat.lt_or_ge b.toNat 48 with hlo | h48
  · -- < 48 : bad
    rw [show pnibR b = 255 from by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)],
        show f+6 = (f+5)+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (A_false h7 h20 hlo),
        show lit dst 255 = Stmt.addi dst 0 (BitVec.ofNat 12 255) from rfl, exec_addi, bad_val]
  · rcases Nat.lt_or_ge b.toNat 58 with h57 | h58
    · -- [48,57] : digit
      rw [show pnibR b = (b.setWidth 64) - 48 from by unfold pnibR; rw [if_pos ⟨h48, by omega⟩],
          show f+6 = (f+5)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (A_true h7 h20 h48),
          show f+5 = (f+4)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (B_true h7 h21 (by omega)),
          show f+4 = (f+3)+1 from rfl, exec_sub, hd]
    · rcases Nat.lt_or_ge b.toNat 65 with h64 | h65
      · -- [58,64] : bad
        rw [show pnibR b = 255 from by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)],
            show f+6 = (f+5)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (A_true h7 h20 h48),
            show f+5 = (f+4)+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (B_false h7 h21 (by omega)),
            show f+4 = (f+3)+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (C_false h7 h22 (by omega)),
            show lit dst 255 = Stmt.addi dst 0 (BitVec.ofNat 12 255) from rfl, exec_addi, bad_val]
      · rcases Nat.lt_or_ge b.toNat 71 with h70 | h71
        · -- [65,70] : A-F
          rw [show pnibR b = (b.setWidth 64) - 55 from by
                unfold pnibR; rw [if_neg (by omega), if_pos ⟨h65, by omega⟩],
              show f+6 = (f+5)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (A_true h7 h20 h48),
              show f+5 = (f+4)+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (B_false h7 h21 (by omega)),
              show f+4 = (f+3)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (C_true h7 h22 h65),
              show f+3 = (f+2)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (D_true h7 h23 (by omega)),
              show f+2 = (f+1)+1 from rfl, exec_sub, hd2]
        · -- > 70 : bad
          rw [show pnibR b = 255 from by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)],
              show f+6 = (f+5)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (A_true h7 h20 h48),
              show f+5 = (f+4)+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (B_false h7 h21 (by omega)),
              show f+4 = (f+3)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ (C_true h7 h22 (by omega)),
              show f+3 = (f+2)+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (D_false h7 h23 (by omega)),
              show lit dst 255 = Stmt.addi dst 0 (BitVec.ofNat 12 255) from rfl, exec_addi, bad_val]

end LowIR.Ctrl.Hex0
