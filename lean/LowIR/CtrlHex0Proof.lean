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

/-! ### readAdv: load mem[p+i] into dst and advance the cursor. -/

/-- `readAdv dst` loads the byte at `p+i` into `dst`, sets `x30 = p+i`, and bumps `x5` to `i+1`. -/
theorem readAdv_eff (f : Nat) (st : St) (dst : Reg) (p i : Word)
    (h10 : st.rget 10 = p) (h5 : st.rget 5 = i)
    (hd0 : dst ≠ 0) (hd5 : dst ≠ 5) (hd10 : dst ≠ 10) (hd30 : dst ≠ 30) :
    ∃ st', exec (f + 4) (readAdv dst) st = some (st', .normal)
      ∧ st'.rget 5 = i + 1
      ∧ st'.rget dst = (st.mem (p + i)).setWidth 64
      ∧ st'.rget 30 = p + i
      ∧ (∀ r, r ≠ 5 → r ≠ dst → r ≠ 30 → st'.rget r = st.rget r)
      ∧ st'.mem = st.mem := by
  have ha : exec (f+3) (.add 30 10 5) st = some (st.rset 30 (p + i), .normal) := by
    rw [exec_add, h10, h5]
  have hb : exec (f+2) (.lbu dst 30 0) (st.rset 30 (p + i))
      = some ((st.rset 30 (p + i)).rset dst ((st.mem (p + i)).setWidth 64), .normal) := by
    rw [exec_lbu]
    have : (st.rset 30 (p + i)).rget 30 = p + i := by simp
    simp only [this, zero_signExtend, wadd_zero, St.loadByte]
    congr 2
  have hc : exec (f+1) (.addi 5 5 1) ((st.rset 30 (p + i)).rset dst ((st.mem (p + i)).setWidth 64))
      = some (((st.rset 30 (p + i)).rset dst ((st.mem (p + i)).setWidth 64)).rset 5 (i + 1), .normal) := by
    rw [exec_addi]
    have h5' : ((st.rset 30 (p + i)).rset dst ((st.mem (p + i)).setWidth 64)).rget 5 = i := by
      rw [rget_rset_ne _ _ _ _ hd5.symm, rget_rset_ne _ _ _ _ (by decide : (5:Reg) ≠ 30), h5]
    rw [h5', show (1 : BitVec 12).signExtend 64 = (1:Word) from by decide]
  refine ⟨((st.rset 30 (p + i)).rset dst ((st.mem (p + i)).setWidth 64)).rset 5 (i + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold readAdv
    simp only [seqs, List.foldr_cons, List.foldr_nil]
    rw [show f+4 = (f+3)+1 from rfl, exec_seq_normal _ _ _ _ _ ha,
        show f+3 = (f+2)+1 from rfl, exec_seq_normal _ _ _ _ _ hb,
        show f+2 = (f+1)+1 from rfl, exec_seq_normal _ _ _ _ _ hc]
    rfl
  · simp
  · rw [rget_rset_ne _ _ _ _ hd5, rget_rset_eq _ _ _ hd0]
  · rw [rget_rset_ne _ _ _ _ (by decide : (30:Reg) ≠ 5), rget_rset_ne _ _ _ _ (Ne.symm hd30),
        rget_rset_eq _ _ _ (by decide : (30:Reg) ≠ 0)]
  · intro r hr5 hrdst hr30
    rw [rget_rset_ne _ _ _ _ hr5, rget_rset_ne _ _ _ _ hrdst, rget_rset_ne _ _ _ _ hr30]
  · simp

/-! ### cgGuard: computes the loop guard `x15`. -/

def nlB : Byte := 10

private theorem mem_eq_nl_iff (b : Byte) : (b.setWidth 64 = (10:Word)) ↔ (b = nlB) := by
  rw [nlB]
  constructor
  · intro h
    have ht : b.toNat = 10 := by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
      simpa using this
    apply BitVec.eq_of_toNat_eq; rw [ht]; decide
  · intro h; rw [h]; decide

/-- The guard value: `1` iff `in_idx < in_len` and the byte there is not a newline. -/
def gOf (mem : Word → Byte) (i L p : Word) : Word :=
  if i.toNat < L.toNat then (if mem (p + i) = nlB then 0 else 1) else 0

theorem cgGuard_eff (f : Nat) (st : St) (i L p : Word)
    (h5 : st.rget 5 = i) (h11 : st.rget 11 = L) (h10 : st.rget 10 = p) (h24 : st.rget 24 = 10)
    (hi : i.toNat < 2^63) (hL : L.toNat < 2^63) :
    ∃ st', exec (f + 6) cgGuard st = some (st', .normal)
      ∧ st'.rget 15 = gOf st.mem i L p
      ∧ (∀ r, r ≠ 8 → r ≠ 15 → r ≠ 30 → st'.rget r = st.rget r)
      ∧ st'.mem = st.mem := by
  have haddr : st.rget 10 + st.rget 5 = p + i := by rw [h10, h5]
  unfold cgGuard
  by_cases hil : i.toNat < L.toNat
  · -- i < L: load and test the byte
    have hlt : evalCond .lt (st.rget 5) (st.rget 11) = true := by rw [h5, h11]; exact slt_true hi hL hil
    have ha : exec (f+4) (.add 30 10 5) st = some (st.rset 30 (p + i), .normal) := by
      rw [exec_add, haddr]
    have hl : exec (f+3) (.lbu 8 30 0) (st.rset 30 (p + i))
        = some ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64), .normal) := by
      rw [exec_lbu]; simp [zero_signExtend, wadd_zero]
    have h24' : ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rget 24 = 10 := by
      simp [h24]
    have h8' : ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rget 8
        = (st.mem (p + i)).setWidth 64 := by simp
    have hz0 : ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rget 0
        + (BitVec.ofNat 12 0).signExtend 64 = (0:Word) := by rw [rget_zero]; decide
    have hz1 : ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rget 0
        + (BitVec.ofNat 12 1).signExtend 64 = (1:Word) := by rw [rget_zero]; decide
    by_cases hnl : st.mem (p + i) = nlB
    · -- newline → g = 0
      have hinner : exec (f+2) (.ife .eq 8 24 (lit 15 0) (lit 15 1))
          ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64))
          = some (((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rset 15 0, .normal) := by
        rw [show f+2 = (f+1)+1 from rfl,
            exec_ife_then _ _ _ _ _ _ _ (by rw [h8', h24']; simp only [evalCond]; rw [decide_eq_true_eq, mem_eq_nl_iff]; exact hnl),
            show lit 15 0 = Stmt.addi 15 0 (BitVec.ofNat 12 0) from rfl, exec_addi, hz0]
      refine ⟨((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rset 15 0, ?_, ?_, ?_, ?_⟩
      · rw [show f+6 = (f+5)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ hlt]
        simp only [seqs, List.foldr_cons, List.foldr_nil]
        rw [show f+5 = (f+4)+1 from rfl, exec_seq_normal _ _ _ _ _ ha,
            show f+4 = (f+3)+1 from rfl, exec_seq_normal _ _ _ _ _ hl,
            show f+3 = (f+2)+1 from rfl, exec_seq_normal _ _ _ _ _ hinner]
        rfl
      · rw [gOf, if_pos hil, if_pos hnl]; simp
      · intro r hr8 hr15 hr30
        rw [rget_rset_ne _ _ _ _ hr15, rget_rset_ne _ _ _ _ hr8, rget_rset_ne _ _ _ _ hr30]
      · simp
    · -- not newline → g = 1
      have hinner : exec (f+2) (.ife .eq 8 24 (lit 15 0) (lit 15 1))
          ((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64))
          = some (((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rset 15 1, .normal) := by
        rw [show f+2 = (f+1)+1 from rfl,
            exec_ife_else _ _ _ _ _ _ _ (by
              rw [h8', h24']; simp only [evalCond]; rw [decide_eq_false_iff_not, mem_eq_nl_iff]; exact hnl),
            show lit 15 1 = Stmt.addi 15 0 (BitVec.ofNat 12 1) from rfl, exec_addi, hz1]
      refine ⟨((st.rset 30 (p + i)).rset 8 ((st.mem (p + i)).setWidth 64)).rset 15 1, ?_, ?_, ?_, ?_⟩
      · rw [show f+6 = (f+5)+1 from rfl, exec_ife_then _ _ _ _ _ _ _ hlt]
        simp only [seqs, List.foldr_cons, List.foldr_nil]
        rw [show f+5 = (f+4)+1 from rfl, exec_seq_normal _ _ _ _ _ ha,
            show f+4 = (f+3)+1 from rfl, exec_seq_normal _ _ _ _ _ hl,
            show f+3 = (f+2)+1 from rfl, exec_seq_normal _ _ _ _ _ hinner]
        rfl
      · rw [gOf, if_pos hil, if_neg hnl]; simp
      · intro r hr8 hr15 hr30
        rw [rget_rset_ne _ _ _ _ hr15, rget_rset_ne _ _ _ _ hr8, rget_rset_ne _ _ _ _ hr30]
      · simp
  · -- i >= L: g = 0 directly
    refine ⟨st.rset 15 0, ?_, ?_, ?_, ?_⟩
    · rw [show f+6 = (f+5)+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (by rw [h5, h11]; exact slt_false hi hL (by omega)),
          show lit 15 0 = Stmt.addi 15 0 (BitVec.ofNat 12 0) from rfl, exec_addi,
          show st.rget 0 + (BitVec.ofNat 12 0).signExtend 64 = (0:Word) from by rw [rget_zero]; decide]
    · rw [gOf, if_neg hil]; simp
    · intro r hr8 hr15 hr30; rw [rget_rset_ne _ _ _ _ hr15]
    · simp

/-! ### The comment-skip loop body and loop. -/

theorem skip_body (f : Nat) (st : St) (i L p : Word)
    (h5 : st.rget 5 = i) (h11 : st.rget 11 = L) (h10 : st.rget 10 = p) (h24 : st.rget 24 = 10)
    (hi1 : i.toNat + 1 < 2^63) (hL : L.toNat < 2^63) :
    ∃ st', exec (f + 8) (.seq (.addi 5 5 1) cgGuard) st = some (st', .normal)
      ∧ st'.rget 5 = i + 1 ∧ st'.rget 11 = L ∧ st'.rget 10 = p ∧ st'.rget 24 = 10
      ∧ st'.rget 16 = st.rget 16 ∧ st'.rget 15 = gOf st.mem (i + 1) L p ∧ st'.mem = st.mem := by
  have ha : exec (f+7) (.addi 5 5 1) st = some (st.rset 5 (i + 1), .normal) := by
    rw [exec_addi, h5, show (1 : BitVec 12).signExtend 64 = (1:Word) from by decide]
  have hi1' : (i + 1).toNat < 2^63 := by bv_omega
  obtain ⟨st', hcg, hg, hpres, hmem⟩ := cgGuard_eff (f+1) (st.rset 5 (i + 1)) (i + 1) L p
    (by simp) (by simp [h11]) (by simp [h10]) (by simp [h24]) hi1' hL
  have hmem' : (st.rset 5 (i + 1)).mem = st.mem := by simp
  refine ⟨st', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show f+8 = (f+7)+1 from rfl, exec_seq_normal _ _ _ _ _ ha]; exact hcg
  · rw [hpres 5 (by decide) (by decide) (by decide)]; simp
  · rw [hpres 11 (by decide) (by decide) (by decide)]; simp [h11]
  · rw [hpres 10 (by decide) (by decide) (by decide)]; simp [h10]
  · rw [hpres 24 (by decide) (by decide) (by decide)]; simp [h24]
  · rw [hpres 16 (by decide) (by decide) (by decide)]; simp
  · rw [hg, hmem']
  · rw [hmem, hmem']

theorem skip_loop (d : Nat) : ∀ (st : St) (i L p : Word),
    st.rget 5 = i → st.rget 11 = L → st.rget 10 = p → st.rget 24 = 10 → st.rget 16 = 1 →
    st.rget 15 = gOf st.mem i L p → L.toNat < 2^63 → i.toNat + d < 2^63 →
    (∀ j, j < d → gOf st.mem (i + BitVec.ofNat 64 j) L p = 1) →
    gOf st.mem (i + BitVec.ofNat 64 d) L p = 0 →
    ∃ st', exec (d + 9) (.while .geu 15 16 (.seq (.addi 5 5 1) cgGuard)) st = some (st', .normal)
      ∧ st'.rget 5 = i + BitVec.ofNat 64 d ∧ st'.rget 11 = L ∧ st'.rget 10 = p
      ∧ st'.rget 24 = 10 ∧ st'.rget 16 = 1 ∧ st'.mem = st.mem := by
  induction d with
  | zero =>
    intro st i L p h5 h11 h10 h24 h16 hg hL _ _ hz
    rw [cur_zero] at hz
    have hcond : evalCond .geu (st.rget 15) (st.rget 16) = false := by rw [hg, h16, hz]; decide
    refine ⟨st, ?_, ?_, h11, h10, h24, h16, rfl⟩
    · rw [show (0:Nat)+9 = 8+1 from rfl, exec_while_done _ _ _ _ _ _ hcond]
    · rw [cur_zero]; exact h5
  | succ d ih =>
    intro st i L p h5 h11 h10 h24 h16 hg hL hbd hdig hz
    have g0 : gOf st.mem i L p = 1 := by have := hdig 0 (by omega); rwa [cur_zero] at this
    have hcond : evalCond .geu (st.rget 15) (st.rget 16) = true := by rw [hg, h16, g0]; decide
    have hi1n : (i + 1).toNat = i.toNat + 1 := by bv_omega
    obtain ⟨st1, hbody, hs5, hs11, hs10, hs24, hs16, hsg, hsmem⟩ :=
      skip_body (d+1) st i L p h5 h11 h10 h24 (by omega) hL
    have hgi1 : st1.rget 15 = gOf st1.mem (i+1) L p := by rw [hsg, hsmem]
    have hdig' : ∀ j, j < d → gOf st1.mem ((i+1) + BitVec.ofNat 64 j) L p = 1 := by
      intro j hj; rw [hsmem, ← cur_step]; exact hdig (j+1) (by omega)
    have hz' : gOf st1.mem ((i+1) + BitVec.ofNat 64 d) L p = 0 := by rw [hsmem, ← cur_step]; exact hz
    obtain ⟨st', he, hr5, hr11, hr10, hr24, hr16, hrmem⟩ :=
      ih st1 (i+1) L p hs5 hs11 hs10 hs24 (hs16.trans h16) hgi1 hL (by rw [hi1n]; omega) hdig' hz'
    refine ⟨st', ?_, ?_, hr11, hr10, hr24, hr16, ?_⟩
    · rw [show (d+1)+9 = (d+9)+1 from rfl, exec_while_step _ _ _ _ _ _ _ hcond hbody]; exact he
    · rw [hr5, cur_step]
    · rw [hrmem, hsmem]

/-- The full comment-skip: advances `in_idx` by `d` to the first newline/EOF. -/
theorem skipComment_eff (d : Nat) (st : St) (i L p : Word)
    (h5 : st.rget 5 = i) (h11 : st.rget 11 = L) (h10 : st.rget 10 = p) (h24 : st.rget 24 = 10)
    (h16 : st.rget 16 = 1) (hi : i.toNat < 2^63) (hL : L.toNat < 2^63) (hd : i.toNat + d < 2^63)
    (hdig : ∀ j, j < d → gOf st.mem (i + BitVec.ofNat 64 j) L p = 1)
    (hz : gOf st.mem (i + BitVec.ofNat 64 d) L p = 0) :
    ∃ st', exec (d + 10) skipComment st = some (st', .normal)
      ∧ st'.rget 5 = i + BitVec.ofNat 64 d ∧ st'.rget 11 = L ∧ st'.rget 10 = p
      ∧ st'.rget 24 = 10 ∧ st'.rget 16 = 1 ∧ st'.mem = st.mem := by
  unfold skipComment
  obtain ⟨s1, hcg, hg, hpres, hmem⟩ := cgGuard_eff (d+3) st i L p h5 h11 h10 h24 hi hL
  have hs5 : s1.rget 5 = i := by rw [hpres 5 (by decide) (by decide) (by decide), h5]
  have hs11 : s1.rget 11 = L := by rw [hpres 11 (by decide) (by decide) (by decide), h11]
  have hs10 : s1.rget 10 = p := by rw [hpres 10 (by decide) (by decide) (by decide), h10]
  have hs24 : s1.rget 24 = 10 := by rw [hpres 24 (by decide) (by decide) (by decide), h24]
  have hs16 : s1.rget 16 = 1 := by rw [hpres 16 (by decide) (by decide) (by decide), h16]
  have hsg : s1.rget 15 = gOf s1.mem i L p := by rw [hg, hmem]
  obtain ⟨st', he, hr5, hr11, hr10, hr24, hr16, hrmem⟩ :=
    skip_loop d s1 i L p hs5 hs11 hs10 hs24 hs16 hsg hL hd
      (by intro j hj; rw [hmem]; exact hdig j hj) (by rw [hmem]; exact hz)
  refine ⟨st', ?_, hr5, hr11, hr10, hr24, hr16, ?_⟩
  · rw [show d+10 = (d+9)+1 from rfl, exec_seq_normal _ _ _ _ _ hcg]; exact he
  · rw [hrmem, hmem]

end LowIR.Ctrl.Hex0
