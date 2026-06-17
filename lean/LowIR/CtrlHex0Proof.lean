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

/-! ### Memory borrows — separation discipline (Tree-Borrows residue; see docs/MEMORY-BORROWS.md).
    We keep only the well-formedness/disjointness consequence, not the TB operational model. -/

structure Slice where
  base : Word
  len  : Nat

/-- Addresses covered by a slice. -/
def Slice.has (s : Slice) (a : Word) : Prop := ∃ k, k < s.len ∧ a = s.base + BitVec.ofNat 64 k

inductive Perm | shared | uniq
deriving DecidableEq, Repr

structure Borrow where
  slice : Slice
  perm  : Perm

def Disjoint (s t : Slice) : Prop := ∀ a, s.has a → t.has a → False

/-- Well-formed borrow set: a unique borrow is disjoint from every other borrow. -/
def Wf (bs : List Borrow) : Prop :=
  ∀ b ∈ bs, ∀ b' ∈ bs, b ≠ b' → (b.perm = .uniq ∨ b'.perm = .uniq) → Disjoint b.slice b'.slice

theorem Disjoint.symm {s t : Slice} (h : Disjoint s t) : Disjoint t s :=
  fun a hat has => h a has hat

theorem Disjoint.not_right {s t : Slice} (h : Disjoint s t) {a : Word} (ha : s.has a) : ¬ t.has a :=
  fun ht => h a ha ht

theorem Disjoint.not_left {s t : Slice} (h : Disjoint s t) {a : Word} (ha : t.has a) : ¬ s.has a :=
  fun hs => h a hs ha

/-- A `Wf` borrow set makes a unique borrow disjoint from any other member. -/
theorem Wf.disjoint {bs : List Borrow} (h : Wf bs) {b b' : Borrow}
    (hb : b ∈ bs) (hb' : b' ∈ bs) (hne : b ≠ b') (hu : b'.perm = .uniq) :
    Disjoint b.slice b'.slice :=
  h b hb b' hb' hne (Or.inr hu)

/-- Writing a byte outside slice `s` preserves every read within `s`. -/
theorem storeByte_preserves {st : St} {s : Slice} {a a' : Word} {b : Byte}
    (hna : ¬ s.has a) (ha' : s.has a') : (st.storeByte a b).mem a' = st.mem a' := by
  show (if a' = a then b else st.mem a') = st.mem a'
  rw [if_neg]; intro he; exact hna (he ▸ ha')

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
      ∧ st'.rget 16 = st.rget 16 ∧ st'.rget 15 = gOf st.mem (i + 1) L p ∧ st'.mem = st.mem
      ∧ (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 15 → r ≠ 30 → st'.rget r = st.rget r) := by
  have ha : exec (f+7) (.addi 5 5 1) st = some (st.rset 5 (i + 1), .normal) := by
    rw [exec_addi, h5, show (1 : BitVec 12).signExtend 64 = (1:Word) from by decide]
  have hi1' : (i + 1).toNat < 2^63 := by bv_omega
  obtain ⟨st', hcg, hg, hpres, hmem⟩ := cgGuard_eff (f+1) (st.rset 5 (i + 1)) (i + 1) L p
    (by simp) (by simp [h11]) (by simp [h10]) (by simp [h24]) hi1' hL
  have hmem' : (st.rset 5 (i + 1)).mem = st.mem := by simp
  refine ⟨st', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show f+8 = (f+7)+1 from rfl, exec_seq_normal _ _ _ _ _ ha]; exact hcg
  · rw [hpres 5 (by decide) (by decide) (by decide)]; simp
  · rw [hpres 11 (by decide) (by decide) (by decide)]; simp [h11]
  · rw [hpres 10 (by decide) (by decide) (by decide)]; simp [h10]
  · rw [hpres 24 (by decide) (by decide) (by decide)]; simp [h24]
  · rw [hpres 16 (by decide) (by decide) (by decide)]; simp
  · rw [hg, hmem']
  · rw [hmem, hmem']
  · intro r h5r h8 h15 h30
    rw [hpres r h8 h15 h30, rget_rset_ne _ _ _ _ h5r]

theorem skip_loop (d : Nat) : ∀ (st : St) (i L p : Word),
    st.rget 5 = i → st.rget 11 = L → st.rget 10 = p → st.rget 24 = 10 → st.rget 16 = 1 →
    st.rget 15 = gOf st.mem i L p → L.toNat < 2^63 → i.toNat + d < 2^63 →
    (∀ j, j < d → gOf st.mem (i + BitVec.ofNat 64 j) L p = 1) →
    gOf st.mem (i + BitVec.ofNat 64 d) L p = 0 →
    ∃ st', exec (d + 9) (.while .geu 15 16 (.seq (.addi 5 5 1) cgGuard)) st = some (st', .normal)
      ∧ st'.rget 5 = i + BitVec.ofNat 64 d ∧ st'.rget 11 = L ∧ st'.rget 10 = p
      ∧ st'.rget 24 = 10 ∧ st'.rget 16 = 1 ∧ st'.mem = st.mem
      ∧ (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 15 → r ≠ 30 → st'.rget r = st.rget r) := by
  induction d with
  | zero =>
    intro st i L p h5 h11 h10 h24 h16 hg hL _ _ hz
    rw [cur_zero] at hz
    have hcond : evalCond .geu (st.rget 15) (st.rget 16) = false := by rw [hg, h16, hz]; decide
    refine ⟨st, ?_, ?_, h11, h10, h24, h16, rfl, fun r _ _ _ _ => rfl⟩
    · rw [show (0:Nat)+9 = 8+1 from rfl, exec_while_done _ _ _ _ _ _ hcond]
    · rw [cur_zero]; exact h5
  | succ d ih =>
    intro st i L p h5 h11 h10 h24 h16 hg hL hbd hdig hz
    have g0 : gOf st.mem i L p = 1 := by have := hdig 0 (by omega); rwa [cur_zero] at this
    have hcond : evalCond .geu (st.rget 15) (st.rget 16) = true := by rw [hg, h16, g0]; decide
    have hi1n : (i + 1).toNat = i.toNat + 1 := by bv_omega
    obtain ⟨st1, hbody, hs5, hs11, hs10, hs24, hs16, hsg, hsmem, hbpres⟩ :=
      skip_body (d+1) st i L p h5 h11 h10 h24 (by omega) hL
    have hgi1 : st1.rget 15 = gOf st1.mem (i+1) L p := by rw [hsg, hsmem]
    have hdig' : ∀ j, j < d → gOf st1.mem ((i+1) + BitVec.ofNat 64 j) L p = 1 := by
      intro j hj; rw [hsmem, ← cur_step]; exact hdig (j+1) (by omega)
    have hz' : gOf st1.mem ((i+1) + BitVec.ofNat 64 d) L p = 0 := by rw [hsmem, ← cur_step]; exact hz
    obtain ⟨st', he, hr5, hr11, hr10, hr24, hr16, hrmem, hrpres⟩ :=
      ih st1 (i+1) L p hs5 hs11 hs10 hs24 (hs16.trans h16) hgi1 hL (by rw [hi1n]; omega) hdig' hz'
    refine ⟨st', ?_, ?_, hr11, hr10, hr24, hr16, ?_, ?_⟩
    · rw [show (d+1)+9 = (d+9)+1 from rfl, exec_while_step _ _ _ _ _ _ _ hcond hbody]; exact he
    · rw [hr5, cur_step]
    · rw [hrmem, hsmem]
    · intro r h5r h8 h15 h30
      rw [hrpres r h5r h8 h15 h30, hbpres r h5r h8 h15 h30]

/-- The full comment-skip: advances `in_idx` by `d` to the first newline/EOF. -/
theorem skipComment_eff (d : Nat) (st : St) (i L p : Word)
    (h5 : st.rget 5 = i) (h11 : st.rget 11 = L) (h10 : st.rget 10 = p) (h24 : st.rget 24 = 10)
    (h16 : st.rget 16 = 1) (hi : i.toNat < 2^63) (hL : L.toNat < 2^63) (hd : i.toNat + d < 2^63)
    (hdig : ∀ j, j < d → gOf st.mem (i + BitVec.ofNat 64 j) L p = 1)
    (hz : gOf st.mem (i + BitVec.ofNat 64 d) L p = 0) :
    ∃ st', exec (d + 10) skipComment st = some (st', .normal)
      ∧ st'.rget 5 = i + BitVec.ofNat 64 d ∧ st'.rget 11 = L ∧ st'.rget 10 = p
      ∧ st'.rget 24 = 10 ∧ st'.rget 16 = 1 ∧ st'.mem = st.mem
      ∧ (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 15 → r ≠ 30 → st'.rget r = st.rget r) := by
  unfold skipComment
  obtain ⟨s1, hcg, hg, hpres, hmem⟩ := cgGuard_eff (d+3) st i L p h5 h11 h10 h24 hi hL
  have hs5 : s1.rget 5 = i := by rw [hpres 5 (by decide) (by decide) (by decide), h5]
  have hs11 : s1.rget 11 = L := by rw [hpres 11 (by decide) (by decide) (by decide), h11]
  have hs10 : s1.rget 10 = p := by rw [hpres 10 (by decide) (by decide) (by decide), h10]
  have hs24 : s1.rget 24 = 10 := by rw [hpres 24 (by decide) (by decide) (by decide), h24]
  have hs16 : s1.rget 16 = 1 := by rw [hpres 16 (by decide) (by decide) (by decide), h16]
  have hsg : s1.rget 15 = gOf s1.mem i L p := by rw [hg, hmem]
  obtain ⟨st', he, hr5, hr11, hr10, hr24, hr16, hrmem, hrpres⟩ :=
    skip_loop d s1 i L p hs5 hs11 hs10 hs24 hs16 hsg hL hd
      (by intro j hj; rw [hmem]; exact hdig j hj) (by rw [hmem]; exact hz)
  refine ⟨st', ?_, hr5, hr11, hr10, hr24, hr16, ?_, ?_⟩
  · rw [show d+10 = (d+9)+1 from rfl, exec_seq_normal _ _ _ _ _ hcg]; exact he
  · rw [hrmem, hmem]
  · intro r h5r h8 h15 h30
    rw [hrpres r h5r h8 h15 h30, hpres r h8 h15 h30]

/-! ### Character-equality dispatch lemmas (`.eq` against a byte). -/

theorem ceq_true {st : St} {b : Byte} {r : Reg} {k : Word} (n : Nat)
    (h7 : st.rget 7 = b.setWidth 64) (hr : st.rget r = k) (hk : k.toNat = n)
    (h : b.toNat = n) : evalCond .eq (st.rget 7) (st.rget r) = true := by
  rw [h7, hr]; simp only [evalCond, decide_eq_true_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega), hk]; exact h

theorem ceq_false {st : St} {b : Byte} {r : Reg} {k : Word} (n : Nat)
    (h7 : st.rget 7 = b.setWidth 64) (hr : st.rget r = k) (hk : k.toNat = n)
    (h : b.toNat ≠ n) : evalCond .eq (st.rget 7) (st.rget r) = false := by
  rw [h7, hr]; simp only [evalCond, decide_eq_false_iff_not]
  intro hc; apply h
  have := congrArg BitVec.toNat hc
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega), hk] at this
  exact this

@[simp] theorem rget_storeByte (s : St) (a : Word) (b : Byte) (r : Reg) :
    (s.storeByte a b).rget r = s.rget r := rfl

@[simp] theorem mem_storeByte_self (s : St) (a : Word) (b : Byte) :
    (s.storeByte a b).mem = fun x => if x = a then b else s.mem x := rfl

/-- Raw word-equality dispatch (compares two registers' contents). -/
theorem weq_true {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : x = y) : evalCond .eq (s.rget a) (s.rget b) = true := by
  rw [ha, hb]; simp only [evalCond, decide_eq_true_eq]; exact h
theorem weq_false {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : x ≠ y) : evalCond .eq (s.rget a) (s.rget b) = false := by
  rw [ha, hb]; simp only [evalCond, decide_eq_false_iff_not]; exact h

/-- Unsigned `≥` between two registers' word contents. -/
theorem geu_ww_true {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : y.toNat ≤ x.toNat) : evalCond .geu (s.rget a) (s.rget b) = true := by
  rw [ha, hb]; simp only [evalCond]
  rw [show x.ult y = decide (x.toNat < y.toNat) from rfl]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
theorem geu_ww_false {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : x.toNat < y.toNat) : evalCond .geu (s.rget a) (s.rget b) = false := by
  rw [ha, hb]; simp only [evalCond]
  rw [show x.ult y = decide (x.toNat < y.toNat) from rfl]
  simp only [Bool.not_eq_false', decide_eq_true_eq]; omega

/-! ### Register context: the constants + pointer registers held at every loop head. -/

structure Regs (st : St) (p L q cap : Word) : Prop where
  h10 : st.rget 10 = p
  h11 : st.rget 11 = L
  h12 : st.rget 12 = q
  h13 : st.rget 13 = cap
  h16 : st.rget 16 = 1
  h17 : st.rget 17 = 55
  h18 : st.rget 18 = 59
  h19 : st.rget 19 = 255
  h20 : st.rget 20 = 48
  h21 : st.rget 21 = 57
  h22 : st.rget 22 = 65
  h23 : st.rget 23 = 70
  h24 : st.rget 24 = 10
  h25 : st.rget 25 = 32
  h26 : st.rget 26 = 95
  h27 : st.rget 27 = 35

/-- The scratch registers `body` ever writes; `Regs` lives on the complement. -/
abbrev Pres (st' st : St) : Prop :=
  ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 14 → r ≠ 15 →
       r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → st'.rget r = st.rget r

/-- `Regs` is preserved by any state change that touches only the scratch registers. -/
theorem Regs.transfer {st st' : St} {p L q cap : Word} (hr : Regs st p L q cap)
    (h : Pres st' st) : Regs st' p L q cap where
  h10 := by rw [h 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h10]
  h11 := by rw [h 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h11]
  h12 := by rw [h 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h12]
  h13 := by rw [h 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h13]
  h16 := by rw [h 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h16]
  h17 := by rw [h 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h17]
  h18 := by rw [h 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h18]
  h19 := by rw [h 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h19]
  h20 := by rw [h 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h20]
  h21 := by rw [h 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h21]
  h22 := by rw [h 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h22]
  h23 := by rw [h 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h23]
  h24 := by rw [h 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h24]
  h25 := by rw [h 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h25]
  h26 := by rw [h 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h26]
  h27 := by rw [h 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr.h27]

/-! ### body_step, case 1: a space character (`\n`/` `/`_`) — skip, continue. -/

theorem body_space (st : St) (p L q cap i : Word) (c : Byte)
    (hr : Regs st p L q cap) (h5 : st.rget 5 = i) (hmemc : st.mem (p + i) = c)
    (hsp : c.toNat = 10 ∨ c.toNat = 32 ∨ c.toNat = 95) :
    ∃ fuel st', exec fuel body st = some (st', .normal)
      ∧ Regs st' p L q cap ∧ st'.rget 5 = i + 1 ∧ st'.rget 6 = st.rget 6
      ∧ st'.rget 14 = st.rget 14 ∧ st'.mem = st.mem := by
  obtain ⟨st1, hread0, hr5, hr7, hr30, hpres, hmem⟩ :=
    readAdv_eff 10 st 7 p i hr.h10 h5 (by decide) (by decide) (by decide) (by decide)
  have hread : exec 14 (readAdv 7) st = some (st1, .normal) := hread0
  have e7 : st1.rget 7 = c.setWidth 64 := by rw [hr7, hmemc]
  have e27 : st1.rget 27 = (35:Word) := by rw [hpres 27 (by decide) (by decide) (by decide), hr.h27]
  have e18 : st1.rget 18 = (59:Word) := by rw [hpres 18 (by decide) (by decide) (by decide), hr.h18]
  have e24 : st1.rget 24 = (10:Word) := by rw [hpres 24 (by decide) (by decide) (by decide), hr.h24]
  have e25 : st1.rget 25 = (32:Word) := by rw [hpres 25 (by decide) (by decide) (by decide), hr.h25]
  have e26 : st1.rget 26 = (95:Word) := by rw [hpres 26 (by decide) (by decide) (by decide), hr.h26]
  have hregs1 : Regs st1 p L q cap :=
    hr.transfer (fun r a5 _ a7 _ _ _ _ _ a30 _ => hpres r a5 a7 a30)
  refine ⟨15, st1, ?_, hregs1, ?_, ?_, ?_, ?_⟩
  · unfold body
    rw [show (15:Nat) = 14+1 from rfl, exec_seq_normal _ _ _ _ _ hread]
    rcases hsp with h10 | h32 | h95
    · rw [show (14:Nat)=13+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 35 e7 e27 (by decide) (by omega)),
          show (13:Nat)=12+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 59 e7 e18 (by decide) (by omega)),
          show (12:Nat)=11+1 from rfl,
          exec_ife_then _ _ _ _ _ _ _ (ceq_true 10 e7 e24 (by decide) h10)]
      rfl
    · rw [show (14:Nat)=13+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 35 e7 e27 (by decide) (by omega)),
          show (13:Nat)=12+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 59 e7 e18 (by decide) (by omega)),
          show (12:Nat)=11+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 10 e7 e24 (by decide) (by omega)),
          show (11:Nat)=10+1 from rfl,
          exec_ife_then _ _ _ _ _ _ _ (ceq_true 32 e7 e25 (by decide) h32)]
      rfl
    · rw [show (14:Nat)=13+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 35 e7 e27 (by decide) (by omega)),
          show (13:Nat)=12+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 59 e7 e18 (by decide) (by omega)),
          show (12:Nat)=11+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 10 e7 e24 (by decide) (by omega)),
          show (11:Nat)=10+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 32 e7 e25 (by decide) (by omega)),
          show (10:Nat)=9+1 from rfl,
          exec_ife_then _ _ _ _ _ _ _ (ceq_true 95 e7 e26 (by decide) h95)]
      rfl
  · rw [hr5]
  · rw [hpres 6 (by decide) (by decide) (by decide)]
  · rw [hpres 14 (by decide) (by decide) (by decide)]
  · exact hmem

/-! ### body_step, case 2: a comment character (`#`/`;`) — skip to newline/EOF. -/

theorem body_comment (st : St) (p L q cap i : Word) (c : Byte) (d : Nat)
    (hr : Regs st p L q cap) (h5 : st.rget 5 = i) (hmemc : st.mem (p + i) = c)
    (hcm : c.toNat = 35 ∨ c.toNat = 59)
    (hi1 : (i+1).toNat < 2^63) (hL : L.toNat < 2^63) (hd : (i+1).toNat + d < 2^63)
    (hdig : ∀ j, j < d → gOf st.mem ((i+1) + BitVec.ofNat 64 j) L p = 1)
    (hz : gOf st.mem ((i+1) + BitVec.ofNat 64 d) L p = 0) :
    ∃ fuel st', exec fuel body st = some (st', .normal)
      ∧ Regs st' p L q cap ∧ st'.rget 5 = (i+1) + BitVec.ofNat 64 d
      ∧ st'.rget 6 = st.rget 6 ∧ st'.rget 14 = st.rget 14 ∧ st'.mem = st.mem := by
  obtain ⟨st1, hread0, hr5, hr7, hr30, hreadpres, hmem⟩ :=
    readAdv_eff (d+12) st 7 p i hr.h10 h5 (by decide) (by decide) (by decide) (by decide)
  have hread : exec (d+16) (readAdv 7) st = some (st1, .normal) := hread0
  have e7 : st1.rget 7 = c.setWidth 64 := by rw [hr7, hmemc]
  have e27 : st1.rget 27 = (35:Word) := by rw [hreadpres 27 (by decide) (by decide) (by decide), hr.h27]
  have e18 : st1.rget 18 = (59:Word) := by rw [hreadpres 18 (by decide) (by decide) (by decide), hr.h18]
  have s5 : st1.rget 5 = i + 1 := hr5
  have s11 : st1.rget 11 = L := by rw [hreadpres 11 (by decide) (by decide) (by decide), hr.h11]
  have s10 : st1.rget 10 = p := by rw [hreadpres 10 (by decide) (by decide) (by decide), hr.h10]
  have s24 : st1.rget 24 = 10 := by rw [hreadpres 24 (by decide) (by decide) (by decide), hr.h24]
  have s16 : st1.rget 16 = 1 := by rw [hreadpres 16 (by decide) (by decide) (by decide), hr.h16]
  obtain ⟨st', hskip, hsk5, hsk11, hsk10, hsk24, hsk16, hskmem, hskpres⟩ :=
    skipComment_eff d st1 (i+1) L p s5 s11 s10 s24 s16 hi1 hL hd
      (by intro j hj; rw [hmem]; exact hdig j hj) (by rw [hmem]; exact hz)
  refine ⟨d+17, st', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold body
    rw [show d+17 = (d+16)+1 from rfl, exec_seq_normal _ _ _ _ _ hread]
    rcases hcm with h35 | h59
    · rw [show d+16 = (d+15)+1 from rfl,
          exec_ife_then _ _ _ _ _ _ _ (ceq_true 35 e7 e27 (by decide) h35)]
      exact exec_mono_le (by omega) hskip
    · rw [show d+16 = (d+15)+1 from rfl,
          exec_ife_else _ _ _ _ _ _ _ (ceq_false 35 e7 e27 (by decide) (by omega)),
          show d+15 = (d+14)+1 from rfl,
          exec_ife_then _ _ _ _ _ _ _ (ceq_true 59 e7 e18 (by decide) h59)]
      exact exec_mono_le (by omega) hskip
  · exact hr.transfer (fun r a5 _ a7 a8 _ a15 _ _ a30 _ => by
      rw [hskpres r a5 a8 a15 a30, hreadpres r a5 a7 a30])
  · exact hsk5
  · rw [hskpres 6 (by decide) (by decide) (by decide) (by decide), hreadpres 6 (by decide) (by decide) (by decide)]
  · rw [hskpres 14 (by decide) (by decide) (by decide) (by decide), hreadpres 14 (by decide) (by decide) (by decide)]
  · rw [hskmem, hmem]

/-! ### body_step, case 3: the hex-digit path (`hexPath`). -/

theorem exec_skip (f : Nat) (s : St) : exec (f+1) .skip s = some (s, .normal) := rfl

theorem exec_sb (f rb rv : Nat) (imm : BitVec 12) (s : St) :
    exec (f+1) (.sb rb rv imm) s
      = some (s.storeByte (s.rget rb + imm.signExtend 64) ((s.rget rv).setWidth 8), .normal) := by
  simp [exec]

/-- `err code` sets the status register and returns. -/
theorem exec_err (f : Nat) (s : St) (code : Nat) :
    exec (f+2) (err code) s = some (s.rset 14 ((BitVec.ofNat 12 code).signExtend 64), .ret) := by
  show exec (f+2) (.seq (lit 14 code) .ret) s = _
  have hlit : exec (f+1) (lit 14 code) s
      = some (s.rset 14 ((BitVec.ofNat 12 code).signExtend 64), .normal) := by
    show exec (f+1) (.addi 14 0 (BitVec.ofNat 12 code)) s = _
    rw [exec_addi, rget_zero, wzero_add]
  rw [show f+2 = (f+1)+1 from rfl, exec_seq_normal _ _ _ _ _ hlit, exec_ret]

/-- An `ife _ _ _ t .skip` whose condition is false: falls through unchanged. -/
theorem ife_skip_false (n : Nat) (hn : 2 ≤ n) (c : Cond) (a b : Reg) (t : Stmt) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = false) :
    exec n (.ife c a b t .skip) s = some (s, .normal) :=
  exec_mono_le hn (by rw [show (2:Nat) = 1+1 from rfl, exec_ife_else _ _ _ _ _ _ _ hc]; rfl)

/-- An `ife _ _ _ (err code) .skip` whose condition is true: returns with the status. -/
theorem ife_err_true (n : Nat) (hn : 4 ≤ n) (c : Cond) (a b : Reg) (code : Nat) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true) :
    exec n (.ife c a b (err code) .skip) s
      = some (s.rset 14 ((BitVec.ofNat 12 code).signExtend 64), .ret) :=
  exec_mono_le hn (by rw [show (4:Nat) = 3+1 from rfl, exec_ife_then _ _ _ _ _ _ _ hc]; exact exec_err 1 s code)

/-- One low-stop test character set (where a low nibble is expected → Split). -/
def lowStop (c : Byte) : Prop :=
  c.toNat = 10 ∨ c.toNat = 32 ∨ c.toNat = 95 ∨ c.toNat = 35 ∨ c.toNat = 59

/-- The full hex-digit path. Six mutually-exclusive outcomes, each carrying its
    defining condition so the loop invariant can align with `decodeS`. -/
theorem hexPath_eff (s : St) (p L q cap m : Word) (chi : Byte)
    (hr : Regs s p L q cap) (h5 : s.rget 5 = m) (h7 : s.rget 7 = chi.setWidth 64) :
    (pnibR chi = 255 ∧ ∃ st', exec 40 hexPath s = some (st', .ret)
        ∧ (st'.rget 14).toNat = 5 ∧ st'.rget 6 = s.rget 6 ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ L.toNat ≤ m.toNat ∧ ∃ st', exec 40 hexPath s = some (st', .ret)
        ∧ (st'.rget 14).toNat = 4 ∧ st'.rget 6 = s.rget 6 ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ m.toNat < L.toNat ∧ lowStop (s.mem (p+m))
        ∧ ∃ st', exec 40 hexPath s = some (st', .ret)
        ∧ (st'.rget 14).toNat = 3 ∧ st'.rget 6 = s.rget 6 ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ m.toNat < L.toNat ∧ ¬ lowStop (s.mem (p+m)) ∧ pnibR (s.mem (p+m)) = 255
        ∧ ∃ st', exec 40 hexPath s = some (st', .ret)
        ∧ (st'.rget 14).toNat = 5 ∧ st'.rget 6 = s.rget 6 ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ m.toNat < L.toNat ∧ ¬ lowStop (s.mem (p+m)) ∧ pnibR (s.mem (p+m)) ≠ 255
        ∧ cap.toNat ≤ (s.rget 6).toNat
        ∧ ∃ st', exec 40 hexPath s = some (st', .ret)
        ∧ (st'.rget 14).toNat = 2 ∧ st'.rget 6 = s.rget 6 ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ m.toNat < L.toNat ∧ ¬ lowStop (s.mem (p+m)) ∧ pnibR (s.mem (p+m)) ≠ 255
        ∧ (s.rget 6).toNat < cap.toNat
        ∧ ∃ st', exec 40 hexPath s = some (st', .normal)
        ∧ st'.rget 5 = m + 1 ∧ st'.rget 6 = s.rget 6 + 1 ∧ st'.rget 14 = s.rget 14
        ∧ Regs st' p L q cap
        ∧ st'.mem = (s.storeByte (q + s.rget 6)
              ((((pnibR chi) <<< 4) ||| pnibR (s.mem (p+m))).setWidth 8)).mem) := by
  -- s0 = state after `pnib 28 7`
  have hpnib28 : exec 6 (pnib 28 7) s = some (s.rset 28 (pnibR chi), .normal) :=
    pnib_correct 0 s chi 28 h7 hr.h20 hr.h21 hr.h22 hr.h23 hr.h17
  have h28_0 : (s.rset 28 (pnibR chi)).rget 28 = pnibR chi := rget_rset_eq _ _ _ (by decide)
  have h19_0 : (s.rset 28 (pnibR chi)).rget 19 = 255 := by
    rw [rget_rset_ne _ _ _ _ (by decide : (19:Reg) ≠ 28)]; exact hr.h19
  have h5_0 : (s.rset 28 (pnibR chi)).rget 5 = m := by
    rw [rget_rset_ne _ _ _ _ (by decide : (5:Reg) ≠ 28)]; exact h5
  have h11_0 : (s.rset 28 (pnibR chi)).rget 11 = L := by
    rw [rget_rset_ne _ _ _ _ (by decide : (11:Reg) ≠ 28)]; exact hr.h11
  have h10_0 : (s.rset 28 (pnibR chi)).rget 10 = p := by
    rw [rget_rset_ne _ _ _ _ (by decide : (10:Reg) ≠ 28)]; exact hr.h10
  by_cases hbad : pnibR chi = (255:Word)
  · -- ARM A: bad high nibble → Unknown (5)
    left
    have hcond : evalCond .eq ((s.rset 28 (pnibR chi)).rget 28) ((s.rset 28 (pnibR chi)).rget 19) = true :=
      weq_true h28_0 h19_0 hbad
    have herr : exec 38 (.ife .eq 28 19 (err 5) .skip) (s.rset 28 (pnibR chi))
        = some ((s.rset 28 (pnibR chi)).rset 14 ((BitVec.ofNat 12 5).signExtend 64), .ret) := by
      rw [show (38:Nat) = 37+1 from rfl, exec_ife_then _ _ _ _ _ _ _ hcond]
      exact exec_mono_le (by omega) (exec_err 0 (s.rset 28 (pnibR chi)) 5)
    refine ⟨hbad, (s.rset 28 (pnibR chi)).rset 14 ((BitVec.ofNat 12 5).signExtend 64), ?_, ?_, ?_, ?_⟩
    · simp only [hexPath, seqs, List.foldr_cons, List.foldr_nil]
      rw [show (40:Nat) = 39+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hpnib28),
          show (39:Nat) = 38+1 from rfl, exec_seq_ret _ _ _ _ _ herr]
    · rw [rget_rset_eq _ _ _ (by decide : (14:Reg) ≠ 0)]; decide
    · rw [rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 14), rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 28)]
    · simp
  · -- high nibble OK; the `ife eq 28 19` falls through (skip)
    have hcondA : evalCond .eq ((s.rset 28 (pnibR chi)).rget 28) ((s.rset 28 (pnibR chi)).rget 19) = false :=
      weq_false h28_0 h19_0 hbad
    have hA : exec 38 (.ife .eq 28 19 (err 5) .skip) (s.rset 28 (pnibR chi))
        = some (s.rset 28 (pnibR chi), .normal) := by
      rw [show (38:Nat) = 37+1 from rfl, exec_ife_else _ _ _ _ _ _ _ hcondA]; rfl
    by_cases htrail : L.toNat ≤ m.toNat
    · -- ARM B: no low char → Trailing (4)
      right; left
      have hcond : evalCond .geu ((s.rset 28 (pnibR chi)).rget 5) ((s.rset 28 (pnibR chi)).rget 11) = true :=
        geu_ww_true h5_0 h11_0 htrail
      have herr : exec 36 (.ife .geu 5 11 (err 4) .skip) (s.rset 28 (pnibR chi))
          = some ((s.rset 28 (pnibR chi)).rset 14 ((BitVec.ofNat 12 4).signExtend 64), .ret) := by
        rw [show (36:Nat) = 35+1 from rfl, exec_ife_then _ _ _ _ _ _ _ hcond]
        exact exec_mono_le (by omega) (exec_err 0 (s.rset 28 (pnibR chi)) 4)
      refine ⟨hbad, htrail, (s.rset 28 (pnibR chi)).rset 14 ((BitVec.ofNat 12 4).signExtend 64), ?_, ?_, ?_, ?_⟩
      · simp only [hexPath, seqs, List.foldr_cons, List.foldr_nil]
        rw [show (40:Nat) = 39+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hpnib28),
            show (39:Nat) = 38+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hA),
            show (38:Nat) = 37+1 from rfl, exec_seq_ret _ _ _ _ _ (exec_mono_le (by omega) herr)]
      · rw [rget_rset_eq _ _ _ (by decide : (14:Reg) ≠ 0)]; decide
      · rw [rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 14), rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 28)]
      · simp
    · -- low char exists; the `ife geu 5 11` falls through (skip), then readAdv loads it
      have htrail2 : m.toNat < L.toNat := by omega
      have hcondB : evalCond .geu ((s.rset 28 (pnibR chi)).rget 5) ((s.rset 28 (pnibR chi)).rget 11) = false :=
        geu_ww_false h5_0 h11_0 htrail2
      have hB : exec 36 (.ife .geu 5 11 (err 4) .skip) (s.rset 28 (pnibR chi))
          = some (s.rset 28 (pnibR chi), .normal) := by
        rw [show (36:Nat) = 35+1 from rfl, exec_ife_else _ _ _ _ _ _ _ hcondB]; rfl
      obtain ⟨sr, hread_r, hsr5, hsr7, hsr30, hsrpres, hsrmem⟩ :=
        readAdv_eff 0 (s.rset 28 (pnibR chi)) 7 p m h10_0 h5_0 (by decide) (by decide) (by decide) (by decide)
      -- low byte
      have hc2 : sr.rget 7 = (s.mem (p+m)).setWidth 64 := by rw [hsr7]; simp
      have hsrconst : ∀ r, r ≠ 5 → r ≠ 7 → r ≠ 30 → r ≠ 28 → sr.rget r = s.rget r := by
        intro r a b c d; rw [hsrpres r a b c, rget_rset_ne _ _ _ _ d]
      have e24 : sr.rget 24 = (10:Word) := by
        rw [hsrconst 24 (by decide) (by decide) (by decide) (by decide)]; exact hr.h24
      have e25 : sr.rget 25 = (32:Word) := by
        rw [hsrconst 25 (by decide) (by decide) (by decide) (by decide)]; exact hr.h25
      have e26 : sr.rget 26 = (95:Word) := by
        rw [hsrconst 26 (by decide) (by decide) (by decide) (by decide)]; exact hr.h26
      have e27 : sr.rget 27 = (35:Word) := by
        rw [hsrconst 27 (by decide) (by decide) (by decide) (by decide)]; exact hr.h27
      have e18 : sr.rget 18 = (59:Word) := by
        rw [hsrconst 18 (by decide) (by decide) (by decide) (by decide)]; exact hr.h18
      have e19 : sr.rget 19 = (255:Word) := by
        rw [hsrconst 19 (by decide) (by decide) (by decide) (by decide)]; exact hr.h19
      have e20 : sr.rget 20 = (48:Word) := by
        rw [hsrconst 20 (by decide) (by decide) (by decide) (by decide)]; exact hr.h20
      have e21 : sr.rget 21 = (57:Word) := by
        rw [hsrconst 21 (by decide) (by decide) (by decide) (by decide)]; exact hr.h21
      have e22 : sr.rget 22 = (65:Word) := by
        rw [hsrconst 22 (by decide) (by decide) (by decide) (by decide)]; exact hr.h22
      have e23 : sr.rget 23 = (70:Word) := by
        rw [hsrconst 23 (by decide) (by decide) (by decide) (by decide)]; exact hr.h23
      have e17 : sr.rget 17 = (55:Word) := by
        rw [hsrconst 17 (by decide) (by decide) (by decide) (by decide)]; exact hr.h17
      have e13 : sr.rget 13 = cap := by
        rw [hsrconst 13 (by decide) (by decide) (by decide) (by decide)]; exact hr.h13
      have e12 : sr.rget 12 = q := by
        rw [hsrconst 12 (by decide) (by decide) (by decide) (by decide)]; exact hr.h12
      have e6 : sr.rget 6 = s.rget 6 := hsrconst 6 (by decide) (by decide) (by decide) (by decide)
      have hsrmem' : sr.mem = s.mem := by rw [hsrmem]; simp
      have hregs_sr : Regs sr p L q cap :=
        hr.transfer (fun r a5 _ a7 _ _ _ a28 _ a30 _ => hsrconst r a5 a7 a30 a28)
      -- peel the prefix: pnib, ife(bad-high) skip, ife(trailing) skip, readAdv
      have hpeel4 : exec 40 hexPath s = exec 36
          (.seq (.ife .eq 7 24 (err 3) .skip) (.seq (.ife .eq 7 25 (err 3) .skip)
            (.seq (.ife .eq 7 26 (err 3) .skip) (.seq (.ife .eq 7 27 (err 3) .skip)
            (.seq (.ife .eq 7 18 (err 3) .skip) (.seq (pnib 29 7)
            (.seq (.ife .eq 29 19 (err 5) .skip) (.seq (.ife .geu 6 13 (err 2) .skip)
            (.seq (.slli 31 28 4) (.seq (.orr 31 31 29) (.seq (.add 30 12 6)
            (.seq (.sb 30 31 0) (.seq (.addi 6 6 1) .skip))))))))))))) sr := by
        simp only [hexPath, seqs, List.foldr_cons, List.foldr_nil]
        rw [show (40:Nat) = 39+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hpnib28),
            show (39:Nat) = 38+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hA),
            show (38:Nat) = 37+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hB),
            show (37:Nat) = 36+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hread_r)]
      by_cases hls : lowStop (s.mem (p+m))
      · -- ARM C: low-stop char → Split (3)
        right; right; left
        refine ⟨hbad, htrail2, hls, sr.rset 14 ((BitVec.ofNat 12 3).signExtend 64), ?_, ?_, ?_, ?_⟩
        · rw [hpeel4]
          rcases hls with h | h | h | h | h
          · rw [show (36:Nat)=35+1 from rfl,
                exec_seq_ret _ _ _ _ _ (ife_err_true 35 (by omega) .eq 7 24 3 sr (ceq_true 10 hc2 e24 (by decide) h))]
          · rw [show (36:Nat)=35+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 35 (by omega) .eq 7 24 (err 3) sr (ceq_false 10 hc2 e24 (by decide) (by omega))),
                show (35:Nat)=34+1 from rfl,
                exec_seq_ret _ _ _ _ _ (ife_err_true 34 (by omega) .eq 7 25 3 sr (ceq_true 32 hc2 e25 (by decide) h))]
          · rw [show (36:Nat)=35+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 35 (by omega) .eq 7 24 (err 3) sr (ceq_false 10 hc2 e24 (by decide) (by omega))),
                show (35:Nat)=34+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 34 (by omega) .eq 7 25 (err 3) sr (ceq_false 32 hc2 e25 (by decide) (by omega))),
                show (34:Nat)=33+1 from rfl,
                exec_seq_ret _ _ _ _ _ (ife_err_true 33 (by omega) .eq 7 26 3 sr (ceq_true 95 hc2 e26 (by decide) h))]
          · rw [show (36:Nat)=35+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 35 (by omega) .eq 7 24 (err 3) sr (ceq_false 10 hc2 e24 (by decide) (by omega))),
                show (35:Nat)=34+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 34 (by omega) .eq 7 25 (err 3) sr (ceq_false 32 hc2 e25 (by decide) (by omega))),
                show (34:Nat)=33+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 33 (by omega) .eq 7 26 (err 3) sr (ceq_false 95 hc2 e26 (by decide) (by omega))),
                show (33:Nat)=32+1 from rfl,
                exec_seq_ret _ _ _ _ _ (ife_err_true 32 (by omega) .eq 7 27 3 sr (ceq_true 35 hc2 e27 (by decide) h))]
          · rw [show (36:Nat)=35+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 35 (by omega) .eq 7 24 (err 3) sr (ceq_false 10 hc2 e24 (by decide) (by omega))),
                show (35:Nat)=34+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 34 (by omega) .eq 7 25 (err 3) sr (ceq_false 32 hc2 e25 (by decide) (by omega))),
                show (34:Nat)=33+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 33 (by omega) .eq 7 26 (err 3) sr (ceq_false 95 hc2 e26 (by decide) (by omega))),
                show (33:Nat)=32+1 from rfl,
                exec_seq_normal _ _ _ _ _ (ife_skip_false 32 (by omega) .eq 7 27 (err 3) sr (ceq_false 35 hc2 e27 (by decide) (by omega))),
                show (32:Nat)=31+1 from rfl,
                exec_seq_ret _ _ _ _ _ (ife_err_true 31 (by omega) .eq 7 18 3 sr (ceq_true 59 hc2 e18 (by decide) h))]
        · rw [rget_rset_eq _ _ _ (by decide : (14:Reg) ≠ 0)]; decide
        · rw [rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 14)]; exact e6
        · simp [hsrmem']
      · -- not a low-stop char
        have hn10 : (s.mem (p+m)).toNat ≠ 10 := fun h => hls (Or.inl h)
        have hn32 : (s.mem (p+m)).toNat ≠ 32 := fun h => hls (Or.inr (Or.inl h))
        have hn95 : (s.mem (p+m)).toNat ≠ 95 := fun h => hls (Or.inr (Or.inr (Or.inl h)))
        have hn35 : (s.mem (p+m)).toNat ≠ 35 := fun h => hls (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have hn59 : (s.mem (p+m)).toNat ≠ 59 := fun h => hls (Or.inr (Or.inr (Or.inr (Or.inr h))))
        -- peel the 5 low-stop ifes (all false), reaching `pnib 29 7`
        have hpeel9 : exec 40 hexPath s = exec 31
            (.seq (pnib 29 7) (.seq (.ife .eq 29 19 (err 5) .skip)
            (.seq (.ife .geu 6 13 (err 2) .skip) (.seq (.slli 31 28 4) (.seq (.orr 31 31 29)
            (.seq (.add 30 12 6) (.seq (.sb 30 31 0) (.seq (.addi 6 6 1) .skip)))))))) sr := by
          rw [hpeel4,
              show (36:Nat)=35+1 from rfl,
              exec_seq_normal _ _ _ _ _ (ife_skip_false 35 (by omega) .eq 7 24 (err 3) sr (ceq_false 10 hc2 e24 (by decide) hn10)),
              show (35:Nat)=34+1 from rfl,
              exec_seq_normal _ _ _ _ _ (ife_skip_false 34 (by omega) .eq 7 25 (err 3) sr (ceq_false 32 hc2 e25 (by decide) hn32)),
              show (34:Nat)=33+1 from rfl,
              exec_seq_normal _ _ _ _ _ (ife_skip_false 33 (by omega) .eq 7 26 (err 3) sr (ceq_false 95 hc2 e26 (by decide) hn95)),
              show (33:Nat)=32+1 from rfl,
              exec_seq_normal _ _ _ _ _ (ife_skip_false 32 (by omega) .eq 7 27 (err 3) sr (ceq_false 35 hc2 e27 (by decide) hn35)),
              show (32:Nat)=31+1 from rfl,
              exec_seq_normal _ _ _ _ _ (ife_skip_false 31 (by omega) .eq 7 18 (err 3) sr (ceq_false 59 hc2 e18 (by decide) hn59))]
        -- s9 = state after `pnib 29 7`
        have hpnib29 : exec 6 (pnib 29 7) sr = some (sr.rset 29 (pnibR (s.mem (p+m))), .normal) :=
          pnib_correct 0 sr (s.mem (p+m)) 29 hc2 e20 e21 e22 e23 e17
        have h29_9 : (sr.rset 29 (pnibR (s.mem (p+m)))).rget 29 = pnibR (s.mem (p+m)) :=
          rget_rset_eq _ _ _ (by decide)
        have h19_9 : (sr.rset 29 (pnibR (s.mem (p+m)))).rget 19 = (255:Word) := by
          rw [rget_rset_ne _ _ _ _ (by decide : (19:Reg) ≠ 29)]; exact e19
        have h6_9 : (sr.rset 29 (pnibR (s.mem (p+m)))).rget 6 = s.rget 6 := by
          rw [rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 29)]; exact e6
        have h13_9 : (sr.rset 29 (pnibR (s.mem (p+m)))).rget 13 = cap := by
          rw [rget_rset_ne _ _ _ _ (by decide : (13:Reg) ≠ 29)]; exact e13
        have hpeel10 : exec 40 hexPath s = exec 30
            (.seq (.ife .eq 29 19 (err 5) .skip)
            (.seq (.ife .geu 6 13 (err 2) .skip) (.seq (.slli 31 28 4) (.seq (.orr 31 31 29)
            (.seq (.add 30 12 6) (.seq (.sb 30 31 0) (.seq (.addi 6 6 1) .skip))))))) (sr.rset 29 (pnibR (s.mem (p+m)))) := by
          rw [hpeel9, show (31:Nat)=30+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) hpnib29)]
        by_cases hbad2 : pnibR (s.mem (p+m)) = (255:Word)
        · -- ARM D: bad low nibble → Unknown (5)
          right; right; right; left
          refine ⟨hbad, htrail2, hls, hbad2,
            (sr.rset 29 (pnibR (s.mem (p+m)))).rset 14 ((BitVec.ofNat 12 5).signExtend 64), ?_, ?_, ?_, ?_⟩
          · rw [hpeel10, show (30:Nat)=29+1 from rfl,
                exec_seq_ret _ _ _ _ _ (ife_err_true 29 (by omega) .eq 29 19 5 _ (weq_true h29_9 h19_9 hbad2))]
          · rw [rget_rset_eq _ _ _ (by decide : (14:Reg) ≠ 0)]; decide
          · rw [rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 14)]; exact h6_9
          · simp [hsrmem']
        · by_cases hfull : cap.toNat ≤ (s.rget 6).toNat
          · -- ARM E: output full → OutputShort (2)
            right; right; right; right; left
            refine ⟨hbad, htrail2, hls, hbad2, hfull,
              (sr.rset 29 (pnibR (s.mem (p+m)))).rset 14 ((BitVec.ofNat 12 2).signExtend 64), ?_, ?_, ?_, ?_⟩
            · rw [hpeel10, show (30:Nat)=29+1 from rfl,
                  exec_seq_normal _ _ _ _ _ (ife_skip_false 29 (by omega) .eq 29 19 (err 5) _ (weq_false h29_9 h19_9 hbad2)),
                  show (29:Nat)=28+1 from rfl,
                  exec_seq_ret _ _ _ _ _ (ife_err_true 28 (by omega) .geu 6 13 2 _ (geu_ww_true h6_9 h13_9 hfull))]
            · rw [rget_rset_eq _ _ _ (by decide : (14:Reg) ≠ 0)]; decide
            · rw [rget_rset_ne _ _ _ _ (by decide : (6:Reg) ≠ 14)]; exact h6_9
            · simp [hsrmem']
          · -- ARM F: write the byte, continue
            right; right; right; right; right
            have hfull2 : (s.rget 6).toNat < cap.toNat := by omega
            have h28_sr : sr.rget 28 = pnibR chi := by
              rw [hsrpres 28 (by decide) (by decide) (by decide)]; exact h28_0
            -- reg facts on s9 = sr.rset 29 (pnibR c2)
            have h28_9 : (sr.rset 29 (pnibR (s.mem (p+m)))).rget 28 = pnibR chi := by
              rw [rget_rset_ne _ _ _ _ (by decide : (28:Reg) ≠ 29)]; exact h28_sr
            have h12_9 : (sr.rset 29 (pnibR (s.mem (p+m)))).rget 12 = q := by
              rw [rget_rset_ne _ _ _ _ (by decide : (12:Reg) ≠ 29)]; exact e12
            -- final state (using simplified values)
            refine ⟨hbad, htrail2, hls, hbad2, hfull2,
              (((((sr.rset 29 (pnibR (s.mem (p+m)))).rset 31 (pnibR chi <<< 4)).rset 31
                  ((pnibR chi <<< 4) ||| pnibR (s.mem (p+m)))).rset 30 (q + s.rget 6)).storeByte
                  (q + s.rget 6) (((pnibR chi <<< 4) ||| pnibR (s.mem (p+m))).setWidth 8)).rset 6
                  (s.rget 6 + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- exec: peel ife(29) skip, ife(geu613) skip, then the five ops + trailing skip
              rw [hpeel10, show (30:Nat)=29+1 from rfl,
                  exec_seq_normal _ _ _ _ _ (ife_skip_false 29 (by omega) .eq 29 19 (err 5) _ (weq_false h29_9 h19_9 hbad2)),
                  show (29:Nat)=28+1 from rfl,
                  exec_seq_normal _ _ _ _ _ (ife_skip_false 28 (by omega) .geu 6 13 (err 2) _ (geu_ww_false h6_9 h13_9 hfull2)),
                  show (28:Nat)=27+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) (exec_slli 0 31 28 4 _)),
                  show (27:Nat)=26+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) (exec_orr 0 31 31 29 _)),
                  show (26:Nat)=25+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) (exec_add 0 30 12 6 _)),
                  show (25:Nat)=24+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) (exec_sb 0 30 31 0 _)),
                  show (24:Nat)=23+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_mono_le (by omega) (exec_addi 0 6 6 1 _)),
                  show (23:Nat)=22+1 from rfl, exec_skip]
              -- reconcile the (unsimplified) execution state with the witness
              simp [h28_9, h12_9, h6_9,
                show (BitVec.ofNat 12 0).signExtend 64 = (0:Word) from by decide,
                show (BitVec.ofNat 12 1).signExtend 64 = (1:Word) from by decide]
            · -- x5 = m + 1
              simp; exact hsr5
            · -- x6 = s.rget 6 + 1
              rw [rget_rset_eq _ _ _ (by decide : (6:Reg) ≠ 0)]
            · -- x14 unchanged
              have h14 : sr.rget 14 = s.rget 14 := hsrconst 14 (by decide) (by decide) (by decide) (by decide)
              simp [h14]
            · -- Regs of the final state
              apply hregs_sr.transfer
              intro r a5 a6 a7 a8 a14 a15 a28 a29 a30 a31
              rw [rget_rset_ne _ _ _ _ a6, rget_storeByte, rget_rset_ne _ _ _ _ a30,
                  rget_rset_ne _ _ _ _ a31, rget_rset_ne _ _ _ _ a31, rget_rset_ne _ _ _ _ a29]
            · -- memory: the written byte
              simp only [rset_mem, mem_storeByte_self, hsrmem']

/-- body_step, case 3 assembled on `body`: read the high char, dispatch falls through
    to `hexPath`. Same six outcomes as `hexPath_eff`, phrased on the loop-head state. -/
theorem body_hex (st : St) (p L q cap i : Word) (c : Byte)
    (hr : Regs st p L q cap) (h5 : st.rget 5 = i) (hmemc : st.mem (p+i) = c)
    (hns : c.toNat ≠ 10 ∧ c.toNat ≠ 32 ∧ c.toNat ≠ 95 ∧ c.toNat ≠ 35 ∧ c.toNat ≠ 59) :
    (pnibR c = 255 ∧ ∃ fuel st', exec fuel body st = some (st', .ret)
        ∧ (st'.rget 14).toNat = 5 ∧ st'.rget 6 = st.rget 6 ∧ st'.mem = st.mem)
  ∨ (pnibR c ≠ 255 ∧ L.toNat ≤ (i+1).toNat ∧ ∃ fuel st', exec fuel body st = some (st', .ret)
        ∧ (st'.rget 14).toNat = 4 ∧ st'.rget 6 = st.rget 6 ∧ st'.mem = st.mem)
  ∨ (pnibR c ≠ 255 ∧ (i+1).toNat < L.toNat ∧ lowStop (st.mem (p+(i+1)))
        ∧ ∃ fuel st', exec fuel body st = some (st', .ret)
        ∧ (st'.rget 14).toNat = 3 ∧ st'.rget 6 = st.rget 6 ∧ st'.mem = st.mem)
  ∨ (pnibR c ≠ 255 ∧ (i+1).toNat < L.toNat ∧ ¬ lowStop (st.mem (p+(i+1))) ∧ pnibR (st.mem (p+(i+1))) = 255
        ∧ ∃ fuel st', exec fuel body st = some (st', .ret)
        ∧ (st'.rget 14).toNat = 5 ∧ st'.rget 6 = st.rget 6 ∧ st'.mem = st.mem)
  ∨ (pnibR c ≠ 255 ∧ (i+1).toNat < L.toNat ∧ ¬ lowStop (st.mem (p+(i+1))) ∧ pnibR (st.mem (p+(i+1))) ≠ 255
        ∧ cap.toNat ≤ (st.rget 6).toNat
        ∧ ∃ fuel st', exec fuel body st = some (st', .ret)
        ∧ (st'.rget 14).toNat = 2 ∧ st'.rget 6 = st.rget 6 ∧ st'.mem = st.mem)
  ∨ (pnibR c ≠ 255 ∧ (i+1).toNat < L.toNat ∧ ¬ lowStop (st.mem (p+(i+1))) ∧ pnibR (st.mem (p+(i+1))) ≠ 255
        ∧ (st.rget 6).toNat < cap.toNat
        ∧ ∃ fuel st', exec fuel body st = some (st', .normal)
        ∧ st'.rget 5 = (i+1) + 1 ∧ st'.rget 6 = st.rget 6 + 1 ∧ st'.rget 14 = st.rget 14
        ∧ Regs st' p L q cap
        ∧ st'.mem = (st.storeByte (q + st.rget 6)
              ((((pnibR c) <<< 4) ||| pnibR (st.mem (p+(i+1)))).setWidth 8)).mem) := by
  obtain ⟨st1, hread0, hr5, hr7, hr30, hreadpres, hmem⟩ :=
    readAdv_eff 41 st 7 p i hr.h10 h5 (by decide) (by decide) (by decide) (by decide)
  have e7 : st1.rget 7 = c.setWidth 64 := by rw [hr7, hmemc]
  have e27 : st1.rget 27 = (35:Word) := by rw [hreadpres 27 (by decide) (by decide) (by decide), hr.h27]
  have e18 : st1.rget 18 = (59:Word) := by rw [hreadpres 18 (by decide) (by decide) (by decide), hr.h18]
  have e24 : st1.rget 24 = (10:Word) := by rw [hreadpres 24 (by decide) (by decide) (by decide), hr.h24]
  have e25 : st1.rget 25 = (32:Word) := by rw [hreadpres 25 (by decide) (by decide) (by decide), hr.h25]
  have e26 : st1.rget 26 = (95:Word) := by rw [hreadpres 26 (by decide) (by decide) (by decide), hr.h26]
  have hregs1 : Regs st1 p L q cap :=
    hr.transfer (fun r a5 _ a7 _ _ _ _ _ a30 _ => hreadpres r a5 a7 a30)
  have hst16 : st1.rget 6 = st.rget 6 := hreadpres 6 (by decide) (by decide) (by decide)
  have hlift : ∀ (st' : St) (oc : Outcome), exec 40 hexPath st1 = some (st', oc) →
      exec 46 body st = some (st', oc) := by
    intro st' oc h
    have hread' : exec 45 (readAdv 7) st = some (st1, .normal) := hread0
    unfold body
    rw [show (46:Nat)=45+1 from rfl, exec_seq_normal _ _ _ _ _ hread',
        show (45:Nat)=44+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (ceq_false 35 e7 e27 (by decide) hns.2.2.2.1),
        show (44:Nat)=43+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (ceq_false 59 e7 e18 (by decide) hns.2.2.2.2),
        show (43:Nat)=42+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (ceq_false 10 e7 e24 (by decide) hns.1),
        show (42:Nat)=41+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (ceq_false 32 e7 e25 (by decide) hns.2.1),
        show (41:Nat)=40+1 from rfl, exec_ife_else _ _ _ _ _ _ _ (ceq_false 95 e7 e26 (by decide) hns.2.2.1)]
    exact h
  rcases hexPath_eff st1 p L q cap (i+1) c hregs1 hr5 e7 with
      ⟨hc, st', he, h14, h6, hm⟩
    | ⟨hc, ht, st', he, h14, h6, hm⟩
    | ⟨hc, ht, hls, st', he, h14, h6, hm⟩
    | ⟨hc, ht, hls, hb2, st', he, h14, h6, hm⟩
    | ⟨hc, ht, hls, hb2, hf, st', he, h14, h6, hm⟩
    | ⟨hc, ht, hls, hb2, hf, st', he, h5', h6', h14', hregs', hm'⟩
  · exact Or.inl ⟨hc, _, _, hlift _ _ he, h14, by rw [h6, hst16], by rw [hm, hmem]⟩
  · exact Or.inr (Or.inl ⟨hc, ht, _, _, hlift _ _ he, h14, by rw [h6, hst16], by rw [hm, hmem]⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨hc, ht, ?_, _, _, hlift _ _ he, h14, by rw [h6, hst16], by rw [hm, hmem]⟩))
    rw [← hmem]; exact hls
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, ht, ?_, ?_, _, _, hlift _ _ he, h14, by rw [h6, hst16], by rw [hm, hmem]⟩)))
    · rw [← hmem]; exact hls
    · rw [← hmem]; exact hb2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, ht, ?_, ?_, ?_, _, _, hlift _ _ he, h14, by rw [h6, hst16], by rw [hm, hmem]⟩))))
    · rw [← hmem]; exact hls
    · rw [← hmem]; exact hb2
    · rw [← hst16]; exact hf
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, ht, ?_, ?_, ?_, _, _, hlift _ _ he, h5', by rw [h6', hst16], ?_, ?_, ?_⟩))))
    · rw [← hmem]; exact hls
    · rw [← hmem]; exact hb2
    · rw [← hst16]; exact hf
    · rw [h14', hreadpres 14 (by decide) (by decide) (by decide)]
    · exact hregs'
    · rw [hm', hst16]; simp only [mem_storeByte_self, hmem]

/-! ### Bridge lemmas: the IL nibble register values vs the spec `Hex0.nibble` (item B prep). -/

/-- `pnib` writes `255` exactly when the spec `nibble` is `none`. -/
theorem pnibR_eq_255_iff (c : Byte) : pnibR c = 255 ↔ Hex0.nibble c.toNat = none := by
  unfold pnibR Hex0.nibble
  by_cases h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · rw [if_pos h1, if_pos h1]; simp only [reduceCtorEq, iff_false]; intro hc; bv_omega
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
    · rw [if_pos h2, if_pos h2]; simp only [reduceCtorEq, iff_false]; intro hc; bv_omega
    · rw [if_neg h2, if_neg h2]; simp

/-- When `pnib` does not write `255`, its value is exactly the spec nibble value. -/
theorem pnibR_nibble (c : Byte) (h : pnibR c ≠ 255) :
    Hex0.nibble c.toNat = some (pnibR c).toNat := by
  unfold pnibR Hex0.nibble
  unfold pnibR at h
  have hsw : (c.setWidth 64).toNat = c.toNat := by
    rw [BitVec.toNat_setWidth]; have := c.isLt; omega
  by_cases h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · obtain ⟨h1a, h1b⟩ := h1
    rw [if_pos ⟨h1a, h1b⟩, if_pos ⟨h1a, h1b⟩]; rw [if_pos ⟨h1a, h1b⟩] at h; congr 1
    rw [BitVec.toNat_sub, hsw, show ((48 : BitVec 64)).toNat = 48 from by decide]; omega
  · rw [if_neg h1, if_neg h1]; rw [if_neg h1] at h
    by_cases h2 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
    · obtain ⟨h2a, h2b⟩ := h2
      rw [if_pos ⟨h2a, h2b⟩, if_pos ⟨h2a, h2b⟩]; rw [if_pos ⟨h2a, h2b⟩] at h; congr 1
      rw [BitVec.toNat_sub, hsw, show ((55 : BitVec 64)).toNat = 55 from by decide]; omega
    · rw [if_neg h2, if_neg h2]; rw [if_neg h2] at h; exact absurd rfl h

/-- A valid nibble value is `< 16`. -/
theorem pnibR_lt_16 (c : Byte) (h : pnibR c ≠ 255) : (pnibR c).toNat < 16 := by
  unfold pnibR at h ⊢
  by_cases h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · rw [if_pos h1] at h ⊢; bv_omega
  · rw [if_neg h1] at h ⊢
    by_cases h2 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
    · rw [if_pos h2] at h ⊢; bv_omega
    · rw [if_neg h2] at h; exact absurd rfl h

/-- The emitted byte `(hi<<4) | lo` equals `hi*16 + lo` as a number (disjoint nibbles). -/
theorem hexbyte_val (c c2 : Byte) (hc : pnibR c ≠ 255) (hc2 : pnibR c2 ≠ 255) :
    ((((pnibR c) <<< 4) ||| pnibR c2).setWidth 8).toNat
      = (pnibR c).toNat * 16 + (pnibR c2).toNat := by
  have h1 := pnibR_lt_16 c hc
  have h2 := pnibR_lt_16 c2 hc2
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : (pnibR c).toNat * 2^4 < 2^64), Nat.mul_comm,
      ← Nat.two_pow_add_eq_or_of_lt (by omega : (pnibR c2).toNat < 2^4)]
  omega

/-- `lowStop` (the IL test) matches the spec `Hex0.isLowStop`. -/
theorem lowStop_iff (c : Byte) : lowStop c ↔ Hex0.isLowStop c.toNat = true := by
  unfold lowStop Hex0.isLowStop Hex0.isSpace Hex0.isComment
    Hex0.c_nl Hex0.c_sp Hex0.c_us Hex0.c_hash Hex0.c_semi
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

end LowIR.Ctrl.Hex0
