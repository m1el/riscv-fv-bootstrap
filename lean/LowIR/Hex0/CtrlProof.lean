/-
  Functional correctness of hex0 on the control-flow IL — FOUNDATION.

  This is the largest of the LowIR proofs (hex0's two-state decoder vs `Hex0.coreSpec`).
  Built in pieces; this file starts with the reusable foundation: unsigned condition
  lemmas in both operand orders, and `pnib_correct` (the nibble parser ≡ `Hex0.nibble`).
  The comment-skip loop and the main-loop invariant follow.
-/
import LowIR.Hex0.Ctrl
import LowIR.Strlen.Ctrl
import LowIR.Strtoull.V1Proof
import LowIR.Strtoull.V2Proof
import Spec.Hex0.Spec

set_option linter.unusedSimpArgs false

namespace LowIR.Ctrl.Hex0

open LowIR.Ctrl
open Rv64i (Word Byte)

/-! ### Memory borrows — separation discipline (Tree-Borrows residue; see docs/MEMORY-BORROWS.md).
    We keep only the well-formedness/disjointness consequence, not the TB operational model. -/

structure Slice where
  base : Word
  len  : Nat
deriving DecidableEq

/-- Addresses covered by a slice. -/
def Slice.has (s : Slice) (a : Word) : Prop := ∃ k, k < s.len ∧ a = s.base + BitVec.ofNat 64 k

inductive Perm | shared | uniq
deriving DecidableEq, Repr

structure Borrow where
  slice : Slice
  perm  : Perm
deriving DecidableEq

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

theorem exec_lit (f : Nat) (r v : Nat) (st : St) :
    exec (f+1) (lit r v) st = some (st.rset r ((BitVec.ofNat 12 v).signExtend 64), .normal) := by
  show exec (f+1) (Stmt.addi r 0 (BitVec.ofNat 12 v)) st = _
  rw [exec_addi, rget_zero, wzero_add]

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

/-! ### Output-region readback + index arithmetic (item B). -/

theorem ofNat_succ (n : Nat) : BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n+1) := by bv_omega

/-- The bytes in `[base, base+n)` read back as a `List Nat` (matches `outBytes`). -/
def regionBytes (mem : Word → Byte) (base : Word) (n : Nat) : List Nat :=
  (List.range n).map (fun k => (mem (base + BitVec.ofNat 64 k)).toNat)

theorem regionBytes_snoc (mem : Word → Byte) (base : Word) (n : Nat) :
    regionBytes mem base (n+1)
      = regionBytes mem base n ++ [(mem (base + BitVec.ofNat 64 n)).toNat] := by
  unfold regionBytes; rw [List.range_succ, List.map_append]; rfl

/-- Writing the byte at index `n` leaves the readback of `[base, base+n)` unchanged. -/
theorem regionBytes_store_self (s : St) (base : Word) (n : Nat) (b : Byte) (hn : n < 2^64) :
    regionBytes (s.storeByte (base + BitVec.ofNat 64 n) b).mem base n = regionBytes s.mem base n := by
  unfold regionBytes
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  show (if base + BitVec.ofNat 64 k = base + BitVec.ofNat 64 n then b else s.mem _).toNat = _
  rw [if_neg (by bv_omega)]

/-! ### Spec-side `decodeS` unfolding (item B's per-iteration case rewrites). -/

theorem decodeS_high_comment (c : Nat) (rest : List Nat) (h : Hex0.isComment c = true) :
    Hex0.decodeS .High (c :: rest) = Hex0.decodeS .High (_root_.Hex0.skipComment rest) := by
  rw [Hex0.decodeS]; simp [h]

theorem decodeS_high_space (c : Nat) (rest : List Nat)
    (hc : Hex0.isComment c = false) (h : Hex0.isSpace c = true) :
    Hex0.decodeS .High (c :: rest) = Hex0.decodeS .High rest := by
  rw [Hex0.decodeS]; simp [hc, h]

theorem decodeS_high_badhi (c : Nat) (rest : List Nat)
    (hc : Hex0.isComment c = false) (hs : Hex0.isSpace c = false) (hn : Hex0.nibble c = none) :
    Hex0.decodeS .High (c :: rest) = ([], .Unknown) := by
  rw [Hex0.decodeS]; simp [hc, hs, hn]

theorem decodeS_high_goodhi (c : Nat) (rest : List Nat) (hi : Nat)
    (hc : Hex0.isComment c = false) (hs : Hex0.isSpace c = false) (hn : Hex0.nibble c = some hi) :
    Hex0.decodeS .High (c :: rest) = Hex0.decodeS (.Low hi) rest := by
  rw [Hex0.decodeS]; simp [hc, hs, hn]

theorem decodeS_high_nil : Hex0.decodeS .High [] = ([], .Ok) := by rw [Hex0.decodeS]

theorem decodeS_low_nil (hi : Nat) : Hex0.decodeS (.Low hi) [] = ([], .Trailing) := by
  rw [Hex0.decodeS]

theorem decodeS_low_split (hi c2 : Nat) (rest : List Nat) (h : Hex0.isLowStop c2 = true) :
    Hex0.decodeS (.Low hi) (c2 :: rest) = ([], .Split) := by
  rw [Hex0.decodeS]; simp [h]

theorem decodeS_low_badlo (hi c2 : Nat) (rest : List Nat)
    (h : Hex0.isLowStop c2 = false) (hn : Hex0.nibble c2 = none) :
    Hex0.decodeS (.Low hi) (c2 :: rest) = ([], .Unknown) := by
  rw [Hex0.decodeS]; simp [h, hn]

theorem decodeS_low_goodlo (hi c2 lo : Nat) (rest : List Nat)
    (h : Hex0.isLowStop c2 = false) (hn : Hex0.nibble c2 = some lo) :
    Hex0.decodeS (.Low hi) (c2 :: rest)
      = ((hi * 16 + lo) :: (Hex0.decodeS .High rest).1, (Hex0.decodeS .High rest).2) := by
  rw [Hex0.decodeS]; simp [h, hn]

/-- `skipComment` over an all-non-newline list drops everything (EOF comment). -/
theorem skipComment_nonl (l : List Nat) (h : ∀ x ∈ l, x ≠ 10) : _root_.Hex0.skipComment l = [] := by
  induction l with
  | nil => rfl
  | cons c l' ih =>
    rw [_root_.Hex0.skipComment]
    have hc : c ≠ 10 := h c (by simp)
    simp only [Hex0.c_nl, beq_iff_eq, if_neg hc]
    exact ih (fun x hx => h x (by simp [hx]))

/-- `skipComment` over a non-newline run then a `\n` drops through the `\n`. -/
theorem skipComment_run (pre rest : List Nat) (h : ∀ x ∈ pre, x ≠ 10) :
    _root_.Hex0.skipComment (pre ++ 10 :: rest) = rest := by
  induction pre with
  | nil => simp [_root_.Hex0.skipComment, Hex0.c_nl]
  | cons c pre' ih =>
    have hc : c ≠ 10 := h c (by simp)
    simp only [List.cons_append, _root_.Hex0.skipComment, Hex0.c_nl, beq_iff_eq, if_neg hc]
    exact ih (fun x hx => h x (by simp [hx]))

/-! ### The bounded (per-byte-capacity) run + comment-scan length (item B). -/

/-- What the IL produces from the suffix `bytes` (with terminal status `dstatus`) starting at output
    length `|produced|`, checking capacity `capN` per byte. -/
def boundedRun (produced bytes : List Nat) (dstatus : Hex0.Status) (capN : Nat) : Nat × List Nat × Nat :=
  if produced.length + bytes.length ≤ capN then
    (Hex0.statusCode dstatus, produced ++ bytes, produced.length + bytes.length)
  else
    (2, produced ++ bytes.take (capN - produced.length), capN)

theorem boundedRun_cons (produced : List Nat) (byte : Nat) (more : List Nat) (dstatus : Hex0.Status)
    (capN : Nat) (h : produced.length < capN) :
    boundedRun produced (byte :: more) dstatus capN
      = boundedRun (produced ++ [byte]) more dstatus capN := by
  unfold boundedRun
  have e1 : produced ++ (byte :: more) = (produced ++ [byte]) ++ more := by simp
  by_cases hc : produced.length + (byte :: more).length ≤ capN
  · have hc2 : (produced ++ [byte]).length + more.length ≤ capN := by simp at hc ⊢; omega
    rw [if_pos hc, if_pos hc2, e1]; congr 2; simp; omega
  · have hc2 : ¬ (produced ++ [byte]).length + more.length ≤ capN := by simp at hc ⊢; omega
    rw [if_neg hc, if_neg hc2]; congr 1
    have hk : capN - produced.length = (capN - (produced.length+1)) + 1 := by omega
    have ht : (byte::more).take (capN - produced.length) = byte :: more.take (capN - (produced.length+1)) := by
      rw [hk, List.take_succ_cons]
    rw [ht]; simp

/-- At the top level (empty prefix), the per-byte-capacity run agrees with `coreSpec`. -/
theorem boundedRun_nil_coreSpec (inp : List Nat) (capN : Nat) :
    boundedRun [] (Hex0.decodeS .High inp).1 (Hex0.decodeS .High inp).2 capN = Hex0.coreSpec inp capN := by
  rw [Hex0.coreSpec, Hex0.decode]
  rcases hd : Hex0.decodeS .High inp with ⟨bs, st⟩
  simp only [boundedRun, hd, List.length_nil, List.nil_append, Nat.zero_add, Nat.sub_zero]
  by_cases h : bs.length ≤ capN
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

/-- Number of characters before the first `\n` (or the whole list if none). -/
def commentSkip : List Nat → Nat
  | [] => 0
  | c :: rest => if c == 10 then 0 else commentSkip rest + 1

theorem commentSkip_le (l : List Nat) : commentSkip l ≤ l.length := by
  induction l with
  | nil => simp [commentSkip]
  | cons c rest ih => unfold commentSkip; split <;> simp <;> omega

theorem commentSkip_get (l : List Nat) (h : commentSkip l < l.length) : l[commentSkip l]! = 10 := by
  induction l with
  | nil => simp [commentSkip] at h
  | cons c rest ih =>
    unfold commentSkip at h ⊢
    by_cases hc : c == 10
    · rw [if_pos hc]; simp only [List.getElem!_cons_zero]; simpa using hc
    · rw [if_neg hc] at h ⊢
      simp only [List.length_cons] at h
      simp only [List.getElem!_cons_succ]; exact ih (by omega)

theorem commentSkip_run_ne (l : List Nat) (j : Nat) (hj : j < commentSkip l) : l[j]! ≠ 10 := by
  induction l generalizing j with
  | nil => simp [commentSkip] at hj
  | cons c rest ih =>
    unfold commentSkip at hj
    by_cases hc : c == 10
    · rw [if_pos hc] at hj; omega
    · rw [if_neg hc] at hj
      cases j with
      | zero => simp only [List.getElem!_cons_zero]; simpa using hc
      | succ j => simp only [List.getElem!_cons_succ]; exact ih j (by omega)

/-- Comment reconciliation: the IL stops *at* the `\n` (`commentSkip` chars in); `decodeS`'s own
    `High` recursion then treats that `\n` as a space, so `drop (commentSkip)` ≡ `skipComment`. -/
theorem decodeS_comment_reconcile (l : List Nat) :
    Hex0.decodeS .High (l.drop (commentSkip l)) = Hex0.decodeS .High (_root_.Hex0.skipComment l) := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    unfold commentSkip _root_.Hex0.skipComment
    simp only [Hex0.c_nl]
    by_cases hc : c == 10
    · rw [if_pos hc, if_pos hc]
      simp only [List.drop_zero]
      have h10 : c = 10 := by simpa using hc
      rw [Hex0.decodeS]
      simp [Hex0.isComment, Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Hex0.c_hash, Hex0.c_semi, h10]
    · rw [if_neg hc, if_neg hc, List.drop_succ_cons]; exact ih

/-! ### The main-loop invariant (item B). -/

theorem main_loop (inp : List Nat) (p q : Word) (capN : Nat)
    (hinp : ∀ x ∈ inp, x < 256) (hlen : inp.length < 2^63) (hcap : capN < 2^63)
    (hdisj : Disjoint ⟨p, inp.length⟩ ⟨q, capN⟩) :
    ∀ (n idx olen : Nat) (st : St) (produced : List Nat),
      n = inp.length - idx →
      Regs st p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) →
      st.rget 5 = BitVec.ofNat 64 idx → st.rget 6 = BitVec.ofNat 64 olen → st.rget 14 = 0 →
      idx ≤ inp.length → olen ≤ capN → olen = produced.length →
      (∀ k : Word, k.toNat < inp.length → st.mem (p + k) = BitVec.ofNat 8 (inp[k.toNat]!)) →
      regionBytes st.mem q olen = produced →
      ∃ fuel st' oc, exec fuel (.while .lt 5 11 body) st = some (st', oc)
        ∧ (oc = .normal ∨ oc = .ret)
        ∧ (st'.rget 14).toNat
            = (boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1 (Hex0.decodeS .High (inp.drop idx)).2 capN).1
        ∧ (st'.rget 6).toNat
            = (boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1 (Hex0.decodeS .High (inp.drop idx)).2 capN).2.2
        ∧ regionBytes st'.mem q (st'.rget 6).toNat
            = (boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1 (Hex0.decodeS .High (inp.drop idx)).2 capN).2.1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro idx olen st produced hn hregs h5 h6 h14 hidx holen holenp hbridge hout
  by_cases hlt : idx < inp.length
  · -- inductive step: one body iteration
    have hkidx : (BitVec.ofNat 64 idx).toNat = idx := tn idx (by omega)
    have htno : (BitVec.ofNat 64 olen).toNat = olen := tn olen (by omega)
    have hvmem : inp[idx]! = inp[idx] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hv : inp[idx]! < 256 := by rw [hvmem]; exact hinp _ (List.getElem_mem hlt)
    have hbr_idx : st.mem (p + BitVec.ofNat 64 idx) = BitVec.ofNat 8 (inp[idx]!) := by
      have hb := hbridge (BitVec.ofNat 64 idx) (by rw [hkidx]; exact hlt)
      rwa [hkidx] at hb
    have hcv : (st.mem (p + BitVec.ofNat 64 idx)).toNat = inp[idx]! := by
      rw [hbr_idx, BitVec.toNat_ofNat]; omega
    have hcond : evalCond .lt (st.rget 5) (st.rget 11) = true := by
      have hx5 : (st.rget 5).toNat = idx := by rw [h5, hkidx]
      have hx11 : (st.rget 11).toNat = inp.length := by rw [hregs.h11, tn inp.length (by omega)]
      exact slt_true (by rw [hx5]; omega) (by rw [hx11]; omega) (by rw [hx5, hx11]; exact hlt)
    have hdropc : inp.drop idx = inp[idx]! :: inp.drop (idx+1) := by
      rw [List.drop_eq_getElem_cons hlt, hvmem]
    rcases (show (inp[idx]! = 10 ∨ inp[idx]! = 32 ∨ inp[idx]! = 95)
        ∨ (inp[idx]! = 35 ∨ inp[idx]! = 59)
        ∨ (inp[idx]! ≠ 10 ∧ inp[idx]! ≠ 32 ∧ inp[idx]! ≠ 95 ∧ inp[idx]! ≠ 35 ∧ inp[idx]! ≠ 59)
        from by omega) with hsp | hcm | hns
    · -- SPACE: \n / space / _  → skip, continue
      have hisS : Hex0.isSpace inp[idx]! = true := by
        unfold Hex0.isSpace Hex0.c_nl Hex0.c_sp Hex0.c_us; rcases hsp with h|h|h <;> simp [h]
      have hisC : Hex0.isComment inp[idx]! = false := by
        unfold Hex0.isComment Hex0.c_hash Hex0.c_semi; rcases hsp with h|h|h <;> simp [h]
      obtain ⟨fb, st1, heb, hr1, hs5, hs6, hs14, hsm⟩ :=
        body_space st p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx)
          (st.mem (p + BitVec.ofNat 64 idx)) hregs h5 rfl (by rw [hcv]; exact hsp)
      have e5 : st1.rget 5 = BitVec.ofNat 64 (idx+1) := by rw [hs5, ofNat_succ]
      have e6 : st1.rget 6 = BitVec.ofNat 64 olen := by rw [hs6, h6]
      have e14 : st1.rget 14 = 0 := by rw [hs14, h14]
      have ebridge : ∀ k : Word, k.toNat < inp.length → st1.mem (p+k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
        intro k hk; rw [hsm]; exact hbridge k hk
      have eout : regionBytes st1.mem q olen = produced := by rw [hsm]; exact hout
      obtain ⟨fr, st', oc, her, hoc, hc14, hc6, hcreg⟩ :=
        ih (inp.length - (idx+1)) (by omega) (idx+1) olen st1 produced rfl hr1 e5 e6 e14
          (by omega) holen holenp ebridge eout
      have hstep : Hex0.decodeS .High (inp.drop idx) = Hex0.decodeS .High (inp.drop (idx+1)) := by
        rw [hdropc]; exact decodeS_high_space _ _ hisC hisS
      refine ⟨max fb fr + 1, st', oc, ?_, hoc, ?_, ?_, ?_⟩
      · rw [exec_while_step _ _ _ _ _ _ _ hcond (exec_mono_le (Nat.le_max_left fb fr) heb)]
        exact exec_mono_le (Nat.le_max_right fb fr) her
      · rw [hstep]; exact hc14
      · rw [hstep]; exact hc6
      · rw [hstep]; exact hcreg
    · -- COMMENT: '#' / ';' → skip to newline/EOF, continue
      have hisCt : Hex0.isComment inp[idx]! = true := by
        unfold Hex0.isComment Hex0.c_hash Hex0.c_semi; rcases hcm with h|h <;> simp [h]
      have hDle : commentSkip (inp.drop (idx+1)) ≤ inp.length - (idx+1) := by
        have := commentSkip_le (inp.drop (idx+1)); rwa [List.length_drop] at this
      -- gOf is 1 on the run before the newline
      have hdig : ∀ j, j < commentSkip (inp.drop (idx+1)) →
          gOf st.mem (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j) (BitVec.ofNat 64 inp.length) p = 1 := by
        intro j hj
        have hoff : (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j).toNat = idx+1+j := by
          rw [show BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j = BitVec.ofNat 64 (idx+1+j) from by bv_omega]
          exact tn _ (by omega)
        have hlt2 : idx+1+j < inp.length := by omega
        unfold gOf
        rw [if_pos (by rw [hoff, tn inp.length (by omega)]; omega)]
        have hmem := hbridge (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j) (by rw [hoff]; omega)
        rw [hoff] at hmem
        rw [if_neg]
        intro hcontra
        rw [hmem] at hcontra
        have hidxval : inp[idx+1+j]! = inp[idx+1+j] := by
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2]
        have hlt256 : inp[idx+1+j]! < 256 := by rw [hidxval]; exact hinp _ (List.getElem_mem hlt2)
        have hne : inp[idx+1+j]! ≠ 10 := by
          have hr := commentSkip_run_ne (inp.drop (idx+1)) j hj
          rwa [show (inp.drop (idx+1))[j]! = inp[idx+1+j]! from by
            simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]] at hr
        apply hne
        have h2 := congrArg BitVec.toNat hcontra
        rw [BitVec.toNat_ofNat, show (nlB : Byte).toNat = 10 from by decide] at h2; omega
      -- gOf is 0 at the newline (or EOF)
      have hz : gOf st.mem (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1))))
          (BitVec.ofNat 64 inp.length) p = 0 := by
        unfold gOf
        by_cases hDlen : commentSkip (inp.drop (idx+1)) < (inp.drop (idx+1)).length
        · have hlt2 : idx+1+commentSkip (inp.drop (idx+1)) < inp.length := by
            rw [List.length_drop] at hDlen; omega
          have hoff : (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))).toNat
              = idx+1+commentSkip (inp.drop (idx+1)) := by
            rw [show BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))
              = BitVec.ofNat 64 (idx+1+commentSkip (inp.drop (idx+1))) from by bv_omega]
            exact tn _ (by omega)
          rw [if_pos (by rw [hoff, tn inp.length (by omega)]; omega)]
          have hmem := hbridge (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1))))
            (by rw [hoff]; omega)
          rw [hoff] at hmem
          rw [if_pos]
          rw [hmem]
          have hg := commentSkip_get (inp.drop (idx+1)) hDlen
          rw [show (inp.drop (idx+1))[commentSkip (inp.drop (idx+1))]! = inp[idx+1+commentSkip (inp.drop (idx+1))]! from by
            simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]] at hg
          rw [hg]; rfl
        · have hDeq : commentSkip (inp.drop (idx+1)) = inp.length - (idx+1) := by
            rw [List.length_drop] at hDlen; omega
          have hoff : (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))).toNat
              = inp.length := by
            rw [show BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))
              = BitVec.ofNat 64 (idx+1+commentSkip (inp.drop (idx+1))) from by bv_omega]
            rw [tn _ (by omega)]; omega
          rw [if_neg (by rw [hoff, tn inp.length (by omega)]; omega)]
      obtain ⟨fb, st1, heb, hr1, hs5, hs6, hs14, hsm⟩ :=
        body_comment st p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx)
          (st.mem (p + BitVec.ofNat 64 idx)) (commentSkip (inp.drop (idx+1))) hregs h5 rfl
          (by rw [hcv]; exact hcm)
          (by rw [show BitVec.ofNat 64 idx + 1 = BitVec.ofNat 64 (idx+1) from by bv_omega, tn _ (by omega)]; omega)
          (by rw [tn inp.length (by omega)]; omega)
          (by rw [show BitVec.ofNat 64 idx + 1 = BitVec.ofNat 64 (idx+1) from by bv_omega, tn _ (by omega)]; omega)
          hdig hz
      -- the IL is now at J = idx+1+D
      have hJ : st1.rget 5 = BitVec.ofNat 64 (idx + 1 + commentSkip (inp.drop (idx+1))) := by
        rw [hs5]; bv_omega
      have e6 : st1.rget 6 = BitVec.ofNat 64 olen := by rw [hs6, h6]
      have e14 : st1.rget 14 = 0 := by rw [hs14, h14]
      have ebridge : ∀ k : Word, k.toNat < inp.length → st1.mem (p+k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
        intro k hk; rw [hsm]; exact hbridge k hk
      have eout : regionBytes st1.mem q olen = produced := by rw [hsm]; exact hout
      obtain ⟨fr, st', oc, her, hoc, hc14, hc6, hcreg⟩ :=
        ih (inp.length - (idx + 1 + commentSkip (inp.drop (idx+1)))) (by omega)
          (idx + 1 + commentSkip (inp.drop (idx+1))) olen st1 produced rfl hr1 hJ e6 e14
          (by omega) holen holenp ebridge eout
      have hstep : Hex0.decodeS .High (inp.drop idx)
          = Hex0.decodeS .High (inp.drop (idx + 1 + commentSkip (inp.drop (idx+1)))) := by
        rw [hdropc, decodeS_high_comment _ _ hisCt, ← decodeS_comment_reconcile,
            show (inp.drop (idx+1)).drop (commentSkip (inp.drop (idx+1)))
              = inp.drop (idx + 1 + commentSkip (inp.drop (idx+1))) from by rw [List.drop_drop]]
      refine ⟨max fb fr + 1, st', oc, ?_, hoc, ?_, ?_, ?_⟩
      · rw [exec_while_step _ _ _ _ _ _ _ hcond (exec_mono_le (Nat.le_max_left fb fr) heb)]
        exact exec_mono_le (Nat.le_max_right fb fr) her
      · rw [hstep]; exact hc14
      · rw [hstep]; exact hc6
      · rw [hstep]; exact hcreg
    · -- HEX: hex-digit path
      have hisCf : Hex0.isComment inp[idx]! = false := by
        unfold Hex0.isComment Hex0.c_hash Hex0.c_semi
        rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]; omega
      have hisSf : Hex0.isSpace inp[idx]! = false := by
        unfold Hex0.isSpace Hex0.c_nl Hex0.c_sp Hex0.c_us
        rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne,
            beq_eq_false_iff_ne]; omega
      have hpc : produced.length ≤ capN := by omega
      have htc1 : (BitVec.ofNat 64 idx + 1).toNat = idx + 1 := by
        rw [show BitVec.ofNat 64 idx + 1 = BitVec.ofNat 64 (idx+1) from by bv_omega]; exact tn _ (by omega)
      rcases body_hex st p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx)
          (st.mem (p + BitVec.ofNat 64 idx)) hregs h5 rfl (by rw [hcv]; exact hns) with
        ⟨hbad, fb, st1, heb, h14', h6', hm'⟩
      | ⟨hbad, htr, fb, st1, heb, h14', h6', hm'⟩
      | ⟨hbad, hlt2, hls, fb, st1, heb, h14', h6', hm'⟩
      | ⟨hbad, hlt2, hls, hbad2, fb, st1, heb, h14', h6', hm'⟩
      | ⟨hbad, hlt2, hls, hbad2, hfull, fb, st1, heb, h14', h6', hm'⟩
      | ⟨hbad, hlt2, hls, hbad2, hfull, fb, st1, heb, hf5, hf6, hf14, hfregs, hfmem⟩
      · -- ARM A: bad high nibble → Unknown (5)
        have hnib : Hex0.nibble inp[idx]! = none := by
          rw [← hcv]; exact (pnibR_eq_255_iff _).mp hbad
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Unknown) := by
          rw [hdropc]; exact decodeS_high_badhi _ _ hisCf hisSf hnib
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (5, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        refine ⟨fb + 1, st1, .ret, ?_, Or.inr rfl, ?_, ?_, ?_⟩
        · exact exec_while_ret _ _ _ _ _ _ _ hcond heb
        · rw [hbr]; exact h14'
        · rw [hbr, h6', h6, htno]; exact holenp
        · rw [hbr, h6', h6, htno, hm']; exact hout
      · -- ARM B: no low char → Trailing (4)
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat := by
          rw [← hcv]; exact pnibR_nibble _ hbad
        have hrestnil : inp.drop (idx+1) = [] := by
          rw [List.drop_eq_nil_iff]
          have ht1 : (BitVec.ofNat 64 idx + 1).toNat = idx + 1 := by
            rw [show BitVec.ofNat 64 idx + 1 = BitVec.ofNat 64 (idx+1) from by bv_omega]; exact tn _ (by omega)
          rw [tn inp.length (by omega), ht1] at htr; omega
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Trailing) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hrestnil, decodeS_low_nil]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (4, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        refine ⟨fb + 1, st1, .ret, ?_, Or.inr rfl, ?_, ?_, ?_⟩
        · exact exec_while_ret _ _ _ _ _ _ _ hcond heb
        · rw [hbr]; exact h14'
        · rw [hbr, h6', h6, htno]; exact holenp
        · rw [hbr, h6', h6, htno, hm']; exact hout
      · -- ARM C: low-stop char → Split (3)
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega), htc1] at hlt2; exact hlt2
        have hc2eq : st.mem (p + (BitVec.ofNat 64 idx + 1)) = BitVec.ofNat 8 (inp[idx+1]!) := by
          have hb := hbridge (BitVec.ofNat 64 idx + 1) (by rw [htc1]; omega); rwa [htc1] at hb
        have hv2 : inp[idx+1]! < 256 := by
          rw [show inp[idx+1]! = inp[idx+1] from by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]]
          exact hinp _ (List.getElem_mem hlt2n)
        have hc2v : (st.mem (p + (BitVec.ofNat 64 idx + 1))).toNat = inp[idx+1]! := by rw [hc2eq, BitVec.toNat_ofNat]; omega
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat := by rw [← hcv]; exact pnibR_nibble _ hbad
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hlsT : Hex0.isLowStop inp[idx+1]! = true := by rw [← hc2v]; exact (lowStop_iff _).mp hls
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Split) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_split _ _ _ hlsT]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (3, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        refine ⟨fb + 1, st1, .ret, ?_, Or.inr rfl, ?_, ?_, ?_⟩
        · exact exec_while_ret _ _ _ _ _ _ _ hcond heb
        · rw [hbr]; exact h14'
        · rw [hbr, h6', h6, htno]; exact holenp
        · rw [hbr, h6', h6, htno, hm']; exact hout
      · -- ARM D: bad low nibble → Unknown (5)
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega), htc1] at hlt2; exact hlt2
        have hc2eq : st.mem (p + (BitVec.ofNat 64 idx + 1)) = BitVec.ofNat 8 (inp[idx+1]!) := by
          have hb := hbridge (BitVec.ofNat 64 idx + 1) (by rw [htc1]; omega); rwa [htc1] at hb
        have hv2 : inp[idx+1]! < 256 := by
          rw [show inp[idx+1]! = inp[idx+1] from by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]]
          exact hinp _ (List.getElem_mem hlt2n)
        have hc2v : (st.mem (p + (BitVec.ofNat 64 idx + 1))).toNat = inp[idx+1]! := by rw [hc2eq, BitVec.toNat_ofNat]; omega
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat := by rw [← hcv]; exact pnibR_nibble _ hbad
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hlsF : Hex0.isLowStop inp[idx+1]! = false := by
          rcases Bool.eq_false_or_eq_true (Hex0.isLowStop inp[idx+1]!) with h | h
          · exact absurd ((lowStop_iff _).mpr (by rw [hc2v]; exact h)) hls
          · exact h
        have hnib2 : Hex0.nibble inp[idx+1]! = none := by rw [← hc2v]; exact (pnibR_eq_255_iff _).mp hbad2
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Unknown) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_badlo _ _ _ hlsF hnib2]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (5, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        refine ⟨fb + 1, st1, .ret, ?_, Or.inr rfl, ?_, ?_, ?_⟩
        · exact exec_while_ret _ _ _ _ _ _ _ hcond heb
        · rw [hbr]; exact h14'
        · rw [hbr, h6', h6, htno]; exact holenp
        · rw [hbr, h6', h6, htno, hm']; exact hout
      · -- ARM E: output full → OutputShort (2)
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega), htc1] at hlt2; exact hlt2
        have hc2eq : st.mem (p + (BitVec.ofNat 64 idx + 1)) = BitVec.ofNat 8 (inp[idx+1]!) := by
          have hb := hbridge (BitVec.ofNat 64 idx + 1) (by rw [htc1]; omega); rwa [htc1] at hb
        have hv2 : inp[idx+1]! < 256 := by
          rw [show inp[idx+1]! = inp[idx+1] from by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]]
          exact hinp _ (List.getElem_mem hlt2n)
        have hc2v : (st.mem (p + (BitVec.ofNat 64 idx + 1))).toNat = inp[idx+1]! := by rw [hc2eq, BitVec.toNat_ofNat]; omega
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat := by rw [← hcv]; exact pnibR_nibble _ hbad
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hlsF : Hex0.isLowStop inp[idx+1]! = false := by
          rcases Bool.eq_false_or_eq_true (Hex0.isLowStop inp[idx+1]!) with h | h
          · exact absurd ((lowStop_iff _).mpr (by rw [hc2v]; exact h)) hls
          · exact h
        have hnib2 : Hex0.nibble inp[idx+1]! = some (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat := by
          rw [← hc2v]; exact pnibR_nibble _ hbad2
        have hcapeq : produced.length = capN := by
          have hh := hfull; rw [tn capN (by omega), h6, htno] at hh; omega
        have hdec : Hex0.decodeS .High (inp.drop idx)
            = (((pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat)
                  :: (Hex0.decodeS .High (inp.drop (idx+2))).1, (Hex0.decodeS .High (inp.drop (idx+2))).2) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_goodlo _ _ _ _ hlsF hnib2]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (2, produced, capN) := by
          rw [hdec]; unfold boundedRun
          rw [if_neg (by simp only [List.length_cons]; omega)]
          simp [show capN - produced.length = 0 from by omega]
        refine ⟨fb + 1, st1, .ret, ?_, Or.inr rfl, ?_, ?_, ?_⟩
        · exact exec_while_ret _ _ _ _ _ _ _ hcond heb
        · rw [hbr]; exact h14'
        · rw [hbr, h6', h6, htno]; exact holenp.trans hcapeq
        · rw [hbr, h6', h6, htno, hm']; exact hout
      · -- ARM F: write the byte, continue
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega), htc1] at hlt2; exact hlt2
        have holt : olen < capN := by have hh := hfull; rw [h6, htno, tn capN (by omega)] at hh; exact hh
        have hc2eq : st.mem (p + (BitVec.ofNat 64 idx + 1)) = BitVec.ofNat 8 (inp[idx+1]!) := by
          have hb := hbridge (BitVec.ofNat 64 idx + 1) (by rw [htc1]; omega); rwa [htc1] at hb
        have hv2 : inp[idx+1]! < 256 := by
          rw [show inp[idx+1]! = inp[idx+1] from by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]]
          exact hinp _ (List.getElem_mem hlt2n)
        have hc2v : (st.mem (p + (BitVec.ofNat 64 idx + 1))).toNat = inp[idx+1]! := by rw [hc2eq, BitVec.toNat_ofNat]; omega
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat := by rw [← hcv]; exact pnibR_nibble _ hbad
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hlsF : Hex0.isLowStop inp[idx+1]! = false := by
          rcases Bool.eq_false_or_eq_true (Hex0.isLowStop inp[idx+1]!) with h | h
          · exact absurd ((lowStop_iff _).mpr (by rw [hc2v]; exact h)) hls
          · exact h
        have hnib2 : Hex0.nibble inp[idx+1]! = some (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat := by
          rw [← hc2v]; exact pnibR_nibble _ hbad2
        have hbyte : ((((pnibR (st.mem (p + BitVec.ofNat 64 idx))) <<< 4)
              ||| pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).setWidth 8).toNat
            = (pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat := hexbyte_val _ _ hbad hbad2
        -- recursion-state facts
        have e5 : st1.rget 5 = BitVec.ofNat 64 (idx+2) := by rw [hf5]; bv_omega
        have e6 : st1.rget 6 = BitVec.ofNat 64 (olen+1) := by rw [hf6, h6]; bv_omega
        have e14 : st1.rget 14 = 0 := by rw [hf14, h14]
        have ebridge : ∀ k : Word, k.toNat < inp.length → st1.mem (p+k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
          intro k hk
          rw [hfmem]
          rw [storeByte_preserves (s := ⟨p, inp.length⟩)
                (a := q + st.rget 6) (a' := p + k) ?hna ⟨k.toNat, hk, by bv_omega⟩]
          · exact hbridge k hk
          case hna =>
            rintro ⟨j, hj, hjeq⟩
            exact hdisj (q + st.rget 6) ⟨j, hj, hjeq⟩ ⟨olen, holt, by rw [h6]⟩
        have eout : regionBytes st1.mem q (olen+1)
            = produced ++ [(pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat] := by
          rw [hfmem, h6, regionBytes_snoc, regionBytes_store_self st q olen _ (by omega), hout]
          congr 2
          rw [show ((st.storeByte (q + BitVec.ofNat 64 olen) _).mem (q + BitVec.ofNat 64 olen))
                = (((pnibR (st.mem (p + BitVec.ofNat 64 idx))) <<< 4)
                    ||| pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).setWidth 8 from by
            simp [mem_storeByte_self]]
          exact hbyte
        obtain ⟨fr, st', oc, her, hoc, hc14, hc6, hcreg⟩ :=
          ih (inp.length - (idx+2)) (by omega) (idx+2) (olen+1) st1
            (produced ++ [(pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat]) rfl hfregs e5 e6 e14
            (by omega) (by omega) (by simp [holenp]) ebridge eout
        have hbreq : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
              (Hex0.decodeS .High (inp.drop idx)).2 capN
            = boundedRun (produced ++ [(pnibR (st.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (st.mem (p + (BitVec.ofNat 64 idx + 1)))).toNat])
              (Hex0.decodeS .High (inp.drop (idx+2))).1 (Hex0.decodeS .High (inp.drop (idx+2))).2 capN := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_goodlo _ _ _ _ hlsF hnib2]
          exact boundedRun_cons _ _ _ _ _ (by omega)
        refine ⟨max fb fr + 1, st', oc, ?_, hoc, ?_, ?_, ?_⟩
        · rw [exec_while_step _ _ _ _ _ _ _ hcond (exec_mono_le (Nat.le_max_left fb fr) heb)]
          exact exec_mono_le (Nat.le_max_right fb fr) her
        · rw [hbreq]; exact hc14
        · rw [hbreq]; exact hc6
        · rw [hbreq]; exact hcreg
  · -- base case: idx = inp.length, loop guard false
    have hidxlen : idx = inp.length := by omega
    subst hidxlen
    have hdrop : inp.drop inp.length = [] := by simp
    have hx5 : (st.rget 5).toNat = inp.length := by rw [h5, tn inp.length (by omega)]
    have hx11 : (st.rget 11).toNat = inp.length := by rw [hregs.h11, tn inp.length (by omega)]
    have hcond : evalCond .lt (st.rget 5) (st.rget 11) = false :=
      slt_false (by rw [hx5]; omega) (by rw [hx11]; omega) (by rw [hx5, hx11] <;> omega)
    have htno : (BitVec.ofNat 64 olen).toNat = olen := tn olen (by omega)
    have hpc : produced.length ≤ capN := by omega
    have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop inp.length)).1
        (Hex0.decodeS .High (inp.drop inp.length)).2 capN = (0, produced, produced.length) := by
      rw [hdrop, decodeS_high_nil]; simp [boundedRun, hpc, Hex0.statusCode]
    refine ⟨1, st, .normal, ?_, Or.inl rfl, ?_, ?_, ?_⟩
    · rw [show (1:Nat) = 0+1 from rfl, exec_while_done _ _ _ _ _ _ hcond]
    · rw [hbr]; simp [h14]
    · rw [hbr, h6, htno]; exact holenp
    · rw [hbr, h6, htno]; exact hout

/-! ### Prelude peel + coreSpec assembly (item C). -/

/-- Peel hex0's 15 const/init instructions into the loop-entry state. -/
theorem hex0_setup (inp : List Nat) (cap : Nat) :
    ∃ st0, Regs st0 inBase (BitVec.ofNat 64 inp.length) outBase (BitVec.ofNat 64 cap)
      ∧ st0.rget 5 = 0 ∧ st0.rget 6 = 0 ∧ st0.rget 14 = 0
      ∧ st0.mem = (hex0ILState (asBytes inp) cap).mem
      ∧ (∀ fw stw oc, exec fw (.while .lt 5 11 body) st0 = some (stw, oc)
          → exec (fw + 16) hex0 (hex0ILState (asBytes inp) cap) = some (stw, oc)) := by
  refine ⟨(hex0ILState (asBytes inp) cap).rset 20 ((BitVec.ofNat 12 48).signExtend 64)
      |>.rset 21 ((BitVec.ofNat 12 57).signExtend 64) |>.rset 22 ((BitVec.ofNat 12 65).signExtend 64)
      |>.rset 23 ((BitVec.ofNat 12 70).signExtend 64) |>.rset 24 ((BitVec.ofNat 12 10).signExtend 64)
      |>.rset 25 ((BitVec.ofNat 12 32).signExtend 64) |>.rset 26 ((BitVec.ofNat 12 95).signExtend 64)
      |>.rset 27 ((BitVec.ofNat 12 35).signExtend 64) |>.rset 18 ((BitVec.ofNat 12 59).signExtend 64)
      |>.rset 19 ((BitVec.ofNat 12 255).signExtend 64) |>.rset 17 ((BitVec.ofNat 12 55).signExtend 64)
      |>.rset 16 ((BitVec.ofNat 12 1).signExtend 64) |>.rset 5 ((BitVec.ofNat 12 0).signExtend 64)
      |>.rset 6 ((BitVec.ofNat 12 0).signExtend 64) |>.rset 14 ((BitVec.ofNat 12 0).signExtend 64),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
    { h10 := by simp; simp [hex0ILState, St.rget, inBase]
      h11 := by simp; simp [hex0ILState, St.rget, asBytes]
      h12 := by simp; simp [hex0ILState, St.rget, outBase]
      h13 := by simp; simp [hex0ILState, St.rget]
      h16 := by simp
      h17 := by simp
      h18 := by simp
      h19 := by simp
      h20 := by simp
      h21 := by simp
      h22 := by simp
      h23 := by simp
      h24 := by simp
      h25 := by simp
      h26 := by simp
      h27 := by simp }
  · simp
  · simp
  · simp
  · simp [hex0ILState]
  · intro fw stw oc hw
    unfold hex0
    simp only [seqs, List.foldr_cons, List.foldr_nil]
    rw [show fw+16 = (fw+15)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+14) 20 48 _),
        show fw+15 = (fw+14)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+13) 21 57 _),
        show fw+14 = (fw+13)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+12) 22 65 _),
        show fw+13 = (fw+12)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+11) 23 70 _),
        show fw+12 = (fw+11)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+10) 24 10 _),
        show fw+11 = (fw+10)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+9) 25 32 _),
        show fw+10 = (fw+9)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+8) 26 95 _),
        show fw+9 = (fw+8)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+7) 27 35 _),
        show fw+8 = (fw+7)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+6) 18 59 _),
        show fw+7 = (fw+6)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+5) 19 255 _),
        show fw+6 = (fw+5)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+4) 17 55 _),
        show fw+5 = (fw+4)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+3) 16 1 _),
        show fw+4 = (fw+3)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+2) 5 0 _),
        show fw+3 = (fw+2)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit (fw+1) 6 0 _),
        show fw+2 = (fw+1)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_lit fw 14 0 _)]
    cases oc with
    | normal =>
      rw [exec_seq_normal _ _ _ _ _ hw]
      cases fw with
      | zero => simp [exec] at hw
      | succ f => exact exec_skip f stw
    | ret => exact exec_seq_ret _ _ _ _ _ hw
    | brk k => exact exec_seq_brk _ _ _ _ _ _ hw
    | cont k => exact exec_seq_cont _ _ _ _ _ _ hw

/-- **hex0 functional correctness**: run on the IL semantics, hex0 computes `Hex0.coreSpec`.
    Input is a shared borrow, output a unique borrow (`Wf` ⇒ the regions don't alias). -/
theorem hex0_correct (inp : List Nat) (cap : Nat)
    (hinp : ∀ x ∈ inp, x < 256) (hlen : inp.length < 2^63) (hcap : cap < 2^63)
    (hwf : Wf [⟨⟨inBase, inp.length⟩, .shared⟩, ⟨⟨outBase, cap⟩, .uniq⟩]) :
    ∃ fuel, hex0Run (asBytes inp) cap fuel = Hex0.coreSpec inp cap := by
  have hdisj : Disjoint ⟨inBase, inp.length⟩ ⟨outBase, cap⟩ :=
    hwf.disjoint (b := ⟨⟨inBase, inp.length⟩, .shared⟩) (b' := ⟨⟨outBase, cap⟩, .uniq⟩)
      (by simp) (by simp) (by intro h; injection h with _ hp; exact absurd hp (by decide)) rfl
  obtain ⟨st0, hregs0, h05, h06, h014, h0mem, hlift⟩ := hex0_setup inp cap
  have hbridge : ∀ k : Word, k.toNat < inp.length → st0.mem (inBase + k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
    intro k hk
    rw [h0mem]
    have hia : ((inBase + k) - inBase).toNat = k.toNat := by bv_omega
    have hlen' : (asBytes inp).length = inp.length := by simp [asBytes]
    simp only [hex0ILState, hia, hlen', if_pos hk]
    rw [List.getElem?_eq_getElem (by rw [hlen']; exact hk)]
    simp [asBytes, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  obtain ⟨fw, stw, oc, hwexec, hoc, hw14, hw6, hwreg⟩ :=
    main_loop inp inBase outBase cap hinp hlen hcap hdisj (inp.length - 0) 0 0 st0 []
      rfl hregs0 (by rw [h05]; rfl) (by rw [h06]; rfl) h014 (by omega) (by omega) rfl hbridge
      (by simp [regionBytes])
  rw [List.drop_zero, boundedRun_nil_coreSpec] at hw14 hw6 hwreg
  refine ⟨fw + 16, ?_⟩
  have hrun : run (fw + 16) hex0 (hex0ILState (asBytes inp) cap) = some stw := by
    unfold run; rw [hlift fw stw oc hwexec]; rcases hoc with h | h <;> subst h <;> rfl
  unfold hex0Run
  rw [hrun]
  show ((stw.rget 14).toNat, outBytes stw, (stw.rget 6).toNat) = Hex0.coreSpec inp cap
  rw [hw14, hw6, show outBytes stw = regionBytes stw.mem outBase (stw.rget 6).toNat from rfl, hwreg]

end LowIR.Ctrl.Hex0
