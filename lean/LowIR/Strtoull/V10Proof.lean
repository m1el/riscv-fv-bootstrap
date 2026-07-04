/-
  Functional correctness of `strtoull10` (wrapping base-10 parse), sorry-free.

  Same shape as `strlen_loop`/`strlen_correct`, with the accumulator (`acc*10+digit`)
  and the `brk 0` termination caught by the surrounding `block`. Reuses the unsigned
  condition lemmas (`Strtoull2.geu_true/geu_false`) and the exec/register foundation.
-/
import LowIR.Strlen.Ctrl
import LowIR.Strtoull.V1
import LowIR.Strtoull.V1Proof
import LowIR.Strtoull.V2Proof

set_option linter.unusedSimpArgs false

namespace LowIR.Ctrl

open Rv64i (Word Byte)

/-- digit predicate (Prop form of `Strtoull.isDig`). -/
def IsD (b : Byte) : Prop := 48 ≤ b.toNat ∧ b.toNat ≤ 57

/-- the digit-check sub-statement and the whole loop body (defeq to `strtoull10`'s). -/
def digitCheck : Stmt := .ife .geu 7 20 (.ife .geu 7 22 (.brkB 0) .skip) (.brkB 0)

def body : Stmt :=
  .seq (.lbu 7 5 0) (.seq digitCheck (.seq (.sub 28 7 20) (.seq (.slli 29 12 3)
    (.seq (.slli 30 12 1) (.seq (.add 12 29 30) (.seq (.add 12 12 28)
      (.seq (.addi 5 5 1) .skip)))))))

/-- left fold of `d` digit bytes starting at `cur`. -/
def accFrom (mem : Word → Byte) : Word → Word → Nat → Word
  | _,   acc, 0     => acc
  | cur, acc, d + 1 => accFrom mem (cur + 1) (acc * 10 + BitVec.ofNat 64 ((mem cur).toNat - 48)) d

/-! ### One body iteration on a digit. -/

theorem body_digit (f : Nat) (st : St) (cur acc0 : Word)
    (h5 : st.rget 5 = cur) (h12 : st.rget 12 = acc0) (h20 : st.rget 20 = 48) (h22 : st.rget 22 = 58)
    (hd1 : 48 ≤ (st.mem cur).toNat) (hd2 : (st.mem cur).toNat ≤ 57) :
    ∃ s', exec (f + 12) body st = some (s', .normal)
      ∧ s'.rget 5 = cur + 1
      ∧ s'.rget 12 = acc0 * 10 + BitVec.ofNat 64 ((st.mem cur).toNat - 48)
      ∧ s'.rget 20 = 48 ∧ s'.rget 22 = 58 ∧ s'.rget 16 = st.rget 16 ∧ s'.mem = st.mem := by
  have e_lbu : exec (f+11) (.lbu 7 5 0) st
      = some (st.rset 7 ((st.mem cur).setWidth 64), .normal) := by
    rw [exec_lbu]; simp [h5, zero_signExtend, wadd_zero]
  have hge : evalCond .geu ((st.rset 7 ((st.mem cur).setWidth 64)).rget 7)
      ((st.rset 7 ((st.mem cur).setWidth 64)).rget 20) = true := by
    rw [rget_rset_eq _ _ _ (by decide : (7:Reg) ≠ 0),
        rget_rset_ne _ _ _ _ (by decide : (20:Reg) ≠ 7), h20]
    exact Strtoull2.geu_true Strtoull2.tn48 hd1
  have hlt : evalCond .geu ((st.rset 7 ((st.mem cur).setWidth 64)).rget 7)
      ((st.rset 7 ((st.mem cur).setWidth 64)).rget 22) = false := by
    rw [rget_rset_eq _ _ _ (by decide : (7:Reg) ≠ 0),
        rget_rset_ne _ _ _ _ (by decide : (22:Reg) ≠ 7), h22]
    exact Strtoull2.geu_false Strtoull2.tn58 (show (st.mem cur).toNat < 58 by omega)
  have e_dc : exec (f+10) digitCheck (st.rset 7 ((st.mem cur).setWidth 64))
      = some (st.rset 7 ((st.mem cur).setWidth 64), .normal) := by
    rw [digitCheck, exec_ife_then _ _ _ _ _ _ _ hge, exec_ife_else _ _ _ _ _ _ _ hlt]; simp [exec]
  have hbody_eq : exec (f + 12) body st = some (
      ((((((st.rset 7 ((st.mem cur).setWidth 64)).rset 28 ((st.mem cur).setWidth 64 - 48#64)).rset
        29 (acc0 <<< 3)).rset 30 (acc0 <<< 1)).rset 12 (acc0 <<< 3 + acc0 <<< 1)).rset
        12 (acc0 <<< 3 + acc0 <<< 1 + ((st.mem cur).setWidth 64 - 48#64))).rset 5 (cur + 1#64),
      .normal) := by
    unfold body
    rw [show f+12 = (f+11)+1 from rfl, exec_seq_normal _ _ _ _ _ e_lbu,
        show f+11 = (f+10)+1 from rfl, exec_seq_normal _ _ _ _ _ e_dc,
        show f+10 = (f+9)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_sub _ _ _ _ _),
        show f+9 = (f+8)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_slli _ _ _ _ _),
        show f+8 = (f+7)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_slli _ _ _ _ _),
        show f+7 = (f+6)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_add _ _ _ _ _),
        show f+6 = (f+5)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_add _ _ _ _ _),
        show f+5 = (f+4)+1 from rfl, exec_seq_normal _ _ _ _ _ (exec_addi _ _ _ _ _)]
    simp [exec, h5, h12, h20]
  refine ⟨_, hbody_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [rget_rset_ne _ _ _ _ (by decide : (12:Reg) ≠ 5),
        rget_rset_eq _ _ _ (by decide : (12:Reg) ≠ 0)]
    bv_omega
  · simp [h20]
  · simp [h22]
  · simp
  · simp

/-! ### One body iteration on a non-digit: returns `brk 0`, cursor unchanged. -/

theorem body_break (f : Nat) (st : St) (cur : Word)
    (h5 : st.rget 5 = cur) (h20 : st.rget 20 = 48) (h22 : st.rget 22 = 58)
    (hnd : ¬ IsD (st.mem cur)) :
    exec (f + 5) body st = some (st.rset 7 ((st.mem cur).setWidth 64), .brk 0) := by
  have e_lbu : exec (f+4) (.lbu 7 5 0) st
      = some (st.rset 7 ((st.mem cur).setWidth 64), .normal) := by
    rw [exec_lbu]; simp [h5, zero_signExtend, wadd_zero]
  have e_dc : exec (f+3) digitCheck (st.rset 7 ((st.mem cur).setWidth 64))
      = some (st.rset 7 ((st.mem cur).setWidth 64), .brk 0) := by
    unfold IsD at hnd
    rcases Nat.lt_or_ge (st.mem cur).toNat 48 with hlo | hge
    · have hcf : evalCond .geu ((st.rset 7 ((st.mem cur).setWidth 64)).rget 7)
          ((st.rset 7 ((st.mem cur).setWidth 64)).rget 20) = false := by
        rw [rget_rset_eq _ _ _ (by decide : (7:Reg) ≠ 0),
            rget_rset_ne _ _ _ _ (by decide : (20:Reg) ≠ 7), h20]
        exact Strtoull2.geu_false Strtoull2.tn48 hlo
      rw [digitCheck, exec_ife_else _ _ _ _ _ _ _ hcf]; simp [exec]
    · have hge58 : 58 ≤ (st.mem cur).toNat := by omega
      have hco : evalCond .geu ((st.rset 7 ((st.mem cur).setWidth 64)).rget 7)
          ((st.rset 7 ((st.mem cur).setWidth 64)).rget 20) = true := by
        rw [rget_rset_eq _ _ _ (by decide : (7:Reg) ≠ 0),
            rget_rset_ne _ _ _ _ (by decide : (20:Reg) ≠ 7), h20]
        exact Strtoull2.geu_true Strtoull2.tn48 hge
      have hci : evalCond .geu ((st.rset 7 ((st.mem cur).setWidth 64)).rget 7)
          ((st.rset 7 ((st.mem cur).setWidth 64)).rget 22) = true := by
        rw [rget_rset_eq _ _ _ (by decide : (7:Reg) ≠ 0),
            rget_rset_ne _ _ _ _ (by decide : (22:Reg) ≠ 7), h22]
        exact Strtoull2.geu_true Strtoull2.tn58 hge58
      rw [digitCheck, exec_ife_then _ _ _ _ _ _ _ hco, exec_ife_then _ _ _ _ _ _ _ hci]; simp [exec]
  unfold body
  rw [show f+5 = (f+4)+1 from rfl, exec_seq_normal _ _ _ _ _ e_lbu]
  exact exec_seq_brk _ _ _ _ _ _ e_dc

/-! ### The digit loop. -/

theorem digit_loop (d : Nat) :
    ∀ (st : St) (cur acc0 : Word),
      st.rget 5 = cur → st.rget 12 = acc0 → st.rget 20 = 48 → st.rget 22 = 58 → st.rget 16 = 1 →
      (∀ j, j < d → IsD (st.mem (cur + BitVec.ofNat 64 j))) →
      ¬ IsD (st.mem (cur + BitVec.ofNat 64 d)) →
      ∃ s', exec (d + 12) (.while .lt 0 16 body) st = some (s', .brk 0)
        ∧ s'.rget 12 = accFrom st.mem cur acc0 d
        ∧ s'.rget 5 = cur + BitVec.ofNat 64 d
        ∧ s'.rget 20 = 48 ∧ s'.rget 22 = 58 ∧ s'.rget 16 = 1 ∧ s'.mem = st.mem := by
  induction d with
  | zero =>
    intro st cur acc0 h5 h12 h20 h22 h16 _ hnd
    rw [cur_zero] at hnd
    have hcond : evalCond .lt (st.rget 0) (st.rget 16) = true := by rw [rget_zero, h16]; decide
    have hbody : exec 11 body st = some (st.rset 7 ((st.mem cur).setWidth 64), .brk 0) :=
      body_break 6 st cur h5 h20 h22 hnd
    refine ⟨st.rset 7 ((st.mem cur).setWidth 64), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show (0:Nat)+12 = 11+1 from rfl]; exact exec_while_brk _ _ _ _ _ _ _ _ hcond hbody
    · simp [accFrom, h12]
    · rw [cur_zero]; simp [h5]
    · simp [h20]
    · simp [h22]
    · simp [h16]
    · simp
  | succ d ih =>
    intro st cur acc0 h5 h12 h20 h22 h16 hdig hnd
    have hd0 : IsD (st.mem cur) := by have := hdig 0 (by omega); rwa [cur_zero] at this
    have hcond : evalCond .lt (st.rget 0) (st.rget 16) = true := by rw [rget_zero, h16]; decide
    obtain ⟨s7, hb, hs5, hs12, hs20, hs22, hs16, hsmem⟩ :=
      body_digit d st cur acc0 h5 h12 h20 h22 hd0.1 hd0.2
    rw [show (d+1)+12 = (d+12)+1 from rfl, exec_while_step _ _ _ _ _ _ _ hcond hb]
    have hpre' : ∀ j, j < d → IsD (s7.mem (cur+1 + BitVec.ofNat 64 j)) := by
      intro j hj; rw [hsmem, ← cur_step]; exact hdig (j+1) (by omega)
    have hnd' : ¬ IsD (s7.mem (cur+1 + BitVec.ofNat 64 d)) := by
      rw [hsmem, ← cur_step]; exact hnd
    have hs16' : s7.rget 16 = 1 := by rw [hs16, h16]
    obtain ⟨s', he, hr12, hr5, hr20, hr22, hr16, hrmem⟩ :=
      ih s7 (cur+1) (acc0 * 10 + BitVec.ofNat 64 ((st.mem cur).toNat - 48)) hs5 hs12 hs20 hs22 hs16' hpre' hnd'
    refine ⟨s', he, ?_, ?_, hr20, hr22, hr16, ?_⟩
    · rw [hr12, hsmem]; simp only [accFrom]
    · rw [hr5, cur_step]
    · rw [hrmem, hsmem]

/-! ### Top-level: the whole program computes the digit fold. -/

theorem strtoull10_correct (st : St) (d : Nat)
    (hdig : ∀ j, j < d → IsD (st.mem (st.rget 10 + BitVec.ofNat 64 j)))
    (hnd : ¬ IsD (st.mem (st.rget 10 + BitVec.ofNat 64 d))) :
    ∃ s, exec (d + 19) Strtoull.strtoull10 st = some (s, .normal)
      ∧ s.rget 12 = accFrom st.mem (st.rget 10) 0 d := by
  -- peel the 5 const/init instructions of the prelude
  have e1 : exec (d+18) (.addi 20 0 (BitVec.ofNat 12 48)) st = some (st.rset 20 48, .normal) := by
    rw [exec_addi, show st.rget 0 + (BitVec.ofNat 12 48).signExtend 64 = (48:Word) from by
      rw [rget_zero]; decide]
  have e2 : exec (d+17) (.addi 22 0 (BitVec.ofNat 12 58)) (st.rset 20 48)
      = some ((st.rset 20 48).rset 22 58, .normal) := by
    rw [exec_addi, show (st.rset 20 48).rget 0 + (BitVec.ofNat 12 58).signExtend 64 = (58:Word) from by
      rw [rget_zero]; decide]
  have e3 : exec (d+16) (.addi 16 0 (BitVec.ofNat 12 1)) ((st.rset 20 48).rset 22 58)
      = some (((st.rset 20 48).rset 22 58).rset 16 1, .normal) := by
    rw [exec_addi, show ((st.rset 20 48).rset 22 58).rget 0 + (BitVec.ofNat 12 1).signExtend 64 = (1:Word) from by
      rw [rget_zero]; decide]
  have e4 : exec (d+15) (.addi 12 0 0) (((st.rset 20 48).rset 22 58).rset 16 1)
      = some ((((st.rset 20 48).rset 22 58).rset 16 1).rset 12 0, .normal) := by
    rw [exec_addi, show (((st.rset 20 48).rset 22 58).rset 16 1).rget 0 + (0:BitVec 12).signExtend 64 = (0:Word) from by
      rw [rget_zero]; decide]
  have e5 : exec (d+14) (.addi 5 10 0) ((((st.rset 20 48).rset 22 58).rset 16 1).rset 12 0)
      = some (((((st.rset 20 48).rset 22 58).rset 16 1).rset 12 0).rset 5 (st.rget 10), .normal) := by
    rw [exec_addi, show (((((st.rset 20 48).rset 22 58).rset 16 1).rset 12 0)).rget 10
        + (0:BitVec 12).signExtend 64 = st.rget 10 from by simp [zero_signExtend, wadd_zero]]
  -- apply the digit loop at the loop-entry state s0
  obtain ⟨s', hwhile, hs12, _, _, _, _, _⟩ :=
    digit_loop d (((((st.rset 20 48).rset 22 58).rset 16 1).rset 12 0).rset 5 (st.rget 10)) (st.rget 10) 0
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by intro j hj; simp only [rset_mem]; exact hdig j hj)
      (by simp only [rset_mem]; exact hnd)
  have hblock : exec (d+13) (.block (.while .lt 0 16 body))
      (((((st.rset 20 48).rset 22 58).rset 16 1).rset 12 0).rset 5 (st.rget 10)) = some (s', .normal) := by
    rw [show d+13 = (d+12)+1 from rfl]; exact exec_block_catch _ _ _ _ hwhile
  refine ⟨s', ?_, ?_⟩
  · show exec (d+19) (.seq (.addi 20 0 (BitVec.ofNat 12 48)) (.seq (.addi 22 0 (BitVec.ofNat 12 58))
        (.seq (.addi 16 0 (BitVec.ofNat 12 1)) (.seq (.addi 12 0 0)
        (.seq (.addi 5 10 0) (.seq (.block (.while .lt 0 16 body)) .skip)))))) st = some (s', .normal)
    rw [show d+19 = (d+18)+1 from rfl, exec_seq_normal _ _ _ _ _ e1,
        show d+18 = (d+17)+1 from rfl, exec_seq_normal _ _ _ _ _ e2,
        show d+17 = (d+16)+1 from rfl, exec_seq_normal _ _ _ _ _ e3,
        show d+16 = (d+15)+1 from rfl, exec_seq_normal _ _ _ _ _ e4,
        show d+15 = (d+14)+1 from rfl, exec_seq_normal _ _ _ _ _ e5,
        show d+14 = (d+13)+1 from rfl, exec_seq_normal _ _ _ _ _ hblock]
    rfl
  · rw [hs12]; simp only [rset_mem]

end LowIR.Ctrl

