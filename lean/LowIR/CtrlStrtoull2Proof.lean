/-
  Functional correctness of the conformant `strtoull` (`CtrlStrtoull2`) — foundation:
  unsigned condition lemmas (bv_omega/ult-friendly), the digit value fact, and the
  threshold-construction lemma (the prelude builds T = 0x1999999999999999).

  The digit loop + correctness build on these (see the lower sections / PROGRESS.md).
-/
import LowIR.CtrlStrlen
import LowIR.CtrlStrtoull2
import LowIR.CtrlStrtoullProof

set_option linter.unusedSimpArgs false

namespace LowIR.Ctrl.Strtoull2

open LowIR.Ctrl
open Rv64i (Word Byte)

/-! ### Unsigned condition lemmas — `geu` against a zero-extended byte. -/

private theorem sw (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega

theorem geu_true {b : Byte} {m : Nat} (hm : (BitVec.ofNat 64 m).toNat = m) (h : m ≤ b.toNat) :
    evalCond .geu (b.setWidth 64) (BitVec.ofNat 64 m) = true := by
  have hult : (b.setWidth 64).ult (BitVec.ofNat 64 m) = false := by
    have e : (b.setWidth 64).ult (BitVec.ofNat 64 m)
        = decide ((b.setWidth 64).toNat < (BitVec.ofNat 64 m).toNat) := rfl
    rw [e, sw, hm]; exact decide_eq_false (by omega)
  simp only [evalCond, hult, Bool.not_false]

theorem geu_false {b : Byte} {m : Nat} (hm : (BitVec.ofNat 64 m).toNat = m) (h : b.toNat < m) :
    evalCond .geu (b.setWidth 64) (BitVec.ofNat 64 m) = false := by
  have hult : (b.setWidth 64).ult (BitVec.ofNat 64 m) = true := by
    have e : (b.setWidth 64).ult (BitVec.ofNat 64 m)
        = decide ((b.setWidth 64).toNat < (BitVec.ofNat 64 m).toNat) := rfl
    rw [e, sw, hm]; rw [decide_eq_true_eq]; omega
  simp only [evalCond, hult]; rfl

-- the concrete constants used by the digit check (`48`, `58`) and the overflow guard (`6`):
theorem tn48 : ((48 : Word)).toNat = 48 := by decide
theorem tn58 : ((58 : Word)).toNat = 58 := by decide
theorem tn6  : ((6  : Word)).toNat = 6  := by decide

theorem digit_val (b : Byte) (h : 48 ≤ b.toNat) :
    (b.setWidth 64) - 48 = BitVec.ofNat 64 (b.toNat - 48) := by bv_omega

/-! ### Threshold construction: the prelude builds `x23 = 0x1999999999999999`. -/

/-- The nibble recurrence `x := (x<<4) + 9`, iterated `n` times. -/
def nib : Word → Nat → Word
  | v, 0     => v
  | v, n + 1 => nib ((v <<< 4) + 9) n

/-- The threshold build as a clean recursive statement (`= seqs thresholdBuild`, see below). -/
def buildN : Nat → Stmt
  | 0     => .skip
  | n + 1 => .seq (.slli 23 23 4) (.seq (.addi 23 23 9) (buildN n))

/-- `buildN n` runs the nibble recurrence into `x23`, preserving every other register. -/
theorem build_step (n : Nat) (s : St) (v : Word) (hv : s.rget 23 = v) :
    ∃ s', exec (2 * n + 1) (buildN n) s = some (s', .normal)
      ∧ s'.rget 23 = nib v n
      ∧ (∀ r, r ≠ 23 → s'.rget r = s.rget r)
      ∧ s'.mem = s.mem := by
  induction n generalizing s v with
  | zero => exact ⟨s, by simp [buildN, exec], by simpa [nib] using hv, fun _ _ => rfl, rfl⟩
  | succ n ih =>
    have h9 : ((9 : BitVec 12).signExtend 64) = (9 : Word) := by decide
    have e_slli : exec (2*n+2) (.slli 23 23 4) s = some (s.rset 23 (v <<< 4), .normal) := by
      rw [exec_slli, hv]
    have e_addi : exec (2*n+1) (.addi 23 23 9) (s.rset 23 (v <<< 4))
        = some ((s.rset 23 (v <<< 4)).rset 23 ((v <<< 4) + 9), .normal) := by
      rw [exec_addi]; simp [h9]
    obtain ⟨s', he, h23, hother, hmem⟩ :=
      ih ((s.rset 23 (v <<< 4)).rset 23 ((v <<< 4) + 9)) ((v <<< 4) + 9) (by simp)
    refine ⟨s', ?_, ?_, ?_, ?_⟩
    · show exec (2*(n+1)+1) (.seq (.slli 23 23 4) (.seq (.addi 23 23 9) (buildN n))) s
            = some (s', .normal)
      rw [show 2*(n+1)+1 = (2*n+2)+1 from by omega, exec_seq_normal _ _ _ _ _ e_slli,
          show 2*n+2 = (2*n+1)+1 from rfl, exec_seq_normal _ _ _ _ _ e_addi]
      exact he
    · rw [h23]; simp [nib]
    · intro r hr; rw [hother r hr, rget_rset_ne _ _ _ _ hr, rget_rset_ne _ _ _ _ hr]
    · rw [hmem]; simp

/-- `seqs thresholdBuild = buildN 15`: the actual prelude's build equals the clean form. -/
theorem thresholdBuild_eq : seqs thresholdBuild = buildN 15 := by rfl

/-- The build, applied to `x23 = 1`, yields the overflow threshold `(2^64-1)/10`. -/
theorem nib_15 : nib 1 15 = BitVec.ofNat 64 0x1999999999999999 := by decide

end LowIR.Ctrl.Strtoull2
