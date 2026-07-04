/-
  strlen re-proved on the NEW control-flow IL (`LowIR.Ctrl`), to compare proof
  ergonomics against the original (`LowIR/StrlenProof.lean`).

  Finding (recorded at the bottom): strlen uses no break/continue/ret, so the outcome
  machinery is pure overhead here — the proof is the *same shape* as before, just
  carrying a `.normal` everywhere. The control-flow IL pays off for hex0/strtoull
  (early returns), not for a single straight loop like strlen.

  Reuses the register/arith/condition lemmas from `LowIR.StrlenProof`.
-/
import LowIR.Ctrl
import LowIR.Strlen.CoreProof

set_option linter.unusedSimpArgs false

namespace LowIR.Ctrl

open Rv64i (Word Byte)

/-! ### exec equations for the new (outcome-threaded) semantics. -/

theorem exec_addi (f rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec (f+1) (.addi rd rs imm) s = some (s.rset rd (s.rget rs + imm.signExtend 64), .normal) := by
  simp [exec]

theorem exec_sub (f rd r1 r2 : Nat) (s : St) :
    exec (f+1) (.sub rd r1 r2) s = some (s.rset rd (s.rget r1 - s.rget r2), .normal) := by simp [exec]

theorem exec_lbu (f rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec (f+1) (.lbu rd rs imm) s
      = some (s.rset rd ((s.loadByte (s.rget rs + imm.signExtend 64)).setWidth 64), .normal) := by
  simp [exec]

/-- Sequence where the first part finishes `normal`. -/
theorem exec_seq_normal (f : Nat) (a b : Stmt) (s s' : St)
    (h : exec f a s = some (s', .normal)) :
    exec (f+1) (.seq a b) s = exec f b s' := by simp [exec, h]

theorem exec_while_step (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true) (hb : exec f body s = some (s', .normal)) :
    exec (f+1) (.while c a b body) s = exec f (.while c a b body) s' := by
  simp [exec, hc, hb]

theorem exec_while_done (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = false) :
    exec (f+1) (.while c a b body) s = some (s, .normal) := by simp [exec, hc]

/-! ### strlen on the new IL — same program, outcome-carrying proof. -/

def lbody : Stmt := .seq (.addi 5 5 1) (.lbu 6 5 0)

def strlen : Stmt :=
  .seq (.addi 7 0 1) <| .seq (.addi 5 10 0) <| .seq (.lbu 6 5 0) <|
  .seq (.while .geu 6 7 lbody) (.sub 12 5 10)

theorem strlen_loop (n : Nat) :
    ∀ (st : St) (cur : Word),
      st.rget 5 = cur → st.rget 7 = 1 → st.rget 6 = (st.mem cur).setWidth 64 →
      (∀ k, k < n → st.mem (cur + BitVec.ofNat 64 k) ≠ 0) →
      st.mem (cur + BitVec.ofNat 64 n) = 0 →
      ∃ st', exec (n + 2) (.while .geu 6 7 lbody) st = some (st', .normal)
        ∧ st'.rget 5 = cur + BitVec.ofNat 64 n
        ∧ st'.rget 10 = st.rget 10
        ∧ st'.mem = st.mem := by
  induction n with
  | zero =>
    intro st cur h5 h7 h6 _ hz
    rw [cur_zero] at hz
    have hc : evalCond .geu (st.rget 6) (st.rget 7) = false := by rw [h6, h7, hz]; exact cond_false_zero
    exact ⟨st, by rw [show (0:Nat)+2 = 1+1 from rfl]; exact exec_while_done _ _ _ _ _ _ hc,
           by rw [cur_zero]; exact h5, rfl, rfl⟩
  | succ n ih =>
    intro st cur h5 h7 h6 hpre hz
    have hb0 : st.mem cur ≠ 0 := by have := hpre 0 (by omega); rwa [cur_zero] at this
    have hcond : evalCond .geu (st.rget 6) (st.rget 7) = true := by rw [h6, h7]; exact cond_true_ne _ hb0
    have ha : exec (n+1) (.addi 5 5 1) st = some (st.rset 5 (cur+1), .normal) := by
      rw [exec_addi]; simp [h5, one_signExtend]
    have hstep : exec (n+2) lbody st
        = some ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64), .normal) := by
      show exec (n+2) (.seq (.addi 5 5 1) (.lbu 6 5 0)) st = _
      rw [show n+2 = (n+1)+1 from rfl, exec_seq_normal _ _ _ _ _ ha, exec_lbu]
      simp [zero_signExtend, wadd_zero]
    rw [show n+1+2 = (n+2)+1 from rfl, exec_while_step _ _ _ _ _ _ _ hcond hstep]
    have h15 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 5 = cur+1 := by simp
    have h17 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 7 = 1 := by simp [h7]
    have h110 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 10 = st.rget 10 := by simp
    have h16 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 6
        = (((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).mem (cur+1)).setWidth 64 := by simp
    have hpre' : ∀ k, k < n →
        ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).mem ((cur+1) + BitVec.ofNat 64 k) ≠ 0 := by
      intro k hk; simp only [rset_mem, ← cur_step]; exact hpre (k+1) (by omega)
    have hz' : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).mem ((cur+1) + BitVec.ofNat 64 n) = 0 := by
      simp only [rset_mem, ← cur_step]; exact hz
    obtain ⟨st', hexec', hr5, hr10, hrmem⟩ :=
      ih ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)) (cur+1) h15 h17 h16 hpre' hz'
    exact ⟨st', hexec', by rw [hr5, ← cur_step], by rw [hr10, h110], by rw [hrmem]; simp⟩

theorem strlen_correct (st : St) (s : Word) (n : Nat)
    (h10 : st.rget 10 = s) (hlen : IsLen st.mem s n) :
    ∃ st', exec (n + 6) strlen st = some (st', .normal) ∧ st'.rget 12 = BitVec.ofNat 64 n := by
  obtain ⟨hnul, hpre⟩ := hlen
  show ∃ st', exec (n + 6)
      (.seq (.addi 7 0 1) (.seq (.addi 5 10 0) (.seq (.lbu 6 5 0)
        (.seq (.while .geu 6 7 lbody) (.sub 12 5 10))))) st = some (st', .normal) ∧ _
  have h1 : exec (n+5) (.addi 7 0 1) st = some (st.rset 7 1, .normal) := by
    rw [exec_addi]; simp [one_signExtend, wzero_add]
  have h2 : exec (n+4) (.addi 5 10 0) (st.rset 7 1) = some ((st.rset 7 1).rset 5 s, .normal) := by
    rw [exec_addi]; simp [zero_signExtend, wadd_zero, h10]
  have h3 : exec (n+3) (.lbu 6 5 0) ((st.rset 7 1).rset 5 s)
      = some (((st.rset 7 1).rset 5 s).rset 6 ((st.mem s).setWidth 64), .normal) := by
    rw [exec_lbu]; simp [zero_signExtend, wadd_zero]
  rw [show n+6 = (n+5)+1 from rfl, exec_seq_normal _ _ _ _ _ h1,
      show n+5 = (n+4)+1 from rfl, exec_seq_normal _ _ _ _ _ h2,
      show n+4 = (n+3)+1 from rfl, exec_seq_normal _ _ _ _ _ h3]
  obtain ⟨st_d, hloop, hr5, hr10, _⟩ :=
    strlen_loop n (((st.rset 7 1).rset 5 s).rset 6 ((st.mem s).setWidth 64)) s
      (by simp) (by simp) (by simp) (fun k hk => by simpa using hpre k hk) (by simpa using hnul)
  rw [show n+3 = (n+2)+1 from rfl, exec_seq_normal _ _ _ _ _ hloop, exec_sub]
  refine ⟨_, rfl, ?_⟩
  have hr10s : st_d.rget 10 = s := by rw [hr10]; simp [h10]
  rw [rget_rset_eq _ _ _ (by decide : (12 : Reg) ≠ 0), hr5, hr10s]
  bv_omega

end LowIR.Ctrl
