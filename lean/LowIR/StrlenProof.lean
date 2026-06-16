/-
  T2 for `strlen` — functional correctness at the STRUCTURED altitude, sorry-free.

  The payoff of the IL design: the proof is a `while`-invariant + induction on the
  distance to the first NUL. No program counter, no instruction decode, no branch
  offsets — contrast the ~3400-line flat-PC `Hex0/Refine.lean`.

  `strlen` performs no stores (memory is invariant), and we take the loop fuel as
  exactly `n + 2`, so the inductive step's recursive `while` call matches the IH
  fuel exactly — no fuel-monotonicity lemma is needed.

  Core-Lean only (no Mathlib): `simp` (+ numeral simprocs), `omega`, `bv_omega`,
  `decide`, `by_cases`.
-/
import LowIR

set_option linter.unusedSimpArgs false

namespace LowIR

open Rv64i (Word Byte)

/-! ### Register bookkeeping. All register indices are literals, so simp's
    `Nat.reduceEq` simproc discharges the `i ≠ j` side conditions automatically. -/

@[simp] theorem rset_mem (s : St) (i : Reg) (v : Word) : (s.rset i v).mem = s.mem := by
  unfold St.rset; split <;> rfl

@[simp] theorem rget_zero (s : St) : s.rget 0 = 0 := by simp [St.rget]

@[simp] theorem rget_rset_eq (s : St) (i : Reg) (v : Word) (h : i ≠ 0) :
    (s.rset i v).rget i = v := by
  unfold St.rset St.rget; rw [if_neg h, if_neg h]; simp

@[simp] theorem rget_rset_ne (s : St) (i j : Reg) (v : Word) (h : j ≠ i) :
    (s.rset i v).rget j = s.rget j := by
  by_cases hi : i = 0
  · subst hi; simp [St.rset]
  · by_cases hj : j = 0
    · subst hj; simp [St.rget]
    · unfold St.rset St.rget
      rw [if_neg hi, if_neg hj, if_neg hj]
      simp only []
      rw [if_neg h]

@[simp] theorem loadByte_eq (s : St) (a : Word) : s.loadByte a = s.mem a := rfl

@[simp] theorem some_bind' {α β} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

/-! ### One-step `exec` equations (peel the clock by one). -/

theorem exec_seq (f : Nat) (a b : Stmt) (s : St) :
    exec (f+1) (.seq a b) s = (exec f a s).bind (exec f b) := by simp [exec]

theorem exec_addi (f rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec (f+1) (.addi rd rs imm) s = some (s.rset rd (s.rget rs + imm.signExtend 64)) := by
  simp [exec]

theorem exec_lbu (f rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec (f+1) (.lbu rd rs imm) s
      = some (s.rset rd ((s.loadByte (s.rget rs + imm.signExtend 64)).setWidth 64)) := by
  simp [exec]

theorem exec_sub (f rd r1 r2 : Nat) (s : St) :
    exec (f+1) (.sub rd r1 r2) s = some (s.rset rd (s.rget r1 - s.rget r2)) := by simp [exec]

theorem exec_while (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s : St) :
    exec (f+1) (.while c a b body) s
      = (if evalCond c (s.rget a) (s.rget b)
         then (exec f body s).bind (exec f (.while c a b body))
         else some s) := by simp [exec]

/-! ### Arithmetic / condition facts. -/

theorem one_signExtend : (1 : BitVec 12).signExtend 64 = (1 : Word) := by decide

theorem zero_signExtend : (0 : BitVec 12).signExtend 64 = (0 : Word) := by decide

theorem wadd_zero (x : Word) : x + (0 : Word) = x := by bv_omega

theorem wzero_add (x : Word) : (0 : Word) + x = x := by bv_omega

theorem cur_zero (cur : Word) : cur + BitVec.ofNat 64 0 = cur := by bv_omega

theorem cur_step (cur : Word) (k : Nat) :
    cur + BitVec.ofNat 64 (k+1) = (cur + 1) + BitVec.ofNat 64 k := by bv_omega

/-- The loop condition `(byte ≥u 1)` is true exactly when the byte is non-NUL. -/
theorem cond_true_ne (b : Byte) (h : b ≠ 0) :
    evalCond .geu (b.setWidth 64) 1 = true := by
  have hbn : b.toNat ≠ 0 := fun hh => h (by bv_omega)
  have hsw : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth]; have := b.isLt; omega
  have h1 : (1 : Word).toNat = 1 := by decide
  have hult : (b.setWidth 64).ult 1 = false := by
    have e : (b.setWidth 64).ult 1 = decide ((b.setWidth 64).toNat < (1 : Word).toNat) := rfl
    rw [e, hsw, h1]; exact decide_eq_false (by omega)
  simp only [evalCond, hult, Bool.not_false]

theorem cond_false_zero : evalCond .geu ((0 : Byte).setWidth 64) 1 = false := by decide

/-- The loop body of `strlen`. -/
def lbody : Stmt := .seq (.addi 5 5 1) (.lbu 6 5 0)

/-! ### The loop lemma — fuel `n + 2` exactly, induction on `n`. -/

theorem strlen_loop (n : Nat) :
    ∀ (st : St) (cur : Word),
      st.rget 5 = cur → st.rget 7 = 1 → st.rget 6 = (st.mem cur).setWidth 64 →
      (∀ k, k < n → st.mem (cur + BitVec.ofNat 64 k) ≠ 0) →
      st.mem (cur + BitVec.ofNat 64 n) = 0 →
      ∃ st', exec (n + 2) (.while .geu 6 7 lbody) st = some st'
        ∧ st'.rget 5 = cur + BitVec.ofNat 64 n
        ∧ st'.rget 10 = st.rget 10
        ∧ st'.mem = st.mem := by
  induction n with
  | zero =>
    intro st cur h5 h7 h6 _ hz
    rw [cur_zero] at hz
    refine ⟨st, ?_, by rw [cur_zero]; exact h5, rfl, rfl⟩
    have hc : evalCond .geu (st.rget 6) (st.rget 7) = false := by
      rw [h6, h7, hz]; exact cond_false_zero
    rw [show (0 : Nat) + 2 = 1 + 1 from rfl, exec_while, if_neg (by simp [hc])]
  | succ n ih =>
    intro st cur h5 h7 h6 hpre hz
    have hb0 : st.mem cur ≠ 0 := by have := hpre 0 (by omega); rwa [cur_zero] at this
    have hcond : evalCond .geu (st.rget 6) (st.rget 7) = true := by
      rw [h6, h7]; exact cond_true_ne _ hb0
    rw [show n + 1 + 2 = (n + 2) + 1 from rfl, exec_while, if_pos hcond]
    -- run the body at fuel n+2 → post-body state E
    have hstep : exec (n + 2) lbody st
        = some ((st.rset 5 (cur + 1)).rset 6 ((st.mem (cur + 1)).setWidth 64)) := by
      show exec (n + 2) (.seq (.addi 5 5 1) (.lbu 6 5 0)) st = _
      rw [show n + 2 = (n + 1) + 1 from rfl, exec_seq, exec_addi]
      simp only [some_bind', h5, one_signExtend]
      rw [exec_lbu]; simp [zero_signExtend]
    rw [hstep, some_bind']
    -- facts about E (written explicitly; `set` is unavailable without Mathlib)
    have h15 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 5 = cur+1 := by simp
    have h17 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 7 = 1 := by
      simp [h7]
    have h110 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 10 = st.rget 10 := by
      simp
    have h16 : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).rget 6
        = (((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).mem (cur+1)).setWidth 64 := by
      simp
    have hpre' : ∀ k, k < n →
        ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).mem ((cur+1) + BitVec.ofNat 64 k) ≠ 0 := by
      intro k hk; simp only [rset_mem, ← cur_step]; exact hpre (k+1) (by omega)
    have hz' : ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)).mem ((cur+1) + BitVec.ofNat 64 n) = 0 := by
      simp only [rset_mem, ← cur_step]; exact hz
    obtain ⟨st', hexec', hr5, hr10, hrmem⟩ :=
      ih ((st.rset 5 (cur+1)).rset 6 ((st.mem (cur+1)).setWidth 64)) (cur+1) h15 h17 h16 hpre' hz'
    refine ⟨st', hexec', ?_, ?_, ?_⟩
    · rw [hr5, ← cur_step]
    · rw [hr10, h110]
    · rw [hrmem]; simp

/-! ### Specification and the theorem. -/

/-- `n` is the length of the NUL-terminated string at `s`: byte `n` is NUL and every
    earlier byte is non-NUL. -/
def IsLen (mem : Word → Byte) (s : Word) (n : Nat) : Prop :=
  mem (s + BitVec.ofNat 64 n) = 0 ∧ ∀ k, k < n → mem (s + BitVec.ofNat 64 k) ≠ 0

/-- **strlen is correct.** With `s` in x10 and the first NUL at offset `n`, `strlen`
    halts with the length `n` in x12. Pure structured-altitude reasoning. -/
theorem strlen_correct (st : St) (s : Word) (n : Nat)
    (h10 : st.rget 10 = s) (hlen : IsLen st.mem s n) :
    ∃ st', exec (n + 6) strlen st = some st' ∧ st'.rget 12 = BitVec.ofNat 64 n := by
  obtain ⟨hnul, hpre⟩ := hlen
  show ∃ st', exec (n + 6)
      (.seq (.addi 7 0 1) (.seq (.addi 5 10 0) (.seq (.lbu 6 5 0)
        (.seq (.while .geu 6 7 lbody) (.sub 12 5 10))))) st = some st' ∧ _
  -- peel the three preamble instructions, normalising the state after each
  rw [show n + 6 = (n + 5) + 1 from rfl, exec_seq, exec_addi]
  simp only [some_bind']
  simp [one_signExtend, wzero_add]
  rw [show n + 5 = (n + 4) + 1 from rfl, exec_seq, exec_addi]
  simp only [some_bind']
  simp [zero_signExtend, wadd_zero, h10]
  rw [show n + 4 = (n + 3) + 1 from rfl, exec_seq, exec_lbu]
  simp only [some_bind']
  simp [zero_signExtend, wadd_zero]
  rw [show n + 3 = (n + 2) + 1 from rfl, exec_seq]
  -- the loop-entry state S1 = ((rset 7 1).rset 5 s).rset 6 (mem[s])
  obtain ⟨st', hloop, hr5, hr10, _⟩ :=
    strlen_loop n (((st.rset 7 (1#64)).rset 5 s).rset 6 ((st.mem s).setWidth 64)) s
      (by simp) (by simp) (by simp)
      (fun k hk => by simpa using hpre k hk)
      (by simpa using hnul)
  rw [hloop, some_bind', exec_sub]
  refine ⟨_, rfl, ?_⟩
  have hr10s : st'.rget 10 = s := by rw [hr10]; simp [h10]
  rw [rget_rset_eq _ _ _ (by decide : (12 : Reg) ≠ 0), hr5, hr10s]
  bv_omega

end LowIR
