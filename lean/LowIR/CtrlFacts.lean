/-
  LowIR.Ctrl proof foundation — the generic exec/outcome equations for the
  clocked big-step semantics of `LowIR.Ctrl`, plus fuel monotonicity. Every
  Ctrl-level program proof (strlen, strtoull, hex0) reuses these; this is the
  LowIR analog of `LowSSA.ExecFacts`.

  Each `exec_*` equation is a one-liner `by simp [exec]` — the value is having
  them named and in one place. Two flavors:

    • the "normal" equations (`exec_addi`/`sub`/`lbu`, `exec_seq_normal`,
      `exec_while_step`/`done`) — straight-line ops and loop progress; and
    • the outcome-threading equations (`brk`/`cont`/`ret` through
      `seq`/`block`/`while`/`call`) — the break/continue/return machinery. The
      ergonomics result: reasoning about the outcome layer costs almost nothing,
      it just adds a few uniform equations alongside the `normal` ones.

  `exec_mono`/`exec_mono_le` (more fuel never changes a `some` result) let every
  lemma return an existential fuel and be combined without exact-fuel arithmetic.
-/
import LowIR.Ctrl

namespace LowIR.Ctrl

open Rv64i (Word Byte)

/-! ### Normal-outcome exec equations — straight-line ops and loop progress. -/

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

/-! ### Outcome-threading exec equations (break / continue / return) — each a one-liner. -/

theorem exec_slli (f rd rs sh : Nat) (s : St) :
    exec (f+1) (.slli rd rs sh) s = some (s.rset rd (s.rget rs <<< sh), .normal) := by simp [exec]

theorem exec_add (f rd r1 r2 : Nat) (s : St) :
    exec (f+1) (.add rd r1 r2) s = some (s.rset rd (s.rget r1 + s.rget r2), .normal) := by simp [exec]

theorem exec_orr (f rd r1 r2 : Nat) (s : St) :
    exec (f+1) (.orr rd r1 r2) s = some (s.rset rd (s.rget r1 ||| s.rget r2), .normal) := by simp [exec]

theorem exec_brkB (f k : Nat) (s : St) :
    exec (f+1) (.brkB k) s = some (s, .brk k) := by simp [exec]

theorem exec_ret (f : Nat) (s : St) : exec (f+1) .ret s = some (s, .ret) := by simp [exec]

/-- `seq` short-circuits on a break (the heart of the flat error cascade). -/
theorem exec_seq_brk (f : Nat) (a b : Stmt) (s s' : St) (k : Nat)
    (h : exec f a s = some (s', .brk k)) :
    exec (f+1) (.seq a b) s = some (s', .brk k) := by simp [exec, h]

/-- `seq` short-circuits on a return. -/
theorem exec_seq_ret (f : Nat) (a b : Stmt) (s s' : St)
    (h : exec f a s = some (s', .ret)) :
    exec (f+1) (.seq a b) s = some (s', .ret) := by simp [exec, h]

/-- a `block` catches `brk 0` and turns it into normal completion. -/
theorem exec_block_catch (f : Nat) (body : Stmt) (s s' : St)
    (h : exec f body s = some (s', .brk 0)) :
    exec (f+1) (.block body) s = some (s', .normal) := by simp [exec, h]

/-- a `while` passes a break straight through (loops are transparent to `brkB`). -/
theorem exec_while_brk (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St) (k : Nat)
    (hc : evalCond c (s.rget a) (s.rget b) = true) (hb : exec f body s = some (s', .brk k)) :
    exec (f+1) (.while c a b body) s = some (s', .brk k) := by simp [exec, hc, hb]

theorem exec_ife_then (f : Nat) (c : Cond) (a b : Reg) (t e : Stmt) (s : St)
    (h : evalCond c (s.rget a) (s.rget b) = true) :
    exec (f+1) (.ife c a b t e) s = exec f t s := by simp [exec, h]

theorem exec_ife_else (f : Nat) (c : Cond) (a b : Reg) (t e : Stmt) (s : St)
    (h : evalCond c (s.rget a) (s.rget b) = false) :
    exec (f+1) (.ife c a b t e) s = exec f e s := by simp [exec, h]

/-- The accumulator step is `*10`: `(acc<<3) + (acc<<1) = acc*10`. -/
theorem acc_times_ten (acc : Word) : (acc <<< 3) + (acc <<< 1) = acc * 10 := by
  bv_omega

/-! ### The remaining one-layer exec equations (needed for fuel monotonicity). -/

theorem exec_seq_cont (f : Nat) (a b : Stmt) (s s' : St) (k : Nat)
    (h : exec f a s = some (s', .cont k)) :
    exec (f+1) (.seq a b) s = some (s', .cont k) := by simp [exec, h]

theorem exec_seq_none (f : Nat) (a b : Stmt) (s : St) (h : exec f a s = none) :
    exec (f+1) (.seq a b) s = none := by simp [exec, h]

theorem exec_block_normal (f : Nat) (body : Stmt) (s s' : St)
    (h : exec f body s = some (s', .normal)) :
    exec (f+1) (.block body) s = some (s', .normal) := by simp [exec, h]

theorem exec_block_brkS (f : Nat) (body : Stmt) (s s' : St) (k : Nat)
    (h : exec f body s = some (s', .brk (k+1))) :
    exec (f+1) (.block body) s = some (s', .brk k) := by simp [exec, h]

theorem exec_block_cont (f : Nat) (body : Stmt) (s s' : St) (k : Nat)
    (h : exec f body s = some (s', .cont k)) :
    exec (f+1) (.block body) s = some (s', .cont k) := by simp [exec, h]

theorem exec_block_ret (f : Nat) (body : Stmt) (s s' : St)
    (h : exec f body s = some (s', .ret)) :
    exec (f+1) (.block body) s = some (s', .ret) := by simp [exec, h]

theorem exec_block_none (f : Nat) (body : Stmt) (s : St) (h : exec f body s = none) :
    exec (f+1) (.block body) s = none := by simp [exec, h]

theorem exec_while_none (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true) (hb : exec f body s = none) :
    exec (f+1) (.while c a b body) s = none := by simp [exec, hc, hb]

theorem exec_while_cont0 (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true) (hb : exec f body s = some (s', .cont 0)) :
    exec (f+1) (.while c a b body) s = exec f (.while c a b body) s' := by simp [exec, hc, hb]

theorem exec_while_contS (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St) (k : Nat)
    (hc : evalCond c (s.rget a) (s.rget b) = true) (hb : exec f body s = some (s', .cont (k+1))) :
    exec (f+1) (.while c a b body) s = some (s', .cont k) := by simp [exec, hc, hb]

theorem exec_while_ret (f : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true) (hb : exec f body s = some (s', .ret)) :
    exec (f+1) (.while c a b body) s = some (s', .ret) := by simp [exec, hc, hb]

/-- A call whose callee falls off the end (`.normal`) continues normally. -/
theorem exec_call_normal (f : Nat) (g : Stmt) (s s' : St) (h : exec f g s = some (s', .normal)) :
    exec (f+1) (.call g) s = some (s', .normal) := by simp [exec, h]

/-- A call whose callee `ret`s: the `ret` is caught and the caller continues normally. -/
theorem exec_call_ret (f : Nat) (g : Stmt) (s s' : St) (h : exec f g s = some (s', .ret)) :
    exec (f+1) (.call g) s = some (s', .normal) := by simp [exec, h]

theorem exec_call_brk (f : Nat) (g : Stmt) (s s' : St) (k : Nat) (h : exec f g s = some (s', .brk k)) :
    exec (f+1) (.call g) s = some (s', .brk k) := by simp [exec, h]

theorem exec_call_cont (f : Nat) (g : Stmt) (s s' : St) (k : Nat) (h : exec f g s = some (s', .cont k)) :
    exec (f+1) (.call g) s = some (s', .cont k) := by simp [exec, h]

theorem exec_call_none (f : Nat) (g : Stmt) (s : St) (h : exec f g s = none) :
    exec (f+1) (.call g) s = none := by simp [exec, h]

/-! ### Fuel monotonicity — more fuel never changes a `some` result.

    The key enabler for composing clocked-exec results without exact-fuel arithmetic:
    every lemma can return an *existential* fuel, and `exec_mono_le` bumps any two
    results up to a common fuel before combining (e.g. in a `while` step, where the
    body and the recursive loop must share one fuel). Proved via the one-layer exec
    equations so the inner recursive calls are never accidentally unfolded. -/

theorem exec_mono (f : Nat) : ∀ (stmt : Stmt) (s : St) (r : St × Outcome),
    exec f stmt s = some r → exec (f+1) stmt s = some r := by
  induction f with
  | zero => intro stmt s r h; rw [show exec 0 stmt s = none from rfl] at h; simp at h
  | succ f ih =>
    intro stmt s r h
    cases stmt with
    | skip => simpa only [exec] using h
    | addi => simpa only [exec] using h
    | add => simpa only [exec] using h
    | sub => simpa only [exec] using h
    | orr => simpa only [exec] using h
    | slli => simpa only [exec] using h
    | srli => simpa only [exec] using h
    | lbu => simpa only [exec] using h
    | sb => simpa only [exec] using h
    | brkB => simpa only [exec] using h
    | contL => simpa only [exec] using h
    | ret => simpa only [exec] using h
    | seq a b =>
      cases ha : exec f a s with
      | none => rw [exec_seq_none _ _ _ _ ha] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨s', o⟩ := r'
        have ha1 := ih a s (s', o) ha
        cases o with
        | normal =>
          rw [exec_seq_normal _ _ _ _ _ ha] at h
          rw [exec_seq_normal _ _ _ _ _ ha1]; exact ih b s' r h
        | brk k =>
          rw [exec_seq_brk _ _ _ _ _ _ ha] at h
          rw [exec_seq_brk _ _ _ _ _ _ ha1]; exact h
        | cont k =>
          rw [exec_seq_cont _ _ _ _ _ _ ha] at h
          rw [exec_seq_cont _ _ _ _ _ _ ha1]; exact h
        | ret =>
          rw [exec_seq_ret _ _ _ _ _ ha] at h
          rw [exec_seq_ret _ _ _ _ _ ha1]; exact h
    | ife c a b t e =>
      cases hc : evalCond c (s.rget a) (s.rget b) with
      | false =>
        rw [exec_ife_else _ _ _ _ _ _ _ hc] at h
        rw [exec_ife_else _ _ _ _ _ _ _ hc]; exact ih e s r h
      | true =>
        rw [exec_ife_then _ _ _ _ _ _ _ hc] at h
        rw [exec_ife_then _ _ _ _ _ _ _ hc]; exact ih t s r h
    | block body =>
      cases hb : exec f body s with
      | none => rw [exec_block_none _ _ _ hb] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨s', o⟩ := r'
        have hb1 := ih body s (s', o) hb
        cases o with
        | normal =>
          rw [exec_block_normal _ _ _ _ hb] at h
          rw [exec_block_normal _ _ _ _ hb1]; exact h
        | brk k => cases k with
          | zero =>
            rw [exec_block_catch _ _ _ _ hb] at h
            rw [exec_block_catch _ _ _ _ hb1]; exact h
          | succ k =>
            rw [exec_block_brkS _ _ _ _ _ hb] at h
            rw [exec_block_brkS _ _ _ _ _ hb1]; exact h
        | cont k =>
          rw [exec_block_cont _ _ _ _ _ hb] at h
          rw [exec_block_cont _ _ _ _ _ hb1]; exact h
        | ret =>
          rw [exec_block_ret _ _ _ _ hb] at h
          rw [exec_block_ret _ _ _ _ hb1]; exact h
    | «while» c a b body =>
      cases hc : evalCond c (s.rget a) (s.rget b) with
      | false =>
        rw [exec_while_done _ _ _ _ _ _ hc] at h
        rw [exec_while_done _ _ _ _ _ _ hc]; exact h
      | true =>
        cases hbody : exec f body s with
        | none => rw [exec_while_none _ _ _ _ _ _ hc hbody] at h; exact absurd h (by simp)
        | some r' =>
          obtain ⟨s', o⟩ := r'
          have hb1 := ih body s (s', o) hbody
          cases o with
          | normal =>
            rw [exec_while_step _ _ _ _ _ _ _ hc hbody] at h
            rw [exec_while_step _ _ _ _ _ _ _ hc hb1]; exact ih (.while c a b body) s' r h
          | cont k => cases k with
            | zero =>
              rw [exec_while_cont0 _ _ _ _ _ _ _ hc hbody] at h
              rw [exec_while_cont0 _ _ _ _ _ _ _ hc hb1]; exact ih (.while c a b body) s' r h
            | succ k =>
              rw [exec_while_contS _ _ _ _ _ _ _ _ hc hbody] at h
              rw [exec_while_contS _ _ _ _ _ _ _ _ hc hb1]; exact h
          | brk k =>
            rw [exec_while_brk _ _ _ _ _ _ _ _ hc hbody] at h
            rw [exec_while_brk _ _ _ _ _ _ _ _ hc hb1]; exact h
          | ret =>
            rw [exec_while_ret _ _ _ _ _ _ _ hc hbody] at h
            rw [exec_while_ret _ _ _ _ _ _ _ hc hb1]; exact h
    | call g =>
      cases hg : exec f g s with
      | none => rw [exec_call_none _ _ _ hg] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨s', o⟩ := r'
        have hg1 := ih g s (s', o) hg
        cases o with
        | normal =>
          rw [exec_call_normal _ _ _ _ hg] at h; rw [exec_call_normal _ _ _ _ hg1]; exact h
        | ret =>
          rw [exec_call_ret _ _ _ _ hg] at h; rw [exec_call_ret _ _ _ _ hg1]; exact h
        | brk k =>
          rw [exec_call_brk _ _ _ _ _ hg] at h; rw [exec_call_brk _ _ _ _ _ hg1]; exact h
        | cont k =>
          rw [exec_call_cont _ _ _ _ _ hg] at h; rw [exec_call_cont _ _ _ _ _ hg1]; exact h

theorem exec_mono_le {f f' : Nat} (hle : f ≤ f') {stmt : Stmt} {s : St} {r : St × Outcome}
    (he : exec f stmt s = some r) : exec f' stmt s = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => exact he
  | succ k ih => rw [show f + (k+1) = (f+k)+1 from rfl]; exact exec_mono (f+k) stmt s r ih

end LowIR.Ctrl
