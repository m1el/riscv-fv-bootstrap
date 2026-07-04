/-
  strtoull (base-10 core) correctness — and the proof-ergonomics finding for the new
  control flow.

  The headline: the reasoning primitives for `break`/`block`/`ret` are *trivial*. Each
  is a one-line `by simp [exec]` equation (below): a `block` catching `brk 0` becomes
  `normal`, a `while` passing `brk` through, a `seq` short-circuiting on `brk`. So the
  outcome machinery costs almost nothing to reason about — it just adds a few uniform
  equations alongside the `normal` ones we already used for strlen.

  The functional proof (`strtoull10_correct`) is then a `digit_loop` invariant +
  induction on the number of leading digits — the same shape as `strlen`'s loop lemma,
  with two additions: the accumulator step `acc*10 = (acc<<3)+(acc<<1)` (a BitVec
  identity), and the terminating iteration returning `brk 0` (caught by the `block`).
  Stated with the invariant here; the induction is deferred (`sorry`), backed by the
  executable certification `strtoull10_matches_spec`.
-/
import LowIR.Strlen.Ctrl
import LowIR.Strtoull.Wrapping

namespace LowIR.Ctrl

open Rv64i (Word Byte)

/-! ### The new-outcome exec equations — each a one-liner. This is the ergonomics result. -/

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

/-! ### Correctness statement + invariant (induction deferred).

    `digit_loop` invariant (the deferred work): for the body
      `seq (lbu c) (seq (ife c<'0' → brk) (seq (ife '9'<c → brk) (acc-update; cursor++)))`,
    indexed by `d` = number of leading digit bytes from `cur`:
      • registers x20='0', x21='9', x16=1 fixed; x5 = cur, x12 = acc;
      • `∀ j < d`, `mem (cur + j)` is a digit byte; `mem (cur + d)` is a non-digit;
      • the loop runs `d` normal iterations (each `acc := acc*10 + digit`, `cur++`),
        then iteration `d` loads the non-digit, takes an `ife … (brkB 0)` branch, and
        the body returns `brk 0` (via `exec_seq_brk`), which the `while` passes up
        (`exec_while_brk`) and the surrounding `block` catches (`exec_block_catch`).
      • result: `x12 = accFold acc (the d digit bytes)` and `x5 = cur + d`.
    The arithmetic per step reduces by `acc_times_ten` + a `digit = ofNat (b.toNat-48)`
    fact (`bv_omega` from `48 ≤ b.toNat ≤ 57`). Identical induction shape to `strlen_loop`.

    `strtoull10_correct` then runs the const/init prelude (straight-line, like strlen's)
    into the loop-entry state and reads off `accFold 0 (inp.takeWhile isDig) = strtoullSpec inp`. -/
-- (the real `strtoull10_correct` is proved in `CtrlStrtoull10Proof.lean`)

end LowIR.Ctrl
