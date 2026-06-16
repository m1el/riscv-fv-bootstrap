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
import LowIR.CtrlStrlen
import LowIR.CtrlStrtoull

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
theorem strtoull10_correct (inp : List Byte) :
    ∃ s, run (8 * inp.length + 32) Strtoull.strtoull10 (Strtoull.strtoull10State inp) = some s
      ∧ s.rget 12 = Strtoull.strtoullSpec inp := by
  sorry   -- wrapping-semantics proof; superseded by the conformant version (CtrlStrtoull2)

end LowIR.Ctrl
