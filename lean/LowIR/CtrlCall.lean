/-
  Calls in LowIR.Ctrl — a worked example of modular, disjointness-aware reasoning
  ACROSS a call boundary.

  `.call g` runs the callee body `g` and catches its `ret` (turning it into the caller's
  `.normal`), so it is a genuine function-return boundary, not just inlining.

  The example: a caller that *writes to `dst`* and then *calls a leaf function to read `src`*.
  For the callee to observe the original `src` byte, the prior write must not have disturbed
  it — i.e. the caller's write footprint (`dst`) must be DISJOINT from the callee's read
  footprint (`src`). We discharge that with the borrow layer (`Slice`/`Disjoint`/
  `storeByte_preserves`), and we reason about the callee MODULARLY via its spec — never
  unfolding its body at the call site.
-/
import LowIR.CtrlHex0Proof

namespace LowIR.Ctrl.Call

open LowIR.Ctrl
open LowIR.Ctrl.Hex0
open Rv64i (Word Byte)

set_option linter.unusedSimpArgs false

/-! ### The callee: a leaf function that loads the byte at `x10` into `x12`. -/

def loadByteFn : Stmt := .lbu 12 10 0

/-- Callee spec: reads `mem[x10]` (a *shared* borrow of one byte), writes `x12`, and leaves
    memory untouched (its frame is all of `mem`). One layer of `exec`, no recursion. -/
theorem loadByteFn_spec (s : St) :
    exec 1 loadByteFn s = some (s.rset 12 ((s.mem (s.rget 10)).setWidth 64), .normal) := by
  show exec 1 (.lbu 12 10 0) s = _
  rw [exec_lbu]; simp [zero_signExtend, wadd_zero, St.loadByte]

/-! ### The caller: write `x13`'s low byte to `mem[x11]`, then CALL the callee to read `mem[x10]`. -/

def writeThenLoad : Stmt := .seq (.sb 11 13 0) (.call loadByteFn)

/-- Caller correctness, reasoning **across the call**:

    `x10 = src`, `x11 = dst`, and the source/dest byte regions are DISJOINT. Then after the
    whole thing, the value the callee loaded into `x12` is the *original* `src` byte — the
    prior write to `dst` did not disturb it — and `src` itself is unchanged.

    The callee is used only through `loadByteFn_spec`; disjointness across the call is exactly
    what lets its precondition ("`src` still holds its original byte") survive the caller's
    write to `dst`. -/
theorem writeThenLoad_spec (s : St) (src dst : Word)
    (h10 : s.rget 10 = src) (h11 : s.rget 11 = dst)
    (hdisj : Disjoint ⟨src, 1⟩ ⟨dst, 1⟩) :
    ∃ st', exec 3 writeThenLoad s = some (st', .normal)
      ∧ st'.rget 12 = (s.mem src).setWidth 64
      ∧ st'.mem src = s.mem src := by
  -- the prior store lands at `dst`
  have hsb : exec 2 (.sb 11 13 0) s
      = some (s.storeByte dst ((s.rget 13).setWidth 8), .normal) := by
    rw [exec_sb]; simp [h11, zero_signExtend, wadd_zero]
  -- the write to `dst` preserves the byte at `src` (disjoint regions)
  have hsrc : (s.storeByte dst ((s.rget 13).setWidth 8)).mem src = s.mem src :=
    storeByte_preserves (s := ⟨src, 1⟩)
      (fun hh => hdisj dst hh ⟨0, Nat.one_pos, by bv_omega⟩) ⟨0, Nat.one_pos, by bv_omega⟩
  -- the callee still reads `src`, and now gets the original byte
  have hr10 : (s.storeByte dst ((s.rget 13).setWidth 8)).rget 10 = src := by
    rw [rget_storeByte, h10]
  have hcall : exec 2 (.call loadByteFn) (s.storeByte dst ((s.rget 13).setWidth 8))
      = some ((s.storeByte dst ((s.rget 13).setWidth 8)).rset 12 ((s.mem src).setWidth 64), .normal) := by
    rw [exec_call_normal _ _ _ _ (loadByteFn_spec _), hr10, hsrc]
  refine ⟨(s.storeByte dst ((s.rget 13).setWidth 8)).rset 12 ((s.mem src).setWidth 64), ?_, ?_, ?_⟩
  · show exec 3 writeThenLoad s = _
    rw [show (3:Nat) = 2+1 from rfl]
    unfold writeThenLoad
    rw [exec_seq_normal _ _ _ _ _ hsb]; exact hcall
  · rw [rget_rset_eq _ _ _ (by decide : (12:Reg) ≠ 0)]
  · simp only [rset_mem]; exact hsrc

end LowIR.Ctrl.Call
