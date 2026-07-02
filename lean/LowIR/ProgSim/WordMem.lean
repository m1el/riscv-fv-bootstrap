/-
  LowIR.ProgSim.WordMem — the 64-bit little-endian load/store algebra on the
  trusted `Rv64i.State` (RESUME-PROGSIM Phase 3 primitives). These are the
  reusable heart of the "slot facts": the machine keeps each IL register in an
  8-byte frame slot, so `compile_sim` needs (a) `sd` then `ld` at the same slot
  round-trips, and (b) a store to one slot leaves every disjoint slot (and the
  saved ra, and const data) untouched.

  Proof note: `bv_decide` in this toolchain (Lean 4.30) cannot handle `>>>`
  (right shift), so the byte-reconstruction is done by `getLsbD` extensionality.
  The reusable lemma is `byte_bit` (one shifted byte, one window); the round-trip
  is then just the OR of eight windows tiling `[0, 64)`, closed by `omega`. Two
  gotchas the fast proof turns on: `omega` rejects a *Bool*-valued goal, so the
  `Bool` equation is turned into a `Prop` via `Bool.eq_iff_iff` first; and that
  `rw` leaves an `↔ True` wrapper `omega` cannot strip, so `iff_true` must be in
  the `simp` set. The store addresses `a … a+7` differ by DISTINCT `BitVec`
  literals, so they are automatically pairwise distinct — the round-trip needs no
  no-overflow hypothesis; only the disjoint case (two independent bases) does.
-/
import Hex0.Rv64i

namespace Rv64i

open Rv64i (Word Byte)

/-- The `i`-th bit of the shifted byte `((v >>> c).setWidth 8).setWidth 64 <<< c`
    (i.e. byte `c` of `v` written back at bit offset `c`): it equals `v`'s bit `i`
    exactly when `i` lies in the byte's window `[c, c+8)` (and in range). This is
    the single reusable fact behind the little-endian reconstruction — proving it
    once, per byte, keeps the round-trip a handful of `omega`s instead of a
    128-way bit blast. Bit-level (`getLsbD`) because `bv_decide` cannot see `>>>`. -/
theorem byte_bit (v : Word) (c i : Nat) :
    (((v >>> c).setWidth 8).setWidth 64 <<< c).getLsbD i
      = (decide (i < 64) && decide (c ≤ i) && decide (i < c + 8) && v.getLsbD i) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : c ≤ i
  · -- inside/above the window: normalise `c + (i - c)` to `i`, then it is a pure
    -- `decide`-arith identity once the (shared) data bit is case-split off.
    rw [Nat.add_sub_cancel' h]
    cases v.getLsbD i <;> simp only [Bool.and_true, Bool.and_false] <;>
      first
        | rfl
        | (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', decide_eq_false_iff_not]; omega)
  · -- below the window (`i < c`): both guards are false, so both sides are `false`.
    have hlt : i < c := Nat.not_le.mp h; simp [hlt, h]

/-- **Round-trip**: storing the word `v` at `a` and loading it straight back
    returns `v`. (The eight byte addresses `a … a+7` differ by distinct literals,
    hence are pairwise distinct with no overflow side condition.) -/
@[simp] theorem loadWord_storeWord_same (s : State) (a v : Word) :
    (s.storeWord a v).loadWord a = v := by
  simp only [State.storeWord, State.loadWord, State.storeByte]
  simp
  apply BitVec.eq_of_getLsbD_eq; intro i
  -- `byte_bit` turns each of the eight OR-ed bytes into `window_k ∧ v.getLsbD i`;
  -- the OR of the windows tiles `[0, 64)`, so each side agrees bit-for-bit.
  simp only [BitVec.getLsbD_or, byte_bit, BitVec.getLsbD_setWidth]
  intro hi
  cases v.getLsbD i <;> simp only [Bool.and_true, Bool.and_false, Bool.or_false] <;>
    first
      | rfl
      | (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
          iff_true]; omega)

/-- A `storeWord` at `a` leaves `mem x` untouched for any `x` outside the eight
    stored addresses (stated with the exact literal forms so `simp` fires). -/
theorem storeWord_mem_of_ne (s : State) (a v x : Word)
    (h0 : x ≠ a) (h1 : x ≠ a+1) (h2 : x ≠ a+2) (h3 : x ≠ a+3)
    (h4 : x ≠ a+4) (h5 : x ≠ a+5) (h6 : x ≠ a+6) (h7 : x ≠ a+7) :
    (s.storeWord a v).mem x = s.mem x := by
  simp only [State.storeWord, State.storeByte, h0, h1, h2, h3, h4, h5, h6, h7, if_false]

/-- The usable form: `storeWord a` touches only the byte range `[a, a+8)`; any
    `x` strictly below `a` or at/after `a+8` is preserved (no wrap: `a+8 ≤ 2⁶⁴`). -/
theorem storeWord_mem_outside (s : State) (a v x : Word)
    (hwa : a.toNat + 8 ≤ 2^64)
    (hx : x.toNat + 1 ≤ a.toNat ∨ a.toNat + 8 ≤ x.toNat) :
    (s.storeWord a v).mem x = s.mem x := by
  refine storeWord_mem_of_ne s a v x ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (intro heq; have ht := congrArg BitVec.toNat heq
     simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow] at ht; omega)

/-- **Disjointness**: a `storeWord` at `a` does not disturb a `loadWord` at `a'`
    when the two 8-byte ranges `[a, a+8)` and `[a', a'+8)` do not overlap (both
    wrap-free). The load's eight byte reads all fall outside the stored range. -/
theorem loadWord_storeWord_disjoint (s : State) (a a' v : Word)
    (hwa : a.toNat + 8 ≤ 2^64) (hwa' : a'.toNat + 8 ≤ 2^64)
    (hd : a.toNat + 8 ≤ a'.toNat ∨ a'.toNat + 8 ≤ a.toNat) :
    (s.storeWord a v).loadWord a' = s.loadWord a' := by
  have key : ∀ y : Word, y.toNat + 1 ≤ a.toNat ∨ a.toNat + 8 ≤ y.toNat →
      (s.storeWord a v).mem y = s.mem y := fun y hy => storeWord_mem_outside s a v y hwa hy
  simp only [State.loadWord]
  rw [key a' (by omega), key (a'+1) ?_, key (a'+2) ?_, key (a'+3) ?_, key (a'+4) ?_,
      key (a'+5) ?_, key (a'+6) ?_, key (a'+7) ?_]
  all_goals (
    simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
    omega)

end Rv64i
