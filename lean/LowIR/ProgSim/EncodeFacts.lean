import LowIR.Core

/-!
# Phase 1 — `decode (encode i) = i`, generically and axiom-clean

The trusted `Rv64i.decode` reads back exactly what the compiler's `encode`
emitted, for every instruction form the compiler produces (operands in range).
Until now this was only checked per-program by `native_decide` (`strlen_roundtrip`,
`denv_roundtrip`); those carry `Lean.ofReduceBool`. This file proves the round-trip
as a general theorem, **axiom-clean** (`[propext, Quot.sound]`), so Phase 2's
`Installed`-from-`progBytes` can decode the byte stream without `native_decide`.

The engine is a small, self-contained bit toolkit (the Mathlib-free stdlib taints
`Nat.and_two_pow_sub_one_eq_mod` and friends with `Classical.choice`, so we reprove
the pieces we need) culminating in `lor_window_add`: an *order-agnostic* "disjoint
OR is addition" combinator. With it, `(encode i).toNat` reduces to an explicit
arithmetic **sum** of shifted operands, and every `field` extraction closes by
`omega`.
-/

open LowIR Rv64i

namespace LowIR.ProgSim.EncodeFacts

/-! ## §1 The clean bit toolkit. -/

/-- Every low bit of `2ⁿ−1` is set (clean replacement for the `Classical`-tainted
    `Nat.testBit_two_pow_sub_one`). -/
theorem testBit_pow_two_sub_one (n : Nat) :
    ∀ i, i < n → Nat.testBit (2 ^ n - 1) i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hpow : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    cases i with
    | zero =>
      have hm : (2 ^ (n + 1) - 1) % 2 = 1 := by
        rw [hpow]; have := Nat.one_le_two_pow (n := n); omega
      rw [Nat.testBit_zero, hm]; rfl
    | succ i' =>
      have hd : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
        rw [hpow]; have := Nat.one_le_two_pow (n := n); omega
      rw [Nat.testBit_succ, hd]; exact ih i' (by omega)

/-- `(2^len - 1).testBit i = decide (i < len)`. -/
theorem testBit_mask (len i : Nat) : (2 ^ len - 1).testBit i = decide (i < len) := by
  by_cases h : i < len
  · rw [testBit_pow_two_sub_one len i h]; simp [h]
  · have hlt : (2:Nat)^len - 1 < 2 ^ i := by
      have h1 : (2:Nat)^len ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 1 ≤ (2:Nat)^len := Nat.one_le_two_pow
      omega
    rw [Nat.testBit_lt_two_pow hlt]; simp [h]

/-- Clean replacement for the `Classical`-tainted `Nat.and_two_pow_sub_one_eq_mod`. -/
theorem and_two_pow_sub_one_eq_mod (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, testBit_mask, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem and_one_eq_mod_two (x : Nat) : x &&& 1 = x % 2 := and_two_pow_sub_one_eq_mod x 1

/-- Disjoint OR is addition. -/
theorem lor_disjoint_add : ∀ (a b : Nat), a &&& b = 0 → a ||| b = a + b := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b h
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp
    · have hdiv : (a/2) &&& (b/2) = 0 := by
        have hh : (a &&& b) / 2 = a/2 &&& b/2 := Nat.and_div_two
        rw [h] at hh; exact hh.symm.trans (by rw [Nat.zero_div])
      have ihd := ih (a/2) (by omega) (b/2) hdiv
      have hlow : ¬ (a % 2 = 1 ∧ b % 2 = 1) := by
        rintro ⟨h1, h2⟩
        have hone : (a &&& b) % 2 = 1 := by
          rw [← and_one_eq_mod_two, Nat.and_assoc, and_one_eq_mod_two, h2,
              and_one_eq_mod_two, h1]
        rw [h] at hone; exact absurd hone (by decide)
      have hordiv : (a ||| b) / 2 = a/2 + b/2 := by rw [Nat.or_div_two, ihd]
      have hormod : (a ||| b) % 2 = a % 2 + b % 2 := by
        rw [← and_one_eq_mod_two, Nat.and_or_distrib_right, and_one_eq_mod_two,
            and_one_eq_mod_two]
        rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
          rw [h1, h2] <;> first | rfl | decide | (exact absurd ⟨h1, h2⟩ hlow)
      omega

/-- Windowed disjointness: `v < 2^w` and `A` has no bits in `[s, s+w)`
    (`A % 2^(s+w) < 2^s`) ⇒ `A` and `v <<< s` are bit-disjoint. Order-agnostic:
    `A` may hold bits both below `s` and at/above `s+w`. -/
theorem and_shiftLeft_window_zero (A v s w : Nat) (hv : v < 2 ^ w)
    (hA : A % 2 ^ (s + w) < 2 ^ s) : A &&& (v <<< s) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
  by_cases hlo : s ≤ i
  · by_cases hhi : i < s + w
    · have h1 : (A % 2 ^ (s + w)).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) hlo))
      rw [Nat.testBit_mod_two_pow] at h1
      simp only [hhi, decide_true, Bool.true_and] at h1
      rw [h1]; simp
    · have : v.testBit (i - s) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [this]; simp
  · simp [hlo]

/-- The uniform combinator: OR-in a windowed piece = add it. Fold pieces in ANY
    bit order (needed for the scattered S/B/J immediates). -/
theorem lor_window_add (A v s w : Nat) (hv : v < 2 ^ w) (hA : A % 2 ^ (s + w) < 2 ^ s) :
    A ||| (v <<< s) = A + v * 2 ^ s := by
  rw [lor_disjoint_add A (v <<< s) (and_shiftLeft_window_zero A v s w hv hA), Nat.shiftLeft_eq]

/-- Shifted piece on the LEFT is bit-disjoint from a low value. -/
theorem shiftLeft_and_low_zero (v s lo : Nat) (hlo : lo < 2 ^ s) : (v <<< s) &&& lo = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
  by_cases hi : s ≤ i
  · have : lo.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by omega) hi))
    rw [this]; simp
  · simp [hi]

/-- Immediate reassembly: `(v <<< s) ||| lo = v * 2^s + lo` when `lo < 2^s`.
    Exactly `decode`'s scattered-immediate `ofNat`-argument shape
    (`(funct7 <<< 5) ||| rd`, `(hi <<< k) ||| lo`). -/
theorem lor_low_add (v s lo : Nat) (hlo : lo < 2 ^ s) : (v <<< s) ||| lo = v * 2 ^ s + lo := by
  rw [lor_disjoint_add _ _ (shiftLeft_and_low_zero v s lo hlo), Nat.shiftLeft_eq]

/-- Multiplication-form windowed combinator — for chaining the `decode`-side
    B/J immediate reassembly (`simp [Nat.shiftLeft_eq]` puts every piece in
    `v * 2^s` form so the accumulator stays visible to `omega`). -/
theorem lor_mul_add (A v s w : Nat) (hv : v < 2 ^ w) (hA : A % 2 ^ (s + w) < 2 ^ s) :
    A ||| (v * 2 ^ s) = A + v * 2 ^ s := by
  have h := lor_window_add A v s w hv hA
  rwa [Nat.shiftLeft_eq] at h

/-- Field extraction against a known `toNat`: `field w lo len = (N / 2^lo) % 2^len`. -/
theorem field_of_toNat {w : BitVec 32} {N : Nat} (hw : w.toNat = N) (lo len : Nat) :
    field w lo len = (N / 2 ^ lo) % 2 ^ len := by
  unfold field; rw [hw, Nat.shiftRight_eq_div_pow, and_two_pow_sub_one_eq_mod]

/-- A masked 12-bit immediate is itself. -/
theorem mask12 (x : Nat) (h : x < 4096) : x &&& 0xFFF = x := by
  rw [show (0xFFF : Nat) = 2 ^ 12 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- `BitVec.ofNat w` of a `w`-bit value's `toNat` is that value (any width;
    the `decode`-side immediate `ofNat` is at width 12/13/21). -/
theorem ofNatW_toNat {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rw [BitVec.ofNat_toNat]; exact BitVec.setWidth_eq x

/-! ## §2 Round-trip, per constructor. -/

theorem addi_roundtrip (rd rs1 : Nat) (imm : BitVec 12) (hrd : rd < 32) (hrs1 : rs1 < 32) :
    decode (encode (.addi rd rs1 imm)) = .addi rd rs1 imm := by
  have him : imm.toNat < 4096 := imm.isLt
  have hN : (encode (.addi rd rs1 imm)).toNat
      = 19 + rd * 128 + rs1 * 32768 + imm.toNat * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, mask12 _ him]
    rw [BitVec.toNat_ofNat,
        lor_window_add 19 rd 7 5 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7) rs1 15 5 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7 + rs1 * 2^15) imm.toNat 20 12 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 12 3, hf 7 5, hf 15 5, hf 20 12,
    show (19 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^0 % 2^7 = 19 by omega,
    show (19 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^12 % 2^3 = 0 by omega,
    show (19 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^7 % 2^5 = rd by omega,
    show (19 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (19 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^20 % 2^12 = imm.toNat by omega,
    ofNatW_toNat]

theorem add_roundtrip (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    decode (encode (.add rd rs1 rs2)) = .add rd rs1 rs2 := by
  have hN : (encode (.add rd rs1 rs2)).toNat = 51 + rd * 128 + rs1 * 32768 + rs2 * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or]
    rw [BitVec.toNat_ofNat,
        lor_window_add 51 rd 7 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7) rs1 15 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 25 7, hf 12 3, hf 7 5, hf 15 5, hf 20 5, if_true, if_false, Nat.reduceEqDiff,
    show (51 + rd*128 + rs1*32768 + rs2*1048576) / 2^0 % 2^7 = 51 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576) / 2^25 % 2^7 = 0 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576) / 2^12 % 2^3 = 0 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576) / 2^7 % 2^5 = rd by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576) / 2^20 % 2^5 = rs2 by omega]

theorem sub_roundtrip (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    decode (encode (.sub rd rs1 rs2)) = .sub rd rs1 rs2 := by
  have hN : (encode (.sub rd rs1 rs2)).toNat
      = 51 + rd * 128 + rs1 * 32768 + rs2 * 1048576 + 32 * 33554432 := by
    simp only [encode, w32, List.foldl, Nat.zero_or]
    rw [BitVec.toNat_ofNat,
        lor_window_add 51 rd 7 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7) rs1 15 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7 + rs1 * 2^15 + rs2 * 2^20) 32 25 7 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 25 7, hf 12 3, hf 7 5, hf 15 5, hf 20 5, if_true, if_false, Nat.reduceEqDiff,
    show (51 + rd*128 + rs1*32768 + rs2*1048576 + 32*33554432) / 2^0 % 2^7 = 51 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576 + 32*33554432) / 2^25 % 2^7 = 32 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576 + 32*33554432) / 2^12 % 2^3 = 0 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576 + 32*33554432) / 2^7 % 2^5 = rd by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576 + 32*33554432) / 2^15 % 2^5 = rs1 by omega,
    show (51 + rd*128 + rs1*32768 + rs2*1048576 + 32*33554432) / 2^20 % 2^5 = rs2 by omega]

theorem or_roundtrip (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    decode (encode (.or rd rs1 rs2)) = .or rd rs1 rs2 := by
  have hN : (encode (.or rd rs1 rs2)).toNat
      = 51 + rd * 128 + 6 * 4096 + rs1 * 32768 + rs2 * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or]
    rw [BitVec.toNat_ofNat,
        lor_window_add 51 rd 7 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7) 6 12 3 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7 + 6 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (51 + rd * 2^7 + 6 * 2^12 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 25 7, hf 12 3, hf 7 5, hf 15 5, hf 20 5, if_true, if_false, Nat.reduceEqDiff,
    show (51 + rd*128 + 6*4096 + rs1*32768 + rs2*1048576) / 2^0 % 2^7 = 51 by omega,
    show (51 + rd*128 + 6*4096 + rs1*32768 + rs2*1048576) / 2^25 % 2^7 = 0 by omega,
    show (51 + rd*128 + 6*4096 + rs1*32768 + rs2*1048576) / 2^12 % 2^3 = 6 by omega,
    show (51 + rd*128 + 6*4096 + rs1*32768 + rs2*1048576) / 2^7 % 2^5 = rd by omega,
    show (51 + rd*128 + 6*4096 + rs1*32768 + rs2*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (51 + rd*128 + 6*4096 + rs1*32768 + rs2*1048576) / 2^20 % 2^5 = rs2 by omega]

theorem lbu_roundtrip (rd rs1 : Nat) (imm : BitVec 12) (hrd : rd < 32) (hrs1 : rs1 < 32) :
    decode (encode (.lbu rd rs1 imm)) = .lbu rd rs1 imm := by
  have him : imm.toNat < 4096 := imm.isLt
  have hN : (encode (.lbu rd rs1 imm)).toNat
      = 3 + rd * 128 + 4 * 4096 + rs1 * 32768 + imm.toNat * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, mask12 _ him]
    rw [BitVec.toNat_ofNat,
        lor_window_add 3 rd 7 5 (by omega) (by omega),
        lor_window_add (3 + rd * 2^7) 4 12 3 (by omega) (by omega),
        lor_window_add (3 + rd * 2^7 + 4 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (3 + rd * 2^7 + 4 * 2^12 + rs1 * 2^15) imm.toNat 20 12 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 12 3, hf 7 5, hf 15 5, hf 20 12,
    show (3 + rd*128 + 4*4096 + rs1*32768 + imm.toNat*1048576) / 2^0 % 2^7 = 3 by omega,
    show (3 + rd*128 + 4*4096 + rs1*32768 + imm.toNat*1048576) / 2^12 % 2^3 = 4 by omega,
    show (3 + rd*128 + 4*4096 + rs1*32768 + imm.toNat*1048576) / 2^7 % 2^5 = rd by omega,
    show (3 + rd*128 + 4*4096 + rs1*32768 + imm.toNat*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (3 + rd*128 + 4*4096 + rs1*32768 + imm.toNat*1048576) / 2^20 % 2^12 = imm.toNat by omega,
    ofNatW_toNat]

theorem ld_roundtrip (rd rs1 : Nat) (imm : BitVec 12) (hrd : rd < 32) (hrs1 : rs1 < 32) :
    decode (encode (.ld rd rs1 imm)) = .ld rd rs1 imm := by
  have him : imm.toNat < 4096 := imm.isLt
  have hN : (encode (.ld rd rs1 imm)).toNat
      = 3 + rd * 128 + 3 * 4096 + rs1 * 32768 + imm.toNat * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, mask12 _ him]
    rw [BitVec.toNat_ofNat,
        lor_window_add 3 rd 7 5 (by omega) (by omega),
        lor_window_add (3 + rd * 2^7) 3 12 3 (by omega) (by omega),
        lor_window_add (3 + rd * 2^7 + 3 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (3 + rd * 2^7 + 3 * 2^12 + rs1 * 2^15) imm.toNat 20 12 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 12 3, hf 7 5, hf 15 5, hf 20 12,
    show (3 + rd*128 + 3*4096 + rs1*32768 + imm.toNat*1048576) / 2^0 % 2^7 = 3 by omega,
    show (3 + rd*128 + 3*4096 + rs1*32768 + imm.toNat*1048576) / 2^12 % 2^3 = 3 by omega,
    show (3 + rd*128 + 3*4096 + rs1*32768 + imm.toNat*1048576) / 2^7 % 2^5 = rd by omega,
    show (3 + rd*128 + 3*4096 + rs1*32768 + imm.toNat*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (3 + rd*128 + 3*4096 + rs1*32768 + imm.toNat*1048576) / 2^20 % 2^12 = imm.toNat by omega,
    ofNatW_toNat]

theorem jalr_roundtrip (rd rs1 : Nat) (imm : BitVec 12) (hrd : rd < 32) (hrs1 : rs1 < 32) :
    decode (encode (.jalr rd rs1 imm)) = .jalr rd rs1 imm := by
  have him : imm.toNat < 4096 := imm.isLt
  have hN : (encode (.jalr rd rs1 imm)).toNat
      = 103 + rd * 128 + rs1 * 32768 + imm.toNat * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, mask12 _ him]
    rw [BitVec.toNat_ofNat,
        lor_window_add 103 rd 7 5 (by omega) (by omega),
        lor_window_add (103 + rd * 2^7) rs1 15 5 (by omega) (by omega),
        lor_window_add (103 + rd * 2^7 + rs1 * 2^15) imm.toNat 20 12 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 12 3, hf 7 5, hf 15 5, hf 20 12, if_true,
    show (103 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^0 % 2^7 = 103 by omega,
    show (103 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^12 % 2^3 = 0 by omega,
    show (103 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^7 % 2^5 = rd by omega,
    show (103 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (103 + rd*128 + rs1*32768 + imm.toNat*1048576) / 2^20 % 2^12 = imm.toNat by omega,
    ofNatW_toNat]

/-- A masked 6-bit value is itself. -/
theorem mask6 (x : Nat) (h : x < 64) : x &&& 0x3F = x := by
  rw [show (0x3F : Nat) = 2 ^ 6 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

-- ⚠ `slli`/`srli` round-trip only for `sh < 32`: the trusted `decode` reads
-- `funct7 := field w 25 7`, whose bit 25 overlaps shamt bit 5, so `sh ≥ 32`
-- decodes to `.unknown`. Phase 2 discharges `sh < 32` from the compiler.
theorem slli_roundtrip (rd rs1 sh : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : sh < 32) :
    decode (encode (.slli rd rs1 sh)) = .slli rd rs1 sh := by
  have hN : (encode (.slli rd rs1 sh)).toNat
      = 19 + rd * 128 + 1 * 4096 + rs1 * 32768 + sh * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, mask6 sh (by omega)]
    rw [BitVec.toNat_ofNat,
        lor_window_add 19 rd 7 5 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7) 1 12 3 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7 + 1 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7 + 1 * 2^12 + rs1 * 2^15) sh 20 6 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 12 3, hf 25 7, hf 7 5, hf 15 5, hf 20 6, if_true,
    show (19 + rd*128 + 1*4096 + rs1*32768 + sh*1048576) / 2^0 % 2^7 = 19 by omega,
    show (19 + rd*128 + 1*4096 + rs1*32768 + sh*1048576) / 2^12 % 2^3 = 1 by omega,
    show (19 + rd*128 + 1*4096 + rs1*32768 + sh*1048576) / 2^25 % 2^7 = 0 by omega,
    show (19 + rd*128 + 1*4096 + rs1*32768 + sh*1048576) / 2^7 % 2^5 = rd by omega,
    show (19 + rd*128 + 1*4096 + rs1*32768 + sh*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (19 + rd*128 + 1*4096 + rs1*32768 + sh*1048576) / 2^20 % 2^6 = sh by omega]

theorem srli_roundtrip (rd rs1 sh : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : sh < 32) :
    decode (encode (.srli rd rs1 sh)) = .srli rd rs1 sh := by
  have hN : (encode (.srli rd rs1 sh)).toNat
      = 19 + rd * 128 + 5 * 4096 + rs1 * 32768 + sh * 1048576 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, mask6 sh (by omega)]
    rw [BitVec.toNat_ofNat,
        lor_window_add 19 rd 7 5 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7) 5 12 3 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7 + 5 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (19 + rd * 2^7 + 5 * 2^12 + rs1 * 2^15) sh 20 6 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  simp only [decode, hf 0 7, hf 12 3, hf 25 7, hf 7 5, hf 15 5, hf 20 6, if_true,
    show (19 + rd*128 + 5*4096 + rs1*32768 + sh*1048576) / 2^0 % 2^7 = 19 by omega,
    show (19 + rd*128 + 5*4096 + rs1*32768 + sh*1048576) / 2^12 % 2^3 = 5 by omega,
    show (19 + rd*128 + 5*4096 + rs1*32768 + sh*1048576) / 2^25 % 2^7 = 0 by omega,
    show (19 + rd*128 + 5*4096 + rs1*32768 + sh*1048576) / 2^7 % 2^5 = rd by omega,
    show (19 + rd*128 + 5*4096 + rs1*32768 + sh*1048576) / 2^15 % 2^5 = rs1 by omega,
    show (19 + rd*128 + 5*4096 + rs1*32768 + sh*1048576) / 2^20 % 2^6 = sh by omega]

/-! ### S-type stores (`sb`/`sd`): the 12-bit offset splits across `rd`
    (`[4:0]`) and `funct7` (`[11:5]`). -/

theorem sb_roundtrip (rs1 rs2 : Nat) (imm : BitVec 12) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    decode (encode (.sb rs1 rs2 imm)) = .sb rs1 rs2 imm := by
  have him : imm.toNat < 4096 := imm.isLt
  obtain ⟨lo, hi, hlob, hhib, hrec, hlo5, hhi7⟩ :
      ∃ lo hi, lo < 32 ∧ hi < 128 ∧ hi * 32 + lo = imm.toNat ∧
        imm.toNat &&& 0x1F = lo ∧ (imm.toNat >>> 5) &&& 0x7F = hi :=
    ⟨imm.toNat % 32, imm.toNat / 32 % 128, by omega, by omega, by omega,
     by rw [show (0x1F:Nat) = 2^5 - 1 from rfl, and_two_pow_sub_one_eq_mod],
     by rw [show (0x7F:Nat) = 2^7 - 1 from rfl, and_two_pow_sub_one_eq_mod,
            Nat.shiftRight_eq_div_pow]⟩
  have hN : (encode (.sb rs1 rs2 imm)).toNat
      = 35 + lo * 128 + rs1 * 32768 + rs2 * 1048576 + hi * 33554432 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, hlo5, hhi7]
    clear hlo5 hhi7 hrec him
    rw [BitVec.toNat_ofNat,
        lor_window_add 35 lo 7 5 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7) rs1 15 5 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7 + rs1 * 2^15 + rs2 * 2^20) hi 25 7 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  have himmeq : (hi <<< 5 ||| lo) = imm.toNat := by
    rw [lor_low_add hi 5 lo (by omega)]; omega
  clear hlo5 hhi7 hrec him
  simp only [decode, hf 0 7, hf 12 3, hf 15 5, hf 20 5, hf 7 5, hf 25 7,
    show (35 + lo*128 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^0 % 2^7 = 35 by omega,
    show (35 + lo*128 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^12 % 2^3 = 0 by omega,
    show (35 + lo*128 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^15 % 2^5 = rs1 by omega,
    show (35 + lo*128 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^20 % 2^5 = rs2 by omega,
    show (35 + lo*128 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^7 % 2^5 = lo by omega,
    show (35 + lo*128 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^25 % 2^7 = hi by omega,
    himmeq, ofNatW_toNat]

theorem sd_roundtrip (rs1 rs2 : Nat) (imm : BitVec 12) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    decode (encode (.sd rs1 rs2 imm)) = .sd rs1 rs2 imm := by
  have him : imm.toNat < 4096 := imm.isLt
  obtain ⟨lo, hi, hlob, hhib, hrec, hlo5, hhi7⟩ :
      ∃ lo hi, lo < 32 ∧ hi < 128 ∧ hi * 32 + lo = imm.toNat ∧
        imm.toNat &&& 0x1F = lo ∧ (imm.toNat >>> 5) &&& 0x7F = hi :=
    ⟨imm.toNat % 32, imm.toNat / 32 % 128, by omega, by omega, by omega,
     by rw [show (0x1F:Nat) = 2^5 - 1 from rfl, and_two_pow_sub_one_eq_mod],
     by rw [show (0x7F:Nat) = 2^7 - 1 from rfl, and_two_pow_sub_one_eq_mod,
            Nat.shiftRight_eq_div_pow]⟩
  have hN : (encode (.sd rs1 rs2 imm)).toNat
      = 35 + lo * 128 + 3 * 4096 + rs1 * 32768 + rs2 * 1048576 + hi * 33554432 := by
    simp only [encode, w32, List.foldl, Nat.zero_or, hlo5, hhi7]
    clear hlo5 hhi7 hrec him
    rw [BitVec.toNat_ofNat,
        lor_window_add 35 lo 7 5 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7) 3 12 3 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7 + 3 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7 + 3 * 2^12 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (35 + lo * 2^7 + 3 * 2^12 + rs1 * 2^15 + rs2 * 2^20) hi 25 7 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  have himmeq : (hi <<< 5 ||| lo) = imm.toNat := by
    rw [lor_low_add hi 5 lo (by omega)]; omega
  clear hlo5 hhi7 hrec him
  simp only [decode, hf 0 7, hf 12 3, hf 15 5, hf 20 5, hf 7 5, hf 25 7,
    show (35 + lo*128 + 3*4096 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^0 % 2^7 = 35 by omega,
    show (35 + lo*128 + 3*4096 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^12 % 2^3 = 3 by omega,
    show (35 + lo*128 + 3*4096 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^15 % 2^5 = rs1 by omega,
    show (35 + lo*128 + 3*4096 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^20 % 2^5 = rs2 by omega,
    show (35 + lo*128 + 3*4096 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^7 % 2^5 = lo by omega,
    show (35 + lo*128 + 3*4096 + rs1*32768 + rs2*1048576 + hi*33554432) / 2^25 % 2^7 = hi by omega,
    himmeq, ofNatW_toNat]

/-! ### B-type branches (`beq`/`blt`/`bge`/`bgeu`): the 13-bit even offset
    scatters over bits 31, 7, 25:6, 8:4. Round-trip needs `imm` even (the
    compiler emits 4-aligned targets); Phase 2 discharges it. -/

/-- The common B-type immediate decomposition + reassembly, shared by all four
    branches. Returns the four scattered halves, their bounds, the reassembly
    fact, and the `decode`-side `immB` reconstruction equal to `imm`. -/
theorem b_imm_parts (imm : BitVec 13) (hev : imm.toNat % 2 = 0) :
    ∃ b12 b11 b6 b4, b12 < 2 ∧ b11 < 2 ∧ b6 < 64 ∧ b4 < 16 ∧
      b12 * 4096 + b11 * 2048 + b6 * 32 + b4 * 2 = imm.toNat ∧
      (imm.toNat >>> 12) &&& 1 = b12 ∧ (imm.toNat >>> 11) &&& 1 = b11 ∧
      (imm.toNat >>> 5) &&& 0x3F = b6 ∧ (imm.toNat >>> 1) &&& 0xF = b4 ∧
      ((b12 <<< 12) ||| (b11 <<< 11) ||| (b6 <<< 5) ||| (b4 <<< 1)) = imm.toNat := by
  have him : imm.toNat < 8192 := imm.isLt
  refine ⟨(imm.toNat / 4096) % 2, (imm.toNat / 2048) % 2, (imm.toNat / 32) % 64,
    (imm.toNat / 2) % 16, by omega, by omega, by omega, by omega, by omega,
    by rw [show (1:Nat) = 2^1 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow],
    by rw [show (1:Nat) = 2^1 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow],
    by rw [show (0x3F:Nat) = 2^6 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow],
    by rw [show (0xF:Nat) = 2^4 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow], ?_⟩
  simp only [Nat.shiftLeft_eq]
  rw [lor_mul_add ((imm.toNat/4096)%2 * 2^12) ((imm.toNat/2048)%2) 11 1 (by omega) (by omega),
      lor_mul_add ((imm.toNat/4096)%2 * 2^12 + (imm.toNat/2048)%2 * 2^11) ((imm.toNat/32)%64) 5 6 (by omega) (by omega),
      lor_mul_add ((imm.toNat/4096)%2 * 2^12 + (imm.toNat/2048)%2 * 2^11 + (imm.toNat/32)%64 * 2^5) ((imm.toNat/2)%16) 1 4 (by omega) (by omega)]
  omega

theorem beq_roundtrip (rs1 rs2 : Nat) (imm : BitVec 13)
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) (hev : imm.toNat % 2 = 0) :
    decode (encode (.beq rs1 rs2 imm)) = .beq rs1 rs2 imm := by
  obtain ⟨b12, b11, b6, b4, hb12, hb11, hb6, hb4, hrec, e12, e11, e6, e4, himmB⟩ :=
    b_imm_parts imm hev
  have hN : (encode (.beq rs1 rs2 imm)).toNat
      = 99 + rs1 * 32768 + rs2 * 1048576 + b12 * 2147483648 + b11 * 128
        + b6 * 33554432 + b4 * 256 := by
    simp only [encode, encB, w32, List.foldl, Nat.zero_or, e12, e11, e6, e4]
    clear e12 e11 e6 e4 hrec himmB hev
    rw [BitVec.toNat_ofNat,
        lor_window_add 99 rs1 15 5 (by omega) (by omega),
        lor_window_add (99 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (99 + rs1 * 2^15 + rs2 * 2^20) b12 31 1 (by omega) (by omega),
        lor_window_add (99 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31) b11 7 1 (by omega) (by omega),
        lor_window_add (99 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7) b6 25 6 (by omega) (by omega),
        lor_window_add (99 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7 + b6 * 2^25) b4 8 4 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  clear e12 e11 e6 e4 hrec hev
  simp only [decode, hf 0 7, hf 12 3, hf 15 5, hf 20 5, hf 31 1, hf 7 1, hf 25 6, hf 8 4,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^0 % 2^7 = 99 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^12 % 2^3 = 0 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^15 % 2^5 = rs1 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^20 % 2^5 = rs2 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^31 % 2^1 = b12 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^7 % 2^1 = b11 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^25 % 2^6 = b6 by omega,
    show (99 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^8 % 2^4 = b4 by omega,
    himmB, ofNatW_toNat]

theorem blt_roundtrip (rs1 rs2 : Nat) (imm : BitVec 13)
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) (hev : imm.toNat % 2 = 0) :
    decode (encode (.blt rs1 rs2 imm)) = .blt rs1 rs2 imm := by
  obtain ⟨b12, b11, b6, b4, hb12, hb11, hb6, hb4, hrec, e12, e11, e6, e4, himmB⟩ :=
    b_imm_parts imm hev
  have hN : (encode (.blt rs1 rs2 imm)).toNat
      = 99 + 4 * 4096 + rs1 * 32768 + rs2 * 1048576 + b12 * 2147483648 + b11 * 128
        + b6 * 33554432 + b4 * 256 := by
    simp only [encode, encB, w32, List.foldl, Nat.zero_or, e12, e11, e6, e4]
    clear e12 e11 e6 e4 hrec himmB hev
    rw [BitVec.toNat_ofNat,
        lor_window_add 99 4 12 3 (by omega) (by omega),
        lor_window_add (99 + 4 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (99 + 4 * 2^12 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (99 + 4 * 2^12 + rs1 * 2^15 + rs2 * 2^20) b12 31 1 (by omega) (by omega),
        lor_window_add (99 + 4 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31) b11 7 1 (by omega) (by omega),
        lor_window_add (99 + 4 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7) b6 25 6 (by omega) (by omega),
        lor_window_add (99 + 4 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7 + b6 * 2^25) b4 8 4 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  clear e12 e11 e6 e4 hrec hev
  simp only [decode, hf 0 7, hf 12 3, hf 15 5, hf 20 5, hf 31 1, hf 7 1, hf 25 6, hf 8 4,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^0 % 2^7 = 99 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^12 % 2^3 = 4 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^15 % 2^5 = rs1 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^20 % 2^5 = rs2 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^31 % 2^1 = b12 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^7 % 2^1 = b11 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^25 % 2^6 = b6 by omega,
    show (99 + 4*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^8 % 2^4 = b4 by omega,
    himmB, ofNatW_toNat]

theorem bge_roundtrip (rs1 rs2 : Nat) (imm : BitVec 13)
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) (hev : imm.toNat % 2 = 0) :
    decode (encode (.bge rs1 rs2 imm)) = .bge rs1 rs2 imm := by
  obtain ⟨b12, b11, b6, b4, hb12, hb11, hb6, hb4, hrec, e12, e11, e6, e4, himmB⟩ :=
    b_imm_parts imm hev
  have hN : (encode (.bge rs1 rs2 imm)).toNat
      = 99 + 5 * 4096 + rs1 * 32768 + rs2 * 1048576 + b12 * 2147483648 + b11 * 128
        + b6 * 33554432 + b4 * 256 := by
    simp only [encode, encB, w32, List.foldl, Nat.zero_or, e12, e11, e6, e4]
    clear e12 e11 e6 e4 hrec himmB hev
    rw [BitVec.toNat_ofNat,
        lor_window_add 99 5 12 3 (by omega) (by omega),
        lor_window_add (99 + 5 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (99 + 5 * 2^12 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (99 + 5 * 2^12 + rs1 * 2^15 + rs2 * 2^20) b12 31 1 (by omega) (by omega),
        lor_window_add (99 + 5 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31) b11 7 1 (by omega) (by omega),
        lor_window_add (99 + 5 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7) b6 25 6 (by omega) (by omega),
        lor_window_add (99 + 5 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7 + b6 * 2^25) b4 8 4 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  clear e12 e11 e6 e4 hrec hev
  simp only [decode, hf 0 7, hf 12 3, hf 15 5, hf 20 5, hf 31 1, hf 7 1, hf 25 6, hf 8 4,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^0 % 2^7 = 99 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^12 % 2^3 = 5 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^15 % 2^5 = rs1 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^20 % 2^5 = rs2 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^31 % 2^1 = b12 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^7 % 2^1 = b11 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^25 % 2^6 = b6 by omega,
    show (99 + 5*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^8 % 2^4 = b4 by omega,
    himmB, ofNatW_toNat]

theorem bgeu_roundtrip (rs1 rs2 : Nat) (imm : BitVec 13)
    (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) (hev : imm.toNat % 2 = 0) :
    decode (encode (.bgeu rs1 rs2 imm)) = .bgeu rs1 rs2 imm := by
  obtain ⟨b12, b11, b6, b4, hb12, hb11, hb6, hb4, hrec, e12, e11, e6, e4, himmB⟩ :=
    b_imm_parts imm hev
  have hN : (encode (.bgeu rs1 rs2 imm)).toNat
      = 99 + 7 * 4096 + rs1 * 32768 + rs2 * 1048576 + b12 * 2147483648 + b11 * 128
        + b6 * 33554432 + b4 * 256 := by
    simp only [encode, encB, w32, List.foldl, Nat.zero_or, e12, e11, e6, e4]
    clear e12 e11 e6 e4 hrec himmB hev
    rw [BitVec.toNat_ofNat,
        lor_window_add 99 7 12 3 (by omega) (by omega),
        lor_window_add (99 + 7 * 2^12) rs1 15 5 (by omega) (by omega),
        lor_window_add (99 + 7 * 2^12 + rs1 * 2^15) rs2 20 5 (by omega) (by omega),
        lor_window_add (99 + 7 * 2^12 + rs1 * 2^15 + rs2 * 2^20) b12 31 1 (by omega) (by omega),
        lor_window_add (99 + 7 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31) b11 7 1 (by omega) (by omega),
        lor_window_add (99 + 7 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7) b6 25 6 (by omega) (by omega),
        lor_window_add (99 + 7 * 2^12 + rs1 * 2^15 + rs2 * 2^20 + b12 * 2^31 + b11 * 2^7 + b6 * 2^25) b4 8 4 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  clear e12 e11 e6 e4 hrec hev
  simp only [decode, hf 0 7, hf 12 3, hf 15 5, hf 20 5, hf 31 1, hf 7 1, hf 25 6, hf 8 4,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^0 % 2^7 = 99 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^12 % 2^3 = 7 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^15 % 2^5 = rs1 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^20 % 2^5 = rs2 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^31 % 2^1 = b12 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^7 % 2^1 = b11 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^25 % 2^6 = b6 by omega,
    show (99 + 7*4096 + rs1*32768 + rs2*1048576 + b12*2147483648 + b11*128 + b6*33554432 + b4*256) / 2^8 % 2^4 = b4 by omega,
    himmB, ofNatW_toNat]

/-! ### J-type jump (`jal`): the 21-bit even offset scatters over bits 31,
    12:8, 20, 21:10. Round-trip needs `imm` even; Phase 2 discharges it. -/

theorem jal_roundtrip (rd : Nat) (imm : BitVec 21) (hrd : rd < 32) (hev : imm.toNat % 2 = 0) :
    decode (encode (.jal rd imm)) = .jal rd imm := by
  have him : imm.toNat < 2097152 := imm.isLt
  obtain ⟨b20, bhi, b11, blo, hb20, hbhi, hb11, hblo, hrec, e20, ehi, e11, elo, himmJ⟩ :
      ∃ b20 bhi b11 blo, b20 < 2 ∧ bhi < 256 ∧ b11 < 2 ∧ blo < 1024 ∧
        b20 * 1048576 + bhi * 4096 + b11 * 2048 + blo * 2 = imm.toNat ∧
        (imm.toNat >>> 20) &&& 1 = b20 ∧ (imm.toNat >>> 12) &&& 0xFF = bhi ∧
        (imm.toNat >>> 11) &&& 1 = b11 ∧ (imm.toNat >>> 1) &&& 0x3FF = blo ∧
        ((b20 <<< 20) ||| (bhi <<< 12) ||| (b11 <<< 11) ||| (blo <<< 1)) = imm.toNat := by
    refine ⟨(imm.toNat / 1048576) % 2, (imm.toNat / 4096) % 256, (imm.toNat / 2048) % 2,
      (imm.toNat / 2) % 1024, by omega, by omega, by omega, by omega, by omega,
      by rw [show (1:Nat) = 2^1 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow],
      by rw [show (0xFF:Nat) = 2^8 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow],
      by rw [show (1:Nat) = 2^1 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow],
      by rw [show (0x3FF:Nat) = 2^10 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow], ?_⟩
    simp only [Nat.shiftLeft_eq]
    rw [lor_mul_add ((imm.toNat/1048576)%2 * 2^20) ((imm.toNat/4096)%256) 12 8 (by omega) (by omega),
        lor_mul_add ((imm.toNat/1048576)%2 * 2^20 + (imm.toNat/4096)%256 * 2^12) ((imm.toNat/2048)%2) 11 1 (by omega) (by omega),
        lor_mul_add ((imm.toNat/1048576)%2 * 2^20 + (imm.toNat/4096)%256 * 2^12 + (imm.toNat/2048)%2 * 2^11) ((imm.toNat/2)%1024) 1 10 (by omega) (by omega)]
    omega
  have hN : (encode (.jal rd imm)).toNat
      = 111 + rd * 128 + b20 * 2147483648 + bhi * 4096 + b11 * 1048576 + blo * 2097152 := by
    simp only [encode, encJ, w32, List.foldl, Nat.zero_or, e20, ehi, e11, elo]
    clear e20 ehi e11 elo hrec himmJ hev him
    rw [BitVec.toNat_ofNat,
        lor_window_add 111 rd 7 5 (by omega) (by omega),
        lor_window_add (111 + rd * 2^7) b20 31 1 (by omega) (by omega),
        lor_window_add (111 + rd * 2^7 + b20 * 2^31) bhi 12 8 (by omega) (by omega),
        lor_window_add (111 + rd * 2^7 + b20 * 2^31 + bhi * 2^12) b11 20 1 (by omega) (by omega),
        lor_window_add (111 + rd * 2^7 + b20 * 2^31 + bhi * 2^12 + b11 * 2^20) blo 21 10 (by omega) (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hf := field_of_toNat hN
  clear e20 ehi e11 elo hrec hev him
  simp only [decode, hf 0 7, hf 7 5, hf 31 1, hf 12 8, hf 20 1, hf 21 10,
    show (111 + rd*128 + b20*2147483648 + bhi*4096 + b11*1048576 + blo*2097152) / 2^0 % 2^7 = 111 by omega,
    show (111 + rd*128 + b20*2147483648 + bhi*4096 + b11*1048576 + blo*2097152) / 2^7 % 2^5 = rd by omega,
    show (111 + rd*128 + b20*2147483648 + bhi*4096 + b11*1048576 + blo*2097152) / 2^31 % 2^1 = b20 by omega,
    show (111 + rd*128 + b20*2147483648 + bhi*4096 + b11*1048576 + blo*2097152) / 2^12 % 2^8 = bhi by omega,
    show (111 + rd*128 + b20*2147483648 + bhi*4096 + b11*1048576 + blo*2097152) / 2^20 % 2^1 = b11 by omega,
    show (111 + rd*128 + b20*2147483648 + bhi*4096 + b11*1048576 + blo*2097152) / 2^21 % 2^10 = blo by omega,
    himmJ, ofNatW_toNat]

/-! ## §3 The unified round-trip (Phase-2 interface).

    `WF i` is the operand-range side condition the compiler's emitted stream
    satisfies (registers `< 32`; shift amounts `< 32` — the `funct7`/shamt
    overlap; branch/jump offsets even — 4-aligned targets). `decode_encode`
    dispatches to the per-constructor lemmas. Phase 2 discharges `WF` for every
    instruction the layout emits, then feeds this to `Installed`. -/

/-- Well-formedness of an emitted instruction: exactly the operand ranges the
    round-trip needs. -/
def WF : Instr → Prop
  | .addi rd rs1 _  => rd < 32 ∧ rs1 < 32
  | .add  rd rs1 rs2 => rd < 32 ∧ rs1 < 32 ∧ rs2 < 32
  | .sub  rd rs1 rs2 => rd < 32 ∧ rs1 < 32 ∧ rs2 < 32
  | .or   rd rs1 rs2 => rd < 32 ∧ rs1 < 32 ∧ rs2 < 32
  | .slli rd rs1 sh  => rd < 32 ∧ rs1 < 32 ∧ sh < 32
  | .srli rd rs1 sh  => rd < 32 ∧ rs1 < 32 ∧ sh < 32
  | .lbu  rd rs1 _   => rd < 32 ∧ rs1 < 32
  | .ld   rd rs1 _   => rd < 32 ∧ rs1 < 32
  | .sb   rs1 rs2 _  => rs1 < 32 ∧ rs2 < 32
  | .sd   rs1 rs2 _  => rs1 < 32 ∧ rs2 < 32
  | .beq  rs1 rs2 imm => rs1 < 32 ∧ rs2 < 32 ∧ imm.toNat % 2 = 0
  | .blt  rs1 rs2 imm => rs1 < 32 ∧ rs2 < 32 ∧ imm.toNat % 2 = 0
  | .bge  rs1 rs2 imm => rs1 < 32 ∧ rs2 < 32 ∧ imm.toNat % 2 = 0
  | .bgeu rs1 rs2 imm => rs1 < 32 ∧ rs2 < 32 ∧ imm.toNat % 2 = 0
  | .jal  rd imm      => rd < 32 ∧ imm.toNat % 2 = 0
  | .jalr rd rs1 _    => rd < 32 ∧ rs1 < 32
  | .unknown          => False

/-- **The round-trip.** Every well-formed instruction decodes back to itself. -/
theorem decode_encode : ∀ (i : Instr), WF i → decode (encode i) = i
  | .addi rd rs1 imm, h  => addi_roundtrip rd rs1 imm h.1 h.2
  | .add  rd rs1 rs2, h  => add_roundtrip rd rs1 rs2 h.1 h.2.1 h.2.2
  | .sub  rd rs1 rs2, h  => sub_roundtrip rd rs1 rs2 h.1 h.2.1 h.2.2
  | .or   rd rs1 rs2, h  => or_roundtrip rd rs1 rs2 h.1 h.2.1 h.2.2
  | .slli rd rs1 sh, h   => slli_roundtrip rd rs1 sh h.1 h.2.1 h.2.2
  | .srli rd rs1 sh, h   => srli_roundtrip rd rs1 sh h.1 h.2.1 h.2.2
  | .lbu  rd rs1 imm, h  => lbu_roundtrip rd rs1 imm h.1 h.2
  | .ld   rd rs1 imm, h  => ld_roundtrip rd rs1 imm h.1 h.2
  | .sb   rs1 rs2 imm, h => sb_roundtrip rs1 rs2 imm h.1 h.2
  | .sd   rs1 rs2 imm, h => sd_roundtrip rs1 rs2 imm h.1 h.2
  | .beq  rs1 rs2 imm, h => beq_roundtrip rs1 rs2 imm h.1 h.2.1 h.2.2
  | .blt  rs1 rs2 imm, h => blt_roundtrip rs1 rs2 imm h.1 h.2.1 h.2.2
  | .bge  rs1 rs2 imm, h => bge_roundtrip rs1 rs2 imm h.1 h.2.1 h.2.2
  | .bgeu rs1 rs2 imm, h => bgeu_roundtrip rs1 rs2 imm h.1 h.2.1 h.2.2
  | .jal  rd imm, h      => jal_roundtrip rd imm h.1 h.2
  | .jalr rd rs1 imm, h  => jalr_roundtrip rd rs1 imm h.1 h.2
  | .unknown, h          => h.elim

end LowIR.ProgSim.EncodeFacts
