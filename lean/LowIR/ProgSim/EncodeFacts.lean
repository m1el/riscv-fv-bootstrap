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

/-- Field extraction against a known `toNat`: `field w lo len = (N / 2^lo) % 2^len`. -/
theorem field_of_toNat {w : BitVec 32} {N : Nat} (hw : w.toNat = N) (lo len : Nat) :
    field w lo len = (N / 2 ^ lo) % 2 ^ len := by
  unfold field; rw [hw, Nat.shiftRight_eq_div_pow, and_two_pow_sub_one_eq_mod]

/-- A masked 12-bit immediate is itself. -/
theorem mask12 (x : Nat) (h : x < 4096) : x &&& 0xFFF = x := by
  rw [show (0xFFF : Nat) = 2 ^ 12 - 1 from rfl, and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- `BitVec.ofNat 12` of a 12-bit value's `toNat` is that value. -/
theorem ofNat12_toNat (imm : BitVec 12) : BitVec.ofNat 12 imm.toNat = imm := by
  rw [BitVec.ofNat_toNat]; exact BitVec.setWidth_eq imm

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
    ofNat12_toNat]

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
    ofNat12_toNat]

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
    ofNat12_toNat]

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
    ofNat12_toNat]

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

end LowIR.ProgSim.EncodeFacts
