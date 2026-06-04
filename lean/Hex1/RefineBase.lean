/-
  Refinement engine for hex1 (`core1`): the per-step reduction machinery,
  retargeted at `Image1`. Mirrors the engine section of Hex0/Refine.lean
  (whose generic toolkit -- state-projection simp lemmas, `ult_ofNat`,
  `ofNat_ne`, `getD_drop`, `setWidth8_64`, `loadBytes_frame/get`,
  `runFuel_halt/one/add` -- is imported and reused as-is).

  New here relative to hex0: step lemmas for SUB/SRLI/LD/SD, and the
  64-bit `loadWord`/`storeWord` toolkit for the label table.
-/
import Hex0.Refine
import Hex1.Image
open Rv64i

namespace Hex1.Refine
open Hex0.Refine (addr_ofNat_succ ult_ofNat ofNat_ne getD_drop setWidth8_64
  rset_rget storeByte_mem li_block_frame runFuel_halt runFuel_one runFuel_add)

/-! ## Code-loaded predicate and the generic fetch lemma (Image1 versions) -/

/-- `core1`'s bytes sit at `coreAddr .. coreAddr+724` in `s`. -/
def CodeLoaded1 (s : State) : Prop :=
  ∀ i, i < Image1.coreBytes.length →
    s.mem (BitVec.ofNat 64 (Image1.coreAddr + i)) = BitVec.ofNat 8 (Image1.coreBytes.getD i 0)

/-- The 32-bit little-endian word formed by the 4 code bytes at offset `off`,
    structured exactly as `fetch32` produces it. -/
def wordAt1 (off : Nat) : BitVec 32 :=
  (BitVec.ofNat 8 (Image1.coreBytes.getD off 0)).setWidth 32 |||
  ((BitVec.ofNat 8 (Image1.coreBytes.getD (off + 1) 0)).setWidth 32) <<< 8 |||
  ((BitVec.ofNat 8 (Image1.coreBytes.getD (off + 2) 0)).setWidth 32) <<< 16 |||
  ((BitVec.ofNat 8 (Image1.coreBytes.getD (off + 3) 0)).setWidth 32) <<< 24

/-- Generic fetch: at a concrete code offset, `fetch32` returns `wordAt1 off`. -/
theorem fetch_code1 (s : State) (hcode : CodeLoaded1 s) (off : Nat)
    (h : off + 3 < Image1.coreBytes.length)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off)) :
    fetch32 s = wordAt1 off := by
  have e1 : s.pc + 1 = BitVec.ofNat 64 (Image1.coreAddr + (off + 1)) := by
    rw [hpc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have e2 : s.pc + 2 = BitVec.ofNat 64 (Image1.coreAddr + (off + 2)) := by
    rw [hpc, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have e3 : s.pc + 3 = BitVec.ofNat 64 (Image1.coreAddr + (off + 3)) := by
    rw [hpc, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, addr_ofNat_succ, Nat.add_assoc]
  unfold fetch32 wordAt1
  rw [e1, e2, e3, hpc,
      hcode off (by omega), hcode (off + 1) (by omega),
      hcode (off + 2) (by omega), hcode (off + 3) (by omega)]

/-! ## Per-instruction step-transition lemmas (16 instruction forms). -/

theorem step_addi (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi rd rs1 imm) :
    step s = (s.rset rd (s.rget rs1 + imm.signExtend 64)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_add (s : State) (off rd rs1 rs2 : Nat) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.add rd rs1 rs2) :
    step s = (s.rset rd (s.rget rs1 + s.rget rs2)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_sub (s : State) (off rd rs1 rs2 : Nat) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.sub rd rs1 rs2) :
    step s = (s.rset rd (s.rget rs1 - s.rget rs2)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_or (s : State) (off rd rs1 rs2 : Nat) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.or rd rs1 rs2) :
    step s = (s.rset rd (s.rget rs1 ||| s.rget rs2)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_slli (s : State) (off rd rs1 sh : Nat) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.slli rd rs1 sh) :
    step s = (s.rset rd (s.rget rs1 <<< sh)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_srli (s : State) (off rd rs1 sh : Nat) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.srli rd rs1 sh) :
    step s = (s.rset rd (s.rget rs1 >>> sh)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_lbu (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.lbu rd rs1 imm) :
    step s = (s.rset rd ((s.loadByte (s.rget rs1 + imm.signExtend 64)).setWidth 64)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_ld (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.ld rd rs1 imm) :
    step s = (s.rset rd (s.loadWord (s.rget rs1 + imm.signExtend 64))).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_sb (s : State) (off rs1 rs2 : Nat) (imm : BitVec 12) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.sb rs1 rs2 imm) :
    step s = (s.storeByte (s.rget rs1 + imm.signExtend 64) ((s.rget rs2).setWidth 8)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_sd (s : State) (off rs1 rs2 : Nat) (imm : BitVec 12) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.sd rs1 rs2 imm) :
    step s = (s.storeWord (s.rget rs1 + imm.signExtend 64) (s.rget rs2)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_beq (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.beq rs1 rs2 imm) :
    step s = s.setPc (if s.rget rs1 = s.rget rs2 then s.pc + imm.signExtend 64 else s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_blt (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.blt rs1 rs2 imm) :
    step s = s.setPc (if (s.rget rs1).slt (s.rget rs2) then s.pc + imm.signExtend 64 else s.pc + 4) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_bge (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.bge rs1 rs2 imm) :
    step s = s.setPc (if (s.rget rs1).slt (s.rget rs2) then s.pc + 4 else s.pc + imm.signExtend 64) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_bgeu (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.bgeu rs1 rs2 imm) :
    step s = s.setPc (if (s.rget rs1).ult (s.rget rs2) then s.pc + 4
                      else s.pc + imm.signExtend 64) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_jal (s : State) (off rd : Nat) (imm : BitVec 21) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.jal rd imm) :
    step s = (s.rset rd (s.pc + 4)).setPc (s.pc + imm.signExtend 64) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

theorem step_jalr (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded1 s)
    (hoff : off + 3 < Image1.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.jalr rd rs1 imm) :
    step s = (s.rset rd (s.pc + 4)).setPc ((s.rget rs1 + imm.signExtend 64) &&& ~~~1) := by
  unfold step; rw [fetch_code1 s hcode off hoff hpc, hd]

/-! ## 64-bit load/store toolkit (label table). -/

/-- `storeWord` leaves pc and registers alone. -/
@[simp] theorem storeWord_pc (s : State) (a v : Word) : (s.storeWord a v).pc = s.pc := rfl
@[simp] theorem storeWord_rget (s : State) (a v : Word) (i : Nat) :
    (s.storeWord a v).rget i = s.rget i := rfl

/-- Reading a byte outside the 8 stored bytes is unchanged. -/
theorem storeWord_frame (s : State) (a v : Word) (x : Word)
    (h : ∀ k : Nat, k < 8 → x ≠ a + BitVec.ofNat 64 k) :
    (s.storeWord a v).mem x = s.mem x := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (by have := h 7 (by omega); simpa using this),
      if_neg (by have := h 6 (by omega); simpa using this),
      if_neg (by have := h 5 (by omega); simpa using this),
      if_neg (by have := h 4 (by omega); simpa using this),
      if_neg (by have := h 3 (by omega); simpa using this),
      if_neg (by have := h 2 (by omega); simpa using this),
      if_neg (by have := h 1 (by omega); simpa using this),
      if_neg (by have := h 0 (by omega); simpa using this)]

/-- Left cancellation for BitVec addition (it is a group). -/
theorem add_left_cancel64 {a b c : Word} (h : a + b = a + c) : b = c := by
  have := congrArg (fun x => x - a) h
  simpa [BitVec.add_comm a, BitVec.add_sub_cancel] using this

/-- `a + i ≠ a + j` for distinct small constants (no hypotheses: BitVec
    addition is injective). -/
theorem add_ne_add (a : Word) (i j : Word) (h : i ≠ j) : a + i ≠ a + j :=
  fun he => h (add_left_cancel64 he)

theorem self_ne_add (a : Word) (j : Word) (h : j ≠ 0) : a ≠ a + j := by
  intro he
  apply h
  have h0 : a + 0 = a + j := by simpa using he
  exact (add_left_cancel64 h0).symm

/-- Reading the 8 stored bytes of a `storeWord` (one lemma per byte; the
    addresses are pairwise distinct unconditionally, BitVec `+` is injective). -/
theorem storeWord_get0 (s : State) (a v : Word) :
    (s.storeWord a v).mem a = v.setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (self_ne_add a 7 (by decide)), if_neg (self_ne_add a 6 (by decide)),
      if_neg (self_ne_add a 5 (by decide)), if_neg (self_ne_add a 4 (by decide)),
      if_neg (self_ne_add a 3 (by decide)), if_neg (self_ne_add a 2 (by decide)),
      if_neg (self_ne_add a 1 (by decide))]
  simp

theorem storeWord_get1 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 1) = (v >>> 8).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (add_ne_add a 1 7 (by decide)), if_neg (add_ne_add a 1 6 (by decide)),
      if_neg (add_ne_add a 1 5 (by decide)), if_neg (add_ne_add a 1 4 (by decide)),
      if_neg (add_ne_add a 1 3 (by decide)), if_neg (add_ne_add a 1 2 (by decide))]
  simp

theorem storeWord_get2 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 2) = (v >>> 16).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (add_ne_add a 2 7 (by decide)), if_neg (add_ne_add a 2 6 (by decide)),
      if_neg (add_ne_add a 2 5 (by decide)), if_neg (add_ne_add a 2 4 (by decide)),
      if_neg (add_ne_add a 2 3 (by decide))]
  simp

theorem storeWord_get3 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 3) = (v >>> 24).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (add_ne_add a 3 7 (by decide)), if_neg (add_ne_add a 3 6 (by decide)),
      if_neg (add_ne_add a 3 5 (by decide)), if_neg (add_ne_add a 3 4 (by decide))]
  simp

theorem storeWord_get4 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 4) = (v >>> 32).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (add_ne_add a 4 7 (by decide)), if_neg (add_ne_add a 4 6 (by decide)),
      if_neg (add_ne_add a 4 5 (by decide))]
  simp

theorem storeWord_get5 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 5) = (v >>> 40).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (add_ne_add a 5 7 (by decide)), if_neg (add_ne_add a 5 6 (by decide))]
  simp

theorem storeWord_get6 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 6) = (v >>> 48).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  rw [if_neg (add_ne_add a 6 7 (by decide))]
  simp

theorem storeWord_get7 (s : State) (a v : Word) :
    (s.storeWord a v).mem (a + 7) = (v >>> 56).setWidth 8 := by
  unfold State.storeWord
  simp only [storeByte_mem]
  simp

set_option linter.unusedSimpArgs false in
/-- Reassembling the 8 little-endian bytes of `v` yields `v` (the
    `loadWord`-after-`storeWord` roundtrip, at the value level). -/
theorem assemble_bytes (v : Word) :
    (v.setWidth 8).setWidth 64 |||
    (((v >>> 8).setWidth 8).setWidth 64 <<< 8) |||
    (((v >>> 16).setWidth 8).setWidth 64 <<< 16) |||
    (((v >>> 24).setWidth 8).setWidth 64 <<< 24) |||
    (((v >>> 32).setWidth 8).setWidth 64 <<< 32) |||
    (((v >>> 40).setWidth 8).setWidth 64 <<< 40) |||
    (((v >>> 48).setWidth 8).setWidth 64 <<< 48) |||
    (((v >>> 56).setWidth 8).setWidth 64 <<< 56) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  intro hi
  rcases (by omega : i < 8 \/ (8 <= i /\ i < 16) \/ (16 <= i /\ i < 24) \/
      (24 <= i /\ i < 32) \/ (32 <= i /\ i < 40) \/ (40 <= i /\ i < 48) \/
      (48 <= i /\ i < 56) \/ 56 <= i) with
    h | h | h | h | h | h | h | h
  · -- octet 0
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = true := decide_eq_true (by omega)
    have c16 : decide (i < 16) = true := decide_eq_true (by omega)
    have c24 : decide (i < 24) = true := decide_eq_true (by omega)
    have c32 : decide (i < 32) = true := decide_eq_true (by omega)
    have c40 : decide (i < 40) = true := decide_eq_true (by omega)
    have c48 : decide (i < 48) = true := decide_eq_true (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = true := decide_eq_true (by omega)
    have s16 : decide (i - 16 < 8) = true := decide_eq_true (by omega)
    have s24 : decide (i - 24 < 8) = true := decide_eq_true (by omega)
    have s32 : decide (i - 32 < 8) = true := decide_eq_true (by omega)
    have s40 : decide (i - 40 < 8) = true := decide_eq_true (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 1
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = true := decide_eq_true (by omega)
    have c24 : decide (i < 24) = true := decide_eq_true (by omega)
    have c32 : decide (i < 32) = true := decide_eq_true (by omega)
    have c40 : decide (i < 40) = true := decide_eq_true (by omega)
    have c48 : decide (i < 48) = true := decide_eq_true (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = true := decide_eq_true (by omega)
    have s16 : decide (i - 16 < 8) = true := decide_eq_true (by omega)
    have s24 : decide (i - 24 < 8) = true := decide_eq_true (by omega)
    have s32 : decide (i - 32 < 8) = true := decide_eq_true (by omega)
    have s40 : decide (i - 40 < 8) = true := decide_eq_true (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 8 + (i - 8) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 2
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = false := decide_eq_false (by omega)
    have c24 : decide (i < 24) = true := decide_eq_true (by omega)
    have c32 : decide (i < 32) = true := decide_eq_true (by omega)
    have c40 : decide (i < 40) = true := decide_eq_true (by omega)
    have c48 : decide (i < 48) = true := decide_eq_true (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
    have s16 : decide (i - 16 < 8) = true := decide_eq_true (by omega)
    have s24 : decide (i - 24 < 8) = true := decide_eq_true (by omega)
    have s32 : decide (i - 32 < 8) = true := decide_eq_true (by omega)
    have s40 : decide (i - 40 < 8) = true := decide_eq_true (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 16 + (i - 16) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 3
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = false := decide_eq_false (by omega)
    have c24 : decide (i < 24) = false := decide_eq_false (by omega)
    have c32 : decide (i < 32) = true := decide_eq_true (by omega)
    have c40 : decide (i < 40) = true := decide_eq_true (by omega)
    have c48 : decide (i < 48) = true := decide_eq_true (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
    have s16 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
    have s24 : decide (i - 24 < 8) = true := decide_eq_true (by omega)
    have s32 : decide (i - 32 < 8) = true := decide_eq_true (by omega)
    have s40 : decide (i - 40 < 8) = true := decide_eq_true (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 24 + (i - 24) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 4
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = false := decide_eq_false (by omega)
    have c24 : decide (i < 24) = false := decide_eq_false (by omega)
    have c32 : decide (i < 32) = false := decide_eq_false (by omega)
    have c40 : decide (i < 40) = true := decide_eq_true (by omega)
    have c48 : decide (i < 48) = true := decide_eq_true (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
    have s16 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
    have s24 : decide (i - 24 < 8) = false := decide_eq_false (by omega)
    have s32 : decide (i - 32 < 8) = true := decide_eq_true (by omega)
    have s40 : decide (i - 40 < 8) = true := decide_eq_true (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 32 + (i - 32) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 5
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = false := decide_eq_false (by omega)
    have c24 : decide (i < 24) = false := decide_eq_false (by omega)
    have c32 : decide (i < 32) = false := decide_eq_false (by omega)
    have c40 : decide (i < 40) = false := decide_eq_false (by omega)
    have c48 : decide (i < 48) = true := decide_eq_true (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
    have s16 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
    have s24 : decide (i - 24 < 8) = false := decide_eq_false (by omega)
    have s32 : decide (i - 32 < 8) = false := decide_eq_false (by omega)
    have s40 : decide (i - 40 < 8) = true := decide_eq_true (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 40 + (i - 40) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 6
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = false := decide_eq_false (by omega)
    have c24 : decide (i < 24) = false := decide_eq_false (by omega)
    have c32 : decide (i < 32) = false := decide_eq_false (by omega)
    have c40 : decide (i < 40) = false := decide_eq_false (by omega)
    have c48 : decide (i < 48) = false := decide_eq_false (by omega)
    have c56 : decide (i < 56) = true := decide_eq_true (by omega)
    have s8 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
    have s16 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
    have s24 : decide (i - 24 < 8) = false := decide_eq_false (by omega)
    have s32 : decide (i - 32 < 8) = false := decide_eq_false (by omega)
    have s40 : decide (i - 40 < 8) = false := decide_eq_false (by omega)
    have s48 : decide (i - 48 < 8) = true := decide_eq_true (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 48 + (i - 48) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]
  · -- octet 7
    have t64 : decide (i < 64) = true := decide_eq_true (by omega)
    have c8 : decide (i < 8) = false := decide_eq_false (by omega)
    have c16 : decide (i < 16) = false := decide_eq_false (by omega)
    have c24 : decide (i < 24) = false := decide_eq_false (by omega)
    have c32 : decide (i < 32) = false := decide_eq_false (by omega)
    have c40 : decide (i < 40) = false := decide_eq_false (by omega)
    have c48 : decide (i < 48) = false := decide_eq_false (by omega)
    have c56 : decide (i < 56) = false := decide_eq_false (by omega)
    have s8 : decide (i - 8 < 8) = false := decide_eq_false (by omega)
    have s16 : decide (i - 16 < 8) = false := decide_eq_false (by omega)
    have s24 : decide (i - 24 < 8) = false := decide_eq_false (by omega)
    have s32 : decide (i - 32 < 8) = false := decide_eq_false (by omega)
    have s40 : decide (i - 40 < 8) = false := decide_eq_false (by omega)
    have s48 : decide (i - 48 < 8) = false := decide_eq_false (by omega)
    have s56 : decide (i - 56 < 8) = true := decide_eq_true (by omega)
    have d8 : decide (i - 8 < 64) = true := decide_eq_true (by omega)
    have d16 : decide (i - 16 < 64) = true := decide_eq_true (by omega)
    have d24 : decide (i - 24 < 64) = true := decide_eq_true (by omega)
    have d32 : decide (i - 32 < 64) = true := decide_eq_true (by omega)
    have d40 : decide (i - 40 < 64) = true := decide_eq_true (by omega)
    have d48 : decide (i - 48 < 64) = true := decide_eq_true (by omega)
    have d56 : decide (i - 56 < 64) = true := decide_eq_true (by omega)
    have e : 56 + (i - 56) = i := by omega
    rw [e]
    simp only [t64, c8, c16, c24, c32, c40, c48, c56, s8, s16, s24, s32, s40, s48, s56, d8, d16, d24, d32, d40, d48, d56, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or]

end Hex1.Refine
