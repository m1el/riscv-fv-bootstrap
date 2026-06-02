/-
  General refinement (T1): for ALL inputs, executing `core` computes `coreSpec`.

  This is the proof-grade theorem (vs. the finite certification in Certify.lean):
  it quantifies over every input via induction on the main loop, so it dominates
  any amount of emulator testing. It uses NO `native_decide`.

  STATUS: scaffold. The per-step reduction primitive is proved and works (see
  `step_li_t0`); the loop invariant and top-level statement are pinned down; the
  inductive body is the remaining frontier (marked `sorry`). See STATUS.md.
-/
import Hex0.Rv64i
import Hex0.Spec
import Hex0.Image
import Hex0.Harness
open Rv64i

namespace Hex0.Refine

/-! ## The per-step reduction primitive (PROVED, and the basis for everything)

    For any state whose code bytes at `pc` are known, one `step` reduces to the
    concrete instruction's effect, while the data it touches stays symbolic. The
    recipe, demonstrated below for `core`'s first instruction `li t0,0`
    (= `addi x5,x0,0`, bytes 93 02 00 00, word 0x293):

      1. `have hw : fetch32 s = W := by simp only [fetch32, <byte eqs>]; decide`
      2. `have hd : Rv64i.decode W = <instr> := by decide`
      3. `simp [step, hw, hd, State.setPc, State.rset, State.rget, ...]`

    This scales to every instruction: each is a closed-word `decide` for decode
    plus a `simp` for the effect. -/
theorem step_li_t0 (s : State)
    (h0 : s.mem s.pc = 0x93) (h1 : s.mem (s.pc + 1) = 0x02)
    (h2 : s.mem (s.pc + 2) = 0x00) (h3 : s.mem (s.pc + 3) = 0x00)
    (hpc : s.pc = 0x80000088) :
    (step s).pc = 0x8000008c ∧ (step s).rget 5 = 0 := by
  have hw : fetch32 s = 659#32 := by simp only [fetch32, h0, h1, h2, h3]; decide
  have hd : Rv64i.decode 659#32 = Rv64i.Instr.addi 5 0 0 := by decide
  simp [step, hw, hd, State.setPc, State.rset, State.rget, hpc]

/-! ## Code-loaded predicate and the generic fetch lemma -/

/-- `core`'s bytes sit at `coreAddr .. coreAddr+324` in `s`. -/
def CodeLoaded (s : State) : Prop :=
  ∀ i, i < Image.coreBytes.length →
    s.mem (BitVec.ofNat 64 (Image.coreAddr + i)) = BitVec.ofNat 8 (Image.coreBytes.getD i 0)

/-- The 32-bit little-endian word formed by the 4 code bytes at offset `off`,
    structured exactly as `fetch32` produces it. -/
def wordAt (off : Nat) : BitVec 32 :=
  (BitVec.ofNat 8 (Image.coreBytes.getD off 0)).setWidth 32 |||
  ((BitVec.ofNat 8 (Image.coreBytes.getD (off + 1) 0)).setWidth 32) <<< 8 |||
  ((BitVec.ofNat 8 (Image.coreBytes.getD (off + 2) 0)).setWidth 32) <<< 16 |||
  ((BitVec.ofNat 8 (Image.coreBytes.getD (off + 3) 0)).setWidth 32) <<< 24

theorem addr_ofNat_succ (a k : Nat) :
    (BitVec.ofNat 64 a) + (BitVec.ofNat 64 k) = BitVec.ofNat 64 (a + k) := by
  simp [BitVec.ofNat_add]

/-- Generic fetch: at a concrete code offset, `fetch32` returns `wordAt off`. -/
theorem fetch_code (s : State) (hcode : CodeLoaded s) (off : Nat)
    (h : off + 3 < Image.coreBytes.length)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off)) :
    fetch32 s = wordAt off := by
  have e1 : s.pc + 1 = BitVec.ofNat 64 (Image.coreAddr + (off + 1)) := by
    rw [hpc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have e2 : s.pc + 2 = BitVec.ofNat 64 (Image.coreAddr + (off + 2)) := by
    rw [hpc, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have e3 : s.pc + 3 = BitVec.ofNat 64 (Image.coreAddr + (off + 3)) := by
    rw [hpc, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, addr_ofNat_succ, Nat.add_assoc]
  unfold fetch32 wordAt
  -- rewrite the offset reads first (they mention s.pc + k), then the bare read
  rw [e1, e2, e3, hpc,
      hcode off (by omega), hcode (off + 1) (by omega),
      hcode (off + 2) (by omega), hcode (off + 3) (by omega)]

/-! ## State-projection simp lemmas -/

@[simp] theorem setPc_pc (s : State) (p : Word) : (s.setPc p).pc = p := rfl
@[simp] theorem setPc_mem (s : State) (p : Word) : (s.setPc p).mem = s.mem := rfl
@[simp] theorem setPc_rget (s : State) (p : Word) (i : Nat) : (s.setPc p).rget i = s.rget i := rfl
@[simp] theorem rset_pc (s : State) (rd : Nat) (v : Word) : (s.rset rd v).pc = s.pc := by
  unfold State.rset; split <;> rfl
@[simp] theorem rset_mem (s : State) (rd : Nat) (v : Word) : (s.rset rd v).mem = s.mem := by
  unfold State.rset; split <;> rfl
/-- Reading a register after a (nonzero-target) write. -/
theorem rset_rget (s : State) (rd : Nat) (v : Word) (i : Nat) (hrd : rd ≠ 0) (hi : i ≠ 0) :
    (s.rset rd v).rget i = if i = rd then v else s.rget i := by
  unfold State.rset State.rget
  simp only [if_neg hrd, if_neg hi]

/-! ## Per-instruction step-transition lemmas (the execution engine).
    Each rewrites one `step` at a known code offset to the instruction's effect. -/

theorem step_addi (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.addi rd rs1 imm) :
    step s = (s.rset rd (s.rget rs1 + imm.signExtend 64)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_bgeu (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.bgeu rs1 rs2 imm) :
    step s = s.setPc (if (s.rget rs1).ult (s.rget rs2) then s.pc + 4
                      else s.pc + imm.signExtend 64) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_jalr (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.jalr rd rs1 imm) :
    step s = (s.rset rd (s.pc + 4)).setPc ((s.rget rs1 + imm.signExtend 64) &&& ~~~1) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_add (s : State) (off rd rs1 rs2 : Nat) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.add rd rs1 rs2) :
    step s = (s.rset rd (s.rget rs1 + s.rget rs2)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_or (s : State) (off rd rs1 rs2 : Nat) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.or rd rs1 rs2) :
    step s = (s.rset rd (s.rget rs1 ||| s.rget rs2)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_slli (s : State) (off rd rs1 sh : Nat) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.slli rd rs1 sh) :
    step s = (s.rset rd (s.rget rs1 <<< sh)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_lbu (s : State) (off rd rs1 : Nat) (imm : BitVec 12) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.lbu rd rs1 imm) :
    step s = (s.rset rd ((s.loadByte (s.rget rs1 + imm.signExtend 64)).setWidth 64)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_sb (s : State) (off rs1 rs2 : Nat) (imm : BitVec 12) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.sb rs1 rs2 imm) :
    step s = (s.storeByte (s.rget rs1 + imm.signExtend 64) ((s.rget rs2).setWidth 8)).setPc (s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_beq (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.beq rs1 rs2 imm) :
    step s = s.setPc (if s.rget rs1 = s.rget rs2 then s.pc + imm.signExtend 64 else s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_blt (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.blt rs1 rs2 imm) :
    step s = s.setPc (if (s.rget rs1).slt (s.rget rs2) then s.pc + imm.signExtend 64 else s.pc + 4) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_bge (s : State) (off rs1 rs2 : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.bge rs1 rs2 imm) :
    step s = s.setPc (if (s.rget rs1).slt (s.rget rs2) then s.pc + 4 else s.pc + imm.signExtend 64) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

theorem step_jal (s : State) (off rd : Nat) (imm : BitVec 21) (hcode : CodeLoaded s)
    (hoff : off + 3 < Image.coreBytes.length) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hd : Rv64i.decode (wordAt off) = Rv64i.Instr.jal rd imm) :
    step s = (s.rset rd (s.pc + 4)).setPc (s.pc + imm.signExtend 64) := by
  unfold step; rw [fetch_code s hcode off hoff hpc, hd]

/-- Preconditions for the calling convention to be sound: the input region fits
    before the output region, and the output region fits in the address space.
    (The fixed addresses come from the linker; see Image.lean / TCB.md.) -/
structure WellFormed (inp : List Nat) (cap : Nat) : Prop where
  in_fits   : Image.inputAddr + inp.length ≤ Image.outAddr
  out_fits  : Image.outAddr + cap < 2 ^ 64
  bytes_ok  : ∀ b ∈ inp, b < 256

/-! ## Loop invariant at the main-loop head (pc = 0x80000090)

    Relates the machine state mid-execution to a partial run of `decodeS`:
    `rest` is the un-consumed input suffix, `emitted` the bytes written so far. -/

def LOOP : BitVec 64 := 0x80000090

structure LoopInv (inp : List Nat) (cap : Nat) (s : State)
    (rest emitted : List Nat) : Prop where
  at_loop   : s.pc = LOOP
  code      : CodeLoaded s
  a0        : s.rget 10 = BitVec.ofNat 64 Image.inputAddr
  a1        : s.rget 11 = BitVec.ofNat 64 inp.length
  a2        : s.rget 12 = BitVec.ofNat 64 Image.outAddr
  a3        : s.rget 13 = BitVec.ofNat 64 cap
  ra0       : s.rget 1  = 0
  -- the input bytes live in the input region (so `lbu` reads the right char)
  in_mem    : ∀ j, j < inp.length →
                s.mem (BitVec.ofNat 64 (Image.inputAddr + j)) = BitVec.ofNat 8 (inp.getD j 0)
  -- in_idx (t0) is the consumed prefix length; `rest` is what remains
  idx       : s.rget 5  = BitVec.ofNat 64 (inp.length - rest.length)
  suffix    : inp.drop (inp.length - rest.length) = rest
  -- out_idx (t1) counts emitted bytes, which are in the output region
  outidx    : s.rget 6  = BitVec.ofNat 64 emitted.length
  emitted_le : emitted.length ≤ cap
  out_mem   : ∀ j, j < emitted.length →
                s.mem (BitVec.ofNat 64 (Image.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0)

/-! ## Running multiple steps -/

@[simp] theorem rset_zero (s : State) (v : Word) : s.rset 0 v = s := by
  unfold State.rset; simp

/-! ## EOF base case (PROVED): input exhausted ⇒ halts Ok, output preserved.

    From the loop head with `rest = []` (so `t0 = a1 = in_len`), the machine runs
    `bgeu`(taken) → `li a0,0` → `mv a1,t1` → `ret`, reaching pc=0 with a0=0 (Ok),
    a1=out_idx, and memory untouched (so the emitted output is preserved). This
    is the base case of the main-loop induction. -/
set_option maxRecDepth 4000 in
theorem core_eof (s : State) (inp : List Nat) (emitted_len : Nat)
    (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 8))
    (ha1 : s.rget 11 = BitVec.ofNat 64 inp.length)
    (ht0 : s.rget 5 = BitVec.ofNat 64 inp.length)
    (ht1 : s.rget 6 = BitVec.ofNat 64 emitted_len)
    (hra : s.rget 1 = 0) :
    (runFuel 0 4 s).pc = 0 ∧ (runFuel 0 4 s).rget 10 = 0 ∧
    (runFuel 0 4 s).rget 11 = BitVec.ofNat 64 emitted_len ∧
    (runFuel 0 4 s).mem = s.mem := by
  -- step 1: bgeu t0,a1 -- branch taken since t0 = a1
  have hult : (s.rget 5).ult (s.rget 11) = false := by rw [ht0, ha1]; simp [BitVec.ult]
  have hs1 : step s = s.setPc (BitVec.ofNat 64 (Image.coreAddr + 264)) := by
    have hbr : s.pc + BitVec.signExtend 64 (0x100#13) = BitVec.ofNat 64 (Image.coreAddr + 264) := by
      rw [hpc]; decide
    rw [step_bgeu s 8 5 11 0x100#13 hcode (by decide) hpc (by decide), hult,
        if_neg (by decide : ¬((false : Bool) = true)), hbr]
  let s1 := s.setPc (BitVec.ofNat 64 (Image.coreAddr + 264))
  have hs1def : s1 = s.setPc (BitVec.ofNat 64 (Image.coreAddr + 264)) := rfl
  rw [← hs1def] at hs1
  -- step 2: li a0,0
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + 264) := rfl
  have hcode1 : CodeLoaded s1 := by intro i hi; rw [hs1def]; simp [hcode i hi]
  have hs2 : step s1 = (s1.rset 10 0).setPc (BitVec.ofNat 64 (Image.coreAddr + 268)) := by
    have hz : s1.rget 0 + BitVec.signExtend 64 (0#12) = 0 := by
      rw [show s1.rget 0 = (0 : Word) from rfl]; decide
    have hpcA : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 268) := by rw [hpc1]; decide
    rw [step_addi s1 264 10 0 0#12 hcode1 (by decide) hpc1 (by decide), hz, hpcA]
  -- step 3: mv a1,t1  (a1 := t1)
  let s2 := (s1.rset 10 0).setPc (BitVec.ofNat 64 (Image.coreAddr + 268))
  have hs2def : s2 = (s1.rset 10 0).setPc (BitVec.ofNat 64 (Image.coreAddr + 268)) := rfl
  rw [← hs2def] at hs2
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image.coreAddr + 268) := rfl
  have hcode2 : CodeLoaded s2 := by
    intro i hi; rw [hs2def]; simp [hcode1 i hi]
  have hrget6_2 : s2.rget 6 = BitVec.ofNat 64 emitted_len := by
    rw [hs2def]; simp only [setPc_rget]; rw [rset_rget _ _ _ _ (by decide) (by decide)]
    simp only [if_neg (by decide : (6:Nat) ≠ 10)]; rw [hs1def]; simp only [setPc_rget]; exact ht1
  have hs3 : step s2 = (s2.rset 11 (BitVec.ofNat 64 emitted_len)).setPc
                          (BitVec.ofNat 64 (Image.coreAddr + 272)) := by
    have hz : s2.rget 6 + BitVec.signExtend 64 (0#12) = BitVec.ofNat 64 emitted_len := by
      rw [hrget6_2, show BitVec.signExtend 64 (0#12) = (0 : Word) from by decide]; simp
    have hpcA : s2.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 272) := by rw [hpc2]; decide
    rw [step_addi s2 268 11 6 0#12 hcode2 (by decide) hpc2 (by decide), hz, hpcA]
  -- step 4: ret  (pc := ra = 0)
  let s3 := (s2.rset 11 (BitVec.ofNat 64 emitted_len)).setPc
              (BitVec.ofNat 64 (Image.coreAddr + 272))
  have hs3def : s3 = (s2.rset 11 (BitVec.ofNat 64 emitted_len)).setPc
              (BitVec.ofNat 64 (Image.coreAddr + 272)) := rfl
  rw [← hs3def] at hs3
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image.coreAddr + 272) := rfl
  have hcode3 : CodeLoaded s3 := by intro i hi; rw [hs3def]; simp [hcode2 i hi]
  have hra3 : s3.rget 1 = 0 := by
    rw [hs3def]; simp only [setPc_rget]; rw [rset_rget _ _ _ _ (by decide) (by decide)]
    simp only [if_neg (by decide : (1:Nat) ≠ 11)]; rw [hs2def]; simp only [setPc_rget]
    rw [rset_rget _ _ _ _ (by decide) (by decide)]
    simp only [if_neg (by decide : (1:Nat) ≠ 10)]; rw [hs1def]; simp only [setPc_rget]; exact hra
  have hs4 : step s3 = s3.setPc 0 := by
    rw [step_jalr s3 272 0 1 0#12 hcode3 (by decide) hpc3 (by decide), rset_zero]
    congr 1; rw [hra3]; decide
  -- assemble: runFuel 0 4 s = step s3
  have hp0 : s.pc ≠ 0 := by rw [hpc]; decide
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; decide
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; decide
  have hp3 : s3.pc ≠ 0 := by rw [hpc3]; decide
  -- unfold the (concrete) fuel and collapse the four pc-checks; result = step^4 s
  simp only [runFuel]
  rw [hs1, hs2, hs3, hs4, if_neg hp0, if_neg hp1, if_neg hp2, if_neg hp3]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · -- a0 = 0
    rw [setPc_rget, hs3def, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (10:Nat) ≠ 11), hs2def, setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · -- a1 = emitted_len
    rw [setPc_rget, hs3def, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · -- mem unchanged
    simp only [setPc_mem, hs3def, hs2def, hs1def, rset_mem]

/-! ## Step 3 (spec side): `decodeS` token decomposition.
    `decode (token ++ rest) = (token's output) ++ decode rest`, per token class. -/

theorem decodeS_spacing (c : Nat) (rest : List Nat)
    (hc : Hex0.isComment c = false) (hs : Hex0.isSpace c = true) :
    Hex0.decodeS .High (c :: rest) = Hex0.decodeS .High rest := by
  rw [Hex0.decodeS]; simp [hc, hs]

theorem decodeS_byte (h l : Nat) (rest : List Nat) (hv lv : Nat)
    (hc : Hex0.isComment h = false) (hs : Hex0.isSpace h = false)
    (hh : Hex0.nibble h = some hv)
    (hlc : Hex0.isLowStop l = false) (hl : Hex0.nibble l = some lv) :
    Hex0.decodeS .High (h :: l :: rest) =
      ((hv * 16 + lv) :: (Hex0.decodeS .High rest).1, (Hex0.decodeS .High rest).2) := by
  rw [Hex0.decodeS]; simp only [hc, hs, hh, Bool.false_eq_true, if_false]
  rw [Hex0.decodeS]; simp [hlc, hl]

theorem decodeS_comment_skip (c : Nat) (rest : List Nat)
    (hc : Hex0.isComment c = true) :
    Hex0.decodeS .High (c :: rest) = Hex0.decodeS .High (Hex0.skipComment rest) := by
  rw [Hex0.decodeS]; simp [hc]

/-! ## The general refinement theorem (FRONTIER)

    The whole-program correctness statement. Proof outline:
      * `WellFormed` + `initOn` establishes `LoopInv inp cap s₀ inp []`.
      * one main-loop iteration: from `LoopInv .. rest emitted` either halts at
        pc=0 with the result = `coreSpec`, or returns to `LoopInv .. rest' emitted'`
        with `rest'.length < rest.length` -- by case analysis on the next char's
        class (comment / spacing / nibble→{trailing,split,unknown,emit}), each a
        straight-line chain of `step_*` reductions + the disjointness frame.
      * strong induction on `rest.length` closes it; `emitted ++ decode rest`
        telescopes to `coreSpec inp cap`.
    The per-step primitive (`step_li_t0`) and the invariant above are the parts
    in hand; the body case analysis + arithmetic/framing lemmas are remaining. -/
theorem core_refines (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    ∃ fuel, Harness.observe inp cap fuel = Hex0.coreSpec inp cap := by
  sorry

end Hex0.Refine
