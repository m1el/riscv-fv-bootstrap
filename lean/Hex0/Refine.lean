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

/-! ## Machine-side arithmetic toolkit (branch decisions + input reads). -/

/-- Unsigned `<` on `ofNat` values (used to resolve `bgeu`). -/
theorem ult_ofNat (a b : Nat) (hb : b < 2 ^ 64) (hab : a < b) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
  have ha : a < 2 ^ 64 := Nat.lt_trans hab hb
  simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hab]

/-- `ofNat` is injective on values below `2^64` (used to resolve `beq`). -/
theorem ofNat_ne (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro he; apply h
  have := congrArg BitVec.toNat he
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- The byte at the current index is the head of the remaining suffix. -/
theorem getD_drop (l : List Nat) (n d : Nat) : (l.drop n).getD 0 d = l.getD n d := by
  simp [List.getD, List.getElem?_drop]

/-- Zero-extending an in-range byte (what `lbu` does). -/
theorem setWidth8_64 (c : Nat) (h : c < 256) :
    (BitVec.ofNat 8 c).setWidth 64 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
        Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]

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
  in_lt     : Image.inputAddr + inp.length < 2 ^ 64    -- no address overflow
  bytes_lt  : ∀ b ∈ inp, b < 256                       -- inputs are bytes
  -- in_idx (t0) is the consumed prefix length; `rest` is what remains
  idx       : s.rget 5  = BitVec.ofNat 64 (inp.length - rest.length)
  suffix    : inp.drop (inp.length - rest.length) = rest
  -- out_idx (t1) counts emitted bytes, which are in the output region
  outidx    : s.rget 6  = BitVec.ofNat 64 emitted.length
  emitted_le : emitted.length ≤ cap
  out_mem   : ∀ j, j < emitted.length →
                s.mem (BitVec.ofNat 64 (Image.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0)
  -- the bytes emitted so far are a value-correct prefix: decoding the whole
  -- input = emitted ++ decoding the remaining suffix (this telescopes the
  -- induction down to `coreSpec inp cap`).
  spec_link : Hex0.decodeS .High inp =
                (emitted ++ (Hex0.decodeS .High rest).1, (Hex0.decodeS .High rest).2)

/-! ## Running multiple steps -/

@[simp] theorem rset_zero (s : State) (v : Word) : s.rset 0 v = s := by
  unfold State.rset; simp

/-- Once halted (pc = 0), more fuel changes nothing. -/
theorem runFuel_halt (b : Nat) (s : State) (h : s.pc = 0) : runFuel 0 b s = s := by
  cases b with
  | zero => rfl
  | succ n => simp [runFuel, h]

/-- Fuel composition: running `a+b` steps = running `b` more after the first `a`.
    Holds unconditionally (halting is absorbed). The backbone of the induction. -/
theorem runFuel_add (a b : Nat) (s : State) :
    runFuel 0 (a + b) s = runFuel 0 b (runFuel 0 a s) := by
  induction a generalizing s with
  | zero => simp [runFuel]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 from by omega]
    by_cases h : s.pc = 0
    · rw [runFuel_halt (a + b + 1) s h, runFuel_halt (a + 1) s h, runFuel_halt b s h]
    · simp only [runFuel, h, if_false]; rw [ih]

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

/-! ## Step 4: the induction.

    `Result f` says the halted state `f` matches `coreSpec inp cap`. `loop_correct`
    proves, by induction on the remaining input, that from any `LoopInv` the
    machine reaches such a state -- using `core_eof` (base), the per-token
    `loop_iteration` (step), `runFuel_add` (chaining), and `spec_link` (telescope). -/

def Result (f : State) (inp : List Nat) (cap : Nat) : Prop :=
  f.pc = 0 ∧
  f.rget 10 = BitVec.ofNat 64 (Hex0.coreSpec inp cap).1 ∧
  f.rget 11 = BitVec.ofNat 64 (Hex0.coreSpec inp cap).2.2 ∧
  ∀ j, j < (Hex0.coreSpec inp cap).2.2 →
    f.mem (BitVec.ofNat 64 (Image.outAddr + j))
      = BitVec.ofNat 8 ((Hex0.coreSpec inp cap).2.1.getD j 0)

set_option maxRecDepth 4000 in
/-- The shared head of every non-EOF iteration: `bgeu`(not taken) → `add` →
    `lbu` (read input char `c`) → `addi` (bump index). After 4 steps the machine
    is at offset 24 with `t2 = c`, `t0` bumped, memory and other registers intact. -/
theorem loop_prefix (inp : List Nat) (cap : Nat) (c : Nat) (rest' emitted : List Nat)
    (s : State) (inv : LoopInv inp cap s (c :: rest') emitted) :
    ∃ s4, runFuel 0 4 s = s4 ∧
      s4.pc = BitVec.ofNat 64 (Image.coreAddr + 24) ∧
      s4.rget 7 = BitVec.ofNat 64 c ∧
      s4.rget 5 = s.rget 5 + 1 ∧
      s4.mem = s.mem ∧ CodeLoaded s4 ∧
      (∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s4.rget i = s.rget i) := by
  -- length / value facts about the current index
  have hsuf := inv.suffix
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at h; omega
  have hilt : inp.length - (c :: rest').length < inp.length := by
    simp only [List.length_cons]; omega
  have hgetd : inp.getD (inp.length - (c :: rest').length) 0 = c := by
    rw [← getD_drop]; rw [hsuf]; rfl
  have hilt64 : inp.length < 2 ^ 64 := by have := inv.in_lt; omega
  have hc256 : c < 256 := by
    apply inv.bytes_lt; have : c ∈ inp.drop (inp.length - (c :: rest').length) := by
      rw [hsuf]; exact List.mem_cons_self
    exact List.drop_subset _ _ this
  have hpc0 : s.pc = BitVec.ofNat 64 (Image.coreAddr + 8) := inv.at_loop.trans (by decide)
  -- step 1: bgeu t0,a1 -- NOT taken (idx < len)
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [inv.idx, inv.a1]; exact ult_ofNat _ _ hilt64 hilt
  have hs1 : step s = s.setPc (BitVec.ofNat 64 (Image.coreAddr + 12)) := by
    have e : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 12) := by rw [hpc0]; decide
    rw [step_bgeu s 8 5 11 0x100#13 inv.code (by decide) hpc0 (by decide), if_pos hult, e]
  -- step 2: add t3,a0,t0  (t3 = inputAddr + idx)
  let s1 := s.setPc (BitVec.ofNat 64 (Image.coreAddr + 12))
  have hs1d : s1 = s.setPc (BitVec.ofNat 64 (Image.coreAddr + 12)) := rfl
  rw [← hs1d] at hs1
  have hc1 : CodeLoaded s1 := inv.code
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + 12) := rfl
  have haddr : s1.rget 10 + s1.rget 5
      = BitVec.ofNat 64 (Image.inputAddr + (inp.length - (c :: rest').length)) := by
    show s.rget 10 + s.rget 5 = _
    rw [inv.a0, inv.idx]; exact addr_ofNat_succ _ _
  have hs2 : step s1 = (s1.rset 28 (BitVec.ofNat 64
        (Image.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 16)) := by
    have e : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 16) := by rw [hpc1]; decide
    rw [step_add s1 12 28 10 5 hc1 (by decide) hpc1 (by decide), haddr, e]
  let s2 := (s1.rset 28 (BitVec.ofNat 64
        (Image.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 16))
  have hs2d : s2 = (s1.rset 28 (BitVec.ofNat 64
        (Image.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 16)) := rfl
  rw [← hs2d] at hs2
  have hc2 : CodeLoaded s2 := by
    intro i hi; have := inv.code i hi; simp only [hs2d, setPc_mem, rset_mem]; exact this
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image.coreAddr + 16) := rfl
  -- step 3: lbu t2,0(t3)  (t2 = input byte c)
  have hr28 : s2.rget 28 = BitVec.ofNat 64 (Image.inputAddr + (inp.length - (c :: rest').length)) := by
    rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hbyte : (s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64
      = BitVec.ofNat 64 c := by
    rw [hr28, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
    show (s2.mem _).setWidth 64 = _
    rw [hs2d]; simp only [setPc_mem, rset_mem, hs1d]
    rw [inv.in_mem _ hilt, hgetd, setWidth8_64 c hc256]
  have hs3 : step s2 = (s2.rset 7 (BitVec.ofNat 64 c)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 20)) := by
    have e : s2.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 20) := by rw [hpc2]; decide
    rw [step_lbu s2 16 7 28 0#12 hc2 (by decide) hpc2 (by decide)]
    show (s2.rset 7 ((s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64)).setPc _
       = (s2.rset 7 (BitVec.ofNat 64 c)).setPc _
    rw [hbyte, e]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 c)).setPc (BitVec.ofNat 64 (Image.coreAddr + 20))
  have hs3d : s3 = (s2.rset 7 (BitVec.ofNat 64 c)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 20)) := rfl
  rw [← hs3d] at hs3
  have hc3 : CodeLoaded s3 := by
    intro i hi; have := hc2 i hi; simp only [hs3d, setPc_mem, rset_mem]; exact this
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image.coreAddr + 20) := rfl
  have hr5_3 : s3.rget 5 = s.rget 5 := by
    rw [hs3d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 7), hs2d, setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28),
        hs1d, setPc_rget]
  -- step 4: addi t0,t0,1  (bump index)
  have hs4 : step s3 = (s3.rset 5 (s.rget 5 + 1)).setPc (BitVec.ofNat 64 (Image.coreAddr + 24)) := by
    have e : s3.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 24) := by rw [hpc3]; decide
    rw [step_addi s3 20 5 5 1#12 hc3 (by decide) hpc3 (by decide), e, hr5_3,
        show (1#12).signExtend 64 = (1 : Word) from by decide]
  let s4 := (s3.rset 5 (s.rget 5 + 1)).setPc (BitVec.ofNat 64 (Image.coreAddr + 24))
  have hs4d : s4 = (s3.rset 5 (s.rget 5 + 1)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 24)) := rfl
  rw [← hs4d] at hs4
  -- assemble runFuel 0 4 s = s4
  have hp0 : s.pc ≠ 0 := by rw [hpc0]; decide
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; decide
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; decide
  have hp3 : s3.pc ≠ 0 := by rw [hpc3]; decide
  refine ⟨s4, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [runFuel]; rw [hs1, hs2, hs3, hs4, if_neg hp0, if_neg hp1, if_neg hp2, if_neg hp3]
  · rw [hs4d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 5), hs3d, setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · rw [hs4d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · rw [hs4d]; simp only [setPc_mem, rset_mem, hs3d, hs2d, hs1d]
  · intro i hi; have := hc3 i hi; rw [hs4d]; simp only [setPc_mem, rset_mem]; exact this
  · intro i h0 h5 h7 h28
    rw [hs4d, setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5,
        hs3d, setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7,
        hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28,
        hs1d, setPc_rget]

/-- One main-loop iteration (the machine side of step 3). From a non-empty
    remaining input, the machine either halts correctly (error / output-short)
    or returns to the loop head with strictly less remaining input and the
    invariant preserved. THIS is the remaining frontier: a case analysis on the
    head char's class, each a straight-line `step_*` chain + the arithmetic
    toolkit + (for `sb`) the output/code disjointness frame. -/
theorem loop_iteration (inp : List Nat) (cap : Nat) (rest emitted : List Nat) (s : State)
    (hne : rest ≠ []) (inv : LoopInv inp cap s rest emitted) :
    ∃ k, (∃ rest' emitted', rest'.length < rest.length ∧
            LoopInv inp cap (runFuel 0 k s) rest' emitted')
         ∨ Result (runFuel 0 k s) inp cap := by
  sorry

/-- The EOF case as a `Result` (base case of the induction). -/
theorem eof_result (inp : List Nat) (cap : Nat) (emitted : List Nat) (s : State)
    (inv : LoopInv inp cap s [] emitted) : ∃ n, Result (runFuel 0 n s) inp cap := by
  have hpc8 : s.pc = BitVec.ofNat 64 (Image.coreAddr + 8) := inv.at_loop.trans (by decide)
  have ht0 : s.rget 5 = BitVec.ofNat 64 inp.length := by simpa using inv.idx
  have heof := core_eof s inp emitted.length inv.code hpc8 inv.a1 ht0 inv.outidx inv.ra0
  have hdec : Hex0.decode inp = (emitted, Hex0.Status.Ok) := by
    have hsl := inv.spec_link; simp [Hex0.decode, Hex0.decodeS] at hsl ⊢; exact hsl
  have hnlt : ¬ cap < emitted.length := Nat.not_lt.mpr inv.emitted_le
  have hcs : Hex0.coreSpec inp cap = (0, emitted, emitted.length) := by
    simp only [Hex0.coreSpec, hdec, hnlt, if_false, Hex0.statusCode]
  obtain ⟨hp, ha0, ha1, hmem⟩ := heof
  refine ⟨4, hp, ?_, ?_, ?_⟩
  · rw [ha0]; simp [hcs]
  · rw [ha1]; simp [hcs]
  · intro j hj; rw [hcs] at hj ⊢; rw [hmem]; exact inv.out_mem j hj

/-- The induction (step 4): from any loop-invariant state the machine halts in a
    `coreSpec`-correct state. Structural induction on a fuel bound on the
    remaining input length; base = `eof_result`, step = `loop_iteration`. -/
theorem loop_correct (inp : List Nat) (cap : Nat) :
    ∀ (n : Nat) (rest emitted : List Nat) (s : State),
      rest.length ≤ n → LoopInv inp cap s rest emitted →
      ∃ m, Result (runFuel 0 m s) inp cap := by
  intro n
  induction n with
  | zero =>
    intro rest emitted s hn inv
    have : rest = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    subst this; exact eof_result inp cap emitted s inv
  | succ n ih =>
    intro rest emitted s hn inv
    cases rest with
    | nil => exact eof_result inp cap emitted s inv
    | cons c rest'' =>
      obtain ⟨k, hk⟩ := loop_iteration inp cap (c :: rest'') emitted s (by simp) inv
      cases hk with
      | inr hres => exact ⟨k, hres⟩
      | inl hstep =>
        obtain ⟨rest', emitted', hlt, inv'⟩ := hstep
        have hn' : rest'.length ≤ n := by
          simp only [List.length_cons] at hn hlt; omega
        obtain ⟨m, hm⟩ := ih rest' emitted' _ hn' inv'
        exact ⟨k + m, by rw [runFuel_add]; exact hm⟩

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
