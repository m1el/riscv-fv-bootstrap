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

@[simp] theorem rget_zero (s : State) : s.rget 0 = 0 := rfl
@[simp] theorem setPc_pc (s : State) (p : Word) : (s.setPc p).pc = p := rfl
@[simp] theorem setPc_mem (s : State) (p : Word) : (s.setPc p).mem = s.mem := rfl
@[simp] theorem setPc_rget (s : State) (p : Word) (i : Nat) : (s.setPc p).rget i = s.rget i := rfl
@[simp] theorem rset_pc (s : State) (rd : Nat) (v : Word) : (s.rset rd v).pc = s.pc := by
  unfold State.rset; split <;> rfl
@[simp] theorem rset_mem (s : State) (rd : Nat) (v : Word) : (s.rset rd v).mem = s.mem := by
  unfold State.rset; split <;> rfl
@[simp] theorem storeByte_pc (s : State) (a : Word) (b : Byte) : (s.storeByte a b).pc = s.pc := rfl
@[simp] theorem storeByte_rget (s : State) (a : Word) (b : Byte) (i : Nat) :
    (s.storeByte a b).rget i = s.rget i := rfl
theorem storeByte_mem (s : State) (a : Word) (b : Byte) :
    (s.storeByte a b).mem = fun x => if x = a then b else s.mem x := rfl
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

/-! ## `loadBytes` correctness (for the `core_refines` prologue). -/

/-- Reading outside the written region returns the original memory. -/
theorem loadBytes_frame (addr : Word) :
    ∀ (base : Nat) (bytes : List Nat) (m : Word → Byte),
      (∀ i, i < bytes.length → addr ≠ BitVec.ofNat 64 (base + i)) →
      Harness.loadBytes base bytes m addr = m addr := by
  intro base bytes
  induction bytes generalizing base with
  | nil => intro m _; rfl
  | cons b rest ih =>
    intro m h
    unfold Harness.loadBytes
    rw [ih (base + 1) _ (by
      intro i hi
      have := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [show base + (i + 1) = (base + 1) + i from by omega] at this)]
    rw [if_neg (by have := h 0 (by simp); simpa using this)]

/-- Reading the `j`-th written address returns the `j`-th byte. -/
theorem loadBytes_get :
    ∀ (base : Nat) (bytes : List Nat) (m : Word → Byte) (j : Nat),
      j < bytes.length → base + bytes.length ≤ 2 ^ 64 →
      Harness.loadBytes base bytes m (BitVec.ofNat 64 (base + j)) = BitVec.ofNat 8 (bytes.getD j 0) := by
  intro base bytes
  induction bytes generalizing base with
  | nil => intro m j hj _; simp at hj
  | cons b rest ih =>
    intro m j hj hlen
    unfold Harness.loadBytes
    cases j with
    | zero =>
      rw [loadBytes_frame (BitVec.ofNat 64 (base + 0)) (base + 1) rest _ (by
        intro i hi
        refine ofNat_ne _ _ ?_ ?_ ?_
        · simp only [List.length_cons] at hlen; omega
        · simp only [List.length_cons] at hlen; omega
        · omega)]
      simp [Nat.add_zero, List.getD_cons_zero]
    | succ j' =>
      rw [show base + (j' + 1) = (base + 1) + j' from by omega,
          ih (base + 1) _ j' (by simp only [List.length_cons] at hj; omega)
             (by simp only [List.length_cons] at hlen; omega),
          List.getD_cons_succ]

/-- Preconditions for the calling convention to be sound: the input region fits
    before the output region, and the output region fits in the address space.
    (The fixed addresses come from the linker; see Image.lean / TCB.md.) -/
structure WellFormed (inp : List Nat) (cap : Nat) : Prop where
  in_fits   : Image.inputAddr + inp.length ≤ Image.outAddr
  out_fits  : Image.outAddr + cap < 2 ^ 64
  bytes_ok  : ∀ b ∈ inp, b < 256

set_option maxRecDepth 4000 in
/-- `initOn` loads the code: the input `loadBytes` layer doesn't shadow the code
    region (they are adjacent-disjoint: code is `[coreAddr, inputAddr)`). -/
theorem code_initOn (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    CodeLoaded (Harness.initOn inp cap) := by
  intro i hi
  have hlen : Image.coreBytes.length = 324 := by decide
  show (Harness.loadBytes Image.inputAddr inp
        (Harness.loadBytes Image.coreAddr Image.coreBytes (fun _ => 0)))
        (BitVec.ofNat 64 (Image.coreAddr + i)) = BitVec.ofNat 8 (Image.coreBytes.getD i 0)
  rw [loadBytes_frame (BitVec.ofNat 64 (Image.coreAddr + i)) Image.inputAddr inp _ (by
    intro j hj
    refine ofNat_ne _ _ ?_ ?_ ?_
    · rw [hlen] at hi; simp only [Image.coreAddr]; omega
    · have := hwf.in_fits; have := hwf.out_fits; omega
    · rw [hlen] at hi; simp only [Image.coreAddr, Image.inputAddr]; omega)]
  exact loadBytes_get Image.coreAddr Image.coreBytes _ i hi (by decide)

/-- `initOn` loads the input. -/
theorem in_initOn (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    ∀ j, j < inp.length →
      (Harness.initOn inp cap).mem (BitVec.ofNat 64 (Image.inputAddr + j))
        = BitVec.ofNat 8 (inp.getD j 0) := by
  intro j hj
  show (Harness.loadBytes Image.inputAddr inp _) (BitVec.ofNat 64 (Image.inputAddr + j))
      = BitVec.ofNat 8 (inp.getD j 0)
  exact loadBytes_get Image.inputAddr inp _ j hj (by have := hwf.in_fits; have := hwf.out_fits; omega)

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
  -- region disjointness (static; from `WellFormed`): the input region ends at
  -- or before the output region, and the output region fits in memory. Needed
  -- so the `sb` store does not clobber code/input, and output indices are
  -- distinct addresses.
  in_fits   : Image.inputAddr + inp.length ≤ Image.outAddr
  out_lt    : Image.outAddr + cap < 2 ^ 64
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

/-- A single step (when not halted). -/
theorem runFuel_one (s : State) (h : s.pc ≠ 0) : runFuel 0 1 s = step s := by
  simp [runFuel, h]

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

set_option maxRecDepth 4000 in
/-- The `beq`-chain stepping for the newline spacing char: from `s4` (offset 24,
    `t2 = '\n'`), 6 steps (`li;beq` ×3, last taken) reach LOOP, touching only `t3`
    and `pc`. Demonstrates the per-char dispatch + loop-back pattern. -/
theorem spacing_tail_nl (s4 : State) (hcode : CodeLoaded s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image.coreAddr + 24))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 10) :
    (runFuel 0 6 s4).pc = LOOP ∧ (runFuel 0 6 s4).mem = s4.mem ∧
    (∀ i, i ≠ 28 → (runFuel 0 6 s4).rget i = s4.rget i) := by
  -- step 1: li t3,35
  have hu1 : step s4 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 28)) := by
    have e : s4.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 28) := by rw [hpc]; decide
    rw [step_addi s4 24 28 0 0x23#12 hcode (by decide) hpc (by decide),
        show s4.rget 0 + (0x23#12).signExtend 64 = BitVec.ofNat 64 35 from by rw [rget_zero]; decide, e]
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image.coreAddr + 28))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 28)) := rfl
  rw [← hv1] at hu1
  have hc1 : CodeLoaded v1 := by intro i hi; rw [hv1]; simp [hcode i hi]
  have h7v1 : v1.rget 7 = BitVec.ofNat 64 10 := by
    rw [hv1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]; exact ht2
  have h28v1 : v1.rget 28 = BitVec.ofNat 64 35 := by
    rw [hv1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  -- step 2: beq t2,t3 -- not taken (10 ≠ 35)
  have hu2 : step v1 = v1.setPc (BitVec.ofNat 64 (Image.coreAddr + 32)) := by
    have e : v1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 32) := by simp only [hv1, setPc_pc]; decide
    rw [step_beq v1 28 7 28 0x0d0#13 hc1 (by decide) rfl (by decide),
        h7v1, h28v1, if_neg (by decide : (BitVec.ofNat 64 10 : Word) ≠ BitVec.ofNat 64 35), e]
  let v2 := v1.setPc (BitVec.ofNat 64 (Image.coreAddr + 32))
  have hv2 : v2 = v1.setPc (BitVec.ofNat 64 (Image.coreAddr + 32)) := rfl
  rw [← hv2] at hu2
  have hc2 : CodeLoaded v2 := by intro i hi; rw [hv2]; simp [hc1 i hi]
  have h7v2 : v2.rget 7 = BitVec.ofNat 64 10 := by rw [hv2, setPc_rget]; exact h7v1
  -- step 3: li t3,59
  have hu3 : step v2 = (v2.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 36)) := by
    have e : v2.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 36) := by simp only [hv2, setPc_pc]; decide
    rw [step_addi v2 32 28 0 0x3b#12 hc2 (by decide) rfl (by decide),
        show v2.rget 0 + (0x3b#12).signExtend 64 = BitVec.ofNat 64 59 from by rw [rget_zero]; decide, e]
  let v3 := (v2.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image.coreAddr + 36))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 36)) := rfl
  rw [← hv3] at hu3
  have hc3 : CodeLoaded v3 := by intro i hi; rw [hv3]; simp [hc2 i hi]
  have h7v3 : v3.rget 7 = BitVec.ofNat 64 10 := by
    rw [hv3, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]; exact h7v2
  have h28v3 : v3.rget 28 = BitVec.ofNat 64 59 := by
    rw [hv3, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  -- step 4: beq -- not taken (10 ≠ 59)
  have hu4 : step v3 = v3.setPc (BitVec.ofNat 64 (Image.coreAddr + 40)) := by
    have e : v3.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 40) := by simp only [hv3, setPc_pc]; decide
    rw [step_beq v3 36 7 28 0x0c8#13 hc3 (by decide) rfl (by decide),
        h7v3, h28v3, if_neg (by decide : (BitVec.ofNat 64 10 : Word) ≠ BitVec.ofNat 64 59), e]
  let v4 := v3.setPc (BitVec.ofNat 64 (Image.coreAddr + 40))
  have hv4 : v4 = v3.setPc (BitVec.ofNat 64 (Image.coreAddr + 40)) := rfl
  rw [← hv4] at hu4
  have hc4 : CodeLoaded v4 := by intro i hi; rw [hv4]; simp [hc3 i hi]
  have h7v4 : v4.rget 7 = BitVec.ofNat 64 10 := by rw [hv4, setPc_rget]; exact h7v3
  -- step 5: li t3,10
  have hu5 : step v4 = (v4.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 44)) := by
    have e : v4.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 44) := by simp only [hv4, setPc_pc]; decide
    rw [step_addi v4 40 28 0 0x00a#12 hc4 (by decide) rfl (by decide),
        show v4.rget 0 + (0x00a#12).signExtend 64 = BitVec.ofNat 64 10 from by rw [rget_zero]; decide, e]
  let v5 := (v4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + 44))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 44)) := rfl
  rw [← hv5] at hu5
  have hc5 : CodeLoaded v5 := by intro i hi; rw [hv5]; simp [hc4 i hi]
  have h7v5 : v5.rget 7 = BitVec.ofNat 64 10 := by
    rw [hv5, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]; exact h7v4
  have h28v5 : v5.rget 28 = BitVec.ofNat 64 10 := by
    rw [hv5, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  -- step 6: beq -- TAKEN (10 = 10) -> LOOP
  have hu6 : step v5 = v5.setPc LOOP := by
    have e : v5.pc + (0x1fdc#13).signExtend 64 = LOOP := by simp only [hv5, setPc_pc]; decide
    rw [step_beq v5 44 7 28 0x1fdc#13 hc5 (by decide) rfl (by decide),
        h7v5, h28v5, if_pos rfl, e]
  -- assemble
  have hp0 : s4.pc ≠ 0 := by rw [hpc]; decide
  have hp1 : v1.pc ≠ 0 := by simp only [hv1, setPc_pc]; decide
  have hp2 : v2.pc ≠ 0 := by simp only [hv2, setPc_pc]; decide
  have hp3 : v3.pc ≠ 0 := by simp only [hv3, setPc_pc]; decide
  have hp4 : v4.pc ≠ 0 := by simp only [hv4, setPc_pc]; decide
  have hp5 : v5.pc ≠ 0 := by simp only [hv5, setPc_pc]; decide
  have hfinal : runFuel 0 6 s4 = v5.setPc LOOP := by
    simp only [runFuel]
    rw [hu1, hu2, hu3, hu4, hu5, hu6, if_neg hp0, if_neg hp1, if_neg hp2, if_neg hp3,
        if_neg hp4, if_neg hp5]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hfinal, setPc_pc]
  · rw [hfinal]; simp only [setPc_mem, hv5, hv4, hv3, hv2, hv1, rset_mem]
  · intro i hi
    rw [hfinal]
    by_cases h0 : i = 0
    · simp only [h0, rget_zero]
    rw [setPc_rget, hv5, setPc_rget, rset_rget _ _ _ _ (by decide) h0,
        if_neg hi, hv4, setPc_rget, hv3, setPc_rget,
        rset_rget _ _ _ _ (by decide) h0, if_neg hi, hv2, setPc_rget,
        hv1, setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg hi]

/-- The frame facts of a `(s.rset 28 v).setPc P` state: memory and every
    register other than `t3` are inherited from `s`. -/
theorem li_block_frame (s : State) (v P : Word) (i : Nat) (hi : i ≠ 28) :
    ((s.rset 28 v).setPc P).rget i = s.rget i := by
  by_cases h0 : i = 0
  · simp [h0]
  · rw [setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg hi]

set_option maxRecDepth 4000 in
/-- General spacing dispatch: from `s4` (offset 24, `t2 = c` with `c` a spacing
    char `∈ {10,32,95}`), the `beq`-chain reaches LOOP touching only `t3`/`pc`.
    Generalises `spacing_tail_nl` to all three spacing characters. -/
theorem spacing_tail (s4 : State) (hcode : CodeLoaded s4) (c : Nat)
    (hpc : s4.pc = BitVec.ofNat 64 (Image.coreAddr + 24))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c)
    (hs : Hex0.isSpace c = true) :
    ∃ k, (runFuel 0 k s4).pc = LOOP ∧ (runFuel 0 k s4).mem = s4.mem ∧
      (∀ i, i ≠ 28 → (runFuel 0 k s4).rget i = s4.rget i) := by
  -- the three spacing characters
  have hc : c = 10 ∨ c = 32 ∨ c = 95 := by
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, beq_iff_eq, Bool.or_eq_true] at hs
    exact hs
  -- block at off 24 (K=35), not taken
  have hb1 := li_beq_ne s4 24 35 c 0x00d0#13 hcode hpc ht2 (by decide) (by decide) (by decide)
    (by rw [ht2] <;> rcases hc with h|h|h <;> subst h <;> decide) (by decide)
  set s_b := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image.coreAddr + (24 + 8)))
    with hs_bdef
  have hcb : CodeLoaded s_b := by intro i hi; rw [hs_bdef]; simp [hcode i hi]
  have hpcb : s_b.pc = BitVec.ofNat 64 (Image.coreAddr + 32) := rfl
  have h7b : s_b.rget 7 = BitVec.ofNat 64 c := by rw [hs_bdef, li_block_frame _ _ _ _ (by decide)]; exact ht2
  -- block at off 32 (K=59), not taken
  have hb2 := li_beq_ne s_b 32 59 c 0x00c8#13 hcb hpcb h7b (by decide) (by decide) (by decide)
    (by rw [h7b] <;> rcases hc with h|h|h <;> subst h <;> decide) (by decide)
  set s_c := (s_b.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image.coreAddr + (32 + 8)))
    with hs_cdef
  have hcc : CodeLoaded s_c := by intro i hi; rw [hs_cdef]; simp [hcb i hi]
  have hpcc : s_c.pc = BitVec.ofNat 64 (Image.coreAddr + 40) := rfl
  have h7c : s_c.rget 7 = BitVec.ofNat 64 c := by rw [hs_cdef, li_block_frame _ _ _ _ (by decide)]; exact h7b
  rcases hc with h|h|h
  · -- c = 10: taken at off 40
    subst h
    have hb3 := li_beq_eq s_c 40 10 10 0x1fdc#13 LOOP hcc hpcc h7c (by decide) (by decide)
      (by decide) rfl (by decide) (by decide)
    refine ⟨2 + (2 + 2), ?_, ?_, ?_⟩
    · rw [runFuel_add, hb1, runFuel_add, hb2, hb3]; rfl
    · rw [runFuel_add, hb1, runFuel_add, hb2, hb3]
      simp only [setPc_mem, rset_mem, hs_cdef, hs_bdef]
    · intro i hi
      rw [runFuel_add, hb1, runFuel_add, hb2, hb3, li_block_frame _ _ _ _ hi, hs_cdef,
          li_block_frame _ _ _ _ hi, hs_bdef, li_block_frame _ _ _ _ hi]
  · -- c = 32: not taken at 40, taken at 48
    subst h
    have hb3 := li_beq_ne s_c 40 10 32 0x1fdc#13 hcc hpcc h7c (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set s_d := (s_c.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + (40 + 8)))
      with hs_ddef
    have hcd : CodeLoaded s_d := by intro i hi; rw [hs_ddef]; simp [hcc i hi]
    have hpcd : s_d.pc = BitVec.ofNat 64 (Image.coreAddr + 48) := rfl
    have h7d : s_d.rget 7 = BitVec.ofNat 64 32 := by rw [hs_ddef, li_block_frame _ _ _ _ (by decide)]; exact h7c
    have hb4 := li_beq_eq s_d 48 32 32 0x1fd4#13 LOOP hcd hpcd h7d (by decide) (by decide)
      (by decide) rfl (by decide) (by decide)
    refine ⟨2 + (2 + (2 + 2)), ?_, ?_, ?_⟩
    · rw [runFuel_add, hb1, runFuel_add, hb2, runFuel_add, hb3, hb4]; rfl
    · rw [runFuel_add, hb1, runFuel_add, hb2, runFuel_add, hb3, hb4]
      simp only [setPc_mem, rset_mem, hs_ddef, hs_cdef, hs_bdef]
    · intro i hi
      rw [runFuel_add, hb1, runFuel_add, hb2, runFuel_add, hb3, hb4,
          li_block_frame _ _ _ _ hi, hs_ddef, li_block_frame _ _ _ _ hi, hs_cdef,
          li_block_frame _ _ _ _ hi, hs_bdef, li_block_frame _ _ _ _ hi]
  · -- c = 95: not taken at 40 and 48, taken at 56
    subst h
    have hb3 := li_beq_ne s_c 40 10 95 0x1fdc#13 hcc hpcc h7c (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set s_d := (s_c.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + (40 + 8)))
      with hs_ddef
    have hcd : CodeLoaded s_d := by intro i hi; rw [hs_ddef]; simp [hcc i hi]
    have hpcd : s_d.pc = BitVec.ofNat 64 (Image.coreAddr + 48) := rfl
    have h7d : s_d.rget 7 = BitVec.ofNat 64 95 := by rw [hs_ddef, li_block_frame _ _ _ _ (by decide)]; exact h7c
    have hb4 := li_beq_ne s_d 48 32 95 0x1fd4#13 hcd hpcd h7d (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set s_e := (s_d.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image.coreAddr + (48 + 8)))
      with hs_edef
    have hce : CodeLoaded s_e := by intro i hi; rw [hs_edef]; simp [hcd i hi]
    have hpce : s_e.pc = BitVec.ofNat 64 (Image.coreAddr + 56) := rfl
    have h7e : s_e.rget 7 = BitVec.ofNat 64 95 := by rw [hs_edef, li_block_frame _ _ _ _ (by decide)]; exact h7d
    have hb5 := li_beq_eq s_e 56 95 95 0x1fcc#13 LOOP hce hpce h7e (by decide) (by decide)
      (by decide) rfl (by decide) (by decide)
    refine ⟨2 + (2 + (2 + (2 + 2))), ?_, ?_, ?_⟩
    · rw [runFuel_add, hb1, runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, hb5]; rfl
    · rw [runFuel_add, hb1, runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, hb5]
      simp only [setPc_mem, rset_mem, hs_edef, hs_ddef, hs_cdef, hs_bdef]
    · intro i hi
      rw [runFuel_add, hb1, runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, hb5,
          li_block_frame _ _ _ _ hi, hs_edef, li_block_frame _ _ _ _ hi, hs_ddef,
          li_block_frame _ _ _ _ hi, hs_cdef, li_block_frame _ _ _ _ hi, hs_bdef,
          li_block_frame _ _ _ _ hi]

/-- Rebuild the loop invariant after a spacing token: same `emitted`, suffix
    shortened by one, index bumped. Used by the spacing case of `loop_iteration`. -/
theorem spacing_loopinv (inp : List Nat) (cap : Nat) (c : Nat) (rest' emitted : List Nat)
    (s s' : State) (inv : LoopInv inp cap s (c :: rest') emitted)
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = true)
    (hpc' : s'.pc = LOOP) (hmem' : s'.mem = s.mem)
    (h5 : s'.rget 5 = s.rget 5 + 1)
    (hp1 : s'.rget 1 = s.rget 1) (hp6 : s'.rget 6 = s.rget 6)
    (hp10 : s'.rget 10 = s.rget 10) (hp11 : s'.rget 11 = s.rget 11)
    (hp12 : s'.rget 12 = s.rget 12) (hp13 : s'.rget 13 = s.rget 13) :
    LoopInv inp cap s' rest' emitted := by
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons] at h; omega
  refine { at_loop := hpc', code := ?_, a0 := ?_, a1 := ?_, a2 := ?_, a3 := ?_,
           ra0 := ?_, in_mem := ?_, in_lt := inv.in_lt, bytes_lt := inv.bytes_lt,
           in_fits := inv.in_fits, out_lt := inv.out_lt,
           idx := ?_, suffix := ?_, outidx := ?_, emitted_le := inv.emitted_le,
           out_mem := ?_, spec_link := ?_ }
  · intro i hi; rw [hmem']; exact inv.code i hi
  · rw [hp10]; exact inv.a0
  · rw [hp11]; exact inv.a1
  · rw [hp12]; exact inv.a2
  · rw [hp13]; exact inv.a3
  · rw [hp1]; exact inv.ra0
  · intro j hj; rw [hmem']; exact inv.in_mem j hj
  · rw [h5, inv.idx, show (1 : Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
    congr 1; simp only [List.length_cons]; omega
  · have hk : inp.length - rest'.length = (inp.length - (c :: rest').length) + 1 := by
      simp only [List.length_cons]; omega
    rw [hk, ← List.tail_drop, inv.suffix]; rfl
  · rw [hp6]; exact inv.outidx
  · intro j hj; rw [hmem']; exact inv.out_mem j hj
  · rw [inv.spec_link, decodeS_spacing c rest' hsc hss]

/-- A COMPLETE main-loop iteration for the newline spacing token: combines
    `loop_prefix` (read the char) + `spacing_tail_nl` (dispatch to loop) +
    `spacing_loopinv` (rebuild the invariant). From `LoopInv .. (10 :: rest')`,
    the machine reaches a `LoopInv .. rest'` state -- one full step proved. -/
theorem loop_spacing_nl (inp : List Nat) (cap : Nat) (rest' emitted : List Nat) (s : State)
    (inv : LoopInv inp cap s (10 :: rest') emitted) :
    ∃ k, LoopInv inp cap (runFuel 0 k s) rest' emitted := by
  obtain ⟨s4, hrun4, hpc4, ht2, ht0, hmem4, hcode4, hother4⟩ :=
    loop_prefix inp cap 10 rest' emitted s inv
  obtain ⟨htpc, htmem, htother⟩ := spacing_tail_nl s4 hcode4 hpc4 ht2
  refine ⟨4 + 6, ?_⟩
  rw [runFuel_add, hrun4]
  exact spacing_loopinv inp cap 10 rest' emitted s (runFuel 0 6 s4) inv (by decide) (by decide)
    htpc (by rw [htmem, hmem4])
    (by rw [htother 5 (by decide), ht0])
    (by rw [htother 1 (by decide), hother4 1 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 6 (by decide), hother4 6 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 10 (by decide), hother4 10 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 11 (by decide), hother4 11 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 12 (by decide), hother4 12 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 13 (by decide), hother4 13 (by decide) (by decide) (by decide) (by decide)])

/-- A COMPLETE main-loop iteration for ANY spacing token (`c ∈ {10,32,95}`):
    `loop_prefix` (read the char) + `spacing_tail` (dispatch to loop) +
    `spacing_loopinv` (rebuild). Generalises `loop_spacing_nl`. -/
theorem loop_spacing (inp : List Nat) (cap : Nat) (c : Nat) (rest' emitted : List Nat) (s : State)
    (hss : Hex0.isSpace c = true) (inv : LoopInv inp cap s (c :: rest') emitted) :
    ∃ k, LoopInv inp cap (runFuel 0 k s) rest' emitted := by
  have hsc : Hex0.isComment c = false := by
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, beq_iff_eq, Bool.or_eq_true] at hss
    rcases hss with h|h|h <;> subst h <;> decide
  obtain ⟨s4, hrun4, hpc4, ht2, ht0, hmem4, hcode4, hother4⟩ :=
    loop_prefix inp cap c rest' emitted s inv
  obtain ⟨k, htpc, htmem, htother⟩ := spacing_tail s4 hcode4 c hpc4 ht2 hss
  refine ⟨4 + k, ?_⟩
  rw [runFuel_add, hrun4]
  exact spacing_loopinv inp cap c rest' emitted s (runFuel 0 k s4) inv hsc hss
    htpc (by rw [htmem, hmem4])
    (by rw [htother 5 (by decide), ht0])
    (by rw [htother 1 (by decide), hother4 1 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 6 (by decide), hother4 6 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 10 (by decide), hother4 10 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 11 (by decide), hother4 11 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 12 (by decide), hother4 12 (by decide) (by decide) (by decide) (by decide)])
    (by rw [htother 13 (by decide), hother4 13 (by decide) (by decide) (by decide) (by decide)])

set_option maxRecDepth 4000 in
/-- Reusable block: a `li t3,K; beq t2,t3` pair where `t2 = c ≠ K` runs as 2
    steps, advancing the pc by 8 (and clobbering only `t3`). Compresses the
    `beq`-dispatch chains in `loop_iteration`'s cases. -/
theorem li_beq_ne (s : State) (off K c : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbeq : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.beq 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hne : (BitVec.ofNat 64 c : Word) ≠ BitVec.ofNat 64 K)
    (ho2 : off + 4 + 3 < Image.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 4 + 3 < 324 := hcl ▸ ho2
  have ho1 : off + 3 < Image.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have e8 : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := by
    rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
  have hu2 : step s1 = s1.setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
    rw [step_beq s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbeq, h7s1, h28s1, if_neg hne, e8]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 4000 in
/-- Reusable block: a `li t3,K; beq t2,t3` pair where `t2 = c = K` runs as 2
    steps, branching to `target` (the `beq` is taken). Mirror of `li_beq_ne`.
    Clobbers only `t3` and `pc`. -/
theorem li_beq_eq (s : State) (off K c : Nat) (imm : BitVec 13) (target : Word)
    (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbeq : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.beq 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (heq : (BitVec.ofNat 64 c : Word) = BitVec.ofNat 64 K)
    (htgt : BitVec.ofNat 64 (Image.coreAddr + (off + 4)) + imm.signExtend 64 = target)
    (ho2 : off + 4 + 3 < Image.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc target := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 4 + 3 < 324 := hcl ▸ ho2
  have ho1 : off + 3 < Image.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hu2 : step s1 = s1.setPc target := by
    rw [step_beq s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbeq, h7s1, h28s1,
        if_pos heq, hpc1, htgt]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

/-- Signed `<` on `ofNat` values below `2^63` agrees with `Nat` `<` (resolves
    the `blt`/`bge` in the nibble-parse chains, where operands are `< 256`). -/
theorem slt_ofNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a).slt (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.slt,
      BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_decide.mpr (by omega)

/-- `addi rd,rs1,imm` with `imm` a (negative) two's-complement offset `-sub`
    computes `rs1 - sub` when `rs1 ≥ sub`. Used for the nibble value `c - 48` /
    `c - 55`. -/
theorem nibble_addi (c sub : Nat) (imm : BitVec 12)
    (hsx : imm.signExtend 64 = BitVec.ofNat 64 (2 ^ 64 - sub)) (hsub : sub ≤ c) (hc : c < 2 ^ 64) :
    BitVec.ofNat 64 c + imm.signExtend 64 = BitVec.ofNat 64 (c - sub) := by
  rw [hsx, addr_ofNat_succ]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- `nibble` always yields a value `< 16` (a single hex digit). -/
theorem nibble_lt (c v : Nat) (h : Hex0.nibble c = some v) : v < 16 := by
  unfold Hex0.nibble at h; split at h <;> simp_all <;> omega

/-- A hex digit is never a low-stop char (`\n ' ' '_' '#' ';'`). -/
theorem nibble_not_lowstop (l v : Nat) (h : Hex0.nibble l = some v) : Hex0.isLowStop l = false := by
  have hr : (48 ≤ l ∧ l ≤ 57) ∨ (65 ≤ l ∧ l ≤ 70) := by
    simp only [Hex0.nibble] at h
    by_cases hd : 48 ≤ l ∧ l ≤ 57
    · exact Or.inl hd
    · rw [if_neg hd] at h
      by_cases he : 65 ≤ l ∧ l ≤ 70
      · exact Or.inr he
      · rw [if_neg he] at h; exact absurd h (by simp)
  simp only [Hex0.isLowStop, Hex0.isSpace, Hex0.isComment, Hex0.c_nl, Hex0.c_sp, Hex0.c_us,
    Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  omega

set_option maxRecDepth 8000 in
/-- Closed enumeration (256 cases): combining two 4-bit nibbles. -/
theorem comb4 : ∀ (x y : BitVec 4),
    (((x.setWidth 64) <<< 4 ||| (y.setWidth 64)).setWidth 8 : BitVec 8)
      = BitVec.ofNat 8 (x.toNat * 16 + y.toNat) := by decide

set_option maxRecDepth 8000 in
/-- The byte assembled by `slli t4,t4,4; or t4,t4,t5` (with `t4 = hi`, `t5 = lo`,
    both `< 16`): `(hi <<< 4) ||| lo`, truncated to a byte by `sb`, equals
    `hi*16 + lo` — exactly the value `decodeS_byte` emits. -/
theorem combine_nibbles (hi lo : Nat) (hhi : hi < 16) (hlo : lo < 16) :
    (((BitVec.ofNat 64 hi) <<< 4 ||| (BitVec.ofNat 64 lo)).setWidth 8 : BitVec 8)
      = BitVec.ofNat 8 (hi * 16 + lo) := by
  have ex : BitVec.ofNat 64 hi = (BitVec.ofNat 4 hi).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhi,
          Nat.mod_eq_of_lt (by omega : hi < 2 ^ 64)]
  have ey : BitVec.ofNat 64 lo = (BitVec.ofNat 4 lo).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlo,
          Nat.mod_eq_of_lt (by omega : lo < 2 ^ 64)]
  rw [ex, ey, comb4 (BitVec.ofNat 4 hi) (BitVec.ofNat 4 lo),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hlo]

set_option maxRecDepth 4000 in
/-- `li t3,K; blt t2,t3` with `t2 = c ≥ K`: the `blt` is NOT taken; 2 steps
    advance `pc` by 8, clobbering only `t3`. -/
theorem li_blt_nt (s : State) (off K c : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hblt : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.blt 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hge : ¬ c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (ho2 : off + 4 + 3 < Image.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 4 + 3 < 324 := hcl ▸ ho2
  have ho1 : off + 3 < Image.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hslt : (s1.rget 7).slt (s1.rget 28) = false := by
    rw [h7s1, h28s1, slt_ofNat _ _ hc63 hK63]; exact decide_eq_false (by omega)
  have e8 : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := by
    rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
  have hu2 : step s1 = s1.setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
    rw [step_blt s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hblt, hslt,
        if_neg (by decide : ¬((false:Bool)=true)), e8]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 4000 in
/-- `li t3,K; bge t2,t3` with `t2 = c < K`: the `bge` is NOT taken; 2 steps
    advance `pc` by 8, clobbering only `t3`. -/
theorem li_bge_nt (s : State) (off K c : Nat) (imm : BitVec 13) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbge : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.bge 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hlt : c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (ho2 : off + 4 + 3 < Image.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 4 + 3 < 324 := hcl ▸ ho2
  have ho1 : off + 3 < Image.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hslt : (s1.rget 7).slt (s1.rget 28) = true := by
    rw [h7s1, h28s1, slt_ofNat _ _ hc63 hK63]; exact decide_eq_true (by omega)
  have e8 : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := by
    rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
  have hu2 : step s1 = s1.setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
    rw [step_bge s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbge, hslt, if_pos rfl, e8]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 4000 in
/-- `li t3,K; bge t2,t3` with `t2 = c ≥ K`: the `bge` IS taken, branching to
    `target`. Clobbers only `t3`/`pc`. -/
theorem li_bge_t (s : State) (off K c : Nat) (imm : BitVec 13) (target : Word) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbge : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.bge 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hge : ¬ c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (htgt : BitVec.ofNat 64 (Image.coreAddr + (off + 4)) + imm.signExtend 64 = target)
    (ho2 : off + 4 + 3 < Image.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc target := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 4 + 3 < 324 := hcl ▸ ho2
  have ho1 : off + 3 < Image.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hslt : (s1.rget 7).slt (s1.rget 28) = false := by
    rw [h7s1, h28s1, slt_ofNat _ _ hc63 hK63]; exact decide_eq_false (by omega)
  have hu2 : step s1 = s1.setPc target := by
    rw [step_bge s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbge, hslt,
        if_neg (by decide : ¬((false:Bool)=true)), hpc1, htgt]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 4000 in
/-- `li t3,K; blt t2,t3` with `t2 = c < K`: the `blt` IS taken, branching to
    `target`. Clobbers only `t3`/`pc`. (Used by the error/`unknown` paths.) -/
theorem li_blt_t (s : State) (off K c : Nat) (imm : BitVec 13) (target : Word) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hblt : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.blt 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hlt : c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (htgt : BitVec.ofNat 64 (Image.coreAddr + (off + 4)) + imm.signExtend 64 = target)
    (ho2 : off + 4 + 3 < Image.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc target := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 4 + 3 < 324 := hcl ▸ ho2
  have ho1 : off + 3 < Image.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hslt : (s1.rget 7).slt (s1.rget 28) = true := by
    rw [h7s1, h28s1, slt_ofNat _ _ hc63 hK63]; exact decide_eq_true (by omega)
  have hu2 : step s1 = s1.setPc target := by
    rw [step_blt s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hblt, hslt, if_pos rfl, hpc1, htgt]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega) (by decide)
      (by simp only [Image.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 4000 in
/-- The high `beq`-chain (offsets 24..60) when `c` is none of the five stop
    chars: all five `beq` fall through, reaching offset 64 in 10 steps, touching
    only `t3`/`pc`. -/
theorem high_beq_ft (s : State) (hcode : CodeLoaded s) (c : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 24)) (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hc256 : c < 256)
    (h35 : c ≠ 35) (h59 : c ≠ 59) (h10 : c ≠ 10) (h32 : c ≠ 32) (h95 : c ≠ 95) :
    (runFuel 0 10 s).pc = BitVec.ofNat 64 (Image.coreAddr + 64) ∧
    (runFuel 0 10 s).mem = s.mem ∧
    (∀ i, i ≠ 28 → (runFuel 0 10 s).rget i = s.rget i) := by
  have hc64 : c < 2 ^ 64 := Nat.lt_trans hc256 (by decide)
  have b1 := li_beq_ne s 24 35 c 0x00d0#13 hcode hpc h7 (by decide) (by decide) (by decide)
    (ofNat_ne c 35 hc64 (by decide) h35) (by decide)
  set sb := (s.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image.coreAddr + (24 + 8)))
    with hsb
  have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hcode i hi]
  have h7b : sb.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7
  have b2 := li_beq_ne sb 32 59 c 0x00c8#13 hcb rfl h7b (by decide) (by decide) (by decide)
    (ofNat_ne c 59 hc64 (by decide) h59) (by decide)
  set sc := (sb.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image.coreAddr + (32 + 8)))
    with hsc
  have hcc : CodeLoaded sc := by intro i hi; rw [hsc]; simp [hcb i hi]
  have h7c : sc.rget 7 = BitVec.ofNat 64 c := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
  have b3 := li_beq_ne sc 40 10 c 0x1fdc#13 hcc rfl h7c (by decide) (by decide) (by decide)
    (ofNat_ne c 10 hc64 (by decide) h10) (by decide)
  set sd := (sc.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + (40 + 8)))
    with hsd
  have hcd : CodeLoaded sd := by intro i hi; rw [hsd]; simp [hcc i hi]
  have h7d : sd.rget 7 = BitVec.ofNat 64 c := by rw [hsd, li_block_frame _ _ _ _ (by decide)]; exact h7c
  have b4 := li_beq_ne sd 48 32 c 0x1fd4#13 hcd rfl h7d (by decide) (by decide) (by decide)
    (ofNat_ne c 32 hc64 (by decide) h32) (by decide)
  set se := (sd.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image.coreAddr + (48 + 8)))
    with hse
  have hce : CodeLoaded se := by intro i hi; rw [hse]; simp [hcd i hi]
  have h7e : se.rget 7 = BitVec.ofNat 64 c := by rw [hse, li_block_frame _ _ _ _ (by decide)]; exact h7d
  have b5 := li_beq_ne se 56 95 c 0x1fcc#13 hce rfl h7e (by decide) (by decide) (by decide)
    (ofNat_ne c 95 hc64 (by decide) h95) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (10:Nat) = 2+(2+(2+(2+2))) from rfl, runFuel_add, b1, runFuel_add, b2,
        runFuel_add, b3, runFuel_add, b4, b5]; rfl
  · rw [show (10:Nat) = 2+(2+(2+(2+2))) from rfl, runFuel_add, b1, runFuel_add, b2,
        runFuel_add, b3, runFuel_add, b4, b5]
    simp only [setPc_mem, rset_mem, hse, hsd, hsc, hsb]
  · intro i hi
    rw [show (10:Nat) = 2+(2+(2+(2+2))) from rfl, runFuel_add, b1, runFuel_add, b2,
        runFuel_add, b3, runFuel_add, b4, b5, li_block_frame _ _ _ _ hi, hse,
        li_block_frame _ _ _ _ hi, hsd, li_block_frame _ _ _ _ hi, hsc,
        li_block_frame _ _ _ _ hi, hsb, li_block_frame _ _ _ _ hi]

set_option maxRecDepth 4000 in
/-- The low `beq`-chain (offsets 124..160) when `c` is none of the five stop
    chars: all five fall through, reaching offset 164 in 10 steps. -/
theorem low_beq_ft (s : State) (hcode : CodeLoaded s) (c : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 124)) (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hc256 : c < 256)
    (h35 : c ≠ 35) (h59 : c ≠ 59) (h10 : c ≠ 10) (h32 : c ≠ 32) (h95 : c ≠ 95) :
    (runFuel 0 10 s).pc = BitVec.ofNat 64 (Image.coreAddr + 164) ∧
    (runFuel 0 10 s).mem = s.mem ∧
    (∀ i, i ≠ 28 → (runFuel 0 10 s).rget i = s.rget i) := by
  have hc64 : c < 2 ^ 64 := Nat.lt_trans hc256 (by decide)
  have b1 := li_beq_ne s 124 10 c 0x00a0#13 hcode hpc h7 (by decide) (by decide) (by decide)
    (ofNat_ne c 10 hc64 (by decide) h10) (by decide)
  set sb := (s.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + (124 + 8)))
    with hsb
  have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hcode i hi]
  have h7b : sb.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7
  have b2 := li_beq_ne sb 132 32 c 0x098#13 hcb rfl h7b (by decide) (by decide) (by decide)
    (ofNat_ne c 32 hc64 (by decide) h32) (by decide)
  set sc := (sb.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image.coreAddr + (132 + 8)))
    with hsc
  have hcc : CodeLoaded sc := by intro i hi; rw [hsc]; simp [hcb i hi]
  have h7c : sc.rget 7 = BitVec.ofNat 64 c := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
  have b3 := li_beq_ne sc 140 95 c 0x090#13 hcc rfl h7c (by decide) (by decide) (by decide)
    (ofNat_ne c 95 hc64 (by decide) h95) (by decide)
  set sd := (sc.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image.coreAddr + (140 + 8)))
    with hsd
  have hcd : CodeLoaded sd := by intro i hi; rw [hsd]; simp [hcc i hi]
  have h7d : sd.rget 7 = BitVec.ofNat 64 c := by rw [hsd, li_block_frame _ _ _ _ (by decide)]; exact h7c
  have b4 := li_beq_ne sd 148 35 c 0x088#13 hcd rfl h7d (by decide) (by decide) (by decide)
    (ofNat_ne c 35 hc64 (by decide) h35) (by decide)
  set se := (sd.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image.coreAddr + (148 + 8)))
    with hse
  have hce : CodeLoaded se := by intro i hi; rw [hse]; simp [hcd i hi]
  have h7e : se.rget 7 = BitVec.ofNat 64 c := by rw [hse, li_block_frame _ _ _ _ (by decide)]; exact h7d
  have b5 := li_beq_ne se 156 59 c 0x080#13 hce rfl h7e (by decide) (by decide) (by decide)
    (ofNat_ne c 59 hc64 (by decide) h59) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (10:Nat) = 2+(2+(2+(2+2))) from rfl, runFuel_add, b1, runFuel_add, b2,
        runFuel_add, b3, runFuel_add, b4, b5]; rfl
  · rw [show (10:Nat) = 2+(2+(2+(2+2))) from rfl, runFuel_add, b1, runFuel_add, b2,
        runFuel_add, b3, runFuel_add, b4, b5]
    simp only [setPc_mem, rset_mem, hse, hsd, hsc, hsb]
  · intro i hi
    rw [show (10:Nat) = 2+(2+(2+(2+2))) from rfl, runFuel_add, b1, runFuel_add, b2,
        runFuel_add, b3, runFuel_add, b4, b5, li_block_frame _ _ _ _ hi, hse,
        li_block_frame _ _ _ _ hi, hsd, li_block_frame _ _ _ _ hi, hsc,
        li_block_frame _ _ _ _ hi, hsb, li_block_frame _ _ _ _ hi]

set_option maxRecDepth 4000 in
/-- Generalised input-read head `bgeu(not taken); add; lbu; addi` at any offset
    `off` whose four words are this shape (true at `off = 8` and `off = 108`).
    Reads `inp[idx]` into `t2`, bumps `t0`, leaving memory and other registers
    intact. (`loop_prefix` is the `off = 8` instance specialised to `LoopInv`.) -/
theorem read_prefix (s : State) (off : Nat) (immB : BitVec 13) (inp : List Nat)
    (idx ch : Nat) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hbgeu : Rv64i.decode (wordAt off) = Rv64i.Instr.bgeu 5 11 immB)
    (hadd : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.add 28 10 5)
    (hlbu : Rv64i.decode (wordAt (off + 8)) = Rv64i.Instr.lbu 7 28 0#12)
    (haddi : Rv64i.decode (wordAt (off + 12)) = Rv64i.Instr.addi 5 5 1#12)
    (hoff : off + 12 + 3 < Image.coreBytes.length)
    (ha0 : s.rget 10 = BitVec.ofNat 64 Image.inputAddr)
    (ha1 : s.rget 11 = BitVec.ofNat 64 inp.length)
    (ht0 : s.rget 5 = BitVec.ofNat 64 idx)
    (hlt : idx < inp.length) (hinlt : inp.length < 2 ^ 64)
    (hin_mem : ∀ j, j < inp.length →
       s.mem (BitVec.ofNat 64 (Image.inputAddr + j)) = BitVec.ofNat 8 (inp.getD j 0))
    (hch : inp.getD idx 0 = ch) (hch256 : ch < 256) :
    ∃ s4, runFuel 0 4 s = s4 ∧
      s4.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 16)) ∧
      s4.rget 7 = BitVec.ofNat 64 ch ∧ s4.rget 5 = s.rget 5 + 1 ∧
      s4.mem = s.mem ∧ CodeLoaded s4 ∧
      (∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s4.rget i = s.rget i) := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 12 + 3 < 324 := hcl ▸ hoff
  -- step 1: bgeu -- NOT taken (idx < len)
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [ht0, ha1]; exact ult_ofNat _ _ hinlt hlt
  have hs1 : step s = s.setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    have e : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
      rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
    rw [step_bgeu s off 5 11 immB hcode (by omega) hpc hbgeu, if_pos hult, e]
  let s1 := s.setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1d : s1 = s.setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1d] at hs1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1d]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  -- step 2: add t3,a0,t0
  have haddr : s1.rget 10 + s1.rget 5 = BitVec.ofNat 64 (Image.inputAddr + idx) := by
    show s.rget 10 + s.rget 5 = _
    rw [ha0, ht0]; exact addr_ofNat_succ _ _
  have hs2 : step s1 = (s1.rset 28 (BitVec.ofNat 64 (Image.inputAddr + idx))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
    have e : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := by
      rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
    rw [step_add s1 (off+4) 28 10 5 hc1 (by omega) hpc1 hadd, haddr, e]
  let s2 := (s1.rset 28 (BitVec.ofNat 64 (Image.inputAddr + idx))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 8)))
  have hs2d : s2 = (s1.rset 28 (BitVec.ofNat 64 (Image.inputAddr + idx))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := rfl
  rw [← hs2d] at hs2
  have hc2 : CodeLoaded s2 := by
    intro i hi; have := hc1 i hi; simp only [hs2d, setPc_mem, rset_mem]; exact this
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := rfl
  -- step 3: lbu t2,0(t3)
  have hr28 : s2.rget 28 = BitVec.ofNat 64 (Image.inputAddr + idx) := by
    rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hbyte : (s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64
      = BitVec.ofNat 64 ch := by
    rw [hr28, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
    show (s2.mem _).setWidth 64 = _
    rw [hs2d]; simp only [setPc_mem, rset_mem, hs1d]
    rw [hin_mem _ hlt, hch, setWidth8_64 ch hch256]
  have hs3 : step s2 = (s2.rset 7 (BitVec.ofNat 64 ch)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 12))) := by
    have e : s2.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 12)) := by
      rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
    rw [step_lbu s2 (off+8) 7 28 0#12 hc2 (by omega) hpc2 hlbu]
    show (s2.rset 7 ((s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64)).setPc _
       = (s2.rset 7 (BitVec.ofNat 64 ch)).setPc _
    rw [hbyte, e]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 ch)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 12)))
  have hs3d : s3 = (s2.rset 7 (BitVec.ofNat 64 ch)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 12))) := rfl
  rw [← hs3d] at hs3
  have hc3 : CodeLoaded s3 := by
    intro i hi; have := hc2 i hi; simp only [hs3d, setPc_mem, rset_mem]; exact this
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 12)) := rfl
  have hr5_3 : s3.rget 5 = s.rget 5 := by
    rw [hs3d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 7), hs2d, setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28),
        hs1d, setPc_rget]
  -- step 4: addi t0,t0,1
  have hs4 : step s3 = (s3.rset 5 (s.rget 5 + 1)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 16))) := by
    have e : s3.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 16)) := by
      rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
    rw [step_addi s3 (off+12) 5 5 1#12 hc3 (by omega) hpc3 haddi, e, hr5_3,
        show (1#12).signExtend 64 = (1 : Word) from by decide]
  let s4 := (s3.rset 5 (s.rget 5 + 1)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 16)))
  have hs4d : s4 = (s3.rset 5 (s.rget 5 + 1)).setPc
        (BitVec.ofNat 64 (Image.coreAddr + (off + 16))) := rfl
  rw [← hs4d] at hs4
  have hp0 : s.pc ≠ 0 := by rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  have hp3 : s3.pc ≠ 0 := by rw [hpc3]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
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

set_option maxRecDepth 4000 in
/-- The high-nibble parse (offsets 64..104): given `nibble c = some hi` (so `c`
    is a hex digit), the machine reaches `have_high` (offset 108) with `t4 = hi`,
    touching only `t3`/`t4`/`pc`. Cases on digit (`'0'..'9'`) vs letter (`'A'..'F'`). -/
theorem high_parse (s : State) (hcode : CodeLoaded s) (c hi : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 64)) (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hc256 : c < 256) (hn : Hex0.nibble c = some hi) :
    ∃ k, (runFuel 0 k s).pc = BitVec.ofNat 64 (Image.coreAddr + 108) ∧
      (runFuel 0 k s).mem = s.mem ∧
      (runFuel 0 k s).rget 29 = BitVec.ofNat 64 hi ∧
      (∀ i, i ≠ 28 → i ≠ 29 → (runFuel 0 k s).rget i = s.rget i) := by
  have hc64 : c < 2 ^ 64 := Nat.lt_trans hc256 (by decide)
  have hcase : (48 ≤ c ∧ c ≤ 57 ∧ c - 48 = hi) ∨ (65 ≤ c ∧ c ≤ 70 ∧ c - 55 = hi) := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn; exact Or.inl ⟨hd.1, hd.2, Option.some.inj hn⟩
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn; exact Or.inr ⟨hl.1, hl.2, Option.some.inj hn⟩
      · rw [if_neg hl] at hn; exact absurd hn (by simp)
  rcases hcase with ⟨h48, h57, hhi⟩ | ⟨h65, h70, hhi⟩
  · -- digit: li 48 (nt), li 58 bge (nt), addi t4=c-48, jal -> 108
    have bA := li_blt_nt s 64 48 c 0x00f4#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_a := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (64 + 8)))
      with hsa
    have hca : CodeLoaded s_a := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : s_a.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_nt s_a 72 58 c 0x000c#13 hca rfl h7a (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_b := (s_a.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + (72 + 8)))
      with hsb
    have hcb : CodeLoaded s_b := by intro i hi; rw [hsb]; simp [hca i hi]
    have hpcb : s_b.pc = BitVec.ofNat 64 (Image.coreAddr + 80) := rfl
    have h7b : s_b.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    -- addi t4,t2,-48  (off 80)
    have haddi : step s_b = (s_b.rset 29 (BitVec.ofNat 64 (c - 48))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 84)) := by
      rw [step_addi s_b 80 29 7 0xfd0#12 hcb (by decide) hpcb (by decide), h7b,
          nibble_addi c 48 0xfd0#12 (by decide) h48 hc64,
          show s_b.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 84) from by rw [hpcb]; decide]
    set s_c := (s_b.rset 29 (BitVec.ofNat 64 (c - 48))).setPc (BitVec.ofNat 64 (Image.coreAddr + 84))
      with hsc
    have hcc : CodeLoaded s_c := by intro i hi; rw [hsc]; simp [hcb i hi]
    have hpcc : s_c.pc = BitVec.ofNat 64 (Image.coreAddr + 84) := rfl
    -- jal -> 108
    have hjal : step s_c = s_c.setPc (BitVec.ofNat 64 (Image.coreAddr + 108)) := by
      rw [step_jal s_c 84 0 0x000018#21 hcc (by decide) hpcc (by decide), rset_zero,
          show s_c.pc + (0x000018#21).signExtend 64 = BitVec.ofNat 64 (Image.coreAddr + 108)
            from by rw [hpcc]; decide]
    have hpb0 : s_b.pc ≠ 0 := by rw [hpcb]; decide
    have hpc0 : s_c.pc ≠ 0 := by rw [hpcc]; decide
    have hbc : runFuel 0 2 s_b = s_c.setPc (BitVec.ofNat 64 (Image.coreAddr + 108)) := by
      simp only [runFuel]; rw [if_neg hpb0, haddi, ← hsc, if_neg hpc0, hjal]
    refine ⟨2 + (2 + 2), ?_, ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, hbc]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, hbc]
      simp only [setPc_mem, hsc, rset_mem, hsb, hsa]
    · rw [runFuel_add, bA, runFuel_add, bB, hbc, setPc_rget, hsc, setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide), hhi]
    · intro i hi28 hi29
      rw [runFuel_add, bA, runFuel_add, bB, hbc, setPc_rget, hsc, setPc_rget,
          rset_rget _ _ _ _ (by decide) hi29, li_block_frame _ _ _ _ hi28, hsb,
          li_block_frame _ _ _ _ hi28, hsa, li_block_frame _ _ _ _ hi28]
  · -- letter: li 48 (nt), li 58 bge (taken ->88), li 65 (nt), li 71 bge (nt), addi t4=c-55
    have bA := li_blt_nt s 64 48 c 0x00f4#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_a := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (64 + 8)))
      with hsa
    have hca : CodeLoaded s_a := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : s_a.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_t s_a 72 58 c 0x000c#13 (BitVec.ofNat 64 (Image.coreAddr + 88))
      hca rfl h7a (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
      (by decide) (by decide)
    set s_b := (s_a.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + 88))
      with hsb
    have hcb : CodeLoaded s_b := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : s_b.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_blt_nt s_b 88 65 c 0x00dc#13 hcb rfl h7b (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_c := (s_b.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image.coreAddr + (88 + 8)))
      with hsc
    have hcc : CodeLoaded s_c := by intro i hi; rw [hsc]; simp [hcb i hi]
    have h7c : s_c.rget 7 = BitVec.ofNat 64 c := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
    have bD := li_bge_nt s_c 96 71 c 0x00d4#13 hcc rfl h7c (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_d := (s_c.rset 28 (BitVec.ofNat 64 71)).setPc (BitVec.ofNat 64 (Image.coreAddr + (96 + 8)))
      with hsd
    have hcd : CodeLoaded s_d := by intro i hi; rw [hsd]; simp [hcc i hi]
    have hpcd : s_d.pc = BitVec.ofNat 64 (Image.coreAddr + 104) := rfl
    have h7d : s_d.rget 7 = BitVec.ofNat 64 c := by rw [hsd, li_block_frame _ _ _ _ (by decide)]; exact h7c
    -- addi t4,t2,-55  (off 104) -> falls through to 108
    have haddi : step s_d = (s_d.rset 29 (BitVec.ofNat 64 (c - 55))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 108)) := by
      rw [step_addi s_d 104 29 7 0xfc9#12 hcd (by decide) hpcd (by decide), h7d,
          nibble_addi c 55 0xfc9#12 (by decide) (by omega) hc64,
          show s_d.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 108) from by rw [hpcd]; decide]
    have hpd0 : s_d.pc ≠ 0 := by rw [hpcd]; decide
    refine ⟨2 + (2 + (2 + (2 + 1))), ?_, ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi]
      simp only [setPc_mem, rset_mem, hsd, hsc, hsb, hsa]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), hhi]
    · intro i hi28 hi29
      rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi, setPc_rget, rset_rget _ _ _ _ (by decide) hi29,
          hsd, li_block_frame _ _ _ _ hi28, hsc, li_block_frame _ _ _ _ hi28, hsb,
          li_block_frame _ _ _ _ hi28, hsa, li_block_frame _ _ _ _ hi28]

set_option maxRecDepth 4000 in
/-- The low-nibble parse (offsets 164..204): given `nibble c = some lo`, the
    machine reaches `have_low` (offset 208) with `t5 = lo`, touching only
    `t3`/`t5`/`pc`. Mirror of `high_parse` (reg 30 instead of 29). -/
theorem low_parse (s : State) (hcode : CodeLoaded s) (c lo : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 164)) (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hc256 : c < 256) (hn : Hex0.nibble c = some lo) :
    ∃ k, (runFuel 0 k s).pc = BitVec.ofNat 64 (Image.coreAddr + 208) ∧
      (runFuel 0 k s).mem = s.mem ∧
      (runFuel 0 k s).rget 30 = BitVec.ofNat 64 lo ∧
      (∀ i, i ≠ 28 → i ≠ 30 → (runFuel 0 k s).rget i = s.rget i) := by
  have hc64 : c < 2 ^ 64 := Nat.lt_trans hc256 (by decide)
  have hcase : (48 ≤ c ∧ c ≤ 57 ∧ c - 48 = lo) ∨ (65 ≤ c ∧ c ≤ 70 ∧ c - 55 = lo) := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn; exact Or.inl ⟨hd.1, hd.2, Option.some.inj hn⟩
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn; exact Or.inr ⟨hl.1, hl.2, Option.some.inj hn⟩
      · rw [if_neg hl] at hn; exact absurd hn (by simp)
  rcases hcase with ⟨h48, h57, hlo⟩ | ⟨h65, h70, hlo⟩
  · -- digit
    have bA := li_blt_nt s 164 48 c 0x0090#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_a := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (164 + 8)))
      with hsa
    have hca : CodeLoaded s_a := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : s_a.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_nt s_a 172 58 c 0x000c#13 hca rfl h7a (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_b := (s_a.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + (172 + 8)))
      with hsb
    have hcb : CodeLoaded s_b := by intro i hi; rw [hsb]; simp [hca i hi]
    have hpcb : s_b.pc = BitVec.ofNat 64 (Image.coreAddr + 180) := rfl
    have h7b : s_b.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have haddi : step s_b = (s_b.rset 30 (BitVec.ofNat 64 (c - 48))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 184)) := by
      rw [step_addi s_b 180 30 7 0xfd0#12 hcb (by decide) hpcb (by decide), h7b,
          nibble_addi c 48 0xfd0#12 (by decide) h48 hc64,
          show s_b.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 184) from by rw [hpcb]; decide]
    set s_c := (s_b.rset 30 (BitVec.ofNat 64 (c - 48))).setPc (BitVec.ofNat 64 (Image.coreAddr + 184))
      with hsc
    have hcc : CodeLoaded s_c := by intro i hi; rw [hsc]; simp [hcb i hi]
    have hpcc : s_c.pc = BitVec.ofNat 64 (Image.coreAddr + 184) := rfl
    have hjal : step s_c = s_c.setPc (BitVec.ofNat 64 (Image.coreAddr + 208)) := by
      rw [step_jal s_c 184 0 0x000018#21 hcc (by decide) hpcc (by decide), rset_zero,
          show s_c.pc + (0x000018#21).signExtend 64 = BitVec.ofNat 64 (Image.coreAddr + 208)
            from by rw [hpcc]; decide]
    have hpb0 : s_b.pc ≠ 0 := by rw [hpcb]; decide
    have hpc0 : s_c.pc ≠ 0 := by rw [hpcc]; decide
    have hbc : runFuel 0 2 s_b = s_c.setPc (BitVec.ofNat 64 (Image.coreAddr + 208)) := by
      simp only [runFuel]; rw [if_neg hpb0, haddi, ← hsc, if_neg hpc0, hjal]
    refine ⟨2 + (2 + 2), ?_, ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, hbc]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, hbc]
      simp only [setPc_mem, hsc, rset_mem, hsb, hsa]
    · rw [runFuel_add, bA, runFuel_add, bB, hbc, setPc_rget, hsc, setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide), hlo]
    · intro i hi28 hi30
      rw [runFuel_add, bA, runFuel_add, bB, hbc, setPc_rget, hsc, setPc_rget,
          rset_rget _ _ _ _ (by decide) hi30, li_block_frame _ _ _ _ hi28, hsb,
          li_block_frame _ _ _ _ hi28, hsa, li_block_frame _ _ _ _ hi28]
  · -- letter
    have bA := li_blt_nt s 164 48 c 0x0090#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_a := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (164 + 8)))
      with hsa
    have hca : CodeLoaded s_a := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : s_a.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_t s_a 172 58 c 0x000c#13 (BitVec.ofNat 64 (Image.coreAddr + 188))
      hca rfl h7a (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
      (by decide) (by decide)
    set s_b := (s_a.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + 188))
      with hsb
    have hcb : CodeLoaded s_b := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : s_b.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_blt_nt s_b 188 65 c 0x0078#13 hcb rfl h7b (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_c := (s_b.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image.coreAddr + (188 + 8)))
      with hsc
    have hcc : CodeLoaded s_c := by intro i hi; rw [hsc]; simp [hcb i hi]
    have h7c : s_c.rget 7 = BitVec.ofNat 64 c := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
    have bD := li_bge_nt s_c 196 71 c 0x0070#13 hcc rfl h7c (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set s_d := (s_c.rset 28 (BitVec.ofNat 64 71)).setPc (BitVec.ofNat 64 (Image.coreAddr + (196 + 8)))
      with hsd
    have hcd : CodeLoaded s_d := by intro i hi; rw [hsd]; simp [hcc i hi]
    have hpcd : s_d.pc = BitVec.ofNat 64 (Image.coreAddr + 204) := rfl
    have h7d : s_d.rget 7 = BitVec.ofNat 64 c := by rw [hsd, li_block_frame _ _ _ _ (by decide)]; exact h7c
    have haddi : step s_d = (s_d.rset 30 (BitVec.ofNat 64 (c - 55))).setPc
        (BitVec.ofNat 64 (Image.coreAddr + 208)) := by
      rw [step_addi s_d 204 30 7 0xfc9#12 hcd (by decide) hpcd (by decide), h7d,
          nibble_addi c 55 0xfc9#12 (by decide) (by omega) hc64,
          show s_d.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 208) from by rw [hpcd]; decide]
    have hpd0 : s_d.pc ≠ 0 := by rw [hpcd]; decide
    refine ⟨2 + (2 + (2 + (2 + 1))), ?_, ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi]
      simp only [setPc_mem, rset_mem, hsd, hsc, hsb, hsa]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), hlo]
    · intro i hi28 hi30
      rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD,
          runFuel_one _ hpd0, haddi, setPc_rget, rset_rget _ _ _ _ (by decide) hi30,
          hsd, li_block_frame _ _ _ _ hi28, hsc, li_block_frame _ _ _ _ hi28, hsb,
          li_block_frame _ _ _ _ hi28, hsa, li_block_frame _ _ _ _ hi28]

set_option maxRecDepth 4000 in
/-- The capacity-OK store epilogue (offsets 208..232): `bgeu`(not taken) →
    `slli; or` (assemble the byte `hi*16+lo`) → `add; sb` (store it at
    `outAddr + n`) → `addi t1` → `jal` back to LOOP. Returns the final state's
    register/memory frame: `t1` bumped, `t0`/`a*`/`ra` intact, memory updated at
    exactly `outAddr + n`. -/
theorem store_epilogue (s : State) (hcode : CodeLoaded s) (hi lo n cap : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 208))
    (h6 : s.rget 6 = BitVec.ofNat 64 n) (h13 : s.rget 13 = BitVec.ofNat 64 cap)
    (h12 : s.rget 12 = BitVec.ofNat 64 Image.outAddr)
    (h29 : s.rget 29 = BitVec.ofNat 64 hi) (h30 : s.rget 30 = BitVec.ofNat 64 lo)
    (hhi : hi < 16) (hlo : lo < 16) (hn : n < cap)
    (hout_lt : Image.outAddr + cap < 2 ^ 64) :
    ∃ sF, runFuel 0 7 s = sF ∧ sF.pc = LOOP ∧ sF.rget 6 = BitVec.ofNat 64 (n + 1) ∧
      (∀ i, i ≠ 6 → i ≠ 28 → i ≠ 29 → sF.rget i = s.rget i) ∧
      sF.mem = (fun a => if a = BitVec.ofNat 64 (Image.outAddr + n)
                          then BitVec.ofNat 8 (hi * 16 + lo) else s.mem a) := by
  have hcap64 : cap < 2 ^ 64 := by have := hout_lt; simp only [Image.outAddr] at this; omega
  -- step 1: bgeu t1,a3 -- NOT taken (n < cap)
  have hult : (s.rget 6).ult (s.rget 13) = true := by rw [h6, h13]; exact ult_ofNat _ _ hcap64 hn
  have hu1 : step s = s.setPc (BitVec.ofNat 64 (Image.coreAddr + 212)) := by
    have e : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 212) := by rw [hpc]; decide
    rw [step_bgeu s 208 6 13 0x0044#13 hcode (by decide) hpc (by decide), if_pos hult, e]
  let v1 := s.setPc (BitVec.ofNat 64 (Image.coreAddr + 212))
  have hv1 : v1 = s.setPc (BitVec.ofNat 64 (Image.coreAddr + 212)) := rfl
  rw [← hv1] at hu1
  have hc1 : CodeLoaded v1 := by intro i hi; rw [hv1]; simp [hcode i hi]
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image.coreAddr + 212) := rfl
  -- step 2: slli t4,t4,4
  have h29v1 : v1.rget 29 = BitVec.ofNat 64 hi := by rw [hv1, setPc_rget]; exact h29
  have hu2 : step v1 = (v1.rset 29 (BitVec.ofNat 64 hi <<< 4)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 216)) := by
    have e : v1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 216) := by rw [hpc1]; decide
    rw [step_slli v1 212 29 29 4 hc1 (by decide) hpc1 (by decide), h29v1, e]
  let v2 := (v1.rset 29 (BitVec.ofNat 64 hi <<< 4)).setPc (BitVec.ofNat 64 (Image.coreAddr + 216))
  have hv2 : v2 = (v1.rset 29 (BitVec.ofNat 64 hi <<< 4)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 216)) := rfl
  rw [← hv2] at hu2
  have hc2 : CodeLoaded v2 := by intro i hi; rw [hv2]; simp [hc1 i hi]
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image.coreAddr + 216) := rfl
  -- step 3: or t4,t4,t5
  have h29v2 : v2.rget 29 = BitVec.ofNat 64 hi <<< 4 := by
    rw [hv2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have h30v2 : v2.rget 30 = BitVec.ofNat 64 lo := by
    rw [hv2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (30:Nat)≠29),
        hv1, setPc_rget]; exact h30
  have hu3 : step v2 = (v2.rset 29 (BitVec.ofNat 64 hi <<< 4 ||| BitVec.ofNat 64 lo)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 220)) := by
    have e : v2.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 220) := by rw [hpc2]; decide
    rw [step_or v2 216 29 29 30 hc2 (by decide) hpc2 (by decide), h29v2, h30v2, e]
  let v3 := (v2.rset 29 (BitVec.ofNat 64 hi <<< 4 ||| BitVec.ofNat 64 lo)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 220))
  have hv3 : v3 = (v2.rset 29 (BitVec.ofNat 64 hi <<< 4 ||| BitVec.ofNat 64 lo)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 220)) := rfl
  rw [← hv3] at hu3
  have hc3 : CodeLoaded v3 := by intro i hi; rw [hv3]; simp [hc2 i hi]
  have hpc3 : v3.pc = BitVec.ofNat 64 (Image.coreAddr + 220) := rfl
  -- step 4: add t3,a2,t1  (t3 := outAddr + n)
  have h12v3 : v3.rget 12 = BitVec.ofNat 64 Image.outAddr := by
    rw [hv3, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (12:Nat)≠29),
        hv2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (12:Nat)≠29),
        hv1, setPc_rget]; exact h12
  have h6v3 : v3.rget 6 = BitVec.ofNat 64 n := by
    rw [hv3, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat)≠29),
        hv2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat)≠29),
        hv1, setPc_rget]; exact h6
  have hu4 : step v3 = (v3.rset 28 (BitVec.ofNat 64 (Image.outAddr + n))).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 224)) := by
    have e : v3.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 224) := by rw [hpc3]; decide
    rw [step_add v3 220 28 12 6 hc3 (by decide) hpc3 (by decide), h12v3, h6v3, addr_ofNat_succ, e]
  let v4 := (v3.rset 28 (BitVec.ofNat 64 (Image.outAddr + n))).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 224))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 (Image.outAddr + n))).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 224)) := rfl
  rw [← hv4] at hu4
  have hc4 : CodeLoaded v4 := by intro i hi; rw [hv4]; simp [hc3 i hi]
  have hpc4 : v4.pc = BitVec.ofNat 64 (Image.coreAddr + 224) := rfl
  -- step 5: sb t4,0(t3)
  have h28v4 : v4.rget 28 = BitVec.ofNat 64 (Image.outAddr + n) := by
    rw [hv4, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have h29v4 : v4.rget 29 = BitVec.ofNat 64 hi <<< 4 ||| BitVec.ofNat 64 lo := by
    rw [hv4, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (29:Nat)≠28),
        hv3, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hu5 : step v4 = (v4.storeByte (BitVec.ofNat 64 (Image.outAddr + n))
        (BitVec.ofNat 8 (hi * 16 + lo))).setPc (BitVec.ofNat 64 (Image.coreAddr + 228)) := by
    have e : v4.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 228) := by rw [hpc4]; decide
    rw [step_sb v4 224 28 29 0#12 hc4 (by decide) hpc4 (by decide), h28v4,
        show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero, h29v4,
        combine_nibbles hi lo hhi hlo, e]
  let v5 := (v4.storeByte (BitVec.ofNat 64 (Image.outAddr + n))
        (BitVec.ofNat 8 (hi * 16 + lo))).setPc (BitVec.ofNat 64 (Image.coreAddr + 228))
  have hv5 : v5 = (v4.storeByte (BitVec.ofNat 64 (Image.outAddr + n))
        (BitVec.ofNat 8 (hi * 16 + lo))).setPc (BitVec.ofNat 64 (Image.coreAddr + 228)) := rfl
  rw [← hv5] at hu5
  have hc5 : CodeLoaded v5 := by
    intro i hi
    have h324 : i < 324 := by have : Image.coreBytes.length = 324 := by decide; omega
    rw [hv5]; simp only [setPc_mem, storeByte_mem]
    rw [if_neg (ofNat_ne _ _ (by simp only [Image.coreAddr]; omega)
      (by have := hout_lt; simp only [Image.outAddr] at this ⊢; omega)
      (by simp only [Image.coreAddr, Image.outAddr]; omega))]
    exact hc4 i hi
  have hpc5 : v5.pc = BitVec.ofNat 64 (Image.coreAddr + 228) := rfl
  -- step 6: addi t1,t1,1
  have h6v5 : v5.rget 6 = BitVec.ofNat 64 n := by
    rw [hv5, setPc_rget, storeByte_rget, hv4, setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat)≠28)]; exact h6v3
  have hu6 : step v5 = (v5.rset 6 (BitVec.ofNat 64 (n + 1))).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 232)) := by
    have e : v5.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 232) := by rw [hpc5]; decide
    rw [step_addi v5 228 6 6 1#12 hc5 (by decide) hpc5 (by decide), h6v5,
        show ((1#12).signExtend 64 : Word) = BitVec.ofNat 64 1 from by decide, addr_ofNat_succ, e]
  let v6 := (v5.rset 6 (BitVec.ofNat 64 (n + 1))).setPc (BitVec.ofNat 64 (Image.coreAddr + 232))
  have hv6 : v6 = (v5.rset 6 (BitVec.ofNat 64 (n + 1))).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 232)) := rfl
  rw [← hv6] at hu6
  have hc6 : CodeLoaded v6 := by intro i hi; rw [hv6]; simp only [setPc_mem, rset_mem]; exact hc5 i hi
  have hpc6 : v6.pc = BitVec.ofNat 64 (Image.coreAddr + 232) := rfl
  -- step 7: jal -> LOOP
  have hu7 : step v6 = v6.setPc LOOP := by
    rw [step_jal v6 232 0 0x1fff20#21 hc6 (by decide) hpc6 (by decide), rset_zero,
        show v6.pc + (0x1fff20#21).signExtend 64 = LOOP from by rw [hpc6]; decide]
  -- assemble
  have hmemv4 : v4.mem = s.mem := by
    simp only [hv4, setPc_mem, rset_mem, hv3, hv2, hv1]
  have hp0 : s.pc ≠ 0 := by rw [hpc]; decide
  have hp1 : v1.pc ≠ 0 := by rw [hpc1]; decide
  have hp2 : v2.pc ≠ 0 := by rw [hpc2]; decide
  have hp3 : v3.pc ≠ 0 := by rw [hpc3]; decide
  have hp4 : v4.pc ≠ 0 := by rw [hpc4]; decide
  have hp5 : v5.pc ≠ 0 := by rw [hpc5]; decide
  have hp6 : v6.pc ≠ 0 := by rw [hpc6]; decide
  have hfinal : runFuel 0 7 s = v6.setPc LOOP := by
    simp only [runFuel]
    rw [hu1, hu2, hu3, hu4, hu5, hu6, hu7, if_neg hp0, if_neg hp1, if_neg hp2,
        if_neg hp3, if_neg hp4, if_neg hp5, if_neg hp6]
  refine ⟨v6.setPc LOOP, hfinal, ?_, ?_, ?_, ?_⟩
  · simp only [setPc_pc]
  · rw [setPc_rget, hv6, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · intro i h6i h28i h29i
    by_cases h0 : i = 0
    · simp [h0]
    rw [setPc_rget, hv6, setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h6i,
        hv5, setPc_rget, storeByte_rget, hv4, setPc_rget,
        rset_rget _ _ _ _ (by decide) h0, if_neg h28i, hv3, setPc_rget,
        rset_rget _ _ _ _ (by decide) h0, if_neg h29i, hv2, setPc_rget,
        rset_rget _ _ _ _ (by decide) h0, if_neg h29i, hv1, setPc_rget]
  · funext a
    show (v6.setPc LOOP).mem a = _
    simp only [setPc_mem, hv6, rset_mem, hv5, storeByte_mem, hmemv4]

set_option maxRecDepth 4000 in
/-- The error epilogue (offsets 264/276/288/300/312): `li a0,code; mv a1,t1; ret`
    halts with `a0 = code`, `a1 = t1`, memory untouched. Generic over the offset
    and the error code. -/
theorem halt_epilogue (s : State) (off code n : Nat) (hcode : CodeLoaded s)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 code))
    (hmv : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.addi 11 6 0#12)
    (hret : Rv64i.decode (wordAt (off + 8)) = Rv64i.Instr.jalr 0 1 0#12)
    (hoff : off + 8 + 3 < Image.coreBytes.length)
    (hcodesx : (BitVec.ofNat 12 code).signExtend 64 = BitVec.ofNat 64 code)
    (h6 : s.rget 6 = BitVec.ofNat 64 n) (hra : s.rget 1 = 0) :
    (runFuel 0 3 s).pc = 0 ∧ (runFuel 0 3 s).rget 10 = BitVec.ofNat 64 code ∧
    (runFuel 0 3 s).rget 11 = BitVec.ofNat 64 n ∧ (runFuel 0 3 s).mem = s.mem := by
  have hcl : Image.coreBytes.length = 324 := by decide
  have hb : off + 8 + 3 < 324 := hcl ▸ hoff
  -- step 1: li a0,code
  have hu1 : step s = (s.rset 10 (BitVec.ofNat 64 code)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := by
    have e : s.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := by
      rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
    rw [step_addi s off 10 0 (BitVec.ofNat 12 code) hcode (by omega) hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 code).signExtend 64 = BitVec.ofNat 64 code from by
          rw [rget_zero, hcodesx]; simp, e]
  let s1 := (s.rset 10 (BitVec.ofNat 64 code)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 10 (BitVec.ofNat 64 code)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 4))) := rfl
  rw [← hs1] at hu1
  have hc1 : CodeLoaded s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 4)) := rfl
  have h6s1 : s1.rget 6 = BitVec.ofNat 64 n := by
    rw [hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat)≠10)]
    exact h6
  -- step 2: mv a1,t1
  have hu2 : step s1 = (s1.rset 11 (BitVec.ofNat 64 n)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := by
    have e : s1.pc + 4 = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := by
      rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
    rw [step_addi s1 (off+4) 11 6 0#12 hc1 (by omega) hpc1 hmv, h6s1,
        show ((0#12).signExtend 64 : Word) = 0 from by decide, BitVec.add_zero, e]
  let s2 := (s1.rset 11 (BitVec.ofNat 64 n)).setPc (BitVec.ofNat 64 (Image.coreAddr + (off + 8)))
  have hs2 : s2 = (s1.rset 11 (BitVec.ofNat 64 n)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + (off + 8))) := rfl
  rw [← hs2] at hu2
  have hc2 : CodeLoaded s2 := by intro i hi; rw [hs2]; simp [hc1 i hi]
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image.coreAddr + (off + 8)) := rfl
  have hra2 : s2.rget 1 = 0 := by
    rw [hs2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (1:Nat)≠11),
        hs1, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (1:Nat)≠10)]
    exact hra
  -- step 3: ret
  have hu3 : step s2 = s2.setPc 0 := by
    rw [step_jalr s2 (off+8) 0 1 0#12 hc2 (by omega) hpc2 hret, rset_zero]
    congr 1; rw [hra2]; decide
  have hp0 : s.pc ≠ 0 := by rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  have hfinal : runFuel 0 3 s = s2.setPc 0 := by
    simp only [runFuel]; rw [hu1, hu2, hu3, if_neg hp0, if_neg hp1, if_neg hp2]
  refine ⟨by rw [hfinal]; rfl, ?_, ?_, ?_⟩
  · rw [hfinal, setPc_rget, hs2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (10:Nat)≠11), hs1, setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · rw [hfinal, setPc_rget, hs2, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · rw [hfinal]; simp only [setPc_mem, hs2, hs1, rset_mem]

set_option maxRecDepth 4000 in
/-- A `bgeu rs1,rs2` with equal operands: the branch IS taken (1 step to the
    branch target). Used for the EOF (`have_high`) and capacity (`have_low`)
    error exits. -/
theorem bgeu_eq_taken (s : State) (off rs1 rs2 A : Nat) (immB : BitVec 13) (target : Word)
    (hcode : CodeLoaded s) (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + off))
    (h1 : s.rget rs1 = BitVec.ofNat 64 A) (h2 : s.rget rs2 = BitVec.ofNat 64 A)
    (hbgeu : Rv64i.decode (wordAt off) = Rv64i.Instr.bgeu rs1 rs2 immB)
    (htgt : BitVec.ofNat 64 (Image.coreAddr + off) + immB.signExtend 64 = target)
    (hoff : off + 3 < Image.coreBytes.length) :
    runFuel 0 1 s = s.setPc target := by
  have hult : (s.rget rs1).ult (s.rget rs2) = false := by rw [h1, h2]; simp [BitVec.ult]
  have hu1 : step s = s.setPc target := by
    rw [step_bgeu s off rs1 rs2 immB hcode hoff hpc hbgeu, hult,
        if_neg (by decide : ¬((false:Bool)=true)), hpc, htgt]
  have hp0 : s.pc ≠ 0 := by rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image.coreAddr]; omega)
    (by decide) (by simp only [Image.coreAddr]; omega)
  rw [runFuel_one _ hp0, hu1]

set_option maxRecDepth 4000 in
/-- The high-nibble parse when `c` is NOT a hex digit (`nibble c = none`): the
    machine reaches `.Lunknown` (offset 312), touching only `t3`/`pc`. -/
theorem high_parse_unknown (s : State) (hcode : CodeLoaded s) (c : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 64)) (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hc256 : c < 256) (hn : Hex0.nibble c = none) :
    ∃ k, (runFuel 0 k s).pc = BitVec.ofNat 64 (Image.coreAddr + 312) ∧
      (runFuel 0 k s).mem = s.mem ∧ (∀ i, i ≠ 28 → (runFuel 0 k s).rget i = s.rget i) := by
  have hrange : c < 48 ∨ (57 < c ∧ c < 65) ∨ 70 < c := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn; exact absurd hn (by simp)
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn; exact absurd hn (by simp)
      · omega
  rcases hrange with h | ⟨h1, h2⟩ | h
  · -- c < 48: blt at 64 taken
    have b := li_blt_t s 64 48 c 0x00f4#13 (BitVec.ofNat 64 (Image.coreAddr + 312)) hcode hpc h7
      (by decide) (by decide) (by decide) h (by omega) (by omega) (by decide) (by decide)
    exact ⟨2, by rw [b]; simp only [setPc_pc], by rw [b]; simp only [setPc_mem, rset_mem],
      fun i hi => by rw [b]; exact li_block_frame s _ _ i hi⟩
  · -- 58..64: nt,bge-t->88, blt-t->312
    have bA := li_blt_nt s 64 48 c 0x00f4#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (64 + 8)))
      with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_t sa 72 58 c 0x000c#13 (BitVec.ofNat 64 (Image.coreAddr + 88)) hca rfl h7a
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + 88))
      with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_blt_t sb 88 65 c 0x00dc#13 (BitVec.ofNat 64 (Image.coreAddr + 312)) hcb rfl h7b
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    refine ⟨2 + (2 + 2), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, bC]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, bC]; simp only [setPc_mem, rset_mem, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, bC, li_block_frame _ _ _ _ hi, hsb,
          li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]
  · -- >70: nt, bge-t->88, nt, bge-t->312
    have bA := li_blt_nt s 64 48 c 0x00f4#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (64 + 8)))
      with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_t sa 72 58 c 0x000c#13 (BitVec.ofNat 64 (Image.coreAddr + 88)) hca rfl h7a
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + 88))
      with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_blt_nt sb 88 65 c 0x00dc#13 hcb rfl h7b (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set sc := (sb.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image.coreAddr + (88 + 8)))
      with hsc
    have hcc : CodeLoaded sc := by intro i hi; rw [hsc]; simp [hcb i hi]
    have h7c : sc.rget 7 = BitVec.ofNat 64 c := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
    have bD := li_bge_t sc 96 71 c 0x00d4#13 (BitVec.ofNat 64 (Image.coreAddr + 312)) hcc rfl h7c
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    refine ⟨2 + (2 + (2 + 2)), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]
      simp only [setPc_mem, rset_mem, hsc, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD, li_block_frame _ _ _ _ hi, hsc,
          li_block_frame _ _ _ _ hi, hsb, li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]

set_option maxRecDepth 4000 in
/-- The low-nibble parse when `l` is NOT a hex digit (and not a stop char, so we
    are past the low `beq` chain): reaches `.Lunknown` (offset 312). -/
theorem low_parse_unknown (s : State) (hcode : CodeLoaded s) (c : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 164)) (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hc256 : c < 256) (hn : Hex0.nibble c = none) :
    ∃ k, (runFuel 0 k s).pc = BitVec.ofNat 64 (Image.coreAddr + 312) ∧
      (runFuel 0 k s).mem = s.mem ∧ (∀ i, i ≠ 28 → (runFuel 0 k s).rget i = s.rget i) := by
  have hrange : c < 48 ∨ (57 < c ∧ c < 65) ∨ 70 < c := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn; exact absurd hn (by simp)
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn; exact absurd hn (by simp)
      · omega
  rcases hrange with h | ⟨h1, h2⟩ | h
  · have b := li_blt_t s 164 48 c 0x0090#13 (BitVec.ofNat 64 (Image.coreAddr + 312)) hcode hpc h7
      (by decide) (by decide) (by decide) h (by omega) (by omega) (by decide) (by decide)
    exact ⟨2, by rw [b]; simp only [setPc_pc], by rw [b]; simp only [setPc_mem, rset_mem],
      fun i hi => by rw [b]; exact li_block_frame s _ _ i hi⟩
  · have bA := li_blt_nt s 164 48 c 0x0090#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (164 + 8)))
      with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_t sa 172 58 c 0x000c#13 (BitVec.ofNat 64 (Image.coreAddr + 188)) hca rfl h7a
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + 188))
      with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_blt_t sb 188 65 c 0x0078#13 (BitVec.ofNat 64 (Image.coreAddr + 312)) hcb rfl h7b
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    refine ⟨2 + (2 + 2), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, bC]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, bC]; simp only [setPc_mem, rset_mem, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, bC, li_block_frame _ _ _ _ hi, hsb,
          li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]
  · have bA := li_blt_nt s 164 48 c 0x0090#13 hcode hpc h7 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image.coreAddr + (164 + 8)))
      with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 c := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_bge_t sa 172 58 c 0x000c#13 (BitVec.ofNat 64 (Image.coreAddr + 188)) hca rfl h7a
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image.coreAddr + 188))
      with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 c := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_blt_nt sb 188 65 c 0x0078#13 hcb rfl h7b (by decide) (by decide) (by decide)
      (by omega) (by omega) (by decide) (by decide)
    set sc := (sb.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image.coreAddr + (188 + 8)))
      with hsc
    have hcc : CodeLoaded sc := by intro i hi; rw [hsc]; simp [hcb i hi]
    have h7c : sc.rget 7 = BitVec.ofNat 64 c := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
    have bD := li_bge_t sc 196 71 c 0x0070#13 (BitVec.ofNat 64 (Image.coreAddr + 312)) hcc rfl h7c
      (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)
    refine ⟨2 + (2 + (2 + 2)), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]
      simp only [setPc_mem, rset_mem, hsc, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD, li_block_frame _ _ _ _ hi, hsc,
          li_block_frame _ _ _ _ hi, hsb, li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]

set_option maxRecDepth 4000 in
/-- The low `beq`-chain when `l` IS a stop char (`∈ {10,32,95,35,59}`): some
    `beq` is taken, reaching `.Lsplit` (offset 288), touching only `t3`/`pc`. -/
theorem low_split (s : State) (hcode : CodeLoaded s) (l : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (Image.coreAddr + 124)) (h7 : s.rget 7 = BitVec.ofNat 64 l)
    (hc256 : l < 256) (hstop : Hex0.isLowStop l = true) :
    ∃ k, (runFuel 0 k s).pc = BitVec.ofNat 64 (Image.coreAddr + 288) ∧
      (runFuel 0 k s).mem = s.mem ∧ (∀ i, i ≠ 28 → (runFuel 0 k s).rget i = s.rget i) := by
  have hc64 : l < 2 ^ 64 := Nat.lt_trans hc256 (by decide)
  have hmem : l = 10 ∨ l = 32 ∨ l = 95 ∨ l = 35 ∨ l = 59 := by
    simp only [Hex0.isLowStop, Hex0.isSpace, Hex0.isComment, Hex0.c_nl, Hex0.c_sp, Hex0.c_us,
      Hex0.c_hash, Hex0.c_semi, beq_iff_eq, Bool.or_eq_true] at hstop; omega
  -- generic single-chain block at off `o`, K, beq imm, NOT matching
  have step124 : ∀ (t : State), CodeLoaded t → t.rget 7 = BitVec.ofNat 64 l →
      t.pc = BitVec.ofNat 64 (Image.coreAddr + 124) → l ≠ 10 →
      runFuel 0 2 t = (t.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + 132)) :=
    fun t hct h7t hpct hne => li_beq_ne t 124 10 l 0x00a0#13 hct hpct h7t (by decide) (by decide)
      (by decide) (ofNat_ne l 10 hc64 (by decide) hne) (by decide)
  rcases hmem with h | h | h | h | h
  · subst h
    have b := li_beq_eq s 124 10 10 0x00a0#13 (BitVec.ofNat 64 (Image.coreAddr + 288)) hcode hpc h7
      (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    exact ⟨2, by rw [b]; simp only [setPc_pc], by rw [b]; simp only [setPc_mem, rset_mem],
      fun i hi => by rw [b]; exact li_block_frame s _ _ i hi⟩
  · subst h
    have bA := step124 s hcode h7 hpc (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + 132)) with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 32 := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have b := li_beq_eq sa 132 32 32 0x098#13 (BitVec.ofNat 64 (Image.coreAddr + 288)) hca rfl h7a
      (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    refine ⟨2 + 2, ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, b]; simp only [setPc_pc]
    · rw [runFuel_add, bA, b]; simp only [setPc_mem, rset_mem, hsa]
    · intro i hi; rw [runFuel_add, bA, b, li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]
  · subst h
    have bA := step124 s hcode h7 hpc (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + 132)) with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 95 := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_beq_ne sa 132 32 95 0x098#13 hca rfl h7a (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image.coreAddr + (132 + 8))) with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 95 := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have b := li_beq_eq sb 140 95 95 0x090#13 (BitVec.ofNat 64 (Image.coreAddr + 288)) hcb rfl h7b
      (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    refine ⟨2 + (2 + 2), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, b]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, b]; simp only [setPc_mem, rset_mem, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, b, li_block_frame _ _ _ _ hi, hsb,
          li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]
  · subst h
    have bA := step124 s hcode h7 hpc (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + 132)) with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 35 := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_beq_ne sa 132 32 35 0x098#13 hca rfl h7a (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image.coreAddr + (132 + 8))) with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 35 := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_beq_ne sb 140 95 35 0x090#13 hcb rfl h7b (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set sc := (sb.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image.coreAddr + (140 + 8))) with hsc
    have hcc : CodeLoaded sc := by intro i hi; rw [hsc]; simp [hcb i hi]
    have h7c : sc.rget 7 = BitVec.ofNat 64 35 := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
    have b := li_beq_eq sc 148 35 35 0x088#13 (BitVec.ofNat 64 (Image.coreAddr + 288)) hcc rfl h7c
      (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    refine ⟨2 + (2 + (2 + 2)), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, b]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, b]
      simp only [setPc_mem, rset_mem, hsc, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, b, li_block_frame _ _ _ _ hi, hsc,
          li_block_frame _ _ _ _ hi, hsb, li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]
  · subst h
    have bA := step124 s hcode h7 hpc (by decide)
    set sa := (s.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image.coreAddr + 132)) with hsa
    have hca : CodeLoaded sa := by intro i hi; rw [hsa]; simp [hcode i hi]
    have h7a : sa.rget 7 = BitVec.ofNat 64 59 := by rw [hsa, li_block_frame _ _ _ _ (by decide)]; exact h7
    have bB := li_beq_ne sa 132 32 59 0x098#13 hca rfl h7a (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set sb := (sa.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image.coreAddr + (132 + 8))) with hsb
    have hcb : CodeLoaded sb := by intro i hi; rw [hsb]; simp [hca i hi]
    have h7b : sb.rget 7 = BitVec.ofNat 64 59 := by rw [hsb, li_block_frame _ _ _ _ (by decide)]; exact h7a
    have bC := li_beq_ne sb 140 95 59 0x090#13 hcb rfl h7b (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set sc := (sb.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image.coreAddr + (140 + 8))) with hsc
    have hcc : CodeLoaded sc := by intro i hi; rw [hsc]; simp [hcb i hi]
    have h7c : sc.rget 7 = BitVec.ofNat 64 59 := by rw [hsc, li_block_frame _ _ _ _ (by decide)]; exact h7b
    have bD := li_beq_ne sc 148 35 59 0x088#13 hcc rfl h7c (by decide) (by decide) (by decide)
      (by decide) (by decide)
    set sd := (sc.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image.coreAddr + (148 + 8))) with hsd
    have hcd : CodeLoaded sd := by intro i hi; rw [hsd]; simp [hcc i hi]
    have h7d : sd.rget 7 = BitVec.ofNat 64 59 := by rw [hsd, li_block_frame _ _ _ _ (by decide)]; exact h7c
    have b := li_beq_eq sd 156 59 59 0x080#13 (BitVec.ofNat 64 (Image.coreAddr + 288)) hcd rfl h7d
      (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    refine ⟨2 + (2 + (2 + (2 + 2))), ?_, ?_, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD, b]; simp only [setPc_pc]
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD, b]
      simp only [setPc_mem, rset_mem, hsd, hsc, hsb, hsa]
    · intro i hi
      rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, runFuel_add, bD, b,
          li_block_frame _ _ _ _ hi, hsd, li_block_frame _ _ _ _ hi, hsc,
          li_block_frame _ _ _ _ hi, hsb, li_block_frame _ _ _ _ hi, hsa, li_block_frame _ _ _ _ hi]

/-- Build a `Result` for the non-truncating terminal statuses (Ok/Split/Trailing/
    Unknown): the machine halted with `a0 = statusCode st`, `a1 = |emitted|`, and
    the output region holds `emitted`, while `decode inp = (emitted, st)` and
    `|emitted| ≤ cap` (so `coreSpec` does not truncate). -/
theorem error_result (s : State) (inp : List Nat) (cap : Nat) (emitted : List Nat)
    (st : Hex0.Status) (hp : s.pc = 0)
    (ha0 : s.rget 10 = BitVec.ofNat 64 (Hex0.statusCode st))
    (ha1 : s.rget 11 = BitVec.ofNat 64 emitted.length)
    (hmem : ∀ j, j < emitted.length →
      s.mem (BitVec.ofNat 64 (Image.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0))
    (hdec : Hex0.decode inp = (emitted, st)) (hle : emitted.length ≤ cap) :
    Result s inp cap := by
  have hcs : Hex0.coreSpec inp cap = (Hex0.statusCode st, emitted, emitted.length) := by
    simp only [Hex0.coreSpec, hdec]; rw [if_neg (Nat.not_lt.mpr hle)]
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [ha0, hcs]
  · rw [ha1, hcs]
  · intro j hj; rw [hcs] at hj ⊢; exact hmem j hj

/-- Given the machine has reached an error epilogue (`sE` at offset `off` with
    `t1 = |emitted|`, `ra = 0`, memory = the entry memory `s.mem`), run the
    3-step `li/mv/ret` tail and conclude `Result`. Shared by all error cases. -/
theorem reach_error (s sE : State) (inp : List Nat) (cap : Nat) (emitted : List Nat)
    (off code k : Nat) (st : Hex0.Status)
    (hrun : runFuel 0 k s = sE)
    (hpcE : sE.pc = BitVec.ofNat 64 (Image.coreAddr + off)) (hcodeE : CodeLoaded sE)
    (hmemE : sE.mem = s.mem) (h6E : sE.rget 6 = BitVec.ofNat 64 emitted.length)
    (h1E : sE.rget 1 = 0)
    (hli : Rv64i.decode (wordAt off) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 code))
    (hmv : Rv64i.decode (wordAt (off + 4)) = Rv64i.Instr.addi 11 6 0#12)
    (hret : Rv64i.decode (wordAt (off + 8)) = Rv64i.Instr.jalr 0 1 0#12)
    (hoff : off + 8 + 3 < Image.coreBytes.length)
    (hcodesx : (BitVec.ofNat 12 code).signExtend 64 = BitVec.ofNat 64 code)
    (hcodeval : code = Hex0.statusCode st)
    (hdec : Hex0.decode inp = (emitted, st)) (hle : emitted.length ≤ cap)
    (hout : ∀ j, j < emitted.length →
      s.mem (BitVec.ofNat 64 (Image.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0)) :
    ∃ m, Result (runFuel 0 m s) inp cap := by
  obtain ⟨hp, ha0, ha1, hm⟩ :=
    halt_epilogue sE off code emitted.length hcodeE hpcE hli hmv hret hoff hcodesx h6E h1E
  refine ⟨k + 3, ?_⟩
  rw [runFuel_add, hrun]
  refine error_result (runFuel 0 3 sE) inp cap emitted st hp ?_ ha1 ?_ hdec hle
  · rw [ha0, hcodeval]
  · intro j hj; rw [hm, hmemE]; exact hout j hj

set_option maxRecDepth 4000 in
/-- A COMPLETE main-loop iteration for a byte token: high nibble `c`, low nibble
    `l` (`hi`/`lo`), with output capacity to spare. Chains `loop_prefix` (read
    `c`) → `high_beq_ft` → `high_parse` → `read_prefix` (read `l`) → `low_beq_ft`
    → `low_parse` → `store_epilogue` (emit `hi*16+lo`), then rebuilds `LoopInv`
    for the shorter suffix with one more emitted byte (via `decodeS_byte`). -/
theorem loop_byte (inp : List Nat) (cap : Nat) (c hi l lo : Nat) (rest'' emitted : List Nat)
    (s : State) (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (hnh : Hex0.nibble c = some hi) (hlls : Hex0.isLowStop l = false)
    (hnl : Hex0.nibble l = some lo) (hcap : emitted.length < cap)
    (inv : LoopInv inp cap s (c :: l :: rest'') emitted) :
    ∃ k, LoopInv inp cap (runFuel 0 k s) rest'' (emitted ++ [hi * 16 + lo]) := by
  -- char-class facts
  have hcm : c ≠ 35 ∧ c ≠ 59 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hsc; exact hsc
  have hsp : c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 := by
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hss; exact ⟨hss.1.1, hss.1.2, hss.2⟩
  have hlstop : l ≠ 10 ∧ l ≠ 32 ∧ l ≠ 95 ∧ l ≠ 35 ∧ l ≠ 59 := by
    simp only [Hex0.isLowStop, Hex0.isSpace, Hex0.isComment, Hex0.c_nl, Hex0.c_sp,
      Hex0.c_us, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hlls
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hc256 : c < 256 := inv.bytes_lt c (by
    have : c ∈ inp.drop (inp.length - (c::l::rest'').length) := by rw [inv.suffix]; exact List.mem_cons_self
    exact List.drop_subset _ _ this)
  have hl256 : l < 256 := inv.bytes_lt l (by
    have : l ∈ inp.drop (inp.length - (c::l::rest'').length) := by
      rw [inv.suffix]; exact List.mem_cons_of_mem _ List.mem_cons_self
    exact List.drop_subset _ _ this)
  have hhi16 : hi < 16 := nibble_lt c hi hnh
  have hlo16 : lo < 16 := nibble_lt l lo hnl
  have hRle : rest''.length + 2 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons] at h; omega
  have hinlt : inp.length < 2 ^ 64 := by have := inv.in_lt; omega
  -- the tail-suffix at position p+1 is l :: rest''
  have hdrop1 : inp.drop ((inp.length - (c::l::rest'').length) + 1) = l :: rest'' := by
    rw [← List.tail_drop, inv.suffix]; rfl
  -- A: read high char c
  obtain ⟨s4, hr4, hpc4, h7_4, h5_4, hmem4, hcode4, hoth4⟩ :=
    loop_prefix inp cap c (l :: rest'') emitted s inv
  -- B: high beq fall-through to off 64
  obtain ⟨hpcB, hmemB, hothB⟩ :=
    high_beq_ft s4 hcode4 c hpc4 h7_4 hc256 hcm.1 hcm.2 hsp.1 hsp.2.1 hsp.2.2
  have hcodeB : CodeLoaded (runFuel 0 10 s4) := by intro i hi; rw [hmemB]; exact hcode4 i hi
  have h7B : (runFuel 0 10 s4).rget 7 = BitVec.ofNat 64 c := by rw [hothB 7 (by decide)]; exact h7_4
  -- C: high nibble parse to off 108, t4 = hi
  obtain ⟨k1, hpcC, hmemC, h29C, hothC⟩ :=
    high_parse (runFuel 0 10 s4) hcodeB c hi hpcB h7B hc256 hnh
  have hcodeC : CodeLoaded (runFuel 0 k1 (runFuel 0 10 s4)) := by
    intro i hi; rw [hmemC, hmemB]; exact hcode4 i hi
  have ha0C : (runFuel 0 k1 (runFuel 0 10 s4)).rget 10 = BitVec.ofNat 64 Image.inputAddr := by
    rw [hothC 10 (by decide) (by decide), hothB 10 (by decide),
        hoth4 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
  have ha1C : (runFuel 0 k1 (runFuel 0 10 s4)).rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hothC 11 (by decide) (by decide), hothB 11 (by decide),
        hoth4 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
  have ht0C : (runFuel 0 k1 (runFuel 0 10 s4)).rget 5
      = BitVec.ofNat 64 ((inp.length - (c::l::rest'').length) + 1) := by
    rw [hothC 5 (by decide) (by decide), hothB 5 (by decide), h5_4, inv.idx,
        show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
  -- D: read low char l (off 108..120)
  obtain ⟨s8, hr8, hpc8, h7_8, h5_8, hmem8, hcode8, hoth8⟩ :=
    read_prefix (runFuel 0 k1 (runFuel 0 10 s4)) 108 0x00c0#13 inp
      ((inp.length - (c::l::rest'').length) + 1) l hcodeC hpcC (by decide) (by decide)
      (by decide) (by decide) (by decide) ha0C ha1C ht0C (by omega) hinlt
      (fun j hj => by rw [hmemC, hmemB, hmem4]; exact inv.in_mem j hj)
      (by rw [← getD_drop, hdrop1]; rfl) hl256
  -- E: low beq fall-through to off 164
  obtain ⟨hpcE, hmemE, hothE⟩ :=
    low_beq_ft s8 hcode8 l hpc8 h7_8 hl256 hlstop.2.2.2.1 hlstop.2.2.2.2
      hlstop.1 hlstop.2.1 hlstop.2.2.1
  have hcodeE : CodeLoaded (runFuel 0 10 s8) := by intro i hi; rw [hmemE]; exact hcode8 i hi
  have h7E : (runFuel 0 10 s8).rget 7 = BitVec.ofNat 64 l := by rw [hothE 7 (by decide)]; exact h7_8
  -- F: low nibble parse to off 208, t5 = lo
  obtain ⟨k2, hpcF, hmemF, h30F, hothF⟩ :=
    low_parse (runFuel 0 10 s8) hcodeE l lo hpcE h7E hl256 hnl
  -- registers/memory at off 208 (sP)
  have hmemP : (runFuel 0 k2 (runFuel 0 10 s8)).mem = s.mem := by
    rw [hmemF, hmemE, hmem8, hmemC, hmemB, hmem4]
  have hcodeP : CodeLoaded (runFuel 0 k2 (runFuel 0 10 s8)) := by
    intro i hi; rw [hmemP]; exact inv.code i hi
  have h6P : (runFuel 0 k2 (runFuel 0 10 s8)).rget 6 = BitVec.ofNat 64 emitted.length := by
    rw [hothF 6 (by decide) (by decide), hothE 6 (by decide),
        hoth8 6 (by decide) (by decide) (by decide) (by decide),
        hothC 6 (by decide) (by decide), hothB 6 (by decide),
        hoth4 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
  have h12P : (runFuel 0 k2 (runFuel 0 10 s8)).rget 12 = BitVec.ofNat 64 Image.outAddr := by
    rw [hothF 12 (by decide) (by decide), hothE 12 (by decide),
        hoth8 12 (by decide) (by decide) (by decide) (by decide),
        hothC 12 (by decide) (by decide), hothB 12 (by decide),
        hoth4 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
  have h13P : (runFuel 0 k2 (runFuel 0 10 s8)).rget 13 = BitVec.ofNat 64 cap := by
    rw [hothF 13 (by decide) (by decide), hothE 13 (by decide),
        hoth8 13 (by decide) (by decide) (by decide) (by decide),
        hothC 13 (by decide) (by decide), hothB 13 (by decide),
        hoth4 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
  have h29P : (runFuel 0 k2 (runFuel 0 10 s8)).rget 29 = BitVec.ofNat 64 hi := by
    rw [hothF 29 (by decide) (by decide), hothE 29 (by decide),
        hoth8 29 (by decide) (by decide) (by decide) (by decide)]; exact h29C
  -- G: capacity check + store
  obtain ⟨sF, hr7, hpcSF, h6SF, hothSF, hmemSF⟩ :=
    store_epilogue (runFuel 0 k2 (runFuel 0 10 s8)) hcodeP hi lo emitted.length cap
      hpcF h6P h13P h12P h29P h30F hhi16 hlo16 hcap inv.out_lt
  -- chain the fuel
  refine ⟨4 + (10 + (k1 + (4 + (10 + (k2 + 7))))), ?_⟩
  have hrun : runFuel 0 (4 + (10 + (k1 + (4 + (10 + (k2 + 7)))))) s = sF := by
    rw [runFuel_add, hr4, runFuel_add, runFuel_add, runFuel_add, hr8,
        runFuel_add, runFuel_add, hr7]
  rw [hrun]
  -- the new emitted is one byte longer
  have hlen' : (emitted ++ [hi * 16 + lo]).length = emitted.length + 1 := by
    simp [List.length_append]
  -- pointwise memory of sF
  have hmem_at : ∀ a, sF.mem a =
      if a = BitVec.ofNat 64 (Image.outAddr + emitted.length)
      then BitVec.ofNat 8 (hi * 16 + lo) else s.mem a := by
    intro a; rw [hmemSF, hmemP]
  -- bounds for output-address injectivity
  have hb_out : ∀ j, j < emitted.length →
      (BitVec.ofNat 64 (Image.outAddr + j) : Word) ≠ BitVec.ofNat 64 (Image.outAddr + emitted.length) := by
    intro j hj
    refine ofNat_ne _ _ ?_ ?_ ?_
    · have := inv.out_lt; omega
    · have := inv.out_lt; omega
    · omega
  refine { at_loop := hpcSF, code := ?_, a0 := ?_, a1 := ?_, a2 := ?_, a3 := ?_,
           ra0 := ?_, in_mem := ?_, in_lt := inv.in_lt, bytes_lt := inv.bytes_lt,
           in_fits := inv.in_fits, out_lt := inv.out_lt,
           idx := ?_, suffix := ?_, outidx := ?_, emitted_le := ?_,
           out_mem := ?_, spec_link := ?_ }
  · -- code: store doesn't touch code region
    intro i hi
    have h324 : i < 324 := by have : Image.coreBytes.length = 324 := by decide; omega
    rw [hmem_at, if_neg (ofNat_ne _ _ (by simp only [Image.coreAddr]; omega)
        (by have := inv.out_lt; simp only [Image.outAddr] at this ⊢; omega)
        (by simp only [Image.coreAddr, Image.outAddr]; omega))]
    exact inv.code i hi
  · rw [hothSF 10 (by decide) (by decide) (by decide),
        hothF 10 (by decide) (by decide), hothE 10 (by decide),
        hoth8 10 (by decide) (by decide) (by decide) (by decide),
        hothC 10 (by decide) (by decide), hothB 10 (by decide),
        hoth4 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
  · rw [hothSF 11 (by decide) (by decide) (by decide),
        hothF 11 (by decide) (by decide), hothE 11 (by decide),
        hoth8 11 (by decide) (by decide) (by decide) (by decide),
        hothC 11 (by decide) (by decide), hothB 11 (by decide),
        hoth4 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
  · rw [hothSF 12 (by decide) (by decide) (by decide)]; exact h12P
  · rw [hothSF 13 (by decide) (by decide) (by decide)]; exact h13P
  · rw [hothSF 1 (by decide) (by decide) (by decide),
        hothF 1 (by decide) (by decide), hothE 1 (by decide),
        hoth8 1 (by decide) (by decide) (by decide) (by decide),
        hothC 1 (by decide) (by decide), hothB 1 (by decide),
        hoth4 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
  · -- in_mem: store disjoint from input region (in_fits)
    intro j hj
    rw [hmem_at, if_neg (ofNat_ne _ _
        (by have := inv.in_lt; omega)
        (by have := inv.out_lt; simp only [Image.outAddr] at this ⊢; omega)
        (by have := inv.in_fits; omega))]
    exact inv.in_mem j hj
  · -- idx
    rw [hothSF 5 (by decide) (by decide) (by decide), hothF 5 (by decide) (by decide),
        hothE 5 (by decide), h5_8, ht0C, show (1:Word) = BitVec.ofNat 64 1 from rfl,
        addr_ofNat_succ]
    congr 1; simp only [List.length_cons]; omega
  · -- suffix
    have hk : inp.length - rest''.length = (inp.length - (c::l::rest'').length) + 1 + 1 := by
      simp only [List.length_cons]; omega
    rw [hk, ← List.tail_drop, hdrop1]; rfl
  · -- outidx
    rw [h6SF, hlen']
  · -- emitted_le
    rw [hlen']; omega
  · -- out_mem
    intro j hj
    rw [hlen'] at hj
    rw [hmem_at]
    by_cases hje : j = emitted.length
    · subst hje
      rw [if_pos rfl, List.getD_append_right (by omega), Nat.sub_self]; rfl
    · rw [if_neg (hb_out j (by omega)), hmemP, List.getD_append _ _ _ (by omega)]
      exact inv.out_mem j (by omega)
  · -- spec_link
    rw [inv.spec_link, decodeS_byte c l rest'' hi lo hsc hss hnh hlls hnl]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

set_option maxRecDepth 4000 in
/-- Navigate from the loop head (`LoopInv` with head char `c`, not space/comment)
    to offset 64 (entry of the high-nibble parse), 14 steps, carrying the
    bookkeeping registers. Shared prefix of every byte/error case. -/
theorem reach64 (inp : List Nat) (cap : Nat) (c : Nat) (rest' emitted : List Nat) (s : State)
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (inv : LoopInv inp cap s (c :: rest') emitted) :
    ∃ s64, runFuel 0 14 s = s64 ∧ s64.pc = BitVec.ofNat 64 (Image.coreAddr + 64) ∧
      s64.rget 7 = BitVec.ofNat 64 c ∧ CodeLoaded s64 ∧ s64.mem = s.mem ∧
      s64.rget 5 = s.rget 5 + 1 ∧ s64.rget 6 = BitVec.ofNat 64 emitted.length ∧
      s64.rget 1 = 0 ∧ s64.rget 10 = BitVec.ofNat 64 Image.inputAddr ∧
      s64.rget 11 = BitVec.ofNat 64 inp.length ∧ s64.rget 13 = BitVec.ofNat 64 cap ∧ c < 256 := by
  have hcm : c ≠ 35 ∧ c ≠ 59 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hsc; exact hsc
  have hsp : c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 := by
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hss; exact ⟨hss.1.1, hss.1.2, hss.2⟩
  have hc256 : c < 256 := inv.bytes_lt c (by
    have : c ∈ inp.drop (inp.length - (c::rest').length) := by rw [inv.suffix]; exact List.mem_cons_self
    exact List.drop_subset _ _ this)
  obtain ⟨s4, hr4, hpc4, h7_4, h5_4, hmem4, hcode4, hoth4⟩ :=
    loop_prefix inp cap c rest' emitted s inv
  obtain ⟨hpcB, hmemB, hothB⟩ :=
    high_beq_ft s4 hcode4 c hpc4 h7_4 hc256 hcm.1 hcm.2 hsp.1 hsp.2.1 hsp.2.2
  refine ⟨runFuel 0 10 s4, ?_, hpcB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc256⟩
  · rw [show (14:Nat) = 4 + 10 from rfl, runFuel_add, hr4]
  · rw [hothB 7 (by decide)]; exact h7_4
  · intro i hi; rw [hmemB]; exact hcode4 i hi
  · rw [hmemB, hmem4]
  · rw [hothB 5 (by decide)]; exact h5_4
  · rw [hothB 6 (by decide), hoth4 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
  · rw [hothB 1 (by decide), hoth4 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
  · rw [hothB 10 (by decide), hoth4 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
  · rw [hothB 11 (by decide), hoth4 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
  · rw [hothB 13 (by decide), hoth4 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3

set_option maxRecDepth 4000 in
/-- Navigate from the loop head to offset 124 (entry of the low `beq` chain) for
    a byte whose head `c` is the hex digit `hi` and which has a following char
    `l`. Reads `c` (high parse) and `l`, carrying bookkeeping. -/
theorem reach124 (inp : List Nat) (cap : Nat) (c hi l : Nat) (rest'' emitted : List Nat) (s : State)
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (hnh : Hex0.nibble c = some hi)
    (inv : LoopInv inp cap s (c :: l :: rest'') emitted) :
    ∃ k s124, runFuel 0 k s = s124 ∧ s124.pc = BitVec.ofNat 64 (Image.coreAddr + 124) ∧
      s124.rget 7 = BitVec.ofNat 64 l ∧ CodeLoaded s124 ∧ s124.mem = s.mem ∧
      s124.rget 6 = BitVec.ofNat 64 emitted.length ∧ s124.rget 1 = 0 ∧
      s124.rget 13 = BitVec.ofNat 64 cap ∧ l < 256 := by
  obtain ⟨s64, hr64, hpc64, h7_64, hcode64, hmem64, h5_64, h6_64, h1_64, h10_64, h11_64, h13_64, hc256⟩ :=
    reach64 inp cap c (l :: rest'') emitted s hsc hss inv
  obtain ⟨k1, hpcC, hmemC, h29C, hothC⟩ := high_parse s64 hcode64 c hi hpc64 h7_64 hc256 hnh
  have hRle : rest''.length + 2 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons] at h; omega
  have hinlt : inp.length < 2 ^ 64 := by have := inv.in_lt; omega
  have hl256 : l < 256 := inv.bytes_lt l (by
    have : l ∈ inp.drop (inp.length - (c::l::rest'').length) := by
      rw [inv.suffix]; exact List.mem_cons_of_mem _ List.mem_cons_self
    exact List.drop_subset _ _ this)
  have hdrop1 : inp.drop ((inp.length - (c::l::rest'').length) + 1) = l :: rest'' := by
    rw [← List.tail_drop, inv.suffix]; rfl
  have ha0C : (runFuel 0 k1 s64).rget 10 = BitVec.ofNat 64 Image.inputAddr := by
    rw [hothC 10 (by decide) (by decide)]; exact h10_64
  have ha1C : (runFuel 0 k1 s64).rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hothC 11 (by decide) (by decide)]; exact h11_64
  have ht0C : (runFuel 0 k1 s64).rget 5
      = BitVec.ofNat 64 ((inp.length - (c::l::rest'').length) + 1) := by
    rw [hothC 5 (by decide) (by decide), h5_64, inv.idx,
        show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
  have hcodeC : CodeLoaded (runFuel 0 k1 s64) := by intro i hi; rw [hmemC, hmem64]; exact inv.code i hi
  obtain ⟨s8, hr8, hpc8, h7_8, h5_8, hmem8, hcode8, hoth8⟩ :=
    read_prefix (runFuel 0 k1 s64) 108 0x00c0#13 inp
      ((inp.length - (c::l::rest'').length) + 1) l hcodeC hpcC (by decide) (by decide)
      (by decide) (by decide) (by decide) ha0C ha1C ht0C (by omega) hinlt
      (fun j hj => by rw [hmemC, hmem64]; exact inv.in_mem j hj)
      (by rw [← getD_drop, hdrop1]; rfl) hl256
  refine ⟨14 + (k1 + 4), s8, ?_, ?_, h7_8, hcode8, ?_, ?_, ?_, ?_, hl256⟩
  · rw [runFuel_add, hr64, runFuel_add, hr8]
  · rw [hpc8]
  · rw [hmem8, hmemC, hmem64]
  · rw [hoth8 6 (by decide) (by decide) (by decide) (by decide), hothC 6 (by decide) (by decide)]
    exact h6_64
  · rw [hoth8 1 (by decide) (by decide) (by decide) (by decide), hothC 1 (by decide) (by decide)]
    exact h1_64
  · rw [hoth8 13 (by decide) (by decide) (by decide) (by decide), hothC 13 (by decide) (by decide)]
    exact h13_64

/-- `Result` builder for output-short (code 2): the full decode `bs` exceeds
    `cap`, so `coreSpec` truncates to `bs.take cap = emitted` with length `cap`. -/
theorem short_result (s : State) (inp : List Nat) (cap : Nat) (emitted bs : List Nat)
    (st : Hex0.Status) (hp : s.pc = 0) (ha0 : s.rget 10 = BitVec.ofNat 64 2)
    (ha1 : s.rget 11 = BitVec.ofNat 64 cap)
    (hmem : ∀ j, j < cap →
      s.mem (BitVec.ofNat 64 (Image.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0))
    (hdec : Hex0.decode inp = (bs, st)) (hbs : cap < bs.length) (htake : bs.take cap = emitted) :
    Result s inp cap := by
  have hcs : Hex0.coreSpec inp cap = (2, emitted, cap) := by
    simp only [Hex0.coreSpec, hdec]; rw [if_pos hbs, htake]
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [ha0, hcs]
  · rw [ha1, hcs]
  · intro j hj; rw [hcs] at hj ⊢; exact hmem j hj

set_option maxRecDepth 4000 in
/-- Error case: high nibble `c` at end of input (no low char) → `Trailing` (4). -/
theorem loop_trailing (inp : List Nat) (cap : Nat) (c hi : Nat) (emitted : List Nat) (s : State)
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false) (hnh : Hex0.nibble c = some hi)
    (inv : LoopInv inp cap s (c :: []) emitted) : ∃ k, Result (runFuel 0 k s) inp cap := by
  have hge1 : 1 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons, List.length_nil] at h; omega
  obtain ⟨s64, hr64, hpc64, h7_64, hcode64, hmem64, h5_64, h6_64, h1_64, h10_64, h11_64, h13_64, hc256⟩ :=
    reach64 inp cap c [] emitted s hsc hss inv
  obtain ⟨k1, hpcC, hmemC, h29C, hothC⟩ := high_parse s64 hcode64 c hi hpc64 h7_64 hc256 hnh
  -- at off 108, t0 = a1 = |inp| → bgeu taken → .Ltrailing (300)
  have h5C : (runFuel 0 k1 s64).rget 5 = BitVec.ofNat 64 inp.length := by
    rw [hothC 5 (by decide) (by decide), h5_64, inv.idx,
        show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
    congr 1; simp only [List.length_cons, List.length_nil]; omega
  have ha1C : (runFuel 0 k1 s64).rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hothC 11 (by decide) (by decide)]; exact h11_64
  have hcodeC : CodeLoaded (runFuel 0 k1 s64) := by intro i hi; rw [hmemC, hmem64]; exact inv.code i hi
  have hbt := bgeu_eq_taken (runFuel 0 k1 s64) 108 5 11 inp.length 0x00c0#13
    (BitVec.ofNat 64 (Image.coreAddr + 300)) hcodeC hpcC h5C ha1C (by decide) (by decide) (by decide)
  have hdec : Hex0.decode inp = (emitted, Hex0.Status.Trailing) := by
    have hsl := inv.spec_link
    have hdtok : Hex0.decodeS .High (c :: []) = ([], Hex0.Status.Trailing) := by
      simp [Hex0.decodeS, hsc, hss, hnh]
    rw [hdtok] at hsl; simpa [Hex0.decode] using hsl
  refine reach_error s ((runFuel 0 k1 s64).setPc (BitVec.ofNat 64 (Image.coreAddr + 300)))
    inp cap emitted 300 4 (14 + (k1 + 1)) Hex0.Status.Trailing ?_ (by simp only [setPc_pc]) ?_ ?_
    ?_ ?_ (by decide) (by decide) (by decide) (by decide) (by decide) rfl hdec inv.emitted_le inv.out_mem
  · rw [runFuel_add, hr64, runFuel_add, hbt]
  · intro i hi; simp only [setPc_mem]; rw [hmemC, hmem64]; exact inv.code i hi
  · simp only [setPc_mem]; rw [hmemC, hmem64]
  · rw [setPc_rget, hothC 6 (by decide) (by decide)]; exact h6_64
  · rw [setPc_rget, hothC 1 (by decide) (by decide)]; exact h1_64

set_option maxRecDepth 4000 in
/-- Error case: high nibble `c`, but the low char `l` is a stop char → `Split` (3). -/
theorem loop_split (inp : List Nat) (cap : Nat) (c hi l : Nat) (rest'' emitted : List Nat) (s : State)
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false) (hnh : Hex0.nibble c = some hi)
    (hlls : Hex0.isLowStop l = true)
    (inv : LoopInv inp cap s (c :: l :: rest'') emitted) : ∃ k, Result (runFuel 0 k s) inp cap := by
  obtain ⟨k0, s124, hr124, hpc124, h7_124, hcode124, hmem124, h6_124, h1_124, h13_124, hl256⟩ :=
    reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv
  obtain ⟨k1, hpcS, hmemS, hothS⟩ := low_split s124 hcode124 l hpc124 h7_124 hl256 hlls
  have hdec : Hex0.decode inp = (emitted, Hex0.Status.Split) := by
    have hsl := inv.spec_link
    have hdtok : Hex0.decodeS .High (c :: l :: rest'') = ([], Hex0.Status.Split) := by
      rw [Hex0.decodeS]; simp only [hsc, hss, hnh, Bool.false_eq_true, if_false]
      rw [Hex0.decodeS]; simp [hlls]
    rw [hdtok] at hsl; simpa [Hex0.decode] using hsl
  refine reach_error s (runFuel 0 k1 s124) inp cap emitted 288 3 (k0 + k1) Hex0.Status.Split
    ?_ hpcS ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide) (by decide) rfl hdec
    inv.emitted_le ?_
  · rw [runFuel_add, hr124]
  · intro i hi; rw [hmemS, hmem124]; exact inv.code i hi
  · rw [hmemS, hmem124]
  · rw [hothS 6 (by decide)]; exact h6_124
  · rw [hothS 1 (by decide)]; exact h1_124
  · intro j hj; rw [hmem124] at *; exact inv.out_mem j hj

set_option maxRecDepth 4000 in
/-- Error case: head char `c` is neither space/comment nor a hex digit → `Unknown` (5). -/
theorem loop_unknown_high (inp : List Nat) (cap : Nat) (c : Nat) (rest' emitted : List Nat) (s : State)
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false) (hn : Hex0.nibble c = none)
    (inv : LoopInv inp cap s (c :: rest') emitted) : ∃ k, Result (runFuel 0 k s) inp cap := by
  obtain ⟨s64, hr64, hpc64, h7_64, hcode64, hmem64, h5_64, h6_64, h1_64, h10_64, h11_64, h13_64, hc256⟩ :=
    reach64 inp cap c rest' emitted s hsc hss inv
  obtain ⟨k1, hpcU, hmemU, hothU⟩ := high_parse_unknown s64 hcode64 c hpc64 h7_64 hc256 hn
  have hdec : Hex0.decode inp = (emitted, Hex0.Status.Unknown) := by
    have hsl := inv.spec_link
    have hdtok : Hex0.decodeS .High (c :: rest') = ([], Hex0.Status.Unknown) := by
      rw [Hex0.decodeS]; simp [hsc, hss, hn]
    rw [hdtok] at hsl; simpa [Hex0.decode] using hsl
  refine reach_error s (runFuel 0 k1 s64) inp cap emitted 312 5 (14 + k1) Hex0.Status.Unknown
    ?_ hpcU ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide) (by decide) rfl hdec
    inv.emitted_le inv.out_mem
  · rw [runFuel_add, hr64]
  · intro i hi; rw [hmemU, hmem64]; exact inv.code i hi
  · rw [hmemU, hmem64]
  · rw [hothU 6 (by decide)]; exact h6_64
  · rw [hothU 1 (by decide)]; exact h1_64

set_option maxRecDepth 4000 in
/-- Error case: high nibble `c`, low char `l` is neither stop nor hex digit → `Unknown` (5). -/
theorem loop_unknown_low (inp : List Nat) (cap : Nat) (c hi l : Nat) (rest'' emitted : List Nat)
    (s : State) (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (hnh : Hex0.nibble c = some hi) (hlls : Hex0.isLowStop l = false) (hnl : Hex0.nibble l = none)
    (inv : LoopInv inp cap s (c :: l :: rest'') emitted) : ∃ k, Result (runFuel 0 k s) inp cap := by
  obtain ⟨k0, s124, hr124, hpc124, h7_124, hcode124, hmem124, h6_124, h1_124, h13_124, hl256⟩ :=
    reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv
  -- l not a stop char → low beq chain falls through to 164
  have hl5 : l ≠ 10 ∧ l ≠ 32 ∧ l ≠ 95 ∧ l ≠ 35 ∧ l ≠ 59 := by
    simp only [Hex0.isLowStop, Hex0.isSpace, Hex0.isComment, Hex0.c_nl, Hex0.c_sp, Hex0.c_us,
      Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hlls
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  obtain ⟨hpcE, hmemE, hothE⟩ :=
    low_beq_ft s124 hcode124 l hpc124 h7_124 hl256 hl5.2.2.2.1 hl5.2.2.2.2 hl5.1 hl5.2.1 hl5.2.2.1
  have hcodeE : CodeLoaded (runFuel 0 10 s124) := by intro i hi; rw [hmemE]; exact hcode124 i hi
  have h7E : (runFuel 0 10 s124).rget 7 = BitVec.ofNat 64 l := by rw [hothE 7 (by decide)]; exact h7_124
  obtain ⟨k1, hpcU, hmemU, hothU⟩ := low_parse_unknown (runFuel 0 10 s124) hcodeE l hpcE h7E hl256 hnl
  have hdec : Hex0.decode inp = (emitted, Hex0.Status.Unknown) := by
    have hsl := inv.spec_link
    have hdtok : Hex0.decodeS .High (c :: l :: rest'') = ([], Hex0.Status.Unknown) := by
      rw [Hex0.decodeS]; simp only [hsc, hss, hnh, Bool.false_eq_true, if_false]
      rw [Hex0.decodeS]; simp [hlls, hnl]
    rw [hdtok] at hsl; simpa [Hex0.decode] using hsl
  refine reach_error s (runFuel 0 k1 (runFuel 0 10 s124)) inp cap emitted 312 5
    (k0 + (10 + k1)) Hex0.Status.Unknown ?_ hpcU ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl hdec inv.emitted_le ?_
  · rw [runFuel_add, hr124, runFuel_add]
  · intro i hi; rw [hmemU, hmemE, hmem124]; exact inv.code i hi
  · rw [hmemU, hmemE, hmem124]
  · rw [hothU 6 (by decide), hothE 6 (by decide)]; exact h6_124
  · rw [hothU 1 (by decide), hothE 1 (by decide)]; exact h1_124
  · intro j hj; rw [hmem124] at *; exact inv.out_mem j hj

set_option maxRecDepth 4000 in
/-- Error case: valid byte `c`,`l` but the output is full (`|emitted| = cap`) →
    OutputShort (2): `coreSpec` truncates the (longer) decode to `emitted`. -/
theorem loop_short (inp : List Nat) (cap : Nat) (c hi l lo : Nat) (rest'' emitted : List Nat)
    (s : State) (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (hnh : Hex0.nibble c = some hi) (hnl : Hex0.nibble l = some lo) (hge : cap ≤ emitted.length)
    (inv : LoopInv inp cap s (c :: l :: rest'') emitted) : ∃ k, Result (runFuel 0 k s) inp cap := by
  have heq : emitted.length = cap := Nat.le_antisymm inv.emitted_le hge
  have hlls : Hex0.isLowStop l = false := nibble_not_lowstop l lo hnl
  obtain ⟨k0, s124, hr124, hpc124, h7_124, hcode124, hmem124, h6_124, h1_124, h13_124, hl256⟩ :=
    reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv
  have hl5 : l ≠ 10 ∧ l ≠ 32 ∧ l ≠ 95 ∧ l ≠ 35 ∧ l ≠ 59 := by
    simp only [Hex0.isLowStop, Hex0.isSpace, Hex0.isComment, Hex0.c_nl, Hex0.c_sp, Hex0.c_us,
      Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hlls
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  obtain ⟨hpcE, hmemE, hothE⟩ :=
    low_beq_ft s124 hcode124 l hpc124 h7_124 hl256 hl5.2.2.2.1 hl5.2.2.2.2 hl5.1 hl5.2.1 hl5.2.2.1
  have hcodeE : CodeLoaded (runFuel 0 10 s124) := by intro i hi; rw [hmemE]; exact hcode124 i hi
  have h7E : (runFuel 0 10 s124).rget 7 = BitVec.ofNat 64 l := by rw [hothE 7 (by decide)]; exact h7_124
  obtain ⟨k1, hpcF, hmemF, h30F, hothF⟩ := low_parse (runFuel 0 10 s124) hcodeE l lo hpcE h7E hl256 hnl
  -- at off 208, t1 = |emitted| = cap = a3 → bgeu taken → .Lshort (276)
  have h6F : (runFuel 0 k1 (runFuel 0 10 s124)).rget 6 = BitVec.ofNat 64 emitted.length := by
    rw [hothF 6 (by decide) (by decide), hothE 6 (by decide)]; exact h6_124
  have h13F : (runFuel 0 k1 (runFuel 0 10 s124)).rget 13 = BitVec.ofNat 64 emitted.length := by
    rw [hothF 13 (by decide) (by decide), hothE 13 (by decide), h13_124, heq]
  have h1F : (runFuel 0 k1 (runFuel 0 10 s124)).rget 1 = 0 := by
    rw [hothF 1 (by decide) (by decide), hothE 1 (by decide)]; exact h1_124
  have hcodeF : CodeLoaded (runFuel 0 k1 (runFuel 0 10 s124)) := by
    intro i hi; rw [hmemF, hmemE, hmem124]; exact inv.code i hi
  have hbt := bgeu_eq_taken (runFuel 0 k1 (runFuel 0 10 s124)) 208 6 13 emitted.length 0x0044#13
    (BitVec.ofNat 64 (Image.coreAddr + 276)) hcodeF hpcF h6F h13F (by decide) (by decide) (by decide)
  have hcodeE : CodeLoaded ((runFuel 0 k1 (runFuel 0 10 s124)).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 276))) := by
    intro i hi; simp only [setPc_mem]; exact hcodeF i hi
  obtain ⟨hp, ha0, ha1, hm⟩ := halt_epilogue
    ((runFuel 0 k1 (runFuel 0 10 s124)).setPc (BitVec.ofNat 64 (Image.coreAddr + 276)))
    276 2 emitted.length hcodeE (by simp only [setPc_pc]) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [setPc_rget]; exact h6F) (by rw [setPc_rget]; exact h1F)
  have hdtok := decodeS_byte c l rest'' hi lo hsc hss hnh hlls hnl
  have hdec : Hex0.decode inp =
      (emitted ++ (hi * 16 + lo) :: (Hex0.decodeS .High rest'').1, (Hex0.decodeS .High rest'').2) := by
    have hsl := inv.spec_link; rw [hdtok] at hsl; simpa [Hex0.decode] using hsl
  refine ⟨k0 + (10 + k1) + 1 + 3, ?_⟩
  rw [runFuel_add]
  have hrunSE : runFuel 0 (k0 + (10 + k1) + 1) s
      = (runFuel 0 k1 (runFuel 0 10 s124)).setPc (BitVec.ofNat 64 (Image.coreAddr + 276)) := by
    rw [runFuel_add, runFuel_add, hr124, runFuel_add, hbt]
  rw [hrunSE]
  refine short_result _ inp cap emitted _ (Hex0.decodeS .High rest'').2 hp ha0 ?_ ?_ hdec ?_ ?_
  · rw [ha1, heq]
  · intro j hj; rw [hm]; simp only [setPc_mem]; rw [hmemF, hmemE, hmem124]
    exact inv.out_mem j (by omega)
  · rw [List.length_append, List.length_cons]; omega
  · rw [← heq]; exact List.take_left _ _

/-- One main-loop iteration (the machine side of step 3). From a non-empty
    remaining input, the machine either halts correctly (error / output-short)
    or returns to the loop head with strictly less remaining input and the
    invariant preserved. THIS is the remaining frontier: a case analysis on the
    head char's class, each a straight-line `step_*` chain + the arithmetic
    toolkit + (for `sb`) the output/code disjointness frame. The reusable blocks
    `loop_prefix`, `li_beq_ne`, `spacing_loopinv` are in hand. -/
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

set_option maxRecDepth 4000 in
/-- The prologue: from `initOn`, the two entry instructions `li t0,0; li t1,0`
    reach the loop head establishing the initial invariant (full input remaining,
    nothing emitted). Uses `code_initOn`/`in_initOn` for the memory facts. -/
theorem init_loopinv (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    LoopInv inp cap (runFuel 0 2 (Harness.initOn inp cap)) inp [] := by
  have hcode0 : CodeLoaded (Harness.initOn inp cap) := code_initOn inp cap hwf
  have hpc0 : (Harness.initOn inp cap).pc = BitVec.ofNat 64 (Image.coreAddr + 0) := rfl
  -- step 1: li t0,0
  have hs1 : step (Harness.initOn inp cap)
      = ((Harness.initOn inp cap).rset 5 0).setPc (BitVec.ofNat 64 (Image.coreAddr + 4)) := by
    have e : (Harness.initOn inp cap).pc + 4 = BitVec.ofNat 64 (Image.coreAddr + 4) := by
      rw [hpc0]; decide
    rw [step_addi (Harness.initOn inp cap) 0 5 0 0#12 hcode0 (by decide) hpc0 (by decide),
        show (Harness.initOn inp cap).rget 0 + (0#12).signExtend 64 = 0 from by rw [rget_zero]; decide, e]
  let s1 := ((Harness.initOn inp cap).rset 5 0).setPc (BitVec.ofNat 64 (Image.coreAddr + 4))
  have hs1d : s1 = ((Harness.initOn inp cap).rset 5 0).setPc
      (BitVec.ofNat 64 (Image.coreAddr + 4)) := rfl
  rw [← hs1d] at hs1
  have hcode1 : CodeLoaded s1 := by intro i hi; rw [hs1d]; simp only [setPc_mem, rset_mem]; exact hcode0 i hi
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image.coreAddr + 4) := rfl
  -- step 2: li t1,0
  have hs2 : step s1 = (s1.rset 6 0).setPc LOOP := by
    have e : s1.pc + 4 = LOOP := by rw [hpc1]; decide
    rw [step_addi s1 4 6 0 0#12 hcode1 (by decide) hpc1 (by decide),
        show s1.rget 0 + (0#12).signExtend 64 = 0 from by rw [rget_zero]; decide, e]
  let s2 := (s1.rset 6 0).setPc LOOP
  have hs2d : s2 = (s1.rset 6 0).setPc LOOP := rfl
  rw [← hs2d] at hs2
  have hfinal : runFuel 0 2 (Harness.initOn inp cap) = s2 := by
    simp only [runFuel]
    rw [hs1, hs2, if_neg (by rw [hpc0]; decide), if_neg (by rw [hpc1]; decide)]
  rw [hfinal]
  refine { at_loop := rfl, code := ?_, a0 := ?_, a1 := ?_, a2 := ?_, a3 := ?_,
           ra0 := ?_, in_mem := ?_, in_lt := ?_, bytes_lt := hwf.bytes_ok,
           in_fits := hwf.in_fits, out_lt := hwf.out_fits,
           idx := ?_, suffix := ?_, outidx := ?_, emitted_le := Nat.zero_le _,
           out_mem := ?_, spec_link := ?_ }
  · intro i hi; rw [hs2d]; simp only [setPc_mem, rset_mem]; rw [hs1d]
    simp only [setPc_mem, rset_mem]; exact hcode0 i hi
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (10:Nat) ≠ 6),
        hs1d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (10:Nat) ≠ 5)]; rfl
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (11:Nat) ≠ 6),
        hs1d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (11:Nat) ≠ 5)]; rfl
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (12:Nat) ≠ 6),
        hs1d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (12:Nat) ≠ 5)]; rfl
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (13:Nat) ≠ 6),
        hs1d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (13:Nat) ≠ 5)]; rfl
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (1:Nat) ≠ 6),
        hs1d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (1:Nat) ≠ 5)]; rfl
  · intro j hj; rw [hs2d]; simp only [setPc_mem, rset_mem]; rw [hs1d]
    simp only [setPc_mem, rset_mem]; exact in_initOn inp cap hwf j hj
  · have := hwf.in_fits; have := hwf.out_fits; omega
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 6),
        hs1d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
    simp [Nat.sub_self]
  · simp [Nat.sub_self]
  · rw [hs2d, setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · intro j hj; simp at hj
  · simp

/-! ## Pure spec lemmas for the `observe`/`coreSpec` conversion. -/

theorem decodeS_bytes_lt : ∀ (st : Hex0.St) (l : List Nat),
    (∀ hi, st = Hex0.St.Low hi → hi < 16) → ∀ b, b ∈ (Hex0.decodeS st l).1 → b < 256
  | .High, [], _, b, hb => by simp [Hex0.decodeS] at hb
  | .Low _, [], _, b, hb => by simp [Hex0.decodeS] at hb
  | .High, c :: rest, _, b, hb => by
      rw [Hex0.decodeS] at hb
      by_cases hc : Hex0.isComment c = true
      · rw [if_pos hc] at hb
        exact decodeS_bytes_lt .High (Hex0.skipComment rest) (fun _ h => nomatch h) b hb
      · rw [if_neg hc] at hb
        by_cases hs : Hex0.isSpace c = true
        · rw [if_pos hs] at hb
          exact decodeS_bytes_lt .High rest (fun _ h => nomatch h) b hb
        · rw [if_neg hs] at hb
          cases hn : Hex0.nibble c with
          | none => rw [hn] at hb; simp [Hex0.decodeS] at hb
          | some hi => rw [hn] at hb
                       exact decodeS_bytes_lt (.Low hi) rest
                         (fun hi' h => by cases h; exact nibble_lt _ _ hn) b hb
  | .Low hi, c :: rest, hpre, b, hb => by
      rw [Hex0.decodeS] at hb
      by_cases hls : Hex0.isLowStop c = true
      · rw [if_pos hls] at hb; simp at hb
      · rw [if_neg hls] at hb
        cases hn : Hex0.nibble c with
        | none => rw [hn] at hb; simp at hb
        | some lo =>
          rw [hn] at hb
          simp only [List.mem_cons] at hb
          rcases hb with h | h
          · subst h
            have := nibble_lt _ _ hn
            have := hpre hi rfl
            omega
          · exact decodeS_bytes_lt .High rest (fun _ hh => nomatch hh) b h
  termination_by st l => l.length
  decreasing_by
    · exact Nat.lt_of_le_of_lt (Hex0.skipComment_len rest) (by simp)
    · simp
    · simp
    · simp

theorem decode_bytes_lt (l : List Nat) : ∀ b ∈ (Hex0.decode l).1, b < 256 :=
  fun b hb => decodeS_bytes_lt Hex0.St.High l (fun _ h => nomatch h) b hb

theorem range_getD (l : List Nat) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 _
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h1)]; rfl

/-- Shape facts about `coreSpec` needed for the conversion. -/
theorem coreSpec_props (inp : List Nat) (cap : Nat) :
    (Hex0.coreSpec inp cap).1 < 2 ^ 64 ∧
    (Hex0.coreSpec inp cap).2.2 = (Hex0.coreSpec inp cap).2.1.length ∧
    (Hex0.coreSpec inp cap).2.2 ≤ cap ∧
    (∀ b ∈ (Hex0.coreSpec inp cap).2.1, b < 256) := by
  unfold Hex0.coreSpec
  have hb := decode_bytes_lt inp
  cases hd : Hex0.decode inp with
  | mk bs st =>
    rw [hd] at hb
    by_cases hlt : cap < bs.length
    · simp only [hlt, if_true]
      refine ⟨(by decide), ?_, Nat.le_refl _, fun b hbm => hb b (List.mem_of_mem_take hbm)⟩
      rw [List.length_take]; omega
    · simp only [hlt, if_false]
      have hst : Hex0.statusCode st < 2 ^ 64 := by cases st <;> decide
      exact ⟨hst, trivial, (by omega), hb⟩

/-! ## The general refinement theorem. -/
theorem core_refines (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    ∃ fuel, Harness.observe inp cap fuel = Hex0.coreSpec inp cap := by
  obtain ⟨m, hres⟩ :=
    loop_correct inp cap inp.length inp [] _ (Nat.le_refl _) (init_loopinv inp cap hwf)
  obtain ⟨_, h10, h11, hmem⟩ := hres
  obtain ⟨hst, hlen, hle, hbytes⟩ := coreSpec_props inp cap
  have hol : (Hex0.coreSpec inp cap).2.2 < 2 ^ 64 := by have := hwf.out_fits; omega
  refine ⟨2 + m, ?_⟩
  -- the three components
  have e10 : ((runFuel 0 m (runFuel 0 2 (Harness.initOn inp cap))).rget 10).toNat
           = (Hex0.coreSpec inp cap).1 := by
    rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hst]
  have e11 : ((runFuel 0 m (runFuel 0 2 (Harness.initOn inp cap))).rget 11).toNat
           = (Hex0.coreSpec inp cap).2.2 := by
    rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hol]
  have eOut : Harness.readMem (runFuel 0 m (runFuel 0 2 (Harness.initOn inp cap))).mem
                Image.outAddr ((runFuel 0 m (runFuel 0 2 (Harness.initOn inp cap))).rget 11).toNat
            = (Hex0.coreSpec inp cap).2.1 := by
    rw [e11, hlen]
    unfold Harness.readMem
    apply List.ext_getElem
    · simp
    · intro i h1 _
      have hi : i < (Hex0.coreSpec inp cap).2.1.length := by simpa using h1
      have hi2 : i < (Hex0.coreSpec inp cap).2.2 := by rw [hlen]; exact hi
      simp only [List.getElem_map, List.getElem_range]
      rw [hmem i hi2, BitVec.toNat_ofNat, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi, Option.getD_some]
      exact Nat.mod_eq_of_lt (hbytes _ (List.getElem_mem hi))
  simp only [Harness.observe, runFuel_add]
  rw [eOut, e10, e11]

end Hex0.Refine
