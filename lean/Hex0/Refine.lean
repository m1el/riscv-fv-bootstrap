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

/-! ## Code-loaded predicate and well-formedness -/

/-- The 81 instruction words of `core` (each 4 LE bytes of `Image.coreBytes`). -/
def coreWords : List (BitVec 32) :=
  (List.range (Image.coreBytes.length / 4)).map (fun k =>
    let b := fun j => BitVec.ofNat 32 (Image.coreBytes.getD (4 * k + j) 0)
    b 0 ||| (b 1) <<< 8 ||| (b 2) <<< 16 ||| (b 3) <<< 24)

/-- `core`'s bytes sit at `coreAddr .. coreAddr+324` in `s`. -/
def CodeLoaded (s : State) : Prop :=
  ∀ i, i < Image.coreBytes.length →
    s.mem (BitVec.ofNat 64 (Image.coreAddr + i)) = BitVec.ofNat 8 (Image.coreBytes.getD i 0)

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
  -- in_idx (t0) is the consumed prefix length; `rest` is what remains
  idx       : s.rget 5  = BitVec.ofNat 64 (inp.length - rest.length)
  suffix    : inp.drop (inp.length - rest.length) = rest
  -- out_idx (t1) counts emitted bytes, which are in the output region
  outidx    : s.rget 6  = BitVec.ofNat 64 emitted.length
  emitted_le : emitted.length ≤ cap
  out_mem   : ∀ j, j < emitted.length →
                s.mem (BitVec.ofNat 64 (Image.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0)

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
