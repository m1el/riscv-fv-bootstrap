/-
  hex0 functional correctness at the IL (structured) altitude — the larger analogue
  of `strlen_correct`. STATEMENT + proof plan now; the inductive proof is deferred
  (`sorry`, sanctioned like `compile_sim`). The executable certification
  (`Hex0Prog.hex0_matches_spec`) already validates this on a 17-case battery; this
  file makes the *general* theorem a concrete object to reason about and discharge.

  IL-level (about `exec`, not the compiled bytes); `T1 ∘ hex0_correct` then transports
  it to the trusted RV64I machine — the same shape `strlen` will follow.
-/
import LowIR.Hex0.Prog
import Spec.Hex0.Spec

namespace LowIR.Hex0Prog

open LowIR
open Rv64i (Word Byte)

/-- Initial IL state: input bytes at `inBase`, x10..x13 = (in_ptr,in_len,out_ptr,cap),
    output region (and all else) reads as 0. -/
def hex0ILState (inp : List Byte) (cap : Nat) : St :=
  { regs := fun i =>
      if i = 10 then inBase
      else if i = 11 then BitVec.ofNat 64 inp.length
      else if i = 12 then outBase
      else if i = 13 then BitVec.ofNat 64 cap
      else 0
    mem := fun a =>
      let ia := (a - inBase).toNat
      if ia < inp.length then (inp[ia]?).getD 0 else 0 }

/-- Decoded output bytes read back from the output region (`out_len = x6`). -/
def outBytes (s : St) : List Nat :=
  (List.range (s.rget 6).toNat).map (fun i => (s.mem (outBase + BitVec.ofNat 64 i)).toNat)

/-- Regions are laid out disjointly (input ⊂ [0x1000,0x4000), output at [0x4000,…)). -/
def Disjoint (inp : List Byte) (cap : Nat) : Prop := inp.length < 0x3000 ∧ cap < 0x3000

/-- **hex0 is correct (IL level).** For disjoint layout, the IL execution of `hex0`
    from `hex0ILState` reproduces the functional spec `coreSpec`: the status (x14),
    the decoded output region, and the output length (x6) match.

    PROOF PLAN (the deferred work — structured, no PC/decode/offsets):

    Central invariant for the main `while in_idx < in_len` loop. Write `J = in_idx`,
    and split `decode = decodeS .High inp` (the spec). The loop maintains, at each head:
      • x5 = in_idx = ofNat J,  x11 = ofNat inp.length,  x10 = inBase, x12 = outBase,
        x13 = ofNat cap, plus the 12 constant registers fixed;
      • the *prefix consumed so far* `inp.take J` has decoded to exactly the bytes
        currently in `[outBase, outBase + out_idx)` (x6 = ofNat out_idx), in agreement
        with `decodeS .High` run on that prefix, AND no error/short has occurred yet
        (x14 = 0); equivalently, `decodeS .High inp = decodeS .High (inp.drop J)`
        pre-pended by the produced bytes;
      • input memory `[inBase, inBase+inp.length)` is unchanged (the program only
        stores into the disjoint output region — uses `Disjoint`);
      • out_idx ≤ cap.

    Three sub-lemmas, each a structured-altitude `while`/`ife` argument like `strlen`:
      (L-skip) the comment inner loop advances in_idx to the next '\n'/EOF, matching
        `Spec.skipComment`, leaving output/out_idx fixed;
      (L-body) one main-loop iteration corresponds to one `decodeS` token: a High-state
        classification (comment/space/hex-digit) and, on a digit, a Low-state step that
        emits `hi*16+lo` (or sets the matching error status and forces `in_idx := in_len`);
      (L-cap) the capacity branch (`out_idx ≥ cap → status 2`) realises `coreSpec`'s
        `if cap < bs.length` truncation.
    Termination/fuel: take fuel ≈ `c₁ * inp.length + c₂` (each input byte consumed by a
    bounded number of statements; the comment loop consumes its own bytes). Induct on
    `inp.length - J` (strictly decreasing: every iteration advances in_idx, like the
    spec's well-founded recursion on input length).
    Finally relate the loop postcondition (in_idx = in_len, or error exit) to
    `coreSpec inp cap` by case-analysis on the terminal `Status`.

    The whole argument is structural induction at the IL level — no program counter,
    no instruction decode, no branch offsets. `T1` then carries it to the bytes. -/
theorem hex0_correct (inp : List Byte) (cap : Nat) (_hdisj : Disjoint inp cap) :
    ∃ fuel s, exec fuel hex0 (hex0ILState inp cap) = some s
      ∧ ((s.rget 14).toNat, outBytes s, (s.rget 6).toNat)
          = Hex0.coreSpec (inp.map (·.toNat)) cap := by
  sorry

end LowIR.Hex0Prog
