/-
  LowIR.ProgSim.LayoutFacts — Phase 2, the `layout`↔`Emitted` position arithmetic.

  The remaining half of `hfn`/`hem` (RESUME-CALL §C4): tie each function's byte
  position `fnPos g` (from the compiler's `layout` pass) to the slice of the
  RESOLVED instruction stream `L.instrs` it occupies, then compose with
  `lower_resolve` (LowerFacts) + `prologue_resolves`/`epilogue_resolves` (AsmFacts
  §6) to get the per-function `Emitted L (fnPos g) (prologueI ++ emitCF … ++
  epilogueI)` that `lower_sim_cf`/`prog_sim` take.

  Built bottom-up:
  - the resolve-length bridge (`resolveOne_length`/`resolve_length`): a laid-out
    item resolves to `symSize/4` instructions, so the resolved instruction count
    times 4 is the byte span — the BYTE-POSITION ↔ INSTRUCTION-INDEX conversion.
-/
import LowIR.ProgSim.LowerFacts

open LowIR Rv64i
open LowIR.Compile
open LowIR.ProgSim
open LowIR.ProgSim.AsmFacts
open LowIR.ProgSim.LowerFacts
open LowIR.Prog (FunDef Data Name)

namespace LowIR.ProgSim.LayoutFacts

local notation "PStmt" => LowIR.Prog.Stmt

/-! ## The resolve-length bridge: resolved instr count × 4 = byte span. -/

/-- A single laid-out symbolic item resolves to exactly `symSize / 4` instructions
    (label → 0, `cref` → 5, everything else → 1). -/
theorem resolveOne_length (lbls fns dats : List _) (pos : Nat) (si : SymInstr) (v : List Instr)
    (h : resolveOne lbls fns dats (pos, si) = some v) : 4 * v.length = symSize si := by
  cases si with
  | label l => rw [← Option.some.inj h]; rfl
  | ins i => rw [← Option.some.inj h]; rfl
  | br c a b l =>
      cases hlk : List.lookup l lbls with
      | none => simp only [resolveOne, hlk, bind, Option.bind] at h; exact absurd h (by simp)
      | some tgt =>
          simp only [resolveOne, hlk, bind, Option.bind] at h; split at h
          all_goals first | (rw [← Option.some.inj h]; rfl) | (exact absurd h (by simp))
  | jmp l =>
      cases hlk : List.lookup l lbls with
      | none => simp only [resolveOne, hlk, bind, Option.bind] at h; exact absurd h (by simp)
      | some tgt =>
          simp only [resolveOne, hlk, bind, Option.bind] at h; split at h
          all_goals first | (rw [← Option.some.inj h]; rfl) | (exact absurd h (by simp))
  | callf f =>
      cases hlk : List.lookup f fns with
      | none => simp only [resolveOne, hlk, bind, Option.bind] at h; exact absurd h (by simp)
      | some tgt =>
          simp only [resolveOne, hlk, bind, Option.bind] at h; split at h
          all_goals first | (rw [← Option.some.inj h]; rfl) | (exact absurd h (by simp))
  | cref d =>
      cases hlk : List.lookup d dats with
      | none => simp only [resolveOne, hlk, bind, Option.bind] at h; exact absurd h (by simp)
      | some off =>
          simp only [resolveOne, hlk, bind, Option.bind] at h; split at h
          all_goals first | (rw [← Option.some.inj h]; rfl) | (exact absurd h (by simp))

/-- `layoutItems` of a cons: the head sits at `pos`, the tail is laid out
    `symSize`-later (uniform because a `.label` has `symSize 0`). -/
theorem layoutItems_cons_fst (si : SymInstr) (rest : List SymInstr) (pos : Nat) :
    (layoutItems (si :: rest) pos).1 = (pos, si) :: (layoutItems rest (pos + symSize si)).1 := by
  cases si <;> simp [layoutItems, symSize]

/-- The resolved stream of a laid-out item list has `totalSymSize / 4` instructions:
    `4 · #instrs = byte span`. -/
theorem resolve_length (lbls fns dats : List _) :
    ∀ (items : List SymInstr) (pos : Nat) (rs : List (List Instr)),
      (layoutItems items pos).1.mapM (resolveOne lbls fns dats) = some rs →
      4 * rs.flatten.length = totalSymSize items := by
  intro items
  induction items with
  | nil => intro pos rs h; simp only [layoutItems, List.mapM_nil] at h
           rw [← Option.some.inj h]; rfl
  | cons si rest ih =>
    intro pos rs h
    rw [layoutItems_cons_fst, List.mapM_cons] at h
    cases hr1 : resolveOne lbls fns dats (pos, si) with
    | none => rw [hr1] at h; simp at h
    | some v1 =>
      cases hr2 : (layoutItems rest (pos + symSize si)).1.mapM (resolveOne lbls fns dats) with
      | none => rw [hr1, hr2] at h; simp at h
      | some rs' =>
        rw [hr1, hr2] at h
        simp only [bind, Option.bind, pure, Option.some.injEq] at h
        rw [← h, List.flatten_cons, List.length_append, Nat.mul_add,
            resolveOne_length _ _ _ _ _ _ hr1, ih _ _ hr2, totalSymSize_cons]

/-! ## The `layout` pass algebra (over the segment list). -/

/-- `layout`'s end position is `pos` plus the total size of all segments' items. -/
theorem layout_end : ∀ (segs : List (Name × List SymInstr)) (pos : Nat),
    (layout segs pos).2.2.2 = pos + totalSymSize (segs.flatMap Prod.snd) := by
  intro segs
  induction segs with
  | nil => intro pos; simp [layout]
  | cons s rest ih =>
    intro pos
    obtain ⟨n, items⟩ := s
    show (layout rest (layoutItems items pos).2.2).2.2.2 = _
    rw [ih, layoutItems_pos, List.flatMap_cons, totalSymSize_append]
    dsimp only; omega

/-- `layout`'s positioned stream distributes over a segment-list append: the second
    group is laid out starting where the first group ended. -/
theorem layout_flat_append : ∀ (segsA segsB : List (Name × List SymInstr)) (pos : Nat),
    (layout (segsA ++ segsB) pos).1
      = (layout segsA pos).1 ++ (layout segsB (layout segsA pos).2.2.2).1 := by
  intro segsA
  induction segsA with
  | nil => intro segsB pos; simp [layout]
  | cons s rest ih =>
    intro segsB pos
    obtain ⟨n, items⟩ := s
    show (layoutItems items pos).1 ++ (layout (rest ++ segsB) (layoutItems items pos).2.2).1
       = ((layoutItems items pos).1 ++ (layout rest (layoutItems items pos).2.2).1)
         ++ (layout segsB (layout rest (layoutItems items pos).2.2).2.2.2).1
    rw [ih, List.append_assoc]

/-- Likewise the function table distributes; the second group's positions start at
    the first group's end. -/
theorem layout_fns_append : ∀ (segsA segsB : List (Name × List SymInstr)) (pos : Nat),
    (layout (segsA ++ segsB) pos).2.2.1
      = (layout segsA pos).2.2.1 ++ (layout segsB (layout segsA pos).2.2.2).2.2.1 := by
  intro segsA
  induction segsA with
  | nil => intro segsB pos; simp [layout]
  | cons s rest ih =>
    intro segsB pos
    obtain ⟨n, items⟩ := s
    show (n, pos) :: (layout (rest ++ segsB) (layoutItems items pos).2.2).2.2.1
       = ((n, pos) :: (layout rest (layoutItems items pos).2.2).2.2.1)
         ++ (layout segsB (layout rest (layoutItems items pos).2.2).2.2.2).2.2.1
    rw [ih, List.cons_append]

end LowIR.ProgSim.LayoutFacts
