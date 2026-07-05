/-
  LowIR.ProgSim.LowerFacts — Phase 2, the `lower`↔`emitCF` correspondence.

  The last big piece of `hfn`/`hem` (RESUME-CALL §C4): the compiler's RESOLVED
  per-function body stream (`resolveOne` over `layoutItems` of `lower dat [] []
  epi gd.body`) equals `emitCF P.data dpos fnPos [] [] epiPos bodyPos gd.body`.
  `matchesRealProg` (CtrlSim) is its decidable shadow.

  This file builds it bottom-up. Layer 1 (here): the structural `layoutItems`
  algebra — `totalSymSize`, `layoutItems_pos`/`_append` — and the resolve
  composition (`mapM_append_inv`, `resolve_flatten_append`). These let the
  correspondence induction split a `lower` output (built by `++`) into its
  positioned, resolved pieces. The correspondence induction itself (threading a
  label-environment consistency relation, deriving each jump's resolved offset
  from the layout positions) builds on top.
-/
import LowIR.ProgSim.AsmFacts

open LowIR Rv64i
open LowIR.Compile
open LowIR.ProgSim
open LowIR.ProgSim.AsmFacts
open LowIR.Prog (FunDef)

namespace LowIR.ProgSim.LowerFacts

local notation "PStmt" => LowIR.Prog.Stmt

/-- Total emitted byte size of a symbolic stream. -/
def totalSymSize (l : List SymInstr) : Nat := (l.map symSize).sum

@[simp] theorem totalSymSize_nil : totalSymSize [] = 0 := rfl

@[simp] theorem totalSymSize_cons (si : SymInstr) (l : List SymInstr) :
    totalSymSize (si :: l) = symSize si + totalSymSize l := by
  simp [totalSymSize]

@[simp] theorem totalSymSize_append (a b : List SymInstr) :
    totalSymSize (a ++ b) = totalSymSize a + totalSymSize b := by
  simp [totalSymSize, List.map_append, List.sum_append]

/-- `layoutItems`'s end position is `pos` plus the total size. -/
theorem layoutItems_pos (sym : List SymInstr) (pos : Nat) :
    (layoutItems sym pos).2.2 = pos + totalSymSize sym := by
  induction sym generalizing pos with
  | nil => simp [layoutItems]
  | cons si rest ih =>
    cases si with
    | label l => simp only [layoutItems, totalSymSize_cons, symSize]; rw [ih]; omega
    | ins i => simp only [layoutItems, totalSymSize_cons]; rw [ih]; omega
    | br c a b l => simp only [layoutItems, totalSymSize_cons]; rw [ih]; omega
    | jmp l => simp only [layoutItems, totalSymSize_cons]; rw [ih]; omega
    | callf f => simp only [layoutItems, totalSymSize_cons]; rw [ih]; omega
    | cref d => simp only [layoutItems, totalSymSize_cons]; rw [ih]; omega

/-- `layoutItems` distributes over append: the flat/label lists concatenate and
    the second stream starts where the first ends. -/
theorem layoutItems_append (a b : List SymInstr) (pos : Nat) :
    (layoutItems (a ++ b) pos).1
      = (layoutItems a pos).1 ++ (layoutItems b (pos + totalSymSize a)).1
    ∧ (layoutItems (a ++ b) pos).2.1
      = (layoutItems a pos).2.1 ++ (layoutItems b (pos + totalSymSize a)).2.1 := by
  induction a generalizing pos with
  | nil => simp [layoutItems]
  | cons si rest ih =>
    -- non-label items advance the position by `symSize si`; label items stay.
    cases si with
    | label l =>
      simp only [List.cons_append, layoutItems, totalSymSize_cons, symSize, Nat.zero_add,
                 List.cons.injEq, true_and]
      exact ih pos
    | ins i =>
      simp only [List.cons_append, layoutItems, totalSymSize_cons, List.cons.injEq, true_and]
      obtain ⟨ih1, ih2⟩ := ih (pos + symSize (.ins i))
      have hrw : pos + symSize (SymInstr.ins i) + totalSymSize rest
          = pos + (symSize (SymInstr.ins i) + totalSymSize rest) := by omega
      rw [hrw] at ih1 ih2; exact ⟨ih1, ih2⟩
    | br c aa bb l =>
      simp only [List.cons_append, layoutItems, totalSymSize_cons, List.cons.injEq, true_and]
      obtain ⟨ih1, ih2⟩ := ih (pos + symSize (.br c aa bb l))
      have hrw : pos + symSize (SymInstr.br c aa bb l) + totalSymSize rest
          = pos + (symSize (SymInstr.br c aa bb l) + totalSymSize rest) := by omega
      rw [hrw] at ih1 ih2; exact ⟨ih1, ih2⟩
    | jmp l =>
      simp only [List.cons_append, layoutItems, totalSymSize_cons, List.cons.injEq, true_and]
      obtain ⟨ih1, ih2⟩ := ih (pos + symSize (.jmp l))
      have hrw : pos + symSize (SymInstr.jmp l) + totalSymSize rest
          = pos + (symSize (SymInstr.jmp l) + totalSymSize rest) := by omega
      rw [hrw] at ih1 ih2; exact ⟨ih1, ih2⟩
    | callf f =>
      simp only [List.cons_append, layoutItems, totalSymSize_cons, List.cons.injEq, true_and]
      obtain ⟨ih1, ih2⟩ := ih (pos + symSize (.callf f))
      have hrw : pos + symSize (SymInstr.callf f) + totalSymSize rest
          = pos + (symSize (SymInstr.callf f) + totalSymSize rest) := by omega
      rw [hrw] at ih1 ih2; exact ⟨ih1, ih2⟩
    | cref d =>
      simp only [List.cons_append, layoutItems, totalSymSize_cons, List.cons.injEq, true_and]
      obtain ⟨ih1, ih2⟩ := ih (pos + symSize (.cref d))
      have hrw : pos + symSize (SymInstr.cref d) + totalSymSize rest
          = pos + (symSize (SymInstr.cref d) + totalSymSize rest) := by omega
      rw [hrw] at ih1 ih2; exact ⟨ih1, ih2⟩

/-! ## Resolve composition — `mapM` over append, inversion. -/

/-- A successful `mapM` over an append splits into successful halves whose
    results concatenate. -/
theorem mapM_append_inv {α β} (f : α → Option β) :
    ∀ (la lb : List α) (r : List β),
      (la ++ lb).mapM f = some r →
      ∃ ra rb, la.mapM f = some ra ∧ lb.mapM f = some rb ∧ r = ra ++ rb := by
  intro la
  induction la with
  | nil => intro lb r h; exact ⟨[], r, rfl, h, rfl⟩
  | cons a la' ih =>
    intro lb r h
    rw [List.cons_append, List.mapM_cons] at h
    cases hfa : f a with
    | none =>
      rw [hfa] at h
      replace h : (none : Option (List β)) = some r := h
      simp at h
    | some b =>
      rw [hfa] at h
      -- `some b >>= k` is defeq `k b`
      replace h : ((la' ++ lb).mapM f >>= fun bs => pure (b :: bs)) = some r := h
      cases hrest : (la' ++ lb).mapM f with
      | none =>
        rw [hrest] at h
        replace h : (none : Option (List β)) = some r := h
        simp at h
      | some bs =>
        rw [hrest] at h
        -- `some bs >>= (fun bs => pure (b::bs))` is defeq `some (b::bs)`
        replace h : (some (b :: bs) : Option (List β)) = some r := h
        obtain rfl := Option.some.inj h
        obtain ⟨ra', rb, hla', hlb, hbs⟩ := ih lb bs hrest
        refine ⟨b :: ra', rb, ?_, hlb, ?_⟩
        · rw [List.mapM_cons, hfa, hla']; rfl
        · rw [hbs, List.cons_append]

/-- Resolve+flatten distributes over a symbolic-stream append. -/
theorem resolve_flatten_append (lbls fns dats : List _) (a b : List SymInstr) (pos : Nat)
    (r : List (List Instr))
    (h : (layoutItems (a ++ b) pos).1.mapM (resolveOne lbls fns dats) = some r) :
    ∃ ra rb, (layoutItems a pos).1.mapM (resolveOne lbls fns dats) = some ra
      ∧ (layoutItems b (pos + totalSymSize a)).1.mapM (resolveOne lbls fns dats) = some rb
      ∧ r.flatten = ra.flatten ++ rb.flatten := by
  rw [(layoutItems_append a b pos).1] at h
  obtain ⟨ra, rb, hra, hrb, hr⟩ := mapM_append_inv _ _ _ _ h
  exact ⟨ra, rb, hra, hrb, by rw [hr, List.flatten_append]⟩

end LowIR.ProgSim.LowerFacts
