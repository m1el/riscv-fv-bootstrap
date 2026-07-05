/-
  LowIR.ProgSim.LowerFacts — Phase 2, the `lower`↔`emitCF` correspondence.

  The last big piece of `hfn`/`hem` (RESUME-CALL §C4): the compiler's RESOLVED
  per-function body stream (`resolveOne` over `layoutItems` of `lower dat [] []
  epi gd.body`) equals `emitCF P.data dpos fnPos [] [] epiPos bodyPos gd.body`.
  `matchesRealProg` (CtrlSim) is its decidable shadow.

  This file builds it bottom-up.
  - Layer 1: the structural `layoutItems` algebra — `totalSymSize`,
    `layoutItems_pos`/`_append` — and the resolve composition (`mapM_append_inv`,
    `resolve_flatten_append`), which let the correspondence induction split a
    `lower` output (built by `++`) into its positioned, resolved pieces.
  - Layer 2: the `lower_*` unfolding equations (all `rfl` — the `StateM Nat`
    counter threading is definitional) and `lower_totalSymSize` (every construct's
    lowering has byte size `4·csize`), the bridge that pins each internal label's
    layout position.
  Still owed (layer 3): the correspondence induction itself, threading a
  label-environment consistency relation and deriving each jump's resolved offset
  from the layout positions. Design in the handoff (RESUME-PROGSIM Phase 2).
-/
import LowIR.ProgSim.AsmFacts

open LowIR Rv64i
open LowIR.Compile
open LowIR.ProgSim
open LowIR.ProgSim.AsmFacts
open LowIR.Prog (FunDef Data Name)

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


/-! # Layer 2 — `lower` unfolding + the `totalSymSize`↔`csize` position bridge.

    The monadic `lower` (a `StateM Nat` allocating fresh label ids via `fresh`)
    unfolds by `rfl` on every constructor (the counter threading is definitional),
    so `lower_*` are the reusable equation lemmas. `lower_totalSymSize` then proves
    every construct's lowering has byte size `4·csize` — the bridge that pins each
    internal label's layout position for the correspondence induction. -/

/-! ## `lower` unfolding equations (all `rfl` — the monadic counter threading). -/

theorem lower_skip (dat : Data) (bs cs : List Nat) (epi cnt : Nat) :
    (lower dat bs cs epi .skip cnt).1 = [] := rfl
theorem lower_annot (dat : Data) (bs cs : List Nat) (epi cnt : Nat) (a : String) :
    (lower dat bs cs epi (.annot a) cnt).1 = [] := rfl
theorem lower_ret (dat : Data) (bs cs : List Nat) (epi cnt : Nat) :
    (lower dat bs cs epi .ret cnt).1 = [SymInstr.jmp epi] := rfl
theorem lower_brkB (dat : Data) (bs cs : List Nat) (epi cnt k : Nat) :
    (lower dat bs cs epi (.brkB k) cnt).1 = [SymInstr.jmp (bs.getD k 0)] := rfl
theorem lower_contL (dat : Data) (bs cs : List Nat) (epi cnt k : Nat) :
    (lower dat bs cs epi (.contL k) cnt).1 = [SymInstr.jmp (cs.getD k 0)] := rfl
theorem lower_seq (dat : Data) (bs cs : List Nat) (epi cnt : Nat) (a b : PStmt) :
    (lower dat bs cs epi (.seq a b) cnt).1
      = (lower dat bs cs epi a cnt).1
        ++ (lower dat bs cs epi b (lower dat bs cs epi a cnt).2).1 := rfl
theorem lower_block (dat : Data) (bs cs : List Nat) (epi cnt : Nat) (body : PStmt) :
    (lower dat bs cs epi (.block body) cnt).1
      = (lower dat (cnt :: bs) cs epi body (cnt + 1)).1 ++ [SymInstr.label cnt] := rfl
theorem lower_ife (dat : Data) (bs cs : List Nat) (epi cnt : Nat) (c : Cond) (a b : Nat) (t e : PStmt) :
    (lower dat bs cs epi (.ife c a b t e) cnt).1
      = loadSlot a T0 ++ loadSlot b T1 ++ [SymInstr.br c T0 T1 cnt]
        ++ (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).1
        ++ [SymInstr.jmp (cnt + 1), SymInstr.label cnt]
        ++ (lower dat bs cs epi t (cnt + 2)).1
        ++ [SymInstr.label (cnt + 1)] := rfl
theorem lower_while (dat : Data) (bs cs : List Nat) (epi cnt : Nat) (c : Cond) (a b : Nat) (body : PStmt) :
    (lower dat bs cs epi (.while c a b body) cnt).1
      = [SymInstr.label cnt] ++ loadSlot a T0 ++ loadSlot b T1
        ++ [SymInstr.br c T0 T1 (cnt + 1), SymInstr.jmp (cnt + 2), SymInstr.label (cnt + 1)]
        ++ (lower dat bs (cnt :: cs) epi body (cnt + 3)).1
        ++ [SymInstr.jmp cnt, SymInstr.label (cnt + 2)] := rfl
theorem lower_cref (dat : Data) (bs cs : List Nat) (epi cnt rd : Nat) (d : Name) :
    (lower dat bs cs epi (.cref rd d) cnt).1 = [SymInstr.cref d] ++ storeSlot rd T0 := rfl
theorem lower_clen (dat : Data) (bs cs : List Nat) (epi cnt rd : Nat) (d : Name) :
    (lower dat bs cs epi (.clen rd d) cnt).1
      = synthConst T0 (((List.lookup d dat).map (·.length)).getD 0) ++ storeSlot rd T0 := rfl

/-! ## `totalSymSize (lower … stmt) = 4 · csize stmt` — the position bridge. -/

theorem totalSymSize_loadSlot (r t : Reg) : totalSymSize (loadSlot r t) = 4 := by
  unfold loadSlot; by_cases h : r = 0 <;> simp [h, totalSymSize, symSize]

theorem totalSymSize_storeSlot (r t : Reg) : totalSymSize (storeSlot r t) = 4 * (storeSlotI r t).length := by
  unfold storeSlot storeSlotI; by_cases h : r = 0 <;> simp [h, totalSymSize, symSize]

theorem totalSymSize_flatMap_loadSlot (l : List (Nat × Nat)) :
    totalSymSize (l.flatMap (fun ri => loadSlot ri.1 (A ri.2))) = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.flatMap_cons, totalSymSize_append, totalSymSize_loadSlot, ih, List.length_cons]; omega

theorem totalSymSize_flatMap_storeSlot (l : List (Nat × Nat)) :
    totalSymSize (l.flatMap (fun ri => storeSlot ri.1 (A ri.2)))
      = 4 * (l.flatMap (fun ri => storeSlotI ri.1 (A ri.2))).length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.flatMap_cons, List.flatMap_cons, totalSymSize_append, totalSymSize_storeSlot,
        List.length_append, ih]; omega

/-- Straight-line op case helper: single-load ops (`addi`/`slli`/`srli`/`lbu`/`ld`). -/
theorem tss_op_load1 (rs rd : Reg) (i : Instr) (dat : Data) (bs cs : List Nat) (epi cnt : Nat)
    (op : PStmt) (hlow : (lower dat bs cs epi op cnt).1 = loadSlot rs T0 ++ [SymInstr.ins i] ++ storeSlot rd T0)
    (hcs : csize op = (loadSlotI rs T0 ++ [i] ++ storeSlotI rd T0).length) :
    totalSymSize (lower dat bs cs epi op cnt).1 = 4 * csize op := by
  rw [hlow, totalSymSize_append, totalSymSize_append, totalSymSize_loadSlot, totalSymSize_storeSlot,
      hcs]
  simp only [List.length_append, loadSlotI_length, List.length_cons, List.length_nil,
             totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil]; omega

/-- Straight-line op case helper: double-load ops (`add`/`sub`/`orr`). -/
theorem tss_op_load2 (r1 r2 rd : Reg) (i : Instr) (dat : Data) (bs cs : List Nat) (epi cnt : Nat)
    (op : PStmt)
    (hlow : (lower dat bs cs epi op cnt).1 = loadSlot r1 T0 ++ loadSlot r2 T1 ++ [SymInstr.ins i] ++ storeSlot rd T0)
    (hcs : csize op = (loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [i] ++ storeSlotI rd T0).length) :
    totalSymSize (lower dat bs cs epi op cnt).1 = 4 * csize op := by
  rw [hlow, totalSymSize_append, totalSymSize_append, totalSymSize_append, totalSymSize_loadSlot,
      totalSymSize_loadSlot, totalSymSize_storeSlot, hcs]
  simp only [List.length_append, loadSlotI_length, List.length_cons, List.length_nil,
             totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil]; omega

/-- Straight-line op case helper: stores (`sb`/`sd`). -/
theorem tss_op_store (rb rv : Reg) (i : Instr) (dat : Data) (bs cs : List Nat) (epi cnt : Nat)
    (op : PStmt)
    (hlow : (lower dat bs cs epi op cnt).1 = loadSlot rb T0 ++ loadSlot rv T1 ++ [SymInstr.ins i])
    (hcs : csize op = (loadSlotI rb T0 ++ loadSlotI rv T1 ++ [i]).length) :
    totalSymSize (lower dat bs cs epi op cnt).1 = 4 * csize op := by
  rw [hlow, totalSymSize_append, totalSymSize_append, totalSymSize_loadSlot, totalSymSize_loadSlot,
      hcs]
  simp only [List.length_append, loadSlotI_length, List.length_cons, List.length_nil,
             totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil]; omega

theorem lower_totalSymSize (dat : Data) :
    ∀ (stmt : PStmt) (bs cs : List Nat) (epi cnt : Nat),
      totalSymSize (lower dat bs cs epi stmt cnt).1 = 4 * csize stmt := by
  intro stmt
  induction stmt with
  | skip => intro bs cs epi cnt; rfl
  | annot a => intro bs cs epi cnt; rfl
  | ret => intro bs cs epi cnt; rfl
  | brkB k => intro bs cs epi cnt; rfl
  | contL k => intro bs cs epi cnt; rfl
  | addi rd rs imm => intro bs cs epi cnt; exact tss_op_load1 rs rd _ _ _ _ _ _ _ rfl rfl
  | slli rd rs sh => intro bs cs epi cnt; exact tss_op_load1 rs rd _ _ _ _ _ _ _ rfl rfl
  | srli rd rs sh => intro bs cs epi cnt; exact tss_op_load1 rs rd _ _ _ _ _ _ _ rfl rfl
  | lbu rd rs imm => intro bs cs epi cnt; exact tss_op_load1 rs rd _ _ _ _ _ _ _ rfl rfl
  | ld rd rs imm => intro bs cs epi cnt; exact tss_op_load1 rs rd _ _ _ _ _ _ _ rfl rfl
  | add rd r1 r2 => intro bs cs epi cnt; exact tss_op_load2 r1 r2 rd _ _ _ _ _ _ _ rfl rfl
  | sub rd r1 r2 => intro bs cs epi cnt; exact tss_op_load2 r1 r2 rd _ _ _ _ _ _ _ rfl rfl
  | orr rd r1 r2 => intro bs cs epi cnt; exact tss_op_load2 r1 r2 rd _ _ _ _ _ _ _ rfl rfl
  | sb rb rv imm => intro bs cs epi cnt; exact tss_op_store rb rv _ _ _ _ _ _ _ rfl rfl
  | sd rb rv imm => intro bs cs epi cnt; exact tss_op_store rb rv _ _ _ _ _ _ _ rfl rfl
  | seq a b iha ihb =>
    intro bs cs epi cnt
    rw [lower_seq, totalSymSize_append, iha, ihb]; simp only [csize]; omega
  | block body ih =>
    intro bs cs epi cnt
    rw [lower_block, totalSymSize_append, ih]; simp only [csize, totalSymSize, List.map_cons,
      List.map_nil, symSize, List.sum_cons, List.sum_nil]; omega
  | ife c a b t e iht ihe =>
    intro bs cs epi cnt
    rw [lower_ife]
    simp only [totalSymSize_append, totalSymSize_loadSlot, iht, ihe, csize]
    simp only [totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil]
    omega
  | «while» c a b body ih =>
    intro bs cs epi cnt
    rw [lower_while]
    simp only [totalSymSize_append, totalSymSize_loadSlot, ih, csize]
    simp only [totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil]
    omega
  | cref rd d =>
    intro bs cs epi cnt
    rw [lower_cref, totalSymSize_append, totalSymSize_storeSlot]
    simp only [csize, totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil,
               storeSlotI]
    by_cases h : rd = 0 <;> simp [h]
  | clen rd d =>
    intro bs cs epi cnt
    rw [lower_clen, totalSymSize_append, totalSymSize_storeSlot]
    simp only [csize, totalSymSize, synthConst, List.map_cons, List.map_nil, symSize, List.sum_cons,
               List.sum_nil, storeSlotI]
    by_cases h : rd = 0 <;> simp [h]
  | call argc rvc f args rets =>
    intro bs cs epi cnt
    show totalSymSize ((args.toList.zipIdx.flatMap (fun ri => loadSlot ri.1 (A ri.2)))
      ++ [SymInstr.callf f] ++ (rets.toList.zipIdx.flatMap (fun ri => storeSlot ri.1 (A ri.2)))) = _
    rw [totalSymSize_append, totalSymSize_append, totalSymSize_flatMap_loadSlot,
        totalSymSize_flatMap_storeSlot]
    simp only [csize, totalSymSize, List.map_cons, List.map_nil, symSize, List.sum_cons, List.sum_nil,
               List.length_zipIdx, retStoresI]
    omega

end LowIR.ProgSim.LowerFacts
