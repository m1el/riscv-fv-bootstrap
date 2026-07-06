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
  - Layer 3 (`lower_resolve`): the correspondence induction itself — resolving the
    laid-out symbolic body stream equals `emitCF` at the same position. It threads
    `LEnvOk` (enclosing brk/cont/epilogue labels), `LblConsistent` (internal labels),
    and `TabOk` (the data/function tables), and reads each jump/branch's resolved
    offset off the layout positions pinned by `lower_totalSymSize`. Axiom-clean
    (`[propext, Quot.sound]`). This is the crux of `hfn`/`hem` (the per-function
    `Emitted` correspondence); the remaining glue is the `layout`-flatten position
    arithmetic tying `fnPos g` to the resolved-stream slice.
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

/-! # Layer 3 — the `lower`↔`emitCF` correspondence induction `lower_resolve`.

    The crux: resolving (`resolveOne`) the compiler's laid-out symbolic body stream
    equals `emitCF` at the same byte position. The induction threads three
    consistency relations — `LEnvOk` (enclosing brk/cont/epilogue labels resolve to
    their positions), `LblConsistent` (every internal label of the stream resolves
    to its layout position), and `TabOk` (the data/function tables agree with
    `dpos`/`fnPos`) — and reads each jump/branch's resolved offset off the layout
    positions pinned by `lower_totalSymSize`. -/

open LowIR.Prog (Program Stmt)

/-! ## Consistency predicates threaded by the induction. -/

/-- The enclosing brk/cont label stacks and the epilogue label resolve (in `lbls`)
    to their claimed byte positions `bp`/`cp`/`ep`. -/
def LEnvOk (lbls : List (Nat × Nat)) (bs cs : List Nat) (epi : Nat)
    (bp cp : List Nat) (ep : Nat) : Prop :=
  List.lookup epi lbls = some ep
  ∧ bs.length = bp.length ∧ cs.length = cp.length
  ∧ (∀ k, k < bs.length → List.lookup (bs.getD k 0) lbls = some (bp.getD k 0))
  ∧ (∀ k, k < cs.length → List.lookup (cs.getD k 0) lbls = some (cp.getD k 0))

/-- Every internal label of a lowered stream resolves in `lbls` to its layout position. -/
def LblConsistent (lbls : List (Nat × Nat)) (locl : List (Nat × Nat)) : Prop :=
  ∀ l p, (l, p) ∈ locl → List.lookup l lbls = some p

/-- The data/function offset tables agree with the `dpos`/`fnPos` used by `emitCF`. -/
def TabOk (dpos fnPos : Name → Nat) (fns : List (Name × Nat)) (dats : List (Name × Nat)) : Prop :=
  (∀ d off, List.lookup d dats = some off → off = dpos d)
  ∧ (∀ f p, List.lookup f fns = some p → p = fnPos f)

theorem LblConsistent_append_left {lbls} {A B : List (Nat × Nat)}
    (h : LblConsistent lbls (A ++ B)) : LblConsistent lbls A :=
  fun l p hm => h l p (List.mem_append_left B hm)

theorem LblConsistent_append_right {lbls} {A B : List (Nat × Nat)}
    (h : LblConsistent lbls (A ++ B)) : LblConsistent lbls B :=
  fun l p hm => h l p (List.mem_append_right A hm)

/-! ## `resolveOne` on the three position-dependent singletons. -/

theorem resolveOne_jmp_eq (lbls fns dats : List _) (pos l tgt : Nat) (r : List Instr)
    (hlk : List.lookup l lbls = some tgt)
    (h : resolveOne lbls fns dats (pos, SymInstr.jmp l) = some r) :
    r = [jal0 ((tgt : Int) - (pos : Int))] := by
  simp only [resolveOne, hlk, bind, Option.bind] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

theorem resolveOne_br_eq (lbls fns dats : List _) (pos tgt : Nat) (c : Cond) (a b l : Nat)
    (r : List Instr) (hlk : List.lookup l lbls = some tgt)
    (h : resolveOne lbls fns dats (pos, SymInstr.br c a b l) = some r) :
    r = [condInstr c a b ((tgt : Int) - (pos : Int))] := by
  simp only [resolveOne, hlk, bind, Option.bind] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

theorem resolveOne_cref_eq (lbls fns dats : List _) (pos : Nat) (d : Name) (off : Nat)
    (r : List Instr) (hlk : List.lookup d dats = some off)
    (h : resolveOne lbls fns dats (pos, SymInstr.cref d) = some r) :
    r = crefI T0 T1 ((off : Int) - ((pos : Int) + 4)) := by
  simp only [resolveOne, hlk, bind, Option.bind] at h
  split at h
  · rw [← Option.some.inj h]; rfl
  · exact absurd h (by simp)

theorem resolveOne_callf_eq (lbls fns dats : List _) (pos : Nat) (f : Name) (tgt : Nat)
    (r : List Instr) (hlk : List.lookup f fns = some tgt)
    (h : resolveOne lbls fns dats (pos, SymInstr.callf f) = some r) :
    r = [Instr.jal RA (BitVec.ofInt 21 ((tgt : Int) - (pos : Int)))] := by
  simp only [resolveOne, hlk, bind, Option.bind] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

/-! ## The all-`.ins`/`.label` payoff: resolve-flatten = `flatMap insUnwrap`. -/

/-- For an all-`.ins`/`.label` symbolic stream, resolving and flattening gives the
    `insUnwrap`-flattened list — which the caller equates to the emitted target. -/
theorem allins_resolve (lbls fns dats : List _) (sym : List SymInstr) (here : Nat)
    (r : List (List Instr)) (target : List Instr)
    (hall : sym.all isInsOrLabel = true)
    (hunw : sym.flatMap insUnwrap = target)
    (h : (layoutItems sym here).1.mapM (resolveOne lbls fns dats) = some r) :
    r.flatten = target := by
  rw [resolve_ins_mapM lbls fns dats sym here hall, Option.some.injEq] at h
  rw [← h, ← List.flatMap_def, hunw]

/-! ## Resolving a single positioned symbolic item. -/

/-- `layoutItems` of a singleton is `[(pos, si)]` (labels included). -/
theorem layoutItems_singleton (si : SymInstr) (pos : Nat) :
    (layoutItems [si] pos).1 = [(pos, si)] := by
  cases si <;> simp [layoutItems]

/-- Resolving a laid-out singleton flattens to its one resolved instruction list,
    characterized by `hval` (fed the `resolveOne_*_eq` lemmas). -/
theorem resolve_singleton_flatten (lbls fns dats : List _) (si : SymInstr) (pos : Nat)
    (r : List (List Instr)) (v : List Instr)
    (hval : ∀ v', resolveOne lbls fns dats (pos, si) = some v' → v' = v)
    (h : (layoutItems [si] pos).1.mapM (resolveOne lbls fns dats) = some r) :
    r.flatten = v := by
  rw [layoutItems_singleton, List.mapM_cons, List.mapM_nil] at h
  cases hv : resolveOne lbls fns dats (pos, si) with
  | none => rw [hv] at h; simp at h
  | some v' =>
    rw [hv] at h
    simp only [bind, Option.bind, pure, Option.some.injEq] at h
    rw [← h, List.flatten_cons, List.flatten_nil, List.append_nil, hval v' hv]

/-! ## Straight-line op shapes: all-`.ins`, `flatMap insUnwrap = emit`. -/

theorem allins_load1 (rs rd : Reg) (i : Instr) :
    (loadSlot rs T0 ++ [SymInstr.ins i] ++ storeSlot rd T0).all isInsOrLabel = true := by
  simp [List.all_append, loadSlot_all_ins, storeSlot_all_ins, isInsOrLabel]

theorem unwrap_load1 (rs rd : Reg) (i : Instr) :
    (loadSlot rs T0 ++ [SymInstr.ins i] ++ storeSlot rd T0).flatMap insUnwrap
      = loadSlotI rs T0 ++ [i] ++ storeSlotI rd T0 := by
  rw [insUnwrap_flatMap_append, insUnwrap_flatMap_append, loadSlot_unwrap, storeSlot_unwrap]
  simp only [List.flatMap_cons, List.flatMap_nil, insUnwrap, List.append_nil]

theorem allins_load2 (r1 r2 rd : Reg) (i : Instr) :
    (loadSlot r1 T0 ++ loadSlot r2 T1 ++ [SymInstr.ins i] ++ storeSlot rd T0).all isInsOrLabel = true := by
  simp [List.all_append, loadSlot_all_ins, storeSlot_all_ins, isInsOrLabel]

theorem unwrap_load2 (r1 r2 rd : Reg) (i : Instr) :
    (loadSlot r1 T0 ++ loadSlot r2 T1 ++ [SymInstr.ins i] ++ storeSlot rd T0).flatMap insUnwrap
      = loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [i] ++ storeSlotI rd T0 := by
  rw [insUnwrap_flatMap_append, insUnwrap_flatMap_append, insUnwrap_flatMap_append,
      loadSlot_unwrap, loadSlot_unwrap, storeSlot_unwrap]
  simp only [List.flatMap_cons, List.flatMap_nil, insUnwrap, List.append_nil]

theorem allins_store (rb rv : Reg) (i : Instr) :
    (loadSlot rb T0 ++ loadSlot rv T1 ++ [SymInstr.ins i]).all isInsOrLabel = true := by
  simp [List.all_append, loadSlot_all_ins, isInsOrLabel]

theorem unwrap_store (rb rv : Reg) (i : Instr) :
    (loadSlot rb T0 ++ loadSlot rv T1 ++ [SymInstr.ins i]).flatMap insUnwrap
      = loadSlotI rb T0 ++ loadSlotI rv T1 ++ [i] := by
  rw [insUnwrap_flatMap_append, insUnwrap_flatMap_append, loadSlot_unwrap, loadSlot_unwrap]
  simp only [List.flatMap_cons, List.flatMap_nil, insUnwrap, List.append_nil]

theorem allins_synthConst (t : Reg) (v : Int) : (synthConst t v).all isInsOrLabel = true := by
  simp [synthConst, isInsOrLabel]

theorem unwrap_synthConst (t : Reg) (v : Int) : (synthConst t v).flatMap insUnwrap = synthI t v := by
  simp only [synthConst, synthI, synthHi, synthLo, List.flatMap_cons, List.flatMap_nil, insUnwrap,
    List.append_nil, List.cons_append, List.nil_append]

/-! ## Locating internal labels: membership of a `.label` marker in `layoutItems`. -/

/-- The label list of a leading `.label l` marker records `(l, pos)` up front. -/
theorem layoutItems_label_head (l : Nat) (Y : List SymInstr) (pos : Nat) :
    (layoutItems (SymInstr.label l :: Y) pos).2.1 = (l, pos) :: (layoutItems Y pos).2.1 := by
  simp only [layoutItems]

/-! ## Cref/callf lookup existence from a successful resolve. -/

theorem resolveOne_cref_lookup (lbls fns dats : List _) (pos : Nat) (d : Name) (v : List Instr)
    (h : resolveOne lbls fns dats (pos, SymInstr.cref d) = some v) :
    ∃ off, List.lookup d dats = some off := by
  cases hd : List.lookup d dats with
  | none => rw [show resolveOne lbls fns dats (pos, SymInstr.cref d)
                    = (List.lookup d dats).bind _ from rfl, hd] at h; simp at h
  | some off => exact ⟨off, rfl⟩

theorem resolveOne_callf_lookup (lbls fns dats : List _) (pos : Nat) (f : Name) (v : List Instr)
    (h : resolveOne lbls fns dats (pos, SymInstr.callf f) = some v) :
    ∃ tgt, List.lookup f fns = some tgt := by
  cases hf : List.lookup f fns with
  | none => rw [show resolveOne lbls fns dats (pos, SymInstr.callf f)
                    = (List.lookup f fns).bind _ from rfl, hf] at h; simp at h
  | some tgt => exact ⟨tgt, rfl⟩

/-! ## Extending `LEnvOk` when entering a `block`/`while` body. -/

theorem LEnvOk_push_brk (lbls : List (Nat × Nat)) (bs cs : List Nat) (epi : Nat)
    (bp cp : List Nat) (ep cnt bpos : Nat)
    (h : LEnvOk lbls bs cs epi bp cp ep) (hcnt : List.lookup cnt lbls = some bpos) :
    LEnvOk lbls (cnt :: bs) cs epi (bpos :: bp) cp ep := by
  obtain ⟨he, hbl, hcl, hb, hc⟩ := h
  refine ⟨he, by simp [hbl], hcl, ?_, hc⟩
  intro k hk
  cases k with
  | zero => simpa using hcnt
  | succ k' => simpa using hb k' (by simpa using hk)

theorem LEnvOk_push_cont (lbls : List (Nat × Nat)) (bs cs : List Nat) (epi : Nat)
    (bp cp : List Nat) (ep cnt cpos : Nat)
    (h : LEnvOk lbls bs cs epi bp cp ep) (hcnt : List.lookup cnt lbls = some cpos) :
    LEnvOk lbls bs (cnt :: cs) epi bp (cpos :: cp) ep := by
  obtain ⟨he, hbl, hcl, hb, hc⟩ := h
  refine ⟨he, hbl, by simp [hcl], hb, ?_⟩
  intro k hk
  cases k with
  | zero => simpa using hcnt
  | succ k' => simpa using hc k' (by simpa using hk)

/-- Split BOTH the resolve and the label-consistency of a stream append at once —
    the peeling primitive for the compound cases. -/
theorem split2 (lbls fns dats : List _) (A B : List SymInstr) (here : Nat)
    (r : List (List Instr))
    (h : (layoutItems (A ++ B) here).1.mapM (resolveOne lbls fns dats) = some r)
    (hlbl : LblConsistent lbls (layoutItems (A ++ B) here).2.1) :
    ∃ ra rb, (layoutItems A here).1.mapM (resolveOne lbls fns dats) = some ra
      ∧ (layoutItems B (here + totalSymSize A)).1.mapM (resolveOne lbls fns dats) = some rb
      ∧ r.flatten = ra.flatten ++ rb.flatten
      ∧ LblConsistent lbls (layoutItems A here).2.1
      ∧ LblConsistent lbls (layoutItems B (here + totalSymSize A)).2.1 := by
  obtain ⟨ra, rb, hra, hrb, hr⟩ := resolve_flatten_append lbls fns dats A B here r h
  rw [(layoutItems_append A B here).2] at hlbl
  exact ⟨ra, rb, hra, hrb, hr, LblConsistent_append_left hlbl, LblConsistent_append_right hlbl⟩

/-- A lone `.label l` piece resolves its label to its byte position. -/
theorem lblLookup_singleton (lbls : List (Nat × Nat)) (l pos : Nat)
    (h : LblConsistent lbls (layoutItems [SymInstr.label l] pos).2.1) :
    List.lookup l lbls = some pos := by
  rw [layoutItems_label_head] at h
  exact h l pos (List.mem_cons_self ..)

/-- A `[.jmp l', .label l]` piece records its label at `pos + 4` (after the jmp). -/
theorem layoutItems_jmplabel (l' l pos : Nat) :
    (layoutItems [SymInstr.jmp l', SymInstr.label l] pos).2.1 = [(l, pos + 4)] := by
  simp [layoutItems, symSize]

theorem lblLookup_jmplabel (lbls : List (Nat × Nat)) (l' l pos : Nat)
    (h : LblConsistent lbls (layoutItems [SymInstr.jmp l', SymInstr.label l] pos).2.1) :
    List.lookup l lbls = some (pos + 4) := by
  rw [layoutItems_jmplabel] at h
  exact h l (pos + 4) (List.mem_cons_self ..)

/-- A `[.jmp l', .label l]` piece resolves+flattens to the single `jal0` to `l'`'s
    target (the trailing 0-byte label emits nothing). -/
theorem resolve_jmplabel_flatten (lbls fns dats : List _) (l' l pos tgt : Nat)
    (r : List (List Instr)) (hlk : List.lookup l' lbls = some tgt)
    (h : (layoutItems [SymInstr.jmp l', SymInstr.label l] pos).1.mapM (resolveOne lbls fns dats)
          = some r) :
    r.flatten = [jal0 ((tgt : Int) - (pos : Int))] := by
  rw [show [SymInstr.jmp l', SymInstr.label l] = [SymInstr.jmp l'] ++ [SymInstr.label l] from rfl] at h
  obtain ⟨rj, rlab, hj, hlab, hf⟩ := resolve_flatten_append lbls fns dats _ _ pos r h
  have hrj : rj.flatten = [jal0 ((tgt : Int) - (pos : Int))] :=
    resolve_singleton_flatten lbls fns dats (SymInstr.jmp l') pos rj _
      (fun v' h' => resolveOne_jmp_eq lbls fns dats pos l' tgt v' hlk h') hj
  have hrlab : rlab.flatten = [] :=
    allins_resolve lbls fns dats _ _ rlab _ (by simp [isInsOrLabel]) (by simp [insUnwrap]) hlab
  rw [hf, hrj, hrlab, List.append_nil]

/-- A `[.br c T0 T1 lB, .jmp lE]` piece (the while-guard test) resolves to the
    conditional branch to `lB` and the exit jump to `lE`. -/
theorem resolve_brjmp (lbls fns dats : List _) (c : Cond) (lB lE pos tgtB tgtE : Nat)
    (r : List (List Instr)) (hlkB : List.lookup lB lbls = some tgtB)
    (hlkE : List.lookup lE lbls = some tgtE)
    (h : (layoutItems [SymInstr.br c T0 T1 lB, SymInstr.jmp lE] pos).1.mapM (resolveOne lbls fns dats)
          = some r) :
    r.flatten = [condInstr c T0 T1 ((tgtB : Int) - (pos : Int)),
                 jal0 ((tgtE : Int) - ((pos : Int) + 4))] := by
  rw [show [SymInstr.br c T0 T1 lB, SymInstr.jmp lE]
        = [SymInstr.br c T0 T1 lB] ++ [SymInstr.jmp lE] from rfl] at h
  obtain ⟨rb, rj, hb, hj, hf⟩ := resolve_flatten_append lbls fns dats _ _ pos r h
  have hrb : rb.flatten = [condInstr c T0 T1 ((tgtB : Int) - (pos : Int))] :=
    resolve_singleton_flatten lbls fns dats (SymInstr.br c T0 T1 lB) pos rb _
      (fun v' h' => resolveOne_br_eq lbls fns dats pos tgtB c T0 T1 lB v' hlkB h') hb
  rw [show totalSymSize [SymInstr.br c T0 T1 lB] = 4 from rfl] at hj
  have hrj : rj.flatten = [jal0 ((tgtE : Int) - ((pos + 4 : Nat) : Int))] :=
    resolve_singleton_flatten lbls fns dats (SymInstr.jmp lE) (pos + 4) rj _
      (fun v' h' => resolveOne_jmp_eq lbls fns dats (pos + 4) lE tgtE v' hlkE h') hj
  have hcast : ((pos + 4 : Nat) : Int) = (pos : Int) + 4 := by push_cast; omega
  rw [hf, hrb, hrj, hcast, List.singleton_append]

/-- The while-mid piece `[.br c T0 T1 lB, .jmp lE, .label lB]`: the conditional
    branch (offset 8 to its own trailing label `lB`) and the exit jump to `lE`. -/
theorem layoutItems_brjmplabel (c : Cond) (lB lE pos : Nat) :
    (layoutItems [SymInstr.br c T0 T1 lB, SymInstr.jmp lE, SymInstr.label lB] pos).2.1
      = [(lB, pos + 8)] := by
  simp [layoutItems, symSize]

theorem resolve_brjmplabel (lbls fns dats : List _) (c : Cond) (lB lE pos tgtE : Nat)
    (r : List (List Instr)) (hlkB : List.lookup lB lbls = some (pos + 8))
    (hlkE : List.lookup lE lbls = some tgtE)
    (h : (layoutItems [SymInstr.br c T0 T1 lB, SymInstr.jmp lE, SymInstr.label lB] pos).1.mapM
          (resolveOne lbls fns dats) = some r) :
    r.flatten = [condInstr c T0 T1 8, jal0 ((tgtE : Int) - ((pos : Int) + 4))] := by
  rw [show [SymInstr.br c T0 T1 lB, SymInstr.jmp lE, SymInstr.label lB]
        = [SymInstr.br c T0 T1 lB, SymInstr.jmp lE] ++ [SymInstr.label lB] from rfl] at h
  obtain ⟨rbj, rlab, hbj, hlab, hf⟩ := resolve_flatten_append lbls fns dats _ _ pos r h
  have hrbj := resolve_brjmp lbls fns dats c lB lE pos (pos + 8) tgtE rbj hlkB hlkE hbj
  have hrlab : rlab.flatten = [] :=
    allins_resolve lbls fns dats _ _ rlab _ (by simp [isInsOrLabel]) (by simp [insUnwrap]) hlab
  have hc8 : ((pos + 8 : Nat) : Int) - (pos : Int) = 8 := by push_cast; omega
  rw [hf, hrbj, hrlab, List.append_nil, hc8]

/-! ## The correspondence induction. -/

set_option maxHeartbeats 800000 in
/-- **Layer 3 — the `lower`↔`emitCF` correspondence.** Resolving the compiler's
    laid-out symbolic body stream (at any byte position `here`, under a consistent
    label environment) flattens to exactly `emitCF` at that position. Structural
    induction on `stmt`; each jump/branch reads its offset off the layout positions
    pinned by `lower_totalSymSize`. -/
theorem lower_resolve (dat : Data) (P : Program) (dpos fnPos : Name → Nat)
    (lbls : List (Nat × Nat)) (fns dats : List (Name × Nat))
    (htab : TabOk dpos fnPos fns dats) :
    ∀ (stmt : PStmt) (bs cs : List Nat) (epi cnt here : Nat) (bp cp : List Nat) (ep : Nat)
      (r : List (List Instr)),
      (layoutItems (lower dat bs cs epi stmt cnt).1 here).1.mapM (resolveOne lbls fns dats) = some r →
      LowIR.Prog.wf P bs.length cs.length stmt = true →
      LEnvOk lbls bs cs epi bp cp ep →
      LblConsistent lbls (layoutItems (lower dat bs cs epi stmt cnt).1 here).2.1 →
      r.flatten = emitCF dat dpos fnPos bp cp ep here stmt := by
  intro stmt
  induction stmt with
  | skip =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (by rfl) (by rfl) h
  | annot a =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (by rfl) (by rfl) h
  | addi rd rs imm =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load1 rs rd _) (unwrap_load1 rs rd _) h
  | slli rd rs sh =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load1 rs rd _) (unwrap_load1 rs rd _) h
  | srli rd rs sh =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load1 rs rd _) (unwrap_load1 rs rd _) h
  | lbu rd rs imm =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load1 rs rd _) (unwrap_load1 rs rd _) h
  | ld rd rs imm =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load1 rs rd _) (unwrap_load1 rs rd _) h
  | add rd r1 r2 =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load2 r1 r2 rd _) (unwrap_load2 r1 r2 rd _) h
  | sub rd r1 r2 =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load2 r1 r2 rd _) (unwrap_load2 r1 r2 rd _) h
  | orr rd r1 r2 =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_load2 r1 r2 rd _) (unwrap_load2 r1 r2 rd _) h
  | sb rb rv imm =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_store rb rv _) (unwrap_store rb rv _) h
  | sd rb rv imm =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      exact allins_resolve lbls fns dats _ here r _ (allins_store rb rv _) (unwrap_store rb rv _) h
  | ret =>
      intro bs cs epi cnt here bp cp ep r h _ hlenv _
      rw [lower_ret] at h
      show r.flatten = [jal0 ((ep : Int) - (here : Int))]
      exact resolve_singleton_flatten lbls fns dats (SymInstr.jmp epi) here r _
        (fun v' h' => resolveOne_jmp_eq lbls fns dats here epi ep v' hlenv.1 h') h
  | brkB k =>
      intro bs cs epi cnt here bp cp ep r h hwf hlenv _
      rw [lower_brkB] at h
      have hklt : k < bs.length := by simpa only [LowIR.Prog.wf, decide_eq_true_eq] using hwf
      have hlk := hlenv.2.2.2.1 k hklt
      show r.flatten = [jal0 ((bp.getD k 0 : Int) - (here : Int))]
      exact resolve_singleton_flatten lbls fns dats (SymInstr.jmp (bs.getD k 0)) here r _
        (fun v' h' => resolveOne_jmp_eq lbls fns dats here (bs.getD k 0) (bp.getD k 0) v' hlk h') h
  | contL k =>
      intro bs cs epi cnt here bp cp ep r h hwf hlenv _
      rw [lower_contL] at h
      have hklt : k < cs.length := by simpa only [LowIR.Prog.wf, decide_eq_true_eq] using hwf
      have hlk := hlenv.2.2.2.2 k hklt
      show r.flatten = [jal0 ((cp.getD k 0 : Int) - (here : Int))]
      exact resolve_singleton_flatten lbls fns dats (SymInstr.jmp (cs.getD k 0)) here r _
        (fun v' h' => resolveOne_jmp_eq lbls fns dats here (cs.getD k 0) (cp.getD k 0) v' hlk h') h
  | clen rd d =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      rw [lower_clen] at h
      refine allins_resolve lbls fns dats _ here r _ ?_ ?_ h
      · simp [List.all_append, allins_synthConst, storeSlot_all_ins]
      · rw [insUnwrap_flatMap_append, unwrap_synthConst, storeSlot_unwrap]; rfl
  | cref rd d =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      rw [lower_cref] at h
      obtain ⟨rc, rs, hc, hs, hflat⟩ :=
        resolve_flatten_append lbls fns dats [SymInstr.cref d] (storeSlot rd T0) here r h
      have hrc : rc.flatten = crefI T0 T1 ((dpos d : Int) - ((here : Int) + 4)) := by
        refine resolve_singleton_flatten lbls fns dats (SymInstr.cref d) here rc _ ?_ hc
        intro v' h'
        obtain ⟨off, hoff⟩ := resolveOne_cref_lookup lbls fns dats here d v' h'
        rw [resolveOne_cref_eq lbls fns dats here d off v' hoff h', htab.1 d off hoff]
      have hrs : rs.flatten = storeSlotI rd T0 :=
        allins_resolve lbls fns dats _ _ rs _ (storeSlot_all_ins rd T0) (storeSlot_unwrap rd T0) hs
      rw [hflat, hrc, hrs]; rfl
  | seq a b iha ihb =>
      intro bs cs epi cnt here bp cp ep r h hwf hlenv hlbl
      rw [lower_seq] at h hlbl
      obtain ⟨ra, rb, ha, hb, hflat⟩ := resolve_flatten_append lbls fns dats _ _ _ _ h
      rw [lower_totalSymSize] at hb
      rw [(layoutItems_append _ _ _).2, lower_totalSymSize] at hlbl
      simp only [LowIR.Prog.wf, Bool.and_eq_true] at hwf
      show r.flatten
        = emitCF dat dpos fnPos bp cp ep here a
          ++ emitCF dat dpos fnPos bp cp ep (here + 4 * csize a) b
      rw [hflat]
      congr 1
      · exact iha bs cs epi cnt here bp cp ep ra ha hwf.1 hlenv (LblConsistent_append_left hlbl)
      · exact ihb bs cs epi _ (here + 4 * csize a) bp cp ep rb hb hwf.2 hlenv
          (LblConsistent_append_right hlbl)
  | block body ih =>
      intro bs cs epi cnt here bp cp ep r h hwf hlenv hlbl
      rw [lower_block] at h hlbl
      obtain ⟨rbody, rlab, hbody, hlab, hflat⟩ := resolve_flatten_append lbls fns dats _ _ _ _ h
      rw [lower_totalSymSize] at hlab
      rw [(layoutItems_append _ _ _).2, lower_totalSymSize] at hlbl
      have hcnt : List.lookup cnt lbls = some (here + 4 * csize body) :=
        (LblConsistent_append_right hlbl) cnt _ (by rw [layoutItems_label_head]; exact List.mem_cons_self ..)
      simp only [LowIR.Prog.wf] at hwf
      show r.flatten = emitCF dat dpos fnPos ((here + 4 * csize body) :: bp) cp ep here body
      have hlab' : rlab.flatten = [] :=
        allins_resolve lbls fns dats _ _ rlab _ (by simp [isInsOrLabel]) (by simp [insUnwrap]) hlab
      rw [hflat, hlab', List.append_nil]
      exact ih (cnt :: bs) cs epi (cnt + 1) here ((here + 4 * csize body) :: bp) cp ep rbody hbody
        (by simpa using hwf)
        (LEnvOk_push_brk lbls bs cs epi bp cp ep cnt (here + 4 * csize body) hlenv hcnt)
        (LblConsistent_append_left hlbl)
  | ife c a b t e iht ihe =>
      intro bs cs epi cnt here bp cp ep r h hwf hlenv hlbl
      rw [lower_ife] at h hlbl
      simp only [LowIR.Prog.wf, Bool.and_eq_true] at hwf
      -- the position-bridge sizes for the two sub-bodies
      have he : totalSymSize (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).1
          = 4 * csize e := lower_totalSymSize dat e bs cs epi _
      have ht : totalSymSize (lower dat bs cs epi t (cnt + 2)).1
          = 4 * csize t := lower_totalSymSize dat t bs cs epi _
      -- peel the 6 pieces from the right (G1 = the two head slot-loads, grouped)
      obtain ⟨rp5, rG6, hp5, hG6, hf6, lp5, lG6⟩ :=
        split2 lbls fns dats _ [SymInstr.label (cnt + 1)] here r h hlbl
      obtain ⟨rp4, rG5, hp4, hG5, hf5, lp4, lG5⟩ :=
        split2 lbls fns dats _ (lower dat bs cs epi t (cnt + 2)).1 here rp5 hp5 lp5
      obtain ⟨rp3, rG4, hp3, hG4, hf4, lp3, lG4⟩ :=
        split2 lbls fns dats _ [SymInstr.jmp (cnt + 1), SymInstr.label cnt] here rp4 hp4 lp4
      obtain ⟨rp2, rG3, hp2, hG3, hf3, lp2, lG3⟩ :=
        split2 lbls fns dats _ (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).1 here rp3 hp3 lp3
      obtain ⟨rG1, rG2, hG1, hG2, hf2, lG1, lG2⟩ :=
        split2 lbls fns dats _ [SymInstr.br c T0 T1 cnt] here rp2 hp2 lp2
      -- normalize the piece positions
      have s1 : totalSymSize (loadSlot a T0 ++ loadSlot b T1) = 8 := by
        rw [totalSymSize_append, totalSymSize_loadSlot, totalSymSize_loadSlot]
      have s2 : totalSymSize (loadSlot a T0 ++ loadSlot b T1 ++ [SymInstr.br c T0 T1 cnt]) = 12 := by
        simp [totalSymSize_append, totalSymSize_loadSlot, symSize]
      have s3 : totalSymSize (loadSlot a T0 ++ loadSlot b T1 ++ [SymInstr.br c T0 T1 cnt]
                  ++ (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).1) = 12 + 4 * csize e := by
        simp [totalSymSize_append, totalSymSize_loadSlot, symSize, he]; omega
      have s4 : totalSymSize (loadSlot a T0 ++ loadSlot b T1 ++ [SymInstr.br c T0 T1 cnt]
                  ++ (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).1
                  ++ [SymInstr.jmp (cnt + 1), SymInstr.label cnt]) = 16 + 4 * csize e := by
        simp [totalSymSize_append, totalSymSize_loadSlot, symSize, he]; omega
      have s5 : totalSymSize (loadSlot a T0 ++ loadSlot b T1 ++ [SymInstr.br c T0 T1 cnt]
                  ++ (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).1
                  ++ [SymInstr.jmp (cnt + 1), SymInstr.label cnt]
                  ++ (lower dat bs cs epi t (cnt + 2)).1) = 16 + 4 * csize e + 4 * csize t := by
        simp [totalSymSize_append, totalSymSize_loadSlot, symSize, he, ht]; omega
      rw [s1] at hG2 lG2
      rw [s2] at hG3 lG3
      rw [s3] at hG4 lG4
      rw [s4] at hG5 lG5
      rw [s5] at hG6 lG6
      simp only [← Nat.add_assoc] at hG4 lG4 hG5 lG5 hG6 lG6
      -- the two internal-label lookups
      have hcnt : List.lookup cnt lbls = some (here + 16 + 4 * csize e) := by
        have := lblLookup_jmplabel lbls (cnt + 1) cnt (here + 12 + 4 * csize e) lG4
        rwa [show here + 12 + 4 * csize e + 4 = here + 16 + 4 * csize e by omega] at this
      have hcnt1 : List.lookup (cnt + 1) lbls = some (here + 16 + 4 * csize e + 4 * csize t) :=
        lblLookup_singleton lbls (cnt + 1) _ lG6
      -- each piece's flatten
      have fG1 : rG1.flatten = loadSlotI a T0 ++ loadSlotI b T1 :=
        allins_resolve lbls fns dats _ _ rG1 _
          (by simp [List.all_append, loadSlot_all_ins])
          (by rw [insUnwrap_flatMap_append, loadSlot_unwrap, loadSlot_unwrap]) hG1
      have fG2 : rG2.flatten = [condInstr c T0 T1 (8 + 4 * (csize e : Int))] := by
        have hbr := resolve_singleton_flatten lbls fns dats (SymInstr.br c T0 T1 cnt) (here + 8) rG2 _
          (fun v' h' => resolveOne_br_eq lbls fns dats (here + 8) (here + 16 + 4 * csize e)
            c T0 T1 cnt v' hcnt h') hG2
        rw [hbr]; congr 2; push_cast; omega
      have fG3 : rG3.flatten = emitCF dat dpos fnPos bp cp ep (here + 12) e :=
        ihe bs cs epi _ (here + 12) bp cp ep rG3 hG3 hwf.2 hlenv lG3
      have fG4 : rG4.flatten = [jal0 (4 + 4 * (csize t : Int))] := by
        have hj := resolve_jmplabel_flatten lbls fns dats (cnt + 1) cnt (here + 12 + 4 * csize e)
          (here + 16 + 4 * csize e + 4 * csize t) rG4 hcnt1 hG4
        rw [hj]; congr 2; push_cast; omega
      have fG5 : rG5.flatten = emitCF dat dpos fnPos bp cp ep (here + 16 + 4 * csize e) t :=
        iht bs cs epi _ (here + 16 + 4 * csize e) bp cp ep rG5 hG5 hwf.1 hlenv lG5
      have fG6 : rG6.flatten = [] :=
        allins_resolve lbls fns dats _ _ rG6 _ (by simp [isInsOrLabel]) (by simp [insUnwrap]) hG6
      -- assemble
      rw [hf6, hf5, hf4, hf3, hf2, fG1, fG2, fG3, fG4, fG5, fG6]
      show _ = loadSlotI a T0 ++ loadSlotI b T1 ++ [condInstr c T0 T1 (8 + 4 * (csize e : Int))]
        ++ emitCF dat dpos fnPos bp cp ep (here + 12) e ++ [jal0 (4 + 4 * (csize t : Int))]
        ++ emitCF dat dpos fnPos bp cp ep (here + 16 + 4 * csize e) t
      simp [List.append_assoc]
  | «while» c a b body ih =>
      intro bs cs epi cnt here bp cp ep r h hwf hlenv hlbl
      rw [lower_while] at h hlbl
      simp only [LowIR.Prog.wf] at hwf
      have hb : totalSymSize (lower dat bs (cnt :: cs) epi body (cnt + 3)).1
          = 4 * csize body := lower_totalSymSize dat body bs (cnt :: cs) epi _
      -- pieces: V1 [.label cnt] · V2 loadSlot a · V3 loadSlot b ·
      --         V4 [.br,.jmp,.label(cnt+1)] · V5 body · V6 [.jmp cnt,.label(cnt+2)]
      obtain ⟨rp5, rV6, hp5, hV6, hf6, lp5, lV6⟩ :=
        split2 lbls fns dats _ [SymInstr.jmp cnt, SymInstr.label (cnt + 2)] here r h hlbl
      obtain ⟨rp4, rV5, hp4, hV5, hf5, lp4, lV5⟩ :=
        split2 lbls fns dats _ (lower dat bs (cnt :: cs) epi body (cnt + 3)).1 here rp5 hp5 lp5
      obtain ⟨rp3, rV4, hp3, hV4, hf4, lp3, lV4⟩ :=
        split2 lbls fns dats _
          [SymInstr.br c T0 T1 (cnt + 1), SymInstr.jmp (cnt + 2), SymInstr.label (cnt + 1)]
          here rp4 hp4 lp4
      obtain ⟨rp2, rV3, hp2, hV3, hf3, lp2, lV3⟩ :=
        split2 lbls fns dats _ (loadSlot b T1) here rp3 hp3 lp3
      obtain ⟨rV1, rV2, hV1, hV2, hf2, lV1, lV2⟩ :=
        split2 lbls fns dats _ (loadSlot a T0) here rp2 hp2 lp2
      -- normalize piece positions
      have s1 : totalSymSize [SymInstr.label cnt] = 0 := rfl
      have s2 : totalSymSize ([SymInstr.label cnt] ++ loadSlot a T0) = 4 := by
        simp [totalSymSize_loadSlot, symSize]
      have s3 : totalSymSize ([SymInstr.label cnt] ++ loadSlot a T0 ++ loadSlot b T1) = 8 := by
        simp [totalSymSize_append, totalSymSize_loadSlot, symSize]
      have s4 : totalSymSize ([SymInstr.label cnt] ++ loadSlot a T0 ++ loadSlot b T1
                  ++ [SymInstr.br c T0 T1 (cnt + 1), SymInstr.jmp (cnt + 2), SymInstr.label (cnt + 1)])
                  = 16 := by
        simp [totalSymSize_append, totalSymSize_loadSlot, symSize]
      have s5 : totalSymSize ([SymInstr.label cnt] ++ loadSlot a T0 ++ loadSlot b T1
                  ++ [SymInstr.br c T0 T1 (cnt + 1), SymInstr.jmp (cnt + 2), SymInstr.label (cnt + 1)]
                  ++ (lower dat bs (cnt :: cs) epi body (cnt + 3)).1) = 16 + 4 * csize body := by
        simp only [totalSymSize_append, totalSymSize_loadSlot, totalSymSize_cons, totalSymSize_nil,
          symSize, hb]
      rw [s1, Nat.add_zero] at hV2 lV2
      rw [s2] at hV3 lV3
      rw [s3] at hV4 lV4
      rw [s4] at hV5 lV5
      rw [s5] at hV6 lV6
      simp only [← Nat.add_assoc] at hV6 lV6
      -- internal-label lookups
      have hcnt : List.lookup cnt lbls = some here := by
        have hmem : (cnt, here) ∈ (layoutItems [SymInstr.label cnt] here).2.1 := by
          rw [layoutItems_label_head]; exact List.mem_cons_self ..
        exact lV1 cnt here hmem
      have hcnt1 : List.lookup (cnt + 1) lbls = some (here + 8 + 8) := by
        have := lV4 (cnt + 1) (here + 8 + 8) (by rw [layoutItems_brjmplabel]; exact List.mem_cons_self ..)
        exact this
      have hcnt2 : List.lookup (cnt + 2) lbls = some (here + 16 + 4 * csize body + 4) :=
        lblLookup_jmplabel lbls cnt (cnt + 2) _ lV6
      -- piece flattens
      have fV1 : rV1.flatten = [] :=
        allins_resolve lbls fns dats _ _ rV1 _ (by simp [isInsOrLabel]) (by simp [insUnwrap]) hV1
      have fV2 : rV2.flatten = loadSlotI a T0 :=
        allins_resolve lbls fns dats _ _ rV2 _ (loadSlot_all_ins a T0) (loadSlot_unwrap a T0) hV2
      have fV3 : rV3.flatten = loadSlotI b T1 :=
        allins_resolve lbls fns dats _ _ rV3 _ (loadSlot_all_ins b T1) (loadSlot_unwrap b T1) hV3
      have fV4 : rV4.flatten = [condInstr c T0 T1 8, jal0 (8 + 4 * (csize body : Int))] := by
        have hr := resolve_brjmplabel lbls fns dats c (cnt + 1) (cnt + 2) (here + 8)
          (here + 16 + 4 * csize body + 4) rV4 hcnt1 hcnt2 hV4
        have hoff : ((here + 16 + 4 * csize body + 4 : Nat) : Int) - (((here + 8 : Nat) : Int) + 4)
            = 8 + 4 * (csize body : Int) := by push_cast; omega
        rw [hr, hoff]
      have fV5 : rV5.flatten = emitCF dat dpos fnPos bp (here :: cp) ep (here + 16) body :=
        ih bs (cnt :: cs) epi _ (here + 16) bp (here :: cp) ep rV5 hV5 (by simpa using hwf)
          (LEnvOk_push_cont lbls bs cs epi bp cp ep cnt here hlenv hcnt) lV5
      have fV6 : rV6.flatten = [jal0 (-(16 + 4 * (csize body : Int)))] := by
        have hr := resolve_jmplabel_flatten lbls fns dats cnt (cnt + 2) (here + 16 + 4 * csize body) here
          rV6 hcnt hV6
        have hoff : ((here : Nat) : Int) - ((here + 16 + 4 * csize body : Nat) : Int)
            = -(16 + 4 * (csize body : Int)) := by push_cast; omega
        rw [hr, hoff]
      -- assemble
      rw [hf6, hf5, hf4, hf3, hf2, fV1, fV2, fV3, fV4, fV5, fV6]
      show _ = loadSlotI a T0 ++ loadSlotI b T1
        ++ [condInstr c T0 T1 8, jal0 (8 + 4 * (csize body : Int))]
        ++ emitCF dat dpos fnPos bp (here :: cp) ep (here + 16) body
        ++ [jal0 (-(16 + 4 * (csize body : Int)))]
      simp [List.append_assoc]
  | call argc rvc f args rets =>
      intro bs cs epi cnt here bp cp ep r h _ _ _
      rw [show (lower dat bs cs epi (.call argc rvc f args rets) cnt).1
          = (args.toList.zipIdx.flatMap (fun ri => loadSlot ri.1 (A ri.2)))
            ++ [SymInstr.callf f]
            ++ (rets.toList.zipIdx.flatMap (fun ri => storeSlot ri.1 (A ri.2))) from rfl] at h
      obtain ⟨rp1, rC3, hp1, hC3, hf3⟩ := resolve_flatten_append lbls fns dats _ _ here r h
      obtain ⟨rC1, rC2, hC1, hC2, hf2⟩ := resolve_flatten_append lbls fns dats _ [SymInstr.callf f] here rp1 hp1
      -- the loads occupy `4·argc` bytes, so the call site sits at `here + 4·argc`
      have hls : totalSymSize (args.toList.zipIdx.flatMap (fun ri => loadSlot ri.1 (A ri.2)))
          = 4 * argc := by
        rw [totalSymSize_flatMap_loadSlot, List.length_zipIdx, Vector.length_toList]
      rw [hls] at hC2
      -- piece flattens
      have fC1 : rC1.flatten = marshalI args.toList :=
        allins_resolve lbls fns dats _ _ rC1 _
          (by simp [List.all_flatMap, loadSlot_all_ins])
          (by rw [marshalI]; exact insUnwrap_flatMap_flatMap _ _ _ (fun ri => loadSlot_unwrap ri.1 (A ri.2)))
          hC1
      have fC2 : rC2.flatten
          = [Instr.jal RA (BitVec.ofInt 21 ((fnPos f : Int) - ((here : Int) + 4 * argc)))] := by
        refine resolve_singleton_flatten lbls fns dats (SymInstr.callf f) (here + 4 * argc) rC2 _ ?_ hC2
        intro v' h'
        obtain ⟨tgt, htgt⟩ := resolveOne_callf_lookup lbls fns dats (here + 4 * argc) f v' h'
        have hoff : ((here + 4 * argc : Nat) : Int) = (here : Int) + 4 * argc := by push_cast; omega
        rw [resolveOne_callf_eq lbls fns dats (here + 4 * argc) f tgt v' htgt h', htab.2 f tgt htgt, hoff]
      have fC3 : rC3.flatten = retStoresI rets.toList :=
        allins_resolve lbls fns dats _ _ rC3 _
          (by simp [List.all_flatMap, storeSlot_all_ins])
          (by rw [retStoresI]; exact insUnwrap_flatMap_flatMap _ _ _ (fun ri => storeSlot_unwrap ri.1 (A ri.2)))
          hC3
      rw [hf3, hf2, fC1, fC2, fC3]
      show _ = marshalI args.toList
        ++ [Instr.jal RA (BitVec.ofInt 21 ((fnPos f : Int) - ((here : Int) + 4 * argc)))]
        ++ retStoresI rets.toList
      rfl

end LowIR.ProgSim.LowerFacts
