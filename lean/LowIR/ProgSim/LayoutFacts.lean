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

/-! ## Per-function slice: `compileFun`'s resolved stream. -/

/-- An all-`.ins`/`.label` stream's byte span is `4 ·` its resolved instruction
    count (each `.ins` is 4 bytes/1 instr; each `.label` is 0/0). -/
theorem totalSymSize_allins : ∀ (sym : List SymInstr), sym.all isInsOrLabel = true →
    totalSymSize sym = 4 * (sym.flatMap insUnwrap).length := by
  intro sym
  induction sym with
  | nil => intro _; rfl
  | cons si rest ih =>
    intro hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [totalSymSize_cons, List.flatMap_cons, List.length_append, Nat.mul_add, ih hall.2]
    cases si with
    | ins i => simp [symSize, insUnwrap]
    | label l => simp [symSize, insUnwrap]
    | br c a b l => exact absurd hall.1 (by simp [isInsOrLabel])
    | jmp l => exact absurd hall.1 (by simp [isInsOrLabel])
    | callf f => exact absurd hall.1 (by simp [isInsOrLabel])
    | cref d => exact absurd hall.1 (by simp [isInsOrLabel])

theorem tss_prologue (fd : FunDef) : totalSymSize (prologue fd) = 4 * (prologueI fd).length := by
  rw [totalSymSize_allins _ (AsmFacts.prologue_all_ins fd), AsmFacts.prologue_unwrap]

theorem tss_epilogue (fd : FunDef) : totalSymSize (epilogue fd) = 4 * (epilogueI fd).length := by
  rw [totalSymSize_allins _ (AsmFacts.epilogue_all_ins fd), AsmFacts.epilogue_unwrap]

/-! ## `lower`'s fresh-label counter is monotone (foundation for global label nodup). -/

/-- The counter `lower` returns is at least the one it started with. -/
theorem lower_snd_ge (dat : Data) : ∀ (stmt : PStmt) (bs cs : List Nat) (epi cnt : Nat),
    cnt ≤ (lower dat bs cs epi stmt cnt).2 := by
  intro stmt
  induction stmt with
  | seq a b iha ihb =>
      intro bs cs epi cnt
      have h1 := iha bs cs epi cnt
      have h2 := ihb bs cs epi (lower dat bs cs epi a cnt).2
      show cnt ≤ (lower dat bs cs epi b (lower dat bs cs epi a cnt).2).2; omega
  | ife c a b t e iht ihe =>
      intro bs cs epi cnt
      have h1 := iht bs cs epi (cnt + 2)
      have h2 := ihe bs cs epi (lower dat bs cs epi t (cnt + 2)).2
      show cnt ≤ (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).2; omega
  | «while» c a b body ih =>
      intro bs cs epi cnt
      have h := ih bs (cnt :: cs) epi (cnt + 3)
      show cnt ≤ (lower dat bs (cnt :: cs) epi body (cnt + 3)).2; omega
  | block body ih =>
      intro bs cs epi cnt
      have h := ih (cnt :: bs) cs epi (cnt + 1)
      show cnt ≤ (lower dat (cnt :: bs) cs epi body (cnt + 1)).2; omega
  | _ => intro bs cs epi cnt; exact Nat.le_refl _

/-- `compileFun`'s resolved byte stream — the direct transcription (label `c` = the
    epilogue label; the body is lowered from counter `c+1`). -/
theorem compileFun_stream (dat : Data) (fd : FunDef) (c : Nat) :
    (compileFun dat fd c).1
      = prologue fd ++ (lower dat [] [] c fd.body (c + 1)).1 ++ [SymInstr.label c] ++ epilogue fd :=
  rfl

/-- **Per-function slice.** Resolving `compileFun`'s stream at byte position `p`
    (under a consistent global label environment) yields exactly `prologueI ++
    emitCF … body ++ epilogueI` — the `Emitted` payload `hfn` demands. Composes
    `prologue_resolves` + `lower_resolve` + `epilogue_resolves`; the label premises
    (`hepi` for the epilogue label, `hlc` for the body's internal labels) are what
    the global label-nodup discharges. -/
theorem compileFun_resolves (dat : Data) (P : LowIR.Prog.Program) (dpos fnPos : Name → Nat)
    (lbls : List (Nat × Nat)) (fns dats : List (Name × Nat)) (htab : TabOk dpos fnPos fns dats)
    (fd : FunDef) (c p : Nat) (rs : List (List Instr))
    (hres : (layoutItems (compileFun dat fd c).1 p).1.mapM (resolveOne lbls fns dats) = some rs)
    (hwf : LowIR.Prog.wf P 0 0 fd.body = true)
    (hepi : List.lookup c lbls = some (p + 4 * (prologueI fd).length + 4 * csize fd.body))
    (hlc : LblConsistent lbls
        (layoutItems (lower dat [] [] c fd.body (c + 1)).1 (p + 4 * (prologueI fd).length)).2.1) :
    rs.flatten = prologueI fd
      ++ emitCF dat dpos fnPos [] []
           (p + 4 * (prologueI fd).length + 4 * csize fd.body) (p + 4 * (prologueI fd).length) fd.body
      ++ epilogueI fd := by
  rw [compileFun_stream] at hres
  obtain ⟨rpre, repi, hpre, hepiR, hf3⟩ :=
    resolve_flatten_append lbls fns dats _ (epilogue fd) p rs hres
  obtain ⟨rpre2, rlab, hpre2, hlabR, hf2⟩ :=
    resolve_flatten_append lbls fns dats _ [SymInstr.label c] p rpre hpre
  obtain ⟨rpro, rbody, hproR, hbodyR, hf1⟩ :=
    resolve_flatten_append lbls fns dats _ (lower dat [] [] c fd.body (c + 1)).1 p rpre2 hpre2
  rw [tss_prologue] at hbodyR
  -- prologue
  have hpro : rpro.flatten = prologueI fd := by
    have h := AsmFacts.prologue_resolves fd lbls fns dats p
    rw [hproR, Option.map_some, Option.some.injEq] at h; exact h
  -- body
  have hbody : rbody.flatten = emitCF dat dpos fnPos [] []
      (p + 4 * (prologueI fd).length + 4 * csize fd.body) (p + 4 * (prologueI fd).length) fd.body :=
    lower_resolve dat P dpos fnPos lbls fns dats htab fd.body [] [] c (c + 1)
      (p + 4 * (prologueI fd).length) [] []
      (p + 4 * (prologueI fd).length + 4 * csize fd.body) rbody hbodyR hwf
      ⟨hepi, rfl, rfl, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp)⟩ hlc
  -- trailing label + epilogue
  have hlabF : rlab.flatten = [] :=
    allins_resolve lbls fns dats _ _ rlab _ (by simp [isInsOrLabel]) (by simp [insUnwrap]) hlabR
  have hepiF : repi.flatten = epilogueI fd := by
    have h := AsmFacts.epilogue_resolves fd lbls fns dats (p + totalSymSize
      (prologue fd ++ (lower dat [] [] c fd.body (c + 1)).1 ++ [SymInstr.label c]))
    rw [hepiR, Option.map_some, Option.some.injEq] at h; exact h
  rw [hf3, hf2, hf1, hpro, hbody, hlabF, hepiF, List.append_nil]

/-! ## `lower`'s label ids: fresh-label range + nodup (global-nodup foundation). -/

/-- The label ids marked in a symbolic stream (the `.label` constructors). -/
def labelIds : List SymInstr → List Nat
  | [] => []
  | SymInstr.label l :: rest => l :: labelIds rest
  | _ :: rest => labelIds rest

@[simp] theorem labelIds_nil : labelIds [] = [] := rfl
@[simp] theorem labelIds_label (l : Nat) (rest) :
    labelIds (SymInstr.label l :: rest) = l :: labelIds rest := rfl

theorem labelIds_append : ∀ (a b : List SymInstr), labelIds (a ++ b) = labelIds a ++ labelIds b := by
  intro a; induction a with
  | nil => intro b; rfl
  | cons si rest ih => intro b; cases si <;> simp [labelIds, ih]

@[simp] theorem labelIds_ins (i) (rest) : labelIds (SymInstr.ins i :: rest) = labelIds rest := rfl
@[simp] theorem labelIds_jmp (l) (rest) : labelIds (SymInstr.jmp l :: rest) = labelIds rest := rfl
@[simp] theorem labelIds_br (c a b l) (rest) : labelIds (SymInstr.br c a b l :: rest) = labelIds rest := rfl
@[simp] theorem labelIds_cref (d) (rest) : labelIds (SymInstr.cref d :: rest) = labelIds rest := rfl

theorem labelIds_of_all_ins : ∀ (sym : List SymInstr), sym.all (fun s => match s with | SymInstr.label _ => false | _ => true) = true → labelIds sym = [] := by
  intro sym; induction sym with
  | nil => intro _; rfl
  | cons si rest ih => intro h; simp only [List.all_cons, Bool.and_eq_true] at h
                       cases si <;> simp_all [labelIds]

@[simp] theorem labelIds_loadSlot (r t : Reg) : labelIds (loadSlot r t) = [] := by
  unfold loadSlot; by_cases h : r = 0 <;> simp [h, labelIds]
@[simp] theorem labelIds_storeSlot (r t : Reg) : labelIds (storeSlot r t) = [] := by
  unfold storeSlot; by_cases h : r = 0 <;> simp [h, labelIds]
@[simp] theorem labelIds_synthConst (t : Reg) (v : Int) : labelIds (synthConst t v) = [] := by
  simp [synthConst, labelIds]

@[simp] theorem labelIds_flatMap {α} (f : α → List SymInstr) (xs : List α) :
    labelIds (xs.flatMap f) = xs.flatMap (fun x => labelIds (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, labelIds_append, ih, List.flatMap_cons]

@[simp] theorem flatMap_const_nil {α β} (xs : List α) : xs.flatMap (fun _ => ([] : List β)) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, ih]; rfl


theorem lower_labels_range (dat : Data) : ∀ (stmt : PStmt) (bs cs : List Nat) (epi cnt : Nat),
    ∀ l ∈ labelIds (lower dat bs cs epi stmt cnt).1,
      cnt ≤ l ∧ l < (lower dat bs cs epi stmt cnt).2 := by
  intro stmt
  induction stmt with
  | seq a b iha ihb =>
    intro bs cs epi cnt l hl
    rw [lower_seq, labelIds_append, List.mem_append] at hl
    have hm := lower_snd_ge dat a bs cs epi cnt
    have hm2 := lower_snd_ge dat b bs cs epi (lower dat bs cs epi a cnt).2
    show cnt ≤ l ∧ l < (lower dat bs cs epi b (lower dat bs cs epi a cnt).2).2
    rcases hl with h | h
    · have := iha bs cs epi cnt l h; exact ⟨by omega, by omega⟩
    · have := ihb bs cs epi (lower dat bs cs epi a cnt).2 l h; exact ⟨by omega, by omega⟩
  | block body ih =>
    intro bs cs epi cnt l hl
    rw [lower_block, labelIds_append] at hl
    simp only [List.mem_append, labelIds_label, labelIds_nil, List.mem_singleton,
      List.mem_cons, List.not_mem_nil, or_false] at hl
    have hm := lower_snd_ge dat body (cnt :: bs) cs epi (cnt + 1)
    show cnt ≤ l ∧ l < (lower dat (cnt :: bs) cs epi body (cnt + 1)).2
    rcases hl with h | h
    · have := ih (cnt :: bs) cs epi (cnt + 1) l h; exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  | ife c a b t e iht ihe =>
    intro bs cs epi cnt l hl
    rw [lower_ife] at hl
    simp only [labelIds_append, labelIds_loadSlot, labelIds_br, labelIds_jmp, labelIds_label,
      labelIds_nil, List.nil_append, List.append_assoc, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hl
    have ht := lower_snd_ge dat t bs cs epi (cnt + 2)
    have he := lower_snd_ge dat e bs cs epi (lower dat bs cs epi t (cnt + 2)).2
    show cnt ≤ l ∧ l < (lower dat bs cs epi e (lower dat bs cs epi t (cnt + 2)).2).2
    rcases hl with h | h | h | h
    · have := ihe bs cs epi (lower dat bs cs epi t (cnt + 2)).2 l h; exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · have := iht bs cs epi (cnt + 2) l h; exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  | «while» c a b body ih =>
    intro bs cs epi cnt l hl
    rw [lower_while] at hl
    simp only [labelIds_append, labelIds_loadSlot, labelIds_br, labelIds_jmp, labelIds_label,
      labelIds_nil, List.nil_append, List.append_assoc, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hl
    have hb := lower_snd_ge dat body bs (cnt :: cs) epi (cnt + 3)
    show cnt ≤ l ∧ l < (lower dat bs (cnt :: cs) epi body (cnt + 3)).2
    rcases hl with h | h | h | h
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · have := ih bs (cnt :: cs) epi (cnt + 3) l h; exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  | _ =>
    intro bs cs epi cnt l hl
    revert hl
    simp only [lower, pure, StateT.pure, bind, StateT.bind, Prod.mk.injEq,
      labelIds_append, labelIds, labelIds_loadSlot, labelIds_storeSlot, labelIds_synthConst,
      labelIds_flatMap, flatMap_const_nil, List.append_nil, List.not_mem_nil, false_implies]


theorem lower_labels_nodup (dat : Data) : ∀ (stmt : PStmt) (bs cs : List Nat) (epi cnt : Nat),
    (labelIds (lower dat bs cs epi stmt cnt).1).Nodup := by
  intro stmt
  induction stmt with
  | seq a b iha ihb =>
    intro bs cs epi cnt
    rw [lower_seq, labelIds_append, List.nodup_append]
    refine ⟨iha _ _ _ _, ihb _ _ _ _, ?_⟩
    intro x hx y hy
    have h1 := lower_labels_range dat a bs cs epi cnt x hx
    have h2 := lower_labels_range dat b bs cs epi (lower dat bs cs epi a cnt).2 y hy
    omega
  | block body ih =>
    intro bs cs epi cnt
    rw [lower_block, labelIds_append, List.nodup_append]
    refine ⟨ih _ _ _ _, by simp, ?_⟩
    intro x hx y hy
    have h1 := lower_labels_range dat body (cnt :: bs) cs epi (cnt + 1) x hx
    simp only [labelIds_label, labelIds_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    omega
  | ife c a b t e iht ihe =>
    intro bs cs epi cnt
    rw [lower_ife]
    simp only [labelIds_append, labelIds_loadSlot, labelIds_br, labelIds_jmp, labelIds_label,
      labelIds_nil, List.nil_append, List.append_assoc, List.singleton_append]
    rw [List.nodup_append]
    refine ⟨ihe _ _ _ _, ?_, ?_⟩
    · rw [List.nodup_cons, List.nodup_append]
      refine ⟨?_, iht _ _ _ _, by simp, ?_⟩
      · simp only [List.mem_append, List.mem_singleton, not_or]
        refine ⟨fun hc => ?_, fun hc => by omega⟩
        have := lower_labels_range dat t bs cs epi (cnt + 2) cnt hc; omega
      · intro x hx y hy
        have := lower_labels_range dat t bs cs epi (cnt + 2) x hx
        simp only [List.mem_singleton] at hy; omega
    · intro x hx y hy
      have hxr := lower_labels_range dat e bs cs epi (lower dat bs cs epi t (cnt + 2)).2 x hx
      have hst := lower_snd_ge dat t bs cs epi (cnt + 2)
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h
      · omega
      · have := lower_labels_range dat t bs cs epi (cnt + 2) y h; omega
      · omega
  | «while» c a b body ih =>
    intro bs cs epi cnt
    rw [lower_while]
    simp only [labelIds_append, labelIds_loadSlot, labelIds_br, labelIds_jmp, labelIds_label,
      labelIds_nil, List.nil_append, List.append_assoc, List.singleton_append]
    rw [List.nodup_cons, List.nodup_cons, List.nodup_append]
    have hb := lower_snd_ge dat body bs (cnt :: cs) epi (cnt + 3)
    refine ⟨?_, ?_, ih _ _ _ _, by simp, ?_⟩
    · simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      refine ⟨by omega, fun hc => ?_, fun hc => by omega⟩
      have := lower_labels_range dat body bs (cnt :: cs) epi (cnt + 3) cnt hc; omega
    · simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨fun hc => ?_, fun hc => by omega⟩
      have := lower_labels_range dat body bs (cnt :: cs) epi (cnt + 3) (cnt + 1) hc; omega
    · intro x hx y hy
      have := lower_labels_range dat body bs (cnt :: cs) epi (cnt + 3) x hx
      simp only [List.mem_singleton] at hy; omega
  | _ =>
    intro bs cs epi cnt
    simp only [lower, pure, StateT.pure, bind, StateT.bind]
    simp [labelIds_append, labelIds, labelIds_loadSlot, labelIds_storeSlot, labelIds_synthConst]


end LowIR.ProgSim.LayoutFacts
