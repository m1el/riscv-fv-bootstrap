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
open LowIR.Prog (FunDef Data Name Program dataOffsetsFrom)

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


/-! ## Lift label range/nodup through `compileFun` (epi label = `c`; body labels ≥ `c+1`). -/

@[simp] theorem labelIds_map_ins {α} (g : α → Instr) (xs : List α) :
    labelIds (xs.map (fun x => SymInstr.ins (g x))) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, labelIds_ins, ih]

theorem labelIds_prologue (fd : FunDef) : labelIds (prologue fd) = [] := by
  simp only [prologue, labelIds_append, labelIds_map_ins, labelIds_flatMap, labelIds_storeSlot,
    flatMap_const_nil, labelIds, List.append_nil]
  split <;> simp [labelIds, labelIds_append, labelIds_storeSlot]

theorem labelIds_epilogue (fd : FunDef) : labelIds (epilogue fd) = [] := by
  simp only [epilogue, labelIds_append, labelIds_flatMap, labelIds_loadSlot, flatMap_const_nil,
    labelIds, List.append_nil]


theorem compileFun_snd (dat : Data) (fd : FunDef) (c : Nat) :
    (compileFun dat fd c).2 = (lower dat [] [] c fd.body (c + 1)).2 := rfl

theorem labelIds_compileFun (dat : Data) (fd : FunDef) (c : Nat) :
    labelIds (compileFun dat fd c).1 = labelIds (lower dat [] [] c fd.body (c + 1)).1 ++ [c] := by
  rw [compileFun_stream]
  simp only [labelIds_append, labelIds_prologue, labelIds_epilogue, labelIds_label, labelIds_nil,
    List.nil_append, List.append_nil]

theorem compileFun_labels_range (dat : Data) (fd : FunDef) (c : Nat) :
    ∀ l ∈ labelIds (compileFun dat fd c).1, c ≤ l ∧ l < (compileFun dat fd c).2 := by
  intro l hl
  rw [labelIds_compileFun, List.mem_append] at hl
  rw [compileFun_snd]
  have hsg := lower_snd_ge dat fd.body [] [] c (c + 1)
  rcases hl with h | h
  · have := lower_labels_range dat fd.body [] [] c (c + 1) l h; exact ⟨by omega, by omega⟩
  · simp only [List.mem_singleton] at h; exact ⟨by omega, by omega⟩

theorem compileFun_labels_nodup (dat : Data) (fd : FunDef) (c : Nat) :
    (labelIds (compileFun dat fd c).1).Nodup := by
  rw [labelIds_compileFun, List.nodup_append]
  refine ⟨lower_labels_nodup dat fd.body [] [] c (c + 1), by simp, ?_⟩
  intro x hx y hy
  have := lower_labels_range dat fd.body [] [] c (c + 1) x hx
  simp only [List.mem_singleton] at hy; omega

theorem compileFun_snd_gt (dat : Data) (fd : FunDef) (c : Nat) : c < (compileFun dat fd c).2 := by
  rw [compileFun_snd]; have := lower_snd_ge dat fd.body [] [] c (c + 1); omega


/-! ## Global label nodup: the fresh-counter-threaded segment mapM. -/

/-- The `compileProgT` segment builder (StateM over the fresh-label counter). -/
def mapSegs (dat : Data) (xs : List (Name × FunDef)) : M (List (Name × List SymInstr)) :=
  xs.mapM (fun nf => do pure (nf.1, ← compileFun dat nf.2))

theorem mapSegs_nil (dat : Data) (c : Nat) : mapSegs dat [] c = ([], c) := rfl

theorem mapSegs_cons (dat : Data) (nf : Name × FunDef) (rest : List (Name × FunDef)) (c : Nat) :
    mapSegs dat (nf :: rest) c
      = ((nf.1, (compileFun dat nf.2 c).1) :: (mapSegs dat rest (compileFun dat nf.2 c).2).1,
         (mapSegs dat rest (compileFun dat nf.2 c).2).2) := by
  rw [mapSegs, List.mapM_cons]; rfl

/-- `mapSegs` distributes over an env append: the second group is compiled from
    the fresh-label counter the first group ends at. The counter-threading twin
    of `layout_flat_append`. -/
theorem mapSegs_append (dat : Data) : ∀ (a b : List (Name × FunDef)) (c : Nat),
    (mapSegs dat (a ++ b) c).1
      = (mapSegs dat a c).1 ++ (mapSegs dat b (mapSegs dat a c).2).1
    ∧ (mapSegs dat (a ++ b) c).2 = (mapSegs dat b (mapSegs dat a c).2).2 := by
  intro a
  induction a with
  | nil => intro b c; rw [List.nil_append, mapSegs_nil]; exact ⟨rfl, rfl⟩
  | cons nf rest ih =>
    intro b c
    rw [List.cons_append, mapSegs_cons, mapSegs_cons]
    obtain ⟨ih1, ih2⟩ := ih b (compileFun dat nf.2 c).2
    constructor
    · dsimp only; rw [ih1, List.cons_append]
    · dsimp only; exact ih2

/-- All segment labels (keys) built from counter `c`: nodup, and every one lies in
    `[c, endCounter)`. The disjoint per-function ranges (`compileFun_snd_gt`) make
    the concatenation nodup. -/
theorem mapSegs_labels (dat : Data) : ∀ (xs : List (Name × FunDef)) (c : Nat),
    ((mapSegs dat xs c).1.flatMap (fun s => labelIds s.2)).Nodup
    ∧ (∀ l ∈ (mapSegs dat xs c).1.flatMap (fun s => labelIds s.2),
        c ≤ l ∧ l < (mapSegs dat xs c).2)
    ∧ c ≤ (mapSegs dat xs c).2 := by
  intro xs
  induction xs with
  | nil => intro c; rw [mapSegs_nil]; refine ⟨by simp, by simp, Nat.le_refl _⟩
  | cons nf rest ih =>
    intro c
    rw [mapSegs_cons]
    have hc' := compileFun_snd_gt dat nf.2 c
    obtain ⟨ihnd, ihrange, ihge⟩ := ih (compileFun dat nf.2 c).2
    simp only [List.flatMap_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨compileFun_labels_nodup dat nf.2 c, ihnd, ?_⟩
      intro x hx y hy
      have hxr := compileFun_labels_range dat nf.2 c x hx
      have hyr := ihrange y hy
      omega
    · intro l hl
      rw [List.mem_append] at hl
      rcases hl with h | h
      · have := compileFun_labels_range dat nf.2 c l h; exact ⟨by omega, by omega⟩
      · have := ihrange l h; exact ⟨by omega, by omega⟩
    · omega

/-! ## Layout label keys = per-segment labelIds; lookup from nodup keys. -/

theorem layoutItems_lbls_keys : ∀ (items : List SymInstr) (pos : Nat),
    (layoutItems items pos).2.1.map Prod.fst = labelIds items := by
  intro items
  induction items with
  | nil => intro pos; rfl
  | cons si rest ih =>
    intro pos
    cases si <;> simp [layoutItems, labelIds, ih]

theorem layout_lbls_keys : ∀ (segs : List (Name × List SymInstr)) (pos : Nat),
    (layout segs pos).2.1.map Prod.fst = segs.flatMap (fun s => labelIds s.2) := by
  intro segs
  induction segs with
  | nil => intro pos; rfl
  | cons s rest ih =>
    intro pos
    obtain ⟨n, items⟩ := s
    show ((layoutItems items pos).2.1 ++ (layout rest (layoutItems items pos).2.2).2.1).map Prod.fst = _
    rw [List.map_append, layoutItems_lbls_keys, ih, List.flatMap_cons]

theorem lookup_of_nodup_mem (l : List (Nat × Nat)) (a b : Nat)
    (hnd : (l.map Prod.fst).Nodup) (hmem : (a, b) ∈ l) : l.lookup a = some b := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    rcases List.mem_cons.mp hmem with h | h
    · injection h with h1 h2; subst h1; subst h2
      have hkk : (a == a) = true := by rw [beq_iff_eq]
      rw [hkk]
    · have hak : (a == k) = false := by
        cases hb : a == k
        · rfl
        · rw [beq_iff_eq] at hb; exact absurd hb (by
            rintro rfl; exact hnd.1 (List.mem_map.mpr ⟨(a, b), h, rfl⟩))
      rw [hak]; exact ih hnd.2 h
/-! ## Assembled: global lbls has nodup keys ⇒ membership determines lookup. -/

theorem global_lbls_nodup (dat : Data) (env : List (Name × FunDef)) (stub : List SymInstr)
    (hstub : labelIds stub = []) :
    ((layout (("", stub) :: (mapSegs dat env 0).1) 0).2.1.map Prod.fst).Nodup := by
  rw [layout_lbls_keys, List.flatMap_cons]
  show (labelIds stub ++ _).Nodup
  rw [hstub, List.nil_append]
  exact (mapSegs_labels dat env 0).1

theorem lbls_lookup (dat : Data) (env : List (Name × FunDef)) (stub : List SymInstr)
    (hstub : labelIds stub = []) (l p : Nat)
    (hmem : (l, p) ∈ (layout (("", stub) :: (mapSegs dat env 0).1) 0).2.1) :
    (layout (("", stub) :: (mapSegs dat env 0).1) 0).2.1.lookup l = some p :=
  lookup_of_nodup_mem _ l p (global_lbls_nodup dat env stub hstub) hmem

/-! ## Position-membership: a function's `layoutItems` label entries live in the
    global label table (so `lbls_lookup` resolves each to its absolute byte pos). -/

/-- Each label entry `layoutItems` records for a segment sits in the global
    `layout` label table: the global table is the positional concatenation of the
    per-segment `layoutItems` tables (the `layout` cons def), so a `mem` on any
    single segment's slice lifts to the whole. `pre` is the list of segments laid
    out before this one; the segment `(n, items)` therefore starts at the end
    position of `pre` (`(layout pre pos).2.2.2`). -/
theorem layout_lbls_mem :
    ∀ (pre : List (Name × List SymInstr)) (n : Name) (items : List SymInstr)
      (suf : List (Name × List SymInstr)) (pos : Nat) (x : Nat × Nat),
      x ∈ (layoutItems items (layout pre pos).2.2.2).2.1 →
      x ∈ (layout (pre ++ (n, items) :: suf) pos).2.1 := by
  intro pre
  induction pre with
  | nil =>
    intro n items suf pos x hx
    show x ∈ ((layoutItems items pos).2.1 ++ (layout suf (layoutItems items pos).2.2).2.1)
    exact List.mem_append.mpr (Or.inl hx)
  | cons mi pre' ih =>
    intro n items suf pos x hx
    obtain ⟨m, its⟩ := mi
    show x ∈ ((layoutItems its pos).2.1
              ++ (layout (pre' ++ (n, items) :: suf) (layoutItems its pos).2.2).2.1)
    exact List.mem_append.mpr (Or.inr (ih n items suf (layoutItems its pos).2.2 x hx))

/-- An all-`.ins`/`.label`-free (i.e. no-`.label`) stream records no label
    entries: its `layoutItems` label table is empty. -/
theorem layoutItems_lbltab_nil (items : List SymInstr) (pos : Nat)
    (h : labelIds items = []) : (layoutItems items pos).2.1 = [] := by
  have hk := layoutItems_lbls_keys items pos
  rw [h] at hk
  exact List.map_eq_nil_iff.mp hk

/-- A singleton `.label l` stream records exactly `(l, pos)`. -/
theorem layoutItems_label_singleton (l pos : Nat) :
    (layoutItems [SymInstr.label l] pos).2.1 = [(l, pos)] := rfl

/-- **`compileFun`'s label table** (at absolute byte position `p`): exactly the
    body's internal labels (at `bodyPos = p + 4·|prologueI|`) followed by the
    single epilogue-label entry `(c, epiPos)` with `epiPos = bodyPos + 4·csize
    body`. Prologue/epilogue are all-`.ins`, contributing nothing. -/
theorem compileFun_lbltab (dat : Data) (fd : FunDef) (c p : Nat) :
    (layoutItems (compileFun dat fd c).1 p).2.1
      = (layoutItems (lower dat [] [] c fd.body (c + 1)).1
            (p + 4 * (prologueI fd).length)).2.1
        ++ [(c, p + 4 * (prologueI fd).length + 4 * csize fd.body)] := by
  rw [compileFun_stream]
  -- peel epilogue (all-.ins) off the right
  rw [(layoutItems_append _ (epilogue fd) p).2,
      layoutItems_lbltab_nil (epilogue fd) _ (labelIds_epilogue fd), List.append_nil]
  -- peel the epilogue-label singleton
  rw [(layoutItems_append _ [SymInstr.label c] p).2, layoutItems_label_singleton]
  -- peel the prologue (all-.ins) off the left
  rw [(layoutItems_append (prologue fd) _ p).2,
      layoutItems_lbltab_nil (prologue fd) _ (labelIds_prologue fd), List.nil_append]
  -- pin the positions via the size bridges
  rw [totalSymSize_append, tss_prologue,
      lower_totalSymSize dat fd.body [] [] c (c + 1), Nat.add_assoc]

/-! ## Per-function discharge: `hepi`/`hlc` for `compileFun_resolves`.

    Given the global program layout and that function `g`'s compiled segment
    `(compileFun dat gd c).1` sits at absolute byte position `p` (i.e. after the
    prefix `pre` of segments), both `compileFun_resolves` label premises hold:
    the epilogue label `c` resolves to its byte position, and every body label
    resolves to its layout position. This packages `compileFun_lbltab` (what the
    labels ARE) + `layout_lbls_mem` (they live in the global table) + `lbls_lookup`
    (nodup keys ⇒ membership determines lookup). The one obligation left to the
    caller is `hseg`/`hp`: that `g` is laid out at `p` — the `fnPos g` tie. -/
theorem compileFun_lbls_discharge (dat : Data) (env : List (Name × FunDef))
    (stub : List SymInstr) (hstub : labelIds stub = [])
    (gd : FunDef) (c p : Nat) (g : Name)
    (pre suf : List (Name × List SymInstr))
    (hseg : ("", stub) :: (mapSegs dat env 0).1
              = pre ++ (g, (compileFun dat gd c).1) :: suf)
    (hp : (layout pre 0).2.2.2 = p) :
    List.lookup c (layout (("", stub) :: (mapSegs dat env 0).1) 0).2.1
        = some (p + 4 * (prologueI gd).length + 4 * csize gd.body)
    ∧ LblConsistent (layout (("", stub) :: (mapSegs dat env 0).1) 0).2.1
        (layoutItems (lower dat [] [] c gd.body (c + 1)).1
          (p + 4 * (prologueI gd).length)).2.1 := by
  -- membership of any compileFun-table entry in the global label table
  have hmem_global : ∀ x, x ∈ (layoutItems (compileFun dat gd c).1 p).2.1 →
      x ∈ (layout (("", stub) :: (mapSegs dat env 0).1) 0).2.1 := by
    intro x hx
    rw [hseg]
    refine layout_lbls_mem pre g (compileFun dat gd c).1 suf 0 x ?_
    rw [hp]; exact hx
  refine ⟨?_, ?_⟩
  · -- epilogue label
    apply lbls_lookup dat env stub hstub
    apply hmem_global
    rw [compileFun_lbltab]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · -- body labels
    intro l lp hlp
    apply lbls_lookup dat env stub hstub
    apply hmem_global
    rw [compileFun_lbltab]
    exact List.mem_append_left _ hlp

/-! ## The `fnPos g` tie: the layout function table records each segment's start.

    `layout` records one `(name, pos)` per segment, in order, at the byte position
    where that segment begins. So a `mem` in the function table decomposes the
    segment list at that name with the recorded position as the prefix's end — the
    `hseg`/`hp` `compileFun_lbls_discharge` demands. -/
theorem layout_fns_decomp :
    ∀ (segs : List (Name × List SymInstr)) (pos : Nat) (g : Name) (p : Nat),
      (g, p) ∈ (layout segs pos).2.2.1 →
      ∃ (pre : List (Name × List SymInstr)) (items : List SymInstr)
        (suf : List (Name × List SymInstr)),
        segs = pre ++ (g, items) :: suf ∧ (layout pre pos).2.2.2 = p := by
  intro segs
  induction segs with
  | nil => intro pos g p hmem; exact absurd hmem List.not_mem_nil
  | cons ni rest ih =>
    intro pos g p hmem
    obtain ⟨n, its⟩ := ni
    rw [show (layout ((n, its) :: rest) pos).2.2.1
          = (n, pos) :: (layout rest (layoutItems its pos).2.2).2.2.1 from rfl,
        List.mem_cons] at hmem
    rcases hmem with h | h
    · -- head: g = n, p = pos
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], its, rest, rfl, rfl⟩
    · -- tail: recurse into `rest`, prepend `(n, its)` to the prefix
      obtain ⟨pre', items, suf, hrest, hp'⟩ := ih (layoutItems its pos).2.2 g p h
      refine ⟨(n, its) :: pre', items, suf, ?_, ?_⟩
      · rw [hrest]; rfl
      · -- (layout ((n,its)::pre') pos).2.2.2 = (layout pre' (layoutItems its pos).2.2).2.2.2 = p
        exact hp'

/-- **Env-level discharge** (the `hfn`/`hem` label premises, keyed on an env
    decomposition). For a program whose env splits as `envPre ++ (g, gd) :: envSuf`,
    function `g`'s fresh-label counter is `(mapSegs dat envPre 0).2` and its byte
    position is the layout end of `("", stub) :: (mapSegs dat envPre 0).1`; at those,
    both `compileFun_resolves` label premises hold. Composes `mapSegs_append` +
    `mapSegs_cons` (the segment decomposition) with `compileFun_lbls_discharge`. The
    caller (Phase 6) supplies the env split and identifies this byte position with
    `g`'s `fnTab` entry (`layout_fns_decomp`). -/
theorem env_fn_lbls_discharge (dat : Data) (envPre envSuf : List (Name × FunDef))
    (stub : List SymInstr) (hstub : labelIds stub = []) (g : Name) (gd : FunDef) :
    List.lookup (mapSegs dat envPre 0).2
        (layout (("", stub) :: (mapSegs dat (envPre ++ (g, gd) :: envSuf) 0).1) 0).2.1
      = some ((layout (("", stub) :: (mapSegs dat envPre 0).1) 0).2.2.2
              + 4 * (prologueI gd).length + 4 * csize gd.body)
    ∧ LblConsistent
        (layout (("", stub) :: (mapSegs dat (envPre ++ (g, gd) :: envSuf) 0).1) 0).2.1
        (layoutItems (lower dat [] [] (mapSegs dat envPre 0).2 gd.body
              ((mapSegs dat envPre 0).2 + 1)).1
          ((layout (("", stub) :: (mapSegs dat envPre 0).1) 0).2.2.2
            + 4 * (prologueI gd).length)).2.1 := by
  have hseg : ("", stub) :: (mapSegs dat (envPre ++ (g, gd) :: envSuf) 0).1
      = (("", stub) :: (mapSegs dat envPre 0).1)
        ++ (g, (compileFun dat gd (mapSegs dat envPre 0).2).1)
           :: (mapSegs dat envSuf (compileFun dat gd (mapSegs dat envPre 0).2).2).1 := by
    rw [(mapSegs_append dat envPre ((g, gd) :: envSuf) 0).1, mapSegs_cons, List.cons_append]
  exact compileFun_lbls_discharge dat (envPre ++ (g, gd) :: envSuf) stub hstub gd
    (mapSegs dat envPre 0).2 ((layout (("", stub) :: (mapSegs dat envPre 0).1) 0).2.2.2) g
    (("", stub) :: (mapSegs dat envPre 0).1)
    (mapSegs dat envSuf (compileFun dat gd (mapSegs dat envPre 0).2).2).1
    hseg rfl

/-! ## Brick 1 — the `compileProgT`/`layoutOf` structural unfolding.

    Expose, from a successful `compileProgT`/`layoutOf`, the internal resolve
    structure: `L.instrs` is the flatten of the whole positioned stream resolved
    under the global tables, `L.fnTab` is the non-stub function table, and the
    data-offset table is `dataOffsetsFrom (pad8 codeEnd)`. Everything downstream
    (`hfn`/`hem`) reads these off `progLayout`. -/

/-- The stub segment `compileProgT` prepends before the functions: the entry
    `jal` (`callf entry`) and the halt self-loop (`jal x0 0`). Label-free. -/
def stubSeg (entry : Name) : List SymInstr :=
  [SymInstr.callf entry, SymInstr.ins (jal0 0)]

@[simp] theorem labelIds_stubSeg (entry : Name) : labelIds (stubSeg entry) = [] := rfl

/-- The whole program's positioned layout (Pass A): the stub segment followed by
    every function's compiled symbolic stream, laid out from byte 0. Its four
    projections are the flat stream, the global label table, the function table,
    and the end position (total code bytes). This is exactly what `compileProgT`
    resolves. -/
def progLayout (P : Program) (entry : Name) :
    List (Nat × SymInstr) × List (Nat × Nat) × List (Name × Nat) × Nat :=
  layout (("", stubSeg entry) :: (mapSegs P.data P.env 0).1) 0

/-- The byte position of each function's entry, read off the (frozen) layout
    function table — the `fnPos` that `emitCF`/`lower_sim_cf` consume. -/
def fnPosOf (L : Layout) : Name → Nat := fun f => (List.lookup f L.fnTab).getD 0

/-- **Brick 1.** A successful `compileProgT` decomposes into a resolve of
    `progLayout`: the flat stream resolves (under the global label/fn/data tables)
    to `rs`, `L.instrs = rs.flatten`, the returned function table is the layout's
    minus the stub, and the data table is `dataOffsetsFrom (pad8 codeEnd)`. -/
theorem compileProgT_decomp {P : Program} {entry : Name} {is : List Instr}
    {fnsF dats : List (Name × Nat)}
    (h : compileProgT P entry = some (is, fnsF, dats)) :
    ∃ rs, (progLayout P entry).1.mapM
              (resolveOne (progLayout P entry).2.1 (progLayout P entry).2.2.1
                (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data)) = some rs
      ∧ is = rs.flatten
      ∧ fnsF = (progLayout P entry).2.2.1.filter (fun f => f.1 != "")
      ∧ dats = dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data := by
  unfold compileProgT at h
  split at h
  · exact absurd h (by simp)
  · -- the good branch: reduce the segs `.run'` and match on the layout tuple
    have hsegs : ((P.env.mapM (fun nf => do pure (nf.1, ← compileFun P.data nf.2)) : M _).run' 0)
        = (mapSegs P.data P.env 0).1 := rfl
    rw [hsegs] at h
    -- `h`'s `layout (...) 0` is now defeq to `progLayout P entry`
    show ∃ rs, _ ∧ _ ∧ _ ∧ _
    revert h
    show (((( progLayout P entry).1.mapM
              (resolveOne (progLayout P entry).2.1 (progLayout P entry).2.2.1
                (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data))).map List.flatten).map
          (fun is => (is, (progLayout P entry).2.2.1.filter (fun f => f.1 != ""),
                      dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data))
        = some (is, fnsF, dats)) → _
    intro h
    cases hm : (progLayout P entry).1.mapM
        (resolveOne (progLayout P entry).2.1 (progLayout P entry).2.2.1
          (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data)) with
    | none => rw [hm] at h; simp at h
    | some rs =>
        rw [hm] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨rs, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- `layoutOf` succeeding gives the same decomposition on `L`'s own fields, plus
    `L.segStart = pad8 (4 * L.instrs.length)` and `L.data = P.data`. -/
theorem layoutOf_decomp {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    (h : layoutOf P entry cb slo = some L) :
    L.codeBase = cb ∧ L.stackLo = slo ∧ L.data = P.data
    ∧ L.segStart = pad8 (4 * L.instrs.length)
    ∧ ∃ dats, compileProgT P entry = some (L.instrs, L.fnTab, dats) := by
  unfold layoutOf at h
  split at h
  · rename_i is fns dats' hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, dats', hc⟩
  · exact absurd h (by simp)

/-! ## Brick 2 — the flat resolve split at each function's byte position.

    Slice the whole-program resolved stream `L.instrs` at a function `g`'s position:
    `L.instrs = pre ++ rsg.flatten ++ suf`, where `rsg` is g's compiled segment
    resolved at `pp` (feeding `compileFun_resolves`' `hres`) and `4·|pre| = pp`. -/

/-- Layout-level resolve-length: the whole positioned stream resolves to
    `totalSymSize/4` instructions (the byte-position ↔ instruction-index bridge,
    lifted from `resolve_length` per segment). -/
theorem resolve_length_layout (lbls fns dats : List _) :
    ∀ (segs : List (Name × List SymInstr)) (pos : Nat) (rs : List (List Instr)),
      (layout segs pos).1.mapM (resolveOne lbls fns dats) = some rs →
      4 * rs.flatten.length = totalSymSize (segs.flatMap Prod.snd) := by
  intro segs
  induction segs with
  | nil => intro pos rs h; simp only [layout, List.mapM_nil] at h; rw [← Option.some.inj h]; rfl
  | cons s rest ih =>
    intro pos rs h
    obtain ⟨n, items⟩ := s
    rw [show (layout ((n, items) :: rest) pos).1
          = (layoutItems items pos).1 ++ (layout rest (layoutItems items pos).2.2).1 from rfl] at h
    obtain ⟨ra, rb, hra, hrb, hr⟩ := mapM_append_inv _ _ _ _ h
    rw [hr, List.flatten_append, List.length_append, Nat.mul_add,
        resolve_length lbls fns dats items pos ra hra, ih _ _ hrb,
        List.flatMap_cons, totalSymSize_append]

/-- **Brick 2.** For a function `g` at env position `envPre ++ (g,gd) :: envSuf`,
    the whole-program resolved stream splits as `pre ++ rsg.flatten ++ suf`, where
    `rsg` is g's compiled segment resolved at its byte position `pp` (the input
    `compileFun_resolves` needs) and `4·|pre.flatten| = pp`. -/
theorem fn_resolve_slice {P : Program} {entry : Name}
    {dats : List (Name × Nat)} {rs : List (List Instr)}
    (envPre envSuf : List (Name × FunDef)) (g : Name) (gd : FunDef)
    (hE : P.env = envPre ++ (g, gd) :: envSuf)
    (hrs : (progLayout P entry).1.mapM
              (resolveOne (progLayout P entry).2.1 (progLayout P entry).2.2.1 dats) = some rs) :
    ∃ (pre rsg suf : List (List Instr)),
      rs.flatten = pre.flatten ++ rsg.flatten ++ suf.flatten
      ∧ 4 * pre.flatten.length
          = (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2
      ∧ (layoutItems (compileFun P.data gd (mapSegs P.data envPre 0).2).1
            (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2).1.mapM
          (resolveOne (progLayout P entry).2.1 (progLayout P entry).2.2.1 dats) = some rsg := by
  -- abbreviations (inlined — this codebase is Mathlib-free, no `set`):
  --   cg      := (mapSegs P.data envPre 0).2         g's fresh-label counter
  --   preSegs := ("", stubSeg entry) :: (mapSegs P.data envPre 0).1
  --   sufSegs := (mapSegs P.data envSuf (compileFun P.data gd cg).2).1
  --   pp      := (layout preSegs 0).2.2.2            g's byte position
  -- the global segment list decomposes at g
  have hseg : ("", stubSeg entry) :: (mapSegs P.data P.env 0).1
      = (("", stubSeg entry) :: (mapSegs P.data envPre 0).1)
        ++ (g, (compileFun P.data gd (mapSegs P.data envPre 0).2).1)
           :: (mapSegs P.data envSuf (compileFun P.data gd (mapSegs P.data envPre 0).2).2).1 := by
    rw [hE, (mapSegs_append P.data envPre ((g, gd) :: envSuf) 0).1, mapSegs_cons, List.cons_append]
  -- split the flat stream at the prefix / g-segment boundary
  have hpl : (progLayout P entry).1
      = (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).1
        ++ (layout ((g, (compileFun P.data gd (mapSegs P.data envPre 0).2).1)
              :: (mapSegs P.data envSuf (compileFun P.data gd (mapSegs P.data envPre 0).2).2).1)
            (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2).1 := by
    unfold progLayout; rw [hseg, layout_flat_append]
  rw [hpl] at hrs
  obtain ⟨rspre, rsGS, hpre, hGS, hsplit1⟩ := mapM_append_inv _ _ _ _ hrs
  rw [show (layout ((g, (compileFun P.data gd (mapSegs P.data envPre 0).2).1)
              :: (mapSegs P.data envSuf (compileFun P.data gd (mapSegs P.data envPre 0).2).2).1)
            (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2).1
        = (layoutItems (compileFun P.data gd (mapSegs P.data envPre 0).2).1
              (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2).1
          ++ (layout (mapSegs P.data envSuf (compileFun P.data gd (mapSegs P.data envPre 0).2).2).1
                (layoutItems (compileFun P.data gd (mapSegs P.data envPre 0).2).1
                  (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2).2.2).1
        from rfl] at hGS
  obtain ⟨rsg, rssuf, hg, hsuf, hsplit2⟩ := mapM_append_inv _ _ _ _ hGS
  refine ⟨rspre, rsg, rssuf, ?_, ?_, hg⟩
  · rw [hsplit1, hsplit2, List.flatten_append, List.flatten_append, List.append_assoc]
  · rw [resolve_length_layout _ _ _ (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0
          rspre hpre, layout_end, Nat.zero_add]

/-! ## Brick 3 — the `codeEnd`/`segStart` identity, `TabOk`, and the `fnPosOf` tie. -/

/-- Clean `lookup` on a matching head. (`beq_self_eq_true` on `String` is
    `Classical.choice`-tainted in this stdlib — its `ReflBEq` instance; `beq_iff_eq
    .mpr rfl` is the clean route.) -/
theorem lc_self {β} (k : Name) (v : β) (l : List (Name × β)) :
    List.lookup k ((k, v) :: l) = some v := by
  rw [List.lookup_cons, show (k == k) = true from beq_iff_eq.mpr rfl]

/-- Clean `lookup` skipping a non-matching head. -/
theorem lc_ne {β} (k k' : Name) (v : β) (l : List (Name × β)) (h : k ≠ k') :
    List.lookup k ((k', v) :: l) = List.lookup k l := by
  rw [List.lookup_cons, show (k == k') = false from by simpa using h]

/-- The resolved code's byte span equals `4·#instrs` (each resolved instruction is
    4 bytes). So `codeEnd = (progLayout).2.2.2 = 4·L.instrs.length`, hence
    `segStart = pad8 codeEnd`. -/
theorem instrs_len_codeEnd {P : Program} {entry : Name} {is : List Instr}
    {fnsF dats : List (Name × Nat)} (h : compileProgT P entry = some (is, fnsF, dats)) :
    4 * is.length = (progLayout P entry).2.2.2 := by
  obtain ⟨rs, hrs, hins, _, _⟩ := compileProgT_decomp h
  have := resolve_length_layout (progLayout P entry).2.1 (progLayout P entry).2.2.1
    (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data)
    (("", stubSeg entry) :: (mapSegs P.data P.env 0).1) 0 rs hrs
  rw [hins]
  unfold progLayout
  rw [this, layout_end, Nat.zero_add]

/-- Looking up a non-`""` key is unaffected by dropping the `""`-keyed entries
    (the `L.fnTab` filter): the first match is preserved. -/
theorem lookup_filter_ne {β} (f : Name) (hf : f ≠ "") :
    ∀ (l : List (Name × β)), List.lookup f (l.filter (fun x => x.1 != "")) = List.lookup f l := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : k = ""
    · subst hk
      rw [List.filter_cons_of_neg (by simp)]
      simp only [List.lookup_cons, (show (f == "") = false by simpa using hf)]
      exact ih
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [List.lookup_cons]
      cases hfk : f == k with
      | true => rfl
      | false => exact ih

/-- No `""`-keyed entry survives the `L.fnTab` filter, so `""` looks up to `none`. -/
theorem lookup_filter_empty {β} :
    ∀ (l : List (Name × β)), List.lookup "" (l.filter (fun x => x.1 != "")) = none := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : k = ""
    · subst hk; rw [List.filter_cons_of_neg (by simp)]; exact ih
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      have hbk : (("" : Name) == k) = false := by
        cases hb : (("" : Name) == k)
        · rfl
        · rw [beq_iff_eq] at hb; exact absurd hb.symm hk
      simp only [List.lookup_cons, hbk]
      exact ih

/-- **`TabOk`.** The compiler's function/data tables agree with `dposOf`/`fnPosOf`.
    The fn clause holds unconditionally: the stub sits first (`lookup "" = some 0`,
    matched by `fnPosOf … "" = 0`), and every other key survives the `L.fnTab`
    filter (`lookup_filter_ne`). The data clause is `dats = dataOffsetsFrom segStart`
    definitionally (`segStart = pad8 codeEnd`, `L.data = P.data`). -/
theorem tabOk_discharge {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    {dats : List (Name × Nat)}
    (hL : layoutOf P entry cb slo = some L)
    (hc : compileProgT P entry = some (L.instrs, L.fnTab, dats)) :
    TabOk (dposOf L) (fnPosOf L) (progLayout P entry).2.2.1 dats := by
  obtain ⟨_, _, hdata, hss, _⟩ := layoutOf_decomp hL
  obtain ⟨rs, hrs, hins, hfnt, hdats⟩ := compileProgT_decomp hc
  refine ⟨?_, ?_⟩
  · -- data clause
    intro d off hlk
    have hseg : L.segStart = pad8 (progLayout P entry).2.2.2 := by
      rw [hss, instrs_len_codeEnd hc]
    unfold dposOf
    rw [hdats] at hlk
    rw [hdata, hseg, hlk, Option.getD_some]
  · -- fn clause
    intro f p hlk
    by_cases hf : f = ""
    · subst hf
      -- the stub is the first fnTab entry: lookup "" (progLayout).2.2.1 = some 0
      have hfirst : (progLayout P entry).2.2.1 = ("", 0)
          :: (layout (mapSegs P.data P.env 0).1
                (layoutItems (stubSeg entry) 0).2.2).2.2.1 := rfl
      rw [hfirst, lc_self] at hlk
      have hp0 : p = 0 := by injection hlk with h; exact h.symm
      unfold fnPosOf
      rw [hfnt, lookup_filter_empty]
      exact hp0
    · -- non-stub key: survives the filter, so fnPosOf reads it back
      unfold fnPosOf
      rw [hfnt, lookup_filter_ne f hf, hlk, Option.getD_some]

/-! ### The `fnPosOf` tie: g's fnTab entry is its layout byte position. -/

/-- A successful `lookup` splits the list at the FIRST occurrence of the key
    (nothing before it shares the key). -/
theorem lookup_split {β} (k : Name) :
    ∀ (l : List (Name × β)) (v : β), List.lookup k l = some v →
      ∃ pre suf, l = pre ++ (k, v) :: suf ∧ k ∉ pre.map Prod.fst := by
  intro l
  induction l with
  | nil => intro v h; simp [List.lookup] at h
  | cons x rest ih =>
    intro v h
    obtain ⟨k', v'⟩ := x
    by_cases hkk : k = k'
    · subst hkk
      rw [lc_self] at h
      injection h with hv; subst hv
      exact ⟨[], rest, rfl, by simp⟩
    · rw [lc_ne k k' v' rest hkk] at h
      obtain ⟨pre, suf, hl, hn⟩ := ih v h
      refine ⟨(k', v') :: pre, suf, by rw [hl]; rfl, ?_⟩
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨hkk, hn⟩

/-- `mapSegs` preserves the segment names (each segment is `(nf.1, …)`). -/
theorem mapSegs_keys (dat : Data) : ∀ (env : List (Name × FunDef)) (c : Nat),
    (mapSegs dat env c).1.map Prod.fst = env.map Prod.fst := by
  intro env
  induction env with
  | nil => intro c; rfl
  | cons nf rest ih =>
    intro c; rw [mapSegs_cons]; simp only [List.map_cons]; rw [ih]

/-- If a key is not among the segment names, it does not resolve in the layout
    function table. -/
theorem layout_fns_lookup_none (g : Name) :
    ∀ (segs : List (Name × List SymInstr)) (pos : Nat),
      g ∉ segs.map Prod.fst → List.lookup g (layout segs pos).2.2.1 = none := by
  intro segs
  induction segs with
  | nil => intro pos _; rfl
  | cons s rest ih =>
    intro pos hg
    obtain ⟨n, items⟩ := s
    simp only [List.map_cons, List.mem_cons, not_or] at hg
    obtain ⟨hne, hrest⟩ := hg
    show List.lookup g ((n, pos) :: (layout rest (layoutItems items pos).2.2).2.2.1) = none
    have hbn : (g == n) = false := by
      cases hb : g == n
      · rfl
      · rw [beq_iff_eq] at hb; exact absurd hb hne
    simp only [List.lookup_cons, hbn]
    exact ih (layoutItems items pos).2.2 hrest

/-- **The `fnPosOf` tie.** For a function `g` at its FIRST env occurrence
    `envPre ++ (g,gd) :: envSuf` (`g ∉ envPre` names, `g ≠ ""`), the `fnPosOf`
    table position IS the layout byte position of g's segment — the input the
    `hfn`/`hem` `Emitted` slice is stated at. -/
theorem fnPosOf_tie {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    {dats : List (Name × Nat)}
    (hL : layoutOf P entry cb slo = some L)
    (hc : compileProgT P entry = some (L.instrs, L.fnTab, dats))
    (envPre envSuf : List (Name × FunDef)) (g : Name) (gd : FunDef) (hg : g ≠ "")
    (hE : P.env = envPre ++ (g, gd) :: envSuf)
    (hnp : g ∉ envPre.map Prod.fst) :
    fnPosOf L g = (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2 := by
  obtain ⟨rs, hrs, hins, hfnt, hdats⟩ := compileProgT_decomp hc
  have hseg : ("", stubSeg entry) :: (mapSegs P.data P.env 0).1
      = (("", stubSeg entry) :: (mapSegs P.data envPre 0).1)
        ++ (g, (compileFun P.data gd (mapSegs P.data envPre 0).2).1)
           :: (mapSegs P.data envSuf (compileFun P.data gd (mapSegs P.data envPre 0).2).2).1 := by
    rw [hE, (mapSegs_append P.data envPre ((g, gd) :: envSuf) 0).1, mapSegs_cons, List.cons_append]
  have hfns : (progLayout P entry).2.2.1
      = (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.1
        ++ (g, (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2)
           :: (layout (mapSegs P.data envSuf (compileFun P.data gd (mapSegs P.data envPre 0).2).2).1
                 (layoutItems (compileFun P.data gd (mapSegs P.data envPre 0).2).1
                   (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2).2.2).2.2.1 := by
    unfold progLayout; rw [hseg, layout_fns_append]; rfl
  have hkeys : g ∉ (("", stubSeg entry) :: (mapSegs P.data envPre 0).1).map Prod.fst := by
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨hg, by rw [mapSegs_keys]; exact hnp⟩
  unfold fnPosOf
  rw [hfnt, hfns, List.filter_append,
      List.filter_cons_of_pos (by simpa using hg), List.lookup_append,
      lookup_filter_ne g hg, layout_fns_lookup_none g _ 0 hkeys, Option.none_or,
      lc_self, Option.getD_some]

/-! ## Brick 4 — the per-function `Emitted` assembly (the `hfn`/`hem` payload). -/

/-- `Emitted` from a positional slice of `L.instrs`: if `L.instrs = A ++ B ++ C`
    with `|A| = pos/4` and `pos` 4-aligned, then `B` is emitted at `pos`. -/
theorem Emitted_of_slice (L : Layout) (pos : Nat) (A B C : List Instr)
    (hpos : pos % 4 = 0) (hA : A.length = pos / 4) (hinstrs : L.instrs = A ++ B ++ C) :
    Emitted L pos B := by
  refine ⟨hpos, fun j hj => ?_⟩
  have hi : pos / 4 + j = A.length + j := by rw [hA]
  have hidx : pos / 4 + j < L.instrs.length := by
    rw [hinstrs, hi]; simp only [List.length_append]; omega
  refine ⟨hidx, ?_⟩
  rw [List.getElem_of_eq hinstrs hidx,
      List.getElem_append_left (show pos / 4 + j < (A ++ B).length by
        simp only [List.length_append]; omega),
      List.getElem_append_right (show A.length ≤ pos / 4 + j by omega)]
  congr 1
  omega

/-- **Brick 4 (the payoff).** Each function `g` at its first env occurrence
    (`g ∉ envPre`, `g ≠ ""`, body `wf`) is `Emitted` at its `fnPosOf` position as
    `prologueI gd ++ emitCF … gd.body ++ epilogueI gd` — the `hfn`/`hem` `Emitted`
    payload `lower_sim_cf`/`prog_sim` consume. Composes the flat resolve slice
    (Brick 2) + `compileFun_resolves` (label premises via `env_fn_lbls_discharge`,
    tables via `tabOk_discharge`) + the `fnPosOf` tie (Brick 3). -/
theorem fn_emitted {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    {dats : List (Name × Nat)}
    (hL : layoutOf P entry cb slo = some L)
    (hc : compileProgT P entry = some (L.instrs, L.fnTab, dats))
    (envPre envSuf : List (Name × FunDef)) (g : Name) (gd : FunDef) (hg : g ≠ "")
    (hE : P.env = envPre ++ (g, gd) :: envSuf)
    (hnp : g ∉ envPre.map Prod.fst)
    (hwf : LowIR.Prog.wf P 0 0 gd.body = true) :
    Emitted L (fnPosOf L g)
      (prologueI gd
        ++ emitCF P.data (dposOf L) (fnPosOf L) [] []
             (fnPosOf L g + 4 * prologueSize gd + 4 * csize gd.body)
             (fnPosOf L g + 4 * prologueSize gd) gd.body
        ++ epilogueI gd) := by
  obtain ⟨rs, hrs, hins, hfnt, hdats⟩ := compileProgT_decomp hc
  obtain ⟨pre, rsg, suf, hflat, hlen, hgres⟩ := fn_resolve_slice envPre envSuf g gd hE hrs
  have htie := fnPosOf_tie hL hc envPre envSuf g gd hg hE hnp
  have htab := tabOk_discharge hL hc
  rw [hdats] at htab
  obtain ⟨hepi, hlc⟩ := env_fn_lbls_discharge P.data envPre envSuf (stubSeg entry)
    (labelIds_stubSeg entry) g gd
  rw [← hE] at hepi hlc
  have hpay := compileFun_resolves P.data P (dposOf L) (fnPosOf L)
    (progLayout P entry).2.1 (progLayout P entry).2.2.1
    (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data) htab gd
    (mapSegs P.data envPre 0).2
    (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2
    rsg hgres hwf hepi hlc
  have hinstrs : L.instrs = pre.flatten ++ rsg.flatten ++ suf.flatten := by rw [hins]; exact hflat
  have hpp4 : (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2 % 4 = 0 := by
    omega
  have hApp : pre.flatten.length
      = (layout (("", stubSeg entry) :: (mapSegs P.data envPre 0).1) 0).2.2.2 / 4 := by omega
  have hslice := Emitted_of_slice L _ pre.flatten rsg.flatten suf.flatten hpp4 hApp hinstrs
  rw [hpay] at hslice
  rw [htie]
  exact hslice

/-! ## The full per-function `hfn` bundle (the `lower_sim_cf`/`prog_sim` hypothesis).

    `fn_emitted` (Brick 4) gives conjunct 1 (`Emitted`). The remaining five come
    from: the tightened compiler guards (`wf`, `≠ ""`, `totalFrame ≤ 2000`,
    `frameSize % 8 = 0` — extracted here), the layout tie (`fnPos % 4 = 0`), and
    the single program-level blob bound `4·|L.instrs| < 2²⁰` (the `< 2²⁰` end
    position). `BranchOk gd.body` is threaded as a per-program structural
    hypothesis — the same shape `lower_sim_cf` itself carries as `hbr`, and
    `decide`-checkable for any concrete program (branches that don't fit make the
    real `Compile` return `none`). -/

/-- `wfProgram P` from a successful compile (the guard's FIRST clause). -/
theorem compileProgT_wfProgram {P : Program} {entry : Name} {t}
    (h : compileProgT P entry = some t) : LowIR.Prog.wfProgram P = true := by
  unfold compileProgT at h
  cases hg : (LowIR.Prog.wfProgram P && P.env.all (fun nf => LowIR.Compile.fnOk nf.2)
       && (List.lookup entry P.env).isSome
       && P.data.all (fun d => d.2.length < 2 ^ 22)) with
  | false => rw [hg] at h; simp at h
  | true => simp only [Bool.and_eq_true] at hg; exact hg.1.1.1

/-- `P.env.all fnOk` from a successful compile (the guard's SECOND clause). -/
theorem compileProgT_fnOkAll {P : Program} {entry : Name} {t}
    (h : compileProgT P entry = some t) : P.env.all (fun nf => fnOk nf.2) = true := by
  unfold compileProgT at h
  cases hg : (LowIR.Prog.wfProgram P && P.env.all (fun nf => LowIR.Compile.fnOk nf.2)
       && (List.lookup entry P.env).isSome
       && P.data.all (fun d => d.2.length < 2 ^ 22)) with
  | false => rw [hg] at h; simp at h
  | true => simp only [Bool.and_eq_true] at hg; exact hg.1.1.2

/-- The entry function is present in the env (the guard's THIRD clause). -/
theorem compileProgT_entry {P : Program} {entry : Name} {t}
    (h : compileProgT P entry = some t) : ∃ fd, List.lookup entry P.env = some fd := by
  unfold compileProgT at h
  cases hg : (LowIR.Prog.wfProgram P && P.env.all (fun nf => LowIR.Compile.fnOk nf.2)
       && (List.lookup entry P.env).isSome
       && P.data.all (fun d => d.2.length < 2 ^ 22)) with
  | false => rw [hg] at h; simp at h
  | true =>
      simp only [Bool.and_eq_true] at hg
      exact Option.isSome_iff_exists.mp hg.1.2

/-- Per-function facts pulled from the tightened guards for `(g, gd) ∈ P.env`:
    body `wf`, name non-empty, `totalFrame ≤ 2000`, `frameSize % 8 = 0`. -/
theorem fn_guard_facts {P : Program} {entry : Name} {t} {g : Name} {gd : FunDef}
    (hc : compileProgT P entry = some t) (hmem : (g, gd) ∈ P.env) :
    LowIR.Prog.wf P 0 0 gd.body = true ∧ g ≠ "" ∧ totalFrame gd ≤ 2000
      ∧ gd.frameSize % 8 = 0 := by
  have hall := compileProgT_fnOkAll hc
  have hwfP := compileProgT_wfProgram hc
  have hok : fnOk gd = true := by
    have := (List.all_eq_true.mp hall) (g, gd) hmem; simpa using this
  simp only [fnOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  rw [LowIR.Prog.wfProgram, Bool.and_eq_true] at hwfP
  have hwfnf : (LowIR.Prog.wf P 0 0 gd.body
                 && !(gd.params.toList.contains gd.frameReg) && g != "") = true := by
    have := (List.all_eq_true.mp hwfP.1) (g, gd) hmem; simpa using this
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hwfnf
  exact ⟨hwfnf.1.1, hwfnf.2, hok.1.2, hok.2⟩

/-- The resolved epilogue has exactly `rvc + 3` instructions (`rets` has `rvc`
    entries, each a single `loadSlotI`, plus the `ld`/`addi`/`jalr` tail). -/
theorem epilogueI_length (fd : FunDef) : (epilogueI fd).length = epilogueSize fd := by
  have hfm : ∀ (l : List (Reg × Nat)),
      (l.flatMap (fun ri => loadSlotI ri.1 (A ri.2))).length = l.length := by
    intro l; induction l with
    | nil => rfl
    | cons x t ih =>
        rw [List.flatMap_cons, List.length_append, ih, loadSlotI_length, List.length_cons]; omega
  unfold epilogueI epilogueSize
  rw [List.length_append, hfm, List.length_zipIdx]
  simp only [List.length_cons, List.length_nil]
  have : fd.rets.toList.length = fd.rvc := by simp
  omega

/-- **The full `hfn` bundle** — for every function of a successfully-compiled
    program, the six-conjunct fact `lower_sim_cf`/`prog_sim` take as `hfn`. -/
theorem fn_hfn {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    {dats : List (Name × Nat)}
    (hL : layoutOf P entry cb slo = some L)
    (hc : compileProgT P entry = some (L.instrs, L.fnTab, dats))
    (hcode : 4 * L.instrs.length < 2 ^ 20)
    (hbr : ∀ g gd, List.lookup g P.env = some gd → BranchOk gd.body)
    (g : Name) (gd : FunDef) (hlk : List.lookup g P.env = some gd) :
    Emitted L (fnPosOf L g)
        (prologueI gd
          ++ emitCF P.data (dposOf L) (fnPosOf L) [] []
               (fnPosOf L g + 4 * prologueSize gd + 4 * csize gd.body)
               (fnPosOf L g + 4 * prologueSize gd) gd.body
          ++ epilogueI gd)
      ∧ fnPosOf L g + 4 * prologueSize gd + 4 * csize gd.body + 4 * epilogueSize gd < 2 ^ 20
      ∧ BranchOk gd.body
      ∧ totalFrame gd ≤ 2000
      ∧ gd.frameSize % 8 = 0
      ∧ fnPosOf L g % 4 = 0
      ∧ 8 ≤ fnPosOf L g := by
  obtain ⟨pre, suf, hE, hnp⟩ := lookup_split g P.env gd hlk
  have hmem : (g, gd) ∈ P.env := by rw [hE]; simp
  obtain ⟨hwf, hg, htf, hfs⟩ := fn_guard_facts hc hmem
  -- conjunct 1 (Brick 4)
  have hEmit := fn_emitted hL hc pre suf g gd hg hE hnp hwf
  -- re-derive the slice + resolved payload for the position/length arithmetic
  obtain ⟨rs, hrs, hins, hfnt, hdats'⟩ := compileProgT_decomp hc
  obtain ⟨preF, rsg, sufF, hflat, hlen, hgres⟩ := fn_resolve_slice pre suf g gd hE hrs
  have htie := fnPosOf_tie hL hc pre suf g gd hg hE hnp
  have htab := tabOk_discharge hL hc
  rw [hdats'] at htab
  obtain ⟨hepi, hlc⟩ := env_fn_lbls_discharge P.data pre suf (stubSeg entry)
    (labelIds_stubSeg entry) g gd
  rw [← hE] at hepi hlc
  have hpay := compileFun_resolves P.data P (dposOf L) (fnPosOf L)
    (progLayout P entry).2.1 (progLayout P entry).2.2.1
    (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data) htab gd
    (mapSegs P.data pre 0).2
    (layout (("", stubSeg entry) :: (mapSegs P.data pre 0).1) 0).2.2.2
    rsg hgres hwf hepi hlc
  -- fnPos = 4·|preF.flatten|  (tie + resolve length)
  have hpos : fnPosOf L g = 4 * preF.flatten.length := by rw [htie, ← hlen]
  -- |rsg.flatten| = prologueSize + csize body + epilogueSize
  have hrsglen : rsg.flatten.length = prologueSize gd + csize gd.body + epilogueSize gd := by
    rw [hpay, List.length_append, List.length_append, emitCF_length, epilogueI_length]; rfl
  -- preF + rsg fit inside L.instrs
  have hfit : preF.flatten.length + rsg.flatten.length ≤ L.instrs.length := by
    rw [hins, hflat, List.length_append, List.length_append]; omega
  -- conjunct 7: 8 ≤ fnPos (the stub occupies the first 8 bytes, so every
  -- function starts at ≥ 8 — `fnPos = layout-end of stub++envPre segments`).
  have hstubsplit :
      totalSymSize ((("", stubSeg entry) :: (mapSegs P.data pre 0).1).flatMap Prod.snd)
        = totalSymSize (stubSeg entry)
          + totalSymSize ((mapSegs P.data pre 0).1.flatMap Prod.snd) := by
    rw [List.flatMap_cons, totalSymSize_append]
  have hstubval : totalSymSize (stubSeg entry) = 8 := rfl
  have h8 : 8 ≤ fnPosOf L g := by rw [htie, layout_end, hstubsplit]; omega
  refine ⟨hEmit, ?_, hbr g gd hlk, htf, hfs, ?_, h8⟩
  · -- conjunct 2: the < 2²⁰ end bound (fnPos = 4·preF, and preF+rsg ≤ instrs)
    rw [hpos]; omega
  · -- conjunct 6: fnPos % 4 = 0
    rw [hpos]; omega

/-! ## The entry-stub `Emitted` (`hem`) — the `[jal ra entry; jal0]` at position 0.

    `compileProgT` prepends `("", stubSeg entry)`; resolved, its two items are the
    initial call `jal ra, entry` (`.callf entry` → `jal RA (ofInt 21 (fnPosOf L
    entry))`) and the halt self-loop `jal x0, 0` (`.ins (jal0 0)`). `prog_sim`
    steps the first to enter `entry` (ra := codeBase+4) and spins on the second
    at the halt PC `codeBase + 4`. -/

/-- `mapM`-resolving a single NON-label positioned item: its layout is `[(pos,
    si)]`, so the result is `[v]` with `resolveOne … (pos, si) = some v`. -/
theorem mapM_single_nonlabel (lbls fns dats : List _) (pos : Nat) (si : SymInstr)
    (r : List (List Instr)) (hne : ∀ l, si ≠ .label l)
    (h : (layoutItems [si] pos).1.mapM (resolveOne lbls fns dats) = some r) :
    ∃ v, resolveOne lbls fns dats (pos, si) = some v ∧ r = [v] := by
  have hli : (layoutItems [si] pos).1 = [(pos, si)] := by
    cases si with
    | label l => exact absurd rfl (hne l)
    | _ => rfl
  rw [hli, List.mapM_cons] at h
  cases hf : resolveOne lbls fns dats (pos, si) with
  | none =>
      rw [hf] at h
      replace h : (none : Option (List (List Instr))) = some r := h
      simp at h
  | some v =>
      rw [hf] at h
      replace h : (some [v] : Option (List (List Instr))) = some r := h
      exact ⟨v, rfl, (Option.some.inj h).symm⟩

/-- **The entry-stub `Emitted` (`hem`).** The resolved stub `[jal ra entry;
    jal x0 0]` is the length-2 prefix of `L.instrs`, emitted at position 0. -/
theorem stub_emitted {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    {dats : List (Name × Nat)}
    (hL : layoutOf P entry cb slo = some L)
    (hc : compileProgT P entry = some (L.instrs, L.fnTab, dats)) :
    Emitted L 0 [Instr.jal RA (BitVec.ofInt 21 (fnPosOf L entry : Int)), jal0 0] := by
  -- entry is a real, non-empty function name (guards)
  obtain ⟨fd, hlk⟩ := compileProgT_entry hc
  obtain ⟨preE, sufE, hEE, _⟩ := lookup_split entry P.env fd hlk
  have hmemE : (entry, fd) ∈ P.env := by rw [hEE]; simp
  obtain ⟨_, hentry, _, _⟩ := fn_guard_facts hc hmemE
  -- decompose the resolve; peel the stub prefix off progLayout.1
  obtain ⟨rs, hrs, hins, hfnt, _⟩ := compileProgT_decomp hc
  have hpl1 : (progLayout P entry).1
      = (layoutItems (stubSeg entry) 0).1
        ++ (layout (mapSegs P.data P.env 0).1 (layoutItems (stubSeg entry) 0).2.2).1 := rfl
  rw [hpl1] at hrs
  obtain ⟨rsStub, rsRest, hStub, _, hsplit⟩ := mapM_append_inv _ _ _ _ hrs
  -- split the stub segment into its two items
  obtain ⟨ra, rb, hra, hrb, hflat⟩ :=
    resolve_flatten_append _ _ _ [SymInstr.callf entry] [SymInstr.ins (jal0 0)] 0 rsStub hStub
  -- second item: `.ins (jal0 0)` → `[jal0 0]`
  obtain ⟨vb, hvb, hrbEq⟩ := mapM_single_nonlabel _ _ _ _ _ rb (by simp) hrb
  rw [show resolveOne (progLayout P entry).2.1 (progLayout P entry).2.2.1
        (dataOffsetsFrom (pad8 (progLayout P entry).2.2.2) P.data)
        (0 + totalSymSize [SymInstr.callf entry], SymInstr.ins (jal0 0)) = some [jal0 0] from rfl]
      at hvb
  obtain rfl := Option.some.inj hvb
  -- first item: `.callf entry` → `jal RA (ofInt 21 (fnPosOf L entry))`
  obtain ⟨va, hva, hraEq⟩ := mapM_single_nonlabel _ _ _ _ _ ra (by simp) hra
  -- the fn-table lookup: entry sits at `fnPosOf L entry`
  cases hlk0 : List.lookup entry (progLayout P entry).2.2.1 with
  | none => simp [resolveOne, hlk0] at hva
  | some tgt =>
      have hfp : fnPosOf L entry = tgt := by
        unfold fnPosOf; rw [hfnt, lookup_filter_ne entry hentry, hlk0]; rfl
      simp only [resolveOne, hlk0, bind, Option.bind] at hva
      split at hva
      · -- range check passed: va = [jal RA (ofInt 21 (tgt - 0))]
        have hva' : va = [Instr.jal RA (BitVec.ofInt 21 (fnPosOf L entry : Int))] := by
          have hval := (Option.some.inj hva).symm
          have hc : ((tgt : Int) - ((0 : Nat) : Int)) = ((fnPosOf L entry : Nat) : Int) := by omega
          rw [hval, hc]
        -- assemble: L.instrs = [] ++ [jal RA …, jal0 0] ++ rsRest.flatten
        refine Emitted_of_slice L 0 [] _ rsRest.flatten (by simp) (by simp) ?_
        rw [hins, hsplit, List.flatten_append, hflat, hraEq, hrbEq, hva']
        simp
      · exact absurd hva (by simp)

end LowIR.ProgSim.LayoutFacts
