/-
  LowIR.ProgSim.CtrlSim — the label-aware lowering `emitCF` and its size `csize`,
  the position/label-resolved extension of `emit` to control flow.

  `emit` (StmtSim) is label-free and returns `[]` for the control-flow ops. This
  file resolves them: given the enclosing break/continue label POSITIONS
  (`brkPos`/`contPos`), the epilogue position (`epiPos`), and the byte offset
  `here` where this statement's code begins, `emitCF` produces the concrete RV64I
  stream the real `Compile.lower ▸ layout ▸ resolveOne` pipeline emits — every
  `.jmp`/`.br` a single `jal x0`/branch whose offset is `target − here`, every
  label 0 bytes. The internal `ife`/`while` label offsets are position-INDEPENDENT
  (they depend only on sub-block sizes, `csize`); only `ret`/`brkB`/`contL` targets
  (external labels) depend on `here`.

  This is the label-aware `emit` the outcome-carrying `lower_sim` (next) inducts
  over — and the seed of the validated IR↔assembly mapping (Dump.lean renders the
  tree; `emitCF`/`csize` annotate it with byte positions).
-/
import LowIR.ProgSim.StmtSim
import LowIR.ProgLib

namespace LowIR.ProgSim

open Rv64i (Instr State step Word)
open LowIR.Compile (T0 T1 userOff slotOff maxRegF maxRegS)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (St Program Name FunDef dbaseOf)

local notation "PStmt" => LowIR.Prog.Stmt

/-- Instruction count of a statement's lowering — position/label-independent
    (every jump/branch is one 4-byte instruction, every label 0 bytes). The
    straight-line cases delegate to `emit` (already `#guard`'d faithful to
    `Compile.lower`); the control-flow overheads are read off the compiler's
    layout: `ife` = 2 slot-loads + branch + jmp (4), `while` = +1 back-edge (5).
    `cref`/`clen` are `0` here (placeholder — `emit` still stubs them). -/
def csize : PStmt → Nat
  | .seq a b        => csize a + csize b
  | .ret            => 1
  | .brkB _         => 1
  | .contL _        => 1
  | .block body     => csize body
  | .ife _ _ _ t e  => 4 + csize e + csize t
  | .while _ _ _ b  => 5 + csize b
  | s               => (emit s).length

/-- The label-aware lowering. `brkPos`/`contPos` are the enclosing block-end /
    loop-top label byte positions (indexed like `brkB`/`contL`'s de-Bruijn
    indices); `epiPos` the epilogue; `here` the byte offset of this code.
    Straight-line cases reuse `emit` (`here` irrelevant). -/
def emitCF (brkPos contPos : List Nat) (epiPos : Nat) : Nat → PStmt → List Instr
  | here, .seq a b =>
      emitCF brkPos contPos epiPos here a ++
        emitCF brkPos contPos epiPos (here + 4 * csize a) b
  | here, .ret     => [LowIR.jal0 ((epiPos : Int) - (here : Int))]
  | here, .brkB k  => [LowIR.jal0 ((brkPos.getD k 0 : Int) - (here : Int))]
  | here, .contL k => [LowIR.jal0 ((contPos.getD k 0 : Int) - (here : Int))]
  | here, .block body =>
      -- the break target `lEnd` sits just past the body (0-byte label).
      emitCF ((here + 4 * csize body) :: brkPos) contPos epiPos here body
  | here, .ife c a b t e =>
      -- br→lT (then) skips over the else block; jmp→lEnd skips over then.
      -- offsets are size-relative: lT is 8 + 4|e| past the branch, lEnd 4 + 4|t|
      -- past the jmp. else code `e` runs on fall-through (at here+12), then `t`.
      loadSlotI a T0 ++ loadSlotI b T1
        ++ [LowIR.condInstr c T0 T1 (8 + 4 * csize e)]
        ++ emitCF brkPos contPos epiPos (here + 12) e
        ++ [LowIR.jal0 (4 + 4 * csize t)]
        ++ emitCF brkPos contPos epiPos (here + 16 + 4 * csize e) t
  | here, .while c a b body =>
      -- lTop = here (0-byte label); br→lBody (+8) enters, jmp→lEnd exits, the
      -- body runs a continue-scope (lTop::contPos), then the back-edge to lTop.
      loadSlotI a T0 ++ loadSlotI b T1
        ++ [LowIR.condInstr c T0 T1 8, LowIR.jal0 (8 + 4 * csize body)]
        ++ emitCF brkPos (here :: contPos) epiPos (here + 16) body
        ++ [LowIR.jal0 (-(16 + 4 * csize body : Int))]
  | _, s => emit s

/-- `emitCF`'s length is exactly `csize` — position/label-independent, as claimed.
    Needed by the outcome-carrying `lower_sim` to place `seq`'s second half and to
    read the fall-through position. -/
theorem emitCF_length (bp cp : List Nat) (ep here : Nat) (stmt : PStmt) :
    (emitCF bp cp ep here stmt).length = csize stmt := by
  induction stmt generalizing bp cp ep here with
  | seq a b iha ihb =>
      simp only [emitCF, csize, List.length_append, iha, ihb]
  | ret => rfl
  | brkB k => rfl
  | contL k => rfl
  | block body ih =>
      simp only [emitCF, csize]; rw [ih]
  | ife c a b t e iht ihe =>
      simp only [emitCF, csize, List.length_append, List.length_cons,
                 List.length_nil, loadSlotI_length, iht, ihe]
      omega
  | «while» c a b body ih =>
      simp only [emitCF, csize, List.length_append, List.length_cons,
                 List.length_nil, loadSlotI_length, ih]
      omega
  | _ => rfl

/-- Sanity: on the straight-line fragment, `emitCF` is exactly `emit` (the
    control-flow arms never fire), so all the existing `#guard`s against
    `Compile.lower` carry over unchanged. -/
example (bp cp : List Nat) (ep here : Nat) :
    emitCF bp cp ep here (.addi 12 5 (BitVec.ofNat 12 3)) = emit (.addi 12 5 (BitVec.ofNat 12 3)) :=
  rfl

/-! ## Validation against the real compiler pipeline.

    `emitCF` must equal what the trusted `Compile.lower ▸ layoutItems ▸ resolveOne`
    actually emits. `realResolve` runs that pipeline on a statement (no data, no
    outer scopes, from byte 0), and the `#guard`s check equality on the library's
    control-flow functions — the concrete, decidable "validated mapping". -/
open LowIR.Compile (lower layoutItems resolveOne)

/-- The real resolved RV64I stream for a body, lowered in isolation from byte 0.
    Epilogue label `0` (targeted by `ret`) is planted just past the body — its
    position is `4·csize body` — and `fresh` is seeded from `1` so internal labels
    can't collide with it. So `emitCF` must be compared with `epiPos = 4·csize`. -/
def realResolve (body : PStmt) : Option (List Instr) :=
  let syms : List LowIR.Compile.SymInstr := (lower [] [] [] 0 body).run' 1
  let (flat, lbls, _) := layoutItems (syms ++ [LowIR.Compile.SymInstr.label 0]) 0
  (flat.mapM (fun p => resolveOne lbls [] [] p)).map List.flatten

/-- `emitCF` matched against the real pipeline, epilogue at the body's end. -/
def matchesReal (body : PStmt) : Bool :=
  realResolve body == some (emitCF [] [] (4 * csize body) 0 body)

-- `strlen` (`while`), `strtoull` (`block`+`while`+`ife`+`brkB`), `hex0` (nested
-- `ife`s + `while` + `ret`): the validated IR↔assembly mapping, checked concretely.
#guard matchesReal LowIR.Prog.Lib.strlenF.body
#guard matchesReal LowIR.Prog.Lib.strtoullF.body
#guard matchesReal LowIR.Prog.Lib.hex0F.body
#guard matchesReal LowIR.Prog.Lib.hex1F.body

/-! ## The outcome-carrying `lower_sim`.

    Where `emit`'s `lower_sim` (StmtSim) is `.normal`-only and lands at the
    fall-through, this carries the `Outcome`: the machine lands at
    `codeBase + landPos(outcome)` — fall-through for `.normal`, the resolved
    break/continue/epilogue label for `.brk`/`.cont`/`.ret`. It inducts over
    `emitCF` with the label-position environment (`brkPos`/`contPos`/`epiPos`).

    `block` is the first compound case (this file): it adds no machine code of its
    own (the `lEnd` label is 0 bytes), so its trace IS the body's trace — the whole
    proof is the IH on `body` with `lEnd` pushed on the break stack, then a
    case-walk on the body outcome showing the landing positions coincide (`.brk 0`
    lands at `lEnd` = block fall-through; deeper `.brk`/`.cont`/`.ret` propagate). -/

/-- Where the machine lands for each outcome: fall-through `ft` for `.normal`, the
    resolved break/continue label for `.brk k`/`.cont k`, the epilogue for `.ret`. -/
def landPos (brkPos contPos : List Nat) (epiPos ft : Nat) : Outcome → Nat
  | .normal => ft
  | .brk k  => brkPos.getD k 0
  | .cont k => contPos.getD k 0
  | .ret    => epiPos

/-- Every label position fits the 21-bit `jal`/branch offset window (from byte 0,
    so target − here ∈ (−2²⁰, 2²⁰) whenever both ends are `< 2²⁰`). -/
def LabelsOk (brkPos contPos : List Nat) (epiPos : Nat) : Prop :=
  (∀ p ∈ brkPos, p < 2 ^ 20) ∧ (∀ p ∈ contPos, p < 2 ^ 20) ∧ epiPos < 2 ^ 20

/-- A `getD` into an all-bounded list is bounded (the default `0` is too). Used to
    keep `brkB`/`contL`'s jump target inside the offset window. -/
theorem getD_lt (l : List Nat) (k b : Nat) (hb : 0 < b) (h : ∀ p ∈ l, p < b) :
    l.getD k 0 < b := by
  induction l generalizing k with
  | nil => simpa using hb
  | cons x t ih =>
    cases k with
    | zero => simpa using h x (by simp)
    | succ k => simpa using ih k (fun p hp => h p (by simp [hp]))

theorem lower_sim_cf
    {P : Program} {dbase : Name → Option Word} {pad : Name → Nat} {stackLo : Word}
    {L : Layout} {fd : FunDef} {holes : List Hole} {epiPos : Nat}
    (fuel : Nat) (stmt : PStmt) (s s' : St) (oc : Outcome) (m : State)
    (here : Nat) (brkPos contPos : List Nat)
    (hexec : LowIR.Prog.exec P dbase pad stackLo fuel stmt s = some (s', oc))
    (hinv  : StInv L fd holes s m)
    (hpc   : m.pc = L.codeBase + BitVec.ofNat 64 here)
    (hem   : Emitted L here (emitCF brkPos contPos epiPos here stmt))
    (hreg  : maxRegS stmt ≤ maxRegF fd)
    (hnw   : s.sp.toNat + userOff fd ≤ 2 ^ 64)
    (hbd   : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
               ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat)
    (haccess : MemAccOff L holes P dbase pad stackLo fuel stmt s)
    (hlbl  : LabelsOk brkPos contPos epiPos)
    (hbnd  : here + 4 * csize stmt < 2 ^ 20)
    (hframe : userOff fd ≤ 2000)
    (hseg  : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64) :
    ∃ k, StInv L fd holes s' (stepN k m)
       ∧ (stepN k m).pc = L.codeBase
           + BitVec.ofNat 64 (landPos brkPos contPos epiPos (here + 4 * csize stmt) oc) := by
  induction fuel generalizing stmt s s' oc m here brkPos contPos with
  | zero => exact absurd hexec (by simp [LowIR.Prog.exec])
  | succ fuel ih =>
    cases stmt
    case skip =>
      rw [LowIR.Prog.exec_skip, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      exact ⟨0, hinv, by simp only [stepN_zero, csize, emit, List.length_nil, Nat.mul_zero,
                                    Nat.add_zero, landPos]; exact hpc⟩
    case annot a =>
      rw [LowIR.Prog.exec_annot, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      exact ⟨0, hinv, by simp only [stepN_zero, csize, emit, List.length_nil, Nat.mul_zero,
                                    Nat.add_zero, landPos]; exact hpc⟩
    case block body =>
      -- csize/emitCF/MemAccOff for `.block body` reduce to `body` with `lEnd` pushed.
      have hbnd' : here + 4 * csize body < 2 ^ 20 := hbnd
      have hlEnd : here + 4 * csize body < 2 ^ 20 := hbnd
      have hlbl' : LabelsOk ((here + 4 * csize body) :: brkPos) contPos epiPos := by
        obtain ⟨hb, hc, he⟩ := hlbl
        refine ⟨fun p hp => ?_, hc, he⟩
        rcases List.mem_cons.mp hp with h | h
        · exact h ▸ hlEnd
        · exact hb p h
      -- `csize`/`emitCF`/`MemAccOff`/`maxRegS` on `.block body` are defeq to the
      -- `body` forms; rebind so the elaborator unfolds them.
      have hem' : Emitted L here (emitCF ((here + 4 * csize body) :: brkPos) contPos epiPos here body)
        := hem
      have hreg' : maxRegS body ≤ maxRegF fd := hreg
      have hacc' : MemAccOff L holes P dbase pad stackLo fuel body s := by
        simpa only [MemAccOff] using haccess
      cases hb : LowIR.Prog.exec P dbase pad stackLo fuel body s with
      | none =>
          rw [LowIR.Prog.exec_block_none P dbase pad stackLo fuel body s hb] at hexec
          simp at hexec
      | some pr =>
          obtain ⟨s'', ocb⟩ := pr
          obtain ⟨k, hst, hpck⟩ :=
            ih body s s'' ocb m here ((here + 4 * csize body) :: brkPos) contPos
              hb hinv hpc hem' hreg' hnw hbd hacc' hlbl' hbnd'
          cases ocb with
          | normal =>
              rw [LowIR.Prog.exec_block_normal P dbase pad stackLo fuel body s s'' hb,
                  Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl⟩ := hexec
              exact ⟨k, hst, by rw [hpck]; simp only [csize, landPos]⟩
          | brk kk =>
              cases kk with
              | zero =>
                  rw [LowIR.Prog.exec_block_catch P dbase pad stackLo fuel body s s'' hb,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨k, hst, by rw [hpck]; simp only [csize, landPos, List.getD_cons_zero]⟩
              | succ kk' =>
                  rw [LowIR.Prog.exec_block_brkS P dbase pad stackLo fuel body s s'' kk' hb,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨k, hst, by rw [hpck]; simp only [landPos, List.getD_cons_succ]⟩
          | cont kk =>
              rw [LowIR.Prog.exec_block_cont P dbase pad stackLo fuel body s s'' kk hb,
                  Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl⟩ := hexec
              exact ⟨k, hst, by rw [hpck]; simp only [landPos]⟩
          | ret =>
              rw [LowIR.Prog.exec_block_ret P dbase pad stackLo fuel body s s'' hb,
                  Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl⟩ := hexec
              exact ⟨k, hst, by rw [hpck]; simp only [landPos]⟩
    case ret =>
      rw [LowIR.Prog.exec_ret, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      have he : here < 2 ^ 20 := by simp only [csize] at hbnd; omega
      have hep : epiPos < 2 ^ 20 := hlbl.2.2
      simp only [emitCF] at hem
      obtain ⟨hst, hpcr⟩ :=
        jump_sim L fd holes s m here epiPos _ hinv hpc hem rfl (by omega) (by omega)
      exact ⟨1, hst, by rw [show stepN 1 m = step m from rfl, hpcr]; simp only [csize, landPos]⟩
    case brkB k =>
      rw [LowIR.Prog.exec_brkB, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      have he : here < 2 ^ 20 := by simp only [csize] at hbnd; omega
      have htgt : brkPos.getD k 0 < 2 ^ 20 := getD_lt brkPos k _ (by omega) hlbl.1
      simp only [emitCF] at hem
      obtain ⟨hst, hpcr⟩ :=
        jump_sim L fd holes s m here (brkPos.getD k 0) _ hinv hpc hem rfl (by omega) (by omega)
      exact ⟨1, hst, by rw [show stepN 1 m = step m from rfl, hpcr]; simp only [csize, landPos]⟩
    case contL k =>
      rw [LowIR.Prog.exec_contL, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      have he : here < 2 ^ 20 := by simp only [csize] at hbnd; omega
      have htgt : contPos.getD k 0 < 2 ^ 20 := getD_lt contPos k _ (by omega) hlbl.2.1
      simp only [emitCF] at hem
      obtain ⟨hst, hpcr⟩ :=
        jump_sim L fd holes s m here (contPos.getD k 0) _ hinv hpc hem rfl (by omega) (by omega)
      exact ⟨1, hst, by rw [show stepN 1 m = step m from rfl, hpcr]; simp only [csize, landPos]⟩
    case seq a b =>
      simp only [maxRegS] at hreg
      obtain ⟨haccA, haccB⟩ := haccess
      have hemA : Emitted L here (emitCF brkPos contPos epiPos here a) :=
        Emitted_append_left L here _ _ hem
      have hemB : Emitted L (here + 4 * csize a)
          (emitCF brkPos contPos epiPos (here + 4 * csize a) b) := by
        have h := Emitted_append_right L here (emitCF brkPos contPos epiPos here a)
                    (emitCF brkPos contPos epiPos (here + 4 * csize a) b) hem
        rwa [emitCF_length] at h
      have hregA : maxRegS a ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      have hregB : maxRegS b ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hreg
      have hbndA : here + 4 * csize a < 2 ^ 20 := by simp only [csize] at hbnd; omega
      cases hea : LowIR.Prog.exec P dbase pad stackLo fuel a s with
      | none => rw [LowIR.Prog.exec_seq_none (h := hea)] at hexec; simp at hexec
      | some r =>
        obtain ⟨s1, o⟩ := r
        cases o with
        | normal =>
            rw [LowIR.Prog.exec_seq_normal (h := hea)] at hexec
            have hbndB : (here + 4 * csize a) + 4 * csize b < 2 ^ 20 := by
              simp only [csize] at hbnd; omega
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 .normal m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA
            have hsp : s1.sp = s.sp := StInv_sp_eq L fd holes s s1 m (stepN k1 m) hinv hinvA
            obtain ⟨k2, hinvB, hpcB⟩ :=
              ih b s1 s' oc (stepN k1 m) (here + 4 * csize a) brkPos contPos hexec hinvA
                (by rw [hpcA]; simp only [landPos]) hemB hregB (by rw [hsp]; exact hnw)
                (by rw [hsp]; exact hbd) (haccB s1 hea) hlbl hbndB
            refine ⟨k1 + k2, by rw [stepN_add]; exact hinvB, ?_⟩
            have hft : (here + 4 * csize a) + 4 * csize b
                = here + 4 * csize (LowIR.Prog.Stmt.seq a b) := by simp only [csize]; omega
            rw [stepN_add, hpcB, hft]
        | brk k =>
            rw [LowIR.Prog.exec_seq_brk (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 (.brk k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos]⟩
        | cont k =>
            rw [LowIR.Prog.exec_seq_cont (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 (.cont k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos]⟩
        | ret =>
            rw [LowIR.Prog.exec_seq_ret (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 .ret m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos]⟩
    case addi rd rs imm =>
      rw [LowIR.Prog.exec_addi, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.addi rd rs imm) s _ m here
          (LowIR.Prog.exec_addi P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case add rd r1 r2 =>
      rw [LowIR.Prog.exec_add, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.add rd r1 r2) s _ m here
          (LowIR.Prog.exec_add P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case sub rd r1 r2 =>
      rw [LowIR.Prog.exec_sub, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.sub rd r1 r2) s _ m here
          (LowIR.Prog.exec_sub P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case orr rd r1 r2 =>
      rw [LowIR.Prog.exec_orr, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.orr rd r1 r2) s _ m here
          (LowIR.Prog.exec_orr P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case slli rd rs sh =>
      rw [LowIR.Prog.exec_slli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.slli rd rs sh) s _ m here
          (LowIR.Prog.exec_slli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case srli rd rs sh =>
      rw [LowIR.Prog.exec_srli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.srli rd rs sh) s _ m here
          (LowIR.Prog.exec_srli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case lbu rd rs imm =>
      rw [LowIR.Prog.exec_lbu, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.lbu rd rs imm) s _ m here
          (LowIR.Prog.exec_lbu P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case ld rd rs imm =>
      rw [LowIR.Prog.exec_ld, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.ld rd rs imm) s _ m here
          (LowIR.Prog.exec_ld P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case sb rb rv imm =>
      rw [LowIR.Prog.exec_sb, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.sb rb rv imm) s _ m here
          (LowIR.Prog.exec_sb P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case sd rb rv imm =>
      rw [LowIR.Prog.exec_sd, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.sd rb rv imm) s _ m here
          (LowIR.Prog.exec_sd P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    all_goals sorry

end LowIR.ProgSim
