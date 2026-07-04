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
import LowIR.Lib

namespace LowIR.ProgSim

open Rv64i (Instr State step Word decode fetch32)
open LowIR.Compile (T0 T1 userOff slotOff maxRegF maxRegS)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (St Program Name FunDef Data dbaseOf)
open LowIR (Cond evalCond condInstr jal0)

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
  | .clen rd _      => 3 + (if rd = 0 then 0 else 1)   -- synthConst (3) + storeSlot
  | s               => (emit s).length

/-- The label-aware lowering. `brkPos`/`contPos` are the enclosing block-end /
    loop-top label byte positions (indexed like `brkB`/`contL`'s de-Bruijn
    indices); `epiPos` the epilogue; `here` the byte offset of this code.
    Straight-line cases reuse `emit` (`here` irrelevant). -/
def emitCF (dat : Data) (dpos : Name → Nat) (brkPos contPos : List Nat) (epiPos : Nat) :
    Nat → PStmt → List Instr
  | here, .seq a b =>
      emitCF dat dpos brkPos contPos epiPos here a ++
        emitCF dat dpos brkPos contPos epiPos (here + 4 * csize a) b
  | here, .ret     => [LowIR.jal0 ((epiPos : Int) - (here : Int))]
  | here, .brkB k  => [LowIR.jal0 ((brkPos.getD k 0 : Int) - (here : Int))]
  | here, .contL k => [LowIR.jal0 ((contPos.getD k 0 : Int) - (here : Int))]
  | here, .block body =>
      -- the break target `lEnd` sits just past the body (0-byte label).
      emitCF dat dpos ((here + 4 * csize body) :: brkPos) contPos epiPos here body
  | here, .ife c a b t e =>
      -- br→lT (then) skips over the else block; jmp→lEnd skips over then.
      -- offsets are size-relative: lT is 8 + 4|e| past the branch, lEnd 4 + 4|t|
      -- past the jmp. else code `e` runs on fall-through (at here+12), then `t`.
      loadSlotI a T0 ++ loadSlotI b T1
        ++ [LowIR.condInstr c T0 T1 (8 + 4 * csize e)]
        ++ emitCF dat dpos brkPos contPos epiPos (here + 12) e
        ++ [LowIR.jal0 (4 + 4 * csize t)]
        ++ emitCF dat dpos brkPos contPos epiPos (here + 16 + 4 * csize e) t
  | here, .while c a b body =>
      -- lTop = here (0-byte label); br→lBody (+8) enters, jmp→lEnd exits, the
      -- body runs a continue-scope (lTop::contPos), then the back-edge to lTop.
      loadSlotI a T0 ++ loadSlotI b T1
        ++ [LowIR.condInstr c T0 T1 8, LowIR.jal0 (8 + 4 * csize body)]
        ++ emitCF dat dpos brkPos (here :: contPos) epiPos (here + 16) body
        ++ [LowIR.jal0 (-(16 + 4 * csize body : Int))]
  | _here, .clen rd d =>
      -- position-independent: synth the data length into T0, park into rd's slot.
      synthI T0 (((List.lookup d dat).map (·.length)).getD 0 : Int) ++ storeSlotI rd T0
  | _, s => emit s

/-- `emitCF`'s length is exactly `csize` — position/label-independent, as claimed.
    Needed by the outcome-carrying `lower_sim` to place `seq`'s second half and to
    read the fall-through position. -/
theorem emitCF_length (dat : Data) (dpos : Name → Nat) (bp cp : List Nat) (ep here : Nat)
    (stmt : PStmt) :
    (emitCF dat dpos bp cp ep here stmt).length = csize stmt := by
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
  | clen rd d =>
      simp only [emitCF, csize, List.length_append, synthI_length, storeSlotI_length]
  | _ => rfl

/-- Sanity: on the straight-line fragment, `emitCF` is exactly `emit` (the
    control-flow arms never fire), so all the existing `#guard`s against
    `Compile.lower` carry over unchanged. -/
example (dat : Data) (dpos : Name → Nat) (bp cp : List Nat) (ep here : Nat) :
    emitCF dat dpos bp cp ep here (.addi 12 5 (BitVec.ofNat 12 3))
      = emit (.addi 12 5 (BitVec.ofNat 12 3)) :=
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
def realResolve (dat : Data) (body : PStmt) : Option (List Instr) :=
  let syms : List LowIR.Compile.SymInstr := (lower dat [] [] 0 body).run' 1
  let (flat, lbls, _) := layoutItems (syms ++ [LowIR.Compile.SymInstr.label 0]) 0
  (flat.mapM (fun p => resolveOne lbls [] [] p)).map List.flatten

/-- `emitCF` matched against the real pipeline, epilogue at the body's end. `dpos`
    is `fun _ => 0`: the bodies below have no `cref` (whose emit reads `dpos`). -/
def matchesReal (dat : Data) (body : PStmt) : Bool :=
  realResolve dat body == some (emitCF dat (fun _ => 0) [] [] (4 * csize body) 0 body)

-- `strlen` (`while`), `strtoull` (`block`+`while`+`ife`+`brkB`), `hex0` (nested
-- `ife`s + `while` + `ret`): the validated IR↔assembly mapping, checked concretely.
#guard matchesReal [] LowIR.Prog.Lib.strlenF.body
#guard matchesReal [] LowIR.Prog.Lib.strtoullF.body
#guard matchesReal [] LowIR.Prog.Lib.hex0F.body
#guard matchesReal [] LowIR.Prog.Lib.hex1F.body

-- `clen`: the synthConst (data-length materialise) + slot-store, validated against
-- the real compiler for several lengths and both `rd = 0` (discard) and `rd ≠ 0`.
#guard matchesReal [("tbl", [1, 2, 3])] (.clen 5 "tbl")
#guard matchesReal [("tbl", List.replicate 300 0)] (.clen 11 "tbl")
#guard matchesReal [("tbl", [1, 2, 3])] (.clen 0 "tbl")
#guard matchesReal [("tbl", [7])] (.seq (.clen 5 "tbl") (.addi 6 5 (BitVec.ofNat 12 1)))

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

/-- Every `ife`'s else-skip branch fits the 13-bit branch window (`8 + 4·csize e`
    = the compiler's `resolveOne` guard `δ ≤ 4094`). `while`'s branch is a fixed
    `+8`, always fine. A structural side condition, discharged per-program by the
    real layout (branches that don't fit make `Compile` return `none`). -/
def BranchOk : PStmt → Prop
  | .seq a b          => BranchOk a ∧ BranchOk b
  | .block body       => BranchOk body
  | .ife _ _ _ t e    => 8 + 4 * csize e < 2 ^ 12 ∧ BranchOk t ∧ BranchOk e
  | .while _ _ _ body => BranchOk body
  | _                 => True

/-- A conditional branch `condInstr c T0 T1 δ` whose registers hold `x`, `y`: when
    `evalCond c x y` holds the branch is taken (`pc += δ`), matching the compiler's
    positive-form encoding (`.ge`/`.geu` take the *else* arm of `bge`/`bgeu`). -/
theorem cond_taken (m : State) (c : Cond) (δ : Int) (x y : Word)
    (hd : decode (fetch32 m) = condInstr c T0 T1 δ)
    (hx : m.rget T0 = x) (hy : m.rget T1 = y) (hev : evalCond c x y = true) :
    step m = m.setPc (m.pc + (BitVec.ofInt 13 δ).signExtend 64) := by
  cases c <;> simp only [condInstr] at hd
  · have h : x = y := by simpa [evalCond] using hev
    rw [step_beq m T0 T1 _ hd, hx, hy, if_pos h]
  · have h : x.slt y = true := by simpa [evalCond] using hev
    rw [step_blt m T0 T1 _ hd, hx, hy, if_pos h]
  · have h : x.slt y = false := by simpa [evalCond] using hev
    rw [step_bge m T0 T1 _ hd, hx, hy, if_neg (by simp [h])]
  · have h : x.ult y = false := by simpa [evalCond] using hev
    rw [step_bgeu m T0 T1 _ hd, hx, hy, if_neg (by simp [h])]

/-- …and when `evalCond c x y` fails the branch falls through (`pc += 4`). -/
theorem cond_not_taken (m : State) (c : Cond) (δ : Int) (x y : Word)
    (hd : decode (fetch32 m) = condInstr c T0 T1 δ)
    (hx : m.rget T0 = x) (hy : m.rget T1 = y) (hev : evalCond c x y = false) :
    step m = m.setPc (m.pc + 4) := by
  cases c <;> simp only [condInstr] at hd
  · have h : ¬ x = y := by simpa [evalCond] using hev
    rw [step_beq m T0 T1 _ hd, hx, hy, if_neg h]
  · have h : x.slt y = false := by simpa [evalCond] using hev
    rw [step_blt m T0 T1 _ hd, hx, hy, if_neg (by simp [h])]
  · have h : x.slt y = true := by simpa [evalCond] using hev
    rw [step_bge m T0 T1 _ hd, hx, hy, if_pos h]
  · have h : x.ult y = true := by simpa [evalCond] using hev
    rw [step_bgeu m T0 T1 _ hd, hx, hy, if_pos h]

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
    {L : Layout} {fd : FunDef} {holes : List Hole} {epiPos : Nat} {dpos : Name → Nat}
    (fuel : Nat) (stmt : PStmt) (s s' : St) (oc : Outcome) (m : State)
    (here : Nat) (brkPos contPos : List Nat)
    (hexec : LowIR.Prog.exec P dbase pad stackLo fuel stmt s = some (s', oc))
    (hinv  : StInv L fd holes s m)
    (hpc   : m.pc = L.codeBase + BitVec.ofNat 64 here)
    (hem   : Emitted L here (emitCF P.data dpos brkPos contPos epiPos here stmt))
    (hreg  : maxRegS stmt ≤ maxRegF fd)
    (hnw   : s.sp.toNat + userOff fd ≤ 2 ^ 64)
    (hbd   : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
               ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat)
    (haccess : MemAccOff L holes P dbase pad stackLo fuel stmt s)
    (hlbl  : LabelsOk brkPos contPos epiPos)
    (hbnd  : here + 4 * csize stmt < 2 ^ 20)
    (hbr   : BranchOk stmt)
    (hframe : userOff fd ≤ 2000)
    (hseg  : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hdat  : ∀ d, -2048 ≤ synthHi (((List.lookup d P.data).map (·.length)).getD 0)
                ∧ synthHi (((List.lookup d P.data).map (·.length)).getD 0) ≤ 2047) :
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
      have hem' : Emitted L here (emitCF P.data dpos ((here + 4 * csize body) :: brkPos) contPos epiPos here body)
        := hem
      have hreg' : maxRegS body ≤ maxRegF fd := hreg
      have hacc' : MemAccOff L holes P dbase pad stackLo fuel body s := by
        simpa only [MemAccOff] using haccess
      have hbr' : BranchOk body := hbr
      cases hb : LowIR.Prog.exec P dbase pad stackLo fuel body s with
      | none =>
          rw [LowIR.Prog.exec_block_none P dbase pad stackLo fuel body s hb] at hexec
          simp at hexec
      | some pr =>
          obtain ⟨s'', ocb⟩ := pr
          obtain ⟨k, hst, hpck⟩ :=
            ih body s s'' ocb m here ((here + 4 * csize body) :: brkPos) contPos
              hb hinv hpc hem' hreg' hnw hbd hacc' hlbl' hbnd' hbr'
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
      obtain ⟨hbrA, hbrB⟩ := hbr
      have hemA : Emitted L here (emitCF P.data dpos brkPos contPos epiPos here a) :=
        Emitted_append_left L here _ _ hem
      have hemB : Emitted L (here + 4 * csize a)
          (emitCF P.data dpos brkPos contPos epiPos (here + 4 * csize a) b) := by
        have h := Emitted_append_right L here (emitCF P.data dpos brkPos contPos epiPos here a)
                    (emitCF P.data dpos brkPos contPos epiPos (here + 4 * csize a) b) hem
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
                hlbl hbndA hbrA
            have hsp : s1.sp = s.sp := StInv_sp_eq L fd holes s s1 m (stepN k1 m) hinv hinvA
            obtain ⟨k2, hinvB, hpcB⟩ :=
              ih b s1 s' oc (stepN k1 m) (here + 4 * csize a) brkPos contPos hexec hinvA
                (by rw [hpcA]; simp only [landPos]) hemB hregB (by rw [hsp]; exact hnw)
                (by rw [hsp]; exact hbd) (haccB s1 hea) hlbl hbndB hbrB
            refine ⟨k1 + k2, by rw [stepN_add]; exact hinvB, ?_⟩
            have hft : (here + 4 * csize a) + 4 * csize b
                = here + 4 * csize (LowIR.Prog.Stmt.seq a b) := by simp only [csize]; omega
            rw [stepN_add, hpcB, hft]
        | brk k =>
            rw [LowIR.Prog.exec_seq_brk (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 (.brk k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos]⟩
        | cont k =>
            rw [LowIR.Prog.exec_seq_cont (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 (.cont k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos]⟩
        | ret =>
            rw [LowIR.Prog.exec_seq_ret (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA⟩ :=
              ih a s s1 .ret m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos]⟩
    case addi rd rs imm =>
      rw [LowIR.Prog.exec_addi, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.addi rd rs imm) s _ m here
          (LowIR.Prog.exec_addi P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case add rd r1 r2 =>
      rw [LowIR.Prog.exec_add, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.add rd r1 r2) s _ m here
          (LowIR.Prog.exec_add P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case sub rd r1 r2 =>
      rw [LowIR.Prog.exec_sub, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.sub rd r1 r2) s _ m here
          (LowIR.Prog.exec_sub P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case orr rd r1 r2 =>
      rw [LowIR.Prog.exec_orr, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.orr rd r1 r2) s _ m here
          (LowIR.Prog.exec_orr P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case slli rd rs sh =>
      rw [LowIR.Prog.exec_slli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.slli rd rs sh) s _ m here
          (LowIR.Prog.exec_slli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case srli rd rs sh =>
      rw [LowIR.Prog.exec_srli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.srli rd rs sh) s _ m here
          (LowIR.Prog.exec_srli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case lbu rd rs imm =>
      rw [LowIR.Prog.exec_lbu, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.lbu rd rs imm) s _ m here
          (LowIR.Prog.exec_lbu P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case ld rd rs imm =>
      rw [LowIR.Prog.exec_ld, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.ld rd rs imm) s _ m here
          (LowIR.Prog.exec_ld P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case sb rb rv imm =>
      rw [LowIR.Prog.exec_sb, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.sb rb rv imm) s _ m here
          (LowIR.Prog.exec_sb P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case sd rb rv imm =>
      rw [LowIR.Prog.exec_sd, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck⟩ :=
        lower_sim (fuel + 1) (.sd rb rv imm) s _ m here
          (LowIR.Prog.exec_sd P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize]⟩
    case ife c a b t e =>
      simp only [maxRegS] at hreg
      obtain ⟨hbrbr, hbrT, hbrE⟩ := hbr
      obtain ⟨haccT, haccE⟩ := haccess
      have hab : max a b ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      have hra : a ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hab
      have hrb : b ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hab
      have hte : max (maxRegS t) (maxRegS e) ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hreg
      have hregT : maxRegS t ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hte
      have hregE : maxRegS e ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hte
      have hfa : slotOff a < 2 ^ 11 := by have := slotOff_add8_le_userOff fd a hra; omega
      have hfb : slotOff b < 2 ^ 11 := by have := slotOff_add8_le_userOff fd b hrb; omega
      have hinst : Installed L m := hinv.2.2.1
      have hemU : Emitted L here (loadSlotI a T0 ++ loadSlotI b T1
          ++ [condInstr c T0 T1 (8 + 4 * csize e)]
          ++ emitCF P.data dpos brkPos contPos epiPos (here + 12) e
          ++ [jal0 (4 + 4 * csize t)]
          ++ emitCF P.data dpos brkPos contPos epiPos (here + 16 + 4 * csize e) t) := hem
      have hP2 : Emitted L here (loadSlotI a T0 ++ loadSlotI b T1) :=
        Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _
          (Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ hemU)))
      obtain ⟨hinv1, h1pc, h1mem, h1T0, -⟩ :=
        run_load L fd holes s m a T0 here hinv hra hfa (by decide) (by decide) hpc
          (Emitted_append_left _ _ _ _ hP2)
      have hemB : Emitted L (here + 4) (loadSlotI b T1) := by
        have h := Emitted_append_right _ _ _ _ hP2; rwa [loadSlotI_length, Nat.mul_one] at h
      obtain ⟨hinv2, h2pc, h2mem, h2T1, h2oth⟩ :=
        run_load L fd holes s (step m) b T1 (here + 4) hinv1 hrb hfb (by decide) (by decide) h1pc hemB
      have h2T0 : (step (step m)).rget T0 = s.rget a := by rw [h2oth T0 (by decide)]; exact h1T0
      have h2mm : (step (step m)).mem = m.mem := by rw [h2mem, h1mem]
      have hemBr : Emitted L (here + 8) [condInstr c T0 T1 (8 + 4 * csize e)] := by
        have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _
          (Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ hemU)))
        rw [List.length_append, loadSlotI_length, loadSlotI_length] at h
        rwa [show here + 4 * (1 + 1) = here + 8 from by omega] at h
      have hdBr : decode (fetch32 (step (step m))) = condInstr c T0 T1 (8 + 4 * csize e) := by
        have h := decode_at L m (step (step m)) (here + 8) _ hemBr hinst 0 (by simp)
          (by rw [h2pc]) h2mm
        simpa using h
      have hb13lo : -(2 ^ 12 : Int) ≤ (8 : Int) + 4 * (csize e : Int) := by omega
      have hb13hi : (8 : Int) + 4 * (csize e : Int) < 2 ^ 12 := by
        have : 8 + 4 * csize e < 2 ^ 12 := hbrbr; omega
      have hbnd2 : here + 16 + 4 * csize e + 4 * csize t < 2 ^ 20 := by
        simp only [csize] at hbnd; omega
      have h3 : stepN 3 m = step (step (step m)) := rfl
      have hsN : ∀ n, stepN (3 + n) m = stepN n (step (step (step m))) := fun n => by
        rw [stepN_add, h3]
      cases hev : evalCond c (s.rget a) (s.rget b) with
      | true =>
          rw [LowIR.Prog.exec_ife_then (h := hev)] at hexec
          have hs3 : step (step (step m)) = (step (step m)).setPc
              ((step (step m)).pc + (BitVec.ofInt 13 (8 + 4 * csize e)).signExtend 64) :=
            cond_taken (step (step m)) c _ (s.rget a) (s.rget b) hdBr h2T0 h2T1 hev
          have hinv3 : StInv L fd holes s (step (step (step m))) := by
            rw [hs3]; exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hinv2
          have hpc3 : (step (step (step m))).pc
              = L.codeBase + BitVec.ofNat 64 (here + 16 + 4 * csize e) := by
            rw [hs3, pc_setPc, h2pc, signExtend_ofInt_13 _ hb13lo hb13hi]
            rw [show ((8 : Int) + 4 * (csize e : Int))
                  = (↑(here + 16 + 4 * csize e) : Int) - ↑(here + 4 + 4) from by push_cast; omega]
            exact jump_lands L.codeBase (here + 4 + 4) (here + 16 + 4 * csize e)
          have hemT : Emitted L (here + 16 + 4 * csize e)
              (emitCF P.data dpos brkPos contPos epiPos (here + 16 + 4 * csize e) t) := by
            have h := Emitted_append_right _ _ _ _ hemU
            rw [show (loadSlotI a T0 ++ loadSlotI b T1 ++ [condInstr c T0 T1 (8 + 4 * csize e)]
                  ++ emitCF P.data dpos brkPos contPos epiPos (here + 12) e ++ [jal0 (4 + 4 * csize t)]).length
                  = 4 + csize e from by
                  simp only [List.length_append, loadSlotI_length, List.length_cons,
                             List.length_nil, emitCF_length]; omega] at h
            rwa [show here + 4 * (4 + csize e) = here + 16 + 4 * csize e from by omega] at h
          obtain ⟨kt, hinvT, hpcT⟩ :=
            ih t s s' oc (step (step (step m))) (here + 16 + 4 * csize e) brkPos contPos hexec hinv3
              hpc3 hemT hregT hnw hbd haccT hlbl (by simp only [csize] at hbnd; omega) hbrT
          refine ⟨3 + kt, by rw [hsN kt]; exact hinvT, ?_⟩
          rw [hsN kt, hpcT,
              show here + 16 + 4 * csize e + 4 * csize t
                = here + 4 * csize (LowIR.Prog.Stmt.ife c a b t e) from by simp only [csize]; omega]
      | false =>
          rw [LowIR.Prog.exec_ife_else (h := hev)] at hexec
          have hs3 : step (step (step m)) = (step (step m)).setPc ((step (step m)).pc + 4) :=
            cond_not_taken (step (step m)) c _ (s.rget a) (s.rget b) hdBr h2T0 h2T1 hev
          have hinv3 : StInv L fd holes s (step (step (step m))) := by
            rw [hs3]; exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hinv2
          have hpc3 : (step (step (step m))).pc = L.codeBase + BitVec.ofNat 64 (here + 12) := by
            rw [hs3, pc_setPc, h2pc, pc_add4]
          have hemE : Emitted L (here + 12) (emitCF P.data dpos brkPos contPos epiPos (here + 12) e) := by
            have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _
              (Emitted_append_left _ _ _ _ hemU))
            rw [show (loadSlotI a T0 ++ loadSlotI b T1
                  ++ [condInstr c T0 T1 (8 + 4 * csize e)]).length = 3 from by
                  simp only [List.length_append, loadSlotI_length, List.length_cons,
                             List.length_nil]] at h
            rwa [show here + 4 * 3 = here + 12 from by omega] at h
          obtain ⟨ke, hinvE, hpcE⟩ :=
            ih e s s' oc (step (step (step m))) (here + 12) brkPos contPos hexec hinv3 hpc3 hemE
              hregE hnw hbd haccE hlbl (by simp only [csize] at hbnd; omega) hbrE
          cases oc with
          | normal =>
              have hemJ : Emitted L (here + 12 + 4 * csize e) [jal0 (4 + 4 * csize t)] := by
                have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _ hemU)
                rw [show (loadSlotI a T0 ++ loadSlotI b T1 ++ [condInstr c T0 T1 (8 + 4 * csize e)]
                      ++ emitCF P.data dpos brkPos contPos epiPos (here + 12) e).length = 3 + csize e from by
                      simp only [List.length_append, loadSlotI_length, List.length_cons,
                                 List.length_nil, emitCF_length]] at h
                rwa [show here + 4 * (3 + csize e) = here + 12 + 4 * csize e from by omega] at h
              have hpcE' : (stepN ke (step (step (step m)))).pc
                  = L.codeBase + BitVec.ofNat 64 (here + 12 + 4 * csize e) := by
                rw [hpcE]; simp only [landPos]
              obtain ⟨hstJ, hpcJ⟩ :=
                jump_sim L fd holes s' (stepN ke (step (step (step m)))) (here + 12 + 4 * csize e)
                  (here + 16 + 4 * csize e + 4 * csize t) _ hinvE hpcE' hemJ (by push_cast; omega)
                  (by omega) (by omega)
              refine ⟨3 + ke + 1, ?_, ?_⟩
              · rw [show stepN (3 + ke + 1) m = step (stepN (3 + ke) m) from by rw [stepN_add]; rfl,
                    hsN ke]
                exact hstJ
              · rw [show stepN (3 + ke + 1) m = step (stepN (3 + ke) m) from by rw [stepN_add]; rfl,
                    hsN ke, hpcJ]
                simp only [landPos]
                exact pc_congr _ (by simp only [csize]; omega)
          | brk k =>
              refine ⟨3 + ke, by rw [hsN ke]; exact hinvE, ?_⟩
              rw [hsN ke, hpcE]; simp only [landPos]
          | cont k =>
              refine ⟨3 + ke, by rw [hsN ke]; exact hinvE, ?_⟩
              rw [hsN ke, hpcE]; simp only [landPos]
          | ret =>
              refine ⟨3 + ke, by rw [hsN ke]; exact hinvE, ?_⟩
              rw [hsN ke, hpcE]; simp only [landPos]
    case «while» c a b body =>
      -- register bounds (`maxRegS (.while) = max (max a b) (maxRegS body)`).
      have hregU : max (max a b) (maxRegS body) ≤ maxRegF fd := hreg
      have hab : max a b ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hregU
      have hra : a ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hab
      have hrb : b ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hab
      have hregBody : maxRegS body ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hregU
      have hfa : slotOff a < 2 ^ 11 := by have := slotOff_add8_le_userOff fd a hra; omega
      have hfb : slotOff b < 2 ^ 11 := by have := slotOff_add8_le_userOff fd b hrb; omega
      have hinst : Installed L m := hinv.2.2.1
      have hbrBody : BranchOk body := hbr
      obtain ⟨haccBody, haccRec⟩ := haccess
      -- position facts (keep `hbnd` intact for the fuel IH).
      have hbnd20 : here + 20 + 4 * csize body < 2 ^ 20 := by
        have h := hbnd; simp only [csize] at h; omega
      have hhere : here < 2 ^ 20 := by omega
      -- the whole emitCF P.data dpos stream, unfolded.
      have hemU : Emitted L here (loadSlotI a T0 ++ loadSlotI b T1
          ++ [condInstr c T0 T1 8, jal0 (8 + 4 * csize body)]
          ++ emitCF P.data dpos brkPos (here :: contPos) epiPos (here + 16) body
          ++ [jal0 (-(16 + 4 * csize body : Int))]) := hem
      -- two slot loads (a→T0, b→T1)
      have hP2 : Emitted L here (loadSlotI a T0 ++ loadSlotI b T1) :=
        Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _
          (Emitted_append_left _ _ _ _ hemU))
      obtain ⟨hinv1, h1pc, h1mem, h1T0, -⟩ :=
        run_load L fd holes s m a T0 here hinv hra hfa (by decide) (by decide) hpc
          (Emitted_append_left _ _ _ _ hP2)
      have hemLb : Emitted L (here + 4) (loadSlotI b T1) := by
        have h := Emitted_append_right _ _ _ _ hP2; rwa [loadSlotI_length, Nat.mul_one] at h
      obtain ⟨hinv2, h2pc, h2mem, h2T1, h2oth⟩ :=
        run_load L fd holes s (step m) b T1 (here + 4) hinv1 hrb hfb (by decide) (by decide) h1pc hemLb
      have h2T0 : (step (step m)).rget T0 = s.rget a := by rw [h2oth T0 (by decide)]; exact h1T0
      have h2mm : (step (step m)).mem = m.mem := by rw [h2mem, h1mem]
      -- the `[branch, exit-jmp]` chunk sits at here+8.
      have hemCJ : Emitted L (here + 8) [condInstr c T0 T1 8, jal0 (8 + 4 * csize body)] := by
        have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _
          (Emitted_append_left _ _ _ _ hemU))
        rw [List.length_append, loadSlotI_length, loadSlotI_length] at h
        rwa [show here + 4 * (1 + 1) = here + 8 from by omega] at h
      have hemBr : Emitted L (here + 8) [condInstr c T0 T1 8] :=
        Emitted_append_left L (here + 8) [condInstr c T0 T1 8] [jal0 (8 + 4 * csize body)] hemCJ
      have hdBr : decode (fetch32 (step (step m))) = condInstr c T0 T1 8 := by
        have h := decode_at L m (step (step m)) (here + 8) _ hemBr hinst 0 (by simp)
          (by rw [h2pc]) h2mm
        simpa using h
      -- body-stream Emitted (at here+16) and the back-edge (at here+16+4·csize body).
      have hemBody : Emitted L (here + 16)
          (emitCF P.data dpos brkPos (here :: contPos) epiPos (here + 16) body) := by
        have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _ hemU)
        rw [show (loadSlotI a T0 ++ loadSlotI b T1
              ++ [condInstr c T0 T1 8, jal0 (8 + 4 * csize body)]).length = 4 from by
              simp only [List.length_append, loadSlotI_length, List.length_cons,
                         List.length_nil]] at h
        rwa [show here + 4 * 4 = here + 16 from by omega] at h
      have hemBack : Emitted L (here + 16 + 4 * csize body)
          [jal0 (-(16 + 4 * csize body : Int))] := by
        have h := Emitted_append_right _ _ _ _ hemU
        rw [show ((loadSlotI a T0 ++ loadSlotI b T1
              ++ [condInstr c T0 T1 8, jal0 (8 + 4 * csize body)])
              ++ emitCF P.data dpos brkPos (here :: contPos) epiPos (here + 16) body).length
              = 4 + csize body from by
            simp only [List.length_append, loadSlotI_length, List.length_cons,
                       List.length_nil, emitCF_length]] at h
        rwa [show here + 4 * (4 + csize body) = here + 16 + 4 * csize body from by omega] at h
      -- label env for the body: continue scope gains `lTop = here`.
      have hlbl' : LabelsOk brkPos (here :: contPos) epiPos := by
        obtain ⟨hb, hc, he⟩ := hlbl
        refine ⟨hb, fun p hp => ?_, he⟩
        rcases List.mem_cons.mp hp with h | h
        · exact h ▸ hhere
        · exact hc p h
      have hbndBody : here + 16 + 4 * csize body < 2 ^ 20 := by omega
      -- step chain: 2 loads + branch = 3 machine steps.
      have h3 : stepN 3 m = step (step (step m)) := rfl
      have hsN : ∀ n, stepN (3 + n) m = stepN n (step (step (step m))) := fun n => by
        rw [stepN_add, h3]
      cases hev : evalCond c (s.rget a) (s.rget b) with
      | false =>
          -- loop exits: `exec` gives `(s, .normal)`; machine falls through then jumps to lEnd.
          rw [LowIR.Prog.exec_while_false P dbase pad stackLo fuel c a b body s hev,
              Option.some.injEq, Prod.mk.injEq] at hexec
          obtain ⟨rfl, rfl⟩ := hexec
          have hs3 : step (step (step m)) = (step (step m)).setPc ((step (step m)).pc + 4) :=
            cond_not_taken (step (step m)) c 8 (s.rget a) (s.rget b) hdBr h2T0 h2T1 hev
          have hinv3 : StInv L fd holes s (step (step (step m))) := by
            rw [hs3]; exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hinv2
          have hpc3 : (step (step (step m))).pc = L.codeBase + BitVec.ofNat 64 (here + 12) := by
            rw [hs3, pc_setPc, h2pc, pc_add4]
          have hemJmp : Emitted L (here + 12) [jal0 (8 + 4 * csize body)] :=
            Emitted_append_right L (here + 8) [condInstr c T0 T1 8]
              [jal0 (8 + 4 * csize body)] hemCJ
          obtain ⟨hstJmp, hpcJmp⟩ :=
            jump_sim L fd holes s (step (step (step m))) (here + 12) (here + 20 + 4 * csize body) _
              hinv3 hpc3 hemJmp (by push_cast; omega) (by omega) (by omega)
          have h4 : stepN 4 m = step (step (step (step m))) := rfl
          refine ⟨4, ?_, ?_⟩
          · rw [h4]; exact hstJmp
          · rw [h4, hpcJmp]; simp only [landPos]; exact pc_congr _ (by simp only [csize]; omega)
      | true =>
          -- loop enters: branch taken to lBody (here+16), then the body IH.
          have hs3 : step (step (step m)) = (step (step m)).setPc
              ((step (step m)).pc + (BitVec.ofInt 13 8).signExtend 64) :=
            cond_taken (step (step m)) c 8 (s.rget a) (s.rget b) hdBr h2T0 h2T1 hev
          have hinv3 : StInv L fd holes s (step (step (step m))) := by
            rw [hs3]; exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hinv2
          have hpc3 : (step (step (step m))).pc = L.codeBase + BitVec.ofNat 64 (here + 16) := by
            rw [hs3, pc_setPc, h2pc, signExtend_ofInt_13 8 (by omega) (by omega)]
            rw [show ((8 : Int)) = (↑(here + 16) : Int) - ↑(here + 4 + 4) from by push_cast; omega]
            exact jump_lands L.codeBase (here + 4 + 4) (here + 16)
          cases hbody : LowIR.Prog.exec P dbase pad stackLo fuel body s with
          | none =>
              rw [LowIR.Prog.exec_while_none P dbase pad stackLo fuel c a b body s hev hbody] at hexec
              simp at hexec
          | some pr =>
              obtain ⟨sb, ocb⟩ := pr
              obtain ⟨kb, hinvB, hpcB⟩ :=
                ih body s sb ocb (step (step (step m))) (here + 16) brkPos (here :: contPos)
                  hbody hinv3 hpc3 hemBody hregBody hnw hbd haccBody hlbl' hbndBody hbrBody
              have hsp : sb.sp = s.sp :=
                StInv_sp_eq L fd holes s sb m (stepN kb (step (step (step m)))) hinv hinvB
              cases ocb with
              | normal =>
                  rw [LowIR.Prog.exec_while_normal P dbase pad stackLo fuel c a b body s sb hev hbody]
                    at hexec
                  have hpcB' : (stepN kb (step (step (step m)))).pc
                      = L.codeBase + BitVec.ofNat 64 (here + 16 + 4 * csize body) := by
                    rw [hpcB]; simp only [landPos]
                  obtain ⟨hstBack, hpcBack⟩ :=
                    jump_sim L fd holes sb (stepN kb (step (step (step m))))
                      (here + 16 + 4 * csize body) here _ hinvB hpcB' hemBack
                      (by push_cast; omega) (by omega) (by omega)
                  obtain ⟨kw, hinvW, hpcW⟩ :=
                    ih (.while c a b body) sb s' oc (step (stepN kb (step (step (step m)))))
                      here brkPos contPos hexec hstBack hpcBack hem hreg
                      (by rw [hsp]; exact hnw) (by rw [hsp]; exact hbd)
                      (haccRec sb (Or.inl hbody)) hlbl hbnd hbr
                  refine ⟨3 + kb + 1 + kw, ?_, ?_⟩
                  · rw [stepN_add (3 + kb + 1) kw, stepN_add (3 + kb) 1, hsN kb]; exact hinvW
                  · rw [stepN_add (3 + kb + 1) kw, stepN_add (3 + kb) 1, hsN kb]; exact hpcW
              | brk k =>
                  rw [LowIR.Prog.exec_while_brk P dbase pad stackLo fuel c a b body s sb k hev hbody,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨3 + kb, by rw [hsN kb]; exact hinvB, ?_⟩
                  rw [hsN kb, hpcB]; simp only [landPos]
              | cont k =>
                  cases k with
                  | zero =>
                      rw [LowIR.Prog.exec_while_cont0 P dbase pad stackLo fuel c a b body s sb hev
                          hbody] at hexec
                      have hpcB' : (stepN kb (step (step (step m)))).pc
                          = L.codeBase + BitVec.ofNat 64 here := by
                        rw [hpcB]; simp only [landPos, List.getD_cons_zero]
                      obtain ⟨kw, hinvW, hpcW⟩ :=
                        ih (.while c a b body) sb s' oc (stepN kb (step (step (step m))))
                          here brkPos contPos hexec hinvB hpcB' hem hreg
                          (by rw [hsp]; exact hnw) (by rw [hsp]; exact hbd)
                          (haccRec sb (Or.inr hbody)) hlbl hbnd hbr
                      refine ⟨3 + kb + kw, ?_, ?_⟩
                      · rw [stepN_add (3 + kb) kw, hsN kb]; exact hinvW
                      · rw [stepN_add (3 + kb) kw, hsN kb]; exact hpcW
                  | succ k' =>
                      rw [LowIR.Prog.exec_while_contS P dbase pad stackLo fuel c a b body s sb k' hev
                          hbody, Option.some.injEq, Prod.mk.injEq] at hexec
                      obtain ⟨rfl, rfl⟩ := hexec
                      refine ⟨3 + kb, by rw [hsN kb]; exact hinvB, ?_⟩
                      rw [hsN kb, hpcB]; simp only [landPos, List.getD_cons_succ]
              | ret =>
                  rw [LowIR.Prog.exec_while_ret P dbase pad stackLo fuel c a b body s sb hev hbody,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨3 + kb, by rw [hsN kb]; exact hinvB, ?_⟩
                  rw [hsN kb, hpcB]; simp only [landPos]
    case clen rd d =>
      -- synthConst the length into T0 (`run_synth`), then park it into rd's slot
      -- (`run_store`). Position-independent; `hdat` supplies the synth range.
      have hrd : rd ≤ maxRegF fd := hreg
      have hfrd : slotOff rd < 2 ^ 11 := by
        have := slotOff_add8_le_userOff fd rd hrd; omega
      cases hlk : List.lookup d P.data with
      | none =>
          rw [LowIR.Prog.exec_clen_none P dbase pad stackLo fuel rd d s hlk] at hexec
          exact absurd hexec (by simp)
      | some bs =>
          rw [LowIR.Prog.exec_clen P dbase pad stackLo fuel rd d s hlk, Option.some.injEq,
              Prod.mk.injEq] at hexec
          obtain ⟨rfl, rfl⟩ := hexec
          simp only [emitCF, hlk, Option.map_some, Option.getD_some] at hem
          have hemS : Emitted L here (synthI T0 (bs.length : Int)) :=
            Emitted_append_left L here (synthI T0 (bs.length : Int)) (storeSlotI rd T0) hem
          have hemST : Emitted L (here + 12) (storeSlotI rd T0) := by
            have h := Emitted_append_right L here (synthI T0 (bs.length : Int)) (storeSlotI rd T0) hem
            rwa [synthI_length] at h
          have hrange : -2048 ≤ synthHi (bs.length : Int) ∧ synthHi (bs.length : Int) ≤ 2047 := by
            have h := hdat d; rwa [hlk, Option.map_some, Option.getD_some] at h
          obtain ⟨hinvS, hT0S, hpcS, -, -⟩ :=
            run_synth L fd holes s m T0 (by decide) (by decide) (bs.length : Int) here
              hinv hpc hemS hrange
          obtain ⟨ks, hinvF, hpcF⟩ :=
            run_store L fd holes s (stepN 3 m) rd (BitVec.ofInt 64 (bs.length : Int)) (here + 12)
              hinvS hT0S hpcS hemST hrd hfrd hnw hseg hblob hbd
          have hval : s.rset rd (BitVec.ofInt 64 (bs.length : Int))
              = s.rset rd (BitVec.ofNat 64 bs.length) := by rw [BitVec.ofInt_natCast]
          refine ⟨3 + ks, ?_, ?_⟩
          · rw [stepN_add 3 ks m]; rw [hval] at hinvF; exact hinvF
          · rw [stepN_add 3 ks m, hpcF]
            apply pc_congr
            simp only [landPos, csize, storeSlotI_length]
            by_cases hrd0 : rd = 0 <;> simp only [hrd0, if_true, if_false] <;> omega
    case cref rd d => sorry
    case call argc rvc f args rets => sorry

end LowIR.ProgSim
