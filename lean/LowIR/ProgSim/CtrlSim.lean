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
open LowIR.Compile (T0 T1 SP RA A userOff totalFrame slotOff maxRegF maxRegS)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (St Program Name FunDef Data dbaseOf)
open LowIR (Cond evalCond condInstr jal0)

local notation "PStmt" => LowIR.Prog.Stmt

/-! ## Call-marshalling emit helpers (arg loads / ret stores).

    A `call` lowers to: one `loadSlotI arg[i] (A i)` per argument (always 1
    instruction each, incl. reg 0 → `addi (A i) x0 0`), then `jal RA` to the
    callee, then one `storeSlotI ret[i] (A i)` per RETURN (0 instructions for
    ret reg 0). These mirror the compiler's `lower` call arm exactly (`A i` =
    `x10+i`), validated by `matchesRealProg` below. -/
def marshalI (args : List Nat) : List Instr :=
  args.zipIdx.flatMap fun ri => loadSlotI ri.1 (A ri.2)

def retStoresI (rets : List Nat) : List Instr :=
  rets.zipIdx.flatMap fun ri => storeSlotI ri.1 (A ri.2)

/-- Each `loadSlotI` is one instruction, so `marshalI`'s length is the argument
    count (independent of the `A`-register indices). -/
theorem length_flatMap_loadSlotI (l : List (Nat × Nat)) :
    (l.flatMap fun ri => loadSlotI ri.1 (A ri.2)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [List.flatMap_cons, List.length_append, loadSlotI_length, ih, List.length_cons,
          Nat.add_comm t.length 1]

theorem marshalI_length (args : List Nat) : (marshalI args).length = args.length := by
  rw [marshalI, length_flatMap_loadSlotI, List.length_zipIdx]

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
  | .cref rd _      => 5 + (if rd = 0 then 0 else 1)   -- pc-read + synth + add + store
  | .call _ _ _ args rets =>                           -- argc loads + jal + ret stores
      args.toList.length + 1 + (retStoresI rets.toList).length
  | s               => (emit s).length

/-- The label-aware lowering. `brkPos`/`contPos` are the enclosing block-end /
    loop-top label byte positions (indexed like `brkB`/`contL`'s de-Bruijn
    indices); `epiPos` the epilogue; `here` the byte offset of this code.
    Straight-line cases reuse `emit` (`here` irrelevant). -/
def emitCF (dat : Data) (dpos fnPos : Name → Nat) (brkPos contPos : List Nat) (epiPos : Nat) :
    Nat → PStmt → List Instr
  | here, .seq a b =>
      emitCF dat dpos fnPos brkPos contPos epiPos here a ++
        emitCF dat dpos fnPos brkPos contPos epiPos (here + 4 * csize a) b
  | here, .ret     => [LowIR.jal0 ((epiPos : Int) - (here : Int))]
  | here, .brkB k  => [LowIR.jal0 ((brkPos.getD k 0 : Int) - (here : Int))]
  | here, .contL k => [LowIR.jal0 ((contPos.getD k 0 : Int) - (here : Int))]
  | here, .block body =>
      -- the break target `lEnd` sits just past the body (0-byte label).
      emitCF dat dpos fnPos ((here + 4 * csize body) :: brkPos) contPos epiPos here body
  | here, .ife c a b t e =>
      -- br→lT (then) skips over the else block; jmp→lEnd skips over then.
      -- offsets are size-relative: lT is 8 + 4|e| past the branch, lEnd 4 + 4|t|
      -- past the jmp. else code `e` runs on fall-through (at here+12), then `t`.
      loadSlotI a T0 ++ loadSlotI b T1
        ++ [LowIR.condInstr c T0 T1 (8 + 4 * csize e)]
        ++ emitCF dat dpos fnPos brkPos contPos epiPos (here + 12) e
        ++ [LowIR.jal0 (4 + 4 * csize t)]
        ++ emitCF dat dpos fnPos brkPos contPos epiPos (here + 16 + 4 * csize e) t
  | here, .while c a b body =>
      -- lTop = here (0-byte label); br→lBody (+8) enters, jmp→lEnd exits, the
      -- body runs a continue-scope (lTop::contPos), then the back-edge to lTop.
      loadSlotI a T0 ++ loadSlotI b T1
        ++ [LowIR.condInstr c T0 T1 8, LowIR.jal0 (8 + 4 * csize body)]
        ++ emitCF dat dpos fnPos brkPos (here :: contPos) epiPos (here + 16) body
        ++ [LowIR.jal0 (-(16 + 4 * csize body : Int))]
  | _here, .clen rd d =>
      -- position-independent: synth the data length into T0, park into rd's slot.
      synthI T0 (((List.lookup d dat).map (·.length)).getD 0 : Int) ++ storeSlotI rd T0
  | here, .cref rd d =>
      -- pc-read (`jal T0,+4`) + synth the delta to `d`'s absolute position into T1
      -- + `add T0,T0,T1` ⇒ T0 = data address; park into rd's slot.
      crefI T0 T1 ((dpos d : Int) - ((here : Int) + 4)) ++ storeSlotI rd T0
  | here, .call argc _rvc f args rets =>
      -- marshal args into `a0..` (argc loads), `jal RA` to the callee (sits at
      -- `here + 4·argc`), then park each return from `a0..` (ret-store per nonzero ret).
      marshalI args.toList
        ++ [Instr.jal RA (BitVec.ofInt 21 ((fnPos f : Int) - ((here : Int) + 4 * argc)))]
        ++ retStoresI rets.toList
  | _, s => emit s

/-- `emitCF`'s length is exactly `csize` — position/label-independent, as claimed.
    Needed by the outcome-carrying `lower_sim` to place `seq`'s second half and to
    read the fall-through position. -/
theorem emitCF_length (dat : Data) (dpos fnPos : Name → Nat) (bp cp : List Nat) (ep here : Nat)
    (stmt : PStmt) :
    (emitCF dat dpos fnPos bp cp ep here stmt).length = csize stmt := by
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
  | cref rd d =>
      simp only [emitCF, csize, List.length_append, crefI_length, storeSlotI_length]
  | call argc rvc f args rets =>
      simp only [emitCF, csize, List.length_append, List.length_cons,
                 List.length_nil, marshalI_length]
  | _ => rfl

/-- Sanity: on the straight-line fragment, `emitCF` is exactly `emit` (the
    control-flow arms never fire), so all the existing `#guard`s against
    `Compile.lower` carry over unchanged. -/
example (dat : Data) (dpos fnPos : Name → Nat) (bp cp : List Nat) (ep here : Nat) :
    emitCF dat dpos fnPos bp cp ep here (.addi 12 5 (BitVec.ofNat 12 3))
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
def realResolve (dat : Data) (dats : List (Name × Nat)) (body : PStmt) : Option (List Instr) :=
  let syms : List LowIR.Compile.SymInstr := (lower dat [] [] 0 body).run' 1
  let (flat, lbls, _) := layoutItems (syms ++ [LowIR.Compile.SymInstr.label 0]) 0
  (flat.mapM (fun p => resolveOne lbls [] dats p)).map List.flatten

/-- `emitCF` matched against the real pipeline, epilogue at the body's end.
    `dpos d = (dats.lookup d).getD 0` mirrors `resolveOne`'s data-offset read. -/
def matchesReal (dat : Data) (dats : List (Name × Nat)) (body : PStmt) : Bool :=
  realResolve dat dats body
    == some (emitCF dat (fun d => (dats.lookup d).getD 0) (fun _ => 0) [] [] (4 * csize body) 0 body)

-- `strlen` (`while`), `strtoull` (`block`+`while`+`ife`+`brkB`), `hex0` (nested
-- `ife`s + `while` + `ret`): the validated IR↔assembly mapping, checked concretely.
#guard matchesReal [] [] LowIR.Prog.Lib.strlenF.body
#guard matchesReal [] [] LowIR.Prog.Lib.strtoullF.body
#guard matchesReal [] [] LowIR.Prog.Lib.hex0F.body
#guard matchesReal [] [] LowIR.Prog.Lib.hex1F.body

-- `clen`: the synthConst (data-length materialise) + slot-store, validated against
-- the real compiler for several lengths and both `rd = 0` (discard) and `rd ≠ 0`.
#guard matchesReal [("tbl", [1, 2, 3])] [] (.clen 5 "tbl")
#guard matchesReal [("tbl", List.replicate 300 0)] [] (.clen 11 "tbl")
#guard matchesReal [("tbl", [1, 2, 3])] [] (.clen 0 "tbl")
#guard matchesReal [("tbl", [7])] [] (.seq (.clen 5 "tbl") (.addi 6 5 (BitVec.ofNat 12 1)))

-- `cref`: pc-read + delta-synth + add + slot-store, validated against `resolveOne`
-- at several data offsets (the `dats` table) and both `rd = 0` and `rd ≠ 0`.
#guard matchesReal [("tbl", [1, 2, 3])] [("tbl", 100)] (.cref 5 "tbl")
#guard matchesReal [("tbl", [1, 2, 3])] [("tbl", 65540)] (.cref 20 "tbl")
#guard matchesReal [("tbl", [1, 2, 3])] [("tbl", 100)] (.cref 0 "tbl")
#guard matchesReal [("a", [1]), ("b", [2])] [("a", 40), ("b", 48)]
  (.seq (.cref 5 "a") (.cref 6 "b"))

/-! ### Whole-program validation: prologue + body + epilogue vs the real compiler.

    The single-body `matchesReal` above can't exercise `.call` (isolated bodies have
    no callee table). `matchesRealProg` runs the FROZEN `compileProgT` and checks,
    per function, that its resolved slice equals `prologueI ++ emitCF … ++ epilogueI`
    at the layout's `fnTab` position — the decidable cross-check of the whole emit
    surface (marshalling, the `jal RA` call site, prologue/epilogue) BEFORE any
    proof leans on it. -/
open LowIR.Compile (compileProgT)

/-- The pre-frame part of the resolved prologue (a direct transcription of
    `Compile.prologue` with `.ins` unwrapped and `storeSlot` → `storeSlotI`,
    minus the zero-frame segment): drop sp, save ra, park params, zero slots,
    materialize frameReg. -/
def prologuePreI (fd : FunDef) : List Instr :=
  let params := fd.params.toList
  [Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))), Instr.sd SP RA 0]
  ++ params.zipIdx.flatMap (fun pi => storeSlotI pi.1 (A pi.2))
  ++ ((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !params.contains r && r != fd.frameReg)).map
       (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r)))
  ++ (if fd.frameReg = 0 then [] else
        [Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd))] ++ storeSlotI fd.frameReg T0)

/-- The zero-frame segment (`sd SP 0` at each user-frame word offset) — the
    machine half of the zero-init frame agreement (RESUME-CALL ★). -/
def frameZeroI (fd : FunDef) : List Instr :=
  (List.range (fd.frameSize / 8)).map
    (fun i => Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i)))

def prologueI (fd : FunDef) : List Instr := prologuePreI fd ++ frameZeroI fd

/-- The RESOLVED epilogue: rets → `a0..`, restore ra + sp, `jalr x0 ra 0`. -/
def epilogueI (fd : FunDef) : List Instr :=
  fd.rets.toList.zipIdx.flatMap (fun ri => loadSlotI ri.1 (A ri.2))
  ++ [Instr.ld RA SP 0, Instr.addi SP SP (BitVec.ofNat 12 (totalFrame fd)), Instr.jalr 0 RA 0]

def prologueSize (fd : FunDef) : Nat := (prologueI fd).length
def epilogueSize (fd : FunDef) : Nat := fd.rvc + 3

/-- Per-function cross-check against the resolved compiler output. -/
def matchesRealProg (P : Program) (entry : Name) : Bool :=
  match compileProgT P entry with
  | none => false
  | some (instrs, fns, dats) =>
      let dpos  : Name → Nat := fun d => (dats.lookup d).getD 0
      let fnPos : Name → Nat := fun f => (fns.lookup f).getD 0
      P.env.all fun nf =>
        let fd := nf.2
        let p := fnPos nf.1
        let bodyPos := p + 4 * (prologueI fd).length
        let epiPos := bodyPos + 4 * csize fd.body
        let expected :=
          prologueI fd ++ emitCF P.data dpos fnPos [] [] epiPos bodyPos fd.body ++ epilogueI fd
        (instrs.drop (p / 4)).take expected.length == expected

-- `caller`→`frameLocal` (arg/ret marshalling + one call), `chainEnv` (3-deep
-- nesting), `recSum` (recursion): the call emit surface, validated end-to-end.
#guard matchesRealProg ⟨[("caller", LowIR.Prog.caller),
                         ("frameLocal", LowIR.Prog.frameLocal)], []⟩ "caller"
#guard matchesRealProg ⟨LowIR.Prog.chainEnv, []⟩ "f3"
#guard matchesRealProg ⟨LowIR.Prog.recSum, []⟩ "rec"
-- corner: a call whose returns include x0 (discarded ret store) and a duplicate
-- argument register (last-wins marshalling) — both exercised against the compiler.
#guard matchesRealProg
  ⟨[("cornerC", { argc := 2, rvc := 2, params := #v[10, 11], rets := #v[10, 11],
                  frameSize := 0, frameReg := 5,
                  body := .call 2 2 "cornerK" #v[10, 10] #v[0, 12] }),
    ("cornerK", { argc := 2, rvc := 2, params := #v[10, 11], rets := #v[10, 11],
                  frameSize := 0, frameReg := 5, body := .skip })], []⟩ "cornerC"

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

/-! ## Call-marshalling simulators (`run_marshalFrom` / `run_retStoresFrom`).

    The call site loads argc args into `a0..` then (after the callee returns)
    parks the rvc returns from `a0..`; the prologue parks params from `a0..`. Each
    is a list fold of single-slot loads/stores whose A-register indices come from
    `zipIdx`. Both lemmas induct on the reg list with the index base generalized —
    the A-registers are all `≥ 10`, so writing them preserves `StInv` (which
    constrains only x2 and the memory slots), and distinct indices keep earlier
    loads/stores live. -/

/-- Run `marshalI`'s arg loads (indices `base, base+1, …`): each `A (base+j)` ends
    holding `s.rget args[j]`, `StInv` and memory preserved, registers outside
    `A base … A (base+len−1)` untouched. -/
theorem run_marshalFrom (L : Layout) (fd : FunDef) (holes : List Hole) (s : St) :
    ∀ (args : List Nat) (base q : Nat) (m : State),
      StInv L fd holes s m →
      m.pc = L.codeBase + BitVec.ofNat 64 q →
      Emitted L q ((args.zipIdx base).flatMap fun ri => loadSlotI ri.1 (A ri.2)) →
      (∀ a ∈ args, a ≤ maxRegF fd) →
      (∀ a ∈ args, slotOff a < 2 ^ 11) →
      ∃ k, StInv L fd holes s (stepN k m)
         ∧ (stepN k m).pc = L.codeBase + BitVec.ofNat 64 (q + 4 * args.length)
         ∧ (stepN k m).mem = m.mem
         ∧ (∀ j, (hj : j < args.length) → (stepN k m).rget (A (base + j)) = s.rget args[j])
         ∧ (∀ t, (∀ j, (hj : j < args.length) → t ≠ A (base + j)) → (stepN k m).rget t = m.rget t)
  | [], base, q, m, hinv, hpc, _, _, _ =>
      ⟨0, hinv, by simpa using hpc, rfl, fun j hj => by simp at hj, fun t _ => rfl⟩
  | a :: rest, base, q, m, hinv, hpc, hem, hreg, hfr => by
      have hAb : A base = 10 + base := rfl
      have h1run : stepN 1 m = step m := rfl
      simp only [List.zipIdx_cons, List.flatMap_cons] at hem
      have hemL : Emitted L q (loadSlotI a (A base)) := Emitted_append_left _ _ _ _ hem
      obtain ⟨hinv1, h1pc, h1mem, h1v, h1oth⟩ :=
        run_load L fd holes s m a (A base) q hinv (hreg a (by simp))
          (hfr a (by simp)) (by rw [hAb]; omega) (by rw [hAb]; omega) hpc hemL
      have hemR : Emitted L (q + 4)
          ((rest.zipIdx (base + 1)).flatMap fun ri => loadSlotI ri.1 (A ri.2)) := by
        have h := Emitted_append_right _ _ _ _ hem
        rwa [loadSlotI_length, Nat.mul_one] at h
      obtain ⟨k, hinvK, hpcK, hmemK, hvK, hothK⟩ :=
        run_marshalFrom L fd holes s rest (base + 1) (q + 4) (step m) hinv1 h1pc hemR
          (fun x hx => hreg x (List.mem_cons_of_mem a hx))
          (fun x hx => hfr x (List.mem_cons_of_mem a hx))
      refine ⟨1 + k, ?_, ?_, ?_, ?_, ?_⟩
      · rw [stepN_add, h1run]; exact hinvK
      · rw [stepN_add, h1run, hpcK]; apply pc_congr; simp only [List.length_cons]; omega
      · rw [stepN_add, h1run, hmemK, h1mem]
      · intro j hj
        rw [stepN_add, h1run]
        have hneA : ∀ j' : Nat, A base ≠ A (base + 1 + j') := by
          intro j' h
          have hn : (10 + base : Nat) = 10 + (base + 1 + j') := h
          omega
        cases j with
        | zero =>
            simp only [Nat.add_zero, List.getElem_cons_zero]
            rw [hothK (A base) (fun j' _ => hneA j'), h1v]
        | succ j' =>
            have hj'' : j' < rest.length := by simp only [List.length_cons] at hj; omega
            rw [show base + (j' + 1) = (base + 1) + j' from by omega, hvK j' hj'']
            simp only [List.getElem_cons_succ]
      · intro t hne
        rw [stepN_add, h1run,
            hothK t (fun j' hj' => by
              have h := hne (j' + 1) (by simp only [List.length_cons]; omega)
              rwa [show base + (j' + 1) = base + 1 + j' from by omega] at h),
            h1oth t (by have h := hne 0 (by simp); rwa [Nat.add_zero] at h)]

/-- Run `retStoresI`'s stores (indices `base, base+1, …`): starting from a machine
    state whose `A (base+i)` hold the return values `vs[i]`, the `rvc` slot stores
    mirror the IL last-wins fold `(rets.zip vs).foldl rset s` — same order, `rd=0`
    ret emits 0 instructions vs an invisible `rset 0`. `StInv` is maintained across
    each single slot write (`run_storeFrom`), whose register-preservation clause
    keeps the yet-unstored `A` values live through earlier stores. -/
theorem run_retStoresFrom (L : Layout) (fd : FunDef) (holes : List Hole)
    (hnw : ∀ s : St, s.sp.toNat + userOff fd ≤ 2 ^ 64)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64) :
    ∀ (rets : List Nat) (vs : List Word) (base q : Nat) (s : St) (m : State),
      StInv L fd holes s m →
      m.pc = L.codeBase + BitVec.ofNat 64 q →
      Emitted L q ((rets.zipIdx base).flatMap fun ri => storeSlotI ri.1 (A ri.2)) →
      (∀ r ∈ rets, r ≤ maxRegF fd) →
      (∀ r ∈ rets, slotOff r < 2 ^ 11) →
      (L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
         ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat) →
      rets.length = vs.length →
      (∀ i, (hi : i < vs.length) → m.rget (A (base + i)) = vs[i]) →
      ∃ k, StInv L fd holes ((rets.zip vs).foldl (fun st rv => st.rset rv.1 rv.2) s) (stepN k m)
         ∧ (stepN k m).pc = L.codeBase
             + BitVec.ofNat 64 (q + 4 * ((rets.zipIdx base).flatMap
                 fun ri => storeSlotI ri.1 (A ri.2)).length)
         ∧ FramesPres holes s.sp fd m (stepN k m) := by
  intro rets
  induction rets with
  | nil =>
      intro vs base q s m hinv hpc _ _ _ _ _ _
      refine ⟨0, ?_, ?_, ?_⟩
      · simpa using hinv
      · simp only [stepN_zero, List.zipIdx_nil, List.flatMap_nil, List.length_nil,
                   Nat.mul_zero, Nat.add_zero]; exact hpc
      · exact FramesPres_of_mem_eq holes s.sp fd m (stepN 0 m) (by rw [stepN_zero])
  | cons r rest ih =>
      intro vs base q s m hinv hpc hem hrd hfr hbd hlen hval
      obtain ⟨v, vrest, rfl⟩ : ∃ v vrest, vs = v :: vrest := by
        cases vs with
        | nil => simp at hlen
        | cons v vrest => exact ⟨v, vrest, rfl⟩
      have hsp : (s.rset r v).sp = s.sp := by
        by_cases h : r = 0 <;> simp [LowIR.Prog.St.rset, h]
      simp only [List.zipIdx_cons, List.flatMap_cons] at hem
      have hemL : Emitted L q (storeSlotI r (A base)) :=
        Emitted_append_left _ _ _ _ hem
      have hemR : Emitted L (q + 4 * (storeSlotI r (A base)).length)
          ((rest.zipIdx (base + 1)).flatMap fun ri => storeSlotI ri.1 (A ri.2)) :=
        Emitted_append_right _ _ _ _ hem
      have hT : m.rget (A base) = v := by
        have h := hval 0 (by simp)
        rwa [Nat.add_zero, List.getElem_cons_zero] at h
      obtain ⟨ks, hSts, hStpc, hFrs, hRegs⟩ :=
        run_storeFrom L fd holes s m r (A base) v q hinv hT hpc hemL
          (hrd r (by simp)) (hfr r (by simp)) (hnw s) hseg hblob hbd
      -- recurse on the tail from the post-store machine state
      have hbd' : L.codeBase.toNat + L.blobLen ≤ (s.rset r v).sp.toNat
          ∨ (s.rset r v).sp.toNat + userOff fd ≤ L.codeBase.toNat := by rw [hsp]; exact hbd
      have hlen' : rest.length = vrest.length := by
        simpa using hlen
      have hvalR : ∀ i, (hi : i < vrest.length) →
          (stepN ks m).rget (A (base + 1 + i)) = vrest[i] := by
        intro i hi
        rw [hRegs (A (base + 1 + i))]
        have h := hval (i + 1) (by simp only [List.length_cons]; omega)
        rw [show base + (i + 1) = base + 1 + i from by omega,
            List.getElem_cons_succ] at h
        exact h
      obtain ⟨k, hStK, hpcK, hFrK⟩ :=
        ih vrest (base + 1) (q + 4 * (storeSlotI r (A base)).length) (s.rset r v) (stepN ks m)
          hSts hStpc hemR (fun x hx => hrd x (List.mem_cons_of_mem r hx))
          (fun x hx => hfr x (List.mem_cons_of_mem r hx)) hbd' hlen' hvalR
      refine ⟨ks + k, ?_, ?_, ?_⟩
      · rw [stepN_add]
        simpa only [List.zip_cons_cons, List.foldl_cons] using hStK
      · rw [stepN_add, hpcK]
        apply pc_congr
        simp only [List.zipIdx_cons, List.flatMap_cons, List.length_append]
        omega
      · rw [stepN_add]
        exact FramesPres_trans holes s.sp fd m (stepN ks m) (stepN k (stepN ks m))
          hFrs (by rw [hsp] at hFrK; exact hFrK)

/-! ## The prologue simulator (`prologue_sim`, RESUME-CALL W5).

    The machine prologue (`prologueI fd`) transforms a CALL-ENTRY machine state
    (x2 = the caller's sp, `a0..` = the argument values, ra = the return address)
    into the callee's entry state: it drops sp by `totalFrame` (= `userOff +
    frameSize`), saves ra at `[sp', sp'+8)`, parks the params from `a0..`,
    zero-inits every other register slot, and materializes the user-frame base
    into `frameReg`'s slot. We show the resulting machine state satisfies the
    callee's `StInv` against `frameEnter`'s IL state (with the P1 pad `= userOff`).

    The heart is the last-wins agreement between the machine's sequential param
    stores and the IL's `withParams` left fold: both write slot `params[i]` the
    value `argVals[i]` in order, so the last write to any register wins on both
    sides. We capture this with `parkFold` — literally `frameEnter`'s fold — and
    show the machine memory tracks it pointwise on slots, off a shifted base. -/

/-- The IL's `withParams` left fold, factored out (matches `frameEnter` verbatim):
    fold the `(param, argVal)` pairs into a register file, last write winning. -/
def parkFold (base : Nat → Word) (pairs : List (Nat × Word)) : Nat → Word :=
  pairs.foldl (fun rf pv => fun r => if r = pv.1 then pv.2 else rf r) base

@[simp] theorem parkFold_nil (base : Nat → Word) : parkFold base [] = base := rfl

theorem parkFold_cons (base : Nat → Word) (p : Nat × Word) (ps : List (Nat × Word)) :
    parkFold base (p :: ps) = parkFold (fun r => if r = p.1 then p.2 else base r) ps := rfl

/-- `parkFold b ps target` depends on `b` only through `b target`: two bases that
    agree at `target` give the same result (either `target` is a fold key — then
    the answer is a paired value — or it isn't, and the answer is `b target`). -/
theorem parkFold_base_congr (target : Nat) :
    ∀ (ps : List (Nat × Word)) (b1 b2 : Nat → Word), b1 target = b2 target →
      parkFold b1 ps target = parkFold b2 ps target
  | [], _, _, h => h
  | p :: ps, b1, b2, h => by
      rw [parkFold_cons, parkFold_cons]
      apply parkFold_base_congr target ps
      by_cases hp : target = p.1
      · rw [if_pos hp, if_pos hp]
      · rw [if_neg hp, if_neg hp]; exact h

/-- If `target` is not among the fold keys, `parkFold` just reads the base there. -/
theorem parkFold_not_mem (target : Nat) :
    ∀ (ps : List (Nat × Word)) (b : Nat → Word), target ∉ ps.map Prod.fst →
      parkFold b ps target = b target
  | [], _, _ => rfl
  | p :: ps, b, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [parkFold_cons, parkFold_not_mem target ps _ h.2]
      simp only [if_neg h.1]

/-- If `target` IS a fold key, the last write to it wins and the base is
    irrelevant: `parkFold` is independent of the base at that target. -/
theorem parkFold_mem_indep (target : Nat) :
    ∀ (ps : List (Nat × Word)) (b1 b2 : Nat → Word), target ∈ ps.map Prod.fst →
      parkFold b1 ps target = parkFold b2 ps target
  | [], _, _, h => by simp at h
  | p :: ps, b1, b2, h => by
      rw [parkFold_cons, parkFold_cons]
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with hh | hh
      · exact parkFold_base_congr target ps _ _ (by rw [if_pos hh, if_pos hh])
      · exact parkFold_mem_indep target ps _ _ hh

/-- `Installed` reads `m` only through `m.mem` (fetch overrides `pc`), so a `pc`
    write preserves it. -/
theorem Installed_setPc (L : Layout) (m : State) (p : Word) (h : Installed L m) :
    Installed L (m.setPc p) := h

@[simp] theorem loadWord_setPc (m : State) (p a : Word) :
    (m.setPc p).loadWord a = m.loadWord a := rfl

/-- `Installed` depends on `m` only through `m.mem` (fetch overrides `pc`), so any
    two states with equal memory install the same blob. -/
theorem Installed_congr (L : Layout) (m m' : State) (hmem : m'.mem = m.mem)
    (h : Installed L m) : Installed L m' := by
  obtain ⟨hc, hd⟩ := h
  refine ⟨fun j hj => ?_, fun i hi => by rw [hmem]; exact hd i hi⟩
  have : fetch32 { m' with pc := L.codeBase + BitVec.ofNat 64 (4 * j) }
       = fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) } := by
    simp only [fetch32, hmem]
  rw [this]; exact hc j hj

/-- Run one prologue slot store `sd SP tsrc (slotOff r)` (`r ≠ 0`, `r ≤ maxRegF`)
    from a machine state whose x2 already holds the callee sp `sp`: it writes
    `m.rget tsrc` into slot `r`, advances pc, and leaves every register, the whole
    memory outside the frame hole `[sp, sp+userOff)`, `Installed`, and every OTHER
    live slot untouched. The bespoke (StInv-free) analogue of `run_storeFrom` used
    inside the prologue, where no full `StInv` holds mid-parking. -/
theorem run_slotStore (L : Layout) (fd : FunDef) (m : State) (sp : Word) (r tsrc q : Nat)
    (hr1 : 1 ≤ r) (hrm : r ≤ maxRegF fd)
    (hsp : m.rget SP = sp)
    (hpc : m.pc = L.codeBase + BitVec.ofNat 64 q)
    (hinst : Installed L m)
    (hem : Emitted L q [Instr.sd SP tsrc (BitVec.ofNat 12 (slotOff r))])
    (huser : userOff fd ≤ 2000)
    (hnw : sp.toNat + userOff fd ≤ 2 ^ 64)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ sp.toNat ∨ sp.toNat + userOff fd ≤ L.codeBase.toNat) :
    (step m).pc = L.codeBase + BitVec.ofNat 64 (q + 4)
    ∧ (∀ t, (step m).rget t = m.rget t)
    ∧ Installed L (step m)
    ∧ (∀ a : Word, ¬ memRange a sp (userOff fd) → (step m).mem a = m.mem a)
    ∧ (step m).loadWord (sp + BitVec.ofNat 64 (slotOff r)) = m.rget tsrc
    ∧ (∀ target : Nat, target ≠ r → 1 ≤ target → target ≤ maxRegF fd →
         (step m).loadWord (sp + BitVec.ofNat 64 (slotOff target))
           = m.loadWord (sp + BitVec.ofNat 64 (slotOff target)))
    ∧ (step m).loadWord sp = m.loadWord sp := by
  have hslot8 : slotOff r + 8 ≤ userOff fd := slotOff_add8_le_userOff fd r hrm
  have hsl16 : 16 ≤ slotOff r := by unfold slotOff; omega
  have hslot : slotOff r < 2 ^ 11 := by omega
  have hlen : (0 : Nat) < ([Instr.sd SP tsrc (BitVec.ofNat 12 (slotOff r))]).length := by simp
  have hd : decode (fetch32 m) = Instr.sd SP tsrc (BitVec.ofNat 12 (slotOff r)) := by
    have h := decode_at L m m q [Instr.sd SP tsrc (BitVec.ofNat 12 (slotOff r))] hem hinst 0 hlen
                (by simpa using hpc) rfl
    simpa using h
  have hatoNat : (sp + BitVec.ofNat 64 (slotOff r)).toNat = sp.toNat + slotOff r :=
    slotAddr_toNat sp r (by omega)
  have hwa : (sp + BitVec.ofNat 64 (slotOff r)).toNat + 8 ≤ 2 ^ 64 := by rw [hatoNat]; omega
  have hstep : step m
      = (m.storeWord (sp + BitVec.ofNat 64 (slotOff r)) (m.rget tsrc)).setPc (m.pc + 4) := by
    rw [step_sd m SP tsrc _ hd, hsp, signExtend_ofNat_lt (slotOff r) hslot]
  have hInstStore : Installed L (m.storeWord (sp + BitVec.ofNat 64 (slotOff r)) (m.rget tsrc)) := by
    apply Installed_storeWord_off_blob L m _ _ hinst hseg hblob hwa
    rw [hatoNat]; rcases hbd with hbd | hbd
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep, pc_setPc, hpc, pc_add4]
  · intro t; rw [hstep, rget_setPc, State_storeWord_rget]
  · rw [hstep]; exact Installed_setPc L _ _ hInstStore
  · intro a hna
    rw [hstep, mem_setPc]
    apply Rv64i.storeWord_mem_outside m _ _ a hwa
    rw [hatoNat]
    rcases Nat.lt_or_ge a.toNat sp.toNat with hlt | hge
    · exact Or.inl (by omega)
    · exact Or.inr (by
        have : ¬ a.toNat < sp.toNat + userOff fd := fun hh => hna ⟨hge, hh⟩
        omega)
  · rw [hstep, loadWord_setPc]; exact loadWord_store_slot_same m sp (m.rget tsrc) r
  · intro target htr _ htm
    have htslot8 : slotOff target + 8 ≤ userOff fd := slotOff_add8_le_userOff fd target htm
    rw [hstep, loadWord_setPc]
    exact loadWord_store_slot_ne m sp (m.rget tsrc) r target (Ne.symm htr) (by omega) (by omega)
  · -- the ra word `[sp, sp+8)` (offset 0) is below every register slot (`slotOff ≥ 16`)
    rw [hstep, loadWord_setPc]
    apply Rv64i.loadWord_storeWord_disjoint m (sp + BitVec.ofNat 64 (slotOff r)) sp (m.rget tsrc) hwa
      (by omega)
    rw [hatoNat]; exact Or.inr (by omega)

/-- Run the prologue's param-parking segment (`params.zipIdx.flatMap (storeSlotI
    pi.1 (A pi.2))`) from a machine state whose x2 = the callee sp and whose
    `a(base+i)` hold the argument values: the machine memory's slot contents track
    the IL `parkFold` (= `frameEnter`'s `withParams`) pointwise, off a base that is
    the ENTRY slot contents. All registers, `Installed`, and off-frame memory are
    preserved. The last-wins heart of `prologue_sim`. -/
theorem run_parkParams (L : Layout) (fd : FunDef) (sp : Word)
    (huser : userOff fd ≤ 2000)
    (hnw : sp.toNat + userOff fd ≤ 2 ^ 64)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ sp.toNat ∨ sp.toNat + userOff fd ≤ L.codeBase.toNat) :
    ∀ (params : List Nat) (argVals : List Word) (base q : Nat) (m : State),
      m.rget SP = sp →
      m.pc = L.codeBase + BitVec.ofNat 64 q →
      Emitted L q ((params.zipIdx base).flatMap fun pi => storeSlotI pi.1 (A pi.2)) →
      Installed L m →
      (∀ p ∈ params, p ≤ maxRegF fd) →
      params.length = argVals.length →
      (∀ i, (hi : i < argVals.length) → m.rget (A (base + i)) = argVals[i]) →
      ∃ k, (stepN k m).rget SP = sp
         ∧ (stepN k m).pc = L.codeBase + BitVec.ofNat 64
             (q + 4 * ((params.zipIdx base).flatMap fun pi => storeSlotI pi.1 (A pi.2)).length)
         ∧ (∀ t, (stepN k m).rget t = m.rget t)
         ∧ Installed L (stepN k m)
         ∧ (∀ a : Word, ¬ memRange a sp (userOff fd) → (stepN k m).mem a = m.mem a)
         ∧ (∀ target : Nat, 1 ≤ target → target ≤ maxRegF fd →
              (stepN k m).loadWord (sp + BitVec.ofNat 64 (slotOff target))
                = parkFold (fun t => m.loadWord (sp + BitVec.ofNat 64 (slotOff t)))
                    (params.zip argVals) target)
         ∧ (stepN k m).loadWord sp = m.loadWord sp := by
  intro params
  induction params with
  | nil =>
      intro argVals base q m hsp hpc _ hinst _ _ _
      refine ⟨0, by simpa using hsp, ?_, fun t => by rw [stepN_zero], by simpa using hinst,
              fun a _ => by rw [stepN_zero], fun target _ _ => ?_, by rw [stepN_zero]⟩
      · simp only [stepN_zero, List.zipIdx_nil, List.flatMap_nil, List.length_nil, Nat.mul_zero,
                   Nat.add_zero]; exact hpc
      · rw [stepN_zero]; rfl
  | cons r rest ih =>
      intro argVals base q m hsp hpc hem hinst hreg hlen hval
      obtain ⟨v, vrest, rfl⟩ : ∃ v vrest, argVals = v :: vrest := by
        cases argVals with
        | nil => simp at hlen
        | cons v vrest => exact ⟨v, vrest, rfl⟩
      simp only [List.zipIdx_cons, List.flatMap_cons] at hem
      have hv0 : m.rget (A base) = v := by
        have h := hval 0 (by simp)
        rwa [Nat.add_zero, List.getElem_cons_zero] at h
      by_cases hr0 : r = 0
      · -- reg-0 param: `storeSlotI 0 _ = []`, no machine step
        subst hr0
        have hs0 : storeSlotI 0 (A base) = [] := by simp [storeSlotI]
        rw [hs0, List.nil_append] at hem
        have hval' : ∀ i, (hi : i < vrest.length) → m.rget (A (base + 1 + i)) = vrest[i] := by
          intro i hi
          have h := hval (i + 1) (by simp only [List.length_cons]; omega)
          rw [show base + (i + 1) = base + 1 + i from by omega, List.getElem_cons_succ] at h
          exact h
        obtain ⟨k, hspK, hpcK, hregK, hinstK, hmemK, hslotK, hraK⟩ :=
          ih vrest (base + 1) q m hsp hpc hem hinst
            (fun p hp => hreg p (List.mem_cons_of_mem 0 hp)) (by simpa using hlen) hval'
        refine ⟨k, hspK, ?_, hregK, hinstK, hmemK, ?_, hraK⟩
        · rw [hpcK]; apply pc_congr
          simp only [List.zipIdx_cons, List.flatMap_cons, hs0, List.nil_append]
        · intro target ht1 htm
          rw [hslotK target ht1 htm]
          rw [show (0 :: rest).zip (v :: vrest) = (0, v) :: rest.zip vrest from rfl, parkFold_cons]
          apply parkFold_base_congr target
          have htne : target ≠ 0 := by omega
          simp only [if_neg htne]
      · -- real param store
        have hemL : Emitted L q [Instr.sd SP (A base) (BitVec.ofNat 12 (slotOff r))] := by
          have h := Emitted_append_left _ _ _ _ hem
          rwa [storeSlotI, if_neg hr0] at h
        obtain ⟨hpc1, hreg1, hinst1, hmem1, hslotr, hslotne, hra1⟩ :=
          run_slotStore L fd m sp r (A base) q (by omega) (hreg r (by simp)) hsp hpc hinst hemL
            huser hnw hseg hblob hbd
        have hemR : Emitted L (q + 4)
            ((rest.zipIdx (base + 1)).flatMap fun pi => storeSlotI pi.1 (A pi.2)) := by
          have h := Emitted_append_right _ _ _ _ hem
          rw [storeSlotI, if_neg hr0, List.length_singleton, Nat.mul_one] at h; exact h
        have hstep1 : stepN 1 m = step m := rfl
        have hsp' : (step m).rget SP = sp := by rw [hreg1]; exact hsp
        have hval' : ∀ i, (hi : i < vrest.length) → (step m).rget (A (base + 1 + i)) = vrest[i] := by
          intro i hi
          rw [hreg1 (A (base + 1 + i))]
          have h := hval (i + 1) (by simp only [List.length_cons]; omega)
          rw [show base + (i + 1) = base + 1 + i from by omega, List.getElem_cons_succ] at h
          exact h
        obtain ⟨k, hspK, hpcK, hregK, hinstK, hmemK, hslotK, hraK⟩ :=
          ih vrest (base + 1) (q + 4) (step m) hsp' hpc1 hemR hinst1
            (fun p hp => hreg p (List.mem_cons_of_mem r hp)) (by simpa using hlen) hval'
        refine ⟨1 + k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [stepN_add, hstep1]; exact hspK
        · rw [stepN_add, hstep1, hpcK]; apply pc_congr
          simp only [List.zipIdx_cons, List.flatMap_cons, storeSlotI, if_neg hr0,
                     List.length_append, List.length_singleton]
          omega
        · intro t; rw [stepN_add, hstep1, hregK, hreg1]
        · rw [stepN_add, hstep1]; exact hinstK
        · intro a ha; rw [stepN_add, hstep1, hmemK a ha, hmem1 a ha]
        · intro target ht1 htm
          rw [stepN_add, hstep1, hslotK target ht1 htm,
              show (r :: rest).zip (v :: vrest) = (r, v) :: rest.zip vrest from rfl, parkFold_cons]
          apply parkFold_base_congr target
          by_cases htr : target = r
          · subst htr; rw [hslotr, hv0, if_pos rfl]
          · rw [hslotne target htr ht1 htm, if_neg htr]
        · rw [stepN_add, hstep1, hraK, hra1]

/-- Run the prologue's zero-init segment (`sd SP 0 (slotOff r)` for each register
    in the filtered list `regs`): every slot in `regs` ends holding `0` (the IL
    fresh-register-file zeroing), every slot OUTSIDE `regs` is untouched, and all
    registers / `Installed` / off-frame memory are preserved. -/
theorem run_zeroSlots (L : Layout) (fd : FunDef) (sp : Word)
    (huser : userOff fd ≤ 2000)
    (hnw : sp.toNat + userOff fd ≤ 2 ^ 64)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ sp.toNat ∨ sp.toNat + userOff fd ≤ L.codeBase.toNat) :
    ∀ (regs : List Nat) (q : Nat) (m : State),
      m.rget SP = sp →
      m.pc = L.codeBase + BitVec.ofNat 64 q →
      Emitted L q (regs.map (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r)))) →
      Installed L m →
      (∀ r ∈ regs, 1 ≤ r ∧ r ≤ maxRegF fd) →
      ∃ k, (stepN k m).rget SP = sp
         ∧ (stepN k m).pc = L.codeBase + BitVec.ofNat 64 (q + 4 * regs.length)
         ∧ (∀ t, (stepN k m).rget t = m.rget t)
         ∧ Installed L (stepN k m)
         ∧ (∀ a : Word, ¬ memRange a sp (userOff fd) → (stepN k m).mem a = m.mem a)
         ∧ (∀ target : Nat, target ∈ regs →
              (stepN k m).loadWord (sp + BitVec.ofNat 64 (slotOff target)) = 0)
         ∧ (∀ target : Nat, 1 ≤ target → target ≤ maxRegF fd → target ∉ regs →
              (stepN k m).loadWord (sp + BitVec.ofNat 64 (slotOff target))
                = m.loadWord (sp + BitVec.ofNat 64 (slotOff target)))
         ∧ (stepN k m).loadWord sp = m.loadWord sp := by
  intro regs
  induction regs with
  | nil =>
      intro q m hsp hpc _ hinst _
      refine ⟨0, by simpa using hsp, ?_, fun t => by rw [stepN_zero], by simpa using hinst,
              fun a _ => by rw [stepN_zero], fun target ht => by simp at ht,
              fun target _ _ _ => by rw [stepN_zero], by rw [stepN_zero]⟩
      simp only [stepN_zero, List.length_nil, Nat.mul_zero, Nat.add_zero]; exact hpc
  | cons r rest ih =>
      intro q m hsp hpc hem hinst hbounds
      simp only [List.map_cons] at hem
      obtain ⟨hr1, hrm⟩ := hbounds r (by simp)
      have hemL : Emitted L q [Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r))] :=
        Emitted_append_left _ _ _ _ hem
      obtain ⟨hpc1, hreg1, hinst1, hmem1, hslotr, hslotne, hra1⟩ :=
        run_slotStore L fd m sp r 0 q hr1 hrm hsp hpc hinst hemL huser hnw hseg hblob hbd
      have hslot_r0 : (step m).loadWord (sp + BitVec.ofNat 64 (slotOff r)) = 0 := by
        rw [hslotr]; rfl
      have hemR : Emitted L (q + 4)
          (rest.map (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r)))) := by
        have h := Emitted_append_right L q [Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r))] _ hem
        rw [List.length_singleton, Nat.mul_one] at h; exact h
      have hstep1 : stepN 1 m = step m := rfl
      have hsp' : (step m).rget SP = sp := by rw [hreg1]; exact hsp
      obtain ⟨k, hspK, hpcK, hregK, hinstK, hmemK, hzeroK, hpresK, hraK⟩ :=
        ih (q + 4) (step m) hsp' hpc1 hemR hinst1
          (fun p hp => hbounds p (List.mem_cons_of_mem r hp))
      refine ⟨1 + k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [stepN_add, hstep1]; exact hspK
      · rw [stepN_add, hstep1, hpcK]; apply pc_congr
        simp only [List.length_cons]; omega
      · intro t; rw [stepN_add, hstep1, hregK, hreg1]
      · rw [stepN_add, hstep1]; exact hinstK
      · intro a ha; rw [stepN_add, hstep1, hmemK a ha, hmem1 a ha]
      · intro target ht
        rw [stepN_add, hstep1]
        rcases List.mem_cons.mp ht with rfl | ht'
        · by_cases hmr : target ∈ rest
          · exact hzeroK target hmr
          · rw [hpresK target hr1 hrm hmr]; exact hslot_r0
        · exact hzeroK target ht'
      · intro target ht1 htm htni
        simp only [List.mem_cons, not_or] at htni
        rw [stepN_add, hstep1, hpresK target ht1 htm htni.2, hslotne target htni.1 ht1 htm]
      · rw [stepN_add, hstep1, hraK, hra1]

/-- Run the prologue's zero-frame segment (`sd SP 0 (userOff + 8·i)` for
    `i ∈ range N`): zeroes the user-frame bytes `[sp+userOff, sp+userOff+8N)`
    (matching the IL `frameEnter`'s `zeroRange`), and preserves every register,
    `Installed`, and all memory OUTSIDE that window (the slots + saved ra below,
    anything at/above). The machine half of the zero-init frame agreement. -/
theorem run_zeroFrame (L : Layout) (fd : FunDef) (sp : Word)
    (hfrO : userOff fd + fd.frameSize ≤ 2000)
    (hnwf : sp.toNat + (userOff fd + fd.frameSize) ≤ 2 ^ 64)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ sp.toNat
             ∨ sp.toNat + (userOff fd + fd.frameSize) ≤ L.codeBase.toNat) :
    ∀ (N q : Nat) (m : State),
      8 * N ≤ fd.frameSize →
      m.rget SP = sp →
      m.pc = L.codeBase + BitVec.ofNat 64 q →
      Emitted L q ((List.range N).map
        (fun i => Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i)))) →
      Installed L m →
      ∃ k, (stepN k m).rget SP = sp
         ∧ (stepN k m).pc = L.codeBase + BitVec.ofNat 64 (q + 4 * N)
         ∧ (∀ t, (stepN k m).rget t = m.rget t)
         ∧ Installed L (stepN k m)
         ∧ (∀ a : Word, memRange a (sp + BitVec.ofNat 64 (userOff fd)) (8 * N)
              → (stepN k m).mem a = 0)
         ∧ (∀ a : Word, ¬ memRange a (sp + BitVec.ofNat 64 (userOff fd)) (8 * N)
              → (stepN k m).mem a = m.mem a)
         ∧ (∀ a : Word, a.toNat + 8 ≤ sp.toNat + userOff fd
              → (stepN k m).loadWord a = m.loadWord a) := by
  intro N
  induction N with
  | zero =>
      intro q m _ hsp hpc _ hinst
      refine ⟨0, by simpa using hsp, ?_, fun t => by rw [stepN_zero], by simpa using hinst,
              ?_, fun a _ => by rw [stepN_zero], fun a _ => by rw [stepN_zero]⟩
      · simp only [stepN_zero, Nat.mul_zero, Nat.add_zero]; exact hpc
      · intro a ha; exact absurd ha (by unfold memRange; omega)
  | succ N ih =>
      intro q m hN hsp hpc hem hinst
      rw [List.range_succ, List.map_append] at hem
      have hemFirst : Emitted L q ((List.range N).map
          (fun i => Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i)))) :=
        Emitted_append_left _ _ _ _ hem
      have hemLast : Emitted L (q + 4 * N)
          [Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * N))] := by
        have h := Emitted_append_right L q ((List.range N).map
          (fun i => Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i)))) _ hem
        rwa [List.length_map, List.length_range] at h
      obtain ⟨kn, hspN, hpcN, hregN, hinstN, hzeroN, hpresN, hloadN⟩ :=
        ih q m (by omega) hsp hpc hemFirst hinst
      have hoff : userOff fd + 8 * N < 2 ^ 11 := by omega
      have haddr : (sp + BitVec.ofNat 64 (userOff fd + 8 * N)).toNat
          = sp.toNat + (userOff fd + 8 * N) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show userOff fd + 8 * N < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (by omega)]
      have hbaseN : (sp + BitVec.ofNat 64 (userOff fd)).toNat = sp.toNat + userOff fd := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show userOff fd < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
      have hwa : (sp + BitVec.ofNat 64 (userOff fd + 8 * N)).toNat + 8 ≤ 2 ^ 64 := by
        rw [haddr]; omega
      have hd : decode (fetch32 (stepN kn m))
          = Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * N)) := by
        have h := decode_at L (stepN kn m) (stepN kn m) (q + 4 * N) _ hemLast hinstN 0 (by simp)
          (by rw [hpcN]; apply pc_congr; omega) rfl
        simpa using h
      have hr0 : (stepN kn m).rget 0 = 0 := rfl
      have hstep : step (stepN kn m)
          = ((stepN kn m).storeWord (sp + BitVec.ofNat 64 (userOff fd + 8 * N)) 0).setPc
              ((stepN kn m).pc + 4) := by
        rw [step_sd (stepN kn m) SP 0 _ hd, hspN, signExtend_ofNat_lt _ hoff, hr0]
      have hstep1 : stepN (kn + 1) m = step (stepN kn m) := by rw [stepN_add]; rfl
      have hInstStore : Installed L
          ((stepN kn m).storeWord (sp + BitVec.ofNat 64 (userOff fd + 8 * N)) 0) := by
        apply Installed_storeWord_off_blob L (stepN kn m) _ _ hinstN hseg hblob hwa
        rw [haddr]; rcases hbd with hbd | hbd
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      refine ⟨kn + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstep1, hstep, rget_setPc, State_storeWord_rget]; exact hspN
      · rw [hstep1, hstep, pc_setPc, hpcN, pc_add4]; apply pc_congr; omega
      · intro t; rw [hstep1, hstep, rget_setPc, State_storeWord_rget]; exact hregN t
      · rw [hstep1, hstep]; exact Installed_setPc L _ _ hInstStore
      · intro a ha
        rw [hstep1, hstep, mem_setPc]
        simp only [memRange, hbaseN] at ha
        rcases Nat.lt_or_ge a.toNat (sp.toNat + userOff fd + 8 * N) with hin | hin
        · rw [Rv64i.storeWord_mem_outside (stepN kn m) _ 0 a hwa (Or.inl (by rw [haddr]; omega))]
          exact hzeroN a (by simp only [memRange, hbaseN]; refine ⟨?_, ?_⟩ <;> omega)
        · exact Rv64i.storeWord_zero_mem_inside (stepN kn m) _ a hwa
            (by rw [haddr]; omega) (by rw [haddr]; omega)
      · intro a ha
        rw [hstep1, hstep, mem_setPc]
        simp only [memRange, hbaseN] at ha
        rcases Nat.lt_or_ge a.toNat (sp.toNat + userOff fd) with hlt | hge
        · rw [Rv64i.storeWord_mem_outside (stepN kn m) _ 0 a hwa (Or.inl (by rw [haddr]; omega))]
          exact hpresN a (by simp only [memRange, hbaseN]; rintro ⟨_, _⟩; omega)
        · rw [Rv64i.storeWord_mem_outside (stepN kn m) _ 0 a hwa (Or.inr (by rw [haddr]; omega))]
          exact hpresN a (by simp only [memRange, hbaseN]; rintro ⟨_, _⟩; omega)
      · intro a ha
        rw [hstep1, hstep, loadWord_setPc,
            Rv64i.loadWord_storeWord_disjoint (stepN kn m) _ a 0 hwa (by omega)
              (Or.inr (by rw [haddr]; omega))]
        exact hloadN a ha

/-- **`prologue_sim` (RESUME-CALL W5).** Running `prologueI fd` from a call-entry
    machine state establishes the callee's `StInv` against `frameEnter`'s IL state
    (given the P1 pad `= userOff fd`, packaged as `hcsp`/`hcrg`): x2 drops to the
    callee sp, the register slots hold the callee's fresh register file (params
    parked last-wins ↔ `withParams`, everything else zeroed, `frameReg` ↦ frame
    base), ra is saved at `[sp', sp'+8)`, and pc reaches the body. `hmemF` is the
    entry memory agreement over the callee's `OffPriv` domain (the callee-frame
    obligation W7 discharges — see RESUME-CALL §2 C2); the caller-hole facts feed
    the LIFO ordering / no-wrap conjuncts. -/
theorem prologue_sim (L : Layout) (fd : FunDef) (holes : List Hole)
    (m : State) (sp0 ra : Word) (callee : St) (argVals : List Word) (p : Nat)
    (hpc : m.pc = L.codeBase + BitVec.ofNat 64 p)
    (hem : Emitted L p (prologueI fd))
    (hinst : Installed L m)
    (hsp0 : m.rget SP = sp0)
    (hra : m.rget RA = ra)
    (hargs : ∀ i, (hi : i < argVals.length) → m.rget (A i) = argVals[i])
    (hlen : fd.params.toList.length = argVals.length)
    (hparb : ∀ x ∈ fd.params.toList, x ≤ maxRegF fd)
    (hfrb : fd.frameReg ≤ maxRegF fd)
    (hcsp : callee.sp = sp0 - BitVec.ofNat 64 (totalFrame fd))
    (hcrg : ∀ r, 1 ≤ r → callee.rget r
              = if r = fd.frameReg then sp0 - BitVec.ofNat 64 fd.frameSize
                else parkFold (fun _ => 0) (fd.params.toList.zip argVals) r)
    (hmemF : ∀ a, OffPriv L ((callee.sp, userOff fd) :: holes) callee.sp a →
               ¬ memRange a (callee.sp + BitVec.ofNat 64 (userOff fd)) fd.frameSize →
               callee.mem a = m.mem a)
    (hcmemZ : ∀ a, memRange a (callee.sp + BitVec.ofNat 64 (userOff fd)) fd.frameSize →
               callee.mem a = 0)
    (htf : totalFrame fd ≤ 2000)
    (hfs8 : fd.frameSize % 8 = 0)
    (hsp0align : sp0.toNat % 8 = 0)
    (hsp0ge : totalFrame fd ≤ sp0.toNat)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbdc : L.codeBase.toNat + L.blobLen ≤ callee.sp.toNat
              ∨ callee.sp.toNat + userOff fd ≤ L.codeBase.toNat)
    (hbdcF : L.codeBase.toNat + L.blobLen ≤ callee.sp.toNat
              ∨ callee.sp.toNat + totalFrame fd ≤ L.codeBase.toNat)
    (hholes_ord : ∀ h ∈ holes, sp0.toNat ≤ (h.1 : Word).toNat)
    (hholes_nw : ∀ h ∈ holes, (h.1 : Word).toNat + h.2 ≤ 2 ^ 64) :
    ∃ k, StInv L fd ((callee.sp, userOff fd) :: holes) callee (stepN k m)
       ∧ (stepN k m).pc = L.codeBase + BitVec.ofNat 64 (p + 4 * prologueSize fd)
       ∧ (stepN k m).loadWord callee.sp = ra
       ∧ (∀ a : Word, ¬ memRange a callee.sp (totalFrame fd) → (stepN k m).mem a = m.mem a) := by
  -- ==== numeric helpers ====
  have hsp0lt : sp0.toNat < 2 ^ 64 := sp0.isLt
  have huser : userOff fd ≤ 2000 := by unfold totalFrame at htf; omega
  have huser16 : 16 ≤ userOff fd := by unfold userOff; omega
  have htf_eq : totalFrame fd = userOff fd + fd.frameSize := rfl
  have hcspN : callee.sp.toNat = sp0.toNat - totalFrame fd := by rw [hcsp]; bv_omega
  have hnwc : callee.sp.toNat + userOff fd ≤ 2 ^ 64 := by omega
  have hcsp8 : callee.sp.toNat % 8 = 0 := by
    have h1 : userOff fd % 8 = 0 := by unfold userOff; omega
    omega
  have hfb : callee.sp + BitVec.ofNat 64 (userOff fd) = sp0 - BitVec.ofNat 64 fd.frameSize := by
    rw [hcsp, htf_eq, ← BitVec.ofNat_add_ofNat]; bv_omega
  -- ==== split off the zero-frame segment, then peel the four pre-frame segments ====
  simp only [prologueI] at hem
  have hemFZ : Emitted L (p + 4 * (prologuePreI fd).length) (frameZeroI fd) :=
    Emitted_append_right _ _ _ _ hem
  replace hem := (Emitted_append_left _ _ _ _ hem : Emitted L p (prologuePreI fd))
  simp only [prologuePreI] at hem
  have hemG0 : Emitted L p [Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))),
                            Instr.sd SP RA 0] :=
    Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ hem))
  have hemG0p : Emitted L p ([Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))),
                              Instr.sd SP RA 0]
                            ++ fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)) :=
    Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ hem)
  have hempseg : Emitted L (p + 8)
      (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)) := by
    have h := Emitted_append_right L p
      [Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))), Instr.sd SP RA 0] _ hemG0p
    simpa using h
  -- ==== G0.1: addi SP SP (-totalFrame) → sp := callee.sp ====
  have hval0 : sp0 + (BitVec.ofInt 12 (-(totalFrame fd : Int))).signExtend 64 = callee.sp := by
    rw [signExtend_ofInt_12 _ (by omega) (by omega), hcsp,
        show BitVec.ofInt 64 (-(totalFrame fd : Int)) = -(BitVec.ofNat 64 (totalFrame fd)) from by
          rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]]
    bv_omega
  have hdA0 : decode (fetch32 m)
      = Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))) := by
    have h := decode_at L m m p _ hemG0 hinst 0 (by simp) (by simpa using hpc) rfl
    simpa using h
  have hstep0 : step m = (m.rset SP callee.sp).setPc (m.pc + 4) := by
    rw [step_addi m SP SP _ hdA0, hsp0, hval0]
  have hm1sp : (step m).rget SP = callee.sp := by
    rw [hstep0, rget_setPc, rget_rset_self m SP callee.sp (by decide)]
  have hm1ra : (step m).rget RA = ra := by
    rw [hstep0, rget_setPc, rget_rset_ne m SP RA callee.sp (by decide), hra]
  have hm1mem : (step m).mem = m.mem := by rw [hstep0, mem_setPc, mem_rset]
  have hm1inst : Installed L (step m) := by
    rw [hstep0]
    exact Installed_setPc L _ _ (Installed_congr L m _ (by rw [mem_rset]) hinst)
  have hm1pc : (step m).pc = L.codeBase + BitVec.ofNat 64 (p + 4) := by
    rw [hstep0, pc_setPc, hpc, pc_add4]
  have hm1Areg : ∀ i, (step m).rget (A i) = m.rget (A i) := by
    intro i; rw [hstep0, rget_setPc, rget_rset_ne m SP (A i) callee.sp (by show 10 + i ≠ 2; omega)]
  -- ==== G0.2: sd SP RA 0 → store ra at [callee.sp, +8) ====
  have hdA1 : decode (fetch32 (step m)) = Instr.sd SP RA 0 := by
    have h := decode_at L m (step m) p _ hemG0 hinst 1 (by simp) (by rw [hm1pc]) hm1mem
    simpa using h
  have haddr02 : (step m).rget SP + ((0 : BitVec 12).signExtend 64) = callee.sp := by
    rw [hm1sp, show ((0 : BitVec 12).signExtend 64) = (0 : BitVec 64) from by decide]; simp
  have hstep1 : step (step m)
      = ((step m).storeWord callee.sp ra).setPc ((step m).pc + 4) := by
    rw [step_sd (step m) SP RA _ hdA1, hm1ra, haddr02]
  -- m2 := step (step m)
  have hSN2 : stepN 2 m = step (step m) := rfl
  have hm2sp : (step (step m)).rget SP = callee.sp := by
    rw [hstep1, rget_setPc, State_storeWord_rget]; exact hm1sp
  have hm2mem_ra : (step (step m)).loadWord callee.sp = ra := by
    rw [hstep1, loadWord_setPc, Rv64i.loadWord_storeWord_same]
  have hm2inst : Installed L (step (step m)) := by
    rw [hstep1]
    refine Installed_setPc L _ _ (Installed_storeWord_off_blob L (step m) callee.sp ra hm1inst hseg hblob
      (by omega) ?_)
    rcases hbdc with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hm2pc : (step (step m)).pc = L.codeBase + BitVec.ofNat 64 (p + 8) := by
    rw [hstep1, pc_setPc, hm1pc, pc_add4]
  have hm2Areg : ∀ i, (step (step m)).rget (A i) = m.rget (A i) := by
    intro i; rw [hstep1, rget_setPc, State_storeWord_rget]; exact hm1Areg i
  have hm2mem_off : ∀ a : Word, ¬ memRange a callee.sp (userOff fd) →
      (step (step m)).mem a = m.mem a := by
    intro a hna
    rw [hstep1, mem_setPc]
    rw [Rv64i.storeWord_mem_outside (step m) callee.sp ra a (by omega) ?_, hm1mem]
    rcases Nat.lt_or_ge a.toNat callee.sp.toNat with hlt | hge
    · exact Or.inl (by omega)
    · exact Or.inr (by
        have : ¬ a.toNat < callee.sp.toNat + userOff fd := fun hh => hna ⟨hge, hh⟩
        omega)
  -- ==== G1: park params ====
  obtain ⟨kP, hPsp, hPpc, hPreg, hPinst, hPmem, hPslot, hPra⟩ :=
    run_parkParams L fd callee.sp huser hnwc hseg hblob hbdc
      fd.params.toList argVals 0 (p + 8) (step (step m)) hm2sp hm2pc hempseg hm2inst hparb hlen
      (fun i hi => by rw [Nat.zero_add, hm2Areg]; exact hargs i hi)
  -- ==== G2: zero-init the remaining slots ====
  have hemzseg : Emitted L ((p + 8) + 4 * (fd.params.toList.zipIdx.flatMap fun pi =>
        storeSlotI pi.1 (A pi.2)).length)
      (((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).map
        (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r)))) := by
    have h := Emitted_append_right L p
      ([Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))), Instr.sd SP RA 0]
        ++ (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)))
      _ (Emitted_append_left _ _ _ _ hem)
    rw [show p + 4 * ([Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))), Instr.sd SP RA 0]
          ++ (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2))).length
        = (p + 8) + 4 * (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
        from by simp only [List.length_append, List.length_cons, List.length_nil]; omega] at h
    exact h
  have hzbounds : ∀ r ∈ ((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)),
      1 ≤ r ∧ r ≤ maxRegF fd := by
    intro r hr
    rw [List.mem_filter, List.mem_range] at hr
    have h := hr.2
    simp only [Bool.and_eq_true, bne_iff_ne] at h
    exact ⟨Nat.pos_of_ne_zero h.1.1, Nat.le_of_lt_succ hr.1⟩
  obtain ⟨kZ, hZsp, hZpc, hZreg, hZinst, hZmem, hZzero, hZpres, hZra⟩ :=
    run_zeroSlots L fd callee.sp huser hnwc hseg hblob hbdc _ _ (stepN kP (step (step m)))
      hPsp hPpc hemzseg hPinst hzbounds
  -- membership characterization for the filtered zero-init set
  have hz_iff : ∀ r : Nat, r ∈ (List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)
      ↔ (r ≤ maxRegF fd ∧ r ≠ 0 ∧ r ∉ fd.params.toList ∧ r ≠ fd.frameReg) := by
    intro r
    rw [List.mem_filter, List.mem_range]
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem,
               decide_eq_false_iff_not]
    constructor
    · rintro ⟨h1, ⟨⟨h2, h3⟩, h4⟩⟩; exact ⟨by omega, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, ⟨⟨h2, h3⟩, h4⟩⟩
  -- ==== G3: frameReg slot (or nothing) ====
  obtain ⟨kF, hFsp, hFpc, hFinst, hFmem, hFslot, hFra⟩ :
      ∃ kF, (stepN kF (stepN kZ (stepN kP (step (step m))))).rget SP = callee.sp
          ∧ (stepN kF (stepN kZ (stepN kP (step (step m))))).pc
              = L.codeBase + BitVec.ofNat 64 (p + 4 * (prologuePreI fd).length)
          ∧ Installed L (stepN kF (stepN kZ (stepN kP (step (step m)))))
          ∧ (∀ a : Word, ¬ memRange a callee.sp (userOff fd) →
               (stepN kF (stepN kZ (stepN kP (step (step m))))).mem a
                 = (stepN kZ (stepN kP (step (step m)))).mem a)
          ∧ (∀ r, 1 ≤ r → r ≤ maxRegF fd →
               (stepN kF (stepN kZ (stepN kP (step (step m))))).loadWord
                   (callee.sp + BitVec.ofNat 64 (slotOff r))
                 = if r = fd.frameReg then sp0 - BitVec.ofNat 64 fd.frameSize
                   else (stepN kZ (stepN kP (step (step m)))).loadWord
                     (callee.sp + BitVec.ofNat 64 (slotOff r)))
          ∧ (stepN kF (stepN kZ (stepN kP (step (step m))))).loadWord callee.sp
              = (stepN kZ (stepN kP (step (step m)))).loadWord callee.sp := by
    -- prologueSize = 2 + |pseg| + |zseg| + |fseg|
    have hpsz : (prologuePreI fd).length
        = 2 + (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
          + ((List.range (maxRegF fd + 1)).filter
              (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length
          + (if fd.frameReg = 0 then 0 else 2) := by
      by_cases hfr : fd.frameReg = 0
      · simp only [prologuePreI, if_pos hfr, storeSlotI, List.length_append,
                   List.length_cons, List.length_nil, List.length_map]
      · simp only [prologuePreI, if_neg hfr, storeSlotI, List.length_append,
                   List.length_cons, List.length_nil, List.length_map, List.length_singleton]
    by_cases hfr0 : fd.frameReg = 0
    · refine ⟨0, by rw [stepN_zero]; exact hZsp, ?_, by rw [stepN_zero]; exact hZinst,
              fun a _ => by rw [stepN_zero], fun r hr1 hrm => ?_, by rw [stepN_zero]⟩
      · rw [stepN_zero, hZpc]; apply pc_congr
        rw [hpsz, show (if fd.frameReg = 0 then (0 : Nat) else 2) = 0 from if_pos hfr0]
        generalize (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length = X
        generalize ((List.range (maxRegF fd + 1)).filter
          (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length = Y
        omega
      · rw [stepN_zero, if_neg (fun h => by rw [h, hfr0] at hr1; omega)]
    · -- fseg = [addi T0 SP userOff, sd SP T0 (slotOff frameReg)]
      have hfr1 : 1 ≤ fd.frameReg := Nat.pos_of_ne_zero hfr0
      have hZpc' : (stepN kZ (stepN kP (step (step m)))).pc
          = L.codeBase + BitVec.ofNat 64
            ((p + 8) + 4 * (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
              + 4 * ((List.range (maxRegF fd + 1)).filter
                (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length) :=
        hZpc
      have hemfseg : Emitted L
          ((p + 8) + 4 * (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
            + 4 * ((List.range (maxRegF fd + 1)).filter
              (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length)
          ([Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd))]
            ++ storeSlotI fd.frameReg T0) := by
        have h := Emitted_append_right L p _ _ hem
        rw [show p + 4 * (([Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))),
              Instr.sd SP RA 0]
              ++ (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)))
              ++ ((List.range (maxRegF fd + 1)).filter
                  (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).map
                  (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r)))).length
            = (p + 8)
              + 4 * (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
              + 4 * ((List.range (maxRegF fd + 1)).filter
                (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length
            from by simp only [List.length_append, List.length_cons, List.length_nil,
                               List.length_map]; omega] at h
        rw [if_neg hfr0] at h; exact h
      -- addi T0 SP userOff
      have hdG3a : decode (fetch32 (stepN kZ (stepN kP (step (step m)))))
          = Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd)) := by
        have h := decode_at L (stepN kZ (stepN kP (step (step m))))
          (stepN kZ (stepN kP (step (step m)))) _ _ (Emitted_append_left _ _ _ _ hemfseg) hZinst 0
          (by simp) (by rw [hZpc']; apply pc_congr; omega) rfl
        simpa using h
      have hstepG3a : step (stepN kZ (stepN kP (step (step m))))
          = ((stepN kZ (stepN kP (step (step m)))).rset T0
              (callee.sp + BitVec.ofNat 64 (userOff fd))).setPc
            ((stepN kZ (stepN kP (step (step m)))).pc + 4) := by
        rw [step_addi _ T0 SP _ hdG3a, hZsp, signExtend_ofNat_lt (userOff fd) (by omega)]
      -- run the frameReg store from the post-addi state
      have hT0v : (step (stepN kZ (stepN kP (step (step m))))).rget T0
          = callee.sp + BitVec.ofNat 64 (userOff fd) := by
        rw [hstepG3a, rget_setPc, rget_rset_self _ T0 _ (by decide)]
      have hStSp : (step (stepN kZ (stepN kP (step (step m))))).rget SP = callee.sp := by
        rw [hstepG3a, rget_setPc, rget_rset_ne _ T0 SP _ (by decide), hZsp]
      have hStPc : (step (stepN kZ (stepN kP (step (step m))))).pc
          = L.codeBase + BitVec.ofNat 64
            ((p + 8) + 4 * (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
              + 4 * ((List.range (maxRegF fd + 1)).filter
                (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length + 4) := by
        rw [hstepG3a, pc_setPc, hZpc', pc_add4]
      have hStInst : Installed L (step (stepN kZ (stepN kP (step (step m))))) := by
        rw [hstepG3a]; exact Installed_setPc L _ _ (Installed_congr L _ _ (by rw [mem_rset]) hZinst)
      have hStMem : (step (stepN kZ (stepN kP (step (step m))))).mem
          = (stepN kZ (stepN kP (step (step m)))).mem := by rw [hstepG3a, mem_setPc, mem_rset]
      have hemsd : Emitted L
          ((p + 8) + 4 * (fd.params.toList.zipIdx.flatMap fun pi => storeSlotI pi.1 (A pi.2)).length
            + 4 * ((List.range (maxRegF fd + 1)).filter
              (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).length + 4)
          [Instr.sd SP T0 (BitVec.ofNat 12 (slotOff fd.frameReg))] := by
        have h := Emitted_append_right L _ [Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd))] _ hemfseg
        rw [List.length_singleton, Nat.mul_one, storeSlotI, if_neg hfr0] at h; exact h
      obtain ⟨hSDpc, hSDreg, hSDinst, hSDmem, hSDslot, hSDslotne, hSDra⟩ :=
        run_slotStore L fd (step (stepN kZ (stepN kP (step (step m))))) callee.sp
          fd.frameReg T0 _ hfr1 hfrb hStSp hStPc hStInst hemsd huser hnwc hseg hblob hbdc
      have hSN2Z : stepN 2 (stepN kZ (stepN kP (step (step m))))
          = step (step (stepN kZ (stepN kP (step (step m))))) := rfl
      have hmemA : (step (stepN kZ (stepN kP (step (step m))))).mem
          = (stepN kZ (stepN kP (step (step m)))).mem := hStMem
      refine ⟨2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hSN2Z, hSDreg SP]; exact hStSp
      · rw [hSN2Z, hSDpc]; apply pc_congr; rw [hpsz, if_neg hfr0]; omega
      · rw [hSN2Z]; exact hSDinst
      · intro a ha; rw [hSN2Z, hSDmem a ha, hStMem]
      · intro r hr1 hrm
        rw [hSN2Z]
        by_cases hrf : r = fd.frameReg
        · subst hrf; rw [hSDslot, hT0v, hfb, if_pos rfl]
        · rw [hSDslotne r hrf hr1 hrm, if_neg hrf]
          exact loadWord_mem_congr _ _ _ hmemA
      · rw [hSN2Z, hSDra]; exact loadWord_mem_congr _ _ _ hmemA
  -- ==== G4: zero the user frame ====
  have hPS : prologueSize fd = (prologuePreI fd).length + fd.frameSize / 8 := by
    simp only [prologueSize, prologueI, frameZeroI, List.length_append, List.length_map,
               List.length_range]
  have hfsN : 8 * (fd.frameSize / 8) = fd.frameSize := by omega
  obtain ⟨kG, hGsp, hGpc, hGreg, hGinst, hGzero, hGpres, hGload⟩ :=
    run_zeroFrame L fd callee.sp (htf_eq ▸ htf) (by omega) hseg hblob hbdcF
      (fd.frameSize / 8) (p + 4 * (prologuePreI fd).length)
      (stepN kF (stepN kZ (stepN kP (step (step m))))) (by omega) hFsp hFpc hemFZ hFinst
  rw [hfsN] at hGzero hGpres
  -- ==== final: assemble the callee StInv ====
  have hfinalPre : stepN (2 + kP + kZ + kF) m
      = stepN kF (stepN kZ (stepN kP (step (step m)))) := by
    rw [show 2 + kP + kZ + kF = 2 + kP + kZ + kF from rfl, stepN_add, stepN_add, stepN_add, hSN2]
  have hfinal : stepN (2 + kP + kZ + kF + kG) m
      = stepN kG (stepN kF (stepN kZ (stepN kP (step (step m))))) := by
    rw [show 2 + kP + kZ + kF + kG = (2 + kP + kZ + kF) + kG from rfl, stepN_add, hfinalPre]
  have hkeys : (fd.params.toList.zip argVals).map Prod.fst = fd.params.toList :=
    List.map_fst_zip (by omega)
  have hcalleeHole : ∀ a : Word, OffPriv L ((callee.sp, userOff fd) :: holes) callee.sp a →
      ¬ memRange a callee.sp (userOff fd) := by
    intro a ha hmr
    exact ha.1 (Or.inr ⟨(callee.sp, userOff fd), List.mem_cons_self, hmr⟩)
  have hcspN' : (callee.sp + BitVec.ofNat 64 (userOff fd)).toNat = callee.sp.toNat + userOff fd := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show userOff fd < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (by omega)]
  -- the frame window `[callee.sp+userOff, +frameSize)` ⊆ the callee frame `[callee.sp, +totalFrame)`
  have hFrameSub : ∀ a : Word, memRange a (callee.sp + BitVec.ofNat 64 (userOff fd)) fd.frameSize →
      memRange a callee.sp (totalFrame fd) := by
    intro a hc; simp only [memRange] at hc ⊢; rw [hcspN'] at hc; rw [htf_eq]
    refine ⟨?_, ?_⟩ <;> omega
  have hHoleSub : ∀ a : Word, memRange a callee.sp (userOff fd) → memRange a callee.sp (totalFrame fd) := by
    intro a hc; simp only [memRange] at hc ⊢; rw [htf_eq]; refine ⟨?_, ?_⟩ <;> omega
  -- off-hole agreement across the pre-frame segments (G0-G3 write only the hole)
  have hPreMem : ∀ a : Word, ¬ memRange a callee.sp (userOff fd) →
      (stepN kF (stepN kZ (stepN kP (step (step m))))).mem a = m.mem a := by
    intro a ha; rw [hFmem a ha, hZmem a ha, hPmem a ha, hm2mem_off a ha]
  refine ⟨2 + kP + kZ + kF + kG, ?_, ?_, ?_, ?_⟩
  · -- StInv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfinal]; exact hGsp
    · intro r hr1 hrm
      have hslot8 : slotOff r + 8 ≤ userOff fd := slotOff_add8_le_userOff fd r hrm
      rw [hfinal, hGload (callee.sp + BitVec.ofNat 64 (slotOff r))
            (by rw [slotAddr_toNat callee.sp r (by omega)]; omega), hFslot r hr1 hrm]
      by_cases hrf : r = fd.frameReg
      · subst hrf; rw [if_pos rfl, hcrg _ hr1, if_pos rfl]
      · rw [if_neg hrf, hcrg _ hr1, if_neg hrf]
        by_cases hrp : r ∈ fd.params.toList
        · rw [hZpres r hr1 hrm (by rw [hz_iff r]; rintro ⟨_, _, hc, _⟩; exact hc hrp),
              hPslot r hr1 hrm]
          exact parkFold_mem_indep r _ _ _ (by rw [hkeys]; exact hrp)
        · rw [hZzero r (by rw [hz_iff r]; exact ⟨hrm, by omega, hrp, hrf⟩)]
          exact parkFold_not_mem r _ _ (by rw [hkeys]; exact hrp)
    · rw [hfinal]; exact hGinst
    · intro a ha
      rw [hfinal]
      by_cases hfr : memRange a (callee.sp + BitVec.ofNat 64 (userOff fd)) fd.frameSize
      · -- in the user frame: both sides are 0 (IL `zeroRange`, machine G4)
        rw [hcmemZ a hfr]; exact (hGzero a hfr).symm
      · -- off the user frame: G4 preserves, `hmemF` gives entry agreement
        rw [hGpres a hfr, hPreMem a (hcalleeHole a ha)]; exact hmemF a ha hfr
    · rfl
    · exact hcsp8
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh'
      · exact Nat.le_refl _
      · exact Nat.le_trans (by omega) (hholes_ord h hh')
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh'
      · exact hnwc
      · exact hholes_nw h hh'
  · rw [hfinal, hGpc]; apply pc_congr; rw [hPS]; omega
  · rw [hfinal, hGload callee.sp (by omega), hFra, hZra, hPra, hm2mem_ra]
  · intro a ha
    rw [hfinal, hGpres a (fun hc => ha (hFrameSub a hc)),
        hPreMem a (fun hc => ha (hHoleSub a hc))]

/-- **W6 — the callee-exit simulator.** Running `epilogueI fd` from a state
    satisfying the callee's post-body `StInv` (with the saved return address `ra`
    still in slot 0) marshals the return registers into `a0..`, restores `ra` and
    the caller's `sp` (P1: machine `sp` back up by `totalFrame`), and lands the pc
    at `ra`. The epilogue issues NO stores, so memory is untouched throughout. -/
theorem epilogue_sim (L : Layout) (fd : FunDef) (holes : List Hole)
    (mE : State) (s1 : St) (ra : Word) (q : Nat)
    (hinv : StInv L fd holes s1 mE)
    (hpc : mE.pc = L.codeBase + BitVec.ofNat 64 q)
    (hem : Emitted L q (epilogueI fd))
    (hraslot : mE.loadWord s1.sp = ra)
    (hraeven : ra.toNat % 2 = 0)
    (hretb : ∀ x ∈ fd.rets.toList, x ≤ maxRegF fd)
    (hretslot : ∀ x ∈ fd.rets.toList, slotOff x < 2 ^ 11)
    (htf : totalFrame fd < 2 ^ 11) :
    ∃ k, (stepN k mE).pc = ra
       ∧ (stepN k mE).rget SP = s1.sp + BitVec.ofNat 64 (totalFrame fd)
       ∧ (∀ j, (hj : j < fd.rets.toList.length) →
            (stepN k mE).rget (A j) = s1.rget fd.rets.toList[j])
       ∧ (stepN k mE).mem = mE.mem := by
  rw [epilogueI] at hem
  -- G1: marshal return registers → a0..
  obtain ⟨kM, hMinv, hMpc, hMmem, hMval, _hMoth⟩ :=
    run_marshalFrom L fd holes s1 fd.rets.toList 0 q mE hinv hpc
      (Emitted_append_left _ _ _ _ hem) hretb hretslot
  obtain ⟨hMx2, _hMslot, hMInst, _, _, _, _, _⟩ := hMinv
  have hSP_M : (stepN kM mE).rget SP = s1.sp := hMx2
  have hR : (fd.rets.toList.zipIdx.flatMap fun ri => loadSlotI ri.1 (A ri.2)).length
      = fd.rets.toList.length := by rw [length_flatMap_loadSlotI, List.length_zipIdx]
  have hemtail : Emitted L (q + 4 * fd.rets.toList.length)
      [Instr.ld RA SP 0, Instr.addi SP SP (BitVec.ofNat 12 (totalFrame fd)), Instr.jalr 0 RA 0] := by
    have h := Emitted_append_right _ _ _ _ hem; rwa [hR] at h
  -- G2: ld ra sp 0 — restore return address from slot 0
  have hdLd : decode (fetch32 (stepN kM mE)) = Instr.ld RA SP 0 := by
    have h := decode_at L (stepN kM mE) (stepN kM mE) _ _ hemtail hMInst 0
      (by simp) (by rw [hMpc]; apply pc_congr; omega) rfl
    simpa using h
  have hstepLd : step (stepN kM mE)
      = ((stepN kM mE).rset RA ((stepN kM mE).loadWord
          ((stepN kM mE).rget SP + (0 : BitVec 12).signExtend 64))).setPc ((stepN kM mE).pc + 4) :=
    step_ld _ RA SP 0 hdLd
  have hRAval : (step (stepN kM mE)).rget RA = ra := by
    rw [hstepLd, rget_setPc, rget_rset_self _ RA _ (by decide), hSP_M,
        show ((0 : BitVec 12).signExtend 64) = (0 : BitVec 64) from by decide,
        show s1.sp + (0 : BitVec 64) = s1.sp from by simp,
        loadWord_mem_congr _ _ _ hMmem]
    exact hraslot
  have hSPld : (step (stepN kM mE)).rget SP = s1.sp := by
    rw [hstepLd, rget_setPc, rget_rset_ne _ RA SP _ (by decide), hSP_M]
  have hPCld : (step (stepN kM mE)).pc
      = L.codeBase + BitVec.ofNat 64 (q + 4 * fd.rets.toList.length + 4) := by
    rw [hstepLd, pc_setPc, hMpc, pc_add4]
  have hINSTld : Installed L (step (stepN kM mE)) :=
    Installed_congr L (stepN kM mE) _ (by rw [hstepLd, mem_setPc, mem_rset]) hMInst
  -- G3: addi sp sp totalFrame — deallocate the frame
  have hdAddi : decode (fetch32 (step (stepN kM mE)))
      = Instr.addi SP SP (BitVec.ofNat 12 (totalFrame fd)) := by
    have h := decode_at L (step (stepN kM mE)) (step (stepN kM mE)) _ _ hemtail hINSTld 1
      (by simp) (by rw [hPCld]) rfl
    simpa using h
  have hstepAddi : step (step (stepN kM mE))
      = ((step (stepN kM mE)).rset SP ((step (stepN kM mE)).rget SP
          + (BitVec.ofNat 12 (totalFrame fd)).signExtend 64)).setPc ((step (stepN kM mE)).pc + 4) :=
    step_addi _ SP SP _ hdAddi
  have hSPaddi : (step (step (stepN kM mE))).rget SP
      = s1.sp + BitVec.ofNat 64 (totalFrame fd) := by
    rw [hstepAddi, rget_setPc, rget_rset_self _ SP _ (by decide), hSPld,
        signExtend_ofNat_lt (totalFrame fd) (by omega)]
  have hRAaddi : (step (step (stepN kM mE))).rget RA = ra := by
    rw [hstepAddi, rget_setPc, rget_rset_ne _ SP RA _ (by decide)]; exact hRAval
  have hPCaddi : (step (step (stepN kM mE))).pc
      = L.codeBase + BitVec.ofNat 64 (q + 4 * fd.rets.toList.length + 4 + 4) := by
    rw [hstepAddi, pc_setPc, hPCld, pc_add4]
  have hINSTaddi : Installed L (step (step (stepN kM mE))) :=
    Installed_congr L (step (stepN kM mE)) _ (by rw [hstepAddi, mem_setPc, mem_rset]) hINSTld
  -- G4: jalr x0 ra 0 — return
  have hdJalr : decode (fetch32 (step (step (stepN kM mE)))) = Instr.jalr 0 RA 0 := by
    have h := decode_at L (step (step (stepN kM mE))) (step (step (stepN kM mE))) _ _ hemtail
      hINSTaddi 2 (by simp) (by rw [hPCaddi]) rfl
    simpa using h
  have hfin : stepN (kM + 3) mE = step (step (step (stepN kM mE))) := by rw [stepN_add]; rfl
  refine ⟨kM + 3, ?_, ?_, ?_, ?_⟩
  · rw [hfin]; exact jalr_lands _ RA ra hdJalr hRAaddi hraeven
  · rw [hfin, step_jalr _ 0 RA 0 hdJalr, rget_setPc, rget_rset_ne _ 0 SP _ (by decide)]
    exact hSPaddi
  · intro j hj
    rw [hfin, step_jalr _ 0 RA 0 hdJalr, rget_setPc,
        rget_rset_ne _ 0 (A j) _ (by show 10 + j ≠ 0; omega),
        hstepAddi, rget_setPc, rget_rset_ne _ SP (A j) _ (by show 10 + j ≠ 2; omega),
        hstepLd, rget_setPc, rget_rset_ne _ RA (A j) _ (by show 10 + j ≠ 1; omega)]
    simpa using hMval j hj
  · rw [hfin]
    have hjmem : (step (step (step (stepN kM mE)))).mem = (step (step (stepN kM mE))).mem := by
      rw [step_jalr _ 0 RA 0 hdJalr, mem_setPc, mem_rset]
    rw [hjmem, hstepAddi, mem_setPc, mem_rset, hstepLd, mem_setPc, mem_rset, hMmem]

/-- The accumulator only grows under `foldl max`. -/
theorem foldl_max_ge_acc : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], a => Nat.le_refl a
  | x :: xs, a => Nat.le_trans (Nat.le_max_left a x) (foldl_max_ge_acc xs (max a x))

/-- Every element of a list is ≤ its `foldl max` (used to bound `args`/`rets`
    registers by `maxRegS`/`maxRegF`). -/
theorem mem_le_foldl_max (x : Nat) : ∀ (l : List Nat) (a : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, h => absurd h (by simp)
  | y :: ys, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge_acc ys (max a x))
      · exact mem_le_foldl_max x ys (max a y) h

theorem lower_sim_cf
    {P : Program} {dbase : Name → Option Word} {pad : Name → Nat} {stackLo : Word}
    {L : Layout} {fd : FunDef} {holes : List Hole} {epiPos : Nat} {dpos fnPos : Name → Nat}
    (fuel : Nat) (stmt : PStmt) (s s' : St) (oc : Outcome) (m : State)
    (here : Nat) (brkPos contPos : List Nat)
    (hexec : LowIR.Prog.exec P dbase pad stackLo fuel stmt s = some (s', oc))
    (hinv  : StInv L fd holes s m)
    (hpc   : m.pc = L.codeBase + BitVec.ofNat 64 here)
    (hem   : Emitted L here (emitCF P.data dpos fnPos brkPos contPos epiPos here stmt))
    (hreg  : maxRegS stmt ≤ maxRegF fd)
    (hnw   : s.sp.toNat + userOff fd ≤ 2 ^ 64)
    (hbd   : (L.codeBase.toNat + L.blobLen ≤ stackLo.toNat ∧ stackLo.toNat ≤ s.sp.toNat)
               ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat)
    (haccess : MemAccOff L holes P dbase pad stackLo fuel stmt s)
    (hlbl  : LabelsOk brkPos contPos epiPos)
    (hbnd  : here + 4 * csize stmt < 2 ^ 20)
    (hbr   : BranchOk stmt)
    (hframe : userOff fd ≤ 2000)
    (hhere4 : here % 4 = 0)
    (hseg  : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hdat  : ∀ d, -2048 ≤ synthHi (((List.lookup d P.data).map (·.length)).getD 0)
                ∧ synthHi (((List.lookup d P.data).map (·.length)).getD 0) ≤ 2047)
    (hdbase : ∀ d a, dbase d = some a → a = L.codeBase + BitVec.ofNat 64 (dpos d))
    (hdpos : ∀ d, dpos d < 2 ^ 20)
    -- C4 (the call case's flat compile-time obligations; Phase-2 discharges them
    -- alongside hdat/hdbase/hdpos):
    (hpad  : ∀ g gd, List.lookup g P.env = some gd → pad g = userOff gd)
    (halign : L.codeBase.toNat % 4 = 0)
    (hfn   : ∀ g gd, List.lookup g P.env = some gd →
        Emitted L (fnPos g)
            (prologueI gd
              ++ emitCF P.data dpos fnPos [] []
                   (fnPos g + 4 * prologueSize gd + 4 * csize gd.body)
                   (fnPos g + 4 * prologueSize gd) gd.body
              ++ epilogueI gd)
          ∧ fnPos g + 4 * prologueSize gd + 4 * csize gd.body + 4 * epilogueSize gd < 2 ^ 20
          ∧ BranchOk gd.body
          ∧ totalFrame gd ≤ 2000
          ∧ gd.frameSize % 8 = 0) :
    ∃ k, StInv L fd holes s' (stepN k m)
       ∧ (stepN k m).pc = L.codeBase
           + BitVec.ofNat 64 (landPos brkPos contPos epiPos (here + 4 * csize stmt) oc)
       ∧ FramesPres holes s.sp fd m (stepN k m) := by
  induction fuel generalizing fd holes epiPos stmt s s' oc m here brkPos contPos with
  | zero => exact absurd hexec (by simp [LowIR.Prog.exec])
  | succ fuel ih =>
    -- the old concrete `hbd` form the leaf/store atoms still expect: both stackLo
    -- disjuncts collapse (codeBase+blob ≤ stackLo ≤ sp), disjunct-2 is identical.
    have hbd_old : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
        ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat := by
      rcases hbd with ⟨h1, h2⟩ | h
      · exact Or.inl (Nat.le_trans h1 h2)
      · exact Or.inr h
    cases stmt
    case skip =>
      rw [LowIR.Prog.exec_skip, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      exact ⟨0, hinv, by simp only [stepN_zero, csize, emit, List.length_nil, Nat.mul_zero,
                                    Nat.add_zero, landPos]; exact hpc,
             FramesPres_of_mem_eq holes s.sp fd m (stepN 0 m) (by rw [stepN_zero])⟩
    case annot a =>
      rw [LowIR.Prog.exec_annot, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      exact ⟨0, hinv, by simp only [stepN_zero, csize, emit, List.length_nil, Nat.mul_zero,
                                    Nat.add_zero, landPos]; exact hpc,
             FramesPres_of_mem_eq holes s.sp fd m (stepN 0 m) (by rw [stepN_zero])⟩
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
      have hem' : Emitted L here (emitCF P.data dpos fnPos ((here + 4 * csize body) :: brkPos) contPos epiPos here body)
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
          obtain ⟨k, hst, hpck, hfr⟩ :=
            ih body s s'' ocb m here ((here + 4 * csize body) :: brkPos) contPos
              hb hinv hpc hem' hreg' hnw hbd hacc' hlbl' hbnd' hbr' hframe (by omega)
          cases ocb with
          | normal =>
              rw [LowIR.Prog.exec_block_normal P dbase pad stackLo fuel body s s'' hb,
                  Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl⟩ := hexec
              exact ⟨k, hst, by rw [hpck]; simp only [csize, landPos], hfr⟩
          | brk kk =>
              cases kk with
              | zero =>
                  rw [LowIR.Prog.exec_block_catch P dbase pad stackLo fuel body s s'' hb,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨k, hst, by rw [hpck]; simp only [csize, landPos, List.getD_cons_zero], hfr⟩
              | succ kk' =>
                  rw [LowIR.Prog.exec_block_brkS P dbase pad stackLo fuel body s s'' kk' hb,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨k, hst, by rw [hpck]; simp only [landPos, List.getD_cons_succ], hfr⟩
          | cont kk =>
              rw [LowIR.Prog.exec_block_cont P dbase pad stackLo fuel body s s'' kk hb,
                  Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl⟩ := hexec
              exact ⟨k, hst, by rw [hpck]; simp only [landPos], hfr⟩
          | ret =>
              rw [LowIR.Prog.exec_block_ret P dbase pad stackLo fuel body s s'' hb,
                  Option.some.injEq, Prod.mk.injEq] at hexec
              obtain ⟨rfl, rfl⟩ := hexec
              exact ⟨k, hst, by rw [hpck]; simp only [landPos], hfr⟩
    case ret =>
      rw [LowIR.Prog.exec_ret, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      have he : here < 2 ^ 20 := by simp only [csize] at hbnd; omega
      have hep : epiPos < 2 ^ 20 := hlbl.2.2
      simp only [emitCF] at hem
      obtain ⟨hst, hpcr, hfrj⟩ :=
        jump_sim L fd holes s m here epiPos _ hinv hpc hem rfl (by omega) (by omega)
      exact ⟨1, hst, by rw [show stepN 1 m = step m from rfl, hpcr]; simp only [csize, landPos], hfrj⟩
    case brkB k =>
      rw [LowIR.Prog.exec_brkB, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      have he : here < 2 ^ 20 := by simp only [csize] at hbnd; omega
      have htgt : brkPos.getD k 0 < 2 ^ 20 := getD_lt brkPos k _ (by omega) hlbl.1
      simp only [emitCF] at hem
      obtain ⟨hst, hpcr, hfrj⟩ :=
        jump_sim L fd holes s m here (brkPos.getD k 0) _ hinv hpc hem rfl (by omega) (by omega)
      exact ⟨1, hst, by rw [show stepN 1 m = step m from rfl, hpcr]; simp only [csize, landPos], hfrj⟩
    case contL k =>
      rw [LowIR.Prog.exec_contL, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      have he : here < 2 ^ 20 := by simp only [csize] at hbnd; omega
      have htgt : contPos.getD k 0 < 2 ^ 20 := getD_lt contPos k _ (by omega) hlbl.2.1
      simp only [emitCF] at hem
      obtain ⟨hst, hpcr, hfrj⟩ :=
        jump_sim L fd holes s m here (contPos.getD k 0) _ hinv hpc hem rfl (by omega) (by omega)
      exact ⟨1, hst, by rw [show stepN 1 m = step m from rfl, hpcr]; simp only [csize, landPos], hfrj⟩
    case seq a b =>
      simp only [maxRegS] at hreg
      obtain ⟨haccA, haccB⟩ := haccess
      obtain ⟨hbrA, hbrB⟩ := hbr
      have hemA : Emitted L here (emitCF P.data dpos fnPos brkPos contPos epiPos here a) :=
        Emitted_append_left L here _ _ hem
      have hemB : Emitted L (here + 4 * csize a)
          (emitCF P.data dpos fnPos brkPos contPos epiPos (here + 4 * csize a) b) := by
        have h := Emitted_append_right L here (emitCF P.data dpos fnPos brkPos contPos epiPos here a)
                    (emitCF P.data dpos fnPos brkPos contPos epiPos (here + 4 * csize a) b) hem
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
            obtain ⟨k1, hinvA, hpcA, hfrA⟩ :=
              ih a s s1 .normal m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA hframe (by omega)
            have hsp : s1.sp = s.sp := StInv_sp_eq L fd holes s s1 m (stepN k1 m) hinv hinvA
            obtain ⟨k2, hinvB, hpcB, hfrB⟩ :=
              ih b s1 s' oc (stepN k1 m) (here + 4 * csize a) brkPos contPos hexec hinvA
                (by rw [hpcA]; simp only [landPos]) hemB hregB (by rw [hsp]; exact hnw)
                (by rw [hsp]; exact hbd) (haccB s1 hea) hlbl hbndB hbrB hframe (by omega)
            refine ⟨k1 + k2, by rw [stepN_add]; exact hinvB, ?_, ?_⟩
            · have hft : (here + 4 * csize a) + 4 * csize b
                  = here + 4 * csize (LowIR.Prog.Stmt.seq a b) := by simp only [csize]; omega
              rw [stepN_add, hpcB, hft]
            · rw [hsp] at hfrB
              rw [stepN_add]
              exact FramesPres_trans holes s.sp fd m (stepN k1 m) (stepN k2 (stepN k1 m)) hfrA hfrB
        | brk k =>
            rw [LowIR.Prog.exec_seq_brk (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA, hfrA⟩ :=
              ih a s s1 (.brk k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA hframe (by omega)
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos], hfrA⟩
        | cont k =>
            rw [LowIR.Prog.exec_seq_cont (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA, hfrA⟩ :=
              ih a s s1 (.cont k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA hframe (by omega)
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos], hfrA⟩
        | ret =>
            rw [LowIR.Prog.exec_seq_ret (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA, hfrA⟩ :=
              ih a s s1 .ret m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA hframe (by omega)
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos], hfrA⟩
    case addi rd rs imm =>
      rw [LowIR.Prog.exec_addi, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.addi rd rs imm) s _ m here
          (LowIR.Prog.exec_addi P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case add rd r1 r2 =>
      rw [LowIR.Prog.exec_add, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.add rd r1 r2) s _ m here
          (LowIR.Prog.exec_add P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case sub rd r1 r2 =>
      rw [LowIR.Prog.exec_sub, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.sub rd r1 r2) s _ m here
          (LowIR.Prog.exec_sub P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case orr rd r1 r2 =>
      rw [LowIR.Prog.exec_orr, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.orr rd r1 r2) s _ m here
          (LowIR.Prog.exec_orr P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case slli rd rs sh =>
      rw [LowIR.Prog.exec_slli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.slli rd rs sh) s _ m here
          (LowIR.Prog.exec_slli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case srli rd rs sh =>
      rw [LowIR.Prog.exec_srli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.srli rd rs sh) s _ m here
          (LowIR.Prog.exec_srli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case lbu rd rs imm =>
      rw [LowIR.Prog.exec_lbu, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.lbu rd rs imm) s _ m here
          (LowIR.Prog.exec_lbu P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case ld rd rs imm =>
      rw [LowIR.Prog.exec_ld, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.ld rd rs imm) s _ m here
          (LowIR.Prog.exec_ld P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case sb rb rv imm =>
      rw [LowIR.Prog.exec_sb, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.sb rb rv imm) s _ m here
          (LowIR.Prog.exec_sb P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case sd rb rv imm =>
      rw [LowIR.Prog.exec_sd, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.sd rb rv imm) s _ m here
          (LowIR.Prog.exec_sd P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd_old haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
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
          ++ emitCF P.data dpos fnPos brkPos contPos epiPos (here + 12) e
          ++ [jal0 (4 + 4 * csize t)]
          ++ emitCF P.data dpos fnPos brkPos contPos epiPos (here + 16 + 4 * csize e) t) := hem
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
              (emitCF P.data dpos fnPos brkPos contPos epiPos (here + 16 + 4 * csize e) t) := by
            have h := Emitted_append_right _ _ _ _ hemU
            rw [show (loadSlotI a T0 ++ loadSlotI b T1 ++ [condInstr c T0 T1 (8 + 4 * csize e)]
                  ++ emitCF P.data dpos fnPos brkPos contPos epiPos (here + 12) e ++ [jal0 (4 + 4 * csize t)]).length
                  = 4 + csize e from by
                  simp only [List.length_append, loadSlotI_length, List.length_cons,
                             List.length_nil, emitCF_length]; omega] at h
            rwa [show here + 4 * (4 + csize e) = here + 16 + 4 * csize e from by omega] at h
          have hmem3 : (step (step (step m))).mem = m.mem := by rw [hs3, mem_setPc]; exact h2mm
          obtain ⟨kt, hinvT, hpcT, hfrT⟩ :=
            ih t s s' oc (step (step (step m))) (here + 16 + 4 * csize e) brkPos contPos hexec hinv3
              hpc3 hemT hregT hnw hbd haccT hlbl (by simp only [csize] at hbnd; omega) hbrT hframe (by omega)
          refine ⟨3 + kt, by rw [hsN kt]; exact hinvT, ?_, ?_⟩
          · rw [hsN kt, hpcT,
                show here + 16 + 4 * csize e + 4 * csize t
                  = here + 4 * csize (LowIR.Prog.Stmt.ife c a b t e) from by simp only [csize]; omega]
          · rw [hsN kt]
            exact FramesPres_trans holes s.sp fd m (step (step (step m)))
              (stepN kt (step (step (step m)))) (FramesPres_of_mem_eq _ _ _ _ _ hmem3) hfrT
      | false =>
          rw [LowIR.Prog.exec_ife_else (h := hev)] at hexec
          have hs3 : step (step (step m)) = (step (step m)).setPc ((step (step m)).pc + 4) :=
            cond_not_taken (step (step m)) c _ (s.rget a) (s.rget b) hdBr h2T0 h2T1 hev
          have hinv3 : StInv L fd holes s (step (step (step m))) := by
            rw [hs3]; exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hinv2
          have hpc3 : (step (step (step m))).pc = L.codeBase + BitVec.ofNat 64 (here + 12) := by
            rw [hs3, pc_setPc, h2pc, pc_add4]
          have hmem3 : (step (step (step m))).mem = m.mem := by rw [hs3, mem_setPc]; exact h2mm
          have hemE : Emitted L (here + 12) (emitCF P.data dpos fnPos brkPos contPos epiPos (here + 12) e) := by
            have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _
              (Emitted_append_left _ _ _ _ hemU))
            rw [show (loadSlotI a T0 ++ loadSlotI b T1
                  ++ [condInstr c T0 T1 (8 + 4 * csize e)]).length = 3 from by
                  simp only [List.length_append, loadSlotI_length, List.length_cons,
                             List.length_nil]] at h
            rwa [show here + 4 * 3 = here + 12 from by omega] at h
          obtain ⟨ke, hinvE, hpcE, hfrE⟩ :=
            ih e s s' oc (step (step (step m))) (here + 12) brkPos contPos hexec hinv3 hpc3 hemE
              hregE hnw hbd haccE hlbl (by simp only [csize] at hbnd; omega) hbrE hframe (by omega)
          have hframesE : FramesPres holes s.sp fd m (stepN ke (step (step (step m)))) :=
            FramesPres_trans holes s.sp fd m (step (step (step m))) (stepN ke (step (step (step m))))
              (FramesPres_of_mem_eq _ _ _ _ _ hmem3) hfrE
          cases oc with
          | normal =>
              have hemJ : Emitted L (here + 12 + 4 * csize e) [jal0 (4 + 4 * csize t)] := by
                have h := Emitted_append_right _ _ _ _ (Emitted_append_left _ _ _ _ hemU)
                rw [show (loadSlotI a T0 ++ loadSlotI b T1 ++ [condInstr c T0 T1 (8 + 4 * csize e)]
                      ++ emitCF P.data dpos fnPos brkPos contPos epiPos (here + 12) e).length = 3 + csize e from by
                      simp only [List.length_append, loadSlotI_length, List.length_cons,
                                 List.length_nil, emitCF_length]] at h
                rwa [show here + 4 * (3 + csize e) = here + 12 + 4 * csize e from by omega] at h
              have hpcE' : (stepN ke (step (step (step m)))).pc
                  = L.codeBase + BitVec.ofNat 64 (here + 12 + 4 * csize e) := by
                rw [hpcE]; simp only [landPos]
              have hspE : s'.sp = s.sp :=
                StInv_sp_eq L fd holes s s' (step (step (step m))) (stepN ke (step (step (step m))))
                  hinv3 hinvE
              obtain ⟨hstJ, hpcJ, hfrJ⟩ :=
                jump_sim L fd holes s' (stepN ke (step (step (step m)))) (here + 12 + 4 * csize e)
                  (here + 16 + 4 * csize e + 4 * csize t) _ hinvE hpcE' hemJ (by push_cast; omega)
                  (by omega) (by omega)
              rw [hspE] at hfrJ
              refine ⟨3 + ke + 1, ?_, ?_, ?_⟩
              · rw [show stepN (3 + ke + 1) m = step (stepN (3 + ke) m) from by rw [stepN_add]; rfl,
                    hsN ke]
                exact hstJ
              · rw [show stepN (3 + ke + 1) m = step (stepN (3 + ke) m) from by rw [stepN_add]; rfl,
                    hsN ke, hpcJ]
                simp only [landPos]
                exact pc_congr _ (by simp only [csize]; omega)
              · rw [show stepN (3 + ke + 1) m = step (stepN (3 + ke) m) from by rw [stepN_add]; rfl,
                    hsN ke]
                exact FramesPres_trans holes s.sp fd m (stepN ke (step (step (step m))))
                  (step (stepN ke (step (step (step m))))) hframesE hfrJ
          | brk k =>
              refine ⟨3 + ke, by rw [hsN ke]; exact hinvE, ?_, by rw [hsN ke]; exact hframesE⟩
              rw [hsN ke, hpcE]; simp only [landPos]
          | cont k =>
              refine ⟨3 + ke, by rw [hsN ke]; exact hinvE, ?_, by rw [hsN ke]; exact hframesE⟩
              rw [hsN ke, hpcE]; simp only [landPos]
          | ret =>
              refine ⟨3 + ke, by rw [hsN ke]; exact hinvE, ?_, by rw [hsN ke]; exact hframesE⟩
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
      -- the whole emitCF P.data dpos fnPos stream, unfolded.
      have hemU : Emitted L here (loadSlotI a T0 ++ loadSlotI b T1
          ++ [condInstr c T0 T1 8, jal0 (8 + 4 * csize body)]
          ++ emitCF P.data dpos fnPos brkPos (here :: contPos) epiPos (here + 16) body
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
          (emitCF P.data dpos fnPos brkPos (here :: contPos) epiPos (here + 16) body) := by
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
              ++ emitCF P.data dpos fnPos brkPos (here :: contPos) epiPos (here + 16) body).length
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
          have hmem3 : (step (step (step m))).mem = m.mem := by rw [hs3, mem_setPc]; exact h2mm
          have hemJmp : Emitted L (here + 12) [jal0 (8 + 4 * csize body)] :=
            Emitted_append_right L (here + 8) [condInstr c T0 T1 8]
              [jal0 (8 + 4 * csize body)] hemCJ
          obtain ⟨hstJmp, hpcJmp, hfrJmp⟩ :=
            jump_sim L fd holes s (step (step (step m))) (here + 12) (here + 20 + 4 * csize body) _
              hinv3 hpc3 hemJmp (by push_cast; omega) (by omega) (by omega)
          have h4 : stepN 4 m = step (step (step (step m))) := rfl
          refine ⟨4, ?_, ?_, ?_⟩
          · rw [h4]; exact hstJmp
          · rw [h4, hpcJmp]; simp only [landPos]; exact pc_congr _ (by simp only [csize]; omega)
          · rw [h4]
            exact FramesPres_trans holes s.sp fd m (step (step (step m)))
              (step (step (step (step m)))) (FramesPres_of_mem_eq _ _ _ _ _ hmem3) hfrJmp
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
          have hmem3 : (step (step (step m))).mem = m.mem := by rw [hs3, mem_setPc]; exact h2mm
          cases hbody : LowIR.Prog.exec P dbase pad stackLo fuel body s with
          | none =>
              rw [LowIR.Prog.exec_while_none P dbase pad stackLo fuel c a b body s hev hbody] at hexec
              simp at hexec
          | some pr =>
              obtain ⟨sb, ocb⟩ := pr
              obtain ⟨kb, hinvB, hpcB, hfrB⟩ :=
                ih body s sb ocb (step (step (step m))) (here + 16) brkPos (here :: contPos)
                  hbody hinv3 hpc3 hemBody hregBody hnw hbd haccBody hlbl' hbndBody hbrBody hframe (by omega)
              have hsp : sb.sp = s.sp :=
                StInv_sp_eq L fd holes s sb m (stepN kb (step (step (step m)))) hinv hinvB
              -- prefix (3 steps) + body preserve the frame → up to `stepN kb (step^3 m)`.
              have hframesBody : FramesPres holes s.sp fd m (stepN kb (step (step (step m)))) :=
                FramesPres_trans holes s.sp fd m (step (step (step m)))
                  (stepN kb (step (step (step m)))) (FramesPres_of_mem_eq _ _ _ _ _ hmem3) hfrB
              cases ocb with
              | normal =>
                  rw [LowIR.Prog.exec_while_normal P dbase pad stackLo fuel c a b body s sb hev hbody]
                    at hexec
                  have hpcB' : (stepN kb (step (step (step m)))).pc
                      = L.codeBase + BitVec.ofNat 64 (here + 16 + 4 * csize body) := by
                    rw [hpcB]; simp only [landPos]
                  obtain ⟨hstBack, hpcBack, hfrBack⟩ :=
                    jump_sim L fd holes sb (stepN kb (step (step (step m))))
                      (here + 16 + 4 * csize body) here _ hinvB hpcB' hemBack
                      (by push_cast; omega) (by omega) (by omega)
                  rw [hsp] at hfrBack
                  obtain ⟨kw, hinvW, hpcW, hfrW⟩ :=
                    ih (.while c a b body) sb s' oc (step (stepN kb (step (step (step m)))))
                      here brkPos contPos hexec hstBack hpcBack hem hreg
                      (by rw [hsp]; exact hnw) (by rw [hsp]; exact hbd)
                      (haccRec sb (Or.inl hbody)) hlbl hbnd hbr hframe (by omega)
                  rw [hsp] at hfrW
                  refine ⟨3 + kb + 1 + kw, ?_, ?_, ?_⟩
                  · rw [stepN_add (3 + kb + 1) kw, stepN_add (3 + kb) 1, hsN kb]; exact hinvW
                  · rw [stepN_add (3 + kb + 1) kw, stepN_add (3 + kb) 1, hsN kb]; exact hpcW
                  · rw [stepN_add (3 + kb + 1) kw, stepN_add (3 + kb) 1, hsN kb]
                    exact FramesPres_trans holes s.sp fd m (stepN kb (step (step (step m))))
                      (stepN kw (step (stepN kb (step (step (step m))))))
                      hframesBody
                      (FramesPres_trans holes s.sp fd (stepN kb (step (step (step m))))
                        (step (stepN kb (step (step (step m)))))
                        (stepN kw (step (stepN kb (step (step (step m)))))) hfrBack hfrW)
              | brk k =>
                  rw [LowIR.Prog.exec_while_brk P dbase pad stackLo fuel c a b body s sb k hev hbody,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨3 + kb, by rw [hsN kb]; exact hinvB, ?_, by rw [hsN kb]; exact hframesBody⟩
                  rw [hsN kb, hpcB]; simp only [landPos]
              | cont k =>
                  cases k with
                  | zero =>
                      rw [LowIR.Prog.exec_while_cont0 P dbase pad stackLo fuel c a b body s sb hev
                          hbody] at hexec
                      have hpcB' : (stepN kb (step (step (step m)))).pc
                          = L.codeBase + BitVec.ofNat 64 here := by
                        rw [hpcB]; simp only [landPos, List.getD_cons_zero]
                      obtain ⟨kw, hinvW, hpcW, hfrW⟩ :=
                        ih (.while c a b body) sb s' oc (stepN kb (step (step (step m))))
                          here brkPos contPos hexec hinvB hpcB' hem hreg
                          (by rw [hsp]; exact hnw) (by rw [hsp]; exact hbd)
                          (haccRec sb (Or.inr hbody)) hlbl hbnd hbr hframe (by omega)
                      rw [hsp] at hfrW
                      refine ⟨3 + kb + kw, ?_, ?_, ?_⟩
                      · rw [stepN_add (3 + kb) kw, hsN kb]; exact hinvW
                      · rw [stepN_add (3 + kb) kw, hsN kb]; exact hpcW
                      · rw [stepN_add (3 + kb) kw, hsN kb]
                        exact FramesPres_trans holes s.sp fd m (stepN kb (step (step (step m))))
                          (stepN kw (stepN kb (step (step (step m))))) hframesBody hfrW
                  | succ k' =>
                      rw [LowIR.Prog.exec_while_contS P dbase pad stackLo fuel c a b body s sb k' hev
                          hbody, Option.some.injEq, Prod.mk.injEq] at hexec
                      obtain ⟨rfl, rfl⟩ := hexec
                      refine ⟨3 + kb, by rw [hsN kb]; exact hinvB, ?_,
                              by rw [hsN kb]; exact hframesBody⟩
                      rw [hsN kb, hpcB]; simp only [landPos, List.getD_cons_succ]
              | ret =>
                  rw [LowIR.Prog.exec_while_ret P dbase pad stackLo fuel c a b body s sb hev hbody,
                      Option.some.injEq, Prod.mk.injEq] at hexec
                  obtain ⟨rfl, rfl⟩ := hexec
                  refine ⟨3 + kb, by rw [hsN kb]; exact hinvB, ?_, by rw [hsN kb]; exact hframesBody⟩
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
          obtain ⟨hinvS, hT0S, hpcS, hmemS, -⟩ :=
            run_synth L fd holes s m T0 (by decide) (by decide) (bs.length : Int) here
              hinv hpc hemS hrange
          obtain ⟨ks, hinvF, hpcF, hfrStore⟩ :=
            run_store L fd holes s (stepN 3 m) rd (BitVec.ofInt 64 (bs.length : Int)) (here + 12)
              hinvS hT0S hpcS hemST hrd hfrd hnw hseg hblob hbd_old
          have hval : s.rset rd (BitVec.ofInt 64 (bs.length : Int))
              = s.rset rd (BitVec.ofNat 64 bs.length) := by rw [BitVec.ofInt_natCast]
          refine ⟨3 + ks, ?_, ?_, ?_⟩
          · rw [stepN_add 3 ks m]; rw [hval] at hinvF; exact hinvF
          · rw [stepN_add 3 ks m, hpcF]
            apply pc_congr
            simp only [landPos, csize, storeSlotI_length]
            by_cases hrd0 : rd = 0 <;> simp only [hrd0, if_true, if_false] <;> omega
          · rw [stepN_add 3 ks m]
            exact FramesPres_trans holes s.sp fd m (stepN 3 m) (stepN ks (stepN 3 m))
              (FramesPres_of_mem_eq _ _ _ _ _ hmemS) hfrStore
    case cref rd d =>
      -- pc-read + delta-synth + add (`run_cref`) loads the data address into T0,
      -- then park it into rd's slot (`run_store`). `hdbase` links the IL `dbase`
      -- to the machine layout; `hdpos`/`here < 2²⁰` give the delta synth range.
      have hrd : rd ≤ maxRegF fd := hreg
      have hfrd : slotOff rd < 2 ^ 11 := by
        have := slotOff_add8_le_userOff fd rd hrd; omega
      have hhere : here < 2 ^ 20 := by
        have : here + 4 * csize (.cref rd d) < 2 ^ 20 := hbnd; omega
      cases hdb : dbase d with
      | none =>
          rw [LowIR.Prog.exec_cref_none P dbase pad stackLo fuel rd d s hdb] at hexec
          exact absurd hexec (by simp)
      | some a =>
          rw [LowIR.Prog.exec_cref P dbase pad stackLo fuel rd d s hdb, Option.some.injEq,
              Prod.mk.injEq] at hexec
          obtain ⟨rfl, rfl⟩ := hexec
          have ha : a = L.codeBase + BitVec.ofNat 64 (dpos d) := hdbase d a hdb
          simp only [emitCF] at hem
          have hemC : Emitted L here (crefI T0 T1 ((dpos d : Int) - ((here : Int) + 4))) :=
            Emitted_append_left L here _ (storeSlotI rd T0) hem
          have hemST : Emitted L (here + 20) (storeSlotI rd T0) := by
            have h := Emitted_append_right L here
              (crefI T0 T1 ((dpos d : Int) - ((here : Int) + 4))) (storeSlotI rd T0) hem
            rwa [crefI_length] at h
          obtain ⟨hinvC, hT0C, hpcC, hmemC⟩ :=
            run_cref L fd holes s m (dpos d) here hinv hpc hemC hhere (hdpos d)
          obtain ⟨ks, hinvF, hpcF, hfrStore⟩ :=
            run_store L fd holes s (stepN 5 m) rd (L.codeBase + BitVec.ofNat 64 (dpos d))
              (here + 20) hinvC hT0C hpcC hemST hrd hfrd hnw hseg hblob hbd_old
          refine ⟨5 + ks, ?_, ?_, ?_⟩
          · rw [stepN_add 5 ks m]; rw [← ha] at hinvF; exact hinvF
          · rw [stepN_add 5 ks m, hpcF]
            apply pc_congr
            simp only [landPos, csize, storeSlotI_length]
            by_cases hrd0 : rd = 0 <;> simp only [hrd0, if_true, if_false] <;> omega
          · rw [stepN_add 5 ks m]
            exact FramesPres_trans holes s.sp fd m (stepN 5 m) (stepN ks (stepN 5 m))
              (FramesPres_of_mem_eq _ _ _ _ _ hmemC) hfrStore
    case call argc rvc f args rets =>
      -- ==== destructure the successful call ====
      obtain ⟨gd, callee, s1, ocb, hlk, harity, hfe, hbody, hocb, hs', hoc⟩ :=
        LowIR.Prog.exec_call_inv P dbase pad stackLo fuel argc rvc f args rets s s' oc hexec
      subst hoc
      simp only [Bool.and_eq_true, beq_iff_eq] at harity
      obtain ⟨hgargc, hgrvc⟩ := harity
      obtain ⟨hfnEm, hfnBnd, hfnBr, hfnTF, hfnFS8⟩ := hfn f gd hlk
      have hpadf : pad f = userOff gd := hpad f gd hlk
      -- caller register/slot bounds from `maxRegS`
      simp only [maxRegS] at hreg
      have hargB : ∀ a ∈ args.toList, a ≤ maxRegF fd := fun a ha =>
        Nat.le_trans (mem_le_foldl_max a args.toList 0 ha) (Nat.le_trans (Nat.le_max_left _ _) hreg)
      have hretB : ∀ a ∈ rets.toList, a ≤ maxRegF fd := fun a ha =>
        Nat.le_trans (mem_le_foldl_max a rets.toList 0 ha) (Nat.le_trans (Nat.le_max_right _ _) hreg)
      have hargSlot : ∀ a ∈ args.toList, slotOff a < 2 ^ 11 := fun a ha => by
        have := slotOff_add8_le_userOff fd a (hargB a ha); omega
      simp only [emitCF] at hem
      -- ==== segment 1: marshal caller args into a0.. ====
      obtain ⟨kMar, hMarInv, hMarPc, hMarMem, hMarVal, hMarOth⟩ :=
        run_marshalFrom L fd holes s args.toList 0 here m hinv hpc
          (Emitted_append_left _ _ _ _ (Emitted_append_left _ _ _ _ hem)) hargB hargSlot
      have hAL : args.toList.length = argc := by simp
      have hbndArgc : here + 4 * argc < 2 ^ 20 := by
        have h := hbnd; simp only [csize] at h; omega
      -- ==== segment 2: `jal RA` to the callee entry ====
      have hemJal : Emitted L (here + 4 * argc)
          [Instr.jal RA (BitVec.ofInt 21 ((fnPos f : Int) - ((here : Int) + 4 * argc)))] := by
        have h := Emitted_append_right L here (marshalI args.toList)
          [Instr.jal RA (BitVec.ofInt 21 ((fnPos f : Int) - ((here : Int) + 4 * argc)))]
          (Emitted_append_left _ _ _ _ hem)
        rwa [marshalI_length, hAL] at h
      have hdJal : decode (fetch32 (stepN kMar m))
          = Instr.jal RA (BitVec.ofInt 21 ((fnPos f : Int) - ((here : Int) + 4 * argc))) := by
        have h := decode_at L (stepN kMar m) (stepN kMar m) _ _ hemJal hMarInv.2.2.1 0
          (by simp) (by rw [hMarPc, hAL]; apply pc_congr; omega) rfl
        simpa using h
      have hδlo : -(2 ^ 20 : Int) ≤ (fnPos f : Int) - ((here : Int) + 4 * argc) := by omega
      have hδhi : ((fnPos f : Int) - ((here : Int) + 4 * argc)) < 2 ^ 20 := by omega
      have hstepJal := step_jal (stepN kMar m) RA _ hdJal
      have hJalInv : StInv L fd holes s (step (stepN kMar m)) := by
        rw [hstepJal]; exact StInv_scratch L fd holes s (stepN kMar m) RA _ _ (by decide) hMarInv
      have hJalPc : (step (stepN kMar m)).pc = L.codeBase + BitVec.ofNat 64 (fnPos f) := by
        rw [hstepJal, pc_setPc, hMarPc, hAL, signExtend_ofInt_21 _ hδlo hδhi,
            show ((fnPos f : Int) - ((here : Int) + 4 * argc))
               = ((fnPos f : Int) - ((here + 4 * argc : Nat) : Int)) from by omega, jump_lands]
      have hJalRA : (step (stepN kMar m)).rget RA
          = L.codeBase + BitVec.ofNat 64 (here + 4 * argc) + 4 := by
        rw [hstepJal, rget_setPc, rget_rset_self _ RA _ (by decide), hMarPc, hAL]
      have hJalMem : (step (stepN kMar m)).mem = m.mem := by
        rw [hstepJal, mem_setPc, mem_rset, hMarMem]
      sorry

end LowIR.ProgSim
