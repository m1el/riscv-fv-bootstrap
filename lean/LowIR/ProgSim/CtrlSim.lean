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

/-- The RESOLVED (label-free) prologue — a direct transcription of
    `Compile.prologue` with `.ins` unwrapped and `storeSlot` → `storeSlotI`
    (`Compile.SP`/`RA`/`A`/`T0` are physical registers, position-independent). -/
def prologueI (fd : FunDef) : List Instr :=
  let params := fd.params.toList
  [Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))), Instr.sd SP RA 0]
  ++ params.zipIdx.flatMap (fun pi => storeSlotI pi.1 (A pi.2))
  ++ ((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !params.contains r && r != fd.frameReg)).map
       (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r)))
  ++ (if fd.frameReg = 0 then [] else
        [Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd))] ++ storeSlotI fd.frameReg T0)

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
                ∧ synthHi (((List.lookup d P.data).map (·.length)).getD 0) ≤ 2047)
    (hdbase : ∀ d a, dbase d = some a → a = L.codeBase + BitVec.ofNat 64 (dpos d))
    (hdpos : ∀ d, dpos d < 2 ^ 20) :
    ∃ k, StInv L fd holes s' (stepN k m)
       ∧ (stepN k m).pc = L.codeBase
           + BitVec.ofNat 64 (landPos brkPos contPos epiPos (here + 4 * csize stmt) oc)
       ∧ FramesPres holes s.sp fd m (stepN k m) := by
  induction fuel generalizing stmt s s' oc m here brkPos contPos with
  | zero => exact absurd hexec (by simp [LowIR.Prog.exec])
  | succ fuel ih =>
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
              hb hinv hpc hem' hreg' hnw hbd hacc' hlbl' hbnd' hbr'
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
                hlbl hbndA hbrA
            have hsp : s1.sp = s.sp := StInv_sp_eq L fd holes s s1 m (stepN k1 m) hinv hinvA
            obtain ⟨k2, hinvB, hpcB, hfrB⟩ :=
              ih b s1 s' oc (stepN k1 m) (here + 4 * csize a) brkPos contPos hexec hinvA
                (by rw [hpcA]; simp only [landPos]) hemB hregB (by rw [hsp]; exact hnw)
                (by rw [hsp]; exact hbd) (haccB s1 hea) hlbl hbndB hbrB
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
                hlbl hbndA hbrA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos], hfrA⟩
        | cont k =>
            rw [LowIR.Prog.exec_seq_cont (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA, hfrA⟩ :=
              ih a s s1 (.cont k) m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos], hfrA⟩
        | ret =>
            rw [LowIR.Prog.exec_seq_ret (h := hea), Option.some.injEq, Prod.mk.injEq] at hexec
            obtain ⟨rfl, rfl⟩ := hexec
            obtain ⟨k1, hinvA, hpcA, hfrA⟩ :=
              ih a s s1 .ret m here brkPos contPos hea hinv hpc hemA hregA hnw hbd haccA
                hlbl hbndA hbrA
            exact ⟨k1, hinvA, by rw [hpcA]; simp only [landPos], hfrA⟩
    case addi rd rs imm =>
      rw [LowIR.Prog.exec_addi, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.addi rd rs imm) s _ m here
          (LowIR.Prog.exec_addi P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case add rd r1 r2 =>
      rw [LowIR.Prog.exec_add, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.add rd r1 r2) s _ m here
          (LowIR.Prog.exec_add P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case sub rd r1 r2 =>
      rw [LowIR.Prog.exec_sub, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.sub rd r1 r2) s _ m here
          (LowIR.Prog.exec_sub P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case orr rd r1 r2 =>
      rw [LowIR.Prog.exec_orr, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.orr rd r1 r2) s _ m here
          (LowIR.Prog.exec_orr P dbase pad stackLo fuel rd r1 r2 s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case slli rd rs sh =>
      rw [LowIR.Prog.exec_slli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.slli rd rs sh) s _ m here
          (LowIR.Prog.exec_slli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case srli rd rs sh =>
      rw [LowIR.Prog.exec_srli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.srli rd rs sh) s _ m here
          (LowIR.Prog.exec_srli P dbase pad stackLo fuel rd rs sh s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case lbu rd rs imm =>
      rw [LowIR.Prog.exec_lbu, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.lbu rd rs imm) s _ m here
          (LowIR.Prog.exec_lbu P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case ld rd rs imm =>
      rw [LowIR.Prog.exec_ld, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.ld rd rs imm) s _ m here
          (LowIR.Prog.exec_ld P dbase pad stackLo fuel rd rs imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case sb rb rv imm =>
      rw [LowIR.Prog.exec_sb, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.sb rb rv imm) s _ m here
          (LowIR.Prog.exec_sb P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
      exact ⟨k, hst, by rw [hpck]; simp only [landPos, csize], hfr⟩
    case sd rb rv imm =>
      rw [LowIR.Prog.exec_sd, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, rfl⟩ := hexec
      obtain ⟨k, hst, hpck, hfr⟩ :=
        lower_sim (fuel + 1) (.sd rb rv imm) s _ m here
          (LowIR.Prog.exec_sd P dbase pad stackLo fuel rb rv imm s) hinv hpc hem hreg hframe hnw
          hseg hblob hbd haccess rfl
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
              hpc3 hemT hregT hnw hbd haccT hlbl (by simp only [csize] at hbnd; omega) hbrT
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
              hregE hnw hbd haccE hlbl (by simp only [csize] at hbnd; omega) hbrE
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
                  hbody hinv3 hpc3 hemBody hregBody hnw hbd haccBody hlbl' hbndBody hbrBody
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
                      (haccRec sb (Or.inl hbody)) hlbl hbnd hbr
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
                          (haccRec sb (Or.inr hbody)) hlbl hbnd hbr
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
              hinvS hT0S hpcS hemST hrd hfrd hnw hseg hblob hbd
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
              (here + 20) hinvC hT0C hpcC hemST hrd hfrd hnw hseg hblob hbd
          refine ⟨5 + ks, ?_, ?_, ?_⟩
          · rw [stepN_add 5 ks m]; rw [← ha] at hinvF; exact hinvF
          · rw [stepN_add 5 ks m, hpcF]
            apply pc_congr
            simp only [landPos, csize, storeSlotI_length]
            by_cases hrd0 : rd = 0 <;> simp only [hrd0, if_true, if_false] <;> omega
          · rw [stepN_add 5 ks m]
            exact FramesPres_trans holes s.sp fd m (stepN 5 m) (stepN ks (stepN 5 m))
              (FramesPres_of_mem_eq _ _ _ _ _ hmemC) hfrStore
    case call argc rvc f args rets => sorry

end LowIR.ProgSim
