/-
  LowIR.ProgSim.StmtSim — `lower_sim`, the statement-level simulation
  (RESUME-PROGSIM §3.2, Phase 4). THE VERTICAL SLICE: this file states the whole
  relation (`emit`/`Emitted`/`lower_sim`) and proves the straight-line cases
  (skip/annot/arith ops/seq); the control-flow and memory cases are `sorry`'d
  (Phases 4.2–4.4). It is the go/no-go for the `StInv`-based relation design — if
  the plain-equality relation is wrong, it is wrong HERE, on a 4-instruction
  slice, cheaply.

  `emit` is the RESOLVED straight-line lowering (mirrors `Compile.lower` for the
  label-free cases, with `loadSlot`/`storeSlot` already resolved to concrete
  `Instr`s — every such `SymInstr` is `.ins`, position-independent). `Emitted L
  pos is` is the STATIC fact that `L.instrs` carries `is` at byte offset `pos`;
  combined with the `Installed` conjunct of `StInv` (preserved across steps), it
  yields the machine fetch. The Phase-2 connection `Emitted L pos (emit stmt)`
  from the real `layout`/`resolveOne` pipeline is deferred (AsmFacts).
-/
import LowIR.ProgSim.SlotFacts

namespace LowIR.ProgSim

open LowIR.Prog (Name FunDef Program dbaseOf)
open LowIR.Compile (userOff slotOff maxRegF maxRegS SP T0 T1)
open Rv64i (Word Byte State Instr fetch32 decode step)

local notation "PStmt" => LowIR.Prog.Stmt

/-! ## Plain machine iteration `stepN` (no early-halt check — `Nat.iterate` and
    the `f^[n]` notation are Mathlib-only in this toolchain). A top-level bridge
    to `runFuel (codeBase+4)` lands in Phase 6; mid-proof we use `stepN`. -/
def stepN : Nat → State → State
  | 0,     m => m
  | k + 1, m => stepN k (step m)

@[simp] theorem stepN_zero (m : State) : stepN 0 m = m := rfl
theorem stepN_succ (k : Nat) (m : State) : stepN (k + 1) m = stepN k (step m) := rfl

/-- Iteration composes: `a` then `b` steps. Induction on `a` (the `step m` peels
    from the front, matching `stepN`'s definitional recursion). -/
theorem stepN_add (a b : Nat) (m : State) : stepN (a + b) m = stepN b (stepN a m) := by
  induction a generalizing m with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 from by omega, stepN_succ, stepN_succ, ih]

/-! ## The resolved straight-line lowering `emit`. -/

/-- Resolved `loadSlot`: physical reg `t := IL reg r` (r=0 ⇒ materialise 0). -/
def loadSlotI (r t : Nat) : List Instr :=
  if r = 0 then [.addi t 0 0] else [.ld t SP (BitVec.ofNat 12 (slotOff r))]

/-- Resolved `storeSlot`: IL reg `r := physical reg t` (r=0 ⇒ discard). -/
def storeSlotI (r t : Nat) : List Instr :=
  if r = 0 then [] else [.sd SP t (BitVec.ofNat 12 (slotOff r))]

/-- The resolved instruction stream for a straight-line statement — mirrors
    `Compile.lower` exactly for the label-free cases (validated by `#guard`
    against the real pipeline below). Control-flow/`cref`/`clen` are `[]` here;
    their `lower_sim` cases are `sorry` (they use the real `Emitted`, not `emit`). -/
def emit : PStmt → List Instr
  | .skip            => []
  | .annot _         => []
  | .addi rd rs imm  => loadSlotI rs T0 ++ [.addi T0 T0 imm] ++ storeSlotI rd T0
  | .add  rd r1 r2   => loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [.add T0 T0 T1] ++ storeSlotI rd T0
  | .sub  rd r1 r2   => loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [.sub T0 T0 T1] ++ storeSlotI rd T0
  | .orr  rd r1 r2   => loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [.or  T0 T0 T1] ++ storeSlotI rd T0
  | .slli rd rs sh   => loadSlotI rs T0 ++ [.slli T0 T0 sh] ++ storeSlotI rd T0
  | .srli rd rs sh   => loadSlotI rs T0 ++ [.srli T0 T0 sh] ++ storeSlotI rd T0
  | .seq a b         => emit a ++ emit b
  | _                => []

/-! ## `Emitted` — the static "code segment carries `is` at `pos`" fact. -/

/-- `L.instrs` has `is` as its segment starting at byte offset `pos`
    (`pos` 4-aligned; each `is[j]` is `L.instrs[pos/4 + j]`). Static in `L`; the
    machine fetch is recovered from `Installed` (a `StInv` conjunct). -/
def Emitted (L : Layout) (pos : Nat) (is : List Instr) : Prop :=
  pos % 4 = 0 ∧ ∀ (j : Nat) (h : j < is.length),
    ∃ (h2 : pos / 4 + j < L.instrs.length), L.instrs[pos / 4 + j] = is[j]'h

/-- `Emitted` of a concatenation splits: `is₁` at `pos`, `is₂` at `pos + 4|is₁|`. -/
theorem Emitted_append_left (L : Layout) (pos : Nat) (is₁ is₂ : List Instr)
    (h : Emitted L pos (is₁ ++ is₂)) : Emitted L pos is₁ := by
  obtain ⟨ha, hf⟩ := h
  refine ⟨ha, fun j hj => ?_⟩
  obtain ⟨h2, he⟩ := hf j (by simp only [List.length_append]; omega)
  exact ⟨h2, by rw [he, List.getElem_append_left hj]⟩

theorem Emitted_append_right (L : Layout) (pos : Nat) (is₁ is₂ : List Instr)
    (h : Emitted L pos (is₁ ++ is₂)) : Emitted L (pos + 4 * is₁.length) is₂ := by
  obtain ⟨ha, hf⟩ := h
  refine ⟨by omega, fun j hj => ?_⟩
  obtain ⟨h2, he⟩ := hf (is₁.length + j) (by simp only [List.length_append]; omega)
  have hpos : (pos + 4 * is₁.length) / 4 + j = pos / 4 + (is₁.length + j) := by omega
  have hb : (pos + 4 * is₁.length) / 4 + j < L.instrs.length := by rw [hpos]; exact h2
  refine ⟨hb, ?_⟩
  simp only [hpos, he]
  simp

/-- The fetch bridge: `Emitted` (static) + `Installed` (a `StInv` conjunct,
    preserved across steps) ⇒ the machine at `codeBase + (pos + 4j)` decodes to
    `is[j]`. This is how the op proofs read each instruction from memory. -/
theorem decode_emitted (L : Layout) (m : State) (pos : Nat) (is : List Instr)
    (hem : Emitted L pos is) (hinst : Installed L m) (j : Nat) (hj : j < is.length) :
    decode (fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (pos + 4 * j) }) = is[j]'hj := by
  obtain ⟨ha, hf⟩ := hem
  obtain ⟨h2, he⟩ := hf j hj
  obtain ⟨hcode, _⟩ := hinst
  have hpc4 : L.codeBase + BitVec.ofNat 64 (pos + 4 * j)
            = L.codeBase + BitVec.ofNat 64 (4 * (pos / 4 + j)) := by
    congr 1; congr 1; omega
  rw [hpc4, ← he]; exact hcode (pos / 4 + j) h2

/-! ## Machine-step lemmas (one decoded instruction ⇒ one `step`). -/

theorem step_addi (m : State) (rd rs : Nat) (imm : BitVec 12)
    (h : decode (fetch32 m) = .addi rd rs imm) :
    step m = (m.rset rd (m.rget rs + imm.signExtend 64)).setPc (m.pc + 4) := by
  simp only [step, h]

theorem step_add (m : State) (rd r1 r2 : Nat) (h : decode (fetch32 m) = .add rd r1 r2) :
    step m = (m.rset rd (m.rget r1 + m.rget r2)).setPc (m.pc + 4) := by simp only [step, h]

theorem step_sub (m : State) (rd r1 r2 : Nat) (h : decode (fetch32 m) = .sub rd r1 r2) :
    step m = (m.rset rd (m.rget r1 - m.rget r2)).setPc (m.pc + 4) := by simp only [step, h]

theorem step_or (m : State) (rd r1 r2 : Nat) (h : decode (fetch32 m) = .or rd r1 r2) :
    step m = (m.rset rd (m.rget r1 ||| m.rget r2)).setPc (m.pc + 4) := by simp only [step, h]

theorem step_slli (m : State) (rd rs sh : Nat) (h : decode (fetch32 m) = .slli rd rs sh) :
    step m = (m.rset rd (m.rget rs <<< sh)).setPc (m.pc + 4) := by simp only [step, h]

theorem step_srli (m : State) (rd rs sh : Nat) (h : decode (fetch32 m) = .srli rd rs sh) :
    step m = (m.rset rd (m.rget rs >>> sh)).setPc (m.pc + 4) := by simp only [step, h]

theorem step_ld (m : State) (rd rs : Nat) (imm : BitVec 12)
    (h : decode (fetch32 m) = .ld rd rs imm) :
    step m = (m.rset rd (m.loadWord (m.rget rs + imm.signExtend 64))).setPc (m.pc + 4) := by
  simp only [step, h]

theorem step_sd (m : State) (rs1 rs2 : Nat) (imm : BitVec 12)
    (h : decode (fetch32 m) = .sd rs1 rs2 imm) :
    step m = (m.storeWord (m.rget rs1 + imm.signExtend 64) (m.rget rs2)).setPc (m.pc + 4) := by
  simp only [step, h]

/-! ## Immediate roundtrip for slot offsets. -/

/-- A small non-negative 12-bit immediate sign-extends to itself: the machine's
    `imm.signExtend 64` recovers `slotOff r` (kept `< 2¹¹` by `fnOk`'s
    `totalFrame ≤ 2000`). Derived through `toInt = toNat.bmod` — the direct
    `toNat_signExtend`/`signExtend_eq_setWidth` are `Classical.choice`-tainted in
    this stdlib, this route stays `[propext, Quot.sound]`. -/
theorem signExtend_ofNat_lt (v : Nat) (h : v < 2 ^ 11) :
    (BitVec.ofNat 12 v).signExtend 64 = BitVec.ofNat 64 v := by
  have ht : (BitVec.ofNat 12 v).toInt = (v : Int) := by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [Int.bmod_eq_emod_of_lt] <;> simp <;> omega
  simp only [BitVec.signExtend, ht, BitVec.ofInt_natCast]

/-! ## `StInv` is insensitive to scratch registers and `pc`.

    `StInv` reads `m` only through `m.rget 2` (= x2/sp) and `m.mem`; so changing
    any other register (the x5/x6 scratch the op lowering churns) or the `pc`
    preserves it. This lets each intermediate machine state in an op's
    instruction sequence keep satisfying `StInv s`. -/
theorem StInv_congr (L : Layout) (fd : FunDef) (holes : List Hole) (s : St)
    (m m' : State) (h2 : m'.rget 2 = m.rget 2) (hmem : m'.mem = m.mem)
    (H : StInv L fd holes s m) : StInv L fd holes s m' := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := H
  refine ⟨by rw [h2]; exact c1, fun r hr hr' => ?_, ?_, fun a ha => by rw [hmem]; exact c4 a ha, c5, c6⟩
  · rw [c2 r hr hr']; simp only [State.loadWord, hmem]
  · obtain ⟨hcode, hdata⟩ := c3
    refine ⟨fun j hj => ?_, fun i hi => by rw [hmem]; exact hdata i hi⟩
    have hf : fetch32 { m' with pc := L.codeBase + BitVec.ofNat 64 (4 * j) }
            = fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) } := by
      simp only [fetch32, hmem]
    rw [hf]; exact hcode j hj

/-! ## `lower_sim` — the statement-level simulation (VERTICAL SLICE).

    If the IL says `stmt` runs `s ↦ s'` with a `.normal` outcome, and the machine
    sits at `codeBase + pos` in a `StInv`-related state with `emit stmt` installed
    there, then it runs `k` steps to `codeBase + (pos + 4·|emit stmt|)` in a state
    still `StInv`-related to `s'`. The `.normal`-only form covers the straight-line
    slice (skip/annot/arith/seq); the control-flow cases (whose outcome selects a
    label target) and the `ld/sd/cref/clen` memory cases are the `sorry`'d
    remainder (Phases 4.2–4.4). The frame- and blob-placement hypotheses
    (`hframe`/`hnw`/`hseg`/`hblob`/`hbd`) are `SlotFacts`' side conditions, from
    `fnOk`+`SimPre` downstream. -/
theorem lower_sim
    {P : Program} {dbase : Name → Option Word} {pad : Name → Nat} {stackLo : Word}
    {L : Layout} {fd : FunDef} {holes : List Hole}
    (fuel : Nat) (stmt : PStmt) (s s' : St) (m : State) (pos : Nat)
    (hexec : LowIR.Prog.exec P dbase pad stackLo fuel stmt s = some (s', .normal))
    (hinv  : StInv L fd holes s m)
    (hpc   : m.pc = L.codeBase + BitVec.ofNat 64 pos)
    (hem   : Emitted L pos (emit stmt))
    (hreg  : maxRegS stmt ≤ maxRegF fd)
    (hframe : userOff fd ≤ 2000)
    (hnw   : s.sp.toNat + userOff fd ≤ 2 ^ 64)
    (hseg  : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd   : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
               ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat) :
    ∃ k, StInv L fd holes s' (stepN k m)
       ∧ (stepN k m).pc
           = L.codeBase + BitVec.ofNat 64 (pos + 4 * (emit stmt).length) := by
  induction fuel generalizing stmt s s' m pos with
  | zero => exact absurd hexec (by simp [LowIR.Prog.exec])
  | succ fuel ih =>
    cases stmt
    case skip =>
      rw [LowIR.Prog.exec_skip, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      exact ⟨0, hinv, by simp only [stepN_zero, emit, List.length_nil, Nat.mul_zero,
                                    Nat.add_zero]; exact hpc⟩
    case annot a =>
      rw [LowIR.Prog.exec_annot, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      exact ⟨0, hinv, by simp only [stepN_zero, emit, List.length_nil, Nat.mul_zero,
                                    Nat.add_zero]; exact hpc⟩
    all_goals sorry

/-! ## Executable oracle: `emit` mirrors the real `Compile.lower` (straight-line). -/

section Guards
open LowIR.Prog (sub3)
open LowIR.Compile (lower)

-- `emit sub3.body` = the resolved (`.ins`-extracted) real lowering of the body.
#guard ((lower [] [] [] 0 sub3.body).run' 0).filterMap
          (fun si => match si with | .ins i => some i | _ => none)
        = emit sub3.body
end Guards

end LowIR.ProgSim
