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

/-! ## Structural register/pc/memory facts (scratch bookkeeping). -/

@[simp] theorem mem_setPc (m : State) (p : Word) : (m.setPc p).mem = m.mem := rfl
@[simp] theorem rget_setPc (m : State) (p : Word) (b : Nat) : (m.setPc p).rget b = m.rget b := rfl
@[simp] theorem pc_setPc (m : State) (p : Word) : (m.setPc p).pc = p := rfl

@[simp] theorem mem_rset (m : State) (a : Nat) (v : Word) : (m.rset a v).mem = m.mem := by
  unfold State.rset; split <;> rfl

/-- `rset a` leaves `rget b` for `b ≠ a` (and x0). -/
theorem rget_rset_ne (m : State) (a b : Nat) (v : Word) (h : b ≠ a) :
    (m.rset a v).rget b = m.rget b := by
  unfold State.rset State.rget
  split
  · rfl
  · split
    · rfl
    · show (if b = a then v else m.reg b) = m.reg b
      rw [if_neg h]

/-- `rset a` then `rget a` returns the written value (`a ≠ 0`). -/
theorem rget_rset_self (m : State) (a : Nat) (v : Word) (ha : a ≠ 0) :
    (m.rset a v).rget a = v := by
  unfold State.rset State.rget
  rw [if_neg ha, if_neg ha]
  show (if a = a then v else m.reg a) = v
  rw [if_pos rfl]

/-- The fetch bridge for an intermediate machine state `mj` reached mid-op: same
    code memory as `m`, positioned at instruction `j`. -/
theorem decode_at (L : Layout) (m mj : State) (pos : Nat) (is : List Instr)
    (hem : Emitted L pos is) (hinst : Installed L m) (j : Nat) (hj : j < is.length)
    (hpcj : mj.pc = L.codeBase + BitVec.ofNat 64 (pos + 4 * j)) (hmemj : mj.mem = m.mem) :
    decode (fetch32 mj) = is[j]'hj := by
  have : fetch32 mj = fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (pos + 4 * j) } := by
    simp only [fetch32, hpcj, hmemj]
  rw [this]; exact decode_emitted L m pos is hem hinst j hj

/-- `StInv` survives a scratch-register write (`a ≠ 2`) plus a `pc` change —
    the shape every intermediate machine state in an op's stream has. -/
theorem StInv_scratch (L : Layout) (fd : FunDef) (holes : List Hole) (s : St)
    (m : State) (a : Nat) (v p : Word) (ha : a ≠ 2) (hinv : StInv L fd holes s m) :
    StInv L fd holes s ((m.rset a v).setPc p) := by
  refine StInv_congr L fd holes s m _ ?_ ?_ hinv
  · rw [rget_setPc]; exact rget_rset_ne m a 2 v (fun h => ha h.symm)
  · rw [mem_setPc, mem_rset]

/-! ## Op-lowering building blocks. -/

/-- pc advances by one instruction: `codeBase + pos + 4 = codeBase + (pos+4)`. -/
theorem pc_add4 (cb : Word) (p : Nat) :
    cb + BitVec.ofNat 64 p + 4 = cb + BitVec.ofNat 64 (p + 4) := by
  rw [BitVec.add_assoc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]

/-- Executing one `loadSlotI r t` instruction parks `IL reg r` into physical `t`,
    uniformly over `r = 0` (materialise 0) and `r ≠ 0` (`ld` from the slot). The
    only machine change is `t := s.rget r` and `pc += 4`. -/
theorem load_step (L : Layout) (fd : FunDef) (holes : List Hole) (s : St) (m : State)
    (r t : Nat) (hinv : StInv L fd holes s m) (hr : r ≤ maxRegF fd) (hfr : slotOff r < 2 ^ 11)
    (hdec : decode (fetch32 m)
              = (if r = 0 then Instr.addi t 0 0
                 else Instr.ld t SP (BitVec.ofNat 12 (slotOff r)))) :
    step m = (m.rset t (s.rget r)).setPc (m.pc + 4) := by
  obtain ⟨c1, c2, -, -, -, -⟩ := hinv
  by_cases hr0 : r = 0
  · subst hr0
    rw [if_pos rfl] at hdec
    rw [step_addi m t 0 0 hdec]
    -- `m.rget 0 + (0).signExtend 64` and `s.rget 0` are both defeq `0`
    congr 2
  · rw [if_neg hr0] at hdec
    rw [step_ld m t SP (BitVec.ofNat 12 (slotOff r)) hdec]
    congr 2
    rw [show m.rget SP = s.sp from c1, signExtend_ofNat_lt (slotOff r) hfr]
    exact (c2 r (by omega) hr).symm

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
    case addi rd rs imm =>
      rw [LowIR.Prog.exec_addi, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      simp only [maxRegS] at hreg
      have hrs : rs ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hreg
      have hrd : rd ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      have hfrs : slotOff rs < 2 ^ 11 := by have := slotOff_add8_le_userOff fd rs hrs; omega
      have hfrd : slotOff rd < 2 ^ 11 := by have := slotOff_add8_le_userOff fd rd hrd; omega
      have hinst : Installed L m := hinv.2.2.1
      cases Nat.decEq rs 0 with
      | isTrue _ => sorry
      | isFalse hrs0 =>
        cases Nat.decEq rd 0 with
        | isTrue _ => sorry
        | isFalse hrd0 =>
          -- MAIN: rs ≠ 0, rd ≠ 0 — the 3-instruction ld/addi/sd path
          have hemit : emit (LowIR.Prog.Stmt.addi rd rs imm)
              = [Instr.ld T0 SP (BitVec.ofNat 12 (slotOff rs)),
                 Instr.addi T0 T0 imm,
                 Instr.sd SP T0 (BitVec.ofNat 12 (slotOff rd))] := by
            simp only [emit, loadSlotI, storeSlotI, if_neg hrs0, if_neg hrd0,
                       List.cons_append, List.nil_append]
          rw [hemit] at hem ⊢
          -- instruction 0: ld T0, slot rs
          have hd0 : decode (fetch32 m) = Instr.ld T0 SP (BitVec.ofNat 12 (slotOff rs)) := by
            have h := decode_at L m m pos _ hem hinst 0 (by simp)
                        (by simp only [Nat.mul_zero, Nat.add_zero]; exact hpc) rfl
            simpa using h
          have hs1 : step m = (m.rset T0 (s.rget rs)).setPc (m.pc + 4) :=
            load_step L fd holes s m rs T0 hinv hrs hfrs (by rw [if_neg hrs0]; exact hd0)
          have hinv1 : StInv L fd holes s ((m.rset T0 (s.rget rs)).setPc (m.pc + 4)) :=
            StInv_scratch L fd holes s m T0 _ _ (by decide) hinv
          have h1pc : ((m.rset T0 (s.rget rs)).setPc (m.pc + 4)).pc
              = L.codeBase + BitVec.ofNat 64 (pos + 4 * 1) := by
            rw [pc_setPc, hpc, pc_add4]
          have h1mem : ((m.rset T0 (s.rget rs)).setPc (m.pc + 4)).mem = m.mem := by
            rw [mem_setPc, mem_rset]
          have h1T0 : ((m.rset T0 (s.rget rs)).setPc (m.pc + 4)).rget T0 = s.rget rs := by
            rw [rget_setPc]; exact rget_rset_self m T0 _ (by decide)
          -- instruction 1: addi T0, T0, imm
          have hd1 : decode (fetch32 ((m.rset T0 (s.rget rs)).setPc (m.pc + 4)))
              = Instr.addi T0 T0 imm := by
            have h := decode_at L m _ pos _ hem hinst 1 (by simp) h1pc h1mem
            simpa using h
          have hs2 : step ((m.rset T0 (s.rget rs)).setPc (m.pc + 4))
              = (((m.rset T0 (s.rget rs)).setPc (m.pc + 4)).rset T0
                    (s.rget rs + imm.signExtend 64)).setPc
                  (((m.rset T0 (s.rget rs)).setPc (m.pc + 4)).pc + 4) := by
            rw [step_addi _ T0 T0 imm hd1, h1T0]
          -- name the two intermediate machine states to keep terms small
          generalize hM1 : (m.rset T0 (s.rget rs)).setPc (m.pc + 4) = M1
            at hs1 hinv1 h1pc h1mem h1T0 hd1 hs2
          generalize hM2 : (M1.rset T0 (s.rget rs + imm.signExtend 64)).setPc (M1.pc + 4) = M2
            at hs2
          -- M2's frame-visible state (from M1's, one scratch write + pc bump)
          have hinv2 : StInv L fd holes s M2 := by
            rw [← hM2]; exact StInv_scratch L fd holes s M1 T0 _ _ (by decide) hinv1
          have h2pc : M2.pc = L.codeBase + BitVec.ofNat 64 (pos + 4 * 2) := by
            rw [← hM2, pc_setPc, h1pc, pc_add4]
          have h2mem : M2.mem = m.mem := by rw [← hM2, mem_setPc, mem_rset]; exact h1mem
          have h2T0 : M2.rget T0 = s.rget rs + imm.signExtend 64 := by
            rw [← hM2, rget_setPc]; exact rget_rset_self M1 T0 _ (by decide)
          -- instruction 2: sd slot rd, T0  (the store — the P1 payoff)
          have hd2 : decode (fetch32 M2) = Instr.sd SP T0 (BitVec.ofNat 12 (slotOff rd)) := by
            have h := decode_at L m M2 pos _ hem hinst 2 (by simp) h2pc h2mem
            simpa using h
          have hs3 : step M2
              = (M2.storeWord (s.sp + BitVec.ofNat 64 (slotOff rd))
                    (s.rget rs + imm.signExtend 64)).setPc (M2.pc + 4) := by
            rw [step_sd M2 SP T0 (BitVec.ofNat 12 (slotOff rd)) hd2,
                show M2.rget SP = s.sp from hinv2.1, signExtend_ofNat_lt (slotOff rd) hfrd, h2T0]
          have hstore : StInv L fd holes (s.rset rd (s.rget rs + imm.signExtend 64))
              (M2.storeWord (s.sp + BitVec.ofNat 64 (slotOff rd))
                 (s.rget rs + imm.signExtend 64)) :=
            StInv_store_slot L fd holes s M2 rd _ hinv2 (by omega) hrd hnw hseg hblob hbd
          -- stepN 3 m = the final state; then StInv + pc
          have hrun : stepN 3 m
              = (M2.storeWord (s.sp + BitVec.ofNat 64 (slotOff rd))
                    (s.rget rs + imm.signExtend 64)).setPc (M2.pc + 4) := by
            simp only [stepN]; rw [hs1, hs2, hs3]
          refine ⟨3, ?_, ?_⟩
          · rw [hrun]
            exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hstore
          · rw [hrun, pc_setPc, h2pc, pc_add4]; rfl
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
