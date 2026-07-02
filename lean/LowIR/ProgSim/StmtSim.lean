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

/-- Normalise a code position under `codeBase +` by any provably-equal `Nat`. -/
theorem pc_congr (cb : Word) {p q : Nat} (h : p = q) :
    cb + BitVec.ofNat 64 p = cb + BitVec.ofNat 64 q := by rw [h]

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

/-! ## Segment length / head lemmas for `loadSlotI`/`storeSlotI`. -/

theorem loadSlotI_length (r t : Nat) : (loadSlotI r t).length = 1 := by
  unfold loadSlotI; split <;> rfl

theorem storeSlotI_length (r t : Nat) : (storeSlotI r t).length = if r = 0 then 0 else 1 := by
  unfold storeSlotI; split <;> rfl

theorem loadSlotI_get0 (r t : Nat) (hj : 0 < (loadSlotI r t).length) :
    (loadSlotI r t)[0]'hj
      = if r = 0 then Instr.addi t 0 0 else Instr.ld t SP (BitVec.ofNat 12 (slotOff r)) := by
  unfold loadSlotI; split <;> rfl

theorem storeSlotI_get0 (r t : Nat) (hr0 : r ≠ 0) (hj : 0 < (storeSlotI r t).length) :
    (storeSlotI r t)[0]'hj = Instr.sd SP t (BitVec.ofNat 12 (slotOff r)) := by
  unfold storeSlotI; split
  · rename_i h; exact absurd h hr0
  · rfl

/-! ## Load / store phase helpers (uniform over `r = 0`, reused by every op). -/

/-- Run one `loadSlotI r t` segment: `t := s.rget r`, `StInv` preserved, `pc += 4`,
    memory and every other register untouched. `t` is a scratch reg (`≠ 2`, `≠ 0`). -/
theorem run_load (L : Layout) (fd : FunDef) (holes : List Hole) (s : St) (m : State)
    (r t q : Nat) (hinv : StInv L fd holes s m) (hr : r ≤ maxRegF fd) (hfr : slotOff r < 2 ^ 11)
    (ht2 : t ≠ 2) (ht0 : t ≠ 0) (hq : m.pc = L.codeBase + BitVec.ofNat 64 q)
    (hem : Emitted L q (loadSlotI r t)) :
    StInv L fd holes s (step m)
    ∧ (step m).pc = L.codeBase + BitVec.ofNat 64 (q + 4)
    ∧ (step m).mem = m.mem
    ∧ (step m).rget t = s.rget r
    ∧ ∀ t', t' ≠ t → (step m).rget t' = m.rget t' := by
  have hinst : Installed L m := hinv.2.2.1
  have hlen : 0 < (loadSlotI r t).length := by rw [loadSlotI_length]; omega
  have hd : decode (fetch32 m)
      = if r = 0 then Instr.addi t 0 0 else Instr.ld t SP (BitVec.ofNat 12 (slotOff r)) := by
    have h := decode_at L m m q (loadSlotI r t) hem hinst 0 hlen
                (by simp only [Nat.mul_zero, Nat.add_zero]; exact hq) rfl
    rwa [loadSlotI_get0] at h
  have hstep : step m = (m.rset t (s.rget r)).setPc (m.pc + 4) :=
    load_step L fd holes s m r t hinv hr hfr hd
  rw [hstep]
  refine ⟨StInv_scratch L fd holes s m t _ _ ht2 hinv, ?_, ?_, ?_, fun t' ht' => ?_⟩
  · rw [pc_setPc, hq, pc_add4]
  · rw [mem_setPc, mem_rset]
  · rw [rget_setPc]; exact rget_rset_self m t _ ht0
  · rw [rget_setPc]; exact rget_rset_ne m t t' _ ht'

/-- Run the final `storeSlotI rd T0` segment given `T0 = v`: reaches `StInv` for
    `s.rset rd v`. `rd = 0` is a no-op (0 steps, `rset 0` discards); `rd ≠ 0` is
    the `sd` + `StInv_store_slot` (the P1 payoff). -/
theorem run_store (L : Layout) (fd : FunDef) (holes : List Hole) (s : St) (m2 : State)
    (rd : Nat) (v : Word) (q : Nat) (hinv2 : StInv L fd holes s m2) (hT0 : m2.rget T0 = v)
    (hq : m2.pc = L.codeBase + BitVec.ofNat 64 q) (hem : Emitted L q (storeSlotI rd T0))
    (hrd : rd ≤ maxRegF fd) (hfrd : slotOff rd < 2 ^ 11)
    (hnw : s.sp.toNat + userOff fd ≤ 2 ^ 64) (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
             ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat) :
    ∃ ks, StInv L fd holes (s.rset rd v) (stepN ks m2)
        ∧ (stepN ks m2).pc
            = L.codeBase + BitVec.ofNat 64 (q + 4 * (storeSlotI rd T0).length) := by
  have hinst : Installed L m2 := hinv2.2.2.1
  cases Nat.decEq rd 0 with
  | isTrue hrd0 =>
    subst hrd0
    exact ⟨0, hinv2, by simp only [stepN_zero]; exact hq⟩
  | isFalse hrd0 =>
    have hlen : 0 < (storeSlotI rd T0).length := by rw [storeSlotI_length, if_neg hrd0]; omega
    have hd : decode (fetch32 m2) = Instr.sd SP T0 (BitVec.ofNat 12 (slotOff rd)) := by
      have h := decode_at L m2 m2 q (storeSlotI rd T0) hem hinst 0 hlen
                  (by simp only [Nat.mul_zero, Nat.add_zero]; exact hq) rfl
      rwa [storeSlotI_get0 rd T0 hrd0] at h
    have hstep : step m2
        = (m2.storeWord (s.sp + BitVec.ofNat 64 (slotOff rd)) v).setPc (m2.pc + 4) := by
      rw [step_sd m2 SP T0 (BitVec.ofNat 12 (slotOff rd)) hd,
          show m2.rget SP = s.sp from hinv2.1, signExtend_ofNat_lt (slotOff rd) hfrd, hT0]
    have hstore : StInv L fd holes (s.rset rd v)
        (m2.storeWord (s.sp + BitVec.ofNat 64 (slotOff rd)) v) :=
      StInv_store_slot L fd holes s m2 rd v hinv2 (by omega) hrd hnw hseg hblob hbd
    refine ⟨1, ?_, ?_⟩
    · rw [show stepN 1 m2 = step m2 from rfl, hstep]
      exact StInv_congr L fd holes _ _ _ (by rw [rget_setPc]) (by rw [mem_setPc]) hstore
    · rw [show stepN 1 m2 = step m2 from rfl, hstep, pc_setPc, hq, pc_add4,
          storeSlotI_length, if_neg hrd0]

/-! ## Whole-op simulators: `single_op_sim` (1 source) / `two_op_sim` (2 sources).

    These factor the shared `load(s) → compute → store` shape of every arithmetic
    op. The compute instruction `C` and the resulting `T0` value `vC` are abstract;
    the caller supplies `hC` (the one-instruction step lemma specialised to `C`),
    so `addi`/`slli`/`srli` (and `add`/`sub`/`orr`) each reduce to a one-line
    application. Source registers stay symbolic (`run_load` is uniform over `r=0`)
    and the `rd=0`/`rd≠0` split lives once inside `run_store`. -/

/-- Single-source op: `emit = loadSlotI rs T0 ++ [C] ++ storeSlotI rd T0`, result
    `s.rset rd vC`. `hC`: once `T0 = s.rget rs`, executing `C` sets `T0 := vC`. -/
theorem single_op_sim {L : Layout} {fd : FunDef} {holes : List Hole}
    (s : St) (m : State) (rd rs pos : Nat) (C : Instr) (vC : Word)
    (hinv : StInv L fd holes s m) (hpc : m.pc = L.codeBase + BitVec.ofNat 64 pos)
    (hem : Emitted L pos (loadSlotI rs T0 ++ [C] ++ storeSlotI rd T0))
    (hrs : rs ≤ maxRegF fd) (hrd : rd ≤ maxRegF fd)
    (hfrs : slotOff rs < 2 ^ 11) (hfrd : slotOff rd < 2 ^ 11)
    (hnw : s.sp.toNat + userOff fd ≤ 2 ^ 64) (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
             ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat)
    (hC : ∀ m', decode (fetch32 m') = C → m'.rget T0 = s.rget rs →
            step m' = (m'.rset T0 vC).setPc (m'.pc + 4)) :
    ∃ k, StInv L fd holes (s.rset rd vC) (stepN k m)
       ∧ (stepN k m).pc = L.codeBase
           + BitVec.ofNat 64 (pos + 4 * (loadSlotI rs T0 ++ [C] ++ storeSlotI rd T0).length) := by
  have hinst : Installed L m := hinv.2.2.1
  -- instruction 0: load rs into T0
  have hemL : Emitted L pos (loadSlotI rs T0) :=
    Emitted_append_left L pos _ _ (Emitted_append_left L pos _ _ hem)
  obtain ⟨hinv1, h1pc, h1mem, h1T0, -⟩ :=
    run_load L fd holes s m rs T0 pos hinv hrs hfrs (by decide) (by decide) hpc hemL
  -- instruction 1: the compute `C` at pos+4
  have hemC : Emitted L (pos + 4) [C] := by
    have h := Emitted_append_right L pos (loadSlotI rs T0) [C] (Emitted_append_left L pos _ _ hem)
    rwa [loadSlotI_length, Nat.mul_one] at h
  have hdC : decode (fetch32 (step m)) = C := by
    have h := decode_at L m (step m) (pos + 4) [C] hemC hinst 0 (by simp) (by rw [h1pc]) h1mem
    simpa using h
  have hsC : step (step m) = ((step m).rset T0 vC).setPc ((step m).pc + 4) := hC _ hdC h1T0
  have hinv2 : StInv L fd holes s (step (step m)) := by
    rw [hsC]; exact StInv_scratch L fd holes s (step m) T0 _ _ (by decide) hinv1
  have h2pc : (step (step m)).pc = L.codeBase + BitVec.ofNat 64 (pos + 8) := by
    rw [hsC, pc_setPc, h1pc, pc_add4]
  have h2T0 : (step (step m)).rget T0 = vC := by
    rw [hsC, rget_setPc]; exact rget_rset_self (step m) T0 _ (by decide)
  -- instruction 2: store T0 into slot rd (the tail; `rd=0`/`≠0` handled by run_store)
  have hemS : Emitted L (pos + 8) (storeSlotI rd T0) := by
    have h := Emitted_append_right L pos (loadSlotI rs T0 ++ [C]) (storeSlotI rd T0) hem
    rw [List.length_append, loadSlotI_length] at h; simpa using h
  obtain ⟨ks, hSt, hStpc⟩ := run_store L fd holes s (step (step m)) rd vC (pos + 8)
    hinv2 h2T0 h2pc hemS hrd hfrd hnw hseg hblob hbd
  have h2run : stepN 2 m = step (step m) := rfl
  refine ⟨2 + ks, ?_, ?_⟩
  · rw [stepN_add, h2run]; exact hSt
  · rw [stepN_add, h2run, hStpc, List.length_append, List.length_append, loadSlotI_length]
    exact pc_congr _ (by simp only [List.length_cons, List.length_nil]; omega)

/-- Two-source op: `emit = loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [C] ++ storeSlotI rd T0`,
    result `s.rset rd vC`. `hC`: once `T0 = s.rget r1` and `T1 = s.rget r2`,
    executing `C` sets `T0 := vC`. -/
theorem two_op_sim {L : Layout} {fd : FunDef} {holes : List Hole}
    (s : St) (m : State) (rd r1 r2 pos : Nat) (C : Instr) (vC : Word)
    (hinv : StInv L fd holes s m) (hpc : m.pc = L.codeBase + BitVec.ofNat 64 pos)
    (hem : Emitted L pos (loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [C] ++ storeSlotI rd T0))
    (hr1 : r1 ≤ maxRegF fd) (hr2 : r2 ≤ maxRegF fd) (hrd : rd ≤ maxRegF fd)
    (hfr1 : slotOff r1 < 2 ^ 11) (hfr2 : slotOff r2 < 2 ^ 11) (hfrd : slotOff rd < 2 ^ 11)
    (hnw : s.sp.toNat + userOff fd ≤ 2 ^ 64) (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
             ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat)
    (hC : ∀ m', decode (fetch32 m') = C → m'.rget T0 = s.rget r1 → m'.rget T1 = s.rget r2 →
            step m' = (m'.rset T0 vC).setPc (m'.pc + 4)) :
    ∃ k, StInv L fd holes (s.rset rd vC) (stepN k m)
       ∧ (stepN k m).pc = L.codeBase + BitVec.ofNat 64
           (pos + 4 * (loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [C] ++ storeSlotI rd T0).length) := by
  have hinst : Installed L m := hinv.2.2.1
  -- instruction 0: load r1 into T0
  have hemL0 : Emitted L pos (loadSlotI r1 T0) :=
    Emitted_append_left L pos _ _ (Emitted_append_left L pos _ _ (Emitted_append_left L pos _ _ hem))
  obtain ⟨hinv1, h1pc, h1mem, h1T0, -⟩ :=
    run_load L fd holes s m r1 T0 pos hinv hr1 hfr1 (by decide) (by decide) hpc hemL0
  -- instruction 1: load r2 into T1 (preserves T0 since T1 ≠ T0)
  have hemL1 : Emitted L (pos + 4) (loadSlotI r2 T1) := by
    have h := Emitted_append_right L pos (loadSlotI r1 T0) (loadSlotI r2 T1)
                (Emitted_append_left L pos _ _ (Emitted_append_left L pos _ _ hem))
    rwa [loadSlotI_length, Nat.mul_one] at h
  obtain ⟨hinv2, h2pc, h2mem, h2T1, h2oth⟩ :=
    run_load L fd holes s (step m) r2 T1 (pos + 4) hinv1 hr2 hfr2 (by decide) (by decide) h1pc hemL1
  have h2T0 : (step (step m)).rget T0 = s.rget r1 := by
    rw [h2oth T0 (by decide)]; exact h1T0
  -- instruction 2: the compute `C` at pos+8
  have hemC : Emitted L (pos + 8) [C] := by
    have h := Emitted_append_right L pos (loadSlotI r1 T0 ++ loadSlotI r2 T1) [C]
                (Emitted_append_left L pos _ _ hem)
    rw [List.length_append, loadSlotI_length, loadSlotI_length] at h; simpa using h
  have hdC : decode (fetch32 (step (step m))) = C := by
    have h := decode_at L m (step (step m)) (pos + 8) [C] hemC hinst 0 (by simp)
                (by rw [h2pc]) (by rw [h2mem, h1mem])
    simpa using h
  have hsC : step (step (step m))
      = ((step (step m)).rset T0 vC).setPc ((step (step m)).pc + 4) := hC _ hdC h2T0 h2T1
  have hinv3 : StInv L fd holes s (step (step (step m))) := by
    rw [hsC]; exact StInv_scratch L fd holes s (step (step m)) T0 _ _ (by decide) hinv2
  have h3pc : (step (step (step m))).pc = L.codeBase + BitVec.ofNat 64 (pos + 12) := by
    rw [hsC, pc_setPc, h2pc, pc_add4]
  have h3T0 : (step (step (step m))).rget T0 = vC := by
    rw [hsC, rget_setPc]; exact rget_rset_self (step (step m)) T0 _ (by decide)
  -- instruction 3: store T0 into slot rd
  have hemS : Emitted L (pos + 12) (storeSlotI rd T0) := by
    have h := Emitted_append_right L pos (loadSlotI r1 T0 ++ loadSlotI r2 T1 ++ [C])
                (storeSlotI rd T0) hem
    rw [List.length_append, List.length_append, loadSlotI_length, loadSlotI_length] at h
    simpa using h
  obtain ⟨ks, hSt, hStpc⟩ := run_store L fd holes s (step (step (step m))) rd vC (pos + 12)
    hinv3 h3T0 h3pc hemS hrd hfrd hnw hseg hblob hbd
  have h3run : stepN 3 m = step (step (step m)) := rfl
  refine ⟨3 + ks, ?_, ?_⟩
  · rw [stepN_add, h3run]; exact hSt
  · rw [stepN_add, h3run, hStpc, List.length_append, List.length_append, List.length_append,
        loadSlotI_length, loadSlotI_length]
    exact pc_congr _ (by simp only [List.length_cons, List.length_nil]; omega)

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
      exact single_op_sim s m rd rs pos (.addi T0 T0 imm) (s.rget rs + imm.signExtend 64)
        hinv hpc hem hrs hrd
        (by have := slotOff_add8_le_userOff fd rs hrs; omega)
        (by have := slotOff_add8_le_userOff fd rd hrd; omega)
        hnw hseg hblob hbd (fun m' hd hT0 => by rw [step_addi m' T0 T0 imm hd, hT0])
    case slli rd rs sh =>
      rw [LowIR.Prog.exec_slli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      simp only [maxRegS] at hreg
      have hrs : rs ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hreg
      have hrd : rd ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      exact single_op_sim s m rd rs pos (.slli T0 T0 sh) (s.rget rs <<< sh)
        hinv hpc hem hrs hrd
        (by have := slotOff_add8_le_userOff fd rs hrs; omega)
        (by have := slotOff_add8_le_userOff fd rd hrd; omega)
        hnw hseg hblob hbd (fun m' hd hT0 => by rw [step_slli m' T0 T0 sh hd, hT0])
    case srli rd rs sh =>
      rw [LowIR.Prog.exec_srli, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      simp only [maxRegS] at hreg
      have hrs : rs ≤ maxRegF fd := Nat.le_trans (Nat.le_max_right _ _) hreg
      have hrd : rd ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      exact single_op_sim s m rd rs pos (.srli T0 T0 sh) (s.rget rs >>> sh)
        hinv hpc hem hrs hrd
        (by have := slotOff_add8_le_userOff fd rs hrs; omega)
        (by have := slotOff_add8_le_userOff fd rd hrd; omega)
        hnw hseg hblob hbd (fun m' hd hT0 => by rw [step_srli m' T0 T0 sh hd, hT0])
    case add rd r1 r2 =>
      rw [LowIR.Prog.exec_add, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      simp only [maxRegS] at hreg
      have hrd : rd ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      have hr1 : r1 ≤ maxRegF fd :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hreg
      have hr2 : r2 ≤ maxRegF fd :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hreg
      exact two_op_sim s m rd r1 r2 pos (.add T0 T0 T1) (s.rget r1 + s.rget r2)
        hinv hpc hem hr1 hr2 hrd
        (by have := slotOff_add8_le_userOff fd r1 hr1; omega)
        (by have := slotOff_add8_le_userOff fd r2 hr2; omega)
        (by have := slotOff_add8_le_userOff fd rd hrd; omega)
        hnw hseg hblob hbd (fun m' hd hT0 hT1 => by rw [step_add m' T0 T0 T1 hd, hT0, hT1])
    case sub rd r1 r2 =>
      rw [LowIR.Prog.exec_sub, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      simp only [maxRegS] at hreg
      have hrd : rd ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      have hr1 : r1 ≤ maxRegF fd :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hreg
      have hr2 : r2 ≤ maxRegF fd :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hreg
      exact two_op_sim s m rd r1 r2 pos (.sub T0 T0 T1) (s.rget r1 - s.rget r2)
        hinv hpc hem hr1 hr2 hrd
        (by have := slotOff_add8_le_userOff fd r1 hr1; omega)
        (by have := slotOff_add8_le_userOff fd r2 hr2; omega)
        (by have := slotOff_add8_le_userOff fd rd hrd; omega)
        hnw hseg hblob hbd (fun m' hd hT0 hT1 => by rw [step_sub m' T0 T0 T1 hd, hT0, hT1])
    case orr rd r1 r2 =>
      rw [LowIR.Prog.exec_orr, Option.some.injEq, Prod.mk.injEq] at hexec
      obtain ⟨rfl, -⟩ := hexec
      simp only [maxRegS] at hreg
      have hrd : rd ≤ maxRegF fd := Nat.le_trans (Nat.le_max_left _ _) hreg
      have hr1 : r1 ≤ maxRegF fd :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hreg
      have hr2 : r2 ≤ maxRegF fd :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hreg
      exact two_op_sim s m rd r1 r2 pos (.or T0 T0 T1) (s.rget r1 ||| s.rget r2)
        hinv hpc hem hr1 hr2 hrd
        (by have := slotOff_add8_le_userOff fd r1 hr1; omega)
        (by have := slotOff_add8_le_userOff fd r2 hr2; omega)
        (by have := slotOff_add8_le_userOff fd rd hrd; omega)
        hnw hseg hblob hbd (fun m' hd hT0 hT1 => by rw [step_or m' T0 T0 T1 hd, hT0, hT1])
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
