/-
  General refinement for hex1: for ALL inputs, executing `core1` computes
  `coreSpec1`. Mirrors Hex0/Refine.lean's architecture, extended to core1's
  three loops (label-table init / pass 1 scan / pass 2 emit) and the label
  table region. See REFINE1.md for the offset map and plan.

  STATUS: IN PROGRESS.
-/
import Hex1.DecodeFacts
import Hex1.Harness
import Hex1.Spec
import Hex1.Grammar
open Rv64i

namespace Hex1.Refine
open Hex0.Refine (addr_ofNat_succ ult_ofNat ofNat_ne getD_drop setWidth8_64
  rset_rget storeByte_mem li_block_frame runFuel_halt runFuel_one runFuel_add
  rset_zero slt_ofNat nibble_addi nibble_lt nibble_none_range nibble_some_range
  skipComment_cons_nl skipComment_cons_ne combine_nibbles
  loadBytes_frame loadBytes_get)

/-! ## Reusable `li K; branch` blocks (ports of Hex0.Refine's, under
    `CodeLoaded1`). Each runs 2 steps, resolving the branch. -/

set_option maxRecDepth 8000 in
/-- `li t3,K; beq t2,t3` with `t2 = c ≠ K`: NOT taken; pc += 8, clobbers t3. -/
theorem li_beq_ne (s : State) (off K c : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbeq : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.beq 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hne : (BitVec.ofNat 64 c : Word) ≠ BitVec.ofNat 64 K)
    (ho2 : off + 4 + 3 < Image1.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 4 + 3 < 724 := hcl ▸ ho2
  have ho1 : off + 3 < Image1.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have e8 : s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) := by
    rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
  have hu2 : step s1 = s1.setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
    rw [step_beq s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbeq, h7s1, h28s1, if_neg hne, e8]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 8000 in
/-- `li t3,K; beq t2,t3` with `t2 = c = K`: TAKEN, branching to `target`. -/
theorem li_beq_eq (s : State) (off K c : Nat) (imm : BitVec 13) (target : Word)
    (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbeq : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.beq 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (heq : (BitVec.ofNat 64 c : Word) = BitVec.ofNat 64 K)
    (htgt : BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) + imm.signExtend 64 = target)
    (ho2 : off + 4 + 3 < Image1.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc target := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 4 + 3 < 724 := hcl ▸ ho2
  have ho1 : off + 3 < Image1.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hu2 : step s1 = s1.setPc target := by
    rw [step_beq s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbeq, h7s1, h28s1,
        if_pos heq, hpc1, htgt]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 8000 in
/-- `li t3,K; blt t2,t3` with `t2 = c`, `¬(c < K)`: NOT taken; pc += 8. -/
theorem li_blt_nt (s : State) (off K c : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hblt : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.blt 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hge : ¬ c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (ho2 : off + 4 + 3 < Image1.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 4 + 3 < 724 := hcl ▸ ho2
  have ho1 : off + 3 < Image1.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have e8 : s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) := by
    rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
  have hslt : (BitVec.ofNat 64 c).slt (BitVec.ofNat 64 K) = false := by
    rw [slt_ofNat c K hc63 hK63]; simp [hge]
  have hu2 : step s1 = s1.setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
    rw [step_blt s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hblt, h7s1, h28s1, hslt]
    simp only [Bool.false_eq_true, if_false]
    rw [e8]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 8000 in
/-- `li t3,K; blt t2,t3` with `t2 = c < K`: TAKEN, branching to `target`. -/
theorem li_blt_t (s : State) (off K c : Nat) (imm : BitVec 13) (target : Word)
    (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hblt : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.blt 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hlt : c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (htgt : BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) + imm.signExtend 64 = target)
    (ho2 : off + 4 + 3 < Image1.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc target := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 4 + 3 < 724 := hcl ▸ ho2
  have ho1 : off + 3 < Image1.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hslt : (BitVec.ofNat 64 c).slt (BitVec.ofNat 64 K) = true := by
    rw [slt_ofNat c K hc63 hK63]; simp [hlt]
  have hu2 : step s1 = s1.setPc target := by
    rw [step_blt s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hblt, h7s1, h28s1, hslt]
    simp only [if_true]
    rw [hpc1, htgt]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 8000 in
/-- `li t3,K; bge t2,t3` with `t2 = c < K`: NOT taken; pc += 8. -/
theorem li_bge_nt (s : State) (off K c : Nat) (imm : BitVec 13) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbge : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.bge 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hlt : c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (ho2 : off + 4 + 3 < Image1.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 4 + 3 < 724 := hcl ▸ ho2
  have ho1 : off + 3 < Image1.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have e8 : s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) := by
    rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1
  have hslt : (BitVec.ofNat 64 c).slt (BitVec.ofNat 64 K) = true := by
    rw [slt_ofNat c K hc63 hK63]; simp [hlt]
  have hu2 : step s1 = s1.setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
    rw [step_bge s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbge, h7s1, h28s1, hslt]
    simp only [if_true]
    rw [e8]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

set_option maxRecDepth 8000 in
/-- `li t3,K; bge t2,t3` with `t2 = c`, `¬(c < K)`: TAKEN, to `target`. -/
theorem li_bge_t (s : State) (off K c : Nat) (imm : BitVec 13) (target : Word)
    (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h7 : s.rget 7 = BitVec.ofNat 64 c)
    (hli : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 K))
    (hbge : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.bge 7 28 imm)
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (hge : ¬ c < K) (hc63 : c < 2 ^ 63) (hK63 : K < 2 ^ 63)
    (htgt : BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) + imm.signExtend 64 = target)
    (ho2 : off + 4 + 3 < Image1.coreBytes.length) :
    runFuel 0 2 s = (s.rset 28 (BitVec.ofNat 64 K)).setPc target := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 4 + 3 < 724 := hcl ▸ ho2
  have ho1 : off + 3 < Image1.coreBytes.length := by omega
  have e4 : s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := by
    rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 28 0 (BitVec.ofNat 12 K) hcode ho1 hpc hli,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp, e4]
  let s1 := (s.rset 28 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := by intro i hi; rw [hs1]; simp [hcode i hi]
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have h7s1 : s1.rget 7 = BitVec.ofNat 64 c := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat)≠28)]
    exact h7
  have h28s1 : s1.rget 28 = BitVec.ofNat 64 K := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hslt : (BitVec.ofNat 64 c).slt (BitVec.ofNat 64 K) = false := by
    rw [slt_ofNat c K hc63 hK63]; simp [hge]
  have hu2 : step s1 = s1.setPc target := by
    rw [step_bge s1 (off+4) 7 28 imm hc1 (by omega) hpc1 hbge, h7s1, h28s1, hslt]
    simp only [Bool.false_eq_true, if_false]
    rw [hpc1, htgt]
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  show runFuel 0 2 s = s1.setPc _
  simp only [runFuel]; rw [hu1, hu2, if_neg hp0, if_neg hp1]

/-! ## Well-formedness: the four regions, in address order
    code [coreAddr, +724) < input [inputAddr, +len) ≤ out [outAddr, +cap)
    ≤ lbl [lblAddr, +2048), with everything below 2^63 (signed compares on
    table addresses; label positions sign-tested in slots). -/

structure WellFormed1 (inp : List Nat) (cap : Nat) : Prop where
  in_fits   : Image1.inputAddr + inp.length ≤ Image1.outAddr
  out_fits  : Image1.outAddr + cap ≤ Image1.lblAddr
  lbl_fits  : Image1.lblAddr + 2048 < 2 ^ 63
  bytes_ok  : ∀ b ∈ inp, b < 256

/-- `cap` is below `2^63` (the out region sits below the lbl region). -/
theorem WellFormed1.cap63 {inp : List Nat} {cap : Nat} (h : WellFormed1 inp cap) :
    cap < 2 ^ 63 := by
  have h1 := h.out_fits; have h2 := h.lbl_fits
  simp only [Image1.outAddr, Image1.lblAddr] at h1 h2 ⊢; omega

/-! ## The label table encoding. -/

/-- How a label slot is stored: undefined ↦ all-ones (-1), defined ↦ the
    position (which is `< 2^63`, so the sign distinguishes them). -/
def encodeSlot : Option Nat → Word
  | none => BitVec.allOnes 64
  | some p => BitVec.ofNat 64 p

/-- The table region holds `lab`, slot `c` at `lblAddr + 8c`, little-endian. -/
def TableLoaded (s : State) (lab : Labels) : Prop :=
  ∀ c, c < 256 → ∀ k, k < 8 →
    s.mem (BitVec.ofNat 64 (Image1.lblAddr + 8 * c + k))
      = ((encodeSlot (lab c)) >>> (8 * k)).setWidth 8

/-- The sign test `bge slot,x0` distinguishes defined from undefined:
    an undefined slot is negative. -/
theorem encodeSlot_none_neg : (encodeSlot none).slt 0 = true := by decide

/-- A defined slot (position < 2^63) is non-negative. -/
theorem encodeSlot_some_nonneg (p : Nat) (hp : p < 2 ^ 63) :
    (encodeSlot (some p)).slt 0 = false := by
  show (BitVec.ofNat 64 p).slt (BitVec.ofNat 64 0) = false
  rw [slt_ofNat p 0 hp (by omega)]
  simp

/-! ## Slot addressing and table access. -/

/-- `slli t3,t2,3` on a label byte: shifting is multiplication by 8. -/
theorem shl3_ofNat (c : Nat) (hc : c < 256) :
    (BitVec.ofNat 64 c) <<< 3 = BitVec.ofNat 64 (8 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.shiftLeft_eq]
  omega

/-- The machine's slot address `(c <<< 3) + a4` is `lblAddr + 8c`. -/
theorem slot_addr (c : Nat) (hc : c < 256) :
    (BitVec.ofNat 64 c) <<< 3 + BitVec.ofNat 64 Image1.lblAddr
      = BitVec.ofNat 64 (Image1.lblAddr + 8 * c) := by
  rw [shl3_ofNat c hc, addr_ofNat_succ]
  congr 1
  omega

/-- Under `TableLoaded`, `loadWord` at slot `c` returns the encoded slot. -/
theorem loadWord_slot (s : State) (lab : Labels) (c : Nat) (hc : c < 256)
    (htbl : TableLoaded s lab) :
    s.loadWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * c)) = encodeSlot (lab c) := by
  unfold State.loadWord
  have addr : ∀ k : Nat, BitVec.ofNat 64 (Image1.lblAddr + 8 * c) + BitVec.ofNat 64 k
      = BitVec.ofNat 64 (Image1.lblAddr + 8 * c + k) := fun k => addr_ofNat_succ _ _
  have rd : ∀ k : Nat, k < 8 →
      s.mem (BitVec.ofNat 64 (Image1.lblAddr + 8 * c) + BitVec.ofNat 64 k)
        = ((encodeSlot (lab c)) >>> (8 * k)).setWidth 8 := by
    intro k hk; rw [addr k]; exact htbl c hc k hk
  have rd0 : s.mem (BitVec.ofNat 64 (Image1.lblAddr + 8 * c))
      = (encodeSlot (lab c)).setWidth 8 := by
    have h := htbl c hc 0 (by omega)
    simpa using h
  have rd1 := rd 1 (by omega)
  have rd2 := rd 2 (by omega); have rd3 := rd 3 (by omega)
  have rd4 := rd 4 (by omega); have rd5 := rd 5 (by omega)
  have rd6 := rd 6 (by omega); have rd7 := rd 7 (by omega)
  simp only [show (8 * 1 : Nat) = 8 from rfl,
    show (8 * 2 : Nat) = 16 from rfl, show (8 * 3 : Nat) = 24 from rfl,
    show (8 * 4 : Nat) = 32 from rfl, show (8 * 5 : Nat) = 40 from rfl,
    show (8 * 6 : Nat) = 48 from rfl, show (8 * 7 : Nat) = 56 from rfl,
    show BitVec.ofNat 64 1 = (1 : Word) from rfl,
    show BitVec.ofNat 64 2 = (2 : Word) from rfl, show BitVec.ofNat 64 3 = (3 : Word) from rfl,
    show BitVec.ofNat 64 4 = (4 : Word) from rfl, show BitVec.ofNat 64 5 = (5 : Word) from rfl,
    show BitVec.ofNat 64 6 = (6 : Word) from rfl, show BitVec.ofNat 64 7 = (7 : Word) from rfl]
    at rd1 rd2 rd3 rd4 rd5 rd6 rd7
  rw [rd0, rd1, rd2, rd3, rd4, rd5, rd6, rd7]
  exact assemble_bytes (encodeSlot (lab c))

/-- `sd` at slot `c` updates the table to `setLabel lab c p`
    (writing `encodeSlot (some p) = ofNat p`). -/
theorem storeWord_slot (s : State) (lab : Labels) (c p : Nat) (hc : c < 256)
    (htbl : TableLoaded s lab) (hlbl : Image1.lblAddr + 2048 < 2 ^ 63) :
    TableLoaded (s.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * c)) (BitVec.ofNat 64 p))
      (setLabel lab c p) := by
  intro c' hc' k hk
  by_cases hcc : c' = c
  · -- the written slot: per-byte storeWord_get
    subst hcc
    have he : encodeSlot (setLabel lab c' p c') = BitVec.ofNat 64 p := by
      unfold setLabel encodeSlot; simp
    rw [he]
    have addr : BitVec.ofNat 64 (Image1.lblAddr + 8 * c' + k)
        = BitVec.ofNat 64 (Image1.lblAddr + 8 * c') + BitVec.ofNat 64 k :=
      (addr_ofNat_succ _ _).symm
    rw [addr]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      h | h | h | h | h | h | h | h <;> subst h
    · simpa using storeWord_get0 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get1 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get2 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get3 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get4 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get5 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get6 s _ (BitVec.ofNat 64 p)
    · simpa using storeWord_get7 s _ (BitVec.ofNat 64 p)
  · -- another slot: frame + unchanged encoding
    have he : encodeSlot (setLabel lab c p c') = encodeSlot (lab c') := by
      unfold setLabel; rw [if_neg hcc]
    rw [he]
    rw [storeWord_frame s _ _ _ (by
      intro k2 hk2
      rw [addr_ofNat_succ]
      refine ofNat_ne _ _ ?_ ?_ ?_
      · simp only [Image1.lblAddr] at hlbl ⊢; omega
      · simp only [Image1.lblAddr] at hlbl ⊢; omega
      · omega)]
    exact htbl c' hc' k hk

/-- A byte store elsewhere (the output region in pass 2) leaves the table
    intact. -/
theorem tableLoaded_storeByte (s : State) (lab : Labels) (a : Word) (b : Byte)
    (htbl : TableLoaded s lab)
    (hdisj : ∀ c k, c < 256 → k < 8 → a ≠ BitVec.ofNat 64 (Image1.lblAddr + 8 * c + k)) :
    TableLoaded (s.storeByte a b) lab := by
  intro c hc k hk
  rw [storeByte_mem]
  simp only []
  rw [if_neg (fun he => hdisj c k hc hk he.symm)]
  exact htbl c hc k hk

/-! ## Region predicates and their preservation lemmas. -/

/-- The input bytes sit in the input region. -/
def InputLoaded (s : State) (inp : List Nat) : Prop :=
  ∀ i, i < inp.length →
    s.mem (BitVec.ofNat 64 (Image1.inputAddr + i)) = BitVec.ofNat 8 (inp.getD i 0)

/-- `setPc` does not touch memory: all region predicates pass through. -/
theorem codeLoaded1_setPc (s : State) (p : Word) (h : CodeLoaded1 s) :
    CodeLoaded1 (s.setPc p) := h

theorem inputLoaded_setPc (s : State) (p : Word) (inp : List Nat)
    (h : InputLoaded s inp) : InputLoaded (s.setPc p) inp := h

theorem codeLoaded1_rset (s : State) (rd : Nat) (v : Word) (h : CodeLoaded1 s) :
    CodeLoaded1 (s.rset rd v) := by
  intro i hi
  rw [Hex0.Refine.rset_mem]
  exact h i hi

theorem inputLoaded_rset (s : State) (rd : Nat) (v : Word) (inp : List Nat)
    (h : InputLoaded s inp) : InputLoaded (s.rset rd v) inp := by
  intro i hi
  rw [Hex0.Refine.rset_mem]
  exact h i hi

theorem codeLoaded1_storeWord (s : State) (a v : Word)
    (hcode : CodeLoaded1 s)
    (hdisj : ∀ i k : Nat, i < Image1.coreBytes.length → k < 8 →
      BitVec.ofNat 64 (Image1.coreAddr + i) ≠ a + BitVec.ofNat 64 k) :
    CodeLoaded1 (s.storeWord a v) := by
  intro i hi
  rw [storeWord_frame s a v _ (fun k hk => hdisj i k hi hk)]
  exact hcode i hi

theorem inputLoaded_storeWord (s : State) (a v : Word) (inp : List Nat)
    (hin : InputLoaded s inp)
    (hdisj : ∀ i k : Nat, i < inp.length → k < 8 →
      BitVec.ofNat 64 (Image1.inputAddr + i) ≠ a + BitVec.ofNat 64 k) :
    InputLoaded (s.storeWord a v) inp := by
  intro i hi
  rw [storeWord_frame s a v _ (fun k hk => hdisj i k hi hk)]
  exact hin i hi

theorem codeLoaded1_storeByte (s : State) (a : Word) (b : Byte)
    (hcode : CodeLoaded1 s)
    (hdisj : ∀ i : Nat, i < Image1.coreBytes.length →
      BitVec.ofNat 64 (Image1.coreAddr + i) ≠ a) :
    CodeLoaded1 (s.storeByte a b) := by
  intro i hi
  rw [storeByte_mem]
  simp only []
  rw [if_neg (hdisj i hi)]
  exact hcode i hi

theorem inputLoaded_storeByte (s : State) (a : Word) (b : Byte) (inp : List Nat)
    (hin : InputLoaded s inp)
    (hdisj : ∀ i : Nat, i < inp.length →
      BitVec.ofNat 64 (Image1.inputAddr + i) ≠ a) :
    InputLoaded (s.storeByte a b) inp := by
  intro i hi
  rw [storeByte_mem]
  simp only []
  rw [if_neg (hdisj i hi)]
  exact hin i hi

/-! ## The init loop: 256 iterations of `sd; addi; blt` filling the table
    with -1. Offsets: entry 0..12, loop body 16/20/24, exit -> 28. -/

/-- Invariant at the init-loop head (offset 16), after `j` slots written. -/
structure InitInv (inp : List Nat) (cap : Nat) (s : State) (j : Nat) : Prop where
  pc    : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 16)
  code  : CodeLoaded1 s
  a0    : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr
  a1    : s.rget 11 = BitVec.ofNat 64 inp.length
  a2    : s.rget 12 = BitVec.ofNat 64 Image1.outAddr
  a3    : s.rget 13 = BitVec.ofNat 64 cap
  a4    : s.rget 14 = BitVec.ofNat 64 Image1.lblAddr
  ra0   : s.rget 1 = 0
  t3    : s.rget 28 = BitVec.ofNat 64 (Image1.lblAddr + 8 * j)
  t4    : s.rget 29 = BitVec.ofNat 64 (Image1.lblAddr + 2048)
  t5    : s.rget 30 = BitVec.allOnes 64
  in_mem : ∀ i, i < inp.length →
      s.mem (BitVec.ofNat 64 (Image1.inputAddr + i)) = BitVec.ofNat 8 (inp.getD i 0)
  tbl   : ∀ b, b < 8 * j → s.mem (BitVec.ofNat 64 (Image1.lblAddr + b)) = 0xFF#8

/-- State shape on arrival at pass 1 (offset 28): table fully initialized. -/
structure Pass1Entry (inp : List Nat) (cap : Nat) (s : State) : Prop where
  pc    : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 28)
  code  : CodeLoaded1 s
  a0    : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr
  a1    : s.rget 11 = BitVec.ofNat 64 inp.length
  a2    : s.rget 12 = BitVec.ofNat 64 Image1.outAddr
  a3    : s.rget 13 = BitVec.ofNat 64 cap
  a4    : s.rget 14 = BitVec.ofNat 64 Image1.lblAddr
  ra0   : s.rget 1 = 0
  in_mem : ∀ i, i < inp.length →
      s.mem (BitVec.ofNat 64 (Image1.inputAddr + i)) = BitVec.ofNat 8 (inp.getD i 0)
  tbl   : TableLoaded s noLabels

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- One init iteration (offsets 16,20,24): writes slot `j`, bumps the
    pointer, loops back while `j+1 < 256` (else falls through to 28). -/
theorem init_iter (inp : List Nat) (cap : Nat) (s : State) (j : Nat)
    (inv : InitInv inp cap s j) (hj : j < 256)
    (hwf : WellFormed1 inp cap) :
    ∃ s', runFuel 0 3 s = s' ∧
      (if j + 1 < 256 then InitInv inp cap s' (j + 1)
       else Pass1Entry inp cap s') := by
  have hlbl := hwf.lbl_fits
  have hin := hwf.in_fits
  have hout := hwf.out_fits
  -- step 1 (off 16): sd t5,0(t3)
  have e0 : s.rget 28 + (0#12).signExtend 64 = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) := by
    rw [inv.t3, show ((0#12).signExtend 64) = 0#64 from by decide, BitVec.add_zero]
  have hu1 : step s = (s.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * j))
      (BitVec.allOnes 64)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 20)) := by
    rw [step_sd s 16 28 30 (0#12) inv.code (by rw [coreBytes_len]; omega) inv.pc dec_16,
        e0, inv.t5]
    congr 1
    rw [inv.pc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]
  let s1 : State := (s.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * j))
      (BitVec.allOnes 64)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 20))
  have hs1 : s1 = (s.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * j))
      (BitVec.allOnes 64)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 20)) := rfl
  try rw [← hs1] at hu1
  -- memory of s1: table prefix extended to 8(j+1); code/input intact
  have htbl1 : ∀ b, b < 8 * (j + 1) →
      s1.mem (BitVec.ofNat 64 (Image1.lblAddr + b)) = 0xFF#8 := by
    intro b hb
    show (s.storeWord _ _).mem _ = _
    by_cases hbj : b < 8 * j
    · rw [storeWord_frame s _ _ _ (by
        intro k hk
        rw [addr_ofNat_succ]
        refine ofNat_ne _ _ ?_ ?_ ?_
        · simp only [Image1.lblAddr] at hlbl ⊢; omega
        · simp only [Image1.lblAddr] at hlbl ⊢; omega
        · omega)]
      exact inv.tbl b hbj
    · -- b ∈ [8j, 8j+8): the freshly stored slot
      rcases (by omega : b = 8 * j ∨ b = 8 * j + 1 ∨ b = 8 * j + 2 ∨ b = 8 * j + 3 ∨
          b = 8 * j + 4 ∨ b = 8 * j + 5 ∨ b = 8 * j + 6 ∨ b = 8 * j + 7) with
        h | h | h | h | h | h | h | h <;> subst h
      · rw [show Image1.lblAddr + 8 * j = Image1.lblAddr + 8 * j from rfl, storeWord_get0]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 1))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 1 from by
              rw [show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get1]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 2))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 2 from by
              rw [show (2:Word) = BitVec.ofNat 64 2 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get2]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 3))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 3 from by
              rw [show (3:Word) = BitVec.ofNat 64 3 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get3]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 4))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 4 from by
              rw [show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get4]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 5))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 5 from by
              rw [show (5:Word) = BitVec.ofNat 64 5 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get5]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 6))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 6 from by
              rw [show (6:Word) = BitVec.ofNat 64 6 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get6]
        decide
      · rw [show BitVec.ofNat 64 (Image1.lblAddr + (8 * j + 7))
            = BitVec.ofNat 64 (Image1.lblAddr + 8 * j) + 7 from by
              rw [show (7:Word) = BitVec.ofNat 64 7 from rfl, addr_ofNat_succ]; congr 1,
            storeWord_get7]
        decide
  have hcode1 : CodeLoaded1 s1 :=
    codeLoaded1_setPc _ _ (codeLoaded1_storeWord s _ _ inv.code (by
      intro i k hi hk
      rw [coreBytes_len] at hi
      rw [addr_ofNat_succ]
      refine ofNat_ne _ _ ?_ ?_ ?_
      · simp only [Image1.coreAddr, Image1.lblAddr] at hlbl ⊢; omega
      · simp only [Image1.lblAddr] at hlbl ⊢; omega
      · simp only [Image1.coreAddr, Image1.lblAddr]; omega))
  have hin1 : InputLoaded s1 inp :=
    inputLoaded_setPc _ _ inp (inputLoaded_storeWord s _ _ inp inv.in_mem (by
      intro i k hi hk
      rw [addr_ofNat_succ]
      refine ofNat_ne _ _ ?_ ?_ ?_
      · simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hlbl hin hout ⊢
        omega
      · simp only [Image1.lblAddr] at hlbl ⊢; omega
      · simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hlbl hin hout ⊢
        omega))
  have hr1 : ∀ i : Nat, s1.rget i = s.rget i := fun i => rfl
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 20) := rfl
  -- step 2 (off 20): addi t3,t3,8
  have hu2 : step s1 = (s1.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1)))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 24)) := by
    have harg : s1.rget 28 + (8#12).signExtend 64
        = BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1)) := by
      rw [hr1 28, inv.t3, show ((8#12).signExtend 64) = BitVec.ofNat 64 8 from by decide,
          addr_ofNat_succ]
      congr 1 <;> omega
    have hpcn : s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 24) := by
      rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]
    rw [step_addi s1 20 28 28 (8#12) hcode1 (by rw [coreBytes_len]; omega) hpc1 dec_20,
        harg, hpcn]
  let s2 : State := (s1.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1)))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 24))
  have hs2 : s2 = (s1.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1)))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 24)) := rfl
  try rw [← hs2] at hu2
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 24) := rfl
  have hcode2 : CodeLoaded1 s2 := fun i hi => hcode1 i hi
  have hmem2 : s2.mem = s1.mem := rfl
  have hr2 : ∀ i : Nat, i ≠ 28 → s2.rget i = s1.rget i := by
    intro i hi
    exact li_block_frame s1 _ _ i hi
  have hr2_28 : s2.rget 28 = BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1)) := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  -- step 3 (off 24): blt t3,t4, back to 16 (taken iff j+1 < 256)
  have hb63 : Image1.lblAddr + 8 * (j + 1) < 2 ^ 63 := by
    simp only [Image1.lblAddr] at hlbl ⊢; omega
  have hr29_2 : s2.rget 29 = BitVec.ofNat 64 (Image1.lblAddr + 2048) := by
    rw [hr2 29 (by decide), hr1 29, inv.t4]
  have hp0 : s.pc ≠ 0 := by
    rw [inv.pc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by
    rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  rcases Nat.lt_or_ge (j + 1) 256 with h | h
  · -- branch TAKEN: back to offset 16, invariant advances
    have hslt : (BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1))).slt
        (BitVec.ofNat 64 (Image1.lblAddr + 2048)) = true := by
      rw [slt_ofNat _ _ hb63 hlbl]
      simp only [decide_eq_true_eq]
      omega
    have hu3 : step s2 = s2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 16)) := by
      rw [step_blt s2 24 28 29 (BitVec.ofNat 13 8184) hcode2 (by rw [coreBytes_len]; omega)
          hpc2 dec_24, hr2_28, hr29_2, hslt]
      simp only [if_true]
      rw [show s2.pc + (BitVec.ofNat 13 8184).signExtend 64
          = BitVec.ofNat 64 (Image1.coreAddr + 16) from by rw [hpc2]; decide]
    refine ⟨s2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 16)), ?_, ?_⟩
    · simp only [runFuel]
      rw [hu1, hu2, hu3, if_neg hp0, if_neg hp1, if_neg hp2]
    rw [if_pos h]
    exact {
      pc := rfl
      code := fun i hi => hcode2 i hi
      a0 := by rw [Hex0.Refine.setPc_rget, hr2 10 (by decide), hr1 10]; exact inv.a0
      a1 := by rw [Hex0.Refine.setPc_rget, hr2 11 (by decide), hr1 11]; exact inv.a1
      a2 := by rw [Hex0.Refine.setPc_rget, hr2 12 (by decide), hr1 12]; exact inv.a2
      a3 := by rw [Hex0.Refine.setPc_rget, hr2 13 (by decide), hr1 13]; exact inv.a3
      a4 := by rw [Hex0.Refine.setPc_rget, hr2 14 (by decide), hr1 14]; exact inv.a4
      ra0 := by rw [Hex0.Refine.setPc_rget, hr2 1 (by decide), hr1 1]; exact inv.ra0
      t3 := by rw [Hex0.Refine.setPc_rget]; exact hr2_28
      t4 := by rw [Hex0.Refine.setPc_rget]; exact hr29_2
      t5 := by rw [Hex0.Refine.setPc_rget, hr2 30 (by decide), hr1 30]; exact inv.t5
      in_mem := fun i hi => hin1 i hi
      tbl := fun b hb => htbl1 b hb }
  · -- branch NOT taken: fall through to offset 28 (pass 1 entry)
    have hslt : (BitVec.ofNat 64 (Image1.lblAddr + 8 * (j + 1))).slt
        (BitVec.ofNat 64 (Image1.lblAddr + 2048)) = false := by
      rw [slt_ofNat _ _ hb63 hlbl]
      simp only [decide_eq_false_iff_not]
      omega
    have hu3 : step s2 = s2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 28)) := by
      rw [step_blt s2 24 28 29 (BitVec.ofNat 13 8184) hcode2 (by rw [coreBytes_len]; omega)
          hpc2 dec_24, hr2_28, hr29_2, hslt]
      simp only [Bool.false_eq_true, if_false]
      rw [show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 28) from by rw [hpc2]; decide]
    refine ⟨s2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 28)), ?_, ?_⟩
    · simp only [runFuel]
      rw [hu1, hu2, hu3, if_neg hp0, if_neg hp1, if_neg hp2]
    rw [if_neg (by omega)]
    exact {
      pc := rfl
      code := fun i hi => hcode2 i hi
      a0 := by rw [Hex0.Refine.setPc_rget, hr2 10 (by decide), hr1 10]; exact inv.a0
      a1 := by rw [Hex0.Refine.setPc_rget, hr2 11 (by decide), hr1 11]; exact inv.a1
      a2 := by rw [Hex0.Refine.setPc_rget, hr2 12 (by decide), hr1 12]; exact inv.a2
      a3 := by rw [Hex0.Refine.setPc_rget, hr2 13 (by decide), hr1 13]; exact inv.a3
      a4 := by rw [Hex0.Refine.setPc_rget, hr2 14 (by decide), hr1 14]; exact inv.a4
      ra0 := by rw [Hex0.Refine.setPc_rget, hr2 1 (by decide), hr1 1]; exact inv.ra0
      in_mem := fun i hi => hin1 i hi
      tbl := by
        intro c hc k hk
        show s2.mem _ = _
        rw [hmem2]
        have heq : Image1.lblAddr + 8 * c + k = Image1.lblAddr + (8 * c + k) := by omega
        rw [heq, htbl1 (8 * c + k) (by omega)]
        show _ = ((encodeSlot none) >>> (8 * k)).setWidth 8
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
          hh | hh | hh | hh | hh | hh | hh | hh <;> subst hh <;> decide }

/-- The init loop runs to completion: from `InitInv j` (j < 256), after
    `3 * (256 - j)` steps the machine is at pass 1 with the table cleared. -/
theorem init_loop (inp : List Nat) (cap : Nat) :
    ∀ (n : Nat) (s : State) (j : Nat), n = 256 - j → j < 256 →
    InitInv inp cap s j → WellFormed1 inp cap →
    ∃ s', runFuel 0 (3 * n) s = s' ∧ Pass1Entry inp cap s' := by
  intro n
  induction n with
  | zero => intro s j hn hj _ _; omega
  | succ n ih =>
    intro s j hn hj inv hwf
    obtain ⟨s', hrun, hpost⟩ := init_iter inp cap s j inv hj hwf
    rcases Nat.lt_or_ge (j + 1) 256 with h | h
    · rw [if_pos h] at hpost
      obtain ⟨s'', hrun2, hp2⟩ := ih s' (j + 1) (by omega) h hpost hwf
      refine ⟨s'', ?_, hp2⟩
      rw [show 3 * (n + 1) = 3 + 3 * n from by omega, runFuel_add, hrun, hrun2]
    · rw [if_neg (by omega)] at hpost
      have hn0 : n = 0 := by omega
      subst hn0
      refine ⟨s', ?_, hpost⟩
      rw [show 3 * 1 = 3 from rfl, hrun]

/-! ## Prologue: from `initOn` through the entry block into the init loop. -/

set_option maxRecDepth 8000 in
/-- `initOn` loads the code (the input layer does not shadow it). -/
theorem code_initOn1 (inp : List Nat) (cap : Nat) (hwf : WellFormed1 inp cap) :
    CodeLoaded1 (Harness1.initOn inp cap) := by
  intro i hi
  have hlen : Image1.coreBytes.length = 724 := coreBytes_len
  show (Rv64i.Harness.loadBytes Image1.inputAddr inp
        (Rv64i.Harness.loadBytes Image1.coreAddr Image1.coreBytes (fun _ => 0)))
        (BitVec.ofNat 64 (Image1.coreAddr + i)) = BitVec.ofNat 8 (Image1.coreBytes.getD i 0)
  rw [loadBytes_frame (BitVec.ofNat 64 (Image1.coreAddr + i)) Image1.inputAddr inp _ (by
    intro j hj
    refine ofNat_ne _ _ ?_ ?_ ?_
    · rw [hlen] at hi; simp only [Image1.coreAddr]; omega
    · have h1 := hwf.in_fits; have h2 := hwf.out_fits; have h3 := hwf.lbl_fits
      simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at h1 h2 h3 ⊢; omega
    · rw [hlen] at hi; simp only [Image1.coreAddr, Image1.inputAddr]; omega)]
  exact loadBytes_get Image1.coreAddr Image1.coreBytes _ i hi (by decide)

/-- `initOn` loads the input. -/
theorem in_initOn1 (inp : List Nat) (cap : Nat) (hwf : WellFormed1 inp cap) :
    InputLoaded (Harness1.initOn inp cap) inp := by
  intro j hj
  show (Rv64i.Harness.loadBytes Image1.inputAddr inp _) (BitVec.ofNat 64 (Image1.inputAddr + j))
      = BitVec.ofNat 8 (inp.getD j 0)
  refine loadBytes_get Image1.inputAddr inp _ j hj ?_
  have h1 := hwf.in_fits; have h2 := hwf.out_fits; have h3 := hwf.lbl_fits
  simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at h1 h2 h3 ⊢; omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The entry block (offsets 0,4,8,12): set up t3/t4/t5, landing at the init
    loop head with `InitInv 0`. -/
theorem entry_block (inp : List Nat) (cap : Nat) (hwf : WellFormed1 inp cap) :
    ∃ s', runFuel 0 4 (Harness1.initOn inp cap) = s' ∧ InitInv inp cap s' 0 := by
  have hcode := code_initOn1 inp cap hwf
  have hin := in_initOn1 inp cap hwf
  let s0 := Harness1.initOn inp cap
  have hs0 : s0 = Harness1.initOn inp cap := rfl
  have hpc0 : s0.pc = BitVec.ofNat 64 (Image1.coreAddr + 0) := by
    show BitVec.ofNat 64 Image1.coreAddr = _
    congr 1
  have hr14 : s0.rget 14 = BitVec.ofNat 64 Image1.lblAddr := rfl
  -- step 1 (off 0): addi t3,a4,0
  have hu1 : step s0 = (s0.rset 28 (BitVec.ofNat 64 Image1.lblAddr)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 4)) := by
    rw [step_addi s0 0 28 14 (BitVec.ofNat 12 0) hcode (by rw [coreBytes_len]; omega) hpc0 dec_0,
        show s0.rget 14 + (BitVec.ofNat 12 0).signExtend 64 = BitVec.ofNat 64 Image1.lblAddr from by
          rw [hr14, show ((BitVec.ofNat 12 0).signExtend 64) = 0#64 from by decide,
              BitVec.add_zero],
        show s0.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 4) from by
          rw [hpc0, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s1 := (s0.rset 28 (BitVec.ofNat 64 Image1.lblAddr)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 4))
  have hs1 : s1 = (s0.rset 28 (BitVec.ofNat 64 Image1.lblAddr)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 4)) := rfl
  try rw [← hs1] at hu1
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 4) := rfl
  have hcode1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hr14_1 : s1.rget 14 = BitVec.ofNat 64 Image1.lblAddr := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (14:Nat) ≠ 28)]
    exact hr14
  -- step 2 (off 4): addi t4,a4,2047
  have hu2 : step s1 = (s1.rset 29 (BitVec.ofNat 64 (Image1.lblAddr + 2047))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 8)) := by
    rw [step_addi s1 4 29 14 (BitVec.ofNat 12 2047) hcode1 (by rw [coreBytes_len]; omega)
        hpc1 dec_4,
        show s1.rget 14 + (BitVec.ofNat 12 2047).signExtend 64
            = BitVec.ofNat 64 (Image1.lblAddr + 2047) from by
          rw [hr14_1, show ((BitVec.ofNat 12 2047).signExtend 64) = BitVec.ofNat 64 2047 from
            by decide, addr_ofNat_succ],
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 8) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s2 := (s1.rset 29 (BitVec.ofNat 64 (Image1.lblAddr + 2047))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 8))
  have hs2 : s2 = (s1.rset 29 (BitVec.ofNat 64 (Image1.lblAddr + 2047))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 8)) := rfl
  try rw [← hs2] at hu2
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 8) := rfl
  have hcode2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode1)
  have hr29_2 : s2.rget 29 = BitVec.ofNat 64 (Image1.lblAddr + 2047) := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  -- step 3 (off 8): addi t4,t4,1
  have hu3 : step s2 = (s2.rset 29 (BitVec.ofNat 64 (Image1.lblAddr + 2048))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 12)) := by
    rw [step_addi s2 8 29 29 (BitVec.ofNat 12 1) hcode2 (by rw [coreBytes_len]; omega)
        hpc2 dec_8,
        show s2.rget 29 + (BitVec.ofNat 12 1).signExtend 64
            = BitVec.ofNat 64 (Image1.lblAddr + 2048) from by
          rw [hr29_2, show ((BitVec.ofNat 12 1).signExtend 64) = BitVec.ofNat 64 1 from
            by decide, addr_ofNat_succ],
        show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 12) from by
          rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s3 := (s2.rset 29 (BitVec.ofNat 64 (Image1.lblAddr + 2048))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 12))
  have hs3 : s3 = (s2.rset 29 (BitVec.ofNat 64 (Image1.lblAddr + 2048))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 12)) := rfl
  try rw [← hs3] at hu3
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 12) := rfl
  have hcode3 : CodeLoaded1 s3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode2)
  -- step 4 (off 12): addi t5,x0,-1
  have hu4 : step s3 = (s3.rset 30 (BitVec.allOnes 64)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 16)) := by
    rw [step_addi s3 12 30 0 (BitVec.ofNat 12 4095) hcode3 (by rw [coreBytes_len]; omega)
        hpc3 dec_12,
        show s3.rget 0 + (BitVec.ofNat 12 4095).signExtend 64 = BitVec.allOnes 64 from by
          rw [Hex0.Refine.rget_zero]; decide,
        show s3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 16) from by
          rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s4 := (s3.rset 30 (BitVec.allOnes 64)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 16))
  have hs4 : s4 = (s3.rset 30 (BitVec.allOnes 64)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 16)) := rfl
  try rw [← hs4] at hu4
  -- register bookkeeping back to s0
  have frame : ∀ i : Nat, i ≠ 0 → i ≠ 28 → i ≠ 29 → i ≠ 30 → s4.rget i = s0.rget i := by
    intro i h0 h28 h29 h30
    rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h30,
        hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29,
        hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29,
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28]
  have hmem4 : s4.mem = s0.mem := by
    rw [hs4, hs3, hs2, hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
  have hp0 : s0.pc ≠ 0 := by
    rw [hpc0]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by
    rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp3 : s3.pc ≠ 0 := by
    rw [hpc3]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  refine ⟨s4, ?_, ?_⟩
  · simp only [runFuel]
    rw [hu1, hu2, hu3, hu4, if_neg hp0, if_neg hp1, if_neg hp2, if_neg hp3]
  exact {
    pc := rfl
    code := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode3)
    a0 := by rw [frame 10 (by decide) (by decide) (by decide) (by decide)]; rfl
    a1 := by rw [frame 11 (by decide) (by decide) (by decide) (by decide)]; rfl
    a2 := by rw [frame 12 (by decide) (by decide) (by decide) (by decide)]; rfl
    a3 := by rw [frame 13 (by decide) (by decide) (by decide) (by decide)]; rfl
    a4 := by rw [frame 14 (by decide) (by decide) (by decide) (by decide)]; rfl
    ra0 := by rw [frame 1 (by decide) (by decide) (by decide) (by decide)]; rfl
    t3 := by
      rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (28:Nat) ≠ 30),
          hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (28:Nat) ≠ 29),
          hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (28:Nat) ≠ 29),
          hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    t4 := by
      rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (29:Nat) ≠ 30),
          hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    t5 := by
      rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    in_mem := by
      intro i hi
      show s4.mem _ = _
      rw [hmem4]
      exact hin i hi
    tbl := by intro b hb; omega }

/-- From reset, after `4 + 3*256` steps the machine is at pass 1 with the
    table cleared (the whole pre-pass-1 phase). -/
theorem init_phase (inp : List Nat) (cap : Nat) (hwf : WellFormed1 inp cap) :
    ∃ s', runFuel 0 772 (Harness1.initOn inp cap) = s' ∧ Pass1Entry inp cap s' := by
  obtain ⟨s4, hrun4, hinv⟩ := entry_block inp cap hwf
  obtain ⟨s', hrun', hp⟩ := init_loop inp cap 256 s4 0 (by omega) (by omega) hinv hwf
  refine ⟨s', ?_, hp⟩
  rw [show (772 : Nat) = 4 + 3 * 256 from rfl, runFuel_add, hrun4, hrun']

/-! ## The result relation and the exit epilogues. -/

/-- The halted state matches `coreSpec1 inp cap`. -/
def Result1 (f : State) (inp : List Nat) (cap : Nat) : Prop :=
  f.pc = 0 ∧
  f.rget 10 = BitVec.ofNat 64 (Hex1.coreSpec1 inp cap).1 ∧
  f.rget 11 = BitVec.ofNat 64 (Hex1.coreSpec1 inp cap).2.2 ∧
  ∀ j, j < (Hex1.coreSpec1 inp cap).2.2 →
    f.mem (BitVec.ofNat 64 (Image1.outAddr + j))
      = BitVec.ofNat 8 ((Hex1.coreSpec1 inp cap).2.1.getD j 0)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Generic exit epilogue, `a1 = 0` shape: `li a0,K; li a1,0; ret`.
    3 steps to a halted state with a0=K, a1=0, memory untouched. -/
theorem exit_zero (s : State) (off K : Nat) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hra : s.rget 1 = 0)
    (hd1 : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 K))
    (hd2 : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0))
    (hd3 : Rv64i.decode (wordAt1 (off + 8)) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0))
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (ho : off + 8 + 3 < Image1.coreBytes.length) :
    ∃ f, runFuel 0 3 s = f ∧ f.pc = 0 ∧ f.rget 10 = BitVec.ofNat 64 K ∧
      f.rget 11 = 0 ∧ f.mem = s.mem := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 8 + 3 < 724 := hcl ▸ ho
  have hu1 : step s = (s.rset 10 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 10 0 (BitVec.ofNat 12 K) hcode (by omega) hpc hd1,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp,
        show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) from by
          rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]]
  let s1 := (s.rset 10 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 10 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have hcode1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hu2 : step s1 = (s1.rset 11 0).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
    rw [step_addi s1 (off + 4) 11 0 (BitVec.ofNat 12 0) hcode1 (by omega) hpc1 hd2,
        show s1.rget 0 + (BitVec.ofNat 12 0).signExtend 64 = (0 : Word) from by
          rw [Hex0.Refine.rget_zero]; decide,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]
          congr 1 <;> omega]
  let s2 := (s1.rset 11 0).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 8)))
  have hs2 : s2 = (s1.rset 11 0).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := rfl
  try rw [← hs2] at hu2
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) := rfl
  have hcode2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode1)
  have hra2 : s2.rget 1 = 0 := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (1:Nat) ≠ 11),
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (1:Nat) ≠ 10)]
    exact hra
  have hu3 : step s2 = s2.setPc 0 := by
    rw [step_jalr s2 (off + 8) 0 1 (BitVec.ofNat 12 0) hcode2 (by omega) hpc2 hd3, rset_zero]
    congr 1
    rw [hra2]
    decide
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by
    rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  refine ⟨s2.setPc 0, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [runFuel]
    rw [hu1, hu2, hu3, if_neg hp0, if_neg hp1, if_neg hp2]
  · rw [Hex0.Refine.setPc_rget, hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (10:Nat) ≠ 11),
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [Hex0.Refine.setPc_rget, hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [Hex0.Refine.setPc_mem, hs2, hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Generic exit epilogue, `a1 = t1` shape: `li a0,K; mv a1,t1; ret`. -/
theorem exit_t1 (s : State) (off K : Nat) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (hra : s.rget 1 = 0)
    (hd1 : Rv64i.decode (wordAt1 off) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 K))
    (hd2 : Rv64i.decode (wordAt1 (off + 4)) = Rv64i.Instr.addi 11 6 (BitVec.ofNat 12 0))
    (hd3 : Rv64i.decode (wordAt1 (off + 8)) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0))
    (hKsx : (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K)
    (ho : off + 8 + 3 < Image1.coreBytes.length) :
    ∃ f, runFuel 0 3 s = f ∧ f.pc = 0 ∧ f.rget 10 = BitVec.ofNat 64 K ∧
      f.rget 11 = s.rget 6 ∧ f.mem = s.mem := by
  have hcl : Image1.coreBytes.length = 724 := coreBytes_len
  have hb : off + 8 + 3 < 724 := hcl ▸ ho
  have hu1 : step s = (s.rset 10 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := by
    rw [step_addi s off 10 0 (BitVec.ofNat 12 K) hcode (by omega) hpc hd1,
        show s.rget 0 + (BitVec.ofNat 12 K).signExtend 64 = BitVec.ofNat 64 K from by
          rw [Hex0.Refine.rget_zero, hKsx]; simp,
        show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) from by
          rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ, Nat.add_assoc]]
  let s1 := (s.rset 10 (BitVec.ofNat 64 K)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 4)))
  have hs1 : s1 = (s.rset 10 (BitVec.ofNat 64 K)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 4))) := rfl
  try rw [← hs1] at hu1
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 4)) := rfl
  have hcode1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hr6_1 : s1.rget 6 = s.rget 6 := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (6:Nat) ≠ 10)]
  have hu2 : step s1 = (s1.rset 11 (s.rget 6)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := by
    rw [step_addi s1 (off + 4) 11 6 (BitVec.ofNat 12 0) hcode1 (by omega) hpc1 hd2,
        show s1.rget 6 + (BitVec.ofNat 12 0).signExtend 64 = s.rget 6 from by
          rw [hr6_1, show ((BitVec.ofNat 12 0).signExtend 64) = 0#64 from by decide,
              BitVec.add_zero],
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]
          congr 1 <;> omega]
  let s2 := (s1.rset 11 (s.rget 6)).setPc (BitVec.ofNat 64 (Image1.coreAddr + (off + 8)))
  have hs2 : s2 = (s1.rset 11 (s.rget 6)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (off + 8))) := rfl
  try rw [← hs2] at hu2
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + (off + 8)) := rfl
  have hcode2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode1)
  have hra2 : s2.rget 1 = 0 := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (1:Nat) ≠ 11),
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (1:Nat) ≠ 10)]
    exact hra
  have hu3 : step s2 = s2.setPc 0 := by
    rw [step_jalr s2 (off + 8) 0 1 (BitVec.ofNat 12 0) hcode2 (by omega) hpc2 hd3, rset_zero]
    congr 1
    rw [hra2]
    decide
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by
    rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  refine ⟨s2.setPc 0, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [runFuel]
    rw [hu1, hu2, hu3, if_neg hp0, if_neg hp1, if_neg hp2]
  · rw [Hex0.Refine.setPc_rget, hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (10:Nat) ≠ 11),
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [Hex0.Refine.setPc_rget, hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [Hex0.Refine.setPc_mem, hs2, hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]

/-! ## Pass 1: the loop invariant and the loop-head prefix. -/

/-- Invariant at the pass-1 loop head (offset 36). `lab`/`pos` are the scan
    state; `rest` the unconsumed input suffix. The telescope `spec` pins the
    whole-input scan to the residual scan. -/
structure P1Inv (inp : List Nat) (cap : Nat) (s : State)
    (lab : Labels) (pos : Nat) (rest : List Nat) : Prop where
  wf      : WellFormed1 inp cap
  at_loop : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 36)
  code    : CodeLoaded1 s
  a0      : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr
  a1      : s.rget 11 = BitVec.ofNat 64 inp.length
  a2      : s.rget 12 = BitVec.ofNat 64 Image1.outAddr
  a3      : s.rget 13 = BitVec.ofNat 64 cap
  a4      : s.rget 14 = BitVec.ofNat 64 Image1.lblAddr
  ra0     : s.rget 1  = 0
  in_mem  : InputLoaded s inp
  idx     : s.rget 5  = BitVec.ofNat 64 (inp.length - rest.length)
  suffix  : inp.drop (inp.length - rest.length) = rest
  outidx  : s.rget 6  = BitVec.ofNat 64 pos
  pos_le  : pos ≤ cap
  tbl     : TableLoaded s lab
  lab_le  : ∀ c p, lab c = some p → p ≤ pos
  spec    : Hex1.scan1 .High lab pos rest = Hex1.scan1 .High Hex1.noLabels 0 inp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The shared head of every non-EOF pass-1 iteration (offsets 36..48):
    `bgeu`(not taken) → `add` → `lbu` (read char `c`) → `addi` (bump index).
    Lands at offset 52 with `t2 = c`. -/
theorem p1_prefix (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State) (inv : P1Inv inp cap s lab pos (c :: rest')) :
    ∃ s4, runFuel 0 4 s = s4 ∧
      s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 52) ∧
      s4.rget 7 = BitVec.ofNat 64 c ∧
      s4.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) ∧
      s4.mem = s.mem ∧ CodeLoaded1 s4 ∧
      (∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s4.rget i = s.rget i) := by
  have hsuf := inv.suffix
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at h; omega
  have hilt : inp.length - (c :: rest').length < inp.length := by
    simp only [List.length_cons]; omega
  have hgetd : inp.getD (inp.length - (c :: rest').length) 0 = c := by
    rw [← getD_drop]; rw [hsuf]; rfl
  have hilt64 : inp.length < 2 ^ 64 := by
    have h1 := inv.wf.in_fits; have h2 := inv.wf.out_fits; have h3 := inv.wf.lbl_fits
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at h1 h2 h3; omega
  have hc256 : c < 256 := by
    apply inv.wf.bytes_ok
    have : c ∈ inp.drop (inp.length - (c :: rest').length) := by
      rw [hsuf]; exact List.mem_cons_self
    exact List.drop_subset _ _ this
  have hpc0 : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 36) := inv.at_loop
  -- step 1: bgeu t0,a1 -- NOT taken (idx < len)
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [inv.idx, inv.a1]; exact ult_ofNat _ _ hilt64 hilt
  have hu1 : step s = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 40)) := by
    rw [step_bgeu s 36 5 11 (BitVec.ofNat 13 324) inv.code (by rw [coreBytes_len]; omega)
        hpc0 dec_36, hult]
    simp only [if_true]
    rw [show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 40) from by
      rw [hpc0, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s1 := s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 40))
  have hs1 : s1 = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 40)) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ inv.code
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 40) := rfl
  -- step 2: add t3,a0,t0
  have haddr : s1.rget 10 + s1.rget 5
      = BitVec.ofNat 64 (Image1.inputAddr + (inp.length - (c :: rest').length)) := by
    show s.rget 10 + s.rget 5 = _
    rw [inv.a0, inv.idx]; exact addr_ofNat_succ _ _
  have hu2 : step s1 = (s1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 44)) := by
    rw [step_add s1 40 28 10 5 hc1 (by rw [coreBytes_len]; omega) hpc1 dec_40, haddr,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 44) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s2 := (s1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 44))
  have hs2 : s2 = (s1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 44)) := rfl
  try rw [← hs2] at hu2
  have hc2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 44) := rfl
  -- step 3: lbu t2,0(t3)
  have hr28 : s2.rget 28 = BitVec.ofNat 64
      (Image1.inputAddr + (inp.length - (c :: rest').length)) := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hbyte : (s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64
      = BitVec.ofNat 64 c := by
    rw [hr28, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
    show (s2.mem _).setWidth 64 = _
    rw [hs2]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem, hs1]
    rw [inv.in_mem _ hilt, hgetd, setWidth8_64 c hc256]
  have hu3 : step s2 = (s2.rset 7 (BitVec.ofNat 64 c)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 48)) := by
    rw [step_lbu s2 44 7 28 (0#12) hc2 (by rw [coreBytes_len]; omega) hpc2 dec_44]
    rw [show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 48) from by
      rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    rw [hbyte]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 c)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 48))
  have hs3 : s3 = (s2.rset 7 (BitVec.ofNat 64 c)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 48)) := rfl
  try rw [← hs3] at hu3
  have hc3 : CodeLoaded1 s3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 48) := rfl
  have hr5_3 : s3.rget 5 = s.rget 5 := by
    rw [hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 7), hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28),
        hs1, Hex0.Refine.setPc_rget]
  -- step 4: addi t0,t0,1
  have hidx1 : s.rget 5 + 1 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [inv.idx, show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
    congr 1
    simp only [List.length_cons]
    omega
  have hu4 : step s3 = (s3.rset 5 (BitVec.ofNat 64 (inp.length - rest'.length))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 52)) := by
    rw [step_addi s3 48 5 5 (BitVec.ofNat 12 1) hc3 (by rw [coreBytes_len]; omega) hpc3 dec_48,
        show s3.rget 5 + (BitVec.ofNat 12 1).signExtend 64
            = BitVec.ofNat 64 (inp.length - rest'.length) from by
          rw [hr5_3, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide]
          exact hidx1,
        show s3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 52) from by
          rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s4 := (s3.rset 5 (BitVec.ofNat 64 (inp.length - rest'.length))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 52))
  have hs4 : s4 = (s3.rset 5 (BitVec.ofNat 64 (inp.length - rest'.length))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 52)) := rfl
  try rw [← hs4] at hu4
  have hp0 : s.pc ≠ 0 := by
    rw [hpc0]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by
    rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp3 : s3.pc ≠ 0 := by
    rw [hpc3]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  refine ⟨s4, ?_, rfl, ?_, ?_, ?_, codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3), ?_⟩
  · simp only [runFuel]
    rw [hu1, hu2, hu3, hu4, if_neg hp0, if_neg hp1, if_neg hp2, if_neg hp3]
  · rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 5), hs3, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [hs4, hs3, hs2, hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
  · intro i h0 h5 h7 h28
    rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5,
        hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7,
        hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28,
        hs1, Hex0.Refine.setPc_rget]

/-! ## Pass-1 iteration: spacing tokens. -/

/-- Suffix step: consuming the head advances the drop index. -/
theorem suffix_step (inp : List Nat) (c : Nat) (rest' : List Nat)
    (hsuf : inp.drop (inp.length - (c :: rest').length) = c :: rest') :
    inp.drop (inp.length - rest'.length) = rest' := by
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at h; omega
  have he : inp.length - rest'.length = (inp.length - (c :: rest').length) + 1 := by
    simp only [List.length_cons]; omega
  rw [he, ← List.drop_drop, hsuf]
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-1 spacing dispatch (from offset 52, `t2 = c ∈ {10,32,95}`):
    the `li;beq` chain falls through `#`/`;` and branches back to the loop
    head at the matching spacing char. Touches only `t3` and `pc`. -/
theorem p1_spacing_tail (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 52))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c)
    (hc : c = 10 ∨ c = 32 ∨ c = 95) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 36) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  -- block 1 (52): li t3,35; beq -- not taken (c ≠ 35)
  have hne35 : (BitVec.ofNat 64 c : Word) ≠ BitVec.ofNat 64 35 := by
    rcases hc with h | h | h <;> subst h <;> decide
  have hb1 := li_beq_ne s4 52 35 c (BitVec.ofNat 13 276) hcode hpc ht2 dec_52 dec_56
    (by decide) hne35 (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 60))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (52 + 8))) := rfl
  try rw [← hv1] at hb1
  have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 60) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  -- block 2 (60): li t3,59; beq -- not taken (c ≠ 59)
  have hne59 : (BitVec.ofNat 64 c : Word) ≠ BitVec.ofNat 64 59 := by
    rcases hc with h | h | h <;> subst h <;> decide
  have hb2 := li_beq_ne v1 60 59 c (BitVec.ofNat 13 268) hc1 hpc1 ht2v1 dec_60 dec_64
    (by decide) hne59 (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 68))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (60 + 8))) := rfl
  try rw [← hv2] at hb2
  have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 68) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have frame12 : ∀ i, i ≠ 28 → v2.rget i = s4.rget i := by
    intro i hi
    rw [hv2, li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]
  have hmem2 : v2.mem = s4.mem := rfl
  rcases hc with h10 | h32 | h95
  · -- '\n': block 3 (68) taken to LOOP
    subst h10
    have hb3 := li_beq_eq v2 68 10 10 (BitVec.ofNat 13 8156)
      (BitVec.ofNat 64 (Image1.coreAddr + 36)) hc2 hpc2 ht2v2 dec_68 dec_72
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨6, (v2.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 36)), ?_, by omega, ?_, ?_, ?_⟩
    · rw [show (6:Nat) = 2 + (2 + 2) from rfl, runFuel_add, hb1, runFuel_add, hb2, hb3]
    · rfl
    · rfl
    · intro i hi
      rw [li_block_frame _ _ _ i hi]
      exact frame12 i hi
  · -- ' ': block 3 (68) not taken, block 4 (76) taken
    subst h32
    have hb3 := li_beq_ne v2 68 10 32 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_68 dec_72
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 76))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (68 + 8))) := rfl
    try rw [← hv3] at hb3
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 76) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 32 := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have hb4 := li_beq_eq v3 76 32 32 (BitVec.ofNat 13 8148)
      (BitVec.ofNat 64 (Image1.coreAddr + 36)) hc3 hpc3 ht2v3 dec_76 dec_80
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨8, (v3.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 36)), ?_, by omega, ?_, ?_, ?_⟩
    · rw [show (8:Nat) = 2 + (2 + (2 + 2)) from rfl, runFuel_add, hb1, runFuel_add, hb2,
          runFuel_add, hb3, hb4]
    · rfl
    · rfl
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi]
      exact frame12 i hi
  · -- '_': blocks 3,4 not taken, block 5 (84) taken
    subst h95
    have hb3 := li_beq_ne v2 68 10 95 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_68 dec_72
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 76))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (68 + 8))) := rfl
    try rw [← hv3] at hb3
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 76) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 95 := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have hb4 := li_beq_ne v3 76 32 95 (BitVec.ofNat 13 8148) hc3 hpc3 ht2v3 dec_76 dec_80
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 84))
    have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (76 + 8))) := rfl
    try rw [← hv4] at hb4
    have hc4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
    have hpc4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 84) := rfl
    have ht2v4 : v4.rget 7 = BitVec.ofNat 64 95 := by
      rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v3
    have hb5 := li_beq_eq v4 84 95 95 (BitVec.ofNat 13 8140)
      (BitVec.ofNat 64 (Image1.coreAddr + 36)) hc4 hpc4 ht2v4 dec_84 dec_88
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨10, (v4.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 36)), ?_, by omega, ?_, ?_, ?_⟩
    · rw [show (10:Nat) = 2 + (2 + (2 + (2 + 2))) from rfl, runFuel_add, hb1, runFuel_add,
          hb2, runFuel_add, hb3, runFuel_add, hb4, hb5]
    · rfl
    · rfl
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv4, li_block_frame _ _ _ i hi, hv3,
          li_block_frame _ _ _ i hi]
      exact frame12 i hi

set_option maxHeartbeats 1000000 in
/-- A COMPLETE pass-1 iteration for a spacing token: prefix + dispatch,
    rebuilding the invariant on the shorter suffix. -/
theorem p1_spacing (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos (c :: rest'))
    (hsp : Hex0.isSpace c = true) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧ P1Inv inp cap s' lab pos rest' := by
  have hc : c = 10 ∨ c = 32 ∨ c = 95 := by
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Bool.or_eq_true,
      beq_iff_eq] at hsp
    rcases hsp with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p1_prefix inp cap c rest' lab pos s inv
  obtain ⟨n, s', hrun', hn, hpc', hmem', hframe'⟩ :=
    p1_spacing_tail s4 c hcode4 hpc4 ht2 hc
  refine ⟨4 + n, s', by omega, ?_, ?_⟩
  · rw [runFuel_add, hrun4, hrun']
  have hmem : s'.mem = s.mem := by rw [hmem', hmem4]
  have hreg : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s'.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframe' i h28]
    exact hframe4 i h0 h5 h7 h28
  exact {
    wf := inv.wf
    at_loop := hpc'
    code := by
      intro i hi
      rw [show s'.mem = s.mem from hmem]
      exact inv.code i hi
    a0 := by rw [hreg 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
    a1 := by rw [hreg 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
    a2 := by rw [hreg 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
    a3 := by rw [hreg 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
    a4 := by rw [hreg 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
    ra0 := by rw [hreg 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
    in_mem := by
      intro i hi
      rw [show s'.mem = s.mem from hmem]
      exact inv.in_mem i hi
    idx := by rw [hframe' 5 (by decide), hidx4]
    suffix := suffix_step inp c rest' inv.suffix
    outidx := by rw [hreg 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
    pos_le := inv.pos_le
    tbl := by
      intro cc hcc k hk
      rw [show s'.mem = s.mem from hmem]
      exact inv.tbl cc hcc k hk
    lab_le := inv.lab_le
    spec := by
      rw [← inv.spec]
      rw [Hex1.scan1]
      rw [if_neg (by simp [Hex0.space_not_comment hsp]), if_pos hsp] }

/-! ## Pass-1 iteration: comment tokens — the inner scan loop. -/

set_option maxRecDepth 8000 in
/-- A `bgeu rs1,rs2` with equal operands: taken (1 step to `target`). -/
theorem bgeu_eq_taken (s : State) (off rs1 rs2 A : Nat) (immB : BitVec 13) (target : Word)
    (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + off))
    (h1 : s.rget rs1 = BitVec.ofNat 64 A) (h2 : s.rget rs2 = BitVec.ofNat 64 A)
    (hd : Rv64i.decode (wordAt1 off) = Rv64i.Instr.bgeu rs1 rs2 immB)
    (ho : off + 3 < Image1.coreBytes.length)
    (htgt : BitVec.ofNat 64 (Image1.coreAddr + off) + immB.signExtend 64 = target) :
    step s = s.setPc target := by
  rw [step_bgeu s off rs1 rs2 immB hcode ho hpc hd, h1, h2,
      show (BitVec.ofNat 64 A).ult (BitVec.ofNat 64 A) = false from by
        simp [BitVec.ult],
      hpc]
  simp only [Bool.false_eq_true, if_false]
  rw [htgt]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The 4-instruction head of the comment inner loop (offsets 332..344):
    `bgeu`(not taken) → `add` → `lbu` (read `inp[idx]`) → `li t3,10`.
    Reaches offset 348 with `t2 = inp[idx]`, `t3 = 10`, `t0` unchanged. -/
theorem comment_read1 (s : State) (inp : List Nat) (idx ch : Nat) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 332))
    (h5 : s.rget 5 = BitVec.ofNat 64 idx)
    (h10 : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr)
    (h11 : s.rget 11 = BitVec.ofNat 64 inp.length)
    (hlt : idx < inp.length)
    (hmem : InputLoaded s inp)
    (hinlt : inp.length < 2 ^ 64) (hch : inp.getD idx 0 = ch) (hch256 : ch < 256) :
    ∃ s4, runFuel 0 4 s = s4 ∧ s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 348) ∧
      s4.rget 7 = BitVec.ofNat 64 ch ∧ s4.rget 28 = BitVec.ofNat 64 10 ∧
      s4.rget 5 = BitVec.ofNat 64 idx ∧ s4.mem = s.mem ∧ CodeLoaded1 s4 ∧
      (∀ i, i ≠ 7 → i ≠ 28 → s4.rget i = s.rget i) := by
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [h5, h11]; exact ult_ofNat _ _ hinlt hlt
  have hs1 : step s = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 336)) := by
    rw [step_bgeu s 332 5 11 (BitVec.ofNat 13 28) hcode (by rw [coreBytes_len]; omega)
        hpc dec_332, if_pos hult,
        show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 336) from by rw [hpc]; decide]
  let s1 := s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 336))
  have hs1d : s1 = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 336)) := rfl
  try rw [← hs1d] at hs1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ hcode
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 336) := rfl
  have haddr : s1.rget 10 + s1.rget 5 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    show s.rget 10 + s.rget 5 = _
    rw [h10, h5]; exact addr_ofNat_succ _ _
  have hs2 : step s1 = (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 340)) := by
    rw [step_add s1 336 28 10 5 hc1 (by rw [coreBytes_len]; omega) hpc1 dec_336, haddr,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 340) from by rw [hpc1]; decide]
  let s2 := (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 340))
  have hs2d : s2 = (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 340)) := rfl
  try rw [← hs2d] at hs2
  have hc2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 340) := rfl
  have hr28 : s2.rget 28 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    rw [hs2d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hbyte : (s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64
      = BitVec.ofNat 64 ch := by
    rw [hr28, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
    show (s2.mem _).setWidth 64 = _
    rw [hs2d]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem, hs1d]
    rw [hmem _ hlt, hch, setWidth8_64 ch hch256]
  have hs3 : step s2 = (s2.rset 7 (BitVec.ofNat 64 ch)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 344)) := by
    rw [step_lbu s2 340 7 28 (0#12) hc2 (by rw [coreBytes_len]; omega) hpc2 dec_340]
    rw [show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 344) from by rw [hpc2]; decide]
    rw [hbyte]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 ch)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 344))
  have hs3d : s3 = (s2.rset 7 (BitVec.ofNat 64 ch)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 344)) := rfl
  try rw [← hs3d] at hs3
  have hc3 : CodeLoaded1 s3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 344) := rfl
  have hs4 : step s3 = (s3.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 348)) := by
    rw [step_addi s3 344 28 0 (BitVec.ofNat 12 10) hc3 (by rw [coreBytes_len]; omega)
        hpc3 dec_344,
        show s3.rget 0 + (BitVec.ofNat 12 10).signExtend 64 = BitVec.ofNat 64 10 from by
          rw [Hex0.Refine.rget_zero]; decide,
        show s3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 348) from by rw [hpc3]; decide]
  let s4 := (s3.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 348))
  have hs4d : s4 = (s3.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 348)) := rfl
  try rw [← hs4d] at hs4
  have hp0 : s.pc ≠ 0 := by
    rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp1 : s1.pc ≠ 0 := by
    rw [hpc1]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp2 : s2.pc ≠ 0 := by
    rw [hpc2]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  have hp3 : s3.pc ≠ 0 := by
    rw [hpc3]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
      (by simp only [Image1.coreAddr]; omega)
  refine ⟨s4, ?_, rfl, ?_, ?_, ?_, ?_, codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3), ?_⟩
  · simp only [runFuel]
    rw [hs1, hs2, hs3, hs4, if_neg hp0, if_neg hp1, if_neg hp2, if_neg hp3]
  · rw [hs4d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28), hs3d, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [hs4d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  · rw [hs4d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 28), hs3d, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 7),
        hs2d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 28), hs1d, Hex0.Refine.setPc_rget]
    exact h5
  · rw [hs4d]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem, hs3d, hs2d, hs1d]
  · intro i h7 h28
    by_cases h0 : i = 0
    · simp [h0]
    rw [hs4d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28,
        hs3d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7,
        hs2d, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28,
        hs1d, Hex0.Refine.setPc_rget]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The comment inner loop (offsets 332..356): scans `inp` from `idx` until a
    newline (left unconsumed, back to the loop head 36 sitting on it) or EOF
    (exits to pass-2 entry 360). Touches only `t0`/`t2`/`t3`. -/
theorem comment_loop1 (inp : List Nat) : ∀ (n : Nat) (s : State) (idx : Nat),
    CodeLoaded1 s → s.pc = BitVec.ofNat 64 (Image1.coreAddr + 332) →
    s.rget 5 = BitVec.ofNat 64 idx → s.rget 10 = BitVec.ofNat 64 Image1.inputAddr →
    s.rget 11 = BitVec.ofNat 64 inp.length →
    InputLoaded s inp →
    inp.length < 2 ^ 64 → (∀ b ∈ inp, b < 256) → idx ≤ inp.length → inp.length - idx ≤ n →
    ∃ k, (∃ q, idx ≤ q ∧ q < inp.length ∧ inp.getD q 0 = 10 ∧
            Hex0.skipComment (inp.drop idx) = inp.drop (q + 1) ∧
            (runFuel 0 k s).pc = BitVec.ofNat 64 (Image1.coreAddr + 36) ∧
            (runFuel 0 k s).rget 5 = BitVec.ofNat 64 q ∧
            (runFuel 0 k s).mem = s.mem ∧
            (∀ i, i ≠ 5 → i ≠ 7 → i ≠ 28 → (runFuel 0 k s).rget i = s.rget i))
         ∨ (Hex0.skipComment (inp.drop idx) = [] ∧
            (runFuel 0 k s).pc = BitVec.ofNat 64 (Image1.coreAddr + 360) ∧
            (runFuel 0 k s).rget 5 = BitVec.ofNat 64 inp.length ∧
            (runFuel 0 k s).mem = s.mem ∧
            (∀ i, i ≠ 5 → i ≠ 7 → i ≠ 28 → (runFuel 0 k s).rget i = s.rget i)) := by
  intro n
  induction n with
  | zero =>
    intro s idx hcode hpc h5 h10 h11 hmem hinlt hbytes hle hn
    have hidx : idx = inp.length := by omega
    subst hidx
    have hbt := bgeu_eq_taken s 332 5 11 inp.length (BitVec.ofNat 13 28)
      (BitVec.ofNat 64 (Image1.coreAddr + 360)) hcode hpc h5 h11 dec_332
      (by rw [coreBytes_len]; omega) (by decide)
    refine ⟨1, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [List.drop_length]; rfl
    · rw [runFuel_one s (by
        rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
          (by simp only [Image1.coreAddr]; omega)), hbt]
      rfl
    · rw [runFuel_one s (by
        rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
          (by simp only [Image1.coreAddr]; omega)), hbt, Hex0.Refine.setPc_rget]
      exact h5
    · rw [runFuel_one s (by
        rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
          (by simp only [Image1.coreAddr]; omega)), hbt]
      rfl
    · intro i _ _ _
      rw [runFuel_one s (by
        rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
          (by simp only [Image1.coreAddr]; omega)), hbt, Hex0.Refine.setPc_rget]
  | succ n ih =>
    intro s idx hcode hpc h5 h10 h11 hmem hinlt hbytes hle hn
    by_cases hlt : idx < inp.length
    · have hch256 : inp.getD idx 0 < 256 := by
        apply hbytes
        rw [show inp.getD idx 0 = inp[idx] from (List.getElem_eq_getD 0).symm]
        exact List.getElem_mem hlt
      have hcons : inp.drop idx = inp.getD idx 0 :: inp.drop (idx + 1) := by
        rw [List.drop_eq_getElem_cons hlt,
            show inp[idx] = inp.getD idx 0 from List.getElem_eq_getD 0]
      obtain ⟨s4, hr4, hpc4, h7_4, h28_4, h5_4, hmem4, hcode4, hoth4⟩ :=
        comment_read1 s inp idx (inp.getD idx 0) hcode hpc h5 h10 h11 hlt hmem hinlt rfl hch256
      by_cases hnl : inp.getD idx 0 = 10
      · -- newline at idx → loop head, sitting on it
        have hbeq : step s4 = s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := by
          rw [step_beq s4 348 7 28 (BitVec.ofNat 13 7880) hcode4
              (by rw [coreBytes_len]; omega) hpc4 dec_348, h7_4, h28_4, hnl, if_pos rfl,
              show s4.pc + (BitVec.ofNat 13 7880).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 36) from by rw [hpc4]; decide]
        have hp4 : s4.pc ≠ 0 := by
          rw [hpc4]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
            (by simp only [Image1.coreAddr]; omega)
        have hskip : Hex0.skipComment (inp.drop idx) = inp.drop (idx + 1) := by
          rw [hcons, skipComment_cons_nl _ _ (by rw [Hex0.c_nl]; exact hnl)]
        refine ⟨4 + 1, Or.inl ⟨idx, Nat.le_refl _, hlt, hnl, hskip, ?_, ?_, ?_, ?_⟩⟩
        · rw [runFuel_add, hr4, runFuel_one _ hp4, hbeq]; rfl
        · rw [runFuel_add, hr4, runFuel_one _ hp4, hbeq, Hex0.Refine.setPc_rget]; exact h5_4
        · rw [runFuel_add, hr4, runFuel_one _ hp4, hbeq]
          show s4.mem = s.mem
          exact hmem4
        · intro i h5i h7i h28i
          rw [runFuel_add, hr4, runFuel_one _ hp4, hbeq, Hex0.Refine.setPc_rget,
              hoth4 i h7i h28i]
      · -- not newline → consume and recurse
        have hch64 : inp.getD idx 0 < 2 ^ 64 := Nat.lt_trans hch256 (by decide)
        have hbeq : step s4 = s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 352)) := by
          rw [step_beq s4 348 7 28 (BitVec.ofNat 13 7880) hcode4
              (by rw [coreBytes_len]; omega) hpc4 dec_348, h7_4, h28_4,
              if_neg (ofNat_ne _ 10 hch64 (by decide) hnl),
              show s4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 352) from by
                rw [hpc4]; decide]
        let v5 := s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 352))
        have hv5 : v5 = s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 352)) := rfl
        try rw [← hv5] at hbeq
        have hc5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ hcode4
        have hpc5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 352) := rfl
        have h5v5 : v5.rget 5 = BitVec.ofNat 64 idx := by
          rw [hv5, Hex0.Refine.setPc_rget]; exact h5_4
        have haddi : step v5 = (v5.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
            (BitVec.ofNat 64 (Image1.coreAddr + 356)) := by
          rw [step_addi v5 352 5 5 (BitVec.ofNat 12 1) hc5 (by rw [coreBytes_len]; omega)
              hpc5 dec_352, h5v5,
              show ((BitVec.ofNat 12 1).signExtend 64 : Word) = BitVec.ofNat 64 1 from by decide,
              addr_ofNat_succ,
              show v5.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 356) from by
                rw [hpc5]; decide]
        let v6 := (v5.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
            (BitVec.ofNat 64 (Image1.coreAddr + 356))
        have hv6 : v6 = (v5.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
            (BitVec.ofNat 64 (Image1.coreAddr + 356)) := rfl
        try rw [← hv6] at haddi
        have hc6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc5)
        have hpc6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 356) := rfl
        have hjal : step v6 = v6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 332)) := by
          rw [step_jal v6 356 0 (BitVec.ofNat 21 2097128) hc6 (by rw [coreBytes_len]; omega)
              hpc6 dec_356, rset_zero,
              show v6.pc + (BitVec.ofNat 21 2097128).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 332) from by rw [hpc6]; decide]
        let s' := v6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 332))
        have hs' : s' = v6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 332)) := rfl
        try rw [← hs'] at hjal
        have hp4 : s4.pc ≠ 0 := by
          rw [hpc4]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
            (by simp only [Image1.coreAddr]; omega)
        have hp5 : v5.pc ≠ 0 := by
          rw [hpc5]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
            (by simp only [Image1.coreAddr]; omega)
        have hp6 : v6.pc ≠ 0 := by
          rw [hpc6]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
            (by simp only [Image1.coreAddr]; omega)
        have hrun3 : runFuel 0 3 s4 = s' := by
          simp only [runFuel]
          rw [hbeq, haddi, hjal, if_neg hp4, if_neg hp5, if_neg hp6]
        have hcs' : CodeLoaded1 s' :=
          codeLoaded1_setPc _ _ (codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _
            (codeLoaded1_setPc _ _ hcode4)))
        have hpcs' : s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 332) := rfl
        have h5s' : s'.rget 5 = BitVec.ofNat 64 (idx + 1) := by
          rw [hs', Hex0.Refine.setPc_rget, hv6, Hex0.Refine.setPc_rget,
              rset_rget _ _ _ _ (by decide) (by decide)]
          simp
        have hother' : ∀ i, i ≠ 5 → i ≠ 7 → i ≠ 28 → s'.rget i = s.rget i := by
          intro i h5i h7i h28i
          by_cases h0 : i = 0
          · simp [h0]
          rw [hs', Hex0.Refine.setPc_rget, hv6, Hex0.Refine.setPc_rget,
              rset_rget _ _ _ _ (by decide) h0, if_neg h5i, hv5, Hex0.Refine.setPc_rget,
              hoth4 i h7i h28i]
        have h10s' : s'.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
          rw [hother' 10 (by decide) (by decide) (by decide)]; exact h10
        have h11s' : s'.rget 11 = BitVec.ofNat 64 inp.length := by
          rw [hother' 11 (by decide) (by decide) (by decide)]; exact h11
        have hmems' : s'.mem = s.mem := by
          rw [hs']
          show v6.mem = s.mem
          rw [hv6]
          show v5.mem = s.mem
          rw [hv5]
          show s4.mem = s.mem
          exact hmem4
        obtain ⟨k, hk⟩ := ih s' (idx + 1) hcs' hpcs' h5s' h10s' h11s'
          (fun j hj => by rw [show s'.mem = s.mem from hmems']; exact hmem j hj)
          hinlt hbytes (by omega) (by omega)
        have hchain : runFuel 0 (4 + (3 + k)) s = runFuel 0 k s' := by
          rw [runFuel_add, hr4, runFuel_add, hrun3]
        refine ⟨4 + (3 + k), ?_⟩
        rcases hk with ⟨q, hq1, hq2, hq3, hqskip, hp, h5q, hmemq, hothq⟩ |
                       ⟨hqskip, hp, h5q, hmemq, hothq⟩
        · refine Or.inl ⟨q, by omega, hq2, hq3, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hcons, skipComment_cons_ne _ _ (by rw [Hex0.c_nl]; exact hnl)]; exact hqskip
          · rw [hchain]; exact hp
          · rw [hchain, h5q]
          · rw [hchain, hmemq, hmems']
          · intro i h5i h7i h28i
            rw [hchain, hothq i h5i h7i h28i, hother' i h5i h7i h28i]
        · refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [hcons, skipComment_cons_ne _ _ (by rw [Hex0.c_nl]; exact hnl)]; exact hqskip
          · rw [hchain]; exact hp
          · rw [hchain, h5q]
          · rw [hchain, hmemq, hmems']
          · intro i h5i h7i h28i
            rw [hchain, hothq i h5i h7i h28i, hother' i h5i h7i h28i]
    · have hidx : idx = inp.length := by omega
      subst hidx
      have hbt := bgeu_eq_taken s 332 5 11 inp.length (BitVec.ofNat 13 28)
        (BitVec.ofNat 64 (Image1.coreAddr + 360)) hcode hpc h5 h11 dec_332
        (by rw [coreBytes_len]; omega) (by decide)
      have hp0 : s.pc ≠ 0 := by
        rw [hpc]; exact ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
          (by simp only [Image1.coreAddr]; omega)
      refine ⟨1, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [List.drop_length]; rfl
      · rw [runFuel_one s hp0, hbt]; rfl
      · rw [runFuel_one s hp0, hbt, Hex0.Refine.setPc_rget]; exact h5
      · rw [runFuel_one s hp0, hbt]; rfl
      · intro i _ _ _
        rw [runFuel_one s hp0, hbt, Hex0.Refine.setPc_rget]

end Hex1.Refine
