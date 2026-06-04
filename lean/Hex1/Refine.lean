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

end Hex1.Refine
