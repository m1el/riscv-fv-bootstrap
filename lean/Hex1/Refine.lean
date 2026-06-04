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

end Hex1.Refine
