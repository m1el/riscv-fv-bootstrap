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

/-! ## Pass-1 iteration: comment tokens, assembled. -/

/-- State shape on arrival at pass-2 entry (offset 360): pass 1 scanned the
    whole input cleanly, the table holds the final label map. -/
structure P2Start (inp : List Nat) (cap : Nat) (s : State)
    (labF : Labels) (m : Nat) : Prop where
  wf      : WellFormed1 inp cap
  pc      : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 360)
  code    : CodeLoaded1 s
  a0      : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr
  a1      : s.rget 11 = BitVec.ofNat 64 inp.length
  a2      : s.rget 12 = BitVec.ofNat 64 Image1.outAddr
  a3      : s.rget 13 = BitVec.ofNat 64 cap
  a4      : s.rget 14 = BitVec.ofNat 64 Image1.lblAddr
  ra0     : s.rget 1  = 0
  in_mem  : InputLoaded s inp
  tbl     : TableLoaded s labF
  m_le    : m ≤ cap
  lab_le  : ∀ c p, labF c = some p → p ≤ m
  scan_ok : Hex1.scan1 .High Hex1.noLabels 0 inp = (labF, m, .Ok)

/-- `rest'` is the drop at the bumped index (suffix decomposition). -/
theorem suffix_tail (inp : List Nat) (c : Nat) (rest' : List Nat)
    (hsuf : inp.drop (inp.length - (c :: rest').length) = c :: rest') :
    inp.drop (inp.length - rest'.length) = rest' := suffix_step inp c rest' hsuf

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-1 iteration for a comment token (`#`/`;`): prefix +
    dispatch to 332 + the inner loop. Lands back at the loop head sitting on
    the newline (invariant on a strictly shorter suffix), or at pass-2 entry
    on EOF (the scan is complete and Ok). -/
theorem p1_comment (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos (c :: rest'))
    (hcm : Hex0.isComment c = true) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ rest2, rest2.length < (c :: rest').length ∧
          P1Inv inp cap s' lab pos rest2) ∨
        P2Start inp cap s' lab pos) := by
  have hc : c = 35 ∨ c = 59 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_true, beq_iff_eq] at hcm
    exact hcm
  -- facts about lengths/indices
  have hlen64 : inp.length < 2 ^ 64 := by
    have h1 := inv.wf.in_fits; have h2 := inv.wf.out_fits; have h3 := inv.wf.lbl_fits
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at h1 h2 h3; omega
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons] at h; omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_tail inp c rest' inv.suffix
  -- the index after consuming c
  have hidx1 : inp.length - rest'.length = (inp.length - (c :: rest').length) + 1 := by
    simp only [List.length_cons]; omega
  -- machine: prefix
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p1_prefix inp cap c rest' lab pos s inv
  -- machine: dispatch to 332 (per comment char)
  have hdispatch : ∃ d sd, runFuel 0 d s4 = sd ∧ 0 < d ∧
      sd.pc = BitVec.ofNat 64 (Image1.coreAddr + 332) ∧ sd.mem = s4.mem ∧
      (∀ i, i ≠ 28 → sd.rget i = s4.rget i) := by
    rcases hc with h35 | h59
    · subst h35
      have hb := li_beq_eq s4 52 35 35 (BitVec.ofNat 13 276)
        (BitVec.ofNat 64 (Image1.coreAddr + 332)) hcode4 hpc4 ht2 dec_52 dec_56
        (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
      refine ⟨2, (s4.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 332)), hb, by omega, rfl, rfl, ?_⟩
      intro i hi
      exact li_block_frame _ _ _ i hi
    · subst h59
      have hb1 := li_beq_ne s4 52 35 59 (BitVec.ofNat 13 276) hcode4 hpc4 ht2 dec_52 dec_56
        (by decide) (by decide) (by rw [coreBytes_len]; omega)
      let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 60))
      have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + (52 + 8))) := rfl
      try rw [← hv1] at hb1
      have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode4)
      have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 60) := rfl
      have ht2v1 : v1.rget 7 = BitVec.ofNat 64 59 := by
        rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (7:Nat) ≠ 28)]
        exact ht2
      have hb2 := li_beq_eq v1 60 59 59 (BitVec.ofNat 13 268)
        (BitVec.ofNat 64 (Image1.coreAddr + 332)) hc1 hpc1 ht2v1 dec_60 dec_64
        (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
      refine ⟨4, (v1.rset 28 (BitVec.ofNat 64 59)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 332)), ?_, by omega, rfl, rfl, ?_⟩
      · rw [show (4:Nat) = 2 + 2 from rfl, runFuel_add, hb1, hb2]
      · intro i hi
        rw [li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]
  obtain ⟨d, sd, hrund, hd, hpcd, hmemd, hframed⟩ := hdispatch
  -- inner loop preconditions at sd
  have hcoded : CodeLoaded1 sd := by
    intro i hi
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi
  have h5d : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide), hidx4]
  have h10d : sd.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
    rw [hframed 10 (by decide), hframe4 10 (by decide) (by decide) (by decide) (by decide)]
    exact inv.a0
  have h11d : sd.rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hframed 11 (by decide), hframe4 11 (by decide) (by decide) (by decide) (by decide)]
    exact inv.a1
  have hind : InputLoaded sd inp := by
    intro j hj
    rw [show sd.mem = s4.mem from hmemd, show s4.mem = s.mem from hmem4]
    exact inv.in_mem j hj
  obtain ⟨k, hk⟩ := comment_loop1 inp (inp.length - (inp.length - rest'.length)) sd
    (inp.length - rest'.length) hcoded hpcd h5d h10d h11d hind hlen64 inv.wf.bytes_ok
    (by omega) (by omega)
  -- spec-side: the comment unfold
  have hspec_cm : Hex1.scan1 .High lab pos (c :: rest')
      = Hex1.scan1 .High lab pos (Hex0.skipComment rest') := by
    rw [Hex1.scan1]
    rw [if_pos hcm]
  -- frame from s to the loop result
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  rcases hk with ⟨q, hq1, hq2, hq3, hqskip, hp, h5q, hmemq, hothq⟩ |
                 ⟨hqskip, hp, h5q, hmemq, hothq⟩
  · -- newline found at q: back to the loop head on suffix `drop q`
    rw [hrest'_eq] at hqskip
    have hmemfin : (runFuel 0 k sd).mem = s.mem := by
      rw [hmemq, hmemd, hmem4]
    have hregfin : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
        (runFuel 0 k sd).rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hothq i h5 h7 h28]
      exact hframe_sd i h0 h5 h7 h28
    refine ⟨4 + (d + k), _, by omega,
      by rw [runFuel_add, hrun4, runFuel_add, hrund], Or.inl ⟨inp.drop q, ?_, ?_⟩⟩
    · simp only [List.length_drop, List.length_cons]
      omega
    exact {
      wf := inv.wf
      at_loop := hp
      code := by
        intro i hi
        rw [hmemfin]
        exact inv.code i hi
      a0 := by rw [hregfin 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
      a1 := by rw [hregfin 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
      a2 := by rw [hregfin 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
      a3 := by rw [hregfin 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
      a4 := by rw [hregfin 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
      ra0 := by rw [hregfin 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
      in_mem := by
        intro j hj
        rw [hmemfin]
        exact inv.in_mem j hj
      idx := by
        rw [h5q]
        congr 1
        simp only [List.length_drop]
        omega
      suffix := by
        have : inp.length - (inp.drop q).length = q := by
          simp only [List.length_drop]
          omega
        rw [this]
      outidx := by
        rw [hregfin 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
      pos_le := inv.pos_le
      tbl := by
        intro cc hcc kk hkk
        rw [hmemfin]
        exact inv.tbl cc hcc kk hkk
      lab_le := inv.lab_le
      spec := by
        -- scan1 (drop q) = scan1 (10 :: drop (q+1)) = scan1 (drop (q+1))
        --   = scan1 (skipComment rest') = scan1 (c :: rest') = whole input
        have hdq : inp.drop q = 10 :: inp.drop (q + 1) := by
          rw [List.drop_eq_getElem_cons hq2,
              show inp[q] = inp.getD q 0 from List.getElem_eq_getD 0, hq3]
        rw [hdq]
        rw [show Hex1.scan1 .High lab pos (10 :: inp.drop (q + 1))
            = Hex1.scan1 .High lab pos (inp.drop (q + 1)) from by
          rw [Hex1.scan1]
          rw [if_neg (by decide), if_pos (by decide)]]
        rw [← hqskip, ← hspec_cm]
        exact inv.spec }
  · -- EOF: the scan is complete and Ok → pass-2 entry
    rw [hrest'_eq] at hqskip
    have hscan_done : Hex1.scan1 .High lab pos (c :: rest') = (lab, pos, .Ok) := by
      rw [hspec_cm, hqskip]
      rw [Hex1.scan1]
    have hmemfin : (runFuel 0 k sd).mem = s.mem := by
      rw [hmemq, hmemd, hmem4]
    have hregfin : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
        (runFuel 0 k sd).rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hothq i h5 h7 h28]
      exact hframe_sd i h0 h5 h7 h28
    refine ⟨4 + (d + k), _, by omega,
      by rw [runFuel_add, hrun4, runFuel_add, hrund], Or.inr ?_⟩
    exact {
      wf := inv.wf
      pc := hp
      code := by
        intro i hi
        rw [hmemfin]
        exact inv.code i hi
      a0 := by rw [hregfin 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
      a1 := by rw [hregfin 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
      a2 := by rw [hregfin 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
      a3 := by rw [hregfin 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
      a4 := by rw [hregfin 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
      ra0 := by rw [hregfin 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
      in_mem := by
        intro j hj
        rw [hmemfin]
        exact inv.in_mem j hj
      tbl := by
        intro cc hcc kk hkk
        rw [hmemfin]
        exact inv.tbl cc hcc kk hkk
      m_le := inv.pos_le
      lab_le := inv.lab_le
      scan_ok := by rw [← inv.spec, hscan_done] }

/-! ## Pass-1 iteration: label definitions (`:l`), plus the `Result1`
    builder for the empty-output error exits. -/

/-- A pc inside the code region is nonzero. -/
theorem corePc_ne_zero (off : Nat) (hoff : off < 724) :
    BitVec.ofNat 64 (Image1.coreAddr + off) ≠ 0 :=
  ofNat_ne _ 0 (by simp only [Image1.coreAddr]; omega) (by decide)
    (by simp only [Image1.coreAddr]; omega)

/-- Build a `Result1` for an empty-output error exit: the machine halted with
    `a0 = statusCode st`, `a1 = 0`, while the whole-input scan stops with
    status `st` (a scan error) at position `m ≤ cap` (so the machine did not
    short). -/
theorem error_result1 (s : State) (inp : List Nat) (cap : Nat) (lab : Labels)
    (m : Nat) (st : Hex1.Status) (hp : s.pc = 0)
    (ha0 : s.rget 10 = BitVec.ofNat 64 (Hex1.statusCode st))
    (ha1 : s.rget 11 = 0)
    (hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, m, st))
    (hne : st ≠ .Ok) (hnu : st ≠ .Undef) (hle : m ≤ cap) :
    Result1 s inp cap := by
  have hdec : Hex1.decode1 inp = ([], m, st) := by
    cases st
    case Ok => exact absurd rfl hne
    case Undef => exact absurd rfl hnu
    all_goals simp only [Hex1.decode1, hscan]
  have hcs : Hex1.coreSpec1 inp cap = (Hex1.statusCode st, [], 0) := by
    cases st
    case Ok => exact absurd rfl hne
    case Undef => exact absurd rfl hnu
    all_goals
      simp only [Hex1.coreSpec1, hdec]
      rw [if_neg (Nat.not_lt.mpr hle)]
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [hcs]; exact ha0
  · rw [hcs]; exact ha1
  · intro j hj
    rw [hcs] at hj
    simp at hj

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-1 colon dispatch (from offset 52, `t2 = 58`): the `li;beq` chain
    falls through `#`/`;`/`\n`/` `/`_` and branches to the label-definition
    block at 264. Touches only `t3` and `pc`. -/
theorem p1_colon_tail (s4 : State) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 52))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 58) :
    ∃ s', runFuel 0 12 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 264) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  -- block 1 (52): li t3,35; beq -- not taken
  have hb1 := li_beq_ne s4 52 35 58 (BitVec.ofNat 13 276) hcode hpc ht2 dec_52 dec_56
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 60))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (52 + 8))) := rfl
  try rw [← hv1] at hb1
  have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 60) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  -- block 2 (60): li t3,59; beq -- not taken
  have hb2 := li_beq_ne v1 60 59 58 (BitVec.ofNat 13 268) hc1 hpc1 ht2v1 dec_60 dec_64
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 68))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (60 + 8))) := rfl
  try rw [← hv2] at hb2
  have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 68) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  -- block 3 (68): li t3,10; beq -- not taken
  have hb3 := li_beq_ne v2 68 10 58 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_68 dec_72
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 76))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (68 + 8))) := rfl
  try rw [← hv3] at hb3
  have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 76) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  -- block 4 (76): li t3,32; beq -- not taken
  have hb4 := li_beq_ne v3 76 32 58 (BitVec.ofNat 13 8148) hc3 hpc3 ht2v3 dec_76 dec_80
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 84))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (76 + 8))) := rfl
  try rw [← hv4] at hb4
  have hc4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
  have hpc4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 84) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  -- block 5 (84): li t3,95; beq -- not taken
  have hb5 := li_beq_ne v4 84 95 58 (BitVec.ofNat 13 8140) hc4 hpc4 ht2v4 dec_84 dec_88
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 92))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (84 + 8))) := rfl
  try rw [← hv5] at hb5
  have hc5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc4)
  have hpc5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 92) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  -- block 6 (92): li t3,58; beq -- TAKEN to 264
  have hb6 := li_beq_eq v5 92 58 58 (BitVec.ofNat 13 168)
    (BitVec.ofNat 64 (Image1.coreAddr + 264)) hc5 hpc5 ht2v5 dec_92 dec_96
    (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
  refine ⟨(v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 264)),
    ?_, rfl, rfl, ?_⟩
  · rw [show (12:Nat) = 2 + (2 + (2 + (2 + (2 + 2)))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, runFuel_add, hb5, hb6]
  · intro i hi
    rw [li_block_frame _ _ _ i hi, hv5, li_block_frame _ _ _ i hi, hv4,
        li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi, hv2,
        li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-1 iteration for a label definition (`:` then label byte):
    prefix + dispatch to 264 + the table update. Lands back at the loop head
    with `setLabel lab l pos` in the table (suffix shorter by 2), or halts
    `Result1` on a duplicate definition (Dup) / EOF after `:` (TrailTok). -/
theorem p1_labelDef (inp : List Nat) (cap : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos (58 :: rest')) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ l rest2, rest' = l :: rest2 ∧
          P1Inv inp cap s' (setLabel lab l pos) pos rest2) ∨
        Result1 s' inp cap) := by
  have hlbl := inv.wf.lbl_fits
  have hin := inv.wf.in_fits
  have hout := inv.wf.out_fits
  have hlen64 : inp.length < 2 ^ 64 := by
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hin hout hlbl
    omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp 58 rest' inv.suffix
  -- machine: prefix (36..48), then dispatch to 264
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p1_prefix inp cap 58 rest' lab pos s inv
  obtain ⟨sd, hrund, hpcd, hmemd, hframed⟩ := p1_colon_tail s4 hcode4 hpc4 ht2
  have hcoded : CodeLoaded1 sd := by
    intro i hi
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi
  have hmem_sd : sd.mem = s.mem := by rw [hmemd, hmem4]
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  have h5d : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide)]; exact hidx4
  have h11d : sd.rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hframe_sd 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
  have hpd0 : sd.pc ≠ 0 := by rw [hpcd]; exact corePc_ne_zero 264 (by omega)
  cases rest' with
  | nil =>
    -- EOF after ':' -- bgeu taken to 712, TrailTok exit
    have h5d' : sd.rget 5 = BitVec.ofNat 64 inp.length := by simpa using h5d
    have hbt := bgeu_eq_taken sd 264 5 11 inp.length (BitVec.ofNat 13 448)
      (BitVec.ofNat 64 (Image1.coreAddr + 712)) hcoded hpcd h5d' h11d dec_264
      (by rw [coreBytes_len]; omega) (by decide)
    let sE := sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 712))
    have hsE : sE = sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 712)) := rfl
    try rw [← hsE] at hbt
    have hrunE : runFuel 0 1 sd = sE := by rw [runFuel_one sd hpd0, hbt]
    have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hcoded
    have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 712) := rfl
    have hraE : sE.rget 1 = 0 := by
      rw [hsE, Hex0.Refine.setPc_rget,
          hframe_sd 1 (by decide) (by decide) (by decide) (by decide)]
      exact inv.ra0
    obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
      exit_zero sE 712 8 hcodeE hpcE hraE dec_712 dec_716 dec_720 (by decide)
        (by rw [coreBytes_len]; omega)
    have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .TrailTok) := by
      rw [← inv.spec]
      rw [Hex1.scan1]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
      rw [Hex1.scan1]
    refine ⟨4 + (12 + (1 + 3)), f, by omega, ?_, Or.inr ?_⟩
    · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunE, hrunf]
    · exact error_result1 f inp cap lab pos .TrailTok hfpc hfa0 hfa1 hscan
        (by decide) (by decide) inv.pos_le
  | cons l rest2 =>
    -- the label byte exists: read it, look the slot up
    have hge2 : rest2.length + 2 ≤ inp.length := by
      have h := congrArg List.length inv.suffix
      simp only [List.length_drop, List.length_cons] at h
      omega
    have hl256 : l < 256 := by
      apply inv.wf.bytes_ok
      have : l ∈ inp.drop (inp.length - (l :: rest2).length) := by
        rw [hrest'_eq]; exact List.mem_cons_self
      exact List.drop_subset _ _ this
    have hidx1lt : inp.length - (l :: rest2).length < inp.length := by
      simp only [List.length_cons]; omega
    have hgetl : inp.getD (inp.length - (l :: rest2).length) 0 = l := by
      rw [← getD_drop]; rw [hrest'_eq]; rfl
    -- step 1 (264): bgeu t0,a1 -- NOT taken
    have hult : (sd.rget 5).ult (sd.rget 11) = true := by
      rw [h5d, h11d]; exact ult_ofNat _ _ hlen64 hidx1lt
    have hu1 : step sd = sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 268)) := by
      rw [step_bgeu sd 264 5 11 (BitVec.ofNat 13 448) hcoded (by rw [coreBytes_len]; omega)
          hpcd dec_264, hult]
      simp only [if_true]
      rw [show sd.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 268) from by
        rw [hpcd, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u1 := sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 268))
    have hsu1 : u1 = sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 268)) := rfl
    try rw [← hsu1] at hu1
    have hc1 : CodeLoaded1 u1 := codeLoaded1_setPc _ _ hcoded
    have hpc1 : u1.pc = BitVec.ofNat 64 (Image1.coreAddr + 268) := rfl
    have hq1 : u1.pc ≠ 0 := by rw [hpc1]; exact corePc_ne_zero 268 (by omega)
    -- step 2 (268): add t3,a0,t0
    have h10u1 : u1.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
      rw [hsu1, Hex0.Refine.setPc_rget,
          hframe_sd 10 (by decide) (by decide) (by decide) (by decide)]
      exact inv.a0
    have h5u1 : u1.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
      rw [hsu1, Hex0.Refine.setPc_rget]; exact h5d
    have hu2 : step u1 = (u1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 272)) := by
      rw [step_add u1 268 28 10 5 hc1 (by rw [coreBytes_len]; omega) hpc1 dec_268,
          show u1.rget 10 + u1.rget 5 = BitVec.ofNat 64
              (Image1.inputAddr + (inp.length - (l :: rest2).length)) from by
            rw [h10u1, h5u1]; exact addr_ofNat_succ _ _,
          show u1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 272) from by
            rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u2 := (u1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 272))
    have hsu2 : u2 = (u1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 272)) := rfl
    try rw [← hsu2] at hu2
    have hc2 : CodeLoaded1 u2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : u2.pc = BitVec.ofNat 64 (Image1.coreAddr + 272) := rfl
    have hq2 : u2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 272 (by omega)
    -- step 3 (272): lbu t2,0(t3) -- reads the label byte l
    have hr28u2 : u2.rget 28 = BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)) := by
      rw [hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
    have hbyte : (u2.loadByte (u2.rget 28 + (0#12).signExtend 64)).setWidth 64
        = BitVec.ofNat 64 l := by
      rw [hr28u2, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
      show (u2.mem _).setWidth 64 = _
      rw [hsu2]
      simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem, hsu1]
      rw [hmem_sd, inv.in_mem _ hidx1lt, hgetl, setWidth8_64 l hl256]
    have hu3 : step u2 = (u2.rset 7 (BitVec.ofNat 64 l)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 276)) := by
      rw [step_lbu u2 272 7 28 (0#12) hc2 (by rw [coreBytes_len]; omega) hpc2 dec_272]
      rw [show u2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 276) from by
        rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
      rw [hbyte]
    let u3 := (u2.rset 7 (BitVec.ofNat 64 l)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 276))
    have hsu3 : u3 = (u2.rset 7 (BitVec.ofNat 64 l)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 276)) := rfl
    try rw [← hsu3] at hu3
    have hc3 : CodeLoaded1 u3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : u3.pc = BitVec.ofNat 64 (Image1.coreAddr + 276) := rfl
    have hq3 : u3.pc ≠ 0 := by rw [hpc3]; exact corePc_ne_zero 276 (by omega)
    -- step 4 (276): addi t0,t0,1
    have hr5u3 : u3.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
      rw [hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (5:Nat) ≠ 7), hsu2, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28),
          hsu1, Hex0.Refine.setPc_rget]
      exact h5d
    have hu4 : step u3 = (u3.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 280)) := by
      rw [step_addi u3 276 5 5 (BitVec.ofNat 12 1) hc3 (by rw [coreBytes_len]; omega)
          hpc3 dec_276,
          show u3.rget 5 + (BitVec.ofNat 12 1).signExtend 64
              = BitVec.ofNat 64 (inp.length - rest2.length) from by
            rw [hr5u3, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide,
                show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
            congr 1
            simp only [List.length_cons]
            omega,
          show u3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 280) from by
            rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u4 := (u3.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 280))
    have hsu4 : u4 = (u3.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 280)) := rfl
    try rw [← hsu4] at hu4
    have hc4 : CodeLoaded1 u4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
    have hpc4u : u4.pc = BitVec.ofNat 64 (Image1.coreAddr + 280) := rfl
    have hq4 : u4.pc ≠ 0 := by rw [hpc4u]; exact corePc_ne_zero 280 (by omega)
    -- step 5 (280): slli t3,t2,3
    have hr7u4 : u4.rget 7 = BitVec.ofNat 64 l := by
      rw [hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 5), hsu3, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have hu5 : step u4 = (u4.rset 28 (BitVec.ofNat 64 (8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 284)) := by
      rw [step_slli u4 280 28 7 3 hc4 (by rw [coreBytes_len]; omega) hpc4u dec_280,
          show u4.rget 7 <<< 3 = BitVec.ofNat 64 (8 * l) from by
            rw [hr7u4]; exact shl3_ofNat l hl256,
          show u4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 284) from by
            rw [hpc4u, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u5 := (u4.rset 28 (BitVec.ofNat 64 (8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 284))
    have hsu5 : u5 = (u4.rset 28 (BitVec.ofNat 64 (8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 284)) := rfl
    try rw [← hsu5] at hu5
    have hc5 : CodeLoaded1 u5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc4)
    have hpc5 : u5.pc = BitVec.ofNat 64 (Image1.coreAddr + 284) := rfl
    have hq5 : u5.pc ≠ 0 := by rw [hpc5]; exact corePc_ne_zero 284 (by omega)
    -- step 6 (284): add t3,t3,a4 -- the slot address
    have hr28u5 : u5.rget 28 = BitVec.ofNat 64 (8 * l) := by
      rw [hsu5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
    have hr14u5 : u5.rget 14 = BitVec.ofNat 64 Image1.lblAddr := by
      rw [hsu5, li_block_frame _ _ _ 14 (by decide),
          hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (14:Nat) ≠ 5),
          hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (14:Nat) ≠ 7),
          hsu2, li_block_frame _ _ _ 14 (by decide),
          hsu1, Hex0.Refine.setPc_rget,
          hframe_sd 14 (by decide) (by decide) (by decide) (by decide)]
      exact inv.a4
    have hu6 : step u5 = (u5.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 288)) := by
      rw [step_add u5 284 28 28 14 hc5 (by rw [coreBytes_len]; omega) hpc5 dec_284,
          show u5.rget 28 + u5.rget 14 = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) from by
            rw [hr28u5, hr14u5, addr_ofNat_succ]
            congr 1
            omega,
          show u5.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 288) from by
            rw [hpc5, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u6 := (u5.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 288))
    have hsu6 : u6 = (u5.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 288)) := rfl
    try rw [← hsu6] at hu6
    have hc6 : CodeLoaded1 u6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc5)
    have hpc6 : u6.pc = BitVec.ofNat 64 (Image1.coreAddr + 288) := rfl
    have hq6 : u6.pc ≠ 0 := by rw [hpc6]; exact corePc_ne_zero 288 (by omega)
    -- step 7 (288): ld t4,0(t3) -- reads the encoded slot
    have hr28u6 : u6.rget 28 = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) := by
      rw [hsu6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
    have hmem_u6 : u6.mem = s.mem := by
      rw [hsu6, hsu5, hsu4, hsu3, hsu2, hsu1]
      simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
      exact hmem_sd
    have htbl_u6 : TableLoaded u6 lab := by
      intro c hc k hk
      rw [hmem_u6]
      exact inv.tbl c hc k hk
    have hu7 : step u6 = (u6.rset 29 (encodeSlot (lab l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 292)) := by
      rw [step_ld u6 288 29 28 (0#12) hc6 (by rw [coreBytes_len]; omega) hpc6 dec_288,
          show u6.rget 28 + (0#12).signExtend 64
              = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) from by
            rw [hr28u6, show ((0#12).signExtend 64) = 0#64 from by decide, BitVec.add_zero],
          loadWord_slot u6 lab l hl256 htbl_u6,
          show u6.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 292) from by
            rw [hpc6, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u7 := (u6.rset 29 (encodeSlot (lab l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 292))
    have hsu7 : u7 = (u6.rset 29 (encodeSlot (lab l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 292)) := rfl
    try rw [← hsu7] at hu7
    have hc7 : CodeLoaded1 u7 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc6)
    have hpc7 : u7.pc = BitVec.ofNat 64 (Image1.coreAddr + 292) := rfl
    have hq7 : u7.pc ≠ 0 := by rw [hpc7]; exact corePc_ne_zero 292 (by omega)
    have hr29u7 : u7.rget 29 = encodeSlot (lab l) := by
      rw [hsu7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
    have hmem_u7 : u7.mem = s.mem := by
      rw [hsu7]
      show (u6.rset 29 (encodeSlot (lab l))).mem = s.mem
      rw [Hex0.Refine.rset_mem]
      exact hmem_u6
    have hframe_u7 : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → i ≠ 29 →
        u7.rget i = s.rget i := by
      intro i h0 h5i h7i h28i h29i
      rw [hsu7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
          hsu6, li_block_frame _ _ _ i h28i,
          hsu5, li_block_frame _ _ _ i h28i,
          hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5i,
          hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7i,
          hsu2, li_block_frame _ _ _ i h28i,
          hsu1, Hex0.Refine.setPc_rget]
      exact hframe_sd i h0 h5i h7i h28i
    have hrun7 : runFuel 0 7 sd = u7 := by
      simp only [runFuel]
      rw [hu1, hu2, hu3, hu4, hu5, hu6, hu7, if_neg hpd0, if_neg hq1, if_neg hq2,
          if_neg hq3, if_neg hq4, if_neg hq5, if_neg hq6]
    -- step 8 (292): bge t4,x0 -- the dup sign test
    cases hlab : lab l with
    | some p =>
      -- duplicate definition: slot non-negative, branch to 688 (Dup exit)
      have hp63 : p < 2 ^ 63 := by
        have h1 := inv.lab_le l p hlab
        have h2 := inv.pos_le
        have h3 := inv.wf.cap63
        omega
      have hu8 : step u7 = u7.setPc (BitVec.ofNat 64 (Image1.coreAddr + 688)) := by
        rw [step_bge u7 292 29 0 (BitVec.ofNat 13 396) hc7 (by rw [coreBytes_len]; omega)
            hpc7 dec_292, hr29u7, hlab, Hex0.Refine.rget_zero,
            encodeSlot_some_nonneg p hp63]
        simp only [Bool.false_eq_true, if_false]
        rw [show u7.pc + (BitVec.ofNat 13 396).signExtend 64
            = BitVec.ofNat 64 (Image1.coreAddr + 688) from by rw [hpc7]; decide]
      let sE := u7.setPc (BitVec.ofNat 64 (Image1.coreAddr + 688))
      have hsE : sE = u7.setPc (BitVec.ofNat 64 (Image1.coreAddr + 688)) := rfl
      try rw [← hsE] at hu8
      have hrunE : runFuel 0 1 u7 = sE := by rw [runFuel_one u7 hq7, hu8]
      have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hc7
      have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 688) := rfl
      have hraE : sE.rget 1 = 0 := by
        rw [hsE, Hex0.Refine.setPc_rget,
            hframe_u7 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact inv.ra0
      obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
        exit_zero sE 688 6 hcodeE hpcE hraE dec_688 dec_692 dec_696 (by decide)
          (by rw [coreBytes_len]; omega)
      have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .Dup) := by
        rw [← inv.spec]
        rw [Hex1.scan1]
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        rw [Hex1.scan1]
        rw [hlab]
      refine ⟨4 + (12 + (7 + (1 + 3))), f, by omega, ?_, Or.inr ?_⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrun7,
            runFuel_add, hrunE, hrunf]
      · exact error_result1 f inp cap lab pos .Dup hfpc hfa0 hfa1 hscan
          (by decide) (by decide) inv.pos_le
    | none =>
      -- fresh label: fall through, store pos in the slot, loop back
      have hu8 : step u7 = u7.setPc (BitVec.ofNat 64 (Image1.coreAddr + 296)) := by
        rw [step_bge u7 292 29 0 (BitVec.ofNat 13 396) hc7 (by rw [coreBytes_len]; omega)
            hpc7 dec_292, hr29u7, hlab, Hex0.Refine.rget_zero, encodeSlot_none_neg]
        simp only [if_true]
        rw [show u7.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 296) from by
          rw [hpc7]; decide]
      let u8 := u7.setPc (BitVec.ofNat 64 (Image1.coreAddr + 296))
      have hsu8 : u8 = u7.setPc (BitVec.ofNat 64 (Image1.coreAddr + 296)) := rfl
      try rw [← hsu8] at hu8
      have hc8 : CodeLoaded1 u8 := codeLoaded1_setPc _ _ hc7
      have hpc8 : u8.pc = BitVec.ofNat 64 (Image1.coreAddr + 296) := rfl
      have hq8 : u8.pc ≠ 0 := by rw [hpc8]; exact corePc_ne_zero 296 (by omega)
      have hmem_u8 : u8.mem = s.mem := by
        rw [hsu8, Hex0.Refine.setPc_mem]
        exact hmem_u7
      -- step 9 (296): sd t1,0(t3) -- store pos in the slot
      have hr28u8 : u8.rget 28 = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) := by
        rw [hsu8, Hex0.Refine.setPc_rget, hsu7, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (28:Nat) ≠ 29)]
        exact hr28u6
      have hr6u8 : u8.rget 6 = BitVec.ofNat 64 pos := by
        rw [hsu8, Hex0.Refine.setPc_rget,
            hframe_u7 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact inv.outidx
      have hu9 : step u8 = (u8.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))
          (BitVec.ofNat 64 pos)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 300)) := by
        rw [step_sd u8 296 28 6 (0#12) hc8 (by rw [coreBytes_len]; omega) hpc8 dec_296,
            show u8.rget 28 + (0#12).signExtend 64
                = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) from by
              rw [hr28u8, show ((0#12).signExtend 64) = 0#64 from by decide,
                  BitVec.add_zero],
            hr6u8,
            show u8.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 300) from by
              rw [hpc8]; decide]
      let u9 := (u8.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))
          (BitVec.ofNat 64 pos)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 300))
      have hsu9 : u9 = (u8.storeWord (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))
          (BitVec.ofNat 64 pos)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 300)) := rfl
      try rw [← hsu9] at hu9
      have htbl_u8 : TableLoaded u8 lab := by
        intro c hc k hk
        rw [hmem_u8]
        exact inv.tbl c hc k hk
      have hc9 : CodeLoaded1 u9 :=
        codeLoaded1_setPc _ _ (codeLoaded1_storeWord u8 _ _ hc8 (by
          intro i k hi hk
          rw [coreBytes_len] at hi
          rw [addr_ofNat_succ]
          refine ofNat_ne _ _ ?_ ?_ ?_
          · simp only [Image1.coreAddr, Image1.lblAddr] at hlbl ⊢; omega
          · simp only [Image1.lblAddr] at hlbl ⊢; omega
          · simp only [Image1.coreAddr, Image1.lblAddr]; omega))
      have hin9 : InputLoaded u9 inp :=
        inputLoaded_setPc _ _ inp (inputLoaded_storeWord u8 _ _ inp (by
          intro j hj
          rw [hmem_u8]
          exact inv.in_mem j hj) (by
          intro i k hi hk
          rw [addr_ofNat_succ]
          refine ofNat_ne _ _ ?_ ?_ ?_
          · simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hlbl hin hout ⊢
            omega
          · simp only [Image1.lblAddr] at hlbl ⊢; omega
          · simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hlbl hin hout ⊢
            omega))
      have htbl9 : TableLoaded u9 (setLabel lab l pos) := by
        intro c hc k hk
        have h := storeWord_slot u8 lab l pos hl256 htbl_u8 hlbl c hc k hk
        rw [hsu9, Hex0.Refine.setPc_mem]
        exact h
      have hpc9 : u9.pc = BitVec.ofNat 64 (Image1.coreAddr + 300) := rfl
      have hq9 : u9.pc ≠ 0 := by rw [hpc9]; exact corePc_ne_zero 300 (by omega)
      -- step 10 (300): j 36 -- back to the loop head
      have hu10 : step u9 = u9.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := by
        rw [step_jal u9 300 0 (BitVec.ofNat 21 2096888) hc9 (by rw [coreBytes_len]; omega)
            hpc9 dec_300, rset_zero,
            show u9.pc + (BitVec.ofNat 21 2096888).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 36) from by rw [hpc9]; decide]
      let sF := u9.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36))
      have hsF : sF = u9.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := rfl
      try rw [← hsF] at hu10
      have hrunF : runFuel 0 3 u7 = sF := by
        simp only [runFuel]
        rw [hu8, hu9, hu10, if_neg hq7, if_neg hq8, if_neg hq9]
      have hregF : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → i ≠ 29 →
          sF.rget i = s.rget i := by
        intro i h0 h5i h7i h28i h29i
        rw [hsF, Hex0.Refine.setPc_rget, hsu9, Hex0.Refine.setPc_rget, storeWord_rget,
            hsu8, Hex0.Refine.setPc_rget]
        exact hframe_u7 i h0 h5i h7i h28i h29i
      have h5sF : sF.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
        rw [hsF, Hex0.Refine.setPc_rget, hsu9, Hex0.Refine.setPc_rget, storeWord_rget,
            hsu8, Hex0.Refine.setPc_rget,
            hsu7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsu6, li_block_frame _ _ _ 5 (by decide),
            hsu5, li_block_frame _ _ _ 5 (by decide),
            hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      have hmemF : sF.mem = u9.mem := by rw [hsF, Hex0.Refine.setPc_mem]
      -- spec side: scan1 steps through ':' and the fresh label byte
      have hspec_step : Hex1.scan1 .High lab pos (58 :: l :: rest2)
          = Hex1.scan1 .High (setLabel lab l pos) pos rest2 := by
        rw [Hex1.scan1]
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        rw [Hex1.scan1]
        rw [hlab]
      refine ⟨4 + (12 + (7 + 3)), sF, by omega, ?_, Or.inl ⟨l, rest2, rfl, ?_⟩⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrun7, hrunF]
      · exact {
          wf := inv.wf
          at_loop := rfl
          code := codeLoaded1_setPc _ _ hc9
          a0 := by
            rw [hregF 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.a0
          a1 := by
            rw [hregF 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.a1
          a2 := by
            rw [hregF 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.a2
          a3 := by
            rw [hregF 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.a3
          a4 := by
            rw [hregF 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.a4
          ra0 := by
            rw [hregF 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.ra0
          in_mem := by
            intro j hj
            rw [hmemF]
            exact hin9 j hj
          idx := h5sF
          suffix := suffix_step inp l rest2 hrest'_eq
          outidx := by
            rw [hregF 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.outidx
          pos_le := inv.pos_le
          tbl := by
            intro c hc k hk
            rw [hmemF]
            exact htbl9 c hc k hk
          lab_le := by
            intro c p hcp
            simp only [setLabel] at hcp
            by_cases hcl : c = l
            · rw [if_pos hcl] at hcp
              injection hcp with h
              omega
            · rw [if_neg hcl] at hcp
              exact inv.lab_le c p hcp
          spec := by
            rw [← hspec_step]
            exact inv.spec }

/-! ## Pass-1 iteration: label references (`%l`), plus the scan-position
    monotonicity lemma and the `Result1` builder for the Short exit. -/

/-- BitVec subtraction of `ofNat`s is the Nat subtraction (no wrap when
    `b ≤ a < 2^64`). -/
theorem sub_ofNat (a b : Nat) (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The scan's output position never decreases: starting at `pos`, the
    returned `m` satisfies `pos ≤ m` (induction on a length bound). -/
theorem scan1_pos_le : ∀ (n : Nat) (st : Hex1.St1) (lab : Labels) (pos : Nat)
    (rest : List Nat), rest.length ≤ n →
    pos ≤ (Hex1.scan1 st lab pos rest).2.1 := by
  intro n
  induction n with
  | zero =>
    intro st lab pos rest hn
    cases rest with
    | cons c rest' => simp only [List.length_cons] at hn; omega
    | nil => cases st <;> (rw [Hex1.scan1]; exact Nat.le_refl pos)
  | succ n ih =>
    intro st lab pos rest hn
    cases rest with
    | nil => cases st <;> (rw [Hex1.scan1]; exact Nat.le_refl pos)
    | cons c rest' =>
      have hlen : rest'.length ≤ n := by
        simp only [List.length_cons] at hn; omega
      cases st with
      | High =>
        rw [Hex1.scan1]
        by_cases hcm : Hex0.isComment c = true
        · rw [if_pos hcm]
          exact ih .High lab pos (Hex0.skipComment rest')
            (Nat.le_trans (Hex0.skipComment_len rest') hlen)
        · rw [if_neg hcm]
          by_cases hsp : Hex0.isSpace c = true
          · rw [if_pos hsp]
            exact ih .High lab pos rest' hlen
          · rw [if_neg hsp]
            by_cases hcol : (c == Hex1.c_colon) = true
            · rw [if_pos hcol]
              exact ih .Col lab pos rest' hlen
            · rw [if_neg hcol]
              by_cases hpct : (c == Hex1.c_pct) = true
              · rw [if_pos hpct]
                exact ih .Pct lab pos rest' hlen
              · rw [if_neg hpct]
                cases hnib : Hex0.nibble c with
                | none => exact Nat.le_refl pos
                | some hi => exact ih (.Low hi) lab pos rest' hlen
      | Low hi =>
        rw [Hex1.scan1]
        by_cases hls : Hex1.isLowStop c = true
        · rw [if_pos hls]
          exact Nat.le_refl pos
        · rw [if_neg hls]
          cases hnib : Hex0.nibble c with
          | none => exact Nat.le_refl pos
          | some lo =>
            show pos ≤ (Hex1.scan1 .High lab (pos + 1) rest').2.1
            have h := ih .High lab (pos + 1) rest' hlen
            omega
      | Col =>
        rw [Hex1.scan1]
        cases hl : lab c with
        | some p => exact Nat.le_refl pos
        | none => exact ih .High (setLabel lab c pos) pos rest' hlen
      | Pct =>
        rw [Hex1.scan1]
        have h := ih .High lab (pos + 4) rest' hlen
        omega

/-- `decode1` reports the scan's stop position `m` whatever the status. -/
theorem decode1_m (inp : List Nat) (lab : Labels) (m : Nat) (st : Hex1.Status)
    (hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, m, st)) :
    ∃ out st', Hex1.decode1 inp = (out, m, st') := by
  cases st with
  | Ok =>
    obtain ⟨out, st', hemit⟩ : ∃ out st', Hex1.emit1 .High lab 0 inp = (out, st') :=
      ⟨(Hex1.emit1 .High lab 0 inp).1, (Hex1.emit1 .High lab 0 inp).2, rfl⟩
    exact ⟨out, st', by simp only [Hex1.decode1, hscan, hemit]⟩
  | Split => exact ⟨[], .Split, by simp only [Hex1.decode1, hscan]⟩
  | Trailing => exact ⟨[], .Trailing, by simp only [Hex1.decode1, hscan]⟩
  | Unknown => exact ⟨[], .Unknown, by simp only [Hex1.decode1, hscan]⟩
  | Dup => exact ⟨[], .Dup, by simp only [Hex1.decode1, hscan]⟩
  | Undef => exact ⟨[], .Undef, by simp only [Hex1.decode1, hscan]⟩
  | TrailTok => exact ⟨[], .TrailTok, by simp only [Hex1.decode1, hscan]⟩

/-- Build a `Result1` for the OutputShort exit: the machine halted with
    `a0 = 2`, `a1 = 0`, while the whole-input scan stops past the capacity
    (`cap < m`), so `coreSpec1 = (2, [], 0)` whatever the final status. -/
theorem short_result1 (s : State) (inp : List Nat) (cap : Nat) (labf : Labels)
    (m : Nat) (stf : Hex1.Status) (hp : s.pc = 0)
    (ha0 : s.rget 10 = BitVec.ofNat 64 2) (ha1 : s.rget 11 = 0)
    (hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (labf, m, stf))
    (hlt : cap < m) :
    Result1 s inp cap := by
  obtain ⟨out, st', hdec⟩ := decode1_m inp labf m stf hscan
  have hcs : Hex1.coreSpec1 inp cap = (2, [], 0) := by
    simp only [Hex1.coreSpec1, hdec]
    rw [if_pos hlt]
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [hcs]; exact ha0
  · rw [hcs]; exact ha1
  · intro j hj
    rw [hcs] at hj
    simp at hj

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-1 percent dispatch (from offset 52, `t2 = 37`): the `li;beq`
    chain falls through `#`/`;`/`\n`/` `/`_`/`:` and branches to the
    label-reference block at 304. Touches only `t3` and `pc`. -/
theorem p1_pct_tail (s4 : State) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 52))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 37) :
    ∃ s', runFuel 0 14 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 304) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  -- block 1 (52): li t3,35; beq -- not taken
  have hb1 := li_beq_ne s4 52 35 37 (BitVec.ofNat 13 276) hcode hpc ht2 dec_52 dec_56
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 60))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (52 + 8))) := rfl
  try rw [← hv1] at hb1
  have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 60) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  -- block 2 (60): li t3,59; beq -- not taken
  have hb2 := li_beq_ne v1 60 59 37 (BitVec.ofNat 13 268) hc1 hpc1 ht2v1 dec_60 dec_64
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 68))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (60 + 8))) := rfl
  try rw [← hv2] at hb2
  have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 68) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  -- block 3 (68): li t3,10; beq -- not taken
  have hb3 := li_beq_ne v2 68 10 37 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_68 dec_72
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 76))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (68 + 8))) := rfl
  try rw [← hv3] at hb3
  have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 76) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  -- block 4 (76): li t3,32; beq -- not taken
  have hb4 := li_beq_ne v3 76 32 37 (BitVec.ofNat 13 8148) hc3 hpc3 ht2v3 dec_76 dec_80
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 84))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (76 + 8))) := rfl
  try rw [← hv4] at hb4
  have hc4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
  have hpc4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 84) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  -- block 5 (84): li t3,95; beq -- not taken
  have hb5 := li_beq_ne v4 84 95 37 (BitVec.ofNat 13 8140) hc4 hpc4 ht2v4 dec_84 dec_88
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 92))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (84 + 8))) := rfl
  try rw [← hv5] at hb5
  have hc5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc4)
  have hpc5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 92) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  -- block 6 (92): li t3,58; beq -- not taken
  have hb6 := li_beq_ne v5 92 58 37 (BitVec.ofNat 13 168) hc5 hpc5 ht2v5 dec_92 dec_96
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v6 := (v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 100))
  have hv6 : v6 = (v5.rset 28 (BitVec.ofNat 64 58)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (92 + 8))) := rfl
  try rw [← hv6] at hb6
  have hc6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc5)
  have hpc6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 100) := rfl
  have ht2v6 : v6.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v5
  -- block 7 (100): li t3,37; beq -- TAKEN to 304
  have hb7 := li_beq_eq v6 100 37 37 (BitVec.ofNat 13 200)
    (BitVec.ofNat 64 (Image1.coreAddr + 304)) hc6 hpc6 ht2v6 dec_100 dec_104
    (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
  refine ⟨(v6.rset 28 (BitVec.ofNat 64 37)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 304)),
    ?_, rfl, rfl, ?_⟩
  · rw [show (14:Nat) = 2 + (2 + (2 + (2 + (2 + (2 + 2))))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, runFuel_add, hb5,
        runFuel_add, hb6, hb7]
  · intro i hi
    rw [li_block_frame _ _ _ i hi, hv6, li_block_frame _ _ _ i hi, hv5,
        li_block_frame _ _ _ i hi, hv4, li_block_frame _ _ _ i hi, hv3,
        li_block_frame _ _ _ i hi, hv2, li_block_frame _ _ _ i hi, hv1,
        li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-1 iteration for a label reference (`%` then label byte):
    prefix + dispatch to 304 + the capacity check. Lands back at the loop
    head with `pos + 4` (suffix shorter by 2), or halts `Result1`: Short when
    the 4 offset bytes cross the capacity, TrailTok on EOF after `%`. -/
theorem p1_ref (inp : List Nat) (cap : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos (37 :: rest')) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ l rest2, rest' = l :: rest2 ∧
          P1Inv inp cap s' lab (pos + 4) rest2) ∨
        Result1 s' inp cap) := by
  have hlbl := inv.wf.lbl_fits
  have hin := inv.wf.in_fits
  have hout := inv.wf.out_fits
  have hcap63 := inv.wf.cap63
  have hlen64 : inp.length < 2 ^ 64 := by
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hin hout hlbl
    omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp 37 rest' inv.suffix
  -- machine: prefix (36..48), then dispatch to 304
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p1_prefix inp cap 37 rest' lab pos s inv
  obtain ⟨sd, hrund, hpcd, hmemd, hframed⟩ := p1_pct_tail s4 hcode4 hpc4 ht2
  have hcoded : CodeLoaded1 sd := by
    intro i hi
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi
  have hmem_sd : sd.mem = s.mem := by rw [hmemd, hmem4]
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  have h5d : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide)]; exact hidx4
  have h11d : sd.rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hframe_sd 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
  have hpd0 : sd.pc ≠ 0 := by rw [hpcd]; exact corePc_ne_zero 304 (by omega)
  cases rest' with
  | nil =>
    -- EOF after '%' -- bgeu taken to 712, TrailTok exit
    have h5d' : sd.rget 5 = BitVec.ofNat 64 inp.length := by simpa using h5d
    have hbt := bgeu_eq_taken sd 304 5 11 inp.length (BitVec.ofNat 13 408)
      (BitVec.ofNat 64 (Image1.coreAddr + 712)) hcoded hpcd h5d' h11d dec_304
      (by rw [coreBytes_len]; omega) (by decide)
    let sE := sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 712))
    have hsE : sE = sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 712)) := rfl
    try rw [← hsE] at hbt
    have hrunE : runFuel 0 1 sd = sE := by rw [runFuel_one sd hpd0, hbt]
    have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hcoded
    have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 712) := rfl
    have hraE : sE.rget 1 = 0 := by
      rw [hsE, Hex0.Refine.setPc_rget,
          hframe_sd 1 (by decide) (by decide) (by decide) (by decide)]
      exact inv.ra0
    obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
      exit_zero sE 712 8 hcodeE hpcE hraE dec_712 dec_716 dec_720 (by decide)
        (by rw [coreBytes_len]; omega)
    have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .TrailTok) := by
      rw [← inv.spec]
      rw [Hex1.scan1]
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
      rw [Hex1.scan1]
    refine ⟨4 + (14 + (1 + 3)), f, by omega, ?_, Or.inr ?_⟩
    · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunE, hrunf]
    · exact error_result1 f inp cap lab pos .TrailTok hfpc hfa0 hfa1 hscan
        (by decide) (by decide) inv.pos_le
  | cons l rest2 =>
    have hge2 : rest2.length + 2 ≤ inp.length := by
      have h := congrArg List.length inv.suffix
      simp only [List.length_drop, List.length_cons] at h
      omega
    have hidx1lt : inp.length - (l :: rest2).length < inp.length := by
      simp only [List.length_cons]; omega
    -- spec side: '%' consumes the label byte and advances pos by 4
    have hspec_pct : Hex1.scan1 .High lab pos (37 :: l :: rest2)
        = Hex1.scan1 .High lab (pos + 4) rest2 := by
      rw [Hex1.scan1]
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
      rw [Hex1.scan1]
    -- step 1 (304): bgeu t0,a1 -- NOT taken
    have hult : (sd.rget 5).ult (sd.rget 11) = true := by
      rw [h5d, h11d]; exact ult_ofNat _ _ hlen64 hidx1lt
    have hu1 : step sd = sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 308)) := by
      rw [step_bgeu sd 304 5 11 (BitVec.ofNat 13 408) hcoded (by rw [coreBytes_len]; omega)
          hpcd dec_304, hult]
      simp only [if_true]
      rw [show sd.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 308) from by
        rw [hpcd, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u1 := sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 308))
    have hsu1 : u1 = sd.setPc (BitVec.ofNat 64 (Image1.coreAddr + 308)) := rfl
    try rw [← hsu1] at hu1
    have hc1 : CodeLoaded1 u1 := codeLoaded1_setPc _ _ hcoded
    have hpc1 : u1.pc = BitVec.ofNat 64 (Image1.coreAddr + 308) := rfl
    have hq1 : u1.pc ≠ 0 := by rw [hpc1]; exact corePc_ne_zero 308 (by omega)
    -- step 2 (308): addi t0,t0,1 -- skip the label byte
    have hr5u1 : u1.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
      rw [hsu1, Hex0.Refine.setPc_rget]; exact h5d
    have hu2 : step u1 = (u1.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 312)) := by
      rw [step_addi u1 308 5 5 (BitVec.ofNat 12 1) hc1 (by rw [coreBytes_len]; omega)
          hpc1 dec_308,
          show u1.rget 5 + (BitVec.ofNat 12 1).signExtend 64
              = BitVec.ofNat 64 (inp.length - rest2.length) from by
            rw [hr5u1, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide,
                show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
            congr 1
            simp only [List.length_cons]
            omega,
          show u1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 312) from by
            rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u2 := (u1.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 312))
    have hsu2 : u2 = (u1.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 312)) := rfl
    try rw [← hsu2] at hu2
    have hc2 : CodeLoaded1 u2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : u2.pc = BitVec.ofNat 64 (Image1.coreAddr + 312) := rfl
    have hq2 : u2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 312 (by omega)
    -- step 3 (312): sub t3,a3,t1 -- remaining capacity
    have h13u2 : u2.rget 13 = BitVec.ofNat 64 cap := by
      rw [hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (13:Nat) ≠ 5), hsu1, Hex0.Refine.setPc_rget,
          hframe_sd 13 (by decide) (by decide) (by decide) (by decide)]
      exact inv.a3
    have h6u2 : u2.rget 6 = BitVec.ofNat 64 pos := by
      rw [hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (6:Nat) ≠ 5), hsu1, Hex0.Refine.setPc_rget,
          hframe_sd 6 (by decide) (by decide) (by decide) (by decide)]
      exact inv.outidx
    have hu3 : step u2 = (u2.rset 28 (BitVec.ofNat 64 (cap - pos))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 316)) := by
      rw [step_sub u2 312 28 13 6 hc2 (by rw [coreBytes_len]; omega) hpc2 dec_312,
          show u2.rget 13 - u2.rget 6 = BitVec.ofNat 64 (cap - pos) from by
            rw [h13u2, h6u2]
            exact sub_ofNat cap pos inv.pos_le (by omega),
          show u2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 316) from by
            rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u3 := (u2.rset 28 (BitVec.ofNat 64 (cap - pos))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 316))
    have hsu3 : u3 = (u2.rset 28 (BitVec.ofNat 64 (cap - pos))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 316)) := rfl
    try rw [← hsu3] at hu3
    have hc3 : CodeLoaded1 u3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : u3.pc = BitVec.ofNat 64 (Image1.coreAddr + 316) := rfl
    have hq3 : u3.pc ≠ 0 := by rw [hpc3]; exact corePc_ne_zero 316 (by omega)
    -- step 4 (316): li t4,4
    have hu4 : step u3 = (u3.rset 29 (BitVec.ofNat 64 4)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 320)) := by
      rw [step_addi u3 316 29 0 (BitVec.ofNat 12 4) hc3 (by rw [coreBytes_len]; omega)
          hpc3 dec_316,
          show u3.rget 0 + (BitVec.ofNat 12 4).signExtend 64 = BitVec.ofNat 64 4 from by
            rw [Hex0.Refine.rget_zero,
                show ((BitVec.ofNat 12 4).signExtend 64) = BitVec.ofNat 64 4 from by decide]
            simp,
          show u3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 320) from by
            rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    let u4 := (u3.rset 29 (BitVec.ofNat 64 4)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 320))
    have hsu4 : u4 = (u3.rset 29 (BitVec.ofNat 64 4)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 320)) := rfl
    try rw [← hsu4] at hu4
    have hc4 : CodeLoaded1 u4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
    have hpc4u : u4.pc = BitVec.ofNat 64 (Image1.coreAddr + 320) := rfl
    have hq4 : u4.pc ≠ 0 := by rw [hpc4u]; exact corePc_ne_zero 320 (by omega)
    have hrun4b : runFuel 0 4 sd = u4 := by
      simp only [runFuel]
      rw [hu1, hu2, hu3, hu4, if_neg hpd0, if_neg hq1, if_neg hq2, if_neg hq3]
    have h28u4 : u4.rget 28 = BitVec.ofNat 64 (cap - pos) := by
      rw [hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (28:Nat) ≠ 29), hsu3, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have h29u4 : u4.rget 29 = BitVec.ofNat 64 4 := by
      rw [hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    -- step 5 (320): blt t3,t4 -- the capacity test
    by_cases hshort : cap < pos + 4
    · -- SHORT: cap - pos < 4, branch to 640
      have hcond : (u4.rget 28).slt (u4.rget 29) = true := by
        rw [h28u4, h29u4, slt_ofNat _ _ (by omega) (by omega)]
        exact decide_eq_true (by omega)
      have hu5 : step u4 = u4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 640)) := by
        rw [step_blt u4 320 28 29 (BitVec.ofNat 13 320) hc4 (by rw [coreBytes_len]; omega)
            hpc4u dec_320, hcond]
        simp only [if_true]
        rw [show u4.pc + (BitVec.ofNat 13 320).signExtend 64
            = BitVec.ofNat 64 (Image1.coreAddr + 640) from by rw [hpc4u]; decide]
      let sE := u4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 640))
      have hsE : sE = u4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 640)) := rfl
      try rw [← hsE] at hu5
      have hrunE : runFuel 0 1 u4 = sE := by rw [runFuel_one u4 hq4, hu5]
      have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hc4
      have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 640) := rfl
      have hraE : sE.rget 1 = 0 := by
        rw [hsE, Hex0.Refine.setPc_rget, hsu4, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (1:Nat) ≠ 29)]
        rw [show u3.rget 1 = u2.rget 1 from by
              rw [hsu3, li_block_frame _ _ _ 1 (by decide)],
            hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (1:Nat) ≠ 5), hsu1, Hex0.Refine.setPc_rget,
            hframe_sd 1 (by decide) (by decide) (by decide) (by decide)]
        exact inv.ra0
      obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
        exit_zero sE 640 2 hcodeE hpcE hraE dec_640 dec_644 dec_648 (by decide)
          (by rw [coreBytes_len]; omega)
      obtain ⟨labf, mres, stf, hres⟩ : ∃ labf mres stf,
          Hex1.scan1 .High lab (pos + 4) rest2 = (labf, mres, stf) :=
        ⟨_, _, _, rfl⟩
      have hmono : pos + 4 ≤ mres := by
        have h := scan1_pos_le rest2.length .High lab (pos + 4) rest2 (Nat.le_refl _)
        rw [hres] at h
        exact h
      have hscan_inp : Hex1.scan1 .High Hex1.noLabels 0 inp = (labf, mres, stf) := by
        rw [← inv.spec, hspec_pct, hres]
      refine ⟨4 + (14 + (4 + (1 + 3))), f, by omega, ?_, Or.inr ?_⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrun4b,
            runFuel_add, hrunE, hrunf]
      · exact short_result1 f inp cap labf mres stf hfpc hfa0 hfa1 hscan_inp (by omega)
    · -- room for the 4 offset bytes: fall through, bump pos, loop back
      have hcond : (u4.rget 28).slt (u4.rget 29) = false := by
        rw [h28u4, h29u4, slt_ofNat _ _ (by omega) (by omega)]
        exact decide_eq_false (by omega)
      have hu5 : step u4 = u4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 324)) := by
        rw [step_blt u4 320 28 29 (BitVec.ofNat 13 320) hc4 (by rw [coreBytes_len]; omega)
            hpc4u dec_320, hcond]
        simp only [Bool.false_eq_true, if_false]
        rw [show u4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 324) from by
          rw [hpc4u, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
      let u5 := u4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 324))
      have hsu5 : u5 = u4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 324)) := rfl
      try rw [← hsu5] at hu5
      have hc5 : CodeLoaded1 u5 := codeLoaded1_setPc _ _ hc4
      have hpc5 : u5.pc = BitVec.ofNat 64 (Image1.coreAddr + 324) := rfl
      have hq5 : u5.pc ≠ 0 := by rw [hpc5]; exact corePc_ne_zero 324 (by omega)
      -- step 6 (324): addi t1,t1,4
      have h6u5 : u5.rget 6 = BitVec.ofNat 64 pos := by
        rw [hsu5, Hex0.Refine.setPc_rget, hsu4, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat) ≠ 29)]
        rw [show u3.rget 6 = u2.rget 6 from by
              rw [hsu3, li_block_frame _ _ _ 6 (by decide)]]
        exact h6u2
      have hu6 : step u5 = (u5.rset 6 (BitVec.ofNat 64 (pos + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 328)) := by
        rw [step_addi u5 324 6 6 (BitVec.ofNat 12 4) hc5 (by rw [coreBytes_len]; omega)
            hpc5 dec_324,
            show u5.rget 6 + (BitVec.ofNat 12 4).signExtend 64
                = BitVec.ofNat 64 (pos + 4) from by
              rw [h6u5, show ((BitVec.ofNat 12 4).signExtend 64) = BitVec.ofNat 64 4 from by
                    decide,
                  addr_ofNat_succ],
            show u5.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 328) from by
              rw [hpc5, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
      let u6 := (u5.rset 6 (BitVec.ofNat 64 (pos + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 328))
      have hsu6 : u6 = (u5.rset 6 (BitVec.ofNat 64 (pos + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 328)) := rfl
      try rw [← hsu6] at hu6
      have hc6 : CodeLoaded1 u6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc5)
      have hpc6 : u6.pc = BitVec.ofNat 64 (Image1.coreAddr + 328) := rfl
      have hq6 : u6.pc ≠ 0 := by rw [hpc6]; exact corePc_ne_zero 328 (by omega)
      -- step 7 (328): j 36 -- back to the loop head
      have hu7 : step u6 = u6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := by
        rw [step_jal u6 328 0 (BitVec.ofNat 21 2096860) hc6 (by rw [coreBytes_len]; omega)
            hpc6 dec_328, rset_zero,
            show u6.pc + (BitVec.ofNat 21 2096860).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 36) from by rw [hpc6]; decide]
      let sF := u6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36))
      have hsF : sF = u6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := rfl
      try rw [← hsF] at hu7
      have hrunF : runFuel 0 3 u4 = sF := by
        simp only [runFuel]
        rw [hu5, hu6, hu7, if_neg hq4, if_neg hq5, if_neg hq6]
      have hmemF : sF.mem = s.mem := by
        rw [hsF, hsu6, hsu5, hsu4, hsu3, hsu2, hsu1]
        simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
        exact hmem_sd
      have hregF : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 28 → i ≠ 29 →
          sF.rget i = s.rget i := by
        intro i h0 h5i h6i h7i h28i h29i
        rw [hsF, Hex0.Refine.setPc_rget, hsu6, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) h0, if_neg h6i,
            hsu5, Hex0.Refine.setPc_rget,
            hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
            hsu3, li_block_frame _ _ _ i h28i,
            hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5i,
            hsu1, Hex0.Refine.setPc_rget]
        exact hframe_sd i h0 h5i h7i h28i
      have h5sF : sF.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
        rw [hsF, Hex0.Refine.setPc_rget, hsu6, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 6),
            hsu5, Hex0.Refine.setPc_rget,
            hsu4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsu3, li_block_frame _ _ _ 5 (by decide),
            hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      have h6sF : sF.rget 6 = BitVec.ofNat 64 (pos + 4) := by
        rw [hsF, Hex0.Refine.setPc_rget, hsu6, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      refine ⟨4 + (14 + (4 + 3)), sF, by omega, ?_, Or.inl ⟨l, rest2, rfl, ?_⟩⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrun4b, hrunF]
      · exact {
          wf := inv.wf
          at_loop := rfl
          code := by
            intro i hi
            rw [hmemF]
            exact inv.code i hi
          a0 := by
            rw [hregF 10 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.a0
          a1 := by
            rw [hregF 11 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.a1
          a2 := by
            rw [hregF 12 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.a2
          a3 := by
            rw [hregF 13 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.a3
          a4 := by
            rw [hregF 14 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.a4
          ra0 := by
            rw [hregF 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.ra0
          in_mem := by
            intro j hj
            rw [hmemF]
            exact inv.in_mem j hj
          idx := h5sF
          suffix := suffix_step inp l rest2 hrest'_eq
          outidx := h6sF
          pos_le := by omega
          tbl := by
            intro c hc k hk
            rw [hmemF]
            exact inv.tbl c hc k hk
          lab_le := by
            intro c p h
            have := inv.lab_le c p h
            omega
          spec := by
            rw [← hspec_pct]
            exact inv.spec }


/-! ## Pass-1 iteration: byte tokens -- the range-check chains.
    Pass 1 validates nibbles but computes no values; every block below
    touches only `t3` and `pc`. -/


set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The full pass-1 dispatch fall-through (52..104): a non-special char
    reaches the high-nibble check at 108. Touches only `t3` and `pc`. -/
theorem p1_fall_tail (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 52))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc64 : c < 2 ^ 64)
    (hne : c ≠ 35 ∧ c ≠ 59 ∧ c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 ∧ c ≠ 58 ∧ c ≠ 37) :
    ∃ s', runFuel 0 14 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 108) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  obtain ⟨h35, h59, h10n, h32, h95, h58, h37⟩ := hne
  have hb1 := li_beq_ne s4 52 35 c (BitVec.ofNat 13 276) hcode hpc ht2 dec_52 dec_56
    (by decide) (ofNat_ne c 35 hc64 (by decide) h35) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 60))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (52 + 8))) := rfl
  try rw [← hv1] at hb1
  have hcv1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpcv1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 60) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  have hb2 := li_beq_ne v1 60 59 c (BitVec.ofNat 13 268) hcv1 hpcv1 ht2v1 dec_60 dec_64
    (by decide) (ofNat_ne c 59 hc64 (by decide) h59) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 68))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (60 + 8))) := rfl
  try rw [← hv2] at hb2
  have hcv2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv1)
  have hpcv2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 68) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have hb3 := li_beq_ne v2 68 10 c (BitVec.ofNat 13 8156) hcv2 hpcv2 ht2v2 dec_68 dec_72
    (by decide) (ofNat_ne c 10 hc64 (by decide) h10n) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 76))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (68 + 8))) := rfl
  try rw [← hv3] at hb3
  have hcv3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv2)
  have hpcv3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 76) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  have hb4 := li_beq_ne v3 76 32 c (BitVec.ofNat 13 8148) hcv3 hpcv3 ht2v3 dec_76 dec_80
    (by decide) (ofNat_ne c 32 hc64 (by decide) h32) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 84))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (76 + 8))) := rfl
  try rw [← hv4] at hb4
  have hcv4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv3)
  have hpcv4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 84) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 c := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  have hb5 := li_beq_ne v4 84 95 c (BitVec.ofNat 13 8140) hcv4 hpcv4 ht2v4 dec_84 dec_88
    (by decide) (ofNat_ne c 95 hc64 (by decide) h95) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 92))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (84 + 8))) := rfl
  try rw [← hv5] at hb5
  have hcv5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv4)
  have hpcv5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 92) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 c := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  have hb6 := li_beq_ne v5 92 58 c (BitVec.ofNat 13 168) hcv5 hpcv5 ht2v5 dec_92 dec_96
    (by decide) (ofNat_ne c 58 hc64 (by decide) h58) (by rw [coreBytes_len]; omega)
  let v6 := (v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 100))
  have hv6 : v6 = (v5.rset 28 (BitVec.ofNat 64 58)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (92 + 8))) := rfl
  try rw [← hv6] at hb6
  have hcv6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv5)
  have hpcv6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 100) := rfl
  have ht2v6 : v6.rget 7 = BitVec.ofNat 64 c := by
    rw [hv6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v5
  have hb7 := li_beq_ne v6 100 37 c (BitVec.ofNat 13 200) hcv6 hpcv6 ht2v6 dec_100 dec_104
    (by decide) (ofNat_ne c 37 hc64 (by decide) h37) (by rw [coreBytes_len]; omega)
  let vF := (v6.rset 28 (BitVec.ofNat 64 37)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 108))
  have hvF : vF = (v6.rset 28 (BitVec.ofNat 64 37)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (100 + 8))) := rfl
  try rw [← hvF] at hb7
  refine ⟨vF, ?_, rfl, rfl, ?_⟩
  · rw [show (14:Nat) = 2 + (2 + (2 + (2 + (2 + (2 + (2)))))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2,
        runFuel_add, hb3,
        runFuel_add, hb4,
        runFuel_add, hb5,
        runFuel_add, hb6,
        hb7]
  · intro i hi
    rw [hvF, li_block_frame _ _ _ i hi, hv6,
        li_block_frame _ _ _ i hi, hv5,
        li_block_frame _ _ _ i hi, hv4,
        li_block_frame _ _ _ i hi, hv3,
        li_block_frame _ _ _ i hi, hv2,
        li_block_frame _ _ _ i hi, hv1,
        li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- High-nibble range check (offsets 108..140), valid case: a hex digit
    falls through to the low-char read at 144. -/
theorem p1_high_ok (s4 : State) (c hi : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 108))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc256 : c < 256)
    (hn : Hex0.nibble c = some hi) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 144) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hc63 : c < 2 ^ 63 := by omega
  have hcase : (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · exact Or.inl hd
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · exact Or.inr hl
      · rw [if_neg hl] at hn
        exact absurd hn (by simp)
  rcases hcase with ⟨h48, h57⟩ | ⟨h65, h70⟩
  · -- digit '0'..'9'
    have bA := li_blt_nt s4 108 48 c (BitVec.ofNat 13 564) hcode hpc ht2 dec_108 dec_112
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 116))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (108 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 116) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_nt v1 116 58 c (BitVec.ofNat 13 8) hc1 hpc1 ht2v1 dec_116 dec_120
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 124))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (116 + 8))) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 124) := rfl
    have hq2 : v2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 124 (by omega)
    have hjal : step v2 = v2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 144)) := by
      rw [step_jal v2 124 0 (BitVec.ofNat 21 20) hc2 (by rw [coreBytes_len]; omega)
          hpc2 dec_124, rset_zero,
          show v2.pc + (BitVec.ofNat 21 20).signExtend 64
              = BitVec.ofNat 64 (Image1.coreAddr + 144) from by rw [hpc2]; decide]
    refine ⟨2 + (2 + 1), v2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 144)), ?_,
      by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_one _ hq2, hjal]
    · intro i hi
      rw [Hex0.Refine.setPc_rget, hv2, li_block_frame _ _ _ i hi, hv1,
          li_block_frame _ _ _ i hi]
  · -- letter 'A'..'F'
    have bA := li_blt_nt s4 108 48 c (BitVec.ofNat 13 564) hcode hpc ht2 dec_108 dec_112
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 116))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (108 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 116) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_t v1 116 58 c (BitVec.ofNat 13 8)
      (BitVec.ofNat 64 (Image1.coreAddr + 128)) hc1 hpc1 ht2v1 dec_116 dec_120
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 128))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 128)) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 128) := rfl
    have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
      rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v1
    have bC := li_blt_nt v2 128 65 c (BitVec.ofNat 13 544) hc2 hpc2 ht2v2 dec_128 dec_132
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 136))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 65)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (128 + 8))) := rfl
    try rw [← hv3] at bC
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 136) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have bD := li_bge_nt v3 136 71 c (BitVec.ofNat 13 536) hc3 hpc3 ht2v3 dec_136 dec_140
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let vF := (v3.rset 28 (BitVec.ofNat 64 71)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 144))
    have hvF : vF = (v3.rset 28 (BitVec.ofNat 64 71)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (136 + 8))) := rfl
    try rw [← hvF] at bD
    refine ⟨2 + (2 + (2 + 2)), vF, ?_, by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]
    · intro i hi
      rw [hvF, li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi, hv2,
          li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- High-nibble range check (offsets 108..140), invalid case: branches to
    the Unknown exit at 676. -/
theorem p1_high_unk (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 108))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc256 : c < 256)
    (hn : Hex0.nibble c = none) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 676) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hc63 : c < 2 ^ 63 := by omega
  have hcase : c < 48 ∨ (58 ≤ c ∧ c < 65) ∨ 71 ≤ c := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn; exact absurd hn (by simp)
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn; exact absurd hn (by simp)
      · omega
  rcases hcase with h48 | ⟨h58, h65⟩ | h71
  · have bA := li_blt_t s4 108 48 c (BitVec.ofNat 13 564)
      (BitVec.ofNat 64 (Image1.coreAddr + 676)) hcode hpc ht2 dec_108 dec_112
      (by decide) h48 hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    exact ⟨2, (s4.rset 28 (BitVec.ofNat 64 48)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 676)), bA, by omega, rfl, rfl,
      fun i hi => li_block_frame _ _ _ i hi⟩
  · have bA := li_blt_nt s4 108 48 c (BitVec.ofNat 13 564) hcode hpc ht2 dec_108 dec_112
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 116))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (108 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 116) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_t v1 116 58 c (BitVec.ofNat 13 8)
      (BitVec.ofNat 64 (Image1.coreAddr + 128)) hc1 hpc1 ht2v1 dec_116 dec_120
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 128))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 128)) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 128) := rfl
    have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
      rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v1
    have bC := li_blt_t v2 128 65 c (BitVec.ofNat 13 544)
      (BitVec.ofNat 64 (Image1.coreAddr + 676)) hc2 hpc2 ht2v2 dec_128 dec_132
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨2 + (2 + 2), (v2.rset 28 (BitVec.ofNat 64 65)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 676)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, bC]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv2, li_block_frame _ _ _ i hi, hv1,
          li_block_frame _ _ _ i hi]
  · have bA := li_blt_nt s4 108 48 c (BitVec.ofNat 13 564) hcode hpc ht2 dec_108 dec_112
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 116))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (108 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 116) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_t v1 116 58 c (BitVec.ofNat 13 8)
      (BitVec.ofNat 64 (Image1.coreAddr + 128)) hc1 hpc1 ht2v1 dec_116 dec_120
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 128))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 128)) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 128) := rfl
    have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
      rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v1
    have bC := li_blt_nt v2 128 65 c (BitVec.ofNat 13 544) hc2 hpc2 ht2v2 dec_128 dec_132
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 136))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 65)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (128 + 8))) := rfl
    try rw [← hv3] at bC
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 136) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have bD := li_bge_t v3 136 71 c (BitVec.ofNat 13 536)
      (BitVec.ofNat 64 (Image1.coreAddr + 676)) hc3 hpc3 ht2v3 dec_136 dec_140
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨2 + (2 + (2 + 2)), (v3.rset 28 (BitVec.ofNat 64 71)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 676)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi, hv2,
          li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The low-char read (offsets 144..156): `bgeu`(not taken) → `add` → `lbu`
    (read char `l` at `idx`) → `addi` (bump index). Lands at offset 160 with
    `t2 = l`. -/
theorem p1_low_read (s : State) (inp : List Nat) (l idx : Nat)
    (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 144))
    (h5 : s.rget 5 = BitVec.ofNat 64 idx)
    (h10 : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr)
    (h11 : s.rget 11 = BitVec.ofNat 64 inp.length)
    (hin : InputLoaded s inp)
    (hidx : idx < inp.length) (hlen64 : inp.length < 2 ^ 64)
    (hgetl : inp.getD idx 0 = l) (hl256 : l < 256) :
    ∃ s4, runFuel 0 4 s = s4 ∧
      s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 160) ∧
      s4.rget 7 = BitVec.ofNat 64 l ∧
      s4.rget 5 = BitVec.ofNat 64 (idx + 1) ∧
      s4.mem = s.mem ∧ CodeLoaded1 s4 ∧
      (∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s4.rget i = s.rget i) := by
  -- step 1: bgeu t0,a1 -- NOT taken (idx < len)
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [h5, h11]; exact ult_ofNat _ _ hlen64 hidx
  have hu1 : step s = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 148)) := by
    rw [step_bgeu s 144 5 11 (BitVec.ofNat 13 520) hcode (by rw [coreBytes_len]; omega)
        hpc dec_144, hult]
    simp only [if_true]
    rw [show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 148) from by
      rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s1 := s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 148))
  have hs1 : s1 = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 148)) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ hcode
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 148) := rfl
  -- step 2: add t3,a0,t0
  have haddr : s1.rget 10 + s1.rget 5 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    show s.rget 10 + s.rget 5 = _
    rw [h10, h5]; exact addr_ofNat_succ _ _
  have hu2 : step s1 = (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 152)) := by
    rw [step_add s1 148 28 10 5 hc1 (by rw [coreBytes_len]; omega) hpc1 dec_148, haddr,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 152) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s2 := (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 152))
  have hs2 : s2 = (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 152)) := rfl
  try rw [← hs2] at hu2
  have hc2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 152) := rfl
  -- step 3: lbu t2,0(t3)
  have hr28 : s2.rget 28 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hbyte : (s2.loadByte (s2.rget 28 + (0#12).signExtend 64)).setWidth 64
      = BitVec.ofNat 64 l := by
    rw [hr28, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
    show (s2.mem _).setWidth 64 = _
    rw [hs2]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem, hs1]
    rw [hin _ hidx, hgetl, setWidth8_64 l hl256]
  have hu3 : step s2 = (s2.rset 7 (BitVec.ofNat 64 l)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 156)) := by
    rw [step_lbu s2 152 7 28 (0#12) hc2 (by rw [coreBytes_len]; omega) hpc2 dec_152]
    rw [show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 156) from by
      rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    rw [hbyte]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 l)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 156))
  have hs3 : s3 = (s2.rset 7 (BitVec.ofNat 64 l)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 156)) := rfl
  try rw [← hs3] at hu3
  have hc3 : CodeLoaded1 s3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 156) := rfl
  have hr5_3 : s3.rget 5 = s.rget 5 := by
    rw [hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 7), hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28),
        hs1, Hex0.Refine.setPc_rget]
  -- step 4: addi t0,t0,1
  have hu4 : step s3 = (s3.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 160)) := by
    rw [step_addi s3 156 5 5 (BitVec.ofNat 12 1) hc3 (by rw [coreBytes_len]; omega) hpc3 dec_156,
        show s3.rget 5 + (BitVec.ofNat 12 1).signExtend 64
            = BitVec.ofNat 64 (idx + 1) from by
          rw [hr5_3, h5, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide,
              show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ],
        show s3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 160) from by
          rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s4 := (s3.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 160))
  have hs4 : s4 = (s3.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 160)) := rfl
  try rw [← hs4] at hu4
  have hp0 : s.pc ≠ 0 := by rw [hpc]; exact corePc_ne_zero 144 (by omega)
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; exact corePc_ne_zero 148 (by omega)
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 152 (by omega)
  have hp3 : s3.pc ≠ 0 := by rw [hpc3]; exact corePc_ne_zero 156 (by omega)
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
  · intro i h0 h5i h7 h28
    rw [hs4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5i,
        hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7,
        hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28,
        hs1, Hex0.Refine.setPc_rget]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The low-stop chain (offsets 160..212), match case: a stop char after a
    high nibble branches to the Split exit at 652. -/
theorem p1_stop_split (s4 : State) (l : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 160))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 l)
    (hls : Hex1.isLowStop l = true) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 652) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hmem : l = 10 ∨ l = 32 ∨ l = 95 ∨ l = 35 ∨ l = 59 ∨ l = 58 ∨ l = 37 := by
    simp only [Hex1.isLowStop, Hex0.isLowStop, Hex0.isSpace, Hex0.isComment, Hex0.c_nl,
      Hex0.c_sp, Hex0.c_us, Hex0.c_hash, Hex0.c_semi, Hex1.c_colon, Hex1.c_pct,
      Bool.or_eq_true, beq_iff_eq] at hls
    omega
  rcases hmem with h | h | h | h | h | h | h
  · subst h
    have hbe := li_beq_eq s4 160 10 10 (BitVec.ofNat 13 488)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcode hpc ht2 dec_160 dec_164
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨2, (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · exact hbe
    · intro i hi
      rw [li_block_frame _ _ _ i hi]
  · subst h
    have hb1 := li_beq_ne s4 160 10 32 (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
    try rw [← hw1] at hb1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
    have ht2w1 : w1.rget 7 = BitVec.ofNat 64 32 := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hbe := li_beq_eq w1 168 32 32 (BitVec.ofNat 13 480)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcw1 hpcw1 ht2w1 dec_168 dec_172
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨4, (w1.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (4:Nat) = 2 + (2) from rfl, runFuel_add, hb1,
          hbe]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hw1,
          li_block_frame _ _ _ i hi]
  · subst h
    have hb1 := li_beq_ne s4 160 10 95 (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
    try rw [← hw1] at hb1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
    have ht2w1 : w1.rget 7 = BitVec.ofNat 64 95 := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hb2 := li_beq_ne w1 168 32 95 (BitVec.ofNat 13 480) hcw1 hpcw1 ht2w1 dec_168 dec_172
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w2 := (w1.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 176))
    have hw2 : w2 = (w1.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (168 + 8))) := rfl
    try rw [← hw2] at hb2
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 176) := rfl
    have ht2w2 : w2.rget 7 = BitVec.ofNat 64 95 := by
      rw [hw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w1
    have hbe := li_beq_eq w2 176 95 95 (BitVec.ofNat 13 472)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcw2 hpcw2 ht2w2 dec_176 dec_180
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨6, (w2.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (6:Nat) = 2 + (2 + (2)) from rfl, runFuel_add, hb1,
          runFuel_add, hb2,
          hbe]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hw2,
          li_block_frame _ _ _ i hi, hw1,
          li_block_frame _ _ _ i hi]
  · subst h
    have hb1 := li_beq_ne s4 160 10 35 (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
    try rw [← hw1] at hb1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
    have ht2w1 : w1.rget 7 = BitVec.ofNat 64 35 := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hb2 := li_beq_ne w1 168 32 35 (BitVec.ofNat 13 480) hcw1 hpcw1 ht2w1 dec_168 dec_172
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w2 := (w1.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 176))
    have hw2 : w2 = (w1.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (168 + 8))) := rfl
    try rw [← hw2] at hb2
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 176) := rfl
    have ht2w2 : w2.rget 7 = BitVec.ofNat 64 35 := by
      rw [hw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w1
    have hb3 := li_beq_ne w2 176 95 35 (BitVec.ofNat 13 472) hcw2 hpcw2 ht2w2 dec_176 dec_180
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w3 := (w2.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 184))
    have hw3 : w3 = (w2.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (176 + 8))) := rfl
    try rw [← hw3] at hb3
    have hcw3 : CodeLoaded1 w3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw2)
    have hpcw3 : w3.pc = BitVec.ofNat 64 (Image1.coreAddr + 184) := rfl
    have ht2w3 : w3.rget 7 = BitVec.ofNat 64 35 := by
      rw [hw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w2
    have hbe := li_beq_eq w3 184 35 35 (BitVec.ofNat 13 464)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcw3 hpcw3 ht2w3 dec_184 dec_188
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨8, (w3.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (8:Nat) = 2 + (2 + (2 + (2))) from rfl, runFuel_add, hb1,
          runFuel_add, hb2,
          runFuel_add, hb3,
          hbe]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hw3,
          li_block_frame _ _ _ i hi, hw2,
          li_block_frame _ _ _ i hi, hw1,
          li_block_frame _ _ _ i hi]
  · subst h
    have hb1 := li_beq_ne s4 160 10 59 (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
    try rw [← hw1] at hb1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
    have ht2w1 : w1.rget 7 = BitVec.ofNat 64 59 := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hb2 := li_beq_ne w1 168 32 59 (BitVec.ofNat 13 480) hcw1 hpcw1 ht2w1 dec_168 dec_172
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w2 := (w1.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 176))
    have hw2 : w2 = (w1.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (168 + 8))) := rfl
    try rw [← hw2] at hb2
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 176) := rfl
    have ht2w2 : w2.rget 7 = BitVec.ofNat 64 59 := by
      rw [hw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w1
    have hb3 := li_beq_ne w2 176 95 59 (BitVec.ofNat 13 472) hcw2 hpcw2 ht2w2 dec_176 dec_180
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w3 := (w2.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 184))
    have hw3 : w3 = (w2.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (176 + 8))) := rfl
    try rw [← hw3] at hb3
    have hcw3 : CodeLoaded1 w3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw2)
    have hpcw3 : w3.pc = BitVec.ofNat 64 (Image1.coreAddr + 184) := rfl
    have ht2w3 : w3.rget 7 = BitVec.ofNat 64 59 := by
      rw [hw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w2
    have hb4 := li_beq_ne w3 184 35 59 (BitVec.ofNat 13 464) hcw3 hpcw3 ht2w3 dec_184 dec_188
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w4 := (w3.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 192))
    have hw4 : w4 = (w3.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (184 + 8))) := rfl
    try rw [← hw4] at hb4
    have hcw4 : CodeLoaded1 w4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw3)
    have hpcw4 : w4.pc = BitVec.ofNat 64 (Image1.coreAddr + 192) := rfl
    have ht2w4 : w4.rget 7 = BitVec.ofNat 64 59 := by
      rw [hw4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w3
    have hbe := li_beq_eq w4 192 59 59 (BitVec.ofNat 13 456)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcw4 hpcw4 ht2w4 dec_192 dec_196
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨10, (w4.rset 28 (BitVec.ofNat 64 59)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (10:Nat) = 2 + (2 + (2 + (2 + (2)))) from rfl, runFuel_add, hb1,
          runFuel_add, hb2,
          runFuel_add, hb3,
          runFuel_add, hb4,
          hbe]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hw4,
          li_block_frame _ _ _ i hi, hw3,
          li_block_frame _ _ _ i hi, hw2,
          li_block_frame _ _ _ i hi, hw1,
          li_block_frame _ _ _ i hi]
  · subst h
    have hb1 := li_beq_ne s4 160 10 58 (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
    try rw [← hw1] at hb1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
    have ht2w1 : w1.rget 7 = BitVec.ofNat 64 58 := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hb2 := li_beq_ne w1 168 32 58 (BitVec.ofNat 13 480) hcw1 hpcw1 ht2w1 dec_168 dec_172
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w2 := (w1.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 176))
    have hw2 : w2 = (w1.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (168 + 8))) := rfl
    try rw [← hw2] at hb2
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 176) := rfl
    have ht2w2 : w2.rget 7 = BitVec.ofNat 64 58 := by
      rw [hw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w1
    have hb3 := li_beq_ne w2 176 95 58 (BitVec.ofNat 13 472) hcw2 hpcw2 ht2w2 dec_176 dec_180
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w3 := (w2.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 184))
    have hw3 : w3 = (w2.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (176 + 8))) := rfl
    try rw [← hw3] at hb3
    have hcw3 : CodeLoaded1 w3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw2)
    have hpcw3 : w3.pc = BitVec.ofNat 64 (Image1.coreAddr + 184) := rfl
    have ht2w3 : w3.rget 7 = BitVec.ofNat 64 58 := by
      rw [hw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w2
    have hb4 := li_beq_ne w3 184 35 58 (BitVec.ofNat 13 464) hcw3 hpcw3 ht2w3 dec_184 dec_188
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w4 := (w3.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 192))
    have hw4 : w4 = (w3.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (184 + 8))) := rfl
    try rw [← hw4] at hb4
    have hcw4 : CodeLoaded1 w4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw3)
    have hpcw4 : w4.pc = BitVec.ofNat 64 (Image1.coreAddr + 192) := rfl
    have ht2w4 : w4.rget 7 = BitVec.ofNat 64 58 := by
      rw [hw4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w3
    have hb5 := li_beq_ne w4 192 59 58 (BitVec.ofNat 13 456) hcw4 hpcw4 ht2w4 dec_192 dec_196
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w5 := (w4.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 200))
    have hw5 : w5 = (w4.rset 28 (BitVec.ofNat 64 59)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (192 + 8))) := rfl
    try rw [← hw5] at hb5
    have hcw5 : CodeLoaded1 w5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw4)
    have hpcw5 : w5.pc = BitVec.ofNat 64 (Image1.coreAddr + 200) := rfl
    have ht2w5 : w5.rget 7 = BitVec.ofNat 64 58 := by
      rw [hw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w4
    have hbe := li_beq_eq w5 200 58 58 (BitVec.ofNat 13 448)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcw5 hpcw5 ht2w5 dec_200 dec_204
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨12, (w5.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (12:Nat) = 2 + (2 + (2 + (2 + (2 + (2))))) from rfl, runFuel_add, hb1,
          runFuel_add, hb2,
          runFuel_add, hb3,
          runFuel_add, hb4,
          runFuel_add, hb5,
          hbe]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hw5,
          li_block_frame _ _ _ i hi, hw4,
          li_block_frame _ _ _ i hi, hw3,
          li_block_frame _ _ _ i hi, hw2,
          li_block_frame _ _ _ i hi, hw1,
          li_block_frame _ _ _ i hi]
  · subst h
    have hb1 := li_beq_ne s4 160 10 37 (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
    try rw [← hw1] at hb1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
    have ht2w1 : w1.rget 7 = BitVec.ofNat 64 37 := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hb2 := li_beq_ne w1 168 32 37 (BitVec.ofNat 13 480) hcw1 hpcw1 ht2w1 dec_168 dec_172
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w2 := (w1.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 176))
    have hw2 : w2 = (w1.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (168 + 8))) := rfl
    try rw [← hw2] at hb2
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 176) := rfl
    have ht2w2 : w2.rget 7 = BitVec.ofNat 64 37 := by
      rw [hw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w1
    have hb3 := li_beq_ne w2 176 95 37 (BitVec.ofNat 13 472) hcw2 hpcw2 ht2w2 dec_176 dec_180
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w3 := (w2.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 184))
    have hw3 : w3 = (w2.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (176 + 8))) := rfl
    try rw [← hw3] at hb3
    have hcw3 : CodeLoaded1 w3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw2)
    have hpcw3 : w3.pc = BitVec.ofNat 64 (Image1.coreAddr + 184) := rfl
    have ht2w3 : w3.rget 7 = BitVec.ofNat 64 37 := by
      rw [hw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w2
    have hb4 := li_beq_ne w3 184 35 37 (BitVec.ofNat 13 464) hcw3 hpcw3 ht2w3 dec_184 dec_188
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w4 := (w3.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 192))
    have hw4 : w4 = (w3.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (184 + 8))) := rfl
    try rw [← hw4] at hb4
    have hcw4 : CodeLoaded1 w4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw3)
    have hpcw4 : w4.pc = BitVec.ofNat 64 (Image1.coreAddr + 192) := rfl
    have ht2w4 : w4.rget 7 = BitVec.ofNat 64 37 := by
      rw [hw4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w3
    have hb5 := li_beq_ne w4 192 59 37 (BitVec.ofNat 13 456) hcw4 hpcw4 ht2w4 dec_192 dec_196
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w5 := (w4.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 200))
    have hw5 : w5 = (w4.rset 28 (BitVec.ofNat 64 59)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (192 + 8))) := rfl
    try rw [← hw5] at hb5
    have hcw5 : CodeLoaded1 w5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw4)
    have hpcw5 : w5.pc = BitVec.ofNat 64 (Image1.coreAddr + 200) := rfl
    have ht2w5 : w5.rget 7 = BitVec.ofNat 64 37 := by
      rw [hw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w4
    have hb6 := li_beq_ne w5 200 58 37 (BitVec.ofNat 13 448) hcw5 hpcw5 ht2w5 dec_200 dec_204
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w6 := (w5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 208))
    have hw6 : w6 = (w5.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (200 + 8))) := rfl
    try rw [← hw6] at hb6
    have hcw6 : CodeLoaded1 w6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw5)
    have hpcw6 : w6.pc = BitVec.ofNat 64 (Image1.coreAddr + 208) := rfl
    have ht2w6 : w6.rget 7 = BitVec.ofNat 64 37 := by
      rw [hw6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2w5
    have hbe := li_beq_eq w6 208 37 37 (BitVec.ofNat 13 440)
      (BitVec.ofNat 64 (Image1.coreAddr + 652)) hcw6 hpcw6 ht2w6 dec_208 dec_212
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨14, (w6.rset 28 (BitVec.ofNat 64 37)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 652)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (14:Nat) = 2 + (2 + (2 + (2 + (2 + (2 + (2)))))) from rfl, runFuel_add, hb1,
          runFuel_add, hb2,
          runFuel_add, hb3,
          runFuel_add, hb4,
          runFuel_add, hb5,
          runFuel_add, hb6,
          hbe]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hw6,
          li_block_frame _ _ _ i hi, hw5,
          li_block_frame _ _ _ i hi, hw4,
          li_block_frame _ _ _ i hi, hw3,
          li_block_frame _ _ _ i hi, hw2,
          li_block_frame _ _ _ i hi, hw1,
          li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The low-stop chain (offsets 160..212), fall-through case: a non-stop
    char reaches the low-nibble check at 216. -/
theorem p1_stop_fall (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 160))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc64 : c < 2 ^ 64)
    (hne : c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 ∧ c ≠ 35 ∧ c ≠ 59 ∧ c ≠ 58 ∧ c ≠ 37) :
    ∃ s', runFuel 0 14 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 216) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  obtain ⟨h10n, h32, h95, h35, h59, h58, h37⟩ := hne
  have hb1 := li_beq_ne s4 160 10 c (BitVec.ofNat 13 488) hcode hpc ht2 dec_160 dec_164
    (by decide) (ofNat_ne c 10 hc64 (by decide) h10n) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 168))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (160 + 8))) := rfl
  try rw [← hv1] at hb1
  have hcv1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpcv1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 168) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  have hb2 := li_beq_ne v1 168 32 c (BitVec.ofNat 13 480) hcv1 hpcv1 ht2v1 dec_168 dec_172
    (by decide) (ofNat_ne c 32 hc64 (by decide) h32) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 176))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (168 + 8))) := rfl
  try rw [← hv2] at hb2
  have hcv2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv1)
  have hpcv2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 176) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have hb3 := li_beq_ne v2 176 95 c (BitVec.ofNat 13 472) hcv2 hpcv2 ht2v2 dec_176 dec_180
    (by decide) (ofNat_ne c 95 hc64 (by decide) h95) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 184))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (176 + 8))) := rfl
  try rw [← hv3] at hb3
  have hcv3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv2)
  have hpcv3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 184) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  have hb4 := li_beq_ne v3 184 35 c (BitVec.ofNat 13 464) hcv3 hpcv3 ht2v3 dec_184 dec_188
    (by decide) (ofNat_ne c 35 hc64 (by decide) h35) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 192))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (184 + 8))) := rfl
  try rw [← hv4] at hb4
  have hcv4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv3)
  have hpcv4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 192) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 c := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  have hb5 := li_beq_ne v4 192 59 c (BitVec.ofNat 13 456) hcv4 hpcv4 ht2v4 dec_192 dec_196
    (by decide) (ofNat_ne c 59 hc64 (by decide) h59) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 200))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (192 + 8))) := rfl
  try rw [← hv5] at hb5
  have hcv5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv4)
  have hpcv5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 200) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 c := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  have hb6 := li_beq_ne v5 200 58 c (BitVec.ofNat 13 448) hcv5 hpcv5 ht2v5 dec_200 dec_204
    (by decide) (ofNat_ne c 58 hc64 (by decide) h58) (by rw [coreBytes_len]; omega)
  let v6 := (v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 208))
  have hv6 : v6 = (v5.rset 28 (BitVec.ofNat 64 58)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (200 + 8))) := rfl
  try rw [← hv6] at hb6
  have hcv6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv5)
  have hpcv6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 208) := rfl
  have ht2v6 : v6.rget 7 = BitVec.ofNat 64 c := by
    rw [hv6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v5
  have hb7 := li_beq_ne v6 208 37 c (BitVec.ofNat 13 440) hcv6 hpcv6 ht2v6 dec_208 dec_212
    (by decide) (ofNat_ne c 37 hc64 (by decide) h37) (by rw [coreBytes_len]; omega)
  let vF := (v6.rset 28 (BitVec.ofNat 64 37)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 216))
  have hvF : vF = (v6.rset 28 (BitVec.ofNat 64 37)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (208 + 8))) := rfl
  try rw [← hvF] at hb7
  refine ⟨vF, ?_, rfl, rfl, ?_⟩
  · rw [show (14:Nat) = 2 + (2 + (2 + (2 + (2 + (2 + (2)))))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2,
        runFuel_add, hb3,
        runFuel_add, hb4,
        runFuel_add, hb5,
        runFuel_add, hb6,
        hb7]
  · intro i hi
    rw [hvF, li_block_frame _ _ _ i hi, hv6,
        li_block_frame _ _ _ i hi, hv5,
        li_block_frame _ _ _ i hi, hv4,
        li_block_frame _ _ _ i hi, hv3,
        li_block_frame _ _ _ i hi, hv2,
        li_block_frame _ _ _ i hi, hv1,
        li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Low-nibble range check (offsets 216..248), valid case: a hex digit
    falls through to the capacity check at 252. -/
theorem p1_low_ok (s4 : State) (c hi : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 216))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc256 : c < 256)
    (hn : Hex0.nibble c = some hi) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 252) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hc63 : c < 2 ^ 63 := by omega
  have hcase : (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · exact Or.inl hd
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · exact Or.inr hl
      · rw [if_neg hl] at hn
        exact absurd hn (by simp)
  rcases hcase with ⟨h48, h57⟩ | ⟨h65, h70⟩
  · -- digit '0'..'9'
    have bA := li_blt_nt s4 216 48 c (BitVec.ofNat 13 456) hcode hpc ht2 dec_216 dec_220
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 224))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (216 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 224) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_nt v1 224 58 c (BitVec.ofNat 13 8) hc1 hpc1 ht2v1 dec_224 dec_228
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 232))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (224 + 8))) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 232) := rfl
    have hq2 : v2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 232 (by omega)
    have hjal : step v2 = v2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 252)) := by
      rw [step_jal v2 232 0 (BitVec.ofNat 21 20) hc2 (by rw [coreBytes_len]; omega)
          hpc2 dec_232, rset_zero,
          show v2.pc + (BitVec.ofNat 21 20).signExtend 64
              = BitVec.ofNat 64 (Image1.coreAddr + 252) from by rw [hpc2]; decide]
    refine ⟨2 + (2 + 1), v2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 252)), ?_,
      by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_one _ hq2, hjal]
    · intro i hi
      rw [Hex0.Refine.setPc_rget, hv2, li_block_frame _ _ _ i hi, hv1,
          li_block_frame _ _ _ i hi]
  · -- letter 'A'..'F'
    have bA := li_blt_nt s4 216 48 c (BitVec.ofNat 13 456) hcode hpc ht2 dec_216 dec_220
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 224))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (216 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 224) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_t v1 224 58 c (BitVec.ofNat 13 8)
      (BitVec.ofNat 64 (Image1.coreAddr + 236)) hc1 hpc1 ht2v1 dec_224 dec_228
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 236))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 236)) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 236) := rfl
    have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
      rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v1
    have bC := li_blt_nt v2 236 65 c (BitVec.ofNat 13 436) hc2 hpc2 ht2v2 dec_236 dec_240
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 244))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 65)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (236 + 8))) := rfl
    try rw [← hv3] at bC
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 244) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have bD := li_bge_nt v3 244 71 c (BitVec.ofNat 13 428) hc3 hpc3 ht2v3 dec_244 dec_248
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let vF := (v3.rset 28 (BitVec.ofNat 64 71)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 252))
    have hvF : vF = (v3.rset 28 (BitVec.ofNat 64 71)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (244 + 8))) := rfl
    try rw [← hvF] at bD
    refine ⟨2 + (2 + (2 + 2)), vF, ?_, by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]
    · intro i hi
      rw [hvF, li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi, hv2,
          li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Low-nibble range check (offsets 216..248), invalid case: branches to
    the Unknown exit at 676. -/
theorem p1_low_unk (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 216))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc256 : c < 256)
    (hn : Hex0.nibble c = none) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 676) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hc63 : c < 2 ^ 63 := by omega
  have hcase : c < 48 ∨ (58 ≤ c ∧ c < 65) ∨ 71 ≤ c := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn; exact absurd hn (by simp)
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn; exact absurd hn (by simp)
      · omega
  rcases hcase with h48 | ⟨h58, h65⟩ | h71
  · have bA := li_blt_t s4 216 48 c (BitVec.ofNat 13 456)
      (BitVec.ofNat 64 (Image1.coreAddr + 676)) hcode hpc ht2 dec_216 dec_220
      (by decide) h48 hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    exact ⟨2, (s4.rset 28 (BitVec.ofNat 64 48)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 676)), bA, by omega, rfl, rfl,
      fun i hi => li_block_frame _ _ _ i hi⟩
  · have bA := li_blt_nt s4 216 48 c (BitVec.ofNat 13 456) hcode hpc ht2 dec_216 dec_220
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 224))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (216 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 224) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_t v1 224 58 c (BitVec.ofNat 13 8)
      (BitVec.ofNat 64 (Image1.coreAddr + 236)) hc1 hpc1 ht2v1 dec_224 dec_228
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 236))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 236)) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 236) := rfl
    have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
      rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v1
    have bC := li_blt_t v2 236 65 c (BitVec.ofNat 13 436)
      (BitVec.ofNat 64 (Image1.coreAddr + 676)) hc2 hpc2 ht2v2 dec_236 dec_240
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨2 + (2 + 2), (v2.rset 28 (BitVec.ofNat 64 65)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 676)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, bC]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv2, li_block_frame _ _ _ i hi, hv1,
          li_block_frame _ _ _ i hi]
  · have bA := li_blt_nt s4 216 48 c (BitVec.ofNat 13 456) hcode hpc ht2 dec_216 dec_220
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v1 := (s4.rset 28 (BitVec.ofNat 64 48)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 224))
    have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 48)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (216 + 8))) := rfl
    try rw [← hv1] at bA
    have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 224) := rfl
    have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
      rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have bB := li_bge_t v1 224 58 c (BitVec.ofNat 13 8)
      (BitVec.ofNat 64 (Image1.coreAddr + 236)) hc1 hpc1 ht2v1 dec_224 dec_228
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v2 := (v1.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 236))
    have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 236)) := rfl
    try rw [← hv2] at bB
    have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 236) := rfl
    have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
      rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v1
    have bC := li_blt_nt v2 236 65 c (BitVec.ofNat 13 436) hc2 hpc2 ht2v2 dec_236 dec_240
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 65)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 244))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 65)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (236 + 8))) := rfl
    try rw [← hv3] at bC
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 244) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have bD := li_bge_t v3 244 71 c (BitVec.ofNat 13 428)
      (BitVec.ofNat 64 (Image1.coreAddr + 676)) hc3 hpc3 ht2v3 dec_244 dec_248
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨2 + (2 + (2 + 2)), (v3.rset 28 (BitVec.ofNat 64 71)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 676)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [runFuel_add, bA, runFuel_add, bB, runFuel_add, bC, bD]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi, hv2,
          li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]

/-! ## Pass-1 iteration: byte tokens, assembled. -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-1 iteration for a byte token: high char `c` (not a
    special), then low char `l`. Lands back at the loop head with `pos + 1`
    (suffix shorter by 2), or halts `Result1`: Unknown (bad nibble),
    Trailing (EOF after high), Split (stop char after high), Short (output
    full). -/
theorem p1_byte (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos (c :: rest'))
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (hncol : (c == Hex1.c_colon) = false) (hnpct : (c == Hex1.c_pct) = false) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ l rest2, rest' = l :: rest2 ∧
          P1Inv inp cap s' lab (pos + 1) rest2) ∨
        Result1 s' inp cap) := by
  have hlbl := inv.wf.lbl_fits
  have hin := inv.wf.in_fits
  have hout := inv.wf.out_fits
  have hcap63 := inv.wf.cap63
  have hlen64 : inp.length < 2 ^ 64 := by
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hin hout hlbl
    omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp c rest' inv.suffix
  have hc256 : c < 256 := by
    apply inv.wf.bytes_ok
    have : c ∈ inp.drop (inp.length - (c :: rest').length) := by
      rw [inv.suffix]; exact List.mem_cons_self
    exact List.drop_subset _ _ this
  have hc64 : c < 2 ^ 64 := by omega
  have hne7 : c ≠ 35 ∧ c ≠ 59 ∧ c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 ∧ c ≠ 58 ∧ c ≠ 37 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hsc
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hss
    simp only [Hex1.c_colon, beq_eq_false_iff_ne] at hncol
    simp only [Hex1.c_pct, beq_eq_false_iff_ne] at hnpct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  -- machine: prefix (36..48), then the full dispatch fall-through to 108
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p1_prefix inp cap c rest' lab pos s inv
  obtain ⟨sd, hrund, hpcd, hmemd, hframed⟩ := p1_fall_tail s4 c hcode4 hpc4 ht2 hc64 hne7
  have hcoded : CodeLoaded1 sd := by
    intro i hi2
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi2
  have hmem_sd : sd.mem = s.mem := by rw [hmemd, hmem4]
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  have ht2d : sd.rget 7 = BitVec.ofNat 64 c := by
    rw [hframed 7 (by decide)]; exact ht2
  have h5sd : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide)]; exact hidx4
  cases hnib : Hex0.nibble c with
  | none =>
    -- bad high nibble -> Unknown exit (676)
    obtain ⟨n1, sU, hrunU, hn1, hpcU, hmemU, hframeU⟩ :=
      p1_high_unk sd c hcoded hpcd ht2d hc256 hnib
    have hcodeU : CodeLoaded1 sU := by
      intro i hi2
      rw [hmemU]
      exact hcoded i hi2
    have hraU : sU.rget 1 = 0 := by
      rw [hframeU 1 (by decide),
          hframe_sd 1 (by decide) (by decide) (by decide) (by decide)]
      exact inv.ra0
    obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
      exit_zero sU 676 5 hcodeU hpcU hraU dec_676 dec_680 dec_684 (by decide)
        (by rw [coreBytes_len]; omega)
    have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .Unknown) := by
      rw [← inv.spec]
      rw [Hex1.scan1]
      rw [if_neg (by simp [hsc]), if_neg (by simp [hss]), if_neg (by simp [hncol]),
          if_neg (by simp [hnpct])]
      rw [hnib]
    refine ⟨4 + (14 + (n1 + 3)), f, by omega, ?_, Or.inr ?_⟩
    · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunU, hrunf]
    · exact error_result1 f inp cap lab pos .Unknown hfpc hfa0 hfa1 hscan
        (by decide) (by decide) inv.pos_le
  | some hi =>
    -- good high nibble: reach the low-char read at 144
    obtain ⟨n1, sH, hrunH, hn1, hpcH, hmemH, hframeH⟩ :=
      p1_high_ok sd c hi hcoded hpcd ht2d hc256 hnib
    have hcodeH : CodeLoaded1 sH := by
      intro i hi2
      rw [hmemH]
      exact hcoded i hi2
    have hmem_sH : sH.mem = s.mem := by rw [hmemH, hmem_sd]
    have hframe_sH : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sH.rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hframeH i h28]
      exact hframe_sd i h0 h5 h7 h28
    have h5H : sH.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
      rw [hframeH 5 (by decide)]; exact h5sd
    have h10H : sH.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
      rw [hframe_sH 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
    have h11H : sH.rget 11 = BitVec.ofNat 64 inp.length := by
      rw [hframe_sH 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
    have hspec_hi : Hex1.scan1 .High lab pos (c :: rest')
        = Hex1.scan1 (.Low hi) lab pos rest' := by
      rw [Hex1.scan1]
      rw [if_neg (by simp [hsc]), if_neg (by simp [hss]), if_neg (by simp [hncol]),
          if_neg (by simp [hnpct])]
      rw [hnib]
    cases rest' with
    | nil =>
      -- EOF after the high nibble -> Trailing exit (664)
      have h5H' : sH.rget 5 = BitVec.ofNat 64 inp.length := by simpa using h5H
      have hbt := bgeu_eq_taken sH 144 5 11 inp.length (BitVec.ofNat 13 520)
        (BitVec.ofNat 64 (Image1.coreAddr + 664)) hcodeH hpcH h5H' h11H dec_144
        (by rw [coreBytes_len]; omega) (by decide)
      let sE := sH.setPc (BitVec.ofNat 64 (Image1.coreAddr + 664))
      have hsE : sE = sH.setPc (BitVec.ofNat 64 (Image1.coreAddr + 664)) := rfl
      try rw [← hsE] at hbt
      have hqH : sH.pc ≠ 0 := by rw [hpcH]; exact corePc_ne_zero 144 (by omega)
      have hrunE : runFuel 0 1 sH = sE := by rw [runFuel_one sH hqH, hbt]
      have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hcodeH
      have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 664) := rfl
      have hraE : sE.rget 1 = 0 := by
        rw [hsE, Hex0.Refine.setPc_rget,
            hframe_sH 1 (by decide) (by decide) (by decide) (by decide)]
        exact inv.ra0
      obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
        exit_zero sE 664 4 hcodeE hpcE hraE dec_664 dec_668 dec_672 (by decide)
          (by rw [coreBytes_len]; omega)
      have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .Trailing) := by
        rw [← inv.spec, hspec_hi]
        rw [Hex1.scan1]
      refine ⟨4 + (14 + (n1 + (1 + 3))), f, by omega, ?_, Or.inr ?_⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunH,
            runFuel_add, hrunE, hrunf]
      · exact error_result1 f inp cap lab pos .Trailing hfpc hfa0 hfa1 hscan
          (by decide) (by decide) inv.pos_le
    | cons l rest2 =>
      have hge2 : rest2.length + 2 ≤ inp.length := by
        have h := congrArg List.length inv.suffix
        simp only [List.length_drop, List.length_cons] at h
        omega
      have hidx1lt : inp.length - (l :: rest2).length < inp.length := by
        simp only [List.length_cons]; omega
      have hgetl : inp.getD (inp.length - (l :: rest2).length) 0 = l := by
        rw [← getD_drop]; rw [hrest'_eq]; rfl
      have hl256 : l < 256 := by
        apply inv.wf.bytes_ok
        have : l ∈ inp.drop (inp.length - (l :: rest2).length) := by
          rw [hrest'_eq]; exact List.mem_cons_self
        exact List.drop_subset _ _ this
      have hl64 : l < 2 ^ 64 := by omega
      have hinH : InputLoaded sH inp := by
        intro j hj
        rw [hmem_sH]
        exact inv.in_mem j hj
      -- read the low char at 144..156
      obtain ⟨s8, hrun8, hpc8, ht2_8, h5_8, hmem8, hcode8, hframe8⟩ :=
        p1_low_read sH inp l (inp.length - (l :: rest2).length) hcodeH hpcH h5H h10H
          h11H hinH hidx1lt hlen64 hgetl hl256
      have hmem_s8 : s8.mem = s.mem := by rw [hmem8, hmem_sH]
      have hframe_s8 : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s8.rget i = s.rget i := by
        intro i h0 h5 h7 h28
        rw [hframe8 i h0 h5 h7 h28]
        exact hframe_sH i h0 h5 h7 h28
      have h5_8' : s8.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
        rw [h5_8]
        congr 1
        simp only [List.length_cons]
        omega
      cases hls : Hex1.isLowStop l with
      | true =>
        -- stop char after the high nibble -> Split exit (652)
        obtain ⟨n2, sS, hrunS, hn2, hpcS, hmemS, hframeS⟩ :=
          p1_stop_split s8 l hcode8 hpc8 ht2_8 hls
        have hcodeS : CodeLoaded1 sS := by
          intro i hi2
          rw [hmemS]
          exact hcode8 i hi2
        have hraS : sS.rget 1 = 0 := by
          rw [hframeS 1 (by decide),
              hframe_s8 1 (by decide) (by decide) (by decide) (by decide)]
          exact inv.ra0
        obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
          exit_zero sS 652 3 hcodeS hpcS hraS dec_652 dec_656 dec_660 (by decide)
            (by rw [coreBytes_len]; omega)
        have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .Split) := by
          rw [← inv.spec, hspec_hi]
          rw [Hex1.scan1]
          rw [if_pos hls]
        refine ⟨4 + (14 + (n1 + (4 + (n2 + 3)))), f, by omega, ?_, Or.inr ?_⟩
        · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunH,
              runFuel_add, hrun8, runFuel_add, hrunS, hrunf]
        · exact error_result1 f inp cap lab pos .Split hfpc hfa0 hfa1 hscan
            (by decide) (by decide) inv.pos_le
      | false =>
        have hnel : l ≠ 10 ∧ l ≠ 32 ∧ l ≠ 95 ∧ l ≠ 35 ∧ l ≠ 59 ∧ l ≠ 58 ∧ l ≠ 37 := by
          have hls' := hls
          simp only [Hex1.isLowStop, Hex0.isLowStop, Hex0.isSpace, Hex0.isComment,
            Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Hex0.c_hash, Hex0.c_semi, Hex1.c_colon,
            Hex1.c_pct, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hls'
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
        obtain ⟨sf, hrunf14, hpcf, hmemf, hframef⟩ :=
          p1_stop_fall s8 l hcode8 hpc8 ht2_8 hl64 hnel
        have hcodef : CodeLoaded1 sf := by
          intro i hi2
          rw [hmemf]
          exact hcode8 i hi2
        have hmem_sf : sf.mem = s.mem := by rw [hmemf, hmem_s8]
        have hframe_sf : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sf.rget i = s.rget i := by
          intro i h0 h5 h7 h28
          rw [hframef i h28]
          exact hframe_s8 i h0 h5 h7 h28
        have ht2f : sf.rget 7 = BitVec.ofNat 64 l := by
          rw [hframef 7 (by decide)]; exact ht2_8
        cases hnl : Hex0.nibble l with
        | none =>
          -- bad low nibble -> Unknown exit (676)
          obtain ⟨n3, sU, hrunU, hn3, hpcU, hmemU, hframeU⟩ :=
            p1_low_unk sf l hcodef hpcf ht2f hl256 hnl
          have hcodeU : CodeLoaded1 sU := by
            intro i hi2
            rw [hmemU]
            exact hcodef i hi2
          have hraU : sU.rget 1 = 0 := by
            rw [hframeU 1 (by decide),
                hframe_sf 1 (by decide) (by decide) (by decide) (by decide)]
            exact inv.ra0
          obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
            exit_zero sU 676 5 hcodeU hpcU hraU dec_676 dec_680 dec_684 (by decide)
              (by rw [coreBytes_len]; omega)
          have hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (lab, pos, .Unknown) := by
            rw [← inv.spec, hspec_hi]
            rw [Hex1.scan1]
            rw [if_neg (by simp [hls])]
            rw [hnl]
          refine ⟨4 + (14 + (n1 + (4 + (14 + (n3 + 3))))), f, by omega, ?_, Or.inr ?_⟩
          · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunH,
                runFuel_add, hrun8, runFuel_add, hrunf14, runFuel_add, hrunU, hrunf]
          · exact error_result1 f inp cap lab pos .Unknown hfpc hfa0 hfa1 hscan
              (by decide) (by decide) inv.pos_le
        | some lo =>
          -- good low nibble: reach the capacity check at 252
          obtain ⟨n3, sk, hrunk, hn3, hpck, hmemk, hframek⟩ :=
            p1_low_ok sf l lo hcodef hpcf ht2f hl256 hnl
          have hcodek : CodeLoaded1 sk := by
            intro i hi2
            rw [hmemk]
            exact hcodef i hi2
          have hmem_sk : sk.mem = s.mem := by rw [hmemk, hmem_sf]
          have hframe_sk : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
              sk.rget i = s.rget i := by
            intro i h0 h5 h7 h28
            rw [hframek i h28]
            exact hframe_sf i h0 h5 h7 h28
          have h6k : sk.rget 6 = BitVec.ofNat 64 pos := by
            rw [hframe_sk 6 (by decide) (by decide) (by decide) (by decide)]
            exact inv.outidx
          have h13k : sk.rget 13 = BitVec.ofNat 64 cap := by
            rw [hframe_sk 13 (by decide) (by decide) (by decide) (by decide)]
            exact inv.a3
          have h5k : sk.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
            rw [hframek 5 (by decide), hframef 5 (by decide)]
            exact h5_8'
          have hqk : sk.pc ≠ 0 := by rw [hpck]; exact corePc_ne_zero 252 (by omega)
          have hspec_lo : Hex1.scan1 (.Low hi) lab pos (l :: rest2)
              = Hex1.scan1 .High lab (pos + 1) rest2 := by
            rw [Hex1.scan1]
            rw [if_neg (by simp [hls])]
            rw [hnl]
          by_cases hcap : pos < cap
          · -- room: bgeu not taken, bump pos, loop back
            have hult : (sk.rget 6).ult (sk.rget 13) = true := by
              rw [h6k, h13k]; exact ult_ofNat _ _ (by omega) hcap
            have hu1 : step sk = sk.setPc (BitVec.ofNat 64 (Image1.coreAddr + 256)) := by
              rw [step_bgeu sk 252 6 13 (BitVec.ofNat 13 388) hcodek
                  (by rw [coreBytes_len]; omega) hpck dec_252, hult]
              simp only [if_true]
              rw [show sk.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 256) from by
                rw [hpck, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
            let k1 := sk.setPc (BitVec.ofNat 64 (Image1.coreAddr + 256))
            have hsk1 : k1 = sk.setPc (BitVec.ofNat 64 (Image1.coreAddr + 256)) := rfl
            try rw [← hsk1] at hu1
            have hck1 : CodeLoaded1 k1 := codeLoaded1_setPc _ _ hcodek
            have hpck1 : k1.pc = BitVec.ofNat 64 (Image1.coreAddr + 256) := rfl
            have hqk1 : k1.pc ≠ 0 := by rw [hpck1]; exact corePc_ne_zero 256 (by omega)
            have h6k1 : k1.rget 6 = BitVec.ofNat 64 pos := by
              rw [hsk1, Hex0.Refine.setPc_rget]; exact h6k
            have hu2 : step k1 = (k1.rset 6 (BitVec.ofNat 64 (pos + 1))).setPc
                (BitVec.ofNat 64 (Image1.coreAddr + 260)) := by
              rw [step_addi k1 256 6 6 (BitVec.ofNat 12 1) hck1
                  (by rw [coreBytes_len]; omega) hpck1 dec_256,
                  show k1.rget 6 + (BitVec.ofNat 12 1).signExtend 64
                      = BitVec.ofNat 64 (pos + 1) from by
                    rw [h6k1, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by
                          decide,
                        show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ],
                  show k1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 260) from by
                    rw [hpck1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
            let k2 := (k1.rset 6 (BitVec.ofNat 64 (pos + 1))).setPc
                (BitVec.ofNat 64 (Image1.coreAddr + 260))
            have hsk2 : k2 = (k1.rset 6 (BitVec.ofNat 64 (pos + 1))).setPc
                (BitVec.ofNat 64 (Image1.coreAddr + 260)) := rfl
            try rw [← hsk2] at hu2
            have hck2 : CodeLoaded1 k2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hck1)
            have hpck2 : k2.pc = BitVec.ofNat 64 (Image1.coreAddr + 260) := rfl
            have hqk2 : k2.pc ≠ 0 := by rw [hpck2]; exact corePc_ne_zero 260 (by omega)
            have hu3 : step k2 = k2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := by
              rw [step_jal k2 260 0 (BitVec.ofNat 21 2096928) hck2
                  (by rw [coreBytes_len]; omega) hpck2 dec_260, rset_zero,
                  show k2.pc + (BitVec.ofNat 21 2096928).signExtend 64
                      = BitVec.ofNat 64 (Image1.coreAddr + 36) from by rw [hpck2]; decide]
            let sF := k2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36))
            have hsF : sF = k2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 36)) := rfl
            try rw [← hsF] at hu3
            have hrun3 : runFuel 0 3 sk = sF := by
              simp only [runFuel]
              rw [hu1, hu2, hu3, if_neg hqk, if_neg hqk1, if_neg hqk2]
            have hmemF : sF.mem = s.mem := by
              rw [hsF, hsk2, hsk1]
              simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
              exact hmem_sk
            have hregF : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 28 →
                sF.rget i = s.rget i := by
              intro i h0 h5i h6i h7i h28i
              rw [hsF, Hex0.Refine.setPc_rget, hsk2, Hex0.Refine.setPc_rget,
                  rset_rget _ _ _ _ (by decide) h0, if_neg h6i,
                  hsk1, Hex0.Refine.setPc_rget]
              exact hframe_sk i h0 h5i h7i h28i
            have h5F : sF.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
              rw [hsF, Hex0.Refine.setPc_rget, hsk2, Hex0.Refine.setPc_rget,
                  rset_rget _ _ _ _ (by decide) (by decide),
                  if_neg (by decide : (5:Nat) ≠ 6), hsk1, Hex0.Refine.setPc_rget]
              exact h5k
            have h6F : sF.rget 6 = BitVec.ofNat 64 (pos + 1) := by
              rw [hsF, Hex0.Refine.setPc_rget, hsk2, Hex0.Refine.setPc_rget,
                  rset_rget _ _ _ _ (by decide) (by decide)]
              simp
            refine ⟨4 + (14 + (n1 + (4 + (14 + (n3 + 3))))), sF, by omega, ?_,
              Or.inl ⟨l, rest2, rfl, ?_⟩⟩
            · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunH,
                  runFuel_add, hrun8, runFuel_add, hrunf14, runFuel_add, hrunk, hrun3]
            · exact {
                wf := inv.wf
                at_loop := rfl
                code := by
                  intro i hi2
                  rw [hmemF]
                  exact inv.code i hi2
                a0 := by
                  rw [hregF 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
                  exact inv.a0
                a1 := by
                  rw [hregF 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
                  exact inv.a1
                a2 := by
                  rw [hregF 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
                  exact inv.a2
                a3 := by
                  rw [hregF 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
                  exact inv.a3
                a4 := by
                  rw [hregF 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
                  exact inv.a4
                ra0 := by
                  rw [hregF 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
                  exact inv.ra0
                in_mem := by
                  intro j hj
                  rw [hmemF]
                  exact inv.in_mem j hj
                idx := h5F
                suffix := suffix_step inp l rest2 hrest'_eq
                outidx := h6F
                pos_le := by omega
                tbl := by
                  intro cc hcc k hk
                  rw [hmemF]
                  exact inv.tbl cc hcc k hk
                lab_le := by
                  intro cc p h
                  have := inv.lab_le cc p h
                  omega
                spec := by
                  rw [← hspec_lo, ← hspec_hi]
                  exact inv.spec }
          · -- output full: bgeu taken to the Short exit (640)
            have hultf : (sk.rget 6).ult (sk.rget 13) = false := by
              have hple := inv.pos_le
              rw [h6k, h13k]
              simp only [BitVec.ult, BitVec.toNat_ofNat]
              exact decide_eq_false (by omega)
            have hu1 : step sk = sk.setPc (BitVec.ofNat 64 (Image1.coreAddr + 640)) := by
              rw [step_bgeu sk 252 6 13 (BitVec.ofNat 13 388) hcodek
                  (by rw [coreBytes_len]; omega) hpck dec_252, hultf]
              simp only [Bool.false_eq_true, if_false]
              rw [show sk.pc + (BitVec.ofNat 13 388).signExtend 64
                  = BitVec.ofNat 64 (Image1.coreAddr + 640) from by rw [hpck]; decide]
            let sE := sk.setPc (BitVec.ofNat 64 (Image1.coreAddr + 640))
            have hsE : sE = sk.setPc (BitVec.ofNat 64 (Image1.coreAddr + 640)) := rfl
            try rw [← hsE] at hu1
            have hrunE : runFuel 0 1 sk = sE := by rw [runFuel_one sk hqk, hu1]
            have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hcodek
            have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 640) := rfl
            have hraE : sE.rget 1 = 0 := by
              rw [hsE, Hex0.Refine.setPc_rget,
                  hframe_sk 1 (by decide) (by decide) (by decide) (by decide)]
              exact inv.ra0
            obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
              exit_zero sE 640 2 hcodeE hpcE hraE dec_640 dec_644 dec_648 (by decide)
                (by rw [coreBytes_len]; omega)
            obtain ⟨labf, mres, stf, hres⟩ : ∃ labf mres stf,
                Hex1.scan1 .High lab (pos + 1) rest2 = (labf, mres, stf) :=
              ⟨_, _, _, rfl⟩
            have hmono : pos + 1 ≤ mres := by
              have h := scan1_pos_le rest2.length .High lab (pos + 1) rest2 (Nat.le_refl _)
              rw [hres] at h
              exact h
            have hscan_inp : Hex1.scan1 .High Hex1.noLabels 0 inp = (labf, mres, stf) := by
              rw [← inv.spec, hspec_hi, hspec_lo, hres]
            refine ⟨4 + (14 + (n1 + (4 + (14 + (n3 + (1 + 3)))))), f, by omega, ?_,
              Or.inr ?_⟩
            · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunH,
                  runFuel_add, hrun8, runFuel_add, hrunf14, runFuel_add, hrunk,
                  runFuel_add, hrunE, hrunf]
            · exact short_result1 f inp cap labf mres stf hfpc hfa0 hfa1 hscan_inp
                (by omega)

/-! ## Pass 1, assembled: the loop runs to a `Result1` or to pass-2 entry. -/

set_option maxRecDepth 8000 in
/-- EOF at the loop head: `bgeu` taken to pass-2 entry (offset 360), and the
    scan is complete and Ok. -/
theorem p1_eof (inp : List Nat) (cap : Nat) (lab : Labels) (pos : Nat) (s : State)
    (inv : P1Inv inp cap s lab pos []) :
    ∃ s', runFuel 0 1 s = s' ∧ P2Start inp cap s' lab pos := by
  have h5' : s.rget 5 = BitVec.ofNat 64 inp.length := by
    have h := inv.idx
    simpa using h
  have hbt := bgeu_eq_taken s 36 5 11 inp.length (BitVec.ofNat 13 324)
    (BitVec.ofNat 64 (Image1.coreAddr + 360)) inv.code inv.at_loop h5' inv.a1 dec_36
    (by rw [coreBytes_len]; omega) (by decide)
  have hp0 : s.pc ≠ 0 := by rw [inv.at_loop]; exact corePc_ne_zero 36 (by omega)
  refine ⟨s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 360)),
    by rw [runFuel_one s hp0, hbt], ?_⟩
  exact {
    wf := inv.wf
    pc := rfl
    code := codeLoaded1_setPc _ _ inv.code
    a0 := by rw [Hex0.Refine.setPc_rget]; exact inv.a0
    a1 := by rw [Hex0.Refine.setPc_rget]; exact inv.a1
    a2 := by rw [Hex0.Refine.setPc_rget]; exact inv.a2
    a3 := by rw [Hex0.Refine.setPc_rget]; exact inv.a3
    a4 := by rw [Hex0.Refine.setPc_rget]; exact inv.a4
    ra0 := by rw [Hex0.Refine.setPc_rget]; exact inv.ra0
    in_mem := inputLoaded_setPc _ _ inp inv.in_mem
    tbl := by
      intro c hc k hk
      rw [Hex0.Refine.setPc_mem]
      exact inv.tbl c hc k hk
    m_le := inv.pos_le
    lab_le := inv.lab_le
    scan_ok := by
      rw [← inv.spec]
      rw [Hex1.scan1] }

set_option maxHeartbeats 1000000 in
/-- Pass 1 runs to completion: from the loop invariant, the machine reaches a
    halted `Result1` state (a pass-1 error) or pass-2 entry (clean scan).
    Strong induction on a bound on the remaining suffix length. -/
theorem pass1_correct : ∀ (n : Nat) (inp : List Nat) (cap : Nat) (rest : List Nat)
    (lab : Labels) (pos : Nat) (s : State), rest.length ≤ n →
    P1Inv inp cap s lab pos rest →
    ∃ k s', runFuel 0 k s = s' ∧
      (Result1 s' inp cap ∨ ∃ labF m, P2Start inp cap s' labF m) := by
  intro n
  induction n with
  | zero =>
    intro inp cap rest lab pos s hn inv
    have hrest : rest = [] := by
      cases rest with
      | nil => rfl
      | cons c r => simp only [List.length_cons] at hn; omega
    subst hrest
    obtain ⟨s', hrun, hp2⟩ := p1_eof inp cap lab pos s inv
    exact ⟨1, s', hrun, Or.inr ⟨lab, pos, hp2⟩⟩
  | succ n ih =>
    intro inp cap rest lab pos s hn inv
    cases rest with
    | nil =>
      obtain ⟨s', hrun, hp2⟩ := p1_eof inp cap lab pos s inv
      exact ⟨1, s', hrun, Or.inr ⟨lab, pos, hp2⟩⟩
    | cons c rest' =>
      have hn' : rest'.length ≤ n := by
        simp only [List.length_cons] at hn; omega
      by_cases hcm : Hex0.isComment c = true
      · -- comment token
        obtain ⟨k1, s1, _, hrun1, hres⟩ := p1_comment inp cap c rest' lab pos s inv hcm
        rcases hres with ⟨rest2, hlen2, hinv2⟩ | hp2
        · have hlen2' : rest2.length ≤ n := by
            simp only [List.length_cons] at hlen2; omega
          obtain ⟨k2, s2, hrun2, hres2⟩ := ih inp cap rest2 lab pos s1 hlen2' hinv2
          exact ⟨k1 + k2, s2, by rw [runFuel_add, hrun1, hrun2], hres2⟩
        · exact ⟨k1, s1, hrun1, Or.inr ⟨lab, pos, hp2⟩⟩
      · by_cases hsp : Hex0.isSpace c = true
        · -- spacing token
          obtain ⟨k1, s1, _, hrun1, hinv1⟩ := p1_spacing inp cap c rest' lab pos s inv hsp
          obtain ⟨k2, s2, hrun2, hres2⟩ := ih inp cap rest' lab pos s1 hn' hinv1
          exact ⟨k1 + k2, s2, by rw [runFuel_add, hrun1, hrun2], hres2⟩
        · by_cases hcol : c = 58
          · -- label definition
            subst hcol
            obtain ⟨k1, s1, _, hrun1, hres⟩ := p1_labelDef inp cap rest' lab pos s inv
            rcases hres with ⟨l, rest2, heq, hinv2⟩ | hr1
            · subst heq
              have hlen2' : rest2.length ≤ n := by
                simp only [List.length_cons] at hn; omega
              obtain ⟨k2, s2, hrun2, hres2⟩ :=
                ih inp cap rest2 (setLabel lab l pos) pos s1 hlen2' hinv2
              exact ⟨k1 + k2, s2, by rw [runFuel_add, hrun1, hrun2], hres2⟩
            · exact ⟨k1, s1, hrun1, Or.inl hr1⟩
          · by_cases hpct : c = 37
            · -- label reference
              subst hpct
              obtain ⟨k1, s1, _, hrun1, hres⟩ := p1_ref inp cap rest' lab pos s inv
              rcases hres with ⟨l, rest2, heq, hinv2⟩ | hr1
              · subst heq
                have hlen2' : rest2.length ≤ n := by
                  simp only [List.length_cons] at hn; omega
                obtain ⟨k2, s2, hrun2, hres2⟩ :=
                  ih inp cap rest2 lab (pos + 4) s1 hlen2' hinv2
                exact ⟨k1 + k2, s2, by rw [runFuel_add, hrun1, hrun2], hres2⟩
              · exact ⟨k1, s1, hrun1, Or.inl hr1⟩
            · -- byte token
              have hsc : Hex0.isComment c = false := by
                cases h : Hex0.isComment c
                · rfl
                · exact absurd h hcm
              have hss : Hex0.isSpace c = false := by
                cases h : Hex0.isSpace c
                · rfl
                · exact absurd h hsp
              have hncol : (c == Hex1.c_colon) = false := by
                simp only [Hex1.c_colon, beq_eq_false_iff_ne]
                exact hcol
              have hnpct : (c == Hex1.c_pct) = false := by
                simp only [Hex1.c_pct, beq_eq_false_iff_ne]
                exact hpct
              obtain ⟨k1, s1, _, hrun1, hres⟩ :=
                p1_byte inp cap c rest' lab pos s inv hsc hss hncol hnpct
              rcases hres with ⟨l, rest2, heq, hinv2⟩ | hr1
              · subst heq
                have hlen2' : rest2.length ≤ n := by
                  simp only [List.length_cons] at hn; omega
                obtain ⟨k2, s2, hrun2, hres2⟩ :=
                  ih inp cap rest2 lab (pos + 1) s1 hlen2' hinv2
                exact ⟨k1 + k2, s2, by rw [runFuel_add, hrun1, hrun2], hres2⟩
              · exact ⟨k1, s1, hrun1, Or.inl hr1⟩

/-! ## Pass 2: the emit loop invariant and entry. -/

/-- Invariant at the pass-2 loop head (offset 368). `labF` is the final label
    map (the table is never written in pass 2); `emitted` the bytes written so
    far; `rest` the unconsumed suffix. `labNow`/`m` track the residual scan,
    which is valid and Ok (`scan_ok`) -- this gives control-flow totality and
    bounds every write below `m ≤ cap`. `spec` is the emit telescope. -/
structure P2Inv (inp : List Nat) (cap : Nat) (s : State) (labF labNow : Labels)
    (m : Nat) (emitted : List Nat) (rest : List Nat) : Prop where
  wf       : WellFormed1 inp cap
  at_loop  : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 368)
  code     : CodeLoaded1 s
  a0       : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr
  a1       : s.rget 11 = BitVec.ofNat 64 inp.length
  a2       : s.rget 12 = BitVec.ofNat 64 Image1.outAddr
  a3       : s.rget 13 = BitVec.ofNat 64 cap
  a4       : s.rget 14 = BitVec.ofNat 64 Image1.lblAddr
  ra0      : s.rget 1  = 0
  in_mem   : InputLoaded s inp
  idx      : s.rget 5  = BitVec.ofNat 64 (inp.length - rest.length)
  suffix   : inp.drop (inp.length - rest.length) = rest
  outidx   : s.rget 6  = BitVec.ofNat 64 emitted.length
  out_mem  : ∀ j, j < emitted.length →
    s.mem (BitVec.ofNat 64 (Image1.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0)
  tbl      : TableLoaded s labF
  m_le     : m ≤ cap
  lab_le   : ∀ c p, labF c = some p → p ≤ m
  scan_inp : Hex1.scan1 .High Hex1.noLabels 0 inp = (labF, m, .Ok)
  scan_ok  : Hex1.scan1 .High labNow emitted.length rest = (labF, m, .Ok)
  spec     : Hex1.emit1 .High labF 0 inp
      = (emitted ++ (Hex1.emit1 .High labF emitted.length rest).1,
         (Hex1.emit1 .High labF emitted.length rest).2)

set_option maxRecDepth 8000 in
/-- Pass-2 entry (offsets 360, 364): zero `t0`/`t1`, establishing the loop
    invariant on the whole input with nothing emitted. -/
theorem p2_entry (inp : List Nat) (cap : Nat) (labF : Labels) (m : Nat) (s : State)
    (hp2 : P2Start inp cap s labF m) :
    ∃ s', runFuel 0 2 s = s' ∧
      P2Inv inp cap s' labF Hex1.noLabels m [] inp := by
  have hu1 : step s = (s.rset 5 (BitVec.ofNat 64 0)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 364)) := by
    rw [step_addi s 360 5 0 (BitVec.ofNat 12 0) hp2.code (by rw [coreBytes_len]; omega)
        hp2.pc dec_360,
        show s.rget 0 + (BitVec.ofNat 12 0).signExtend 64 = BitVec.ofNat 64 0 from by
          rw [Hex0.Refine.rget_zero]; decide,
        show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 364) from by
          rw [hp2.pc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s1 := (s.rset 5 (BitVec.ofNat 64 0)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 364))
  have hs1 : s1 = (s.rset 5 (BitVec.ofNat 64 0)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 364)) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hp2.code)
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 364) := rfl
  have hu2 : step s1 = (s1.rset 6 (BitVec.ofNat 64 0)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 368)) := by
    rw [step_addi s1 364 6 0 (BitVec.ofNat 12 0) hc1 (by rw [coreBytes_len]; omega)
        hpc1 dec_364,
        show s1.rget 0 + (BitVec.ofNat 12 0).signExtend 64 = BitVec.ofNat 64 0 from by
          rw [Hex0.Refine.rget_zero]; decide,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 368) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s2 := (s1.rset 6 (BitVec.ofNat 64 0)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 368))
  have hs2 : s2 = (s1.rset 6 (BitVec.ofNat 64 0)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 368)) := rfl
  try rw [← hs2] at hu2
  have hp0 : s.pc ≠ 0 := by rw [hp2.pc]; exact corePc_ne_zero 360 (by omega)
  have hq1 : s1.pc ≠ 0 := by rw [hpc1]; exact corePc_ne_zero 364 (by omega)
  have hrun : runFuel 0 2 s = s2 := by
    simp only [runFuel]
    rw [hu1, hu2, if_neg hp0, if_neg hq1]
  have hmem2 : s2.mem = s.mem := by
    rw [hs2, hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
  have hreg2 : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → s2.rget i = s.rget i := by
    intro i h0 h5 h6
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h6,
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5]
  refine ⟨s2, hrun, ?_⟩
  exact {
    wf := hp2.wf
    at_loop := rfl
    code := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
    a0 := by rw [hreg2 10 (by decide) (by decide) (by decide)]; exact hp2.a0
    a1 := by rw [hreg2 11 (by decide) (by decide) (by decide)]; exact hp2.a1
    a2 := by rw [hreg2 12 (by decide) (by decide) (by decide)]; exact hp2.a2
    a3 := by rw [hreg2 13 (by decide) (by decide) (by decide)]; exact hp2.a3
    a4 := by rw [hreg2 14 (by decide) (by decide) (by decide)]; exact hp2.a4
    ra0 := by rw [hreg2 1 (by decide) (by decide) (by decide)]; exact hp2.ra0
    in_mem := by
      intro j hj
      rw [hmem2]
      exact hp2.in_mem j hj
    idx := by
      rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (5:Nat) ≠ 6), hs1, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide)]
      simp [Nat.sub_self]
    suffix := by simp
    outidx := by
      rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    out_mem := by
      intro j hj
      simp at hj
    tbl := by
      intro c hc k hk
      rw [hmem2]
      exact hp2.tbl c hc k hk
    m_le := hp2.m_le
    lab_le := hp2.lab_le
    scan_inp := hp2.scan_ok
    scan_ok := hp2.scan_ok
    spec := by simp }

/-- Build a `Result1` for a pass-2 exit (`Ok` or `Undef`): the machine halted
    with `a0 = statusCode st'`, `a1 = |emitted|`, the out region holds
    `emitted`, while scan and emit agree. -/
theorem emit_result1 (s : State) (inp : List Nat) (cap : Nat) (labF : Labels)
    (m : Nat) (emitted : List Nat) (st' : Hex1.Status)
    (hst : st' = .Ok ∨ st' = .Undef) (hp : s.pc = 0)
    (ha0 : s.rget 10 = BitVec.ofNat 64 (Hex1.statusCode st'))
    (ha1 : s.rget 11 = BitVec.ofNat 64 emitted.length)
    (hout : ∀ j, j < emitted.length →
      s.mem (BitVec.ofNat 64 (Image1.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0))
    (hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (labF, m, .Ok))
    (hm : m ≤ cap)
    (hemit : Hex1.emit1 .High labF 0 inp = (emitted, st')) :
    Result1 s inp cap := by
  have hdec : Hex1.decode1 inp = (emitted, m, st') := by
    simp only [Hex1.decode1, hscan, hemit]
  have hcs : Hex1.coreSpec1 inp cap
      = (Hex1.statusCode st', emitted, emitted.length) := by
    rcases hst with h | h <;> subst h <;>
      · simp only [Hex1.coreSpec1, hdec]
        rw [if_neg (Nat.not_lt.mpr hm)]
        rfl
  refine ⟨hp, ?_, ?_, ?_⟩
  · rw [hcs]; exact ha0
  · rw [hcs]; exact ha1
  · intro j hj
    rw [hcs] at hj ⊢
    exact hout j hj

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The Ok exit (offset 628): `li a0,0; mv a1,t1; ret`, producing `Result1`
    from a state whose residual emit is complete. -/
theorem p2_ok_exit (inp : List Nat) (cap : Nat) (labF : Labels) (m : Nat)
    (emitted : List Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 628))
    (hcode : CodeLoaded1 s) (hra : s.rget 1 = 0)
    (h6 : s.rget 6 = BitVec.ofNat 64 emitted.length)
    (hout : ∀ j, j < emitted.length →
      s.mem (BitVec.ofNat 64 (Image1.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0))
    (hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (labF, m, .Ok))
    (hm : m ≤ cap)
    (hemit : Hex1.emit1 .High labF 0 inp = (emitted, .Ok)) :
    ∃ f, runFuel 0 3 s = f ∧ Result1 f inp cap := by
  obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
    exit_t1 s 628 0 hcode hpc hra dec_628 dec_632 dec_636 (by decide)
      (by rw [coreBytes_len]; omega)
  refine ⟨f, hrunf, ?_⟩
  refine emit_result1 f inp cap labF m emitted .Ok (Or.inl rfl) hfpc hfa0 ?_ ?_ hscan
    hm hemit
  · rw [hfa1, h6]
  · intro j hj
    rw [hfmem]
    exact hout j hj

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The shared head of every non-EOF pass-2 iteration (offsets 368..380):
    `bgeu`(not taken) → `add` → `lbu` (read char `c`) → `addi` (bump index).
    Lands at offset 384 with `t2 = c`. -/
theorem p2_prefix (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (labF labNow : Labels) (m : Nat) (emitted : List Nat) (s : State)
    (inv : P2Inv inp cap s labF labNow m emitted (c :: rest')) :
    ∃ s4, runFuel 0 4 s = s4 ∧
      s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 384) ∧
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
  have hpc0 : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 368) := inv.at_loop
  -- step 1: bgeu t0,a1 -- NOT taken (idx < len)
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [inv.idx, inv.a1]; exact ult_ofNat _ _ hilt64 hilt
  have hu1 : step s = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 372)) := by
    rw [step_bgeu s 368 5 11 (BitVec.ofNat 13 260) inv.code (by rw [coreBytes_len]; omega)
        hpc0 dec_368, hult]
    simp only [if_true]
    rw [show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 372) from by
      rw [hpc0, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s1 := s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 372))
  have hs1 : s1 = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 372)) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ inv.code
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 372) := rfl
  -- step 2: add t3,a0,t0
  have haddr : s1.rget 10 + s1.rget 5
      = BitVec.ofNat 64 (Image1.inputAddr + (inp.length - (c :: rest').length)) := by
    show s.rget 10 + s.rget 5 = _
    rw [inv.a0, inv.idx]; exact addr_ofNat_succ _ _
  have hu2 : step s1 = (s1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 376)) := by
    rw [step_add s1 372 28 10 5 hc1 (by rw [coreBytes_len]; omega) hpc1 dec_372, haddr,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 376) from by
          rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s2 := (s1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 376))
  have hs2 : s2 = (s1.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (c :: rest').length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 376)) := rfl
  try rw [← hs2] at hu2
  have hc2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 376) := rfl
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
        (BitVec.ofNat 64 (Image1.coreAddr + 380)) := by
    rw [step_lbu s2 376 7 28 (0#12) hc2 (by rw [coreBytes_len]; omega) hpc2 dec_376]
    rw [show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 380) from by
      rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    rw [hbyte]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 c)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 380))
  have hs3 : s3 = (s2.rset 7 (BitVec.ofNat 64 c)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 380)) := rfl
  try rw [← hs3] at hu3
  have hc3 : CodeLoaded1 s3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 380) := rfl
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
      (BitVec.ofNat 64 (Image1.coreAddr + 384)) := by
    rw [step_addi s3 380 5 5 (BitVec.ofNat 12 1) hc3 (by rw [coreBytes_len]; omega)
        hpc3 dec_380,
        show s3.rget 5 + (BitVec.ofNat 12 1).signExtend 64
            = BitVec.ofNat 64 (inp.length - rest'.length) from by
          rw [hr5_3, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide]
          exact hidx1,
        show s3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 384) from by
          rw [hpc3, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s4 := (s3.rset 5 (BitVec.ofNat 64 (inp.length - rest'.length))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 384))
  have hs4 : s4 = (s3.rset 5 (BitVec.ofNat 64 (inp.length - rest'.length))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 384)) := rfl
  try rw [← hs4] at hu4
  have hp0 : s.pc ≠ 0 := by rw [hpc0]; exact corePc_ne_zero 368 (by omega)
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; exact corePc_ne_zero 372 (by omega)
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 376 (by omega)
  have hp3 : s3.pc ≠ 0 := by rw [hpc3]; exact corePc_ne_zero 380 (by omega)
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-2 spacing dispatch (from offset 384, `t2 = c ∈ {10,32,95}`):
    falls through `#`/`;` and branches back to the loop head at the matching
    spacing char. Touches only `t3` and `pc`. -/
theorem p2_spacing_tail (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 384))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c)
    (hc : c = 10 ∨ c = 32 ∨ c = 95) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 368) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hne35 : (BitVec.ofNat 64 c : Word) ≠ BitVec.ofNat 64 35 := by
    rcases hc with h | h | h <;> subst h <;> decide
  have hb1 := li_beq_ne s4 384 35 c (BitVec.ofNat 13 212) hcode hpc ht2 dec_384 dec_388
    (by decide) hne35 (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 392))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (384 + 8))) := rfl
  try rw [← hv1] at hb1
  have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 392) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  have hne59 : (BitVec.ofNat 64 c : Word) ≠ BitVec.ofNat 64 59 := by
    rcases hc with h | h | h <;> subst h <;> decide
  have hb2 := li_beq_ne v1 392 59 c (BitVec.ofNat 13 204) hc1 hpc1 ht2v1 dec_392 dec_396
    (by decide) hne59 (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 400))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (392 + 8))) := rfl
  try rw [← hv2] at hb2
  have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 400) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have frame12 : ∀ i, i ≠ 28 → v2.rget i = s4.rget i := by
    intro i hi
    rw [hv2, li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]
  rcases hc with h10 | h32 | h95
  · subst h10
    have hb3 := li_beq_eq v2 400 10 10 (BitVec.ofNat 13 8156)
      (BitVec.ofNat 64 (Image1.coreAddr + 368)) hc2 hpc2 ht2v2 dec_400 dec_404
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨6, (v2.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 368)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (6:Nat) = 2 + (2 + 2) from rfl, runFuel_add, hb1, runFuel_add, hb2, hb3]
    · intro i hi
      rw [li_block_frame _ _ _ i hi]
      exact frame12 i hi
  · subst h32
    have hb3 := li_beq_ne v2 400 10 32 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_400 dec_404
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 408))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (400 + 8))) := rfl
    try rw [← hv3] at hb3
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 408) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 32 := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have hb4 := li_beq_eq v3 408 32 32 (BitVec.ofNat 13 8148)
      (BitVec.ofNat 64 (Image1.coreAddr + 368)) hc3 hpc3 ht2v3 dec_408 dec_412
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨8, (v3.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 368)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (8:Nat) = 2 + (2 + (2 + 2)) from rfl, runFuel_add, hb1, runFuel_add, hb2,
          runFuel_add, hb3, hb4]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi]
      exact frame12 i hi
  · subst h95
    have hb3 := li_beq_ne v2 400 10 95 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_400 dec_404
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 408))
    have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (400 + 8))) := rfl
    try rw [← hv3] at hb3
    have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
    have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 408) := rfl
    have ht2v3 : v3.rget 7 = BitVec.ofNat 64 95 := by
      rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v2
    have hb4 := li_beq_ne v3 408 32 95 (BitVec.ofNat 13 8148) hc3 hpc3 ht2v3 dec_408 dec_412
      (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 416))
    have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (408 + 8))) := rfl
    try rw [← hv4] at hb4
    have hc4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
    have hpc4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 416) := rfl
    have ht2v4 : v4.rget 7 = BitVec.ofNat 64 95 := by
      rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2v3
    have hb5 := li_beq_eq v4 416 95 95 (BitVec.ofNat 13 8140)
      (BitVec.ofNat 64 (Image1.coreAddr + 368)) hc4 hpc4 ht2v4 dec_416 dec_420
      (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
    refine ⟨10, (v4.rset 28 (BitVec.ofNat 64 95)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 368)), ?_, by omega, rfl, rfl, ?_⟩
    · rw [show (10:Nat) = 2 + (2 + (2 + (2 + 2))) from rfl, runFuel_add, hb1, runFuel_add,
          hb2, runFuel_add, hb3, runFuel_add, hb4, hb5]
    · intro i hi
      rw [li_block_frame _ _ _ i hi, hv4, li_block_frame _ _ _ i hi, hv3,
          li_block_frame _ _ _ i hi]
      exact frame12 i hi

set_option maxHeartbeats 1000000 in
/-- A COMPLETE pass-2 iteration for a spacing token. -/
theorem p2_spacing (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (labF labNow : Labels) (m : Nat) (emitted : List Nat) (s : State)
    (inv : P2Inv inp cap s labF labNow m emitted (c :: rest'))
    (hsp : Hex0.isSpace c = true) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      P2Inv inp cap s' labF labNow m emitted rest' := by
  have hc : c = 10 ∨ c = 32 ∨ c = 95 := by
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Bool.or_eq_true,
      beq_iff_eq] at hsp
    rcases hsp with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p2_prefix inp cap c rest' labF labNow m emitted s inv
  obtain ⟨n, s', hrun', hn, hpc', hmem', hframe'⟩ :=
    p2_spacing_tail s4 c hcode4 hpc4 ht2 hc
  have hsc : Hex0.isComment c = false := by
    rcases hc with h | h | h <;> subst h <;> rfl
  have hstep_s : Hex1.scan1 .High labNow emitted.length (c :: rest')
      = Hex1.scan1 .High labNow emitted.length rest' := by
    rw [Hex1.scan1]
    rw [if_neg (by simp [hsc]), if_pos hsp]
  have hstep_e : Hex1.emit1 .High labF emitted.length (c :: rest')
      = Hex1.emit1 .High labF emitted.length rest' := by
    rw [Hex1.emit1]
    rw [if_neg (by simp [hsc]), if_pos hsp]
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
      rw [hmem]
      exact inv.code i hi
    a0 := by rw [hreg 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
    a1 := by rw [hreg 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
    a2 := by rw [hreg 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
    a3 := by rw [hreg 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
    a4 := by rw [hreg 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
    ra0 := by rw [hreg 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
    in_mem := by
      intro j hj
      rw [hmem]
      exact inv.in_mem j hj
    idx := by rw [hframe' 5 (by decide), hidx4]
    suffix := suffix_step inp c rest' inv.suffix
    outidx := by rw [hreg 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
    out_mem := by
      intro j hj
      rw [hmem]
      exact inv.out_mem j hj
    tbl := by
      intro cc hcc k hk
      rw [hmem]
      exact inv.tbl cc hcc k hk
    m_le := inv.m_le
    lab_le := inv.lab_le
    scan_inp := inv.scan_inp
    scan_ok := by
      rw [← hstep_s]
      exact inv.scan_ok
    spec := by
      rw [← hstep_e]
      exact inv.spec }

/-! ## Pass 2: comment tokens -- the inner scan loop (port of pass 1's). -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The 4-instruction head of the comment inner loop (offsets 600..612 (pass 2)):
    `bgeu`(not taken) → `add` → `lbu` (read `inp[idx]`) → `li t3,10`.
    Reaches offset 616 with `t2 = inp[idx]`, `t3 = 10`, `t0` unchanged. -/
theorem comment_read2 (s : State) (inp : List Nat) (idx ch : Nat) (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 600))
    (h5 : s.rget 5 = BitVec.ofNat 64 idx)
    (h10 : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr)
    (h11 : s.rget 11 = BitVec.ofNat 64 inp.length)
    (hlt : idx < inp.length)
    (hmem : InputLoaded s inp)
    (hinlt : inp.length < 2 ^ 64) (hch : inp.getD idx 0 = ch) (hch256 : ch < 256) :
    ∃ s4, runFuel 0 4 s = s4 ∧ s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 616) ∧
      s4.rget 7 = BitVec.ofNat 64 ch ∧ s4.rget 28 = BitVec.ofNat 64 10 ∧
      s4.rget 5 = BitVec.ofNat 64 idx ∧ s4.mem = s.mem ∧ CodeLoaded1 s4 ∧
      (∀ i, i ≠ 7 → i ≠ 28 → s4.rget i = s.rget i) := by
  have hult : (s.rget 5).ult (s.rget 11) = true := by
    rw [h5, h11]; exact ult_ofNat _ _ hinlt hlt
  have hs1 : step s = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 604)) := by
    rw [step_bgeu s 600 5 11 (BitVec.ofNat 13 28) hcode (by rw [coreBytes_len]; omega)
        hpc dec_600, if_pos hult,
        show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 604) from by rw [hpc]; decide]
  let s1 := s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 604))
  have hs1d : s1 = s.setPc (BitVec.ofNat 64 (Image1.coreAddr + 604)) := rfl
  try rw [← hs1d] at hs1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ hcode
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 604) := rfl
  have haddr : s1.rget 10 + s1.rget 5 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    show s.rget 10 + s.rget 5 = _
    rw [h10, h5]; exact addr_ofNat_succ _ _
  have hs2 : step s1 = (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 608)) := by
    rw [step_add s1 604 28 10 5 hc1 (by rw [coreBytes_len]; omega) hpc1 dec_604, haddr,
        show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 608) from by rw [hpc1]; decide]
  let s2 := (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 608))
  have hs2d : s2 = (s1.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 608)) := rfl
  try rw [← hs2d] at hs2
  have hc2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 608) := rfl
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
      (BitVec.ofNat 64 (Image1.coreAddr + 612)) := by
    rw [step_lbu s2 608 7 28 (0#12) hc2 (by rw [coreBytes_len]; omega) hpc2 dec_608]
    rw [show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 612) from by rw [hpc2]; decide]
    rw [hbyte]
  let s3 := (s2.rset 7 (BitVec.ofNat 64 ch)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 612))
  have hs3d : s3 = (s2.rset 7 (BitVec.ofNat 64 ch)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 612)) := rfl
  try rw [← hs3d] at hs3
  have hc3 : CodeLoaded1 s3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 612) := rfl
  have hs4 : step s3 = (s3.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 616)) := by
    rw [step_addi s3 612 28 0 (BitVec.ofNat 12 10) hc3 (by rw [coreBytes_len]; omega)
        hpc3 dec_612,
        show s3.rget 0 + (BitVec.ofNat 12 10).signExtend 64 = BitVec.ofNat 64 10 from by
          rw [Hex0.Refine.rget_zero]; decide,
        show s3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 616) from by rw [hpc3]; decide]
  let s4 := (s3.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 616))
  have hs4d : s4 = (s3.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 616)) := rfl
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
/-- The comment inner loop (offsets 600..624): scans `inp` from `idx` until a
    newline (left unconsumed, back to the loop head 368 sitting on it) or EOF
    (exits to pass-2 entry 628). Touches only `t0`/`t2`/`t3`. -/
theorem comment_loop2 (inp : List Nat) : ∀ (n : Nat) (s : State) (idx : Nat),
    CodeLoaded1 s → s.pc = BitVec.ofNat 64 (Image1.coreAddr + 600) →
    s.rget 5 = BitVec.ofNat 64 idx → s.rget 10 = BitVec.ofNat 64 Image1.inputAddr →
    s.rget 11 = BitVec.ofNat 64 inp.length →
    InputLoaded s inp →
    inp.length < 2 ^ 64 → (∀ b ∈ inp, b < 256) → idx ≤ inp.length → inp.length - idx ≤ n →
    ∃ k, (∃ q, idx ≤ q ∧ q < inp.length ∧ inp.getD q 0 = 10 ∧
            Hex0.skipComment (inp.drop idx) = inp.drop (q + 1) ∧
            (runFuel 0 k s).pc = BitVec.ofNat 64 (Image1.coreAddr + 368) ∧
            (runFuel 0 k s).rget 5 = BitVec.ofNat 64 q ∧
            (runFuel 0 k s).mem = s.mem ∧
            (∀ i, i ≠ 5 → i ≠ 7 → i ≠ 28 → (runFuel 0 k s).rget i = s.rget i))
         ∨ (Hex0.skipComment (inp.drop idx) = [] ∧
            (runFuel 0 k s).pc = BitVec.ofNat 64 (Image1.coreAddr + 628) ∧
            (runFuel 0 k s).rget 5 = BitVec.ofNat 64 inp.length ∧
            (runFuel 0 k s).mem = s.mem ∧
            (∀ i, i ≠ 5 → i ≠ 7 → i ≠ 28 → (runFuel 0 k s).rget i = s.rget i)) := by
  intro n
  induction n with
  | zero =>
    intro s idx hcode hpc h5 h10 h11 hmem hinlt hbytes hle hn
    have hidx : idx = inp.length := by omega
    subst hidx
    have hbt := bgeu_eq_taken s 600 5 11 inp.length (BitVec.ofNat 13 28)
      (BitVec.ofNat 64 (Image1.coreAddr + 628)) hcode hpc h5 h11 dec_600
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
        comment_read2 s inp idx (inp.getD idx 0) hcode hpc h5 h10 h11 hlt hmem hinlt rfl hch256
      by_cases hnl : inp.getD idx 0 = 10
      · -- newline at idx → loop head, sitting on it
        have hbeq : step s4 = s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := by
          rw [step_beq s4 616 7 28 (BitVec.ofNat 13 7944) hcode4
              (by rw [coreBytes_len]; omega) hpc4 dec_616, h7_4, h28_4, hnl, if_pos rfl,
              show s4.pc + (BitVec.ofNat 13 7944).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 368) from by rw [hpc4]; decide]
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
        have hbeq : step s4 = s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 620)) := by
          rw [step_beq s4 616 7 28 (BitVec.ofNat 13 7944) hcode4
              (by rw [coreBytes_len]; omega) hpc4 dec_616, h7_4, h28_4,
              if_neg (ofNat_ne _ 10 hch64 (by decide) hnl),
              show s4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 620) from by
                rw [hpc4]; decide]
        let v5 := s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 620))
        have hv5 : v5 = s4.setPc (BitVec.ofNat 64 (Image1.coreAddr + 620)) := rfl
        try rw [← hv5] at hbeq
        have hc5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ hcode4
        have hpc5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 620) := rfl
        have h5v5 : v5.rget 5 = BitVec.ofNat 64 idx := by
          rw [hv5, Hex0.Refine.setPc_rget]; exact h5_4
        have haddi : step v5 = (v5.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
            (BitVec.ofNat 64 (Image1.coreAddr + 624)) := by
          rw [step_addi v5 620 5 5 (BitVec.ofNat 12 1) hc5 (by rw [coreBytes_len]; omega)
              hpc5 dec_620, h5v5,
              show ((BitVec.ofNat 12 1).signExtend 64 : Word) = BitVec.ofNat 64 1 from by decide,
              addr_ofNat_succ,
              show v5.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 624) from by
                rw [hpc5]; decide]
        let v6 := (v5.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
            (BitVec.ofNat 64 (Image1.coreAddr + 624))
        have hv6 : v6 = (v5.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
            (BitVec.ofNat 64 (Image1.coreAddr + 624)) := rfl
        try rw [← hv6] at haddi
        have hc6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc5)
        have hpc6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 624) := rfl
        have hjal : step v6 = v6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 600)) := by
          rw [step_jal v6 624 0 (BitVec.ofNat 21 2097128) hc6 (by rw [coreBytes_len]; omega)
              hpc6 dec_624, rset_zero,
              show v6.pc + (BitVec.ofNat 21 2097128).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 600) from by rw [hpc6]; decide]
        let s' := v6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 600))
        have hs' : s' = v6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 600)) := rfl
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
        have hpcs' : s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 600) := rfl
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
      have hbt := bgeu_eq_taken s 600 5 11 inp.length (BitVec.ofNat 13 28)
        (BitVec.ofNat 64 (Image1.coreAddr + 628)) hcode hpc h5 h11 dec_600
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


set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-2 iteration for a comment token (`#`/`;`): prefix +
    dispatch to 600 + the inner loop. Lands back at the loop head sitting on
    the newline, or halts `Result1` (Ok) on EOF inside the comment. -/
theorem p2_comment (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (labF labNow : Labels) (m : Nat) (emitted : List Nat) (s : State)
    (inv : P2Inv inp cap s labF labNow m emitted (c :: rest'))
    (hcm : Hex0.isComment c = true) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ rest2, rest2.length < (c :: rest').length ∧
          P2Inv inp cap s' labF labNow m emitted rest2) ∨
        Result1 s' inp cap) := by
  have hc : c = 35 ∨ c = 59 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_true, beq_iff_eq] at hcm
    exact hcm
  have hlen64 : inp.length < 2 ^ 64 := by
    have h1 := inv.wf.in_fits; have h2 := inv.wf.out_fits; have h3 := inv.wf.lbl_fits
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at h1 h2 h3; omega
  have hge : rest'.length + 1 ≤ inp.length := by
    have h := congrArg List.length inv.suffix
    simp only [List.length_drop, List.length_cons] at h; omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp c rest' inv.suffix
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p2_prefix inp cap c rest' labF labNow m emitted s inv
  -- dispatch to 600 (per comment char)
  have hdispatch : ∃ d sd, runFuel 0 d s4 = sd ∧ 0 < d ∧
      sd.pc = BitVec.ofNat 64 (Image1.coreAddr + 600) ∧ sd.mem = s4.mem ∧
      (∀ i, i ≠ 28 → sd.rget i = s4.rget i) := by
    rcases hc with h35 | h59
    · subst h35
      have hb := li_beq_eq s4 384 35 35 (BitVec.ofNat 13 212)
        (BitVec.ofNat 64 (Image1.coreAddr + 600)) hcode4 hpc4 ht2 dec_384 dec_388
        (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
      refine ⟨2, (s4.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 600)), hb, by omega, rfl, rfl, ?_⟩
      intro i hi
      exact li_block_frame _ _ _ i hi
    · subst h59
      have hb1 := li_beq_ne s4 384 35 59 (BitVec.ofNat 13 212) hcode4 hpc4 ht2
        dec_384 dec_388 (by decide) (by decide) (by rw [coreBytes_len]; omega)
      let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 392))
      have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + (384 + 8))) := rfl
      try rw [← hv1] at hb1
      have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode4)
      have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 392) := rfl
      have ht2v1 : v1.rget 7 = BitVec.ofNat 64 59 := by
        rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (7:Nat) ≠ 28)]
        exact ht2
      have hb2 := li_beq_eq v1 392 59 59 (BitVec.ofNat 13 204)
        (BitVec.ofNat 64 (Image1.coreAddr + 600)) hc1 hpc1 ht2v1 dec_392 dec_396
        (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
      refine ⟨4, (v1.rset 28 (BitVec.ofNat 64 59)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 600)), ?_, by omega, rfl, rfl, ?_⟩
      · rw [show (4:Nat) = 2 + 2 from rfl, runFuel_add, hb1, hb2]
      · intro i hi
        rw [li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]
  obtain ⟨d, sd, hrund, hd, hpcd, hmemd, hframed⟩ := hdispatch
  have hcoded : CodeLoaded1 sd := by
    intro i hi
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi
  have h5d : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide), hidx4]
  have h10d : sd.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
    rw [hframed 10 (by decide), hframe4 10 (by decide) (by decide) (by decide) (by decide)]
    exact inv.a0
  have h11d : sd.rget 11 = BitVec.ofNat 64 inp.length := by
    rw [hframed 11 (by decide), hframe4 11 (by decide) (by decide) (by decide) (by decide)]
    exact inv.a1
  have hind : InputLoaded sd inp := by
    intro j hj
    rw [show sd.mem = s4.mem from hmemd, show s4.mem = s.mem from hmem4]
    exact inv.in_mem j hj
  obtain ⟨k, hk⟩ := comment_loop2 inp (inp.length - (inp.length - rest'.length)) sd
    (inp.length - rest'.length) hcoded hpcd h5d h10d h11d hind hlen64 inv.wf.bytes_ok
    (by omega) (by omega)
  -- spec-side: the comment unfolds (scan and emit)
  have hsc_step : Hex1.scan1 .High labNow emitted.length (c :: rest')
      = Hex1.scan1 .High labNow emitted.length (Hex0.skipComment rest') := by
    rw [Hex1.scan1]
    rw [if_pos hcm]
  have hem_step : Hex1.emit1 .High labF emitted.length (c :: rest')
      = Hex1.emit1 .High labF emitted.length (Hex0.skipComment rest') := by
    rw [Hex1.emit1]
    rw [if_pos hcm]
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  rcases hk with ⟨q, hq1, hq2, hq3, hqskip, hp, h5q, hmemq, hothq⟩ |
                 ⟨hqskip, hp, h5q, hmemq, hothq⟩
  · -- newline found at q: back to the loop head on suffix `drop q`
    rw [hrest'_eq] at hqskip
    have hmemfin : (runFuel 0 k sd).mem = s.mem := by
      rw [hmemq, hmemd, hmem4]
    have hregfin : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
        (runFuel 0 k sd).rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hothq i h5 h7 h28]
      exact hframe_sd i h0 h5 h7 h28
    have hdq : inp.drop q = 10 :: inp.drop (q + 1) := by
      rw [List.drop_eq_getElem_cons hq2,
          show inp[q] = inp.getD q 0 from List.getElem_eq_getD 0, hq3]
    have hsc_nl : Hex1.scan1 .High labNow emitted.length (inp.drop q)
        = Hex1.scan1 .High labNow emitted.length (inp.drop (q + 1)) := by
      rw [hdq]
      rw [Hex1.scan1]
      rw [if_neg (by decide), if_pos (by decide)]
    have hem_nl : Hex1.emit1 .High labF emitted.length (inp.drop q)
        = Hex1.emit1 .High labF emitted.length (inp.drop (q + 1)) := by
      rw [hdq]
      rw [Hex1.emit1]
      rw [if_neg (by decide), if_pos (by decide)]
    refine ⟨4 + (d + k), _, by omega,
      by rw [runFuel_add, hrun4, runFuel_add, hrund], Or.inl ⟨inp.drop q, ?_, ?_⟩⟩
    · simp only [List.length_drop, List.length_cons]
      omega
    exact {
      wf := inv.wf
      at_loop := hp
      code := by
        intro i hi
        rw [hmemfin]
        exact inv.code i hi
      a0 := by rw [hregfin 10 (by decide) (by decide) (by decide) (by decide)]; exact inv.a0
      a1 := by rw [hregfin 11 (by decide) (by decide) (by decide) (by decide)]; exact inv.a1
      a2 := by rw [hregfin 12 (by decide) (by decide) (by decide) (by decide)]; exact inv.a2
      a3 := by rw [hregfin 13 (by decide) (by decide) (by decide) (by decide)]; exact inv.a3
      a4 := by rw [hregfin 14 (by decide) (by decide) (by decide) (by decide)]; exact inv.a4
      ra0 := by rw [hregfin 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0
      in_mem := by
        intro j hj
        rw [hmemfin]
        exact inv.in_mem j hj
      idx := by
        rw [h5q]
        congr 1
        simp only [List.length_drop]
        omega
      suffix := by
        have : inp.length - (inp.drop q).length = q := by
          simp only [List.length_drop]
          omega
        rw [this]
      outidx := by
        rw [hregfin 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx
      out_mem := by
        intro j hj
        rw [hmemfin]
        exact inv.out_mem j hj
      tbl := by
        intro cc hcc kk hkk
        rw [hmemfin]
        exact inv.tbl cc hcc kk hkk
      m_le := inv.m_le
      lab_le := inv.lab_le
      scan_inp := inv.scan_inp
      scan_ok := by
        rw [hsc_nl, ← hqskip, ← hsc_step]
        exact inv.scan_ok
      spec := by
        rw [hem_nl, ← hqskip, ← hem_step]
        exact inv.spec }
  · -- EOF inside the comment: the residual emit is complete -> Ok exit
    rw [hrest'_eq] at hqskip
    have hem_done : Hex1.emit1 .High labF emitted.length (c :: rest') = ([], .Ok) := by
      rw [hem_step, hqskip]
      rw [Hex1.emit1]
    have hemit_whole : Hex1.emit1 .High labF 0 inp = (emitted, .Ok) := by
      have h := inv.spec
      rw [hem_done] at h
      simpa using h
    have hmemfin : (runFuel 0 k sd).mem = s.mem := by
      rw [hmemq, hmemd, hmem4]
    have hregfin : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 →
        (runFuel 0 k sd).rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hothq i h5 h7 h28]
      exact hframe_sd i h0 h5 h7 h28
    have hcodefin : CodeLoaded1 (runFuel 0 k sd) := by
      intro i hi
      rw [hmemfin]
      exact inv.code i hi
    obtain ⟨f, hrunf, hres⟩ := p2_ok_exit inp cap labF m emitted (runFuel 0 k sd) hp
      hcodefin
      (by rw [hregfin 1 (by decide) (by decide) (by decide) (by decide)]; exact inv.ra0)
      (by rw [hregfin 6 (by decide) (by decide) (by decide) (by decide)]; exact inv.outidx)
      (by
        intro j hj
        rw [hmemfin]
        exact inv.out_mem j hj)
      inv.scan_inp inv.m_le hemit_whole
    refine ⟨4 + (d + (k + 3)), f, by omega, ?_, Or.inr hres⟩
    rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunf]


/-! ## Pass 2: byte tokens -- value chains (these COMPUTE the nibbles; pass 1
    already validated them, so there are no error branches). -/


set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The full pass-2 dispatch fall-through (384..436): a non-special char
    reaches the high-nibble value chain at 440. Touches only `t3`/`pc`. -/
theorem p2_byte_fall (s4 : State) (c : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 384))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc64 : c < 2 ^ 64)
    (hne : c ≠ 35 ∧ c ≠ 59 ∧ c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 ∧ c ≠ 58 ∧ c ≠ 37) :
    ∃ s', runFuel 0 14 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 440) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  obtain ⟨h35, h59, h10n, h32, h95, h58, h37⟩ := hne
  have hb1 := li_beq_ne s4 384 35 c (BitVec.ofNat 13 212) hcode hpc ht2 dec_384 dec_388
    (by decide) (ofNat_ne c 35 hc64 (by decide) h35) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 392))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (384 + 8))) := rfl
  try rw [← hv1] at hb1
  have hcv1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpcv1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 392) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 c := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  have hb2 := li_beq_ne v1 392 59 c (BitVec.ofNat 13 204) hcv1 hpcv1 ht2v1 dec_392 dec_396
    (by decide) (ofNat_ne c 59 hc64 (by decide) h59) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 400))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (392 + 8))) := rfl
  try rw [← hv2] at hb2
  have hcv2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv1)
  have hpcv2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 400) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 c := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have hb3 := li_beq_ne v2 400 10 c (BitVec.ofNat 13 8156) hcv2 hpcv2 ht2v2 dec_400 dec_404
    (by decide) (ofNat_ne c 10 hc64 (by decide) h10n) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 408))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (400 + 8))) := rfl
  try rw [← hv3] at hb3
  have hcv3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv2)
  have hpcv3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 408) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 c := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  have hb4 := li_beq_ne v3 408 32 c (BitVec.ofNat 13 8148) hcv3 hpcv3 ht2v3 dec_408 dec_412
    (by decide) (ofNat_ne c 32 hc64 (by decide) h32) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 416))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (408 + 8))) := rfl
  try rw [← hv4] at hb4
  have hcv4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv3)
  have hpcv4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 416) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 c := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  have hb5 := li_beq_ne v4 416 95 c (BitVec.ofNat 13 8140) hcv4 hpcv4 ht2v4 dec_416 dec_420
    (by decide) (ofNat_ne c 95 hc64 (by decide) h95) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 424))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (416 + 8))) := rfl
  try rw [← hv5] at hb5
  have hcv5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv4)
  have hpcv5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 424) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 c := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  have hb6 := li_beq_ne v5 424 58 c (BitVec.ofNat 13 88) hcv5 hpcv5 ht2v5 dec_424 dec_428
    (by decide) (ofNat_ne c 58 hc64 (by decide) h58) (by rw [coreBytes_len]; omega)
  let v6 := (v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 432))
  have hv6 : v6 = (v5.rset 28 (BitVec.ofNat 64 58)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (424 + 8))) := rfl
  try rw [← hv6] at hb6
  have hcv6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcv5)
  have hpcv6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 432) := rfl
  have ht2v6 : v6.rget 7 = BitVec.ofNat 64 c := by
    rw [hv6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v5
  have hb7 := li_beq_ne v6 432 37 c (BitVec.ofNat 13 88) hcv6 hpcv6 ht2v6 dec_432 dec_436
    (by decide) (ofNat_ne c 37 hc64 (by decide) h37) (by rw [coreBytes_len]; omega)
  let vF := (v6.rset 28 (BitVec.ofNat 64 37)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 440))
  have hvF : vF = (v6.rset 28 (BitVec.ofNat 64 37)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (432 + 8))) := rfl
  try rw [← hvF] at hb7
  refine ⟨vF, ?_, rfl, rfl, ?_⟩
  · rw [show (14:Nat) = 2 + (2 + (2 + (2 + (2 + (2 + (2)))))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2,
        runFuel_add, hb3,
        runFuel_add, hb4,
        runFuel_add, hb5,
        runFuel_add, hb6,
        hb7]
  · intro i hi
    rw [hvF, li_block_frame _ _ _ i hi, hv6,
        li_block_frame _ _ _ i hi, hv5,
        li_block_frame _ _ _ i hi, hv4,
        li_block_frame _ _ _ i hi, hv3,
        li_block_frame _ _ _ i hi, hv2,
        li_block_frame _ _ _ i hi, hv1,
        li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- High-nibble value (offsets 440..456): `t4 := nibble c`, landing at 460.
    Touches only `t3`/`t4`/`pc`. -/
theorem p2_hi_value (s4 : State) (c hi : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 440))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc256 : c < 256)
    (hn : Hex0.nibble c = some hi) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 460) ∧
      s'.rget 29 = BitVec.ofNat 64 hi ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → i ≠ 29 → s'.rget i = s4.rget i) := by
  have hc63 : c < 2 ^ 63 := by omega
  have hc64 : c < 2 ^ 64 := by omega
  have hcase : (48 ≤ c ∧ c ≤ 57 ∧ c - 48 = hi) ∨ (65 ≤ c ∧ c ≤ 70 ∧ c - 55 = hi) := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn
      exact Or.inl ⟨hd.1, hd.2, Option.some.inj hn⟩
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn
        exact Or.inr ⟨hl.1, hl.2, Option.some.inj hn⟩
      · rw [if_neg hl] at hn
        exact absurd hn (by simp)
  rcases hcase with ⟨h48, h57, hhi⟩ | ⟨h65, h70, hhi⟩
  · -- digit '0'..'9'
    have b1 := li_blt_t s4 440 58 c (BitVec.ofNat 13 12)
      (BitVec.ofNat 64 (Image1.coreAddr + 456)) hcode hpc ht2 dec_440 dec_444
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 456))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 456)) := rfl
    try rw [← hw1] at b1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 456) := rfl
    have hqw1 : w1.pc ≠ 0 := by rw [hpcw1]; exact corePc_ne_zero 456 (by omega)
    have h7w1 : w1.rget 7 = BitVec.ofNat 64 c := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hu := step_addi w1 456 29 7 (BitVec.ofNat 12 4048) hcw1
      (by rw [coreBytes_len]; omega) hpcw1 dec_456
    rw [h7w1, nibble_addi c 48 (BitVec.ofNat 12 4048) (by decide) h48 hc64,
        show c - 48 = hi from hhi,
        show w1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 460) from by
          rw [hpcw1]; decide] at hu
    refine ⟨2 + 1, (w1.rset 29 (BitVec.ofNat 64 hi)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 460)), ?_, by omega, rfl, ?_, rfl, ?_⟩
    · rw [runFuel_add, b1, runFuel_one _ hqw1, hu]
    · rw [Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    · intro i h28 hreg
      by_cases h0 : i = 0
      · simp [h0]
      rw [Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg hreg,
          hw1, li_block_frame _ _ _ i h28]
  · -- letter 'A'..'F'
    have b1 := li_blt_nt s4 440 58 c (BitVec.ofNat 13 12) hcode hpc ht2 dec_440 dec_444
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 448))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (440 + 8))) := rfl
    try rw [← hw1] at b1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 448) := rfl
    have hqw1 : w1.pc ≠ 0 := by rw [hpcw1]; exact corePc_ne_zero 448 (by omega)
    have h7w1 : w1.rget 7 = BitVec.ofNat 64 c := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hu := step_addi w1 448 29 7 (BitVec.ofNat 12 4041) hcw1
      (by rw [coreBytes_len]; omega) hpcw1 dec_448
    rw [h7w1, nibble_addi c 55 (BitVec.ofNat 12 4041) (by decide) (by omega) hc64,
        show c - 55 = hi from hhi,
        show w1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 452) from by
          rw [hpcw1]; decide] at hu
    let w2 := (w1.rset 29 (BitVec.ofNat 64 hi)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 452))
    have hw2 : w2 = (w1.rset 29 (BitVec.ofNat 64 hi)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 452)) := rfl
    try rw [← hw2] at hu
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 452) := rfl
    have hqw2 : w2.pc ≠ 0 := by rw [hpcw2]; exact corePc_ne_zero 452 (by omega)
    have hjal : step w2 = w2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 460)) := by
      rw [step_jal w2 452 0 (BitVec.ofNat 21 8) hcw2 (by rw [coreBytes_len]; omega)
          hpcw2 dec_452, rset_zero,
          show w2.pc + (BitVec.ofNat 21 8).signExtend 64
              = BitVec.ofNat 64 (Image1.coreAddr + 460) from by rw [hpcw2]; decide]
    refine ⟨2 + (1 + 1), w2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 460)), ?_,
      by omega, rfl, ?_, rfl, ?_⟩
    · rw [runFuel_add, b1, runFuel_add, runFuel_one _ hqw1, hu, runFuel_one _ hqw2, hjal]
    · rw [Hex0.Refine.setPc_rget, hw2, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    · intro i h28 hreg
      by_cases h0 : i = 0
      · simp [h0]
      rw [Hex0.Refine.setPc_rget, hw2, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) h0, if_neg hreg,
          hw1, li_block_frame _ _ _ i h28]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-2 low-char read (offsets 460..468, no EOF check -- pass 1
    certified the char exists): `add` → `lbu` → `addi`. Lands at 472 with
    `t2 = l`. -/
theorem p2_read2 (s : State) (inp : List Nat) (l idx : Nat)
    (hcode : CodeLoaded1 s)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 460))
    (h5 : s.rget 5 = BitVec.ofNat 64 idx)
    (h10 : s.rget 10 = BitVec.ofNat 64 Image1.inputAddr)
    (hin : InputLoaded s inp)
    (hidx : idx < inp.length)
    (hgetl : inp.getD idx 0 = l) (hl256 : l < 256) :
    ∃ s3, runFuel 0 3 s = s3 ∧
      s3.pc = BitVec.ofNat 64 (Image1.coreAddr + 472) ∧
      s3.rget 7 = BitVec.ofNat 64 l ∧
      s3.rget 5 = BitVec.ofNat 64 (idx + 1) ∧
      s3.mem = s.mem ∧ CodeLoaded1 s3 ∧
      (∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → s3.rget i = s.rget i) := by
  -- step 1: add t3,a0,t0
  have haddr : s.rget 10 + s.rget 5 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    rw [h10, h5]; exact addr_ofNat_succ _ _
  have hu1 : step s = (s.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 464)) := by
    rw [step_add s 460 28 10 5 hcode (by rw [coreBytes_len]; omega) hpc dec_460, haddr,
        show s.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 464) from by
          rw [hpc, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s1 := (s.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 464))
  have hs1 : s1 = (s.rset 28 (BitVec.ofNat 64 (Image1.inputAddr + idx))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 464)) := rfl
  try rw [← hs1] at hu1
  have hc1 : CodeLoaded1 s1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : s1.pc = BitVec.ofNat 64 (Image1.coreAddr + 464) := rfl
  -- step 2: lbu t2,0(t3)
  have hr28 : s1.rget 28 = BitVec.ofNat 64 (Image1.inputAddr + idx) := by
    rw [hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]; simp
  have hbyte : (s1.loadByte (s1.rget 28 + (0#12).signExtend 64)).setWidth 64
      = BitVec.ofNat 64 l := by
    rw [hr28, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
    show (s1.mem _).setWidth 64 = _
    rw [hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
    rw [hin _ hidx, hgetl, setWidth8_64 l hl256]
  have hu2 : step s1 = (s1.rset 7 (BitVec.ofNat 64 l)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 468)) := by
    rw [step_lbu s1 464 7 28 (0#12) hc1 (by rw [coreBytes_len]; omega) hpc1 dec_464]
    rw [show s1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 468) from by
      rw [hpc1, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
    rw [hbyte]
  let s2 := (s1.rset 7 (BitVec.ofNat 64 l)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 468))
  have hs2 : s2 = (s1.rset 7 (BitVec.ofNat 64 l)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 468)) := rfl
  try rw [← hs2] at hu2
  have hc2 : CodeLoaded1 s2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : s2.pc = BitVec.ofNat 64 (Image1.coreAddr + 468) := rfl
  have hr5_2 : s2.rget 5 = s.rget 5 := by
    rw [hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (5:Nat) ≠ 7), hs1, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28)]
  -- step 3: addi t0,t0,1
  have hu3 : step s2 = (s2.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 472)) := by
    rw [step_addi s2 468 5 5 (BitVec.ofNat 12 1) hc2 (by rw [coreBytes_len]; omega)
        hpc2 dec_468,
        show s2.rget 5 + (BitVec.ofNat 12 1).signExtend 64
            = BitVec.ofNat 64 (idx + 1) from by
          rw [hr5_2, h5, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide,
              show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ],
        show s2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 472) from by
          rw [hpc2, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
  let s3 := (s2.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 472))
  have hs3 : s3 = (s2.rset 5 (BitVec.ofNat 64 (idx + 1))).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 472)) := rfl
  try rw [← hs3] at hu3
  have hp0 : s.pc ≠ 0 := by rw [hpc]; exact corePc_ne_zero 460 (by omega)
  have hp1 : s1.pc ≠ 0 := by rw [hpc1]; exact corePc_ne_zero 464 (by omega)
  have hp2 : s2.pc ≠ 0 := by rw [hpc2]; exact corePc_ne_zero 468 (by omega)
  refine ⟨s3, ?_, rfl, ?_, ?_, ?_, codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2), ?_⟩
  · simp only [runFuel]
    rw [hu1, hu2, hu3, if_neg hp0, if_neg hp1, if_neg hp2]
  · rw [hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 5), hs2, Hex0.Refine.setPc_rget,
        rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
    simp
  · rw [hs3, hs2, hs1]
    simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
  · intro i h0 h5i h7 h28
    rw [hs3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5i,
        hs2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7,
        hs1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Low-nibble value (offsets 472..488): `t5 := nibble l`, landing at 492.
    Touches only `t3`/`t5`/`pc`. -/
theorem p2_lo_value (s4 : State) (c hi : Nat) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 472))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 c) (hc256 : c < 256)
    (hn : Hex0.nibble c = some hi) :
    ∃ n s', runFuel 0 n s4 = s' ∧ 0 < n ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 492) ∧
      s'.rget 30 = BitVec.ofNat 64 hi ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → i ≠ 30 → s'.rget i = s4.rget i) := by
  have hc63 : c < 2 ^ 63 := by omega
  have hc64 : c < 2 ^ 64 := by omega
  have hcase : (48 ≤ c ∧ c ≤ 57 ∧ c - 48 = hi) ∨ (65 ≤ c ∧ c ≤ 70 ∧ c - 55 = hi) := by
    simp only [Hex0.nibble] at hn
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · rw [if_pos hd] at hn
      exact Or.inl ⟨hd.1, hd.2, Option.some.inj hn⟩
    · rw [if_neg hd] at hn
      by_cases hl : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos hl] at hn
        exact Or.inr ⟨hl.1, hl.2, Option.some.inj hn⟩
      · rw [if_neg hl] at hn
        exact absurd hn (by simp)
  rcases hcase with ⟨h48, h57, hhi⟩ | ⟨h65, h70, hhi⟩
  · -- digit '0'..'9'
    have b1 := li_blt_t s4 472 58 c (BitVec.ofNat 13 12)
      (BitVec.ofNat 64 (Image1.coreAddr + 488)) hcode hpc ht2 dec_472 dec_476
      (by decide) (by omega) hc63 (by decide) (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 488))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 488)) := rfl
    try rw [← hw1] at b1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 488) := rfl
    have hqw1 : w1.pc ≠ 0 := by rw [hpcw1]; exact corePc_ne_zero 488 (by omega)
    have h7w1 : w1.rget 7 = BitVec.ofNat 64 c := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hu := step_addi w1 488 30 7 (BitVec.ofNat 12 4048) hcw1
      (by rw [coreBytes_len]; omega) hpcw1 dec_488
    rw [h7w1, nibble_addi c 48 (BitVec.ofNat 12 4048) (by decide) h48 hc64,
        show c - 48 = hi from hhi,
        show w1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 492) from by
          rw [hpcw1]; decide] at hu
    refine ⟨2 + 1, (w1.rset 30 (BitVec.ofNat 64 hi)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + 492)), ?_, by omega, rfl, ?_, rfl, ?_⟩
    · rw [runFuel_add, b1, runFuel_one _ hqw1, hu]
    · rw [Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    · intro i h28 hreg
      by_cases h0 : i = 0
      · simp [h0]
      rw [Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg hreg,
          hw1, li_block_frame _ _ _ i h28]
  · -- letter 'A'..'F'
    have b1 := li_blt_nt s4 472 58 c (BitVec.ofNat 13 12) hcode hpc ht2 dec_472 dec_476
      (by decide) (by omega) hc63 (by decide) (by rw [coreBytes_len]; omega)
    let w1 := (s4.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 480))
    have hw1 : w1 = (s4.rset 28 (BitVec.ofNat 64 58)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + (472 + 8))) := rfl
    try rw [← hw1] at b1
    have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
    have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 480) := rfl
    have hqw1 : w1.pc ≠ 0 := by rw [hpcw1]; exact corePc_ne_zero 480 (by omega)
    have h7w1 : w1.rget 7 = BitVec.ofNat 64 c := by
      rw [hw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 28)]
      exact ht2
    have hu := step_addi w1 480 30 7 (BitVec.ofNat 12 4041) hcw1
      (by rw [coreBytes_len]; omega) hpcw1 dec_480
    rw [h7w1, nibble_addi c 55 (BitVec.ofNat 12 4041) (by decide) (by omega) hc64,
        show c - 55 = hi from hhi,
        show w1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 484) from by
          rw [hpcw1]; decide] at hu
    let w2 := (w1.rset 30 (BitVec.ofNat 64 hi)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 484))
    have hw2 : w2 = (w1.rset 30 (BitVec.ofNat 64 hi)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 484)) := rfl
    try rw [← hw2] at hu
    have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
    have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 484) := rfl
    have hqw2 : w2.pc ≠ 0 := by rw [hpcw2]; exact corePc_ne_zero 484 (by omega)
    have hjal : step w2 = w2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 492)) := by
      rw [step_jal w2 484 0 (BitVec.ofNat 21 8) hcw2 (by rw [coreBytes_len]; omega)
          hpcw2 dec_484, rset_zero,
          show w2.pc + (BitVec.ofNat 21 8).signExtend 64
              = BitVec.ofNat 64 (Image1.coreAddr + 492) from by rw [hpcw2]; decide]
    refine ⟨2 + (1 + 1), w2.setPc (BitVec.ofNat 64 (Image1.coreAddr + 492)), ?_,
      by omega, rfl, ?_, rfl, ?_⟩
    · rw [runFuel_add, b1, runFuel_add, runFuel_one _ hqw1, hu, runFuel_one _ hqw2, hjal]
    · rw [Hex0.Refine.setPc_rget, hw2, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    · intro i h28 hreg
      by_cases h0 : i = 0
      · simp [h0]
      rw [Hex0.Refine.setPc_rget, hw2, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) h0, if_neg hreg,
          hw1, li_block_frame _ _ _ i h28]

/-! ## Pass 2: byte tokens, assembled. -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-2 iteration for a byte token: the machine computes the
    nibbles (validated by pass 1, via `scan_ok`), emits `hi*16+lo` at
    `outAddr + |emitted|`, and loops back. -/
theorem p2_byte (inp : List Nat) (cap : Nat) (c : Nat) (rest' : List Nat)
    (labF labNow : Labels) (m : Nat) (emitted : List Nat) (s : State)
    (inv : P2Inv inp cap s labF labNow m emitted (c :: rest'))
    (hsc : Hex0.isComment c = false) (hss : Hex0.isSpace c = false)
    (hncol : (c == Hex1.c_colon) = false) (hnpct : (c == Hex1.c_pct) = false) :
    ∃ n s' l rest2 b, rest' = l :: rest2 ∧ 0 < n ∧ runFuel 0 n s = s' ∧
      P2Inv inp cap s' labF labNow m (emitted ++ [b]) rest2 := by
  have hlbl := inv.wf.lbl_fits
  have hin := inv.wf.in_fits
  have hout := inv.wf.out_fits
  have hcap63 := inv.wf.cap63
  have hlen64 : inp.length < 2 ^ 64 := by
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hin hout hlbl
    omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp c rest' inv.suffix
  have hc256 : c < 256 := by
    apply inv.wf.bytes_ok
    have : c ∈ inp.drop (inp.length - (c :: rest').length) := by
      rw [inv.suffix]; exact List.mem_cons_self
    exact List.drop_subset _ _ this
  have hc64 : c < 2 ^ 64 := by omega
  have hne7 : c ≠ 35 ∧ c ≠ 59 ∧ c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 95 ∧ c ≠ 58 ∧ c ≠ 37 := by
    simp only [Hex0.isComment, Hex0.c_hash, Hex0.c_semi, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hsc
    simp only [Hex0.isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hss
    simp only [Hex1.c_colon, beq_eq_false_iff_ne] at hncol
    simp only [Hex1.c_pct, beq_eq_false_iff_ne] at hnpct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  -- the scan certifies the token shape
  have hscu := inv.scan_ok
  rw [Hex1.scan1] at hscu
  rw [if_neg (by simp [hsc]), if_neg (by simp [hss]), if_neg (by simp [hncol]),
      if_neg (by simp [hnpct])] at hscu
  -- machine: prefix + dispatch fall-through to 440
  obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
    p2_prefix inp cap c rest' labF labNow m emitted s inv
  obtain ⟨sd, hrund, hpcd, hmemd, hframed⟩ := p2_byte_fall s4 c hcode4 hpc4 ht2 hc64 hne7
  have hcoded : CodeLoaded1 sd := by
    intro i hi2
    rw [show sd.mem = s4.mem from hmemd]
    exact hcode4 i hi2
  have hmem_sd : sd.mem = s.mem := by rw [hmemd, hmem4]
  have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
    intro i h0 h5 h7 h28
    rw [hframed i h28]
    exact hframe4 i h0 h5 h7 h28
  have ht2d : sd.rget 7 = BitVec.ofNat 64 c := by
    rw [hframed 7 (by decide)]; exact ht2
  have h5sd : sd.rget 5 = BitVec.ofNat 64 (inp.length - rest'.length) := by
    rw [hframed 5 (by decide)]; exact hidx4
  cases hnh : Hex0.nibble c with
  | none =>
    rw [hnh] at hscu
    simp at hscu
  | some hi =>
    simp only [hnh] at hscu
    have hhi16 : hi < 16 := nibble_lt c hi hnh
    cases rest' with
    | nil =>
      rw [Hex1.scan1] at hscu
      simp at hscu
    | cons l rest2 =>
      rw [Hex1.scan1] at hscu
      cases hls : Hex1.isLowStop l with
      | true =>
        rw [if_pos hls] at hscu
        simp at hscu
      | false =>
        rw [if_neg (by simp [hls])] at hscu
        cases hnl : Hex0.nibble l with
        | none =>
          simp only [hnl] at hscu
          simp at hscu
        | some lo =>
          simp only [hnl] at hscu
          have hlo16 : lo < 16 := nibble_lt l lo hnl
          have hposm : emitted.length + 1 ≤ m := by
            have h := scan1_pos_le rest2.length .High labNow (emitted.length + 1) rest2
              (Nat.le_refl _)
            rw [hscu] at h
            exact h
          have hposcap : emitted.length < cap := by
            have := inv.m_le
            omega
          have hge2 : rest2.length + 2 ≤ inp.length := by
            have h := congrArg List.length inv.suffix
            simp only [List.length_drop, List.length_cons] at h
            omega
          have hidx1lt : inp.length - (l :: rest2).length < inp.length := by
            simp only [List.length_cons]; omega
          have hgetl : inp.getD (inp.length - (l :: rest2).length) 0 = l := by
            rw [← getD_drop]; rw [hrest'_eq]; rfl
          have hl256 : l < 256 := by
            apply inv.wf.bytes_ok
            have : l ∈ inp.drop (inp.length - (l :: rest2).length) := by
              rw [hrest'_eq]; exact List.mem_cons_self
            exact List.drop_subset _ _ this
          -- machine: high-nibble value
          obtain ⟨nH, sH, hrunH, hnH, hpcH, hr29H, hmemH, hframeH⟩ :=
            p2_hi_value sd c hi hcoded hpcd ht2d hc256 hnh
          have hcodeH : CodeLoaded1 sH := by
            intro i hi2
            rw [hmemH]
            exact hcoded i hi2
          have hmem_sH : sH.mem = s.mem := by rw [hmemH, hmem_sd]
          have hframe_sH : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → i ≠ 29 →
              sH.rget i = s.rget i := by
            intro i h0 h5 h7 h28 h29
            rw [hframeH i h28 h29]
            exact hframe_sd i h0 h5 h7 h28
          have h5H : sH.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
            rw [hframeH 5 (by decide) (by decide)]
            exact h5sd
          have h10H : sH.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
            rw [hframe_sH 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact inv.a0
          have hinH : InputLoaded sH inp := by
            intro j hj
            rw [hmem_sH]
            exact inv.in_mem j hj
          -- machine: read the low char
          obtain ⟨s8, hrun8, hpc8, ht2_8, h5_8, hmem8, hcode8, hframe8⟩ :=
            p2_read2 sH inp l (inp.length - (l :: rest2).length) hcodeH hpcH h5H h10H
              hinH hidx1lt hgetl hl256
          have hmem_s8 : s8.mem = s.mem := by rw [hmem8, hmem_sH]
          have hframe_s8 : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → i ≠ 29 →
              s8.rget i = s.rget i := by
            intro i h0 h5 h7 h28 h29
            rw [hframe8 i h0 h5 h7 h28]
            exact hframe_sH i h0 h5 h7 h28 h29
          have hr29_8 : s8.rget 29 = BitVec.ofNat 64 hi := by
            rw [hframe8 29 (by decide) (by decide) (by decide) (by decide)]
            exact hr29H
          have h5_8' : s8.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
            rw [h5_8]
            congr 1
            simp only [List.length_cons]
            omega
          -- machine: low-nibble value
          obtain ⟨nL, sL, hrunL, hnL, hpcL, hr30L, hmemL, hframeL⟩ :=
            p2_lo_value s8 l lo hcode8 hpc8 ht2_8 hl256 hnl
          have hcodeL : CodeLoaded1 sL := by
            intro i hi2
            rw [hmemL]
            exact hcode8 i hi2
          have hmem_sL : sL.mem = s.mem := by rw [hmemL, hmem_s8]
          have hframe_sL : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → i ≠ 29 → i ≠ 30 →
              sL.rget i = s.rget i := by
            intro i h0 h5 h7 h28 h29 h30
            rw [hframeL i h28 h30]
            exact hframe_s8 i h0 h5 h7 h28 h29
          have hr29L : sL.rget 29 = BitVec.ofNat 64 hi := by
            rw [hframeL 29 (by decide) (by decide)]
            exact hr29_8
          have h5L : sL.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
            rw [hframeL 5 (by decide) (by decide)]
            exact h5_8'
          have h6L : sL.rget 6 = BitVec.ofNat 64 emitted.length := by
            rw [hframe_sL 6 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.outidx
          have h12L : sL.rget 12 = BitVec.ofNat 64 Image1.outAddr := by
            rw [hframe_sL 12 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]
            exact inv.a2
          have hqL : sL.pc ≠ 0 := by rw [hpcL]; exact corePc_ne_zero 492 (by omega)
          -- store epilogue (492..512): slli/or/add/sb/addi/jal
          have hu1 : step sL = (sL.rset 29 (BitVec.ofNat 64 hi <<< 4)).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 496)) := by
            rw [step_slli sL 492 29 29 4 hcodeL (by rw [coreBytes_len]; omega) hpcL dec_492,
                hr29L,
                show sL.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 496) from by
                  rw [hpcL]; decide]
          let u1 := (sL.rset 29 (BitVec.ofNat 64 hi <<< 4)).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 496))
          have hsu1 : u1 = (sL.rset 29 (BitVec.ofNat 64 hi <<< 4)).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 496)) := rfl
          try rw [← hsu1] at hu1
          have hcu1 : CodeLoaded1 u1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcodeL)
          have hpcu1 : u1.pc = BitVec.ofNat 64 (Image1.coreAddr + 496) := rfl
          have hqu1 : u1.pc ≠ 0 := by rw [hpcu1]; exact corePc_ne_zero 496 (by omega)
          have h29u1 : u1.rget 29 = BitVec.ofNat 64 hi <<< 4 := by
            rw [hsu1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
            simp
          have h30u1 : u1.rget 30 = BitVec.ofNat 64 lo := by
            rw [hsu1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (30:Nat) ≠ 29)]
            exact hr30L
          have hu2 : step u1 = (u1.rset 29 (BitVec.ofNat 64 hi <<< 4
              ||| BitVec.ofNat 64 lo)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 500)) := by
            rw [step_or u1 496 29 29 30 hcu1 (by rw [coreBytes_len]; omega) hpcu1 dec_496,
                h29u1, h30u1,
                show u1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 500) from by
                  rw [hpcu1]; decide]
          let u2 := (u1.rset 29 (BitVec.ofNat 64 hi <<< 4 ||| BitVec.ofNat 64 lo)).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 500))
          have hsu2 : u2 = (u1.rset 29 (BitVec.ofNat 64 hi <<< 4
              ||| BitVec.ofNat 64 lo)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 500)) := rfl
          try rw [← hsu2] at hu2
          have hcu2 : CodeLoaded1 u2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcu1)
          have hpcu2 : u2.pc = BitVec.ofNat 64 (Image1.coreAddr + 500) := rfl
          have hqu2 : u2.pc ≠ 0 := by rw [hpcu2]; exact corePc_ne_zero 500 (by omega)
          have h12u2 : u2.rget 12 = BitVec.ofNat 64 Image1.outAddr := by
            rw [hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (12:Nat) ≠ 29), hsu1, Hex0.Refine.setPc_rget,
                rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (12:Nat) ≠ 29)]
            exact h12L
          have h6u2 : u2.rget 6 = BitVec.ofNat 64 emitted.length := by
            rw [hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (6:Nat) ≠ 29), hsu1, Hex0.Refine.setPc_rget,
                rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat) ≠ 29)]
            exact h6L
          have hu3 : step u2 = (u2.rset 28 (BitVec.ofNat 64
              (Image1.outAddr + emitted.length))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 504)) := by
            rw [step_add u2 500 28 12 6 hcu2 (by rw [coreBytes_len]; omega) hpcu2 dec_500,
                show u2.rget 12 + u2.rget 6 = BitVec.ofNat 64
                    (Image1.outAddr + emitted.length) from by
                  rw [h12u2, h6u2]; exact addr_ofNat_succ _ _,
                show u2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 504) from by
                  rw [hpcu2]; decide]
          let u3 := (u2.rset 28 (BitVec.ofNat 64 (Image1.outAddr + emitted.length))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 504))
          have hsu3 : u3 = (u2.rset 28 (BitVec.ofNat 64
              (Image1.outAddr + emitted.length))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 504)) := rfl
          try rw [← hsu3] at hu3
          have hcu3 : CodeLoaded1 u3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcu2)
          have hpcu3 : u3.pc = BitVec.ofNat 64 (Image1.coreAddr + 504) := rfl
          have hqu3 : u3.pc ≠ 0 := by rw [hpcu3]; exact corePc_ne_zero 504 (by omega)
          have h28u3 : u3.rget 28 = BitVec.ofNat 64 (Image1.outAddr + emitted.length) := by
            rw [hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
            simp
          have h29u3 : u3.rget 29 = BitVec.ofNat 64 hi <<< 4 ||| BitVec.ofNat 64 lo := by
            rw [hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (29:Nat) ≠ 28), hsu2, Hex0.Refine.setPc_rget,
                rset_rget _ _ _ _ (by decide) (by decide)]
            simp
          have h6u3 : u3.rget 6 = BitVec.ofNat 64 emitted.length := by
            rw [hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (6:Nat) ≠ 28)]
            exact h6u2
          have hmem_u3 : u3.mem = s.mem := by
            rw [hsu3, hsu2, hsu1]
            simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
            exact hmem_sL
          have hu4 : step u3 = (u3.storeByte (BitVec.ofNat 64
              (Image1.outAddr + emitted.length)) (BitVec.ofNat 8 (hi * 16 + lo))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 508)) := by
            rw [step_sb u3 504 28 29 (0#12) hcu3 (by rw [coreBytes_len]; omega) hpcu3 dec_504,
                show u3.rget 28 + (0#12).signExtend 64 = BitVec.ofNat 64
                    (Image1.outAddr + emitted.length) from by
                  rw [h28u3, show ((0#12).signExtend 64) = 0#64 from by decide,
                      BitVec.add_zero],
                show (u3.rget 29).setWidth 8 = BitVec.ofNat 8 (hi * 16 + lo) from by
                  rw [h29u3]; exact combine_nibbles hi lo hhi16 hlo16,
                show u3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 508) from by
                  rw [hpcu3]; decide]
          let u4 := (u3.storeByte (BitVec.ofNat 64 (Image1.outAddr + emitted.length))
              (BitVec.ofNat 8 (hi * 16 + lo))).setPc (BitVec.ofNat 64 (Image1.coreAddr + 508))
          have hsu4 : u4 = (u3.storeByte (BitVec.ofNat 64
              (Image1.outAddr + emitted.length)) (BitVec.ofNat 8 (hi * 16 + lo))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 508)) := rfl
          try rw [← hsu4] at hu4
          have hcu4 : CodeLoaded1 u4 :=
            codeLoaded1_setPc _ _ (codeLoaded1_storeByte u3 _ _ hcu3 (by
              intro i2 hi2
              rw [coreBytes_len] at hi2
              refine ofNat_ne _ _ ?_ ?_ ?_
              · simp only [Image1.coreAddr]; omega
              · simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega
              · simp only [Image1.coreAddr, Image1.inputAddr, Image1.outAddr] at hin ⊢
                omega))
          have hpcu4 : u4.pc = BitVec.ofNat 64 (Image1.coreAddr + 508) := rfl
          have hqu4 : u4.pc ≠ 0 := by rw [hpcu4]; exact corePc_ne_zero 508 (by omega)
          have h6u4 : u4.rget 6 = BitVec.ofNat 64 emitted.length := by
            rw [hsu4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
            exact h6u3
          have hu5 : step u4 = (u4.rset 6 (BitVec.ofNat 64 (emitted.length + 1))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 512)) := by
            rw [step_addi u4 508 6 6 (BitVec.ofNat 12 1) hcu4 (by rw [coreBytes_len]; omega)
                hpcu4 dec_508,
                show u4.rget 6 + (BitVec.ofNat 12 1).signExtend 64
                    = BitVec.ofNat 64 (emitted.length + 1) from by
                  rw [h6u4, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by
                        decide,
                      show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ],
                show u4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 512) from by
                  rw [hpcu4]; decide]
          let u5 := (u4.rset 6 (BitVec.ofNat 64 (emitted.length + 1))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 512))
          have hsu5 : u5 = (u4.rset 6 (BitVec.ofNat 64 (emitted.length + 1))).setPc
              (BitVec.ofNat 64 (Image1.coreAddr + 512)) := rfl
          try rw [← hsu5] at hu5
          have hcu5 : CodeLoaded1 u5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcu4)
          have hpcu5 : u5.pc = BitVec.ofNat 64 (Image1.coreAddr + 512) := rfl
          have hqu5 : u5.pc ≠ 0 := by rw [hpcu5]; exact corePc_ne_zero 512 (by omega)
          have hu6 : step u5 = u5.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := by
            rw [step_jal u5 512 0 (BitVec.ofNat 21 2097008) hcu5
                (by rw [coreBytes_len]; omega) hpcu5 dec_512, rset_zero,
                show u5.pc + (BitVec.ofNat 21 2097008).signExtend 64
                    = BitVec.ofNat 64 (Image1.coreAddr + 368) from by rw [hpcu5]; decide]
          let sF := u5.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368))
          have hsF : sF = u5.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := rfl
          try rw [← hsF] at hu6
          have hrunE : runFuel 0 6 sL = sF := by
            simp only [runFuel]
            rw [hu1, hu2, hu3, hu4, hu5, hu6, if_neg hqL, if_neg hqu1, if_neg hqu2,
                if_neg hqu3, if_neg hqu4, if_neg hqu5]
          have hmem_at : ∀ a, sF.mem a
              = if a = BitVec.ofNat 64 (Image1.outAddr + emitted.length)
                then BitVec.ofNat 8 (hi * 16 + lo) else s.mem a := by
            intro a
            rw [hsF, hsu5, hsu4]
            simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
            rw [storeByte_mem]
            simp only []
            rw [hmem_u3]
          have hregF : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 28 → i ≠ 29 → i ≠ 30 →
              sF.rget i = s.rget i := by
            intro i h0 h5i h6i h7i h28i h29i h30i
            rw [hsF, Hex0.Refine.setPc_rget, hsu5, Hex0.Refine.setPc_rget,
                rset_rget _ _ _ _ (by decide) h0, if_neg h6i,
                hsu4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
                hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28i,
                hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
                hsu1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i]
            exact hframe_sL i h0 h5i h7i h28i h29i h30i
          have h5F : sF.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
            rw [hsF, Hex0.Refine.setPc_rget, hsu5, Hex0.Refine.setPc_rget,
                rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 6),
                hsu4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
                hsu3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (5:Nat) ≠ 28),
                hsu2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (5:Nat) ≠ 29),
                hsu1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
                if_neg (by decide : (5:Nat) ≠ 29)]
            exact h5L
          have h6F : sF.rget 6 = BitVec.ofNat 64 (emitted.length + 1) := by
            rw [hsF, Hex0.Refine.setPc_rget, hsu5, Hex0.Refine.setPc_rget,
                rset_rget _ _ _ _ (by decide) (by decide)]
            simp
          -- spec side: the emit telescope steps through the byte
          obtain ⟨out2, st2, hrest⟩ : ∃ o s2,
              Hex1.emit1 .High labF (emitted.length + 1) rest2 = (o, s2) :=
            ⟨_, _, rfl⟩
          have hstep_e : Hex1.emit1 .High labF emitted.length (c :: l :: rest2)
              = ((hi * 16 + lo) :: out2, st2) := by
            rw [Hex1.emit1]
            rw [if_neg (by simp [hsc]), if_neg (by simp [hss]), if_neg (by simp [hncol]),
                if_neg (by simp [hnpct])]
            simp only [hnh]
            rw [Hex1.emit1]
            rw [if_neg (by simp [hls])]
            simp only [hnl, hrest]
          refine ⟨4 + (14 + (nH + (3 + (nL + 6)))), sF, l, rest2, hi * 16 + lo, rfl,
            by omega, ?_, ?_⟩
          · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrunH,
                runFuel_add, hrun8, runFuel_add, hrunL, hrunE]
          · exact {
              wf := inv.wf
              at_loop := rfl
              code := codeLoaded1_setPc _ _ hcu5
              a0 := by
                rw [hregF 10 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide)]
                exact inv.a0
              a1 := by
                rw [hregF 11 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide)]
                exact inv.a1
              a2 := by
                rw [hregF 12 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide)]
                exact inv.a2
              a3 := by
                rw [hregF 13 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide)]
                exact inv.a3
              a4 := by
                rw [hregF 14 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide)]
                exact inv.a4
              ra0 := by
                rw [hregF 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide)]
                exact inv.ra0
              in_mem := by
                intro j hj
                rw [hmem_at, if_neg (ofNat_ne _ _
                  (by
                    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr]
                      at hin hout hlbl ⊢
                    omega)
                  (by
                    simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢
                    omega)
                  (by
                    simp only [Image1.inputAddr, Image1.outAddr] at hin ⊢
                    omega))]
                exact inv.in_mem j hj
              idx := h5F
              suffix := suffix_step inp l rest2 hrest'_eq
              outidx := by
                rw [h6F]
                congr 1
                simp
              out_mem := by
                intro j hj
                rw [show (emitted ++ [hi * 16 + lo]).length = emitted.length + 1 from by
                      simp] at hj
                rw [hmem_at]
                by_cases hje : j = emitted.length
                · subst hje
                  rw [if_pos rfl]
                  simp only [List.getD_eq_getElem?_getD,
                    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
                  rfl
                · rw [if_neg (ofNat_ne _ _
                    (by
                      simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢
                      omega)
                    (by
                      simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢
                      omega)
                    (by omega))]
                  simp only [List.getD_eq_getElem?_getD,
                    List.getElem?_append_left (by omega : j < emitted.length)]
                  exact inv.out_mem j (by omega)
              tbl := by
                intro cc hcc k hk
                rw [hmem_at, if_neg (ofNat_ne _ _
                  (by
                    simp only [Image1.lblAddr] at hlbl ⊢
                    omega)
                  (by
                    simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢
                    omega)
                  (by
                    simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢
                    omega))]
                exact inv.tbl cc hcc k hk
              m_le := inv.m_le
              lab_le := inv.lab_le
              scan_inp := inv.scan_inp
              scan_ok := by
                rw [show (emitted ++ [hi * 16 + lo]).length = emitted.length + 1 from by
                      simp]
                exact hscu
              spec := by
                have h := inv.spec
                rw [hstep_e] at h
                rw [show (emitted ++ [hi * 16 + lo]).length = emitted.length + 1 from by
                      simp,
                    hrest, h]
                simp }

/-! ## Pass 2: the offset-byte value lemmas and the Undef exit. -/

/-- Byte 0 of the machine's i32 offset (`p - (pos+4)` as a 64-bit sub) is
    `offBytes`'s byte 0 (Int emod 2^32 truncation). -/
theorem offBytes_b0 (p pos : Nat) (hp : p < 2 ^ 63) (hpos : pos + 4 < 2 ^ 63) :
    (BitVec.ofNat 64 p - BitVec.ofNat 64 (pos + 4)).setWidth 8
      = BitVec.ofNat 8 ((Hex1.offBytes p pos).getD 0 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Hex1.offBytes, List.getD_cons_zero, BitVec.toNat_setWidth, BitVec.toNat_sub,
    BitVec.toNat_ofNat]
  omega

/-- Byte 1 (after one `srli 8`). -/
theorem offBytes_b1 (p pos : Nat) (hp : p < 2 ^ 63) (hpos : pos + 4 < 2 ^ 63) :
    ((BitVec.ofNat 64 p - BitVec.ofNat 64 (pos + 4)) >>> 8).setWidth 8
      = BitVec.ofNat 8 ((Hex1.offBytes p pos).getD 1 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Hex1.offBytes, List.getD_cons_succ, List.getD_cons_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- Byte 2 (after two `srli 8`). -/
theorem offBytes_b2 (p pos : Nat) (hp : p < 2 ^ 63) (hpos : pos + 4 < 2 ^ 63) :
    (((BitVec.ofNat 64 p - BitVec.ofNat 64 (pos + 4)) >>> 8) >>> 8).setWidth 8
      = BitVec.ofNat 8 ((Hex1.offBytes p pos).getD 2 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Hex1.offBytes, List.getD_cons_succ, List.getD_cons_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- Byte 3 (after three `srli 8`). -/
theorem offBytes_b3 (p pos : Nat) (hp : p < 2 ^ 63) (hpos : pos + 4 < 2 ^ 63) :
    ((((BitVec.ofNat 64 p - BitVec.ofNat 64 (pos + 4)) >>> 8) >>> 8) >>> 8).setWidth 8
      = BitVec.ofNat 8 ((Hex1.offBytes p pos).getD 3 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Hex1.offBytes, List.getD_cons_succ, List.getD_cons_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- `offBytes` has exactly 4 entries. -/
theorem offBytes_len (p pos : Nat) : (Hex1.offBytes p pos).length = 4 := by
  simp [Hex1.offBytes]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The Undef exit (offset 700): `li a0,7; mv a1,t1; ret`, producing `Result1`
    from a state whose residual emit hit an unbound reference. -/
theorem p2_undef_exit (inp : List Nat) (cap : Nat) (labF : Labels) (m : Nat)
    (emitted : List Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (Image1.coreAddr + 700))
    (hcode : CodeLoaded1 s) (hra : s.rget 1 = 0)
    (h6 : s.rget 6 = BitVec.ofNat 64 emitted.length)
    (hout : ∀ j, j < emitted.length →
      s.mem (BitVec.ofNat 64 (Image1.outAddr + j)) = BitVec.ofNat 8 (emitted.getD j 0))
    (hscan : Hex1.scan1 .High Hex1.noLabels 0 inp = (labF, m, .Ok))
    (hm : m ≤ cap)
    (hemit : Hex1.emit1 .High labF 0 inp = (emitted, .Undef)) :
    ∃ f, runFuel 0 3 s = f ∧ Result1 f inp cap := by
  obtain ⟨f, hrunf, hfpc, hfa0, hfa1, hfmem⟩ :=
    exit_t1 s 700 7 hcode hpc hra dec_700 dec_704 dec_708 (by decide)
      (by rw [coreBytes_len]; omega)
  refine ⟨f, hrunf, ?_⟩
  refine emit_result1 f inp cap labF m emitted .Undef (Or.inr rfl) hfpc hfa0 ?_ ?_ hscan
    hm hemit
  · rw [hfa1, h6]
  · intro j hj
    rw [hfmem]
    exact hout j hj

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-2 colon dispatch (from offset 384, `t2 = 58`): falls through to
    the label-skip at 516. Touches only `t3` and `pc`. -/
theorem p2_lbl_tail (s4 : State) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 384))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 58) :
    ∃ s', runFuel 0 12 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 516) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hb1 := li_beq_ne s4 384 35 58 (BitVec.ofNat 13 212) hcode hpc ht2 dec_384 dec_388
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 392))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (384 + 8))) := rfl
  try rw [← hv1] at hb1
  have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 392) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  have hb2 := li_beq_ne v1 392 59 58 (BitVec.ofNat 13 204) hc1 hpc1 ht2v1 dec_392 dec_396
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 400))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (392 + 8))) := rfl
  try rw [← hv2] at hb2
  have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 400) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have hb3 := li_beq_ne v2 400 10 58 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_400 dec_404
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 408))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (400 + 8))) := rfl
  try rw [← hv3] at hb3
  have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 408) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  have hb4 := li_beq_ne v3 408 32 58 (BitVec.ofNat 13 8148) hc3 hpc3 ht2v3 dec_408 dec_412
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 416))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (408 + 8))) := rfl
  try rw [← hv4] at hb4
  have hc4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
  have hpc4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 416) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  have hb5 := li_beq_ne v4 416 95 58 (BitVec.ofNat 13 8140) hc4 hpc4 ht2v4 dec_416 dec_420
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 424))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (416 + 8))) := rfl
  try rw [← hv5] at hb5
  have hc5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc4)
  have hpc5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 424) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 58 := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  have hb6 := li_beq_eq v5 424 58 58 (BitVec.ofNat 13 88)
    (BitVec.ofNat 64 (Image1.coreAddr + 516)) hc5 hpc5 ht2v5 dec_424 dec_428
    (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
  refine ⟨(v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 516)),
    ?_, rfl, rfl, ?_⟩
  · rw [show (12:Nat) = 2 + (2 + (2 + (2 + (2 + 2)))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, runFuel_add, hb5, hb6]
  · intro i hi
    rw [li_block_frame _ _ _ i hi, hv5, li_block_frame _ _ _ i hi, hv4,
        li_block_frame _ _ _ i hi, hv3, li_block_frame _ _ _ i hi, hv2,
        li_block_frame _ _ _ i hi, hv1, li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- A COMPLETE pass-2 iteration for a label definition: skip the label byte
    (the table already holds the final map). The residual-scan label map picks
    the definition up. -/
theorem p2_labelDef (inp : List Nat) (cap : Nat) (rest' : List Nat)
    (labF labNow : Labels) (m : Nat) (emitted : List Nat) (s : State)
    (inv : P2Inv inp cap s labF labNow m emitted (58 :: rest')) :
    ∃ n s' l rest2, rest' = l :: rest2 ∧ 0 < n ∧ runFuel 0 n s = s' ∧
      P2Inv inp cap s' labF (setLabel labNow l emitted.length) m emitted rest2 := by
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp 58 rest' inv.suffix
  -- the scan certifies the label byte exists and is fresh in `labNow`
  have hscu := inv.scan_ok
  rw [Hex1.scan1] at hscu
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)] at hscu
  cases rest' with
  | nil =>
    rw [Hex1.scan1] at hscu
    simp at hscu
  | cons l rest2 =>
    rw [Hex1.scan1] at hscu
    cases hll : labNow l with
    | some p =>
      simp only [hll] at hscu
      simp at hscu
    | none =>
      simp only [hll] at hscu
      -- hscu : scan1 .High (setLabel labNow l emitted.length) emitted.length rest2
      --        = (labF, m, .Ok)
      have hge2 : rest2.length + 2 ≤ inp.length := by
        have h := congrArg List.length inv.suffix
        simp only [List.length_drop, List.length_cons] at h
        omega
      -- machine: prefix + dispatch + skip (516, 520)
      obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
        p2_prefix inp cap 58 (l :: rest2) labF labNow m emitted s inv
      obtain ⟨sd, hrund, hpcd, hmemd, hframed⟩ := p2_lbl_tail s4 hcode4 hpc4 ht2
      have hcoded : CodeLoaded1 sd := by
        intro i hi2
        rw [show sd.mem = s4.mem from hmemd]
        exact hcode4 i hi2
      have hmem_sd : sd.mem = s.mem := by rw [hmemd, hmem4]
      have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
        intro i h0 h5 h7 h28
        rw [hframed i h28]
        exact hframe4 i h0 h5 h7 h28
      have h5sd : sd.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
        rw [hframed 5 (by decide)]
        exact hidx4
      have hqd : sd.pc ≠ 0 := by rw [hpcd]; exact corePc_ne_zero 516 (by omega)
      -- step: addi t0,t0,1 (skip the label byte)
      have hu1 : step sd = (sd.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 520)) := by
        rw [step_addi sd 516 5 5 (BitVec.ofNat 12 1) hcoded (by rw [coreBytes_len]; omega)
            hpcd dec_516,
            show sd.rget 5 + (BitVec.ofNat 12 1).signExtend 64
                = BitVec.ofNat 64 (inp.length - rest2.length) from by
              rw [h5sd, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide,
                  show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
              congr 1
              simp only [List.length_cons]
              omega,
            show sd.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 520) from by
              rw [hpcd, show (4:Word) = BitVec.ofNat 64 4 from rfl, addr_ofNat_succ]]
      let u1 := (sd.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 520))
      have hsu1 : u1 = (sd.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 520)) := rfl
      try rw [← hsu1] at hu1
      have hcu1 : CodeLoaded1 u1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcoded)
      have hpcu1 : u1.pc = BitVec.ofNat 64 (Image1.coreAddr + 520) := rfl
      have hqu1 : u1.pc ≠ 0 := by rw [hpcu1]; exact corePc_ne_zero 520 (by omega)
      -- step: j 368
      have hu2 : step u1 = u1.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := by
        rw [step_jal u1 520 0 (BitVec.ofNat 21 2097000) hcu1 (by rw [coreBytes_len]; omega)
            hpcu1 dec_520, rset_zero,
            show u1.pc + (BitVec.ofNat 21 2097000).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 368) from by rw [hpcu1]; decide]
      let sF := u1.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368))
      have hsF : sF = u1.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := rfl
      try rw [← hsF] at hu2
      have hrun2 : runFuel 0 2 sd = sF := by
        simp only [runFuel]
        rw [hu1, hu2, if_neg hqd, if_neg hqu1]
      have hmemF : sF.mem = s.mem := by
        rw [hsF, hsu1]
        simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
        exact hmem_sd
      have hregF : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sF.rget i = s.rget i := by
        intro i h0 h5i h7i h28i
        rw [hsF, Hex0.Refine.setPc_rget, hsu1, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) h0, if_neg h5i]
        exact hframe_sd i h0 h5i h7i h28i
      have h5F : sF.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
        rw [hsF, Hex0.Refine.setPc_rget, hsu1, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      -- the emit telescope steps through the labelDef (no output)
      have hem_step : Hex1.emit1 .High labF emitted.length (58 :: l :: rest2)
          = Hex1.emit1 .High labF emitted.length rest2 := by
        rw [Hex1.emit1]
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        rw [Hex1.emit1]
      refine ⟨4 + (12 + 2), sF, l, rest2, rfl, by omega, ?_, ?_⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, hrun2]
      · exact {
          wf := inv.wf
          at_loop := rfl
          code := by
            intro i hi2
            rw [hmemF]
            exact inv.code i hi2
          a0 := by
            rw [hregF 10 (by decide) (by decide) (by decide) (by decide)]
            exact inv.a0
          a1 := by
            rw [hregF 11 (by decide) (by decide) (by decide) (by decide)]
            exact inv.a1
          a2 := by
            rw [hregF 12 (by decide) (by decide) (by decide) (by decide)]
            exact inv.a2
          a3 := by
            rw [hregF 13 (by decide) (by decide) (by decide) (by decide)]
            exact inv.a3
          a4 := by
            rw [hregF 14 (by decide) (by decide) (by decide) (by decide)]
            exact inv.a4
          ra0 := by
            rw [hregF 1 (by decide) (by decide) (by decide) (by decide)]
            exact inv.ra0
          in_mem := by
            intro j hj
            rw [hmemF]
            exact inv.in_mem j hj
          idx := h5F
          suffix := suffix_step inp l rest2 hrest'_eq
          outidx := by
            rw [hregF 6 (by decide) (by decide) (by decide) (by decide)]
            exact inv.outidx
          out_mem := by
            intro j hj
            rw [hmemF]
            exact inv.out_mem j hj
          tbl := by
            intro cc hcc k hk
            rw [hmemF]
            exact inv.tbl cc hcc k hk
          m_le := inv.m_le
          lab_le := inv.lab_le
          scan_inp := inv.scan_inp
          scan_ok := hscu
          spec := by
            rw [← hem_step]
            exact inv.spec }

/-! ## Pass 2: label references, assembled. -/

/-- `getD` over an append, as a single if. -/
theorem getD_append (xs ys : List Nat) (j : Nat) :
    (xs ++ ys).getD j 0 = if j < xs.length then xs.getD j 0
                          else ys.getD (j - xs.length) 0 := by
  by_cases h : j < xs.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : xs.length ≤ j)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The pass-2 percent dispatch (from offset 384, `t2 = 37`): falls through to
    the reference block at 524. Touches only `t3` and `pc`. -/
theorem p2_ref_tail (s4 : State) (hcode : CodeLoaded1 s4)
    (hpc : s4.pc = BitVec.ofNat 64 (Image1.coreAddr + 384))
    (ht2 : s4.rget 7 = BitVec.ofNat 64 37) :
    ∃ s', runFuel 0 14 s4 = s' ∧
      s'.pc = BitVec.ofNat 64 (Image1.coreAddr + 524) ∧ s'.mem = s4.mem ∧
      (∀ i, i ≠ 28 → s'.rget i = s4.rget i) := by
  have hb1 := li_beq_ne s4 384 35 37 (BitVec.ofNat 13 212) hcode hpc ht2 dec_384 dec_388
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v1 := (s4.rset 28 (BitVec.ofNat 64 35)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 392))
  have hv1 : v1 = (s4.rset 28 (BitVec.ofNat 64 35)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (384 + 8))) := rfl
  try rw [← hv1] at hb1
  have hc1 : CodeLoaded1 v1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcode)
  have hpc1 : v1.pc = BitVec.ofNat 64 (Image1.coreAddr + 392) := rfl
  have ht2v1 : v1.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2
  have hb2 := li_beq_ne v1 392 59 37 (BitVec.ofNat 13 204) hc1 hpc1 ht2v1 dec_392 dec_396
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v2 := (v1.rset 28 (BitVec.ofNat 64 59)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 400))
  have hv2 : v2 = (v1.rset 28 (BitVec.ofNat 64 59)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (392 + 8))) := rfl
  try rw [← hv2] at hb2
  have hc2 : CodeLoaded1 v2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc1)
  have hpc2 : v2.pc = BitVec.ofNat 64 (Image1.coreAddr + 400) := rfl
  have ht2v2 : v2.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v1
  have hb3 := li_beq_ne v2 400 10 37 (BitVec.ofNat 13 8156) hc2 hpc2 ht2v2 dec_400 dec_404
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v3 := (v2.rset 28 (BitVec.ofNat 64 10)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 408))
  have hv3 : v3 = (v2.rset 28 (BitVec.ofNat 64 10)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (400 + 8))) := rfl
  try rw [← hv3] at hb3
  have hc3 : CodeLoaded1 v3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc2)
  have hpc3 : v3.pc = BitVec.ofNat 64 (Image1.coreAddr + 408) := rfl
  have ht2v3 : v3.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v2
  have hb4 := li_beq_ne v3 408 32 37 (BitVec.ofNat 13 8148) hc3 hpc3 ht2v3 dec_408 dec_412
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v4 := (v3.rset 28 (BitVec.ofNat 64 32)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 416))
  have hv4 : v4 = (v3.rset 28 (BitVec.ofNat 64 32)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (408 + 8))) := rfl
  try rw [← hv4] at hb4
  have hc4 : CodeLoaded1 v4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc3)
  have hpc4 : v4.pc = BitVec.ofNat 64 (Image1.coreAddr + 416) := rfl
  have ht2v4 : v4.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v3
  have hb5 := li_beq_ne v4 416 95 37 (BitVec.ofNat 13 8140) hc4 hpc4 ht2v4 dec_416 dec_420
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v5 := (v4.rset 28 (BitVec.ofNat 64 95)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 424))
  have hv5 : v5 = (v4.rset 28 (BitVec.ofNat 64 95)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (416 + 8))) := rfl
  try rw [← hv5] at hb5
  have hc5 : CodeLoaded1 v5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc4)
  have hpc5 : v5.pc = BitVec.ofNat 64 (Image1.coreAddr + 424) := rfl
  have ht2v5 : v5.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v4
  have hb6 := li_beq_ne v5 424 58 37 (BitVec.ofNat 13 88) hc5 hpc5 ht2v5 dec_424 dec_428
    (by decide) (by decide) (by rw [coreBytes_len]; omega)
  let v6 := (v5.rset 28 (BitVec.ofNat 64 58)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 432))
  have hv6 : v6 = (v5.rset 28 (BitVec.ofNat 64 58)).setPc
      (BitVec.ofNat 64 (Image1.coreAddr + (424 + 8))) := rfl
  try rw [← hv6] at hb6
  have hc6 : CodeLoaded1 v6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hc5)
  have hpc6 : v6.pc = BitVec.ofNat 64 (Image1.coreAddr + 432) := rfl
  have ht2v6 : v6.rget 7 = BitVec.ofNat 64 37 := by
    rw [hv6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
        if_neg (by decide : (7:Nat) ≠ 28)]
    exact ht2v5
  have hb7 := li_beq_eq v6 432 37 37 (BitVec.ofNat 13 88)
    (BitVec.ofNat 64 (Image1.coreAddr + 524)) hc6 hpc6 ht2v6 dec_432 dec_436
    (by decide) rfl (by decide) (by rw [coreBytes_len]; omega)
  refine ⟨(v6.rset 28 (BitVec.ofNat 64 37)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 524)),
    ?_, rfl, rfl, ?_⟩
  · rw [show (14:Nat) = 2 + (2 + (2 + (2 + (2 + (2 + 2))))) from rfl, runFuel_add, hb1,
        runFuel_add, hb2, runFuel_add, hb3, runFuel_add, hb4, runFuel_add, hb5,
        runFuel_add, hb6, hb7]
  · intro i hi
    rw [li_block_frame _ _ _ i hi, hv6, li_block_frame _ _ _ i hi, hv5,
        li_block_frame _ _ _ i hi, hv4, li_block_frame _ _ _ i hi, hv3,
        li_block_frame _ _ _ i hi, hv2, li_block_frame _ _ _ i hi, hv1,
        li_block_frame _ _ _ i hi]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- A COMPLETE pass-2 iteration for a label reference: read the label byte,
    look the slot up; on an unbound label halt `Result1` (Undef), else emit
    the 4 little-endian offset bytes and loop back. -/
theorem p2_ref (inp : List Nat) (cap : Nat) (rest' : List Nat)
    (labF labNow : Labels) (m : Nat) (emitted : List Nat) (s : State)
    (inv : P2Inv inp cap s labF labNow m emitted (37 :: rest')) :
    ∃ n s', 0 < n ∧ runFuel 0 n s = s' ∧
      ((∃ l rest2, rest' = l :: rest2 ∧ ∃ p,
          P2Inv inp cap s' labF labNow m (emitted ++ Hex1.offBytes p emitted.length)
            rest2) ∨
        Result1 s' inp cap) := by
  have hlbl := inv.wf.lbl_fits
  have hin := inv.wf.in_fits
  have hout := inv.wf.out_fits
  have hcap63 := inv.wf.cap63
  have hmle := inv.m_le
  have hlen64 : inp.length < 2 ^ 64 := by
    simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr] at hin hout hlbl
    omega
  have hrest'_eq : inp.drop (inp.length - rest'.length) = rest' :=
    suffix_step inp 37 rest' inv.suffix
  -- the scan certifies the label byte exists
  have hscu := inv.scan_ok
  rw [Hex1.scan1] at hscu
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_pos (by decide)] at hscu
  cases rest' with
  | nil =>
    rw [Hex1.scan1] at hscu
    simp at hscu
  | cons l rest2 =>
    rw [Hex1.scan1] at hscu
    -- hscu : scan1 .High labNow (emitted.length + 4) rest2 = (labF, m, .Ok)
    have hposm4 : emitted.length + 4 ≤ m := by
      have h := scan1_pos_le rest2.length .High labNow (emitted.length + 4) rest2
        (Nat.le_refl _)
      rw [hscu] at h
      exact h
    have hge2 : rest2.length + 2 ≤ inp.length := by
      have h := congrArg List.length inv.suffix
      simp only [List.length_drop, List.length_cons] at h
      omega
    have hidx1lt : inp.length - (l :: rest2).length < inp.length := by
      simp only [List.length_cons]; omega
    have hgetl : inp.getD (inp.length - (l :: rest2).length) 0 = l := by
      rw [← getD_drop]; rw [hrest'_eq]; rfl
    have hl256 : l < 256 := by
      apply inv.wf.bytes_ok
      have : l ∈ inp.drop (inp.length - (l :: rest2).length) := by
        rw [hrest'_eq]; exact List.mem_cons_self
      exact List.drop_subset _ _ this
    -- machine: prefix + dispatch to 524
    obtain ⟨s4, hrun4, hpc4, ht2, hidx4, hmem4, hcode4, hframe4⟩ :=
      p2_prefix inp cap 37 (l :: rest2) labF labNow m emitted s inv
    obtain ⟨sd, hrund, hpcd, hmemd, hframed⟩ := p2_ref_tail s4 hcode4 hpc4 ht2
    have hcoded : CodeLoaded1 sd := by
      intro i hi2
      rw [show sd.mem = s4.mem from hmemd]
      exact hcode4 i hi2
    have hmem_sd : sd.mem = s.mem := by rw [hmemd, hmem4]
    have hframe_sd : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → sd.rget i = s.rget i := by
      intro i h0 h5 h7 h28
      rw [hframed i h28]
      exact hframe4 i h0 h5 h7 h28
    have h5sd : sd.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
      rw [hframed 5 (by decide)]
      exact hidx4
    have h10sd : sd.rget 10 = BitVec.ofNat 64 Image1.inputAddr := by
      rw [hframe_sd 10 (by decide) (by decide) (by decide) (by decide)]
      exact inv.a0
    -- steps 524..544: read the label byte, address the slot, load it
    have hqd : sd.pc ≠ 0 := by rw [hpcd]; exact corePc_ne_zero 524 (by omega)
    have hu1 : step sd = (sd.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 528)) := by
      rw [step_add sd 524 28 10 5 hcoded (by rw [coreBytes_len]; omega) hpcd dec_524,
          show sd.rget 10 + sd.rget 5 = BitVec.ofNat 64
              (Image1.inputAddr + (inp.length - (l :: rest2).length)) from by
            rw [h10sd, h5sd]; exact addr_ofNat_succ _ _,
          show sd.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 528) from by
            rw [hpcd]; decide]
    let r1 := (sd.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 528))
    have hsr1 : r1 = (sd.rset 28 (BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 528)) := rfl
    try rw [← hsr1] at hu1
    have hcr1 : CodeLoaded1 r1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcoded)
    have hpcr1 : r1.pc = BitVec.ofNat 64 (Image1.coreAddr + 528) := rfl
    have hqr1 : r1.pc ≠ 0 := by rw [hpcr1]; exact corePc_ne_zero 528 (by omega)
    have h28r1 : r1.rget 28 = BitVec.ofNat 64
        (Image1.inputAddr + (inp.length - (l :: rest2).length)) := by
      rw [hsr1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have hbyte : (r1.loadByte (r1.rget 28 + (0#12).signExtend 64)).setWidth 64
        = BitVec.ofNat 64 l := by
      rw [h28r1, show (0#12).signExtend 64 = (0#64) from by decide, BitVec.add_zero]
      show (r1.mem _).setWidth 64 = _
      rw [hsr1]
      simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
      rw [hmem_sd, inv.in_mem _ hidx1lt, hgetl, setWidth8_64 l hl256]
    have hu2 : step r1 = (r1.rset 7 (BitVec.ofNat 64 l)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 532)) := by
      rw [step_lbu r1 528 7 28 (0#12) hcr1 (by rw [coreBytes_len]; omega) hpcr1 dec_528]
      rw [show r1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 532) from by
        rw [hpcr1]; decide]
      rw [hbyte]
    let r2 := (r1.rset 7 (BitVec.ofNat 64 l)).setPc (BitVec.ofNat 64 (Image1.coreAddr + 532))
    have hsr2 : r2 = (r1.rset 7 (BitVec.ofNat 64 l)).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 532)) := rfl
    try rw [← hsr2] at hu2
    have hcr2 : CodeLoaded1 r2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcr1)
    have hpcr2 : r2.pc = BitVec.ofNat 64 (Image1.coreAddr + 532) := rfl
    have hqr2 : r2.pc ≠ 0 := by rw [hpcr2]; exact corePc_ne_zero 532 (by omega)
    have h5r2 : r2.rget 5 = BitVec.ofNat 64 (inp.length - (l :: rest2).length) := by
      rw [hsr2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (5:Nat) ≠ 7), hsr1, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (5:Nat) ≠ 28)]
      exact h5sd
    have hu3 : step r2 = (r2.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 536)) := by
      rw [step_addi r2 532 5 5 (BitVec.ofNat 12 1) hcr2 (by rw [coreBytes_len]; omega)
          hpcr2 dec_532,
          show r2.rget 5 + (BitVec.ofNat 12 1).signExtend 64
              = BitVec.ofNat 64 (inp.length - rest2.length) from by
            rw [h5r2, show ((BitVec.ofNat 12 1).signExtend 64) = (1 : Word) from by decide,
                show (1:Word) = BitVec.ofNat 64 1 from rfl, addr_ofNat_succ]
            congr 1
            simp only [List.length_cons]
            omega,
          show r2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 536) from by
            rw [hpcr2]; decide]
    let r3 := (r2.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 536))
    have hsr3 : r3 = (r2.rset 5 (BitVec.ofNat 64 (inp.length - rest2.length))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 536)) := rfl
    try rw [← hsr3] at hu3
    have hcr3 : CodeLoaded1 r3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcr2)
    have hpcr3 : r3.pc = BitVec.ofNat 64 (Image1.coreAddr + 536) := rfl
    have hqr3 : r3.pc ≠ 0 := by rw [hpcr3]; exact corePc_ne_zero 536 (by omega)
    have h7r3 : r3.rget 7 = BitVec.ofNat 64 l := by
      rw [hsr3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (7:Nat) ≠ 5), hsr2, Hex0.Refine.setPc_rget,
          rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have hu4 : step r3 = (r3.rset 28 (BitVec.ofNat 64 (8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 540)) := by
      rw [step_slli r3 536 28 7 3 hcr3 (by rw [coreBytes_len]; omega) hpcr3 dec_536,
          show r3.rget 7 <<< 3 = BitVec.ofNat 64 (8 * l) from by
            rw [h7r3]; exact shl3_ofNat l hl256,
          show r3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 540) from by
            rw [hpcr3]; decide]
    let r4 := (r3.rset 28 (BitVec.ofNat 64 (8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 540))
    have hsr4 : r4 = (r3.rset 28 (BitVec.ofNat 64 (8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 540)) := rfl
    try rw [← hsr4] at hu4
    have hcr4 : CodeLoaded1 r4 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcr3)
    have hpcr4 : r4.pc = BitVec.ofNat 64 (Image1.coreAddr + 540) := rfl
    have hqr4 : r4.pc ≠ 0 := by rw [hpcr4]; exact corePc_ne_zero 540 (by omega)
    have h28r4 : r4.rget 28 = BitVec.ofNat 64 (8 * l) := by
      rw [hsr4, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have h14r4 : r4.rget 14 = BitVec.ofNat 64 Image1.lblAddr := by
      rw [hsr4, li_block_frame _ _ _ 14 (by decide),
          hsr3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (14:Nat) ≠ 5),
          hsr2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
          if_neg (by decide : (14:Nat) ≠ 7),
          hsr1, li_block_frame _ _ _ 14 (by decide),
          hframe_sd 14 (by decide) (by decide) (by decide) (by decide)]
      exact inv.a4
    have hu5 : step r4 = (r4.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 544)) := by
      rw [step_add r4 540 28 28 14 hcr4 (by rw [coreBytes_len]; omega) hpcr4 dec_540,
          show r4.rget 28 + r4.rget 14 = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) from by
            rw [h28r4, h14r4, addr_ofNat_succ]
            congr 1
            omega,
          show r4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 544) from by
            rw [hpcr4]; decide]
    let r5 := (r4.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 544))
    have hsr5 : r5 = (r4.rset 28 (BitVec.ofNat 64 (Image1.lblAddr + 8 * l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 544)) := rfl
    try rw [← hsr5] at hu5
    have hcr5 : CodeLoaded1 r5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcr4)
    have hpcr5 : r5.pc = BitVec.ofNat 64 (Image1.coreAddr + 544) := rfl
    have hqr5 : r5.pc ≠ 0 := by rw [hpcr5]; exact corePc_ne_zero 544 (by omega)
    have h28r5 : r5.rget 28 = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) := by
      rw [hsr5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have hmem_r5 : r5.mem = s.mem := by
      rw [hsr5, hsr4, hsr3, hsr2, hsr1]
      simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
      exact hmem_sd
    have htbl_r5 : TableLoaded r5 labF := by
      intro cc hcc k hk
      rw [hmem_r5]
      exact inv.tbl cc hcc k hk
    have hu6 : step r5 = (r5.rset 29 (encodeSlot (labF l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 548)) := by
      rw [step_ld r5 544 29 28 (0#12) hcr5 (by rw [coreBytes_len]; omega) hpcr5 dec_544,
          show r5.rget 28 + (0#12).signExtend 64
              = BitVec.ofNat 64 (Image1.lblAddr + 8 * l) from by
            rw [h28r5, show ((0#12).signExtend 64) = 0#64 from by decide, BitVec.add_zero],
          loadWord_slot r5 labF l hl256 htbl_r5,
          show r5.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 548) from by
            rw [hpcr5]; decide]
    let r6 := (r5.rset 29 (encodeSlot (labF l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 548))
    have hsr6 : r6 = (r5.rset 29 (encodeSlot (labF l))).setPc
        (BitVec.ofNat 64 (Image1.coreAddr + 548)) := rfl
    try rw [← hsr6] at hu6
    have hcr6 : CodeLoaded1 r6 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcr5)
    have hpcr6 : r6.pc = BitVec.ofNat 64 (Image1.coreAddr + 548) := rfl
    have hqr6 : r6.pc ≠ 0 := by rw [hpcr6]; exact corePc_ne_zero 548 (by omega)
    have h29r6 : r6.rget 29 = encodeSlot (labF l) := by
      rw [hsr6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
      simp
    have hmem_r6 : r6.mem = s.mem := by
      rw [hsr6]
      show (r5.rset 29 (encodeSlot (labF l))).mem = s.mem
      rw [Hex0.Refine.rset_mem]
      exact hmem_r5
    have hframe_r6 : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 7 → i ≠ 28 → i ≠ 29 →
        r6.rget i = s.rget i := by
      intro i h0 h5i h7i h28i h29i
      rw [hsr6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
          hsr5, li_block_frame _ _ _ i h28i,
          hsr4, li_block_frame _ _ _ i h28i,
          hsr3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h5i,
          hsr2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h7i,
          hsr1, li_block_frame _ _ _ i h28i]
      exact hframe_sd i h0 h5i h7i h28i
    have hrun6 : runFuel 0 6 sd = r6 := by
      simp only [runFuel]
      rw [hu1, hu2, hu3, hu4, hu5, hu6, if_neg hqd, if_neg hqr1, if_neg hqr2,
          if_neg hqr3, if_neg hqr4, if_neg hqr5]
    -- the slot sign test
    cases hll : labF l with
    | none =>
      -- unbound: blt taken to the Undef exit (700)
      have hu7 : step r6 = r6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 700)) := by
        rw [step_blt r6 548 29 0 (BitVec.ofNat 13 152) hcr6 (by rw [coreBytes_len]; omega)
            hpcr6 dec_548, h29r6, hll, Hex0.Refine.rget_zero, encodeSlot_none_neg]
        simp only [if_true]
        rw [show r6.pc + (BitVec.ofNat 13 152).signExtend 64
            = BitVec.ofNat 64 (Image1.coreAddr + 700) from by rw [hpcr6]; decide]
      let sE := r6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 700))
      have hsE : sE = r6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 700)) := rfl
      try rw [← hsE] at hu7
      have hrunE : runFuel 0 1 r6 = sE := by rw [runFuel_one r6 hqr6, hu7]
      have hcodeE : CodeLoaded1 sE := codeLoaded1_setPc _ _ hcr6
      have hpcE : sE.pc = BitVec.ofNat 64 (Image1.coreAddr + 700) := rfl
      -- the residual emit hits the unbound reference
      have hem_undef : Hex1.emit1 .High labF emitted.length (37 :: l :: rest2)
          = ([], .Undef) := by
        rw [Hex1.emit1]
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos (by decide)]
        rw [Hex1.emit1]
        simp only [hll]
      have hemit_whole : Hex1.emit1 .High labF 0 inp = (emitted, .Undef) := by
        have h := inv.spec
        rw [hem_undef] at h
        simpa using h
      obtain ⟨f, hrunf, hres⟩ := p2_undef_exit inp cap labF m emitted sE hpcE hcodeE
        (by
          rw [hsE, Hex0.Refine.setPc_rget,
              hframe_r6 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact inv.ra0)
        (by
          rw [hsE, Hex0.Refine.setPc_rget,
              hframe_r6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact inv.outidx)
        (by
          intro j hj
          rw [hsE, Hex0.Refine.setPc_mem, hmem_r6]
          exact inv.out_mem j hj)
        inv.scan_inp inv.m_le hemit_whole
      refine ⟨4 + (14 + (6 + (1 + 3))), f, by omega, ?_, Or.inr hres⟩
      rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrun6,
          runFuel_add, hrunE, hrunf]
    | some p =>
      -- bound: emit the 4 offset bytes
      have hpm : p ≤ m := inv.lab_le l p hll
      have hp63 : p < 2 ^ 63 := by omega
      have hpos63 : emitted.length + 4 < 2 ^ 63 := by omega
      have h29r6' : r6.rget 29 = BitVec.ofNat 64 p := by
        rw [h29r6, hll]
        rfl
      have hu7 : step r6 = r6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 552)) := by
        rw [step_blt r6 548 29 0 (BitVec.ofNat 13 152) hcr6 (by rw [coreBytes_len]; omega)
            hpcr6 dec_548, h29r6, hll, Hex0.Refine.rget_zero, encodeSlot_some_nonneg p hp63]
        simp only [Bool.false_eq_true, if_false]
        rw [show r6.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 552) from by
          rw [hpcr6]; decide]
      let w0 := r6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 552))
      have hsw0 : w0 = r6.setPc (BitVec.ofNat 64 (Image1.coreAddr + 552)) := rfl
      try rw [← hsw0] at hu7
      have hcw0 : CodeLoaded1 w0 := codeLoaded1_setPc _ _ hcr6
      have hpcw0 : w0.pc = BitVec.ofNat 64 (Image1.coreAddr + 552) := rfl
      have hqw0 : w0.pc ≠ 0 := by rw [hpcw0]; exact corePc_ne_zero 552 (by omega)
      have h6w0 : w0.rget 6 = BitVec.ofNat 64 emitted.length := by
        rw [hsw0, Hex0.Refine.setPc_rget,
            hframe_r6 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact inv.outidx
      -- t5 := t1 + 4
      have hu8 : step w0 = (w0.rset 30 (BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 556)) := by
        rw [step_addi w0 552 30 6 (BitVec.ofNat 12 4) hcw0 (by rw [coreBytes_len]; omega)
            hpcw0 dec_552,
            show w0.rget 6 + (BitVec.ofNat 12 4).signExtend 64
                = BitVec.ofNat 64 (emitted.length + 4) from by
              rw [h6w0, show ((BitVec.ofNat 12 4).signExtend 64) = BitVec.ofNat 64 4 from by
                    decide,
                  addr_ofNat_succ],
            show w0.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 556) from by
              rw [hpcw0]; decide]
      let w1 := (w0.rset 30 (BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 556))
      have hsw1 : w1 = (w0.rset 30 (BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 556)) := rfl
      try rw [← hsw1] at hu8
      have hcw1 : CodeLoaded1 w1 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw0)
      have hpcw1 : w1.pc = BitVec.ofNat 64 (Image1.coreAddr + 556) := rfl
      have hqw1 : w1.pc ≠ 0 := by rw [hpcw1]; exact corePc_ne_zero 556 (by omega)
      have h29w1 : w1.rget 29 = BitVec.ofNat 64 p := by
        rw [hsw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (29:Nat) ≠ 30), hsw0, Hex0.Refine.setPc_rget]
        exact h29r6'
      have h30w1 : w1.rget 30 = BitVec.ofNat 64 (emitted.length + 4) := by
        rw [hsw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      -- t4 := slot - (t1+4)
      have hu9 : step w1 = (w1.rset 29 (BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 560)) := by
        rw [step_sub w1 556 29 29 30 hcw1 (by rw [coreBytes_len]; omega) hpcw1 dec_556,
            h29w1, h30w1,
            show w1.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 560) from by
              rw [hpcw1]; decide]
      let w2 := (w1.rset 29 (BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 560))
      have hsw2 : w2 = (w1.rset 29 (BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 560)) := rfl
      try rw [← hsw2] at hu9
      have hcw2 : CodeLoaded1 w2 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw1)
      have hpcw2 : w2.pc = BitVec.ofNat 64 (Image1.coreAddr + 560) := rfl
      have hqw2 : w2.pc ≠ 0 := by rw [hpcw2]; exact corePc_ne_zero 560 (by omega)
      have h12w2 : w2.rget 12 = BitVec.ofNat 64 Image1.outAddr := by
        rw [hsw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (12:Nat) ≠ 29), hsw1, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (12:Nat) ≠ 30),
            hsw0, Hex0.Refine.setPc_rget,
            hframe_r6 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact inv.a2
      have h6w2 : w2.rget 6 = BitVec.ofNat 64 emitted.length := by
        rw [hsw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (6:Nat) ≠ 29), hsw1, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide), if_neg (by decide : (6:Nat) ≠ 30)]
        exact h6w0
      -- t3 := out + t1
      have hu10 : step w2 = (w2.rset 28 (BitVec.ofNat 64
          (Image1.outAddr + emitted.length))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 564)) := by
        rw [step_add w2 560 28 12 6 hcw2 (by rw [coreBytes_len]; omega) hpcw2 dec_560,
            show w2.rget 12 + w2.rget 6 = BitVec.ofNat 64
                (Image1.outAddr + emitted.length) from by
              rw [h12w2, h6w2]; exact addr_ofNat_succ _ _,
            show w2.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 564) from by
              rw [hpcw2]; decide]
      let w3 := (w2.rset 28 (BitVec.ofNat 64 (Image1.outAddr + emitted.length))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 564))
      have hsw3 : w3 = (w2.rset 28 (BitVec.ofNat 64
          (Image1.outAddr + emitted.length))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 564)) := rfl
      try rw [← hsw3] at hu10
      have hcw3 : CodeLoaded1 w3 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw2)
      have hpcw3 : w3.pc = BitVec.ofNat 64 (Image1.coreAddr + 564) := rfl
      have hqw3 : w3.pc ≠ 0 := by rw [hpcw3]; exact corePc_ne_zero 564 (by omega)
      have h28w3 : w3.rget 28 = BitVec.ofNat 64 (Image1.outAddr + emitted.length) := by
        rw [hsw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      have h29w3 : w3.rget 29 = BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4) := by
        rw [hsw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (29:Nat) ≠ 28), hsw2, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      have hmem_w3 : w3.mem = s.mem := by
        rw [hsw3, hsw2, hsw1, hsw0]
        simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem]
        exact hmem_r6
      -- the four stores with srli in between; disjointness facts first
      have hAddrOk : ∀ k : Nat, k < 4 →
          Image1.outAddr + emitted.length + k < 2 ^ 64 := by
        intro k hk
        simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢
        omega
      have hCodeNe : ∀ (A : Nat), A < 2 ^ 64 → Image1.inputAddr ≤ A →
          ∀ i2, i2 < Image1.coreBytes.length →
          BitVec.ofNat 64 (Image1.coreAddr + i2) ≠ BitVec.ofNat 64 A := by
        intro A hA64 hAlo i2 hi2
        rw [coreBytes_len] at hi2
        refine ofNat_ne _ _ ?_ hA64 ?_
        · simp only [Image1.coreAddr]; omega
        · simp only [Image1.coreAddr, Image1.inputAddr] at hAlo ⊢; omega
      have hInLe : Image1.inputAddr ≤ Image1.outAddr + emitted.length := by
        simp only [Image1.inputAddr, Image1.outAddr]; omega
      -- sb 0 (564)
      have hu11 : step w3 = (w3.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 0 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 568)) := by
        rw [step_sb w3 564 28 29 (0#12) hcw3 (by rw [coreBytes_len]; omega) hpcw3 dec_564,
            show w3.rget 28 + (0#12).signExtend 64 = BitVec.ofNat 64
                (Image1.outAddr + emitted.length) from by
              rw [h28w3, show ((0#12).signExtend 64) = 0#64 from by decide,
                  BitVec.add_zero],
            show (w3.rget 29).setWidth 8
                = BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 0 0) from by
              rw [h29w3]; exact offBytes_b0 p emitted.length hp63 hpos63,
            show w3.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 568) from by
              rw [hpcw3]; decide]
      let w4 := (w3.storeByte (BitVec.ofNat 64 (Image1.outAddr + emitted.length))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 0 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 568))
      have hsw4 : w4 = (w3.storeByte (BitVec.ofNat 64 (Image1.outAddr + emitted.length))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 0 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 568)) := rfl
      try rw [← hsw4] at hu11
      have hcw4 : CodeLoaded1 w4 :=
        codeLoaded1_setPc _ _ (codeLoaded1_storeByte w3 _ _ hcw3
          (fun i2 hi2 => hCodeNe (Image1.outAddr + emitted.length)
            (by have := hAddrOk 0 (by omega); omega) hInLe i2 hi2))
      have hpcw4 : w4.pc = BitVec.ofNat 64 (Image1.coreAddr + 568) := rfl
      have hqw4 : w4.pc ≠ 0 := by rw [hpcw4]; exact corePc_ne_zero 568 (by omega)
      have h29w4 : w4.rget 29 = BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4) := by
        rw [hsw4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h29w3
      -- srli (568)
      have hu12 : step w4 = (w4.rset 29 ((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 572)) := by
        rw [step_srli w4 568 29 29 8 hcw4 (by rw [coreBytes_len]; omega) hpcw4 dec_568,
            h29w4,
            show w4.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 572) from by
              rw [hpcw4]; decide]
      let w5 := (w4.rset 29 ((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 572))
      have hsw5 : w5 = (w4.rset 29 ((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 572)) := rfl
      try rw [← hsw5] at hu12
      have hcw5 : CodeLoaded1 w5 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw4)
      have hpcw5 : w5.pc = BitVec.ofNat 64 (Image1.coreAddr + 572) := rfl
      have hqw5 : w5.pc ≠ 0 := by rw [hpcw5]; exact corePc_ne_zero 572 (by omega)
      have h28w5 : w5.rget 28 = BitVec.ofNat 64 (Image1.outAddr + emitted.length) := by
        rw [hsw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (28:Nat) ≠ 29),
            hsw4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h28w3
      have h29w5 : w5.rget 29 = (BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8 := by
        rw [hsw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      -- sb 1 (572)
      have hu13 : step w5 = (w5.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length + 1))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 1 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 576)) := by
        rw [step_sb w5 572 28 29 (BitVec.ofNat 12 1) hcw5 (by rw [coreBytes_len]; omega)
            hpcw5 dec_572,
            show w5.rget 28 + (BitVec.ofNat 12 1).signExtend 64 = BitVec.ofNat 64
                (Image1.outAddr + emitted.length + 1) from by
              rw [h28w5, show ((BitVec.ofNat 12 1).signExtend 64)
                    = BitVec.ofNat 64 1 from by decide,
                  addr_ofNat_succ],
            show (w5.rget 29).setWidth 8
                = BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 1 0) from by
              rw [h29w5]; exact offBytes_b1 p emitted.length hp63 hpos63,
            show w5.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 576) from by
              rw [hpcw5]; decide]
      let w6 := (w5.storeByte (BitVec.ofNat 64 (Image1.outAddr + emitted.length + 1))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 1 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 576))
      have hsw6 : w6 = (w5.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length + 1))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 1 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 576)) := rfl
      try rw [← hsw6] at hu13
      have hcw6 : CodeLoaded1 w6 :=
        codeLoaded1_setPc _ _ (codeLoaded1_storeByte w5 _ _ hcw5
          (fun i2 hi2 => hCodeNe (Image1.outAddr + emitted.length + 1)
            (by have := hAddrOk 1 (by omega); omega)
            (by simp only [Image1.inputAddr, Image1.outAddr]; omega) i2 hi2))
      have hpcw6 : w6.pc = BitVec.ofNat 64 (Image1.coreAddr + 576) := rfl
      have hqw6 : w6.pc ≠ 0 := by rw [hpcw6]; exact corePc_ne_zero 576 (by omega)
      have h29w6 : w6.rget 29 = (BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8 := by
        rw [hsw6, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h29w5
      -- srli (576)
      have hu14 : step w6 = (w6.rset 29 (((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 580)) := by
        rw [step_srli w6 576 29 29 8 hcw6 (by rw [coreBytes_len]; omega) hpcw6 dec_576,
            h29w6,
            show w6.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 580) from by
              rw [hpcw6]; decide]
      let w7 := (w6.rset 29 (((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 580))
      have hsw7 : w7 = (w6.rset 29 (((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 580)) := rfl
      try rw [← hsw7] at hu14
      have hcw7 : CodeLoaded1 w7 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw6)
      have hpcw7 : w7.pc = BitVec.ofNat 64 (Image1.coreAddr + 580) := rfl
      have hqw7 : w7.pc ≠ 0 := by rw [hpcw7]; exact corePc_ne_zero 580 (by omega)
      have h28w7 : w7.rget 28 = BitVec.ofNat 64 (Image1.outAddr + emitted.length) := by
        rw [hsw7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (28:Nat) ≠ 29),
            hsw6, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h28w5
      have h29w7 : w7.rget 29 = ((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8 := by
        rw [hsw7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      -- sb 2 (580)
      have hu15 : step w7 = (w7.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length + 2))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 2 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 584)) := by
        rw [step_sb w7 580 28 29 (BitVec.ofNat 12 2) hcw7 (by rw [coreBytes_len]; omega)
            hpcw7 dec_580,
            show w7.rget 28 + (BitVec.ofNat 12 2).signExtend 64 = BitVec.ofNat 64
                (Image1.outAddr + emitted.length + 2) from by
              rw [h28w7, show ((BitVec.ofNat 12 2).signExtend 64)
                    = BitVec.ofNat 64 2 from by decide,
                  addr_ofNat_succ],
            show (w7.rget 29).setWidth 8
                = BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 2 0) from by
              rw [h29w7]; exact offBytes_b2 p emitted.length hp63 hpos63,
            show w7.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 584) from by
              rw [hpcw7]; decide]
      let w8 := (w7.storeByte (BitVec.ofNat 64 (Image1.outAddr + emitted.length + 2))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 2 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 584))
      have hsw8 : w8 = (w7.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length + 2))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 2 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 584)) := rfl
      try rw [← hsw8] at hu15
      have hcw8 : CodeLoaded1 w8 :=
        codeLoaded1_setPc _ _ (codeLoaded1_storeByte w7 _ _ hcw7
          (fun i2 hi2 => hCodeNe (Image1.outAddr + emitted.length + 2)
            (by have := hAddrOk 2 (by omega); omega)
            (by simp only [Image1.inputAddr, Image1.outAddr]; omega) i2 hi2))
      have hpcw8 : w8.pc = BitVec.ofNat 64 (Image1.coreAddr + 584) := rfl
      have hqw8 : w8.pc ≠ 0 := by rw [hpcw8]; exact corePc_ne_zero 584 (by omega)
      have h29w8 : w8.rget 29 = ((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8 := by
        rw [hsw8, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h29w7
      -- srli (584)
      have hu16 : step w8 = (w8.rset 29 ((((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 588)) := by
        rw [step_srli w8 584 29 29 8 hcw8 (by rw [coreBytes_len]; omega) hpcw8 dec_584,
            h29w8,
            show w8.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 588) from by
              rw [hpcw8]; decide]
      let w9 := (w8.rset 29 ((((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 588))
      have hsw9 : w9 = (w8.rset 29 ((((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8) >>> 8)).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 588)) := rfl
      try rw [← hsw9] at hu16
      have hcw9 : CodeLoaded1 w9 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw8)
      have hpcw9 : w9.pc = BitVec.ofNat 64 (Image1.coreAddr + 588) := rfl
      have hqw9 : w9.pc ≠ 0 := by rw [hpcw9]; exact corePc_ne_zero 588 (by omega)
      have h28w9 : w9.rget 28 = BitVec.ofNat 64 (Image1.outAddr + emitted.length) := by
        rw [hsw9, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (28:Nat) ≠ 29),
            hsw8, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h28w7
      have h29w9 : w9.rget 29 = (((BitVec.ofNat 64 p
          - BitVec.ofNat 64 (emitted.length + 4)) >>> 8) >>> 8) >>> 8 := by
        rw [hsw9, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      -- sb 3 (588)
      have hu17 : step w9 = (w9.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length + 3))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 3 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 592)) := by
        rw [step_sb w9 588 28 29 (BitVec.ofNat 12 3) hcw9 (by rw [coreBytes_len]; omega)
            hpcw9 dec_588,
            show w9.rget 28 + (BitVec.ofNat 12 3).signExtend 64 = BitVec.ofNat 64
                (Image1.outAddr + emitted.length + 3) from by
              rw [h28w9, show ((BitVec.ofNat 12 3).signExtend 64)
                    = BitVec.ofNat 64 3 from by decide,
                  addr_ofNat_succ],
            show (w9.rget 29).setWidth 8
                = BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 3 0) from by
              rw [h29w9]; exact offBytes_b3 p emitted.length hp63 hpos63,
            show w9.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 592) from by
              rw [hpcw9]; decide]
      let w10 := (w9.storeByte (BitVec.ofNat 64 (Image1.outAddr + emitted.length + 3))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 3 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 592))
      have hsw10 : w10 = (w9.storeByte (BitVec.ofNat 64
          (Image1.outAddr + emitted.length + 3))
          (BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 3 0))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 592)) := rfl
      try rw [← hsw10] at hu17
      have hcw10 : CodeLoaded1 w10 :=
        codeLoaded1_setPc _ _ (codeLoaded1_storeByte w9 _ _ hcw9
          (fun i2 hi2 => hCodeNe (Image1.outAddr + emitted.length + 3)
            (by have := hAddrOk 3 (by omega); omega)
            (by simp only [Image1.inputAddr, Image1.outAddr]; omega) i2 hi2))
      have hpcw10 : w10.pc = BitVec.ofNat 64 (Image1.coreAddr + 592) := rfl
      have hqw10 : w10.pc ≠ 0 := by rw [hpcw10]; exact corePc_ne_zero 592 (by omega)
      -- t1 += 4 (592)
      have h6w3 : w3.rget 6 = BitVec.ofNat 64 emitted.length := by
        rw [hsw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (6:Nat) ≠ 28)]
        exact h6w2
      have h6w10 : w10.rget 6 = BitVec.ofNat 64 emitted.length := by
        rw [hsw10, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw9, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (6:Nat) ≠ 29),
            hsw8, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (6:Nat) ≠ 29),
            hsw6, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (6:Nat) ≠ 29),
            hsw4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget]
        exact h6w3
      have hu18 : step w10 = (w10.rset 6 (BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 596)) := by
        rw [step_addi w10 592 6 6 (BitVec.ofNat 12 4) hcw10 (by rw [coreBytes_len]; omega)
            hpcw10 dec_592,
            show w10.rget 6 + (BitVec.ofNat 12 4).signExtend 64
                = BitVec.ofNat 64 (emitted.length + 4) from by
              rw [h6w10, show ((BitVec.ofNat 12 4).signExtend 64)
                    = BitVec.ofNat 64 4 from by decide,
                  addr_ofNat_succ],
            show w10.pc + 4 = BitVec.ofNat 64 (Image1.coreAddr + 596) from by
              rw [hpcw10]; decide]
      let w11 := (w10.rset 6 (BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 596))
      have hsw11 : w11 = (w10.rset 6 (BitVec.ofNat 64 (emitted.length + 4))).setPc
          (BitVec.ofNat 64 (Image1.coreAddr + 596)) := rfl
      try rw [← hsw11] at hu18
      have hcw11 : CodeLoaded1 w11 := codeLoaded1_setPc _ _ (codeLoaded1_rset _ _ _ hcw10)
      have hpcw11 : w11.pc = BitVec.ofNat 64 (Image1.coreAddr + 596) := rfl
      have hqw11 : w11.pc ≠ 0 := by rw [hpcw11]; exact corePc_ne_zero 596 (by omega)
      -- j 368 (596)
      have hu19 : step w11 = w11.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := by
        rw [step_jal w11 596 0 (BitVec.ofNat 21 2096924) hcw11
            (by rw [coreBytes_len]; omega) hpcw11 dec_596, rset_zero,
            show w11.pc + (BitVec.ofNat 21 2096924).signExtend 64
                = BitVec.ofNat 64 (Image1.coreAddr + 368) from by rw [hpcw11]; decide]
      let sF := w11.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368))
      have hsF : sF = w11.setPc (BitVec.ofNat 64 (Image1.coreAddr + 368)) := rfl
      try rw [← hsF] at hu19
      have hrun13 : runFuel 0 13 r6 = sF := by
        simp only [runFuel]
        rw [hu7, hu8, hu9, hu10, hu11, hu12, hu13, hu14, hu15, hu16, hu17, hu18, hu19,
            if_neg hqr6, if_neg hqw0, if_neg hqw1, if_neg hqw2, if_neg hqw3, if_neg hqw4,
            if_neg hqw5, if_neg hqw6, if_neg hqw7, if_neg hqw8, if_neg hqw9, if_neg hqw10,
            if_neg hqw11]
      have hmem_at : ∀ a, sF.mem a
          = if a = BitVec.ofNat 64 (Image1.outAddr + emitted.length + 3)
              then BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 3 0)
            else if a = BitVec.ofNat 64 (Image1.outAddr + emitted.length + 2)
              then BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 2 0)
            else if a = BitVec.ofNat 64 (Image1.outAddr + emitted.length + 1)
              then BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 1 0)
            else if a = BitVec.ofNat 64 (Image1.outAddr + emitted.length)
              then BitVec.ofNat 8 ((Hex1.offBytes p emitted.length).getD 0 0)
            else s.mem a := by
        intro a
        rw [hsF, hsw11, hsw10, hsw9, hsw8, hsw7, hsw6, hsw5, hsw4]
        simp only [Hex0.Refine.setPc_mem, Hex0.Refine.rset_mem, storeByte_mem]
        rw [hmem_w3]
      have hregF : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 28 → i ≠ 29 → i ≠ 30 →
          sF.rget i = s.rget i := by
        intro i h0 h5i h6i h7i h28i h29i h30i
        rw [hsF, Hex0.Refine.setPc_rget,
            hsw11, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h6i,
            hsw10, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw9, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
            hsw8, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
            hsw6, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
            hsw4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h28i,
            hsw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h29i,
            hsw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) h0, if_neg h30i,
            hsw0, Hex0.Refine.setPc_rget]
        exact hframe_r6 i h0 h5i h7i h28i h29i
      have h5r6 : r6.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
        rw [hsr6, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsr5, li_block_frame _ _ _ 5 (by decide),
            hsr4, li_block_frame _ _ _ 5 (by decide),
            hsr3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      have h5F : sF.rget 5 = BitVec.ofNat 64 (inp.length - rest2.length) := by
        rw [hsF, Hex0.Refine.setPc_rget,
            hsw11, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 6),
            hsw10, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw9, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsw8, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw7, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsw6, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw5, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsw4, Hex0.Refine.setPc_rget, Hex0.Refine.storeByte_rget,
            hsw3, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 28),
            hsw2, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 29),
            hsw1, Hex0.Refine.setPc_rget, rset_rget _ _ _ _ (by decide) (by decide),
            if_neg (by decide : (5:Nat) ≠ 30),
            hsw0, Hex0.Refine.setPc_rget]
        exact h5r6
      have h6F : sF.rget 6 = BitVec.ofNat 64 (emitted.length + 4) := by
        rw [hsF, Hex0.Refine.setPc_rget, hsw11, Hex0.Refine.setPc_rget,
            rset_rget _ _ _ _ (by decide) (by decide)]
        simp
      -- spec side: the emit telescope steps through the reference
      obtain ⟨out2, st2, hrest⟩ : ∃ o s2,
          Hex1.emit1 .High labF (emitted.length + 4) rest2 = (o, s2) := ⟨_, _, rfl⟩
      have hem_step : Hex1.emit1 .High labF emitted.length (37 :: l :: rest2)
          = (Hex1.offBytes p emitted.length ++ out2, st2) := by
        rw [Hex1.emit1]
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_pos (by decide)]
        rw [Hex1.emit1]
        simp only [hll, hrest]
      refine ⟨4 + (14 + (6 + 13)), sF, by omega, ?_, Or.inl ⟨l, rest2, rfl, p, ?_⟩⟩
      · rw [runFuel_add, hrun4, runFuel_add, hrund, runFuel_add, hrun6, hrun13]
      · exact {
          wf := inv.wf
          at_loop := rfl
          code := codeLoaded1_setPc _ _ hcw11
          a0 := by
            rw [hregF 10 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)]
            exact inv.a0
          a1 := by
            rw [hregF 11 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)]
            exact inv.a1
          a2 := by
            rw [hregF 12 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)]
            exact inv.a2
          a3 := by
            rw [hregF 13 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)]
            exact inv.a3
          a4 := by
            rw [hregF 14 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)]
            exact inv.a4
          ra0 := by
            rw [hregF 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)]
            exact inv.ra0
          in_mem := by
            intro j hj
            rw [hmem_at,
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr]
                        at hin hout hlbl ⊢; omega)
                  (by have := hAddrOk 3 (by omega); omega)
                  (by simp only [Image1.inputAddr, Image1.outAddr] at hin ⊢; omega)),
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr]
                        at hin hout hlbl ⊢; omega)
                  (by have := hAddrOk 2 (by omega); omega)
                  (by simp only [Image1.inputAddr, Image1.outAddr] at hin ⊢; omega)),
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr]
                        at hin hout hlbl ⊢; omega)
                  (by have := hAddrOk 1 (by omega); omega)
                  (by simp only [Image1.inputAddr, Image1.outAddr] at hin ⊢; omega)),
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.inputAddr, Image1.outAddr, Image1.lblAddr]
                        at hin hout hlbl ⊢; omega)
                  (by have := hAddrOk 0 (by omega); omega)
                  (by simp only [Image1.inputAddr, Image1.outAddr] at hin ⊢; omega))]
            exact inv.in_mem j hj
          idx := h5F
          suffix := suffix_step inp l rest2 hrest'_eq
          outidx := by
            rw [h6F]
            congr 1
            rw [List.length_append, offBytes_len]
          out_mem := by
            intro j hj
            rw [show (emitted ++ Hex1.offBytes p emitted.length).length
                  = emitted.length + 4 from by
                  rw [List.length_append, offBytes_len]] at hj
            rw [hmem_at, getD_append]
            by_cases hj0 : j < emitted.length
            · rw [if_pos hj0,
                  if_neg (ofNat_ne _ _
                    (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)
                    (by have := hAddrOk 3 (by omega); omega)
                    (by omega)),
                  if_neg (ofNat_ne _ _
                    (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)
                    (by have := hAddrOk 2 (by omega); omega)
                    (by omega)),
                  if_neg (ofNat_ne _ _
                    (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)
                    (by have := hAddrOk 1 (by omega); omega)
                    (by omega)),
                  if_neg (ofNat_ne _ _
                    (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)
                    (by have := hAddrOk 0 (by omega); omega)
                    (by omega))]
              exact inv.out_mem j hj0
            · rw [if_neg hj0]
              rcases (by omega : j = emitted.length ∨ j = emitted.length + 1 ∨
                  j = emitted.length + 2 ∨ j = emitted.length + 3) with h | h | h | h
              · subst h
                rw [if_neg (ofNat_ne _ _
                      (by have := hAddrOk 0 (by omega); omega)
                      (by have := hAddrOk 3 (by omega); omega)
                      (by omega)),
                    if_neg (ofNat_ne _ _
                      (by have := hAddrOk 0 (by omega); omega)
                      (by have := hAddrOk 2 (by omega); omega)
                      (by omega)),
                    if_neg (ofNat_ne _ _
                      (by have := hAddrOk 0 (by omega); omega)
                      (by have := hAddrOk 1 (by omega); omega)
                      (by omega)),
                    if_pos rfl,
                    show emitted.length - emitted.length = 0 from by omega]
              · subst h
                rw [if_neg (ofNat_ne _ _
                      (by have := hAddrOk 1 (by omega); omega)
                      (by have := hAddrOk 3 (by omega); omega)
                      (by omega)),
                    if_neg (ofNat_ne _ _
                      (by have := hAddrOk 1 (by omega); omega)
                      (by have := hAddrOk 2 (by omega); omega)
                      (by omega)),
                    if_pos (show BitVec.ofNat 64 (Image1.outAddr + (emitted.length + 1))
                        = BitVec.ofNat 64 (Image1.outAddr + emitted.length + 1) from by
                      congr 1),
                    show emitted.length + 1 - emitted.length = 1 from by omega]
              · subst h
                rw [if_neg (ofNat_ne _ _
                      (by have := hAddrOk 2 (by omega); omega)
                      (by have := hAddrOk 3 (by omega); omega)
                      (by omega)),
                    if_pos (show BitVec.ofNat 64 (Image1.outAddr + (emitted.length + 2))
                        = BitVec.ofNat 64 (Image1.outAddr + emitted.length + 2) from by
                      congr 1),
                    show emitted.length + 2 - emitted.length = 2 from by omega]
              · subst h
                rw [if_pos (show BitVec.ofNat 64 (Image1.outAddr + (emitted.length + 3))
                        = BitVec.ofNat 64 (Image1.outAddr + emitted.length + 3) from by
                      congr 1),
                    show emitted.length + 3 - emitted.length = 3 from by omega]
          tbl := by
            intro cc hcc k hk
            rw [hmem_at,
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.lblAddr] at hlbl ⊢; omega)
                  (by have := hAddrOk 3 (by omega); omega)
                  (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)),
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.lblAddr] at hlbl ⊢; omega)
                  (by have := hAddrOk 2 (by omega); omega)
                  (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)),
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.lblAddr] at hlbl ⊢; omega)
                  (by have := hAddrOk 1 (by omega); omega)
                  (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega)),
                if_neg (ofNat_ne _ _
                  (by simp only [Image1.lblAddr] at hlbl ⊢; omega)
                  (by have := hAddrOk 0 (by omega); omega)
                  (by simp only [Image1.outAddr, Image1.lblAddr] at hout hlbl ⊢; omega))]
            exact inv.tbl cc hcc k hk
          m_le := inv.m_le
          lab_le := inv.lab_le
          scan_inp := inv.scan_inp
          scan_ok := by
            rw [show (emitted ++ Hex1.offBytes p emitted.length).length
                  = emitted.length + 4 from by
                  rw [List.length_append, offBytes_len]]
            exact hscu
          spec := by
            have h := inv.spec
            rw [hem_step] at h
            rw [show (emitted ++ Hex1.offBytes p emitted.length).length
                  = emitted.length + 4 from by
                  rw [List.length_append, offBytes_len],
                hrest, h]
            simp }

end Hex1.Refine
