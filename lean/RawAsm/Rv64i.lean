/-
  A minimal, executable RV64I model -- exactly the 16 instruction encodings
  used by `bare/core.s` (hex0) and `bare/core1.s` (hex1):

    ADDI ADD OR SLLI LBU SB BEQ BLT BGE BGEU JAL JALR   (hex0's 12)
    SUB SRLI LD SD                                       (added for hex1)

  (li, mv collapse to ADDI; j = JAL x0; ret = JALR x0,ra,0; bgez/bltz are
  BGE/BLT vs x0). No LUI/AUIPC -- this is the whole trusted ISA surface for
  the hex0/hex1 rungs.

  Words/addresses are `BitVec 64`, memory is byte-addressed (`BitVec 64 -> BitVec 8`),
  instructions are decoded from little-endian 32-bit words. The model is
  executable (`#eval`) so it can be run on the actual binary's bytes and checked
  against the QEMU run before any proof (see Hex0/Validate.lean).
-/

namespace Rv64i

abbrev Word := BitVec 64
abbrev Byte := BitVec 8

structure State where
  reg : Nat → Word          -- x0..x31; x0 hardwired to 0 by rget/rset
  pc  : Word
  mem : Word → Byte

/-- Read register `i` (x0 reads as 0). -/
@[inline] def State.rget (s : State) (i : Nat) : Word :=
  if i = 0 then 0 else s.reg i

/-- Write register `i` (writes to x0 are ignored). -/
@[inline] def State.rset (s : State) (i : Nat) (v : Word) : State :=
  if i = 0 then s else { s with reg := fun j => if j = i then v else s.reg j }

@[inline] def State.setPc (s : State) (p : Word) : State := { s with pc := p }

@[inline] def State.loadByte (s : State) (a : Word) : Byte := s.mem a

@[inline] def State.storeByte (s : State) (a : Word) (b : Byte) : State :=
  { s with mem := fun x => if x = a then b else s.mem x }

/-- Fetch the little-endian 32-bit word at `pc`. -/
def fetch32 (s : State) : BitVec 32 :=
  let b0 := (s.mem s.pc).setWidth 32
  let b1 := (s.mem (s.pc + 1)).setWidth 32
  let b2 := (s.mem (s.pc + 2)).setWidth 32
  let b3 := (s.mem (s.pc + 3)).setWidth 32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Extract `len` bits starting at bit `lo` as a Nat. -/
@[inline] def field (w : BitVec 32) (lo len : Nat) : Nat :=
  (w.toNat >>> lo) &&& (2 ^ len - 1)

inductive Instr where
  | addi (rd rs1 : Nat) (imm : BitVec 12)
  | add  (rd rs1 rs2 : Nat)
  | sub  (rd rs1 rs2 : Nat)
  | or   (rd rs1 rs2 : Nat)
  | slli (rd rs1 : Nat) (shamt : Nat)
  | srli (rd rs1 : Nat) (shamt : Nat)
  | lbu  (rd rs1 : Nat) (imm : BitVec 12)
  | ld   (rd rs1 : Nat) (imm : BitVec 12)
  | sb   (rs1 rs2 : Nat) (imm : BitVec 12)
  | sd   (rs1 rs2 : Nat) (imm : BitVec 12)
  | beq  (rs1 rs2 : Nat) (imm : BitVec 13)
  | blt  (rs1 rs2 : Nat) (imm : BitVec 13)
  | bge  (rs1 rs2 : Nat) (imm : BitVec 13)
  | bgeu (rs1 rs2 : Nat) (imm : BitVec 13)
  | jal  (rd : Nat) (imm : BitVec 21)
  | jalr (rd rs1 : Nat) (imm : BitVec 12)
  | unknown
deriving Repr, DecidableEq

def decode (w : BitVec 32) : Instr :=
  let opcode := field w 0 7
  let rd     := field w 7 5
  let funct3 := field w 12 3
  let rs1    := field w 15 5
  let rs2    := field w 20 5
  let funct7 := field w 25 7
  let immI   : BitVec 12 := BitVec.ofNat 12 (field w 20 12)
  let shamt  := field w 20 6
  -- S-type immediate: [11:5]=funct7, [4:0]=rd
  let immS   : BitVec 12 := BitVec.ofNat 12 ((funct7 <<< 5) ||| rd)
  -- B-type immediate: [12]=b31 [11]=b7 [10:5]=b[30:25] [4:1]=b[11:8] [0]=0
  let immB   : BitVec 13 := BitVec.ofNat 13
      (((field w 31 1) <<< 12) ||| ((field w 7 1) <<< 11) |||
       ((field w 25 6) <<< 5)  ||| ((field w 8 4) <<< 1))
  -- J-type immediate: [20]=b31 [19:12]=b[19:12] [11]=b20 [10:1]=b[30:21] [0]=0
  let immJ   : BitVec 21 := BitVec.ofNat 21
      (((field w 31 1) <<< 20) ||| ((field w 12 8) <<< 12) |||
       ((field w 20 1) <<< 11) ||| ((field w 21 10) <<< 1))
  match opcode with
  | 0x13 => -- OP-IMM
      match funct3 with
      | 0x0 => .addi rd rs1 immI
      | 0x1 => if funct7 = 0 then .slli rd rs1 shamt else .unknown
      | 0x5 => if funct7 = 0 then .srli rd rs1 shamt else .unknown
      | _   => .unknown
  | 0x33 => -- OP
      if funct7 = 0 then
        match funct3 with
        | 0x0 => .add rd rs1 rs2
        | 0x6 => .or  rd rs1 rs2
        | _   => .unknown
      else if funct7 = 0x20 then
        match funct3 with
        | 0x0 => .sub rd rs1 rs2
        | _   => .unknown
      else .unknown
  | 0x03 => -- LOAD
      match funct3 with
      | 0x4 => .lbu rd rs1 immI
      | 0x3 => .ld  rd rs1 immI
      | _   => .unknown
  | 0x23 => -- STORE
      match funct3 with
      | 0x0 => .sb rs1 rs2 immS
      | 0x3 => .sd rs1 rs2 immS
      | _   => .unknown
  | 0x63 => -- BRANCH
      match funct3 with
      | 0x0 => .beq  rs1 rs2 immB
      | 0x4 => .blt  rs1 rs2 immB
      | 0x5 => .bge  rs1 rs2 immB
      | 0x7 => .bgeu rs1 rs2 immB
      | _   => .unknown
  | 0x6f => .jal rd immJ
  | 0x67 => if funct3 = 0 then .jalr rd rs1 immI else .unknown
  | _    => .unknown

/-- Load the little-endian 64-bit word at address `a`. -/
def State.loadWord (s : State) (a : Word) : Word :=
  (s.mem a).setWidth 64 |||
  ((s.mem (a + 1)).setWidth 64) <<< 8 |||
  ((s.mem (a + 2)).setWidth 64) <<< 16 |||
  ((s.mem (a + 3)).setWidth 64) <<< 24 |||
  ((s.mem (a + 4)).setWidth 64) <<< 32 |||
  ((s.mem (a + 5)).setWidth 64) <<< 40 |||
  ((s.mem (a + 6)).setWidth 64) <<< 48 |||
  ((s.mem (a + 7)).setWidth 64) <<< 56

/-- Store the 64-bit word `v` at address `a`, little-endian (8 byte stores,
    low byte first -- compositional for the proof side). -/
def State.storeWord (s : State) (a : Word) (v : Word) : State :=
  (((((((s.storeByte a (v.setWidth 8)
    ).storeByte (a + 1) ((v >>> 8).setWidth 8)
    ).storeByte (a + 2) ((v >>> 16).setWidth 8)
    ).storeByte (a + 3) ((v >>> 24).setWidth 8)
    ).storeByte (a + 4) ((v >>> 32).setWidth 8)
    ).storeByte (a + 5) ((v >>> 40).setWidth 8)
    ).storeByte (a + 6) ((v >>> 48).setWidth 8)
    ).storeByte (a + 7) ((v >>> 56).setWidth 8)

/-- Execute one instruction. Undecodable instructions leave the state stuck
    (pc unchanged), which the proof side treats as a non-final, non-advancing
    state. -/
def step (s : State) : State :=
  let next := s.pc + 4
  match decode (fetch32 s) with
  | .addi rd rs1 imm => (s.rset rd (s.rget rs1 + imm.signExtend 64)).setPc next
  | .add  rd rs1 rs2 => (s.rset rd (s.rget rs1 + s.rget rs2)).setPc next
  | .sub  rd rs1 rs2 => (s.rset rd (s.rget rs1 - s.rget rs2)).setPc next
  | .or   rd rs1 rs2 => (s.rset rd (s.rget rs1 ||| s.rget rs2)).setPc next
  | .slli rd rs1 sh  => (s.rset rd (s.rget rs1 <<< sh)).setPc next
  | .srli rd rs1 sh  => (s.rset rd (s.rget rs1 >>> sh)).setPc next
  | .lbu  rd rs1 imm =>
      let a := s.rget rs1 + imm.signExtend 64
      (s.rset rd ((s.loadByte a).setWidth 64)).setPc next
  | .ld   rd rs1 imm =>
      let a := s.rget rs1 + imm.signExtend 64
      (s.rset rd (s.loadWord a)).setPc next
  | .sb   rs1 rs2 imm =>
      let a := s.rget rs1 + imm.signExtend 64
      (s.storeByte a ((s.rget rs2).setWidth 8)).setPc next
  | .sd   rs1 rs2 imm =>
      let a := s.rget rs1 + imm.signExtend 64
      (s.storeWord a (s.rget rs2)).setPc next
  | .beq  rs1 rs2 imm =>
      s.setPc (if s.rget rs1 = s.rget rs2 then s.pc + imm.signExtend 64 else next)
  | .blt  rs1 rs2 imm =>
      s.setPc (if (s.rget rs1).slt (s.rget rs2) then s.pc + imm.signExtend 64 else next)
  | .bge  rs1 rs2 imm =>
      s.setPc (if (s.rget rs1).slt (s.rget rs2) then next else s.pc + imm.signExtend 64)
  | .bgeu rs1 rs2 imm =>
      s.setPc (if (s.rget rs1).ult (s.rget rs2) then next else s.pc + imm.signExtend 64)
  | .jal  rd imm => (s.rset rd next).setPc (s.pc + imm.signExtend 64)
  | .jalr rd rs1 imm =>
      let t := (s.rget rs1 + imm.signExtend 64) &&& (~~~ (1 : Word))
      (s.rset rd next).setPc t
  | .unknown => s

/-- Run until pc = `halt`. `partial`: used only for executable validation,
    NOT in proofs (the proof side reasons about `step` directly). -/
partial def runUntil (halt : Word) (s : State) : State :=
  if s.pc = halt then s else runUntil halt (step s)

/-- Structural fuel-based runner: usable in proofs (`decide`/`native_decide`)
    because it is total. Stops early when `pc = halt`. -/
def runFuel (halt : Word) : Nat → State → State
  | 0,     s => s
  | n + 1, s => if s.pc = halt then s else runFuel halt n (step s)

/-- Steps actually taken before halting (or `fuel` if it never halts). -/
def stepsToHalt (halt : Word) : Nat → State → Nat
  | 0,     _ => 0
  | n + 1, s => if s.pc = halt then 0 else 1 + stepsToHalt halt n (step s)

end Rv64i
