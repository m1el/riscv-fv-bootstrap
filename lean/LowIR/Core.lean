/-
  LowIR — a *structured* near-assembly IL, and a compiler down to the trusted
  RV64I model (`Hex0/Rv64i.lean`).

  WHY THIS EXISTS
  ---------------
  The hex0 correctness proof (`Hex0/Refine.lean`, ~3400 lines) is almost entirely
  a fuel-bounded PC-simulation loop lemma: matching `Rv64i.step` iterations against
  spec tokens over a *flat program-counter machine*. That is the cost of reasoning
  at the bare-assembly altitude.

  Surveying the IL stacks of CompCert (Cminor → RTL → … → Asm) and CakeML/Pancake
  (panLang → … → wordLang → stackLang → labLang) shows a sharp boundary: ILs with
  *structured* control flow (Seq / If / While, no explicit PC) are proved by
  STRUCTURAL INDUCTION on the program; ILs with a flat PC/CFG are proved by
  per-instruction simulation. The "sweet spot" — low-level but still structured —
  is CompCert's Cminor / CakeML's stackLang.

  LowIR sits at that altitude: three-address machine ops (1:1 with RV64I) but
  STRUCTURED control (`ife`, `while`). A program is proved correct by induction on
  its big-step evaluation; the per-instruction PC-simulation cost is paid ONCE, in
  the verified `compile : Stmt → List Rv64i.Instr` pass, and reused by every program.

  The compiler targets EXACTLY the 16-instruction trusted surface of `Rv64i`
  (add sub or addi slli srli lbu sb + the 4 branches beq/blt/bge/bgeu + jal) — no
  new ISA surface. Branch conditions are limited to {eq, lt(s), ge(s), geu} so that
  every emitted branch is one of those four (the deliberately-excluded `bltu`/`bne`
  are simulated by branch-target swapping at compile time).

  This file (pass 1): syntax + big-step semantics, validated by running a real
  `strlen` in the IL. Compiler + RV64I cross-check + correctness theorems follow.
-/
import RawAsm.Rv64i

namespace LowIR

open Rv64i (Word Byte)

abbrev Reg := Nat

/-- Branch/relational conditions — exactly the four available RV64I branches.
    `ne`, `ltu`, `le`, `gt` are derived by the compiler via target swapping. -/
inductive Cond where
  | eq        -- ==        → beq
  | lt        -- <  signed → blt
  | ge        -- >= signed → bge
  | geu       -- >= unsigned → bgeu
deriving DecidableEq, Repr

/-- Structured near-assembly. Ops are three-address (map 1:1 to RV64I); control
    flow is structured (`ife`/`while`) with NO explicit program counter. -/
inductive Stmt where
  | skip
  | seq   (a b : Stmt)
  | addi  (rd rs : Reg) (imm : BitVec 12)            -- rd := rs + sext imm  (set const via rs=0)
  | add   (rd rs1 rs2 : Reg)                         -- rd := rs1 + rs2
  | sub   (rd rs1 rs2 : Reg)                         -- rd := rs1 - rs2
  | orr   (rd rs1 rs2 : Reg)                         -- rd := rs1 ||| rs2
  | slli  (rd rs : Reg) (sh : Nat)                   -- rd := rs <<< sh
  | srli  (rd rs : Reg) (sh : Nat)                   -- rd := rs >>> sh
  | lbu   (rd rs : Reg) (imm : BitVec 12)            -- rd := zext mem[rs + sext imm]
  | sb    (rbase rval : Reg) (imm : BitVec 12)       -- mem[rbase + sext imm] := low8 rval
  | ife   (c : Cond) (a b : Reg) (t e : Stmt)        -- if (a c b) then t else e
  | while (c : Cond) (a b : Reg) (body : Stmt)       -- while (a c b) do body
deriving Repr

/-- IL machine state: a register file (x0 hardwired to 0) over byte memory. -/
structure St where
  regs : Reg → Word
  mem  : Word → Byte

@[inline] def St.rget (s : St) (i : Reg) : Word := if i = 0 then 0 else s.regs i

@[inline] def St.rset (s : St) (i : Reg) (v : Word) : St :=
  if i = 0 then s else { s with regs := fun j => if j = i then v else s.regs j }

@[inline] def St.loadByte (s : St) (a : Word) : Byte := s.mem a

@[inline] def St.storeByte (s : St) (a : Word) (b : Byte) : St :=
  { s with mem := fun x => if x = a then b else s.mem x }

/-- Evaluate a relational condition between two register values. -/
@[inline] def evalCond (c : Cond) (x y : Word) : Bool :=
  match c with
  | .eq  => x = y
  | .lt  => x.slt y
  | .ge  => !x.slt y
  | .geu => !x.ult y

/-- Clocked big-step semantics. `fuel` bounds nesting depth of evaluation; `none`
    means the fuel ran out (never reached on a well-fuelled terminating program).
    Every recursive call is at `fuel` from `fuel+1`, so this is structurally
    terminating AND directly executable. Proofs induct on `fuel` / on `Stmt`. -/
def exec : Nat → Stmt → St → Option St
  | 0,      _,    _ => none
  | fuel+1, stmt, s =>
    match stmt with
    | .skip            => some s
    | .seq a b         => (exec fuel a s).bind (exec fuel b)
    | .addi rd rs imm  => some (s.rset rd (s.rget rs + imm.signExtend 64))
    | .add  rd r1 r2   => some (s.rset rd (s.rget r1 + s.rget r2))
    | .sub  rd r1 r2   => some (s.rset rd (s.rget r1 - s.rget r2))
    | .orr  rd r1 r2   => some (s.rset rd (s.rget r1 ||| s.rget r2))
    | .slli rd rs sh   => some (s.rset rd (s.rget rs <<< sh))
    | .srli rd rs sh   => some (s.rset rd (s.rget rs >>> sh))
    | .lbu  rd rs imm  =>
        let a := s.rget rs + imm.signExtend 64
        some (s.rset rd ((s.loadByte a).setWidth 64))
    | .sb   rb rv imm  =>
        let a := s.rget rb + imm.signExtend 64
        some (s.storeByte a ((s.rget rv).setWidth 8))
    | .ife c a b t e   =>
        if evalCond c (s.rget a) (s.rget b) then exec fuel t s else exec fuel e s
    | .while c a b body =>
        if evalCond c (s.rget a) (s.rget b)
        then (exec fuel body s).bind (exec fuel (.while c a b body))
        else some s

/-- Run with a large default fuel (executable validation convenience). -/
def run (p : Stmt) (s : St) : Option St := exec 100000 p s

/-! ### Demo: `strlen` written in LowIR

    Registers: x10 = s (argument, the string pointer); x5 = cursor; x6 = current
    byte; x7 = the constant 1; x12 = result length.

    `while (x6 >=u 1)` runs exactly while the current byte is non-zero (a zero byte
    is `< 1` unsigned), i.e. it stops at the NUL terminator — a faithful `strlen`. -/
def strlen : Stmt :=
  .seq (.addi 7 0 1) <|            -- x7 := 1
  .seq (.addi 5 10 0) <|           -- x5 := s            (cursor := s)
  .seq (.lbu 6 5 0) <|             -- x6 := mem[x5]      (load first byte)
  .seq (.while .geu 6 7            -- while (x6 >=u 1):
        (.seq (.addi 5 5 1)        --   x5 := x5 + 1     (advance)
              (.lbu 6 5 0))) <|    --   x6 := mem[x5]    (reload)
  (.sub 12 5 10)                   -- x12 := x5 - s      (length)

/-- A test state: the bytes of `s` laid out at address `base`, NUL-terminated. -/
def memOf (base : Word) (bytes : List Byte) : Word → Byte :=
  fun a => (bytes[(a - base).toNat]?).getD 0

def stateWith (base : Word) (bytes : List Byte) : St :=
  { regs := fun i => if i = 10 then base else 0, mem := memOf base bytes }

-- "ABC" then NUL (length 3) at address 0x1000.
def demoBytes : List Byte := [0x41, 0x42, 0x43, 0x00]

#guard
  match run strlen (stateWith 0x1000 demoBytes) with
  | some s => (s.rget 12).toNat == 3
  | none   => false

-- empty string "" (just NUL) → length 0
#guard
  match run strlen (stateWith 0x2000 [0x00]) with
  | some s => (s.rget 12).toNat == 0
  | none   => false

-- "HELLO" → length 5
#guard
  match run strlen (stateWith 0x3000 [0x48,0x45,0x4C,0x4C,0x4F,0x00]) with
  | some s => (s.rget 12).toNat == 5
  | none   => false

/-! ## The compiler: LowIR → flat RV64I

    Structured control flow is lowered to the four trusted branches + `jal`. The
    per-instruction PC-simulation burden lives here (proved once), not in the
    per-program correctness proofs above.

    Layouts (offsets are byte deltas relative to the branching instruction; each
    instruction is 4 bytes). Both use only the *positive* branch form, so the
    excluded `bne`/`bltu` are never needed:

      ife c a b T E:                       while c a b BODY:
        0: branch c → THEN  (+4*(|E|+2))     0: branch c → BODY  (+8)
        1.. : compile E                      1: jal → END        (+4*(|B|+2))
        : jal → END        (+4*(|T|+1))      2.. : compile BODY
        : compile T                          : jal → TOP         (-4*(|B|+2))
        END:                                 END:
-/

open Rv64i (Instr decode)

/-- The branch instruction for a condition (positive form). -/
def condInstr (c : Cond) (a b : Reg) (off : Int) : Instr :=
  let imm : BitVec 13 := BitVec.ofInt 13 off
  match c with
  | .eq  => .beq  a b imm
  | .lt  => .blt  a b imm
  | .ge  => .bge  a b imm
  | .geu => .bgeu a b imm

/-- Unconditional jump (`jal x0, off`). -/
def jal0 (off : Int) : Instr := .jal 0 (BitVec.ofInt 21 off)

def compile : Stmt → List Instr
  | .skip            => []
  | .seq a b         => compile a ++ compile b
  | .addi rd rs imm  => [.addi rd rs imm]
  | .add  rd r1 r2   => [.add rd r1 r2]
  | .sub  rd r1 r2   => [.sub rd r1 r2]
  | .orr  rd r1 r2   => [.or rd r1 r2]
  | .slli rd rs sh   => [.slli rd rs sh]
  | .srli rd rs sh   => [.srli rd rs sh]
  | .lbu  rd rs imm  => [.lbu rd rs imm]
  | .sb   rb rv imm  => [.sb rb rv imm]
  | .ife c a b t e   =>
      let cE := compile e
      let cT := compile t
      condInstr c a b ((4 * (cE.length + 2) : Nat) : Int)
        :: cE ++ jal0 ((4 * (cT.length + 1) : Nat) : Int) :: cT
  | .while c a b body =>
      let cB := compile body
      let span : Int := ((4 * (cB.length + 2) : Nat) : Int)
      condInstr c a b 8 :: jal0 span :: (cB ++ [jal0 (-span)])

/-! ### Encoder: `Instr → BitVec 32`, the byte-exact inverse of `Rv64i.decode`.

    The compiler's output must become *actual bytes* that the trusted `decode`
    reads back. We assemble each instruction with `encode` and assert
    `decode (encode i) = i` (round-trip) as a checked theorem. -/

private def w32 (parts : List Nat) : BitVec 32 := BitVec.ofNat 32 (parts.foldl (· ||| ·) 0)

/-- B-type immediate scatter (matches `decode`'s `immB`). -/
private def encB (imm : BitVec 13) : List Nat :=
  let o := imm.toNat
  [ ((o >>> 12) &&& 1) <<< 31, ((o >>> 11) &&& 1) <<< 7,
    ((o >>> 5) &&& 0x3F) <<< 25, ((o >>> 1) &&& 0xF) <<< 8 ]

/-- J-type immediate scatter (matches `decode`'s `immJ`). -/
private def encJ (imm : BitVec 21) : List Nat :=
  let o := imm.toNat
  [ ((o >>> 20) &&& 1) <<< 31, ((o >>> 12) &&& 0xFF) <<< 12,
    ((o >>> 11) &&& 1) <<< 20, ((o >>> 1) &&& 0x3FF) <<< 21 ]

def encode : Instr → BitVec 32
  | .addi rd rs1 imm => w32 [0x13, rd <<< 7, rs1 <<< 15, (imm.toNat &&& 0xFFF) <<< 20]
  | .add  rd rs1 rs2 => w32 [0x33, rd <<< 7, rs1 <<< 15, rs2 <<< 20]
  | .sub  rd rs1 rs2 => w32 [0x33, rd <<< 7, rs1 <<< 15, rs2 <<< 20, 0x20 <<< 25]
  | .or   rd rs1 rs2 => w32 [0x33, rd <<< 7, (6 : Nat) <<< 12, rs1 <<< 15, rs2 <<< 20]
  | .slli rd rs1 sh  => w32 [0x13, rd <<< 7, (1 : Nat) <<< 12, rs1 <<< 15, (sh &&& 0x3F) <<< 20]
  | .srli rd rs1 sh  => w32 [0x13, rd <<< 7, (5 : Nat) <<< 12, rs1 <<< 15, (sh &&& 0x3F) <<< 20]
  | .lbu  rd rs1 imm => w32 [0x03, rd <<< 7, (4 : Nat) <<< 12, rs1 <<< 15, (imm.toNat &&& 0xFFF) <<< 20]
  | .ld   rd rs1 imm => w32 [0x03, rd <<< 7, (3 : Nat) <<< 12, rs1 <<< 15, (imm.toNat &&& 0xFFF) <<< 20]
  | .sb   rs1 rs2 imm =>
      let i := imm.toNat
      w32 [0x23, (i &&& 0x1F) <<< 7, rs1 <<< 15, rs2 <<< 20, ((i >>> 5) &&& 0x7F) <<< 25]
  | .sd   rs1 rs2 imm =>
      let i := imm.toNat
      w32 [0x23, (i &&& 0x1F) <<< 7, (3 : Nat) <<< 12, rs1 <<< 15, rs2 <<< 20, ((i >>> 5) &&& 0x7F) <<< 25]
  | .beq  rs1 rs2 imm => w32 (0x63 :: rs1 <<< 15 :: rs2 <<< 20 :: encB imm)
  | .blt  rs1 rs2 imm => w32 (0x63 :: (4 : Nat) <<< 12 :: rs1 <<< 15 :: rs2 <<< 20 :: encB imm)
  | .bge  rs1 rs2 imm => w32 (0x63 :: (5 : Nat) <<< 12 :: rs1 <<< 15 :: rs2 <<< 20 :: encB imm)
  | .bgeu rs1 rs2 imm => w32 (0x63 :: (7 : Nat) <<< 12 :: rs1 <<< 15 :: rs2 <<< 20 :: encB imm)
  | .jal  rd imm      => w32 (0x6f :: rd <<< 7 :: encJ imm)
  | .jalr rd rs1 imm  => w32 [0x67, rd <<< 7, rs1 <<< 15, (imm.toNat &&& 0xFFF) <<< 20]
  | .unknown          => 0

/-! ### Assemble + run on the trusted `Rv64i` machine. -/

/-- Little-endian 4 bytes of an instruction. -/
def insBytes (i : Instr) : List Byte :=
  let w := encode i
  [w.setWidth 8, (w >>> 8).setWidth 8, (w >>> 16).setWidth 8, (w >>> 24).setWidth 8]

def asmBytes (is : List Instr) : List Byte := (is.map insBytes).flatten

/-- Memory holding `code` at `codeBase` and `data` at `dataBase` (disjoint). -/
def loadMem (codeBase : Word) (code : List Byte) (dataBase : Word) (data : List Byte) : Word → Byte :=
  fun a =>
    let ca := (a - codeBase).toNat
    if ca < code.length then (code[ca]?).getD 0
    else (data[(a - dataBase).toNat]?).getD 0

/-- Initial RV64I state: program assembled at `codeBase`, string at `dataBase`,
    x10 = dataBase (the argument). -/
def mkState (codeBase dataBase : Word) (p : Stmt) (data : List Byte) : Rv64i.State :=
  { reg := fun i => if i = 10 then dataBase else 0
    pc  := codeBase
    mem := loadMem codeBase (asmBytes (compile p)) dataBase data }

/-- Run the compiled program on `Rv64i` until it falls off the end. -/
def rvRun (codeBase dataBase : Word) (p : Stmt) (data : List Byte) (fuel : Nat) : Rv64i.State :=
  let halt := codeBase + BitVec.ofNat 64 (4 * (compile p).length)
  Rv64i.runFuel halt fuel (mkState codeBase dataBase p data)

/-! ### Checks

    1. The encoder round-trips through the trusted decoder for every emitted form.
    2. End-to-end: the compiled `strlen`, assembled to bytes and executed by the
       genuine `Rv64i.step` machine, produces the same length the IL semantics did. -/

/-- Round-trip: every instruction `compile strlen` emits decodes back to itself. -/
theorem strlen_roundtrip :
    (compile strlen).all (fun i => decode (encode i) == i) = true := by native_decide

/-- End-to-end on the trusted machine: compiled `strlen` of "ABC" returns 3 in x12. -/
theorem strlen_rv_abc :
    ((rvRun 0x80000000 0x1000 strlen demoBytes 2000).rget 12).toNat = 3 := by native_decide

/-- "HELLO" → 5, via the genuine RV64I `step`. -/
theorem strlen_rv_hello :
    ((rvRun 0x80000000 0x1000 strlen [0x48,0x45,0x4C,0x4C,0x4F,0x00] 2000).rget 12).toNat = 5 := by
  native_decide

/-- Empty string → 0. -/
theorem strlen_rv_empty :
    ((rvRun 0x80000000 0x1000 strlen [0x00] 2000).rget 12).toNat = 0 := by native_decide

/-! ## T1 — the compiler-correctness framework (statement now; proof later)

    The checks above are *finite* (`native_decide`, certification-grade). T1 is the
    GENERAL theorem: the compiler is a forward simulation, so a proof done at the
    structured altitude transports to the real RV64I bytes. We define the simulation
    relation here so T1 is a well-formed, reason-about-able statement; the proof is
    deferred (`sorry`) — what matters first is that the *design* admits the theorem.

    Everything below the statement (the IL semantics `exec`, the machine `Rv64i.step`,
    the relation) is ordinary provable Lean — only `compile_sim`'s proof is open. -/

/-- Where a program's code is installed: its first instruction's address and the
    instruction list (`= compile p`). -/
structure Layout where
  codeBase : Word
  code     : List Rv64i.Instr

/-- Address one past the last instruction — the fall-through / return PC. -/
def Layout.endPc (L : Layout) : Word := L.codeBase + BitVec.ofNat 64 (4 * L.code.length)

/-- Is address `a` inside the installed code window? -/
def Layout.inCode (L : Layout) (a : Word) : Prop := L.codeBase ≤ a ∧ a < L.endPc

/-- The code is faithfully present in the machine's memory: the 32-bit word at
    `codeBase + 4j` decodes (via the *trusted* `Rv64i.decode`) to `code[j]`. -/
def Installed (L : Layout) (m : Rv64i.State) : Prop :=
  ∀ (j : Nat) (h : j < L.code.length),
    Rv64i.decode (Rv64i.fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) })
      = L.code[j]'h

/-- The IL state `s` and machine state `m` agree: all registers equal, and memory
    equal *off the code window* (the IL state has no code in its memory; agreement
    there is meaningless). -/
def Agree (L : Layout) (s : St) (m : Rv64i.State) : Prop :=
  (∀ i, s.rget i = m.rget i) ∧ (∀ a, ¬ L.inCode a → s.mem a = m.mem a)

/-- Separation side-condition: executing `p` leaves the code window of memory
    unchanged (no self-modifying code). True for the usual loader placement, where
    the program's data pointers are disjoint from the installed code. A proof
    obligation per program; assumed by T1. (Refinement note: the fully faithful
    form is *step-wise* "no store ever targets the code window"; this end-to-end
    form is the v1 approximation and will be tightened when `compile_sim` is proved.) -/
def NoSelfModify (L : Layout) (p : Stmt) (s : St) : Prop :=
  ∀ fuel s', exec fuel p s = some s' → ∀ a, L.inCode a → s.mem a = s'.mem a

/-- **T1 (compiler correctness, forward simulation).** If the IL big-step succeeds
    (`exec … = some s'`) and `compile p` is installed at `m.pc` in agreement with the
    IL state, then the trusted machine runs to the fall-through PC in a state that
    still has the code installed and agrees with `s'`.

    PROOF STRATEGY (deferred): structural induction on `p`.
      • ops: one `Rv64i.step`; the register/memory update matches `exec`'s.
      • `seq a b`: compose the sub-simulations (run `a`'s block, then `b`'s).
      • `ife`/`while`: the *only* flat-PC reasoning — discharge the fixed branch/`jal`
        offset arithmetic of the lowering once; `while` adds a measure induction on
        the back-edge, its body handled by the structural IH.
    This is the per-program cost `Hex0/Refine.lean` pays at the flat altitude — here
    amortised into the compiler, then reused by every program (e.g. T2 below). -/
theorem compile_sim
    {p : Stmt} {s s' : St} {m : Rv64i.State} {fuel : Nat} {L : Layout}
    (hcode : L.code = compile p)
    (hpc   : m.pc = L.codeBase)
    (hinst : Installed L m)
    (hag   : Agree L s m)
    (hsep  : NoSelfModify L p s)
    (hexec : exec fuel p s = some s') :
    ∃ k, (Rv64i.runFuel L.endPc k m).pc = L.endPc
       ∧ Installed L (Rv64i.runFuel L.endPc k m)
       ∧ Agree L s' (Rv64i.runFuel L.endPc k m) := by
  sorry

/-! ## T2 — per-program functional correctness, at the EASY (structured) altitude.

    e.g. `strlen` meets its spec for ALL strings (no PC, no decode, no offsets — a
    `while`-invariant + induction on the distance to the first NUL):

      theorem strlen_correct (s : St) (base : Word) (n : Nat)
          (h10 : s.rget 10 = base) (hz : firstNulAt s.mem base = n) :
        ∃ F s', exec F strlen s = some s' ∧ (s'.rget 12).toNat = n

    `T1 ∘ T2` then transports it to the real RV64I bytes. (Stated as a target; to be
    written when we "prove strlen".) -/

end LowIR
