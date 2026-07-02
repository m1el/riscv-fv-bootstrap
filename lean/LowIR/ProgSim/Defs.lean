/-
  LowIR.ProgSim.Defs — the `compile_sim`-for-Prog relation and its executable
  scaffolding (RESUME-PROGSIM §3). This file is the FOUNDATION of the D7/D8
  compiler-correctness campaign: the simulation `Layout`/`Installed`/`StInv`,
  the write-footprint instrumentation `execT`, and (in ProgSim/Main, later) the
  top-level theorems. Everything here is a real, `sorry`-free DEFINITION plus a
  handful of `sorry`'d equivalence theorems whose statements are the deliverable
  — the proofs land in later phases.

  Discipline (RESUME-PROGSIM §6): every relation piece gets an EXECUTABLE
  sanity check (`#guard`) against real compiled programs BEFORE any lemma leans
  on it. This file's #guards compile fixtures through the FROZEN compiler, load
  the bytes into the trusted `Rv64i` machine, and check the relation's
  computable shadow holds — a wrong def is caught here in seconds, not inside
  Phase 5 in weeks.

  Commit A (this file, first cut): `Layout`, `layoutOf`, `Installed` + the
  computable `codeInstalledB`/`dataInstalledB`, `execT` + `execT_erase`. The
  relation `StInv`/`MachPriv`/`SimPre` and the `lower_sim`/`call_sim`/`prog_sim`
  statements arrive in a follow-up commit.
-/
import LowIR.Compile

namespace LowIR.ProgSim

open LowIR (Cond evalCond)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (Reg Name FunDef Env Data Program frameEnter
                 dataSegment dataOffsetsFrom pad8 dbaseOf installData)
open LowIR.Compile (compileProgT progBytes userOff totalFrame slotOff maxRegF)
open Rv64i (Word Byte Instr State)

-- `St`/`exec`/`Stmt` collide with the Ctrl-level `LowIR.St`/`LowIR.exec`
-- (enclosing-namespace lookup wins over `open LowIR.Prog`), so alias the Prog
-- ones locally and qualify the rest.
local notation "PStmt" => LowIR.Prog.Stmt
abbrev St := LowIR.Prog.St

/-! ## §3.1 (part) — where the code and data live: `Layout` and `Installed` -/

/-- The compiled artifact's placement, per RESUME-PROGSIM §3.1: the base
    address, the resolved instruction stream (`= (compileProgT P entry).1`), the
    function→byte-offset table, the byte offset where the data segment starts
    inside the blob (`pad8 (4 * #instrs)` — every instruction is 4 bytes after
    resolution), and the program's const data. -/
structure Layout where
  codeBase : Word
  instrs   : List Instr
  fnTab    : List (Name × Nat)
  segStart : Nat
  data     : Data
deriving Repr

/-- Build the `Layout` for `entry` at `codeBase` straight from the FROZEN
    compiler. `none` iff the program is uncompilable (same condition as
    `compileProgT`). `segStart` is recomputed here from the resolved stream
    and is DEFINITIONALLY the compiler's `pad8 codeEnd` (proved in Phase 2). -/
def layoutOf (P : Program) (entry : Name) (codeBase : Word) : Option Layout :=
  match compileProgT P entry with
  | some (is, fns, _) =>
      some { codeBase, instrs := is, fnTab := fns,
             segStart := pad8 (4 * is.length), data := P.data }
  | none => none

/-- The machine halt pc: the self-loop landing pad the compiler puts at
    `codeBase+4` (the entry stub is `jal ra,entry` at `codeBase`; the entry
    returns to `codeBase+4`). Run the machine with `runFuel L.haltPc`. -/
def Layout.haltPc (L : Layout) : Word := L.codeBase + 4

/-- Address one past the last instruction — the code window's top. -/
def Layout.codeEnd (L : Layout) : Word :=
  L.codeBase + BitVec.ofNat 64 (4 * L.instrs.length)

/-- `Installed L m` — the compiled blob is faithfully present in `m`'s memory:
    (code) the 32-bit word at `codeBase + 4j` decodes via the TRUSTED
    `Rv64i.decode` to `instrs[j]`; (data) the const-data byte at
    `codeBase + segStart + i` equals `dataSegment data`'s byte `i`
    (`Prog.dataSegment_at` already relates that segment to the object bytes). -/
def Installed (L : Layout) (m : State) : Prop :=
  (∀ (j : Nat) (h : j < L.instrs.length),
      Rv64i.decode (Rv64i.fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) })
        = L.instrs[j]'h)
  ∧ (∀ (i : Nat) (h : i < (dataSegment L.data).length),
      m.mem (L.codeBase + BitVec.ofNat 64 (L.segStart + i)) = (dataSegment L.data)[i]'h)

/-! ### Computable shadows of `Installed` (the #guard oracle). -/

/-- Every instruction slot decodes correctly (computable form of `Installed`'s
    code conjunct). -/
def codeInstalledB (L : Layout) (m : State) : Bool :=
  (List.range L.instrs.length).all fun j =>
    Rv64i.decode (Rv64i.fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) })
      == L.instrs.getD j .unknown

/-- Every data byte is present (computable form of `Installed`'s data conjunct). -/
def dataInstalledB (L : Layout) (m : State) : Bool :=
  (List.range (dataSegment L.data).length).all fun i =>
    m.mem (L.codeBase + BitVec.ofNat 64 (L.segStart + i))
      == (dataSegment L.data).getD i 0

/-! ## §3.4 — the write-footprint instrumentation `execT`.

    `execT` is `Prog.exec` verbatim, additionally accumulating the list of BYTE
    ADDRESSES written (`sb` → 1, `sd` → 8, calls → the callee's footprint). The
    `lower_sim` footprint side condition is then `ws.all (¬ MachPriv ·)` — no
    IL store lands in the machine's private bytes (code, spill slots, saved ra,
    pad holes). `execT_erase` says the instrumentation is observationally
    invisible: erasing the footprint recovers `exec` exactly. -/
def execT (P : Program) (dbase : Name → Option Word) (pad : Name → Nat)
    (stackLo : Word) :
    Nat → PStmt → St → Option (St × Outcome × List Word)
  | 0,      _,    _ => none
  | fuel+1, stmt, s =>
    match stmt with
    | .skip            => some (s, .normal, [])
    | .annot _         => some (s, .normal, [])
    | .cref rd d       =>
        match dbase d with
        | some a => some (s.rset rd a, .normal, [])
        | none   => none
    | .clen rd d       =>
        match List.lookup d P.data with
        | some bs => some (s.rset rd (BitVec.ofNat 64 bs.length), .normal, [])
        | none    => none
    | .addi rd rs imm  => some (s.rset rd (s.rget rs + imm.signExtend 64), .normal, [])
    | .add  rd r1 r2   => some (s.rset rd (s.rget r1 + s.rget r2), .normal, [])
    | .sub  rd r1 r2   => some (s.rset rd (s.rget r1 - s.rget r2), .normal, [])
    | .orr  rd r1 r2   => some (s.rset rd (s.rget r1 ||| s.rget r2), .normal, [])
    | .slli rd rs sh   => some (s.rset rd (s.rget rs <<< sh), .normal, [])
    | .srli rd rs sh   => some (s.rset rd (s.rget rs >>> sh), .normal, [])
    | .lbu  rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd ((s.loadByte a).setWidth 64), .normal, [])
    | .sb   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeByte a ((s.rget rv).setWidth 8), .normal, [a])
    | .ld   rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd (s.loadWord a), .normal, [])
    | .sd   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeWord a (s.rget rv), .normal,
                                [a, a+1, a+2, a+3, a+4, a+5, a+6, a+7])
    | .ife c a b t e   =>
        if evalCond c (s.rget a) (s.rget b)
        then execT P dbase pad stackLo fuel t s else execT P dbase pad stackLo fuel e s
    | .seq a b         =>
        match execT P dbase pad stackLo fuel a s with
        | some (s', .normal, ws) =>
            match execT P dbase pad stackLo fuel b s' with
            | some (s'', o, ws') => some (s'', o, ws ++ ws')
            | none               => none
        | other                  => other
    | .block body      =>
        match execT P dbase pad stackLo fuel body s with
        | some (s', .normal, ws)     => some (s', .normal, ws)
        | some (s', .brk 0, ws)      => some (s', .normal, ws)
        | some (s', .brk (k+1), ws)  => some (s', .brk k, ws)
        | some (s', .cont k, ws)     => some (s', .cont k, ws)
        | some (s', .ret, ws)        => some (s', .ret, ws)
        | none                       => none
    | .while c a b body =>
        if evalCond c (s.rget a) (s.rget b) then
          match execT P dbase pad stackLo fuel body s with
          | some (s', .normal, ws) =>
              match execT P dbase pad stackLo fuel (.while c a b body) s' with
              | some (s'', o, ws') => some (s'', o, ws ++ ws')
              | none               => none
          | some (s', .cont 0, ws) =>
              match execT P dbase pad stackLo fuel (.while c a b body) s' with
              | some (s'', o, ws') => some (s'', o, ws ++ ws')
              | none               => none
          | some (s', .cont (k+1), ws) => some (s', .cont k, ws)
          | some (s', .brk k, ws)      => some (s', .brk k, ws)
          | some (s', .ret, ws)        => some (s', .ret, ws)
          | none                       => none
        else some (s, .normal, [])
    | .brkB k          => some (s, .brk k, [])
    | .contL k         => some (s, .cont k, [])
    | .ret             => some (s, .ret, [])
    | .call argc rvc f args rets =>
        match List.lookup f P.env with
        | none => none
        | some fd =>
          if fd.argc == argc && fd.rvc == rvc then
            match frameEnter stackLo fd (pad f) (args.toList.map s.rget) s.mem s.sp with
            | none => none
            | some callee =>
              match execT P dbase pad stackLo fuel fd.body callee with
              | some (s1, .normal, ws) | some (s1, .ret, ws) =>
                  let retVals := fd.rets.toList.map s1.rget
                  some ((rets.toList.zip retVals).foldl
                          (fun st rv => st.rset rv.1 rv.2)
                          { s with mem := s1.mem }, .normal, ws)
              | some _ => none
              | none   => none
          else none

/-- **`execT_erase`** — the footprint instrumentation is observationally
    invisible: whenever `execT` succeeds with some footprint, `exec` succeeds
    with the SAME final state and outcome. (Statement now; proof — a mechanical
    fuel induction mirroring the two functions' identical structure — in the
    Phase 0.3 chunk.) -/
theorem execT_erase (P : Program) (dbase : Name → Option Word) (pad : Name → Nat)
    (stackLo : Word) (fuel : Nat) (stmt : PStmt) (s s' : St) (o : Outcome)
    (ws : List Word) :
    execT P dbase pad stackLo fuel stmt s = some (s', o, ws) →
    LowIR.Prog.exec P dbase pad stackLo fuel stmt s = some (s', o) := by
  sorry

/-- Instrumented top-level runner (mirrors `Prog.run`, keeps the footprint) —
    the executable interface `execT_erase` and the #guards go through. -/
def runT (P : Program) (stackLo : Word) (fuel : Nat) (f : Name) (argVals : List Word)
    (mem : Word → Byte) (sp0 : Word) (pad : Name → Nat := fun _ => 0)
    (dataBase : Word := 0x30000) : Option (St × Outcome × List Word) :=
  match List.lookup f P.env with
  | none => none
  | some fd =>
    let dbase := dbaseOf dataBase P.data
    let mem'  := installData dataBase P.data mem
    match frameEnter stackLo fd (pad f) argVals mem' sp0 with
    | none => none
    | some st0 => execT P dbase pad stackLo fuel fd.body st0

/-! ## Executable sanity (`#guard`) — the def oracle (RESUME-PROGSIM §6). -/

section Guards
open LowIR.Prog (chainEnv sumData frameLocal sub3 caller STACK_LO SP0 zeroMem)

/-- A bare machine with `blob` loaded at `CB`, everything else zero. -/
private def CB : Word := 0x10000
private def mkM (blob : List Byte) : State :=
  { reg := fun _ => 0, pc := CB, mem := LowIR.loadMem CB blob 0x20000 [] }

-- CODE half of `Installed`: the compiled chain decodes back, byte-for-byte.
#guard (do let blob ← progBytes chainEnv "f3"
           let L ← layoutOf chainEnv "f3" CB
           pure (codeInstalledB L (mkM blob))).getD false = true

-- CODE + DATA halves: `sumData` has a const-data object in the blob.
#guard (do let blob ← progBytes sumData "sumd"
           let L ← layoutOf sumData "sumd" CB
           pure (codeInstalledB L (mkM blob) && dataInstalledB L (mkM blob))).getD false = true

-- `execT` erases to `exec`: same observable return on the fixtures.
#guard (runT [("sub3", sub3)] STACK_LO 1000 "sub3" [30, 12, 2] zeroMem SP0).map
        (fun soo => (soo.1.rget 10).toNat) = some 40
#guard (runT [("frameLocal", frameLocal)] STACK_LO 1000 "frameLocal" [0xDEAD] zeroMem SP0).map
        (fun soo => (soo.1.rget 10).toNat) = some 0xDEAD

-- FOOTPRINTS: sub3 writes no memory; frameLocal's `sd` writes exactly 8 bytes;
-- caller inherits the callee `frameLocal`'s 8-byte footprint through the call.
#guard (runT [("sub3", sub3)] STACK_LO 1000 "sub3" [30, 12, 2] zeroMem SP0).map
        (fun soo => soo.2.2.length) = some 0
#guard (runT [("frameLocal", frameLocal)] STACK_LO 1000 "frameLocal" [0xDEAD] zeroMem SP0).map
        (fun soo => soo.2.2.length) = some 8
#guard (runT [("caller", caller), ("frameLocal", frameLocal)]
             STACK_LO 1000 "caller" [5] zeroMem SP0).map
        (fun soo => soo.2.2.length) = some 8

-- and the footprint bytes are the 8 consecutive frame addresses of the `sd`
-- (frameLocal's frameReg = sp0 - frameSize = SP0 - 16), in order.
#guard (runT [("frameLocal", frameLocal)] STACK_LO 1000 "frameLocal" [0xDEAD] zeroMem SP0).map
        (fun soo => soo.2.2) = some ((List.range 8).map (fun i => SP0 - 16 + BitVec.ofNat 64 i))

end Guards

end LowIR.ProgSim
