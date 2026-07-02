/-
  LowIR.Dump — a WAST-flavoured s-expression dumper for the Prog IR.

  A DEBUG tool, not a verified artifact: it pretty-prints a `Prog.Program`
  (or a single `FunDef` / `Stmt`) as nested s-expressions in a WebAssembly-text
  idiom, so a reader can eyeball the structure — the seq spine, the block/loop
  scopes, the `brk`/`cont` de-Bruijn depths, register moves, and the rodata.
  Registers are `$rN`; named symbols (functions and data objects) are `'name`, so
  the two namespaces can't collide (a data object called `r0` ≠ register 0).

  It is the seed of the "IR ↔ assembly mapping" discussed for `prog_sim`: this
  pass renders just the IR tree; a later pass will thread the layout positions
  (byte offset per node, resolved label positions) onto the same structure so it
  can serve both proof-transfer and (verified) debug-info consumers. Parsing and
  round-trip correctness are explicitly out of scope here.
-/
import LowIR.ProgLib

namespace LowIR.Prog

open LowIR (Cond)
open Rv64i (Word Byte)

/-! ## Small rendering helpers. -/

/-- Two-space indent for depth `n`. -/
def pad (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

/-- A register as a WASM-style local name, `$rN`. -/
def reg (r : Reg) : String := "$r" ++ toString r

/-- Signed rendering of a 12-bit immediate (the machine sign-extends it). -/
def imm12 (i : BitVec 12) : String := toString i.toInt

/-- Two-hex-digit byte, for data-string escapes. -/
def hex2 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  if s.length == 1 then "0" ++ s else s

/-- A `Cond` applied to two registers, as an s-expr comparison. -/
def dumpCond : Cond → Reg → Reg → String
  | .eq,  a, b => s!"(i64.eq (local.get {reg a}) (local.get {reg b}))"
  | .lt,  a, b => s!"(i64.lt_s (local.get {reg a}) (local.get {reg b}))"
  | .ge,  a, b => s!"(i64.ge_s (local.get {reg a}) (local.get {reg b}))"
  | .geu, a, b => s!"(i64.ge_u (local.get {reg a}) (local.get {reg b}))"

/-- `local.set $rd (op …)` — the common "compute into a register" shape. -/
def setr (rd : Reg) (rhs : String) : String := s!"(local.set {reg rd} {rhs})"

/-! ## The statement dumper.

    Each statement renders as one string with NO trailing newline, its first line
    already indented to `n`; compound nodes attach their closing parens to the last
    line of their last child (idiomatic Lisp), so `dumpStmt (n+1) child ++ ")"`
    just works. The `seq` spine is flattened into consecutive lines. -/
partial def dumpStmt (n : Nat) : Stmt → String
  | .skip            => pad n ++ "(nop)"
  | .seq a b         => dumpStmt n a ++ "\n" ++ dumpStmt n b
  | .addi rd rs imm  => pad n ++ setr rd s!"(i64.add (local.get {reg rs}) (i64.const {imm12 imm}))"
  | .add  rd a b     => pad n ++ setr rd s!"(i64.add (local.get {reg a}) (local.get {reg b}))"
  | .sub  rd a b     => pad n ++ setr rd s!"(i64.sub (local.get {reg a}) (local.get {reg b}))"
  | .orr  rd a b     => pad n ++ setr rd s!"(i64.or (local.get {reg a}) (local.get {reg b}))"
  | .slli rd rs sh   => pad n ++ setr rd s!"(i64.shl (local.get {reg rs}) (i64.const {sh}))"
  | .srli rd rs sh   => pad n ++ setr rd s!"(i64.shr_u (local.get {reg rs}) (i64.const {sh}))"
  | .lbu  rd rs imm  => pad n ++ setr rd s!"(i64.load8_u offset={imm12 imm} (local.get {reg rs}))"
  | .ld   rd rs imm  => pad n ++ setr rd s!"(i64.load offset={imm12 imm} (local.get {reg rs}))"
  | .sb   rb rv imm  => pad n ++ s!"(i64.store8 offset={imm12 imm} (local.get {reg rb}) (local.get {reg rv}))"
  | .sd   rb rv imm  => pad n ++ s!"(i64.store offset={imm12 imm} (local.get {reg rb}) (local.get {reg rv}))"
  | .annot a         => pad n ++ s!"(annot {String.quote a})"
  | .cref rd d       => pad n ++ setr rd s!"(cref '{d})"
  | .clen rd d       => pad n ++ setr rd s!"(clen '{d})"
  | .brkB k          => pad n ++ s!"(brk {k})"
  | .contL k         => pad n ++ s!"(cont {k})"
  | .ret             => pad n ++ "(return)"
  | .call _ _ f args rets =>
      let a := " ".intercalate (args.toList.map (fun r => s!"(local.get {reg r})"))
      let r := " ".intercalate (rets.toList.map reg)
      pad n ++ s!"(call '{f} (args {a}) (rets {r}))"
  | .ife c a b t e =>
      pad n ++ s!"(if {dumpCond c a b}" ++ "\n" ++
      pad (n+1) ++ "(then" ++ "\n" ++ dumpStmt (n+2) t ++ ")" ++ "\n" ++
      pad (n+1) ++ "(else" ++ "\n" ++ dumpStmt (n+2) e ++ "))"
  | .while c a b body =>
      pad n ++ s!"(while {dumpCond c a b}" ++ "\n" ++ dumpStmt (n+1) body ++ ")"
  | .block body =>
      pad n ++ "(block" ++ "\n" ++ dumpStmt (n+1) body ++ ")"

/-! ## Function and program dumpers. -/

/-- A function as a WAST `(func …)`. -/
def dumpFun (name : Name) (fd : FunDef) : String :=
  let params := " ".intercalate (fd.params.toList.map reg)
  let rets   := " ".intercalate (fd.rets.toList.map reg)
  pad 1 ++ s!"(func '{name} (param {params}) (result {rets}) " ++
    s!"(frame (size {fd.frameSize}) (base {reg fd.frameReg}))" ++ "\n" ++
    dumpStmt 2 fd.body ++ ")"

/-- A rodata object as a WAST `(data …)` with `\HH` byte escapes. -/
def dumpData (name : Name) (bytes : List Byte) : String :=
  let esc := String.join (bytes.map (fun b => "\\" ++ hex2 b.toNat))
  pad 1 ++ s!"(data '{name} \"{esc}\")"

/-- The whole program as a `(module …)`: rodata first, then functions. -/
def dumpProgram (p : Program) : String :=
  let datas := p.data.map (fun (nm, bs) => dumpData nm bs)
  let funs  := p.env.map (fun (nm, fd) => dumpFun nm fd)
  "(module\n" ++ String.intercalate "\n" (datas ++ funs) ++ ")"

/-! ## Demo. -/

-- A single function:
#eval IO.println (dumpFun "strlen" Lib.strlenF)

-- The whole library program (functions + rodata):
#eval IO.println (dumpProgram Lib.libProgram)

end LowIR.Prog
