/-
  LowIR.SSADump — the WAST-flavoured s-expression dumper for the SSA IR
  (the `LowIR.Dump` sibling; same conventions: registers `$rN`, names `'name`,
  seq spine flattened, closing parens on the last child line).

  The SSA IR sits closer to the WebAssembly text idiom than Prog does, and the
  dump shows it: `brk`/`ret` render as multi-value `(br k v…)`/`(return v…)`,
  `block`/`if` carry their result binders as `(outs $rN…)` (Wasm's result
  types, but named), and `while` shows the block-parameter plumbing
  explicitly — `(init …) (args …)` plus the `(default …)` guard-false body.
  A DEBUG tool, not a verified artifact; parsing is out of scope.
-/
import LowSSA.Lib
import LowIR.Dump            -- reuse the rendering helpers (pad/reg/imm12/…)

namespace LowIR.SSA

open LowIR.Prog (pad reg imm12 dumpCond setr)

/-- An operand: register read or immediate (signed rendering). -/
def opnd : Opnd → String
  | .reg r   => s!"(local.get {reg r})"
  | .const v => s!"(i64.const {v.toInt})"

/-- A value list, each with a leading space (empty list → empty string). -/
def vals (vs : List Opnd) : String := String.join (vs.map (fun o => " " ++ opnd o))

/-- Result binders, `" (outs $rA $rB)"`, empty for `[]`. -/
def outsS (outs : List Reg) : String :=
  if outs.isEmpty then "" else " (outs" ++ String.join (outs.map (fun r => " " ++ reg r)) ++ ")"

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
  | .brk k vs        => pad n ++ s!"(br {k}{vals vs})"
  | .cont k vs       => pad n ++ s!"(cont {k}{vals vs})"
  | .ret vs          => pad n ++ s!"(return{vals vs})"
  | .block outs body =>
      pad n ++ s!"(block{outsS outs}" ++ "\n" ++ dumpStmt (n+1) body ++ ")"
  | .ife c ca cb outs t e =>
      pad n ++ s!"(if{outsS outs} {dumpCond c ca cb}" ++ "\n" ++
      pad (n+1) ++ "(then" ++ "\n" ++ dumpStmt (n+2) t ++ ")" ++ "\n" ++
      pad (n+1) ++ "(else" ++ "\n" ++ dumpStmt (n+2) e ++ "))"
  | .«while» outs inits args c ca cb body dflt =>
      pad n ++ s!"(while{outsS outs} (init{vals inits}) (args" ++
        String.join (args.map (fun r => " " ++ reg r)) ++ s!") {dumpCond c ca cb}" ++ "\n" ++
      pad (n+1) ++ "(body" ++ "\n" ++ dumpStmt (n+2) body ++ ")" ++ "\n" ++
      pad (n+1) ++ "(default" ++ "\n" ++ dumpStmt (n+2) dflt ++ "))"
  | .call f argOps outs =>
      pad n ++ s!"(call '{f} (args{vals argOps}){outsS outs})"

/-- A function: params by name, results by ARITY (no return registers). -/
def dumpFun (name : Name) (fd : FunDef) : String :=
  let params := String.join (fd.params.map (fun r => " " ++ reg r))
  pad 1 ++ s!"(func '{name} (param{params}) (results {fd.rvc}) " ++
    s!"(frame (size {fd.frameSize}) (base {reg fd.frameReg}))" ++ "\n" ++
    dumpStmt 2 fd.body ++ ")"

/-- An environment as a `(module …)`. -/
def dumpEnv (env : Env) : String :=
  "(module\n" ++ String.intercalate "\n" (env.map fun nf => dumpFun nf.1 nf.2) ++ ")"

/-! ## Demo: the two ProgLib ports. -/

#eval IO.println (dumpFun "strlen" Lib.strlenS)
#eval IO.println (dumpEnv Lib.libEnvS)

end LowIR.SSA
