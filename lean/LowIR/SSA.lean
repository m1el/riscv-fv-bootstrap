/-
  LowIR.SSA — EXPERIMENT (2026-07-02, user-directed): an SSA variant of the
  D7/D8 Prog IR. Design record + criticism: docs/LOWIR-SSA-EXPERIMENT.md.

  Deltas from LowIR.Prog:

  • SSA over registers: every register is textually defined at most once per
    function (params, frameReg, op destinations, and the out/arg binders below).
    Enforced by a decidable checker (`wfFun` = def census + use/arity/type
    check), NOT intrinsically — semantics stays a mutable register file, the
    checker is the N3 "checker produces the hypothesis" pattern.

  • Valued outcomes: `brk`/`cont`/`ret` carry a `List Word`. Function results
    come out of `ret [operands]` — `FunDef` declares only the return ARITY
    (`rvc`), there are no return registers (D7's `rets : Vector Reg rvc` is
    gone). `run` returns the values directly.

  • `block (outs) body` and `ife c a b (outs) t e` are value-binding BREAK
    scopes (Wasm-style — note: in Prog, `ife` was transparent to brk indices;
    here it shifts them). `brk 0 [vs]` delivers the construct's outs. An arm /
    body may instead end `.never` (ret, or a jump further out) — then outs are
    simply not bound on that path, which is fine because the join is not
    reached through it. Plain fall-through is allowed only when `outs = []`.

  • `while (outs) (inits) (args) c a b body defaultBody` — block-parameter
    loops, "iteration is a tail call": `args` are bound to `inits` on entry
    and REBOUND by `cont 0 [vs]` (they are the φ-nodes, Cranelift/MLIR-style).
    Each head entry evaluates `c` with args in scope: true → `body`,
    false → `defaultBody` — ALSO with the current args in scope, so a
    guard-exit can deliver loop-carried values (`brk 0 [.reg acc]`); the
    zero-trip case sees args = inits. Both bodies must be `.never`-typed
    (end in cont/brk/ret): there is no implicit fall-through-and-loop.
    `while` is both a break scope (brk 0 exits with outs) and a continue
    scope (cont 0 re-enters) — in Prog/Ctrl it was only a continue scope.

  • Operands: `Opnd = .reg r | .const v` wherever values flow into a
    construct (brk/cont/ret arguments, while inits, call arguments) — kills
    the addi-a-constant-into-a-register dance at those sites.

  • Types: a statement is `.never` (control cannot fall through) or `.thru`.
    The value arities the user sketched as `.value (Vect n Word)` live in the
    checker's label contexts (`brks`/`conts : List Nat` = arity of each
    enclosing break/continue target, innermost first). Never-detection for
    `ife`/`block` needs may-break-0 information (Wasm validator's
    "unreachable" polymorphism) — approximated by the syntactic `mayBrk`.

  Omitted as orthogonal (they'd port verbatim from Prog): const data
  (`cref`/`clen`/`Program.data`), the P1 `pad` oracle, `execT` footprints.
-/
import LowIR.Prog

namespace LowIR.SSA

open LowIR (Cond evalCond)
open Rv64i (Word Byte)

/- Prog's machine state (regs / mem / semantic sp) is reused verbatim. NB: the
   abbrevs are needed because inside `namespace LowIR.SSA` a bare `St` resolves
   to `LowIR.St` (the original flat IL's state, no `sp`) before any `open`. -/
abbrev St   := LowIR.Prog.St
abbrev Reg  := LowIR.Prog.Reg
abbrev Name := LowIR.Prog.Name

/-- Value operand: a register read or an immediate 64-bit constant. -/
inductive Opnd where
  | reg   (r : Reg)
  | const (v : Word)
deriving Repr

def evalOpnd (s : St) : Opnd → Word
  | .reg r   => s.rget r
  | .const v => v

/-- Outcomes carry the values of the jump that produced them. -/
inductive Outcome where
  | normal
  | brk  (k : Nat) (vs : List Word)
  | cont (k : Nat) (vs : List Word)
  | ret  (vs : List Word)
deriving Repr

inductive Stmt where
  | skip
  | seq    (a b : Stmt)
  | addi   (rd rs : Reg) (imm : BitVec 12)
  | add    (rd rs1 rs2 : Reg)
  | sub    (rd rs1 rs2 : Reg)
  | orr    (rd rs1 rs2 : Reg)
  | slli   (rd rs : Reg) (sh : Nat)
  | srli   (rd rs : Reg) (sh : Nat)
  | lbu    (rd rs : Reg) (imm : BitVec 12)
  | sb     (rbase rval : Reg) (imm : BitVec 12)
  | ld     (rd rs : Reg) (imm : BitVec 12)
  | sd     (rbase rval : Reg) (imm : BitVec 12)
  | annot  (a : String)
  | ife    (c : Cond) (ca cb : Reg) (outs : List Reg) (t e : Stmt)
  | block  (outs : List Reg) (body : Stmt)
  | «while» (outs : List Reg) (inits : List Opnd) (args : List Reg)
            (c : Cond) (ca cb : Reg) (body dflt : Stmt)
  | brk    (k : Nat) (vs : List Opnd)
  | cont   (k : Nat) (vs : List Opnd)
  | ret    (vs : List Opnd)
  | call   (f : Name) (argOps : List Opnd) (outs : List Reg)
deriving Repr

/-- A function: parameter registers, return ARITY (no return registers — D7's
    `rets` vector is gone; results travel in the `.ret` outcome), D8 frame. -/
structure FunDef where
  rvc       : Nat
  params    : List Reg
  frameSize : Nat
  frameReg  : Reg
  body      : Stmt

abbrev Env := List (Name × FunDef)

/-- Bind `outs := vs` positionally (zip truncates; arities are guarded at the
    produce sites in `exec` and statically by `check`). -/
def bindOuts (s : St) (outs : List Reg) (vs : List Word) : St :=
  (outs.zip vs).foldl (fun st rv => st.rset rv.1 rv.2) s

/-- D8 frame entry, minus the P1 pad oracle (orthogonal, omitted here). -/
def frameEnter (stackLo : Word) (fd : FunDef) (argVals : List Word)
    (mem : Word → Byte) (spCaller : Word) : Option St :=
  if spCaller.toNat < stackLo.toNat + fd.frameSize then none
  else
    let frameBase := spCaller - BitVec.ofNat 64 fd.frameSize
    let withParams : Reg → Word :=
      (fd.params.zip argVals).foldl
        (fun rf pv => fun r => if r = pv.1 then pv.2 else rf r) (fun _ => 0)
    some { regs := fun r => if r = fd.frameReg then frameBase else withParams r
           mem  := mem
           sp   := frameBase }

/-- The value-binding break-scope catch shared by `block` and `ife`:
    `brk 0 vs` binds the outs and normalizes; `normal` falls through only for
    `outs = []`; deeper brks shift; cont/ret pass (these are not cont scopes). -/
def catch0 (outs : List Reg) : Option (St × Outcome) → Option (St × Outcome)
  | some (s, .brk 0 vs)     =>
      if vs.length == outs.length then some (bindOuts s outs vs, .normal) else none
  | some (s, .normal)       => if outs.isEmpty then some (s, .normal) else none
  | some (s, .brk (k+1) vs) => some (s, .brk k vs)
  | some (s, .cont k vs)    => some (s, .cont k vs)
  | some (s, .ret vs)       => some (s, .ret vs)
  | none                    => none

/-- Clocked big-step semantics, Prog's shape with valued outcomes.

    `while`: bind args := inits, evaluate the guard WITH args in scope; true →
    body, false → dflt (same scopes — dflt may brk 0 with loop-carried values,
    or even cont 0 to restart). Iteration is re-execution of the `while` with
    `inits := consts of the continued values` — the "tail call" made literal;
    recursion is at `fuel` from `fuel+1` as everywhere else. -/
def exec (env : Env) (stackLo : Word) : Nat → Stmt → St → Option (St × Outcome)
  | 0,      _,    _ => none
  | fuel+1, stmt, s =>
    match stmt with
    | .skip            => some (s, .normal)
    | .annot _         => some (s, .normal)
    | .addi rd rs imm  => some (s.rset rd (s.rget rs + imm.signExtend 64), .normal)
    | .add  rd r1 r2   => some (s.rset rd (s.rget r1 + s.rget r2), .normal)
    | .sub  rd r1 r2   => some (s.rset rd (s.rget r1 - s.rget r2), .normal)
    | .orr  rd r1 r2   => some (s.rset rd (s.rget r1 ||| s.rget r2), .normal)
    | .slli rd rs sh   => some (s.rset rd (s.rget rs <<< sh), .normal)
    | .srli rd rs sh   => some (s.rset rd (s.rget rs >>> sh), .normal)
    | .lbu  rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd ((s.loadByte a).setWidth 64), .normal)
    | .sb   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeByte a ((s.rget rv).setWidth 8), .normal)
    | .ld   rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd (s.loadWord a), .normal)
    | .sd   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeWord a (s.rget rv), .normal)
    | .seq a b         =>
        match exec env stackLo fuel a s with
        | some (s', .normal) => exec env stackLo fuel b s'
        | other              => other
    | .brk k vs        => some (s, .brk k (vs.map (evalOpnd s)))
    | .cont k vs       => some (s, .cont k (vs.map (evalOpnd s)))
    | .ret vs          => some (s, .ret (vs.map (evalOpnd s)))
    | .block outs body => catch0 outs (exec env stackLo fuel body s)
    | .ife c ca cb outs t e =>
        let arm := if evalCond c (s.rget ca) (s.rget cb) then t else e
        catch0 outs (exec env stackLo fuel arm s)
    | .«while» outs inits args c ca cb body dflt =>
        if inits.length == args.length then
          let s0 := bindOuts s args (inits.map (evalOpnd s))
          let branch := if evalCond c (s0.rget ca) (s0.rget cb) then body else dflt
          match exec env stackLo fuel branch s0 with
          | some (s1, .cont 0 vs) =>
              if vs.length == args.length then
                exec env stackLo fuel (.«while» outs (vs.map .const) args c ca cb body dflt) s1
              else none
          | some (s1, .brk 0 vs)  =>
              if vs.length == outs.length then some (bindOuts s1 outs vs, .normal) else none
          | some (s1, .brk (k+1) vs)  => some (s1, .brk k vs)
          | some (s1, .cont (k+1) vs) => some (s1, .cont k vs)
          | some (s1, .ret vs)        => some (s1, .ret vs)
          | some (_, .normal)         => none   -- bodies are .never (checker bans this)
          | none                      => none
        else none
    | .call f argOps outs =>
        match List.lookup f env with
        | none => none
        | some fd =>
          if argOps.length == fd.params.length && outs.length == fd.rvc then
            match frameEnter stackLo fd (argOps.map (evalOpnd s)) s.mem s.sp with
            | none => none
            | some callee =>
              match exec env stackLo fuel fd.body callee with
              | some (s1, .ret vs)  =>
                  if vs.length == fd.rvc then
                    some (bindOuts { s with mem := s1.mem } outs vs, .normal)
                  else none
              | some (s1, .normal)  =>
                  if fd.rvc == 0 then some ({ s with mem := s1.mem }, .normal) else none
              | some _ => none      -- escaping brk/cont (checker bans)
              | none   => none
          else none

/-! ### The checker (SSA + arities + never/thru types) -/

/-- Statement type: can control fall through to the next statement? -/
inductive Ty where
  | never
  | thru
deriving BEq, DecidableEq, Repr

/-- May `stmt` surface outcome `.brk k`? Syntactic over-approximation, used
    only to GRANT `.thru` to a construct whose bodies are all `.never` but
    which is still enterable-from-below via its own `brk 0`. -/
def mayBrk : Nat → Stmt → Bool
  | k, .seq a b                     => mayBrk k a || mayBrk k b
  | k, .brk j _                     => j == k
  | k, .ife _ _ _ _ t e             => mayBrk (k+1) t || mayBrk (k+1) e
  | k, .block _ body                => mayBrk (k+1) body
  | k, .«while» _ _ _ _ _ _ body dflt => mayBrk (k+1) body || mayBrk (k+1) dflt
  | _, _                            => false

/-- All textual definition sites (x0 filtered later — writing it is a discard). -/
def defs : Stmt → List Reg
  | .seq a b            => defs a ++ defs b
  | .addi rd _ _        => [rd]
  | .add rd _ _         => [rd]
  | .sub rd _ _         => [rd]
  | .orr rd _ _         => [rd]
  | .slli rd _ _        => [rd]
  | .srli rd _ _        => [rd]
  | .lbu rd _ _         => [rd]
  | .ld rd _ _          => [rd]
  | .ife _ _ _ outs t e => outs ++ defs t ++ defs e
  | .block outs body    => outs ++ defs body
  | .«while» outs _ args _ _ _ body dflt => outs ++ args ++ defs body ++ defs dflt
  | .call _ _ outs      => outs
  | _                   => []

def useR (avail : List Reg) (r : Reg) : Bool := r == 0 || avail.contains r

def useO (avail : List Reg) : Opnd → Bool
  | .reg r   => useR avail r
  | .const _ => true

/-- Use/arity/type check. `brks`/`conts` are the arities of the enclosing
    break/continue targets (innermost first); `avail` the registers defined on
    every path reaching this point (dominance in a structured IR). Returns the
    statement's `Ty` and the fall-through `avail`. Def-once is NOT checked
    here — that is `wfFun`'s census. Dead code after a `.never` statement is
    rejected (`seq`). -/
def check (env : Env) (rvc : Nat) :
    List Nat → List Nat → List Reg → Stmt → Option (Ty × List Reg)
  | _, _, avail, .skip    => some (.thru, avail)
  | _, _, avail, .annot _ => some (.thru, avail)
  | brks, conts, avail, .seq a b => do
      let (ta, av1) ← check env rvc brks conts avail a
      if ta == Ty.thru then check env rvc brks conts av1 b else none
  | _, _, avail, .addi rd rs _ =>
      if useR avail rs then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .add rd r1 r2 =>
      if useR avail r1 && useR avail r2 then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .sub rd r1 r2 =>
      if useR avail r1 && useR avail r2 then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .orr rd r1 r2 =>
      if useR avail r1 && useR avail r2 then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .slli rd rs sh =>
      if useR avail rs && decide (sh < 64) then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .srli rd rs sh =>
      if useR avail rs && decide (sh < 64) then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .lbu rd rs _ =>
      if useR avail rs then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .ld rd rs _ =>
      if useR avail rs then some (.thru, avail ++ [rd]) else none
  | _, _, avail, .sb rb rv _ =>
      if useR avail rb && useR avail rv then some (.thru, avail) else none
  | _, _, avail, .sd rb rv _ =>
      if useR avail rb && useR avail rv then some (.thru, avail) else none
  | brks, _, avail, .brk k vs => do
      let ar ← brks[k]?
      if vs.length == ar && vs.all (useO avail) then some (Ty.never, avail) else none
  | _, conts, avail, .cont k vs => do
      let ar ← conts[k]?
      if vs.length == ar && vs.all (useO avail) then some (Ty.never, avail) else none
  | _, _, avail, .ret vs =>
      if vs.length == rvc && vs.all (useO avail) then some (.never, avail) else none
  | brks, conts, avail, .block outs body => do
      let (tb, _) ← check env rvc (outs.length :: brks) conts avail body
      if tb == Ty.never || outs.isEmpty then
        some (if tb == Ty.thru || mayBrk 0 body then Ty.thru else .never, avail ++ outs)
      else none
  | brks, conts, avail, .ife _ ca cb outs t e =>
      if useR avail ca && useR avail cb then do
        let (tt, _) ← check env rvc (outs.length :: brks) conts avail t
        let (te, _) ← check env rvc (outs.length :: brks) conts avail e
        if (tt == Ty.never || outs.isEmpty) && (te == Ty.never || outs.isEmpty) then
          some (if tt == Ty.thru || te == Ty.thru || mayBrk 0 t || mayBrk 0 e
                then Ty.thru else .never,
                avail ++ outs)
        else none
      else none
  | brks, conts, avail, .«while» outs inits args _ ca cb body dflt =>
      let availB := avail ++ args
      if inits.length == args.length && inits.all (useO avail)
         && useR availB ca && useR availB cb then do
        let (tb, _) ← check env rvc (outs.length :: brks) (args.length :: conts) availB body
        let (td, _) ← check env rvc (outs.length :: brks) (args.length :: conts) availB dflt
        if tb == Ty.never && td == Ty.never then
          some (if mayBrk 0 body || mayBrk 0 dflt then Ty.thru else .never, avail ++ outs)
        else none
      else none
  | _, _, avail, .call f argOps outs =>
      match List.lookup f env with
      | some fd =>
          if argOps.length == fd.params.length && outs.length == fd.rvc
             && argOps.all (useO avail)
          then some (.thru, avail ++ outs) else none
      | none => none

/-- SSA well-formedness of one function: every register textually defined at
    most once (params + frameReg + body defs; x0 exempt — it's a discard), and
    the body checks with type `.never` (all paths end in `ret`) unless the
    function returns nothing (then fall-through = `ret []`). -/
def wfFun (env : Env) (fd : FunDef) : Bool :=
  let ds := (fd.params ++ [fd.frameReg] ++ defs fd.body).filter (· != 0)
  ds.eraseDups.length == ds.length &&
  match check env fd.rvc [] [] (fd.params ++ [fd.frameReg]) fd.body with
  | some (ty, _) => ty == Ty.never || fd.rvc == 0
  | none         => false

def wfEnv (env : Env) : Bool := env.all (fun nf => wfFun env nf.2)

/-- Top-level entry: call `f` on a fresh machine; results are the `.ret`
    VALUES — no register-reading convention at the boundary. -/
def run (env : Env) (stackLo : Word) (fuel : Nat) (f : Name) (argVals : List Word)
    (mem : Word → Byte) (sp0 : Word) : Option (St × List Word) :=
  match List.lookup f env with
  | none => none
  | some fd =>
    if argVals.length == fd.params.length then
      match frameEnter stackLo fd argVals mem sp0 with
      | none => none
      | some st0 =>
        match exec env stackLo fuel fd.body st0 with
        | some (s1, .ret vs) => if vs.length == fd.rvc then some (s1, vs) else none
        | some (s1, .normal) => if fd.rvc == 0 then some (s1, []) else none
        | _ => none
    else none

/-! ### Sanity battery (`#guard` — executable, no proofs) -/

/-- `sub3 (a,b,c) = (a+b)-c` — SSA: fresh destination each step. -/
def sub3 : FunDef :=
  { rvc := 1, params := [10, 11, 12], frameSize := 0, frameReg := 3
    body := .seq (.add 6 10 11) (.seq (.sub 7 6 12) (.ret [.reg 7])) }

/-- The user's `if` example: `pick (c, x) = if c = 0 then 99 else x`.
    The then-arm is `.never` (returns directly) — out r12 is NOT initialized
    on that path and needn't be; the else-arm delivers r12 via `brk 0`. -/
def pick : FunDef :=
  { rvc := 1, params := [10, 11], frameSize := 0, frameReg := 3
    body := .seq (.ife .eq 10 0 [12]
                    (.ret [.const 99])
                    (.brk 0 [.reg 11]))
                 (.ret [.reg 12]) }

/-- A value-producing block: outs bound by the mandatory terminal `brk 0`. -/
def blockVal : FunDef :=
  { rvc := 1, params := [], frameSize := 0, frameReg := 3
    body := .seq (.block [5, 6]
                    (.seq (.addi 7 0 1) (.seq (.addi 8 0 2) (.brk 0 [.reg 7, .reg 8]))))
                 (.seq (.add 9 5 6) (.ret [.reg 9])) }

/-- `sumTo n = 1+…+n`, the block-parameter loop: args (i, acc) carried by
    `cont 0`; the guard-exit `dflt` sees the CURRENT args and delivers acc —
    the loop-carried result survives a guard exit (with the earlier
    `defaultOut : List Opnd` design it would have been discarded). -/
def sumTo : FunDef :=
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := .seq (.«while» [20] [.const 1, .const 0] [11, 12] .geu 10 11
                    (.seq (.add 13 12 11) (.seq (.addi 14 11 1)
                       (.cont 0 [.reg 14, .reg 13])))
                    (.brk 0 [.reg 12]))
                 (.ret [.reg 20]) }

/-- `sumCap (n, cap)`: sum 1..n but stop as soon as acc ≥ cap — exercises a
    `brk 1` escaping an `ife` into the `while` (ife shifts brk, not cont). -/
def sumCap : FunDef :=
  { rvc := 1, params := [10, 15], frameSize := 0, frameReg := 3
    body := .seq (.«while» [20] [.const 1, .const 0] [11, 12] .geu 10 11
                    (.seq (.add 13 12 11) <| .seq (.addi 14 11 1) <|
                       .ife .geu 13 15 []
                         (.brk 1 [.reg 13])
                         (.cont 0 [.reg 14, .reg 13]))
                    (.brk 0 [.reg 12]))
                 (.ret [.reg 20]) }

/-- Multi-value return, no return registers anywhere. -/
def swap : FunDef :=
  { rvc := 2, params := [10, 11], frameSize := 0, frameReg := 3
    body := .ret [.reg 11, .reg 10] }

/-- D8 frame roundtrip under SSA names. -/
def frameLocal : FunDef :=
  { rvc := 1, params := [10], frameSize := 16, frameReg := 8
    body := .seq (.sd 8 10 0) (.seq (.ld 11 8 0) (.ret [.reg 11])) }

/-- `caller v = frameLocal (v+1) + 1` — call results bind at the site. -/
def caller : FunDef :=
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := .seq (.addi 11 10 1) <|
            .seq (.call "frameLocal" [.reg 11] [12]) <|
            .seq (.addi 13 12 1) (.ret [.reg 13]) }

/-- Recursive sum with a frame-parked `n`; both `ife` arms are `.never`, so
    the `ife` itself types `.never` and IS the function's ending. -/
def recFn : FunDef :=
  { rvc := 1, params := [10], frameSize := 8, frameReg := 8
    body := .seq (.addi 5 0 1)
            (.ife .geu 10 5 []
              (.seq (.sd 8 10 0) <| .seq (.addi 6 10 (-1 : BitVec 12)) <|
               .seq (.call "rec" [.reg 6] [7]) <| .seq (.ld 9 8 0) <|
               .seq (.add 11 9 7) (.ret [.reg 11]))
              (.ret [.const 0])) }

def testEnv : Env :=
  [("sub3", sub3), ("pick", pick), ("blockVal", blockVal), ("sumTo", sumTo),
   ("sumCap", sumCap), ("swap", swap), ("frameLocal", frameLocal),
   ("caller", caller), ("rec", recFn)]

def testRun (f : Name) (args : List Word) : Option (St × List Word) :=
  run testEnv Prog.STACK_LO 1000 f args Prog.zeroMem Prog.SP0

#guard wfEnv testEnv

#guard (testRun "sub3" [30, 12, 2]).map (·.2.map (·.toNat)) = some [40]

-- the user's if: else-arm breaks with a value; then-arm returns, r12 uninitialized
#guard (testRun "pick" [1, 7]).map (·.2.map (·.toNat)) = some [7]
#guard (testRun "pick" [0, 7]).map (·.2.map (·.toNat)) = some [99]

#guard (testRun "blockVal" []).map (·.2.map (·.toNat)) = some [3]

-- guard-exit CARRIES the loop-carried acc (the defaultBody payoff)…
#guard (testRun "sumTo" [10]).map (·.2.map (·.toNat)) = some [55]
-- …and the zero-trip case sees args = inits (acc = 0)
#guard (testRun "sumTo" [0]).map (·.2.map (·.toNat)) = some [0]

-- early break out of ife-in-while (10 = 1+2+3+4, capped at ≥ 7);
-- guard exit still fine when the cap is never hit
#guard (testRun "sumCap" [10, 7]).map (·.2.map (·.toNat)) = some [10]
#guard (testRun "sumCap" [3, 100]).map (·.2.map (·.toNat)) = some [6]

#guard (testRun "swap" [3, 4]).map (·.2.map (·.toNat)) = some [4, 3]
#guard (testRun "frameLocal" [0xDEAD]).map (·.2.map (·.toNat)) = some [0xDEAD]
#guard (testRun "caller" [5]).map (·.2.map (·.toNat)) = some [7]
#guard (testRun "caller" [5]).map (·.1.sp) = some Prog.SP0

#guard (testRun "rec" [10]).map (·.2.map (·.toNat)) = some [55]
-- 8-byte frames on a 0x4000 stack: depth 3000 must trip the overflow check
#guard run testEnv Prog.STACK_LO 100000 "rec" [3000] Prog.zeroMem Prog.SP0 = none

/-! Checker negatives — each violates exactly one rule. -/

-- double definition of r5 (SSA census)
#guard !wfFun testEnv
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := .seq (.addi 5 0 1) (.seq (.addi 5 5 1) (.ret [.reg 5])) }

-- use before definition (r5 never defined)
#guard !wfFun testEnv
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := .seq (.add 6 5 10) (.ret [.reg 6]) }

-- arm-local r5 is not in scope after the join (outs are the only exports)
#guard !wfFun testEnv
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := .seq (.ife .eq 10 0 [] (.addi 5 0 1) .skip) (.ret [.reg 5]) }

-- brk arity ≠ outs arity
#guard !wfFun testEnv
  { rvc := 0, params := [], frameSize := 0, frameReg := 3
    body := .block [5] (.brk 0 []) }

-- while body must be .never (no implicit fall-through-and-loop)
#guard !wfFun testEnv
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := .seq (.«while» [20] [.const 0] [11] .geu 10 11
                    (.addi 13 11 1) (.brk 0 [.reg 11]))
                 (.ret [.reg 20]) }

-- rvc = 1 but the body can fall through without returning
#guard !wfFun testEnv
  { rvc := 1, params := [], frameSize := 0, frameReg := 3
    body := .addi 5 0 1 }

-- dead code after a .never statement is rejected
#guard !wfFun testEnv
  { rvc := 0, params := [], frameSize := 0, frameReg := 3
    body := .seq (.ret []) .skip }

-- never-typing: both recFn ife arms return, so its body types .never …
#guard (check testEnv 1 [] [] [10, 8] recFn.body).map (·.1) = some Ty.never
-- … while pick's ife can be exited via brk 0, so its body needs the final ret
#guard (check testEnv 1 [] [] [10, 11, 3] pick.body).map (·.1) = some Ty.never

end LowIR.SSA
