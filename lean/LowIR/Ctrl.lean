/-
  LowIR.Ctrl — LowIR extended with structured non-local control flow, as designed:

    block  body          -- break scope
    while  c a b body     -- continue scope (the loop)
    brkB k               -- break: exit the k-th enclosing BLOCK (loops transparent)
    contL k              -- continue: restart the k-th enclosing LOOP (blocks transparent)
    ret                  -- return from the function (absolute; caught only at the boundary)

  Semantics thread an `Outcome` through a clocked big-step `exec`. `ret` is the
  maximally-non-local outcome: every block/loop/seq/ife passes it through unchanged,
  caught only by the function-level `run`. `brkB`/`contL` use two independent de Bruijn
  index spaces (CompCert-style; LowIR is a compile target, so positional indices are fine).

  Built additively over `LowIR` (reuses `St`/`Cond`/`evalCond`); the original
  `LowIR` IL + compiler + proofs are left intact for comparison.
-/
import LowIR

namespace LowIR.Ctrl

open LowIR (St Cond evalCond)
open Rv64i (Word Byte)

abbrev Reg := Nat

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
  | ife    (c : Cond) (a b : Reg) (t e : Stmt)
  | while  (c : Cond) (a b : Reg) (body : Stmt)   -- continue scope
  | block  (body : Stmt)                           -- break scope
  | brkB   (k : Nat)                               -- exit k-th enclosing block
  | contL  (k : Nat)                               -- restart k-th enclosing loop
  | ret                                            -- return from function
deriving Repr

/-- Control outcome of a statement. -/
inductive Outcome where
  | normal | brk (k : Nat) | cont (k : Nat) | ret
deriving DecidableEq, Repr

/-- n-ary block as a smart constructor (keeps the core binary). -/
def block_ : List Stmt → Stmt := fun xs => .block (List.foldr .seq .skip xs)
def seqs   : List Stmt → Stmt := List.foldr .seq .skip

/-- Clocked big-step semantics with an outcome. Every recursive call is at `fuel`
    from `fuel+1` (structurally terminating, executable). -/
def exec : Nat → Stmt → St → Option (St × Outcome)
  | 0,      _,    _ => none
  | fuel+1, stmt, s =>
    match stmt with
    | .skip            => some (s, .normal)
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
    | .ife c a b t e   =>
        if evalCond c (s.rget a) (s.rget b) then exec fuel t s else exec fuel e s
    | .seq a b         =>
        match exec fuel a s with
        | some (s', .normal) => exec fuel b s'
        | other              => other                       -- brk/cont/ret skip b
    | .block body      =>
        match exec fuel body s with
        | some (s', .normal)     => some (s', .normal)
        | some (s', .brk 0)      => some (s', .normal)       -- caught here
        | some (s', .brk (k+1))  => some (s', .brk k)        -- cross this block
        | some (s', .cont k)     => some (s', .cont k)       -- transparent to continue
        | some (s', .ret)        => some (s', .ret)          -- transparent to return
        | none                   => none
    | .while c a b body =>
        if evalCond c (s.rget a) (s.rget b) then
          match exec fuel body s with
          | some (s', .normal)     => exec fuel (.while c a b body) s'
          | some (s', .cont 0)     => exec fuel (.while c a b body) s'   -- continue this loop
          | some (s', .cont (k+1)) => some (s', .cont k)                 -- cross this loop
          | some (s', .brk k)      => some (s', .brk k)                  -- transparent to break
          | some (s', .ret)        => some (s', .ret)
          | none                   => none
        else some (s, .normal)
    | .brkB k          => some (s, .brk k)
    | .contL k         => some (s, .cont k)
    | .ret             => some (s, .ret)

/-- Function-level runner: `normal` (fell off the end) and `ret` both mean "done". -/
def run (fuel : Nat) (p : Stmt) (s : St) : Option St :=
  match exec fuel p s with
  | some (s', .normal) => some s'
  | some (s', .ret)    => some s'
  | _                  => none

/-! ### Sanity: the control constructs do what they say. -/

-- a block with an early break: set x5:=1, break, then (skipped) x5:=2 → x5 = 1
private def s0 : St := { regs := fun _ => 0, mem := fun _ => 0 }

#guard
  (run 50 (.block (seqs [ .addi 5 0 1, .brkB 0, .addi 5 0 2 ])) s0).map (·.rget 5 |>.toNat)
    = some 1

-- ret short-circuits everything below it
#guard
  (run 50 (seqs [ .addi 5 0 7, .ret, .addi 5 0 9 ]) s0).map (·.rget 5 |>.toNat) = some 7

-- continue skips the rest of the loop body; loop runs while x6 < x7 (x6 counts up)
-- here: while x6 < 3 { x6++ ; continue ; x8:=1 }  → x8 stays 0, x6 ends 3
#guard
  (run 200 (seqs
      [ .addi 7 0 3,
        .while .lt 6 7 (seqs [ .addi 6 6 1, .contL 0, .addi 8 0 1 ]) ]) s0
   ).map (fun s => (s.rget 6 |>.toNat, s.rget 8 |>.toNat)) = some (3, 0)

end LowIR.Ctrl
