/-
  strtoull (base-10) — CONFORMANT overflow handling. On overflow the value saturates
  to ULLONG_MAX (2⁶⁴−1) and `errno` is set to ERANGE (34), and scanning continues to the
  first non-digit (C/POSIX behaviour). errno is returned in a register (x14), not a
  global — the function returns `(value=x12, errno=x14)`.

  Overflow test per digit (the standard one): `acc > T  ∨  (acc == T ∧ digit > 5)`, where
  `T = (2⁶⁴−1)/10 = 0x1999999999999999` and `(2⁶⁴−1) % 10 = 5`. `T` is built in the
  prelude by the nibble recurrence `x := 1; repeat 15×: x := (x<<4) | 9` (here `(x<<4)+9`,
  since the low nibble is 0 after the shift). ULLONG_MAX is `addi rd, x0, -1` (one instr).

  Unsigned (`geu`) comparisons throughout (bytes/thresholds are unsigned). Validated at the
  IL level against a conformant reference `strtoullConfSpec`.
-/
import LowIR.Ctrl

namespace LowIR.Ctrl.Strtoull2

open LowIR.Ctrl
open Rv64i (Word Byte)

-- regs: s=10 cursor=5 acc=12 errno=14 c=7 digit=28 t1=29 t2=30
-- consts: '0'=20(48) ':'=22(58) one=16(1) six=24(6) T=23(0x1999999999999999)
def lit (r v : Nat) : Stmt := .addi r 0 (BitVec.ofNat 12 v)

def ovf   : Stmt := seqs [ .addi 12 0 (BitVec.ofNat 12 4095),    -- acc := ULLONG_MAX (= -1)
                           lit 14 34 ]                           -- errno := ERANGE
def accum : Stmt := seqs [ .slli 29 12 3, .slli 30 12 1, .add 12 29 30, .add 12 12 28 ]

/-- one main-loop iteration: digit-check/break, then (if not yet overflowed) overflow-check
    + accumulate, then advance the cursor unconditionally. -/
def cbody : Stmt := seqs
  [ .lbu 7 5 0,
    .ife .geu 7 20 (.ife .geu 7 22 (.brkB 0) .skip) (.brkB 0),   -- digit? else break
    .ife .eq 14 0
      (seqs
        [ .sub 28 7 20,                                          -- digit := c - '0'
          .ife .geu 12 23                                        -- acc >= T ?
            (.ife .eq 12 23                                      -- acc == T ?
              (.ife .geu 28 24 ovf accum)                        -- digit >= 6 ? overflow : accum
              ovf)                                               -- acc > T : overflow
            accum ])                                             -- acc < T : accum
      .skip,                                                     -- already overflowed: skip
    .addi 5 5 1 ]                                                -- cursor++

def thresholdBuild : List Stmt :=
  (List.replicate 15 [Stmt.slli 23 23 4, Stmt.addi 23 23 (BitVec.ofNat 12 9)]).flatten

def strtoull : Stmt := seqs
  ([ lit 20 48, lit 22 58, lit 16 1, lit 24 6, lit 23 1 ]
    ++ thresholdBuild
    ++ [ .addi 12 0 0, .addi 14 0 0, .addi 5 10 0,
         .block (.while .lt 0 16 cbody) ])

/-! ### Conformant reference spec. -/

def ULLONG : Word := 0 - 1
def isDig (b : Byte) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- One conformant step: saturate on overflow, hold ULLONG once overflowed. -/
def confStep : Word × Nat → Byte → Word × Nat
  | (acc, e), b =>
    if e ≠ 0 then (acc, e)
    else
      let d := b.toNat - 48
      if acc.toNat * 10 + d > 2 ^ 64 - 1 then (ULLONG, 34)
      else (acc * 10 + BitVec.ofNat 64 d, 0)

def confFold : Word × Nat → List Byte → Word × Nat
  | st, []        => st
  | st, b :: rest => if isDig b then confFold (confStep st b) rest else st

def strtoullConfSpec (inp : List Byte) : Word × Nat := confFold (0, 0) inp

/-! ### IL-level harness + certification. -/

def inBase : Word := 0x1000

def strtoullState (inp : List Byte) : St :=
  { regs := fun i => if i = 10 then inBase else 0
    mem := fun a => let ia := (a - inBase).toNat; if ia < inp.length then (inp[ia]?).getD 0 else 0 }

def strtoullRun (inp : List Byte) (fuel : Nat) : Word × Nat :=
  match run fuel strtoull (strtoullState inp) with
  | some s => (s.rget 12, (s.rget 14).toNat)
  | none   => (0xDEAD, 0)

def asBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)

def battery : List (List Nat) :=
  [ [], [0x30], [0x31,0x32,0x33], [0x31,0x32,0x61,0x33], [0x61], [0x30,0x30,0x37],
    [0x34,0x32,0x39,0x34,0x39,0x36,0x37,0x32,0x39,0x36],                  -- 4294967296
    -- 18446744073709551615 = 2^64-1 (exactly max; NOT overflow, errno 0)
    [0x31,0x38,0x34,0x34,0x36,0x37,0x34,0x34,0x30,0x37,0x33,0x37,0x30,0x39,0x35,0x35,0x31,0x36,0x31,0x35],
    -- 18446744073709551616 = 2^64 (overflow → ULLONG, errno 34)
    [0x31,0x38,0x34,0x34,0x36,0x37,0x34,0x34,0x30,0x37,0x33,0x37,0x30,0x39,0x35,0x35,0x31,0x36,0x31,0x36],
    -- 99999999999999999999 (20 nines, way over → overflow), then a trailing non-digit
    [0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x7A] ]

/-- IL execution matches the conformant reference (value AND errno) on every case. -/
theorem strtoull_matches_spec :
    battery.all (fun inp => strtoullRun (asBytes inp) 100000 == strtoullConfSpec (asBytes inp)) = true := by
  native_decide

end LowIR.Ctrl.Strtoull2
