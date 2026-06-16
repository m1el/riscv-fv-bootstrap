/-
  strtoull (base-10 core) on the control-flow IL — a fresh function exercising the
  new constructs: an infinite `while` whose exit is `block { while(true) { … break … } }`
  (break-out-of-loop = wrap in block + `break-block 0`, crossing the transparent loop),
  and the no-multiply accumulator `acc*10 = (acc<<3) + (acc<<1)`.

  Scope: parses the leading decimal digits of a NUL-terminated string into x12,
  stopping at the first non-digit (64-bit wraparound on overflow, like the real
  strtoull modulo ULLONG_MAX+1). No whitespace/sign/base-prefix/errno — the digit
  loop is the heart of strtoull; those are straight-line preludes to add later.

  Validated at the IL level against a Lean reference `strtoullSpec`.
-/
import LowIR.Ctrl

namespace LowIR.Ctrl.Strtoull

open LowIR.Ctrl
open Rv64i (Word Byte)

-- regs: s=10(arg) cursor=5 acc=12(result) c=7 digit=28 t1=29 t2=30 ; '0'=20 '9'=21 one=16
def lit (r v : Nat) : Stmt := .addi r 0 (BitVec.ofNat 12 v)

/-- The digit loop, written as an infinite loop broken by `break-block`. -/
def strtoull10 : Stmt :=
  seqs
    [ lit 20 48, lit 21 57, lit 16 1,
      .addi 12 0 0,                 -- acc := 0
      .addi 5 10 0,                 -- cursor := s
      .block (.while .lt 0 16 (seqs -- while (0 < 1)  ≡  while true
        [ .lbu 7 5 0,                       -- c := mem[cursor]
          .ife .lt 7 20 (.brkB 0) .skip,    -- c < '0'  → break the block (exits loop)
          .ife .lt 21 7 (.brkB 0) .skip,    -- '9' < c  → break
          .sub 28 7 20,                     -- digit := c - '0'
          .slli 29 12 3,                    -- t1 := acc << 3   (acc*8)
          .slli 30 12 1,                    -- t2 := acc << 1   (acc*2)
          .add 12 29 30,                    -- acc := t1 + t2   (acc*10)
          .add 12 12 28,                    -- acc := acc + digit
          .addi 5 5 1 ]))                   -- cursor++
    ]

/-! ### Reference spec + IL-level harness. -/

def isDig (b : Byte) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- Fold the leading decimal digits, BitVec-64 arithmetic (matches the IL wraparound). -/
def specFold : Word → List Byte → Word
  | acc, []        => acc
  | acc, b :: rest =>
      if isDig b then specFold (acc * 10 + BitVec.ofNat 64 (b.toNat - 48)) rest else acc

def strtoullSpec (inp : List Byte) : Word := specFold 0 inp

def inBase : Word := 0x1000

def strtoull10State (inp : List Byte) : St :=
  { regs := fun i => if i = 10 then inBase else 0
    mem := fun a => let ia := (a - inBase).toNat; if ia < inp.length then (inp[ia]?).getD 0 else 0 }

def strtoull10Run (inp : List Byte) (fuel : Nat) : Word :=
  match run fuel strtoull10 (strtoull10State inp) with
  | some s => s.rget 12
  | none   => 0xDEAD

def asBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)

def battery : List (List Nat) :=
  [ [], [0x30],                                   -- "" , "0"
    [0x31,0x32,0x33],                             -- "123"
    [0x39,0x39,0x39,0x39,0x39],                   -- "99999"
    [0x31,0x32,0x61,0x33,0x34],                   -- "12a34" → 12
    [0x61],                                       -- "a" → 0
    [0x30,0x30,0x37],                             -- "007" → 7
    [0x34,0x32,0x39,0x34,0x39,0x36,0x37,0x32,0x39,0x36],   -- "4294967296" (>2^32)
    -- "18446744073709551615" = 2^64-1 (max, no overflow)
    [0x31,0x38,0x34,0x34,0x36,0x37,0x34,0x34,0x30,0x37,0x33,0x37,0x30,0x39,0x35,0x35,0x31,0x36,0x31,0x35],
    -- "18446744073709551616" = 2^64 (wraps to 0)
    [0x31,0x38,0x34,0x34,0x36,0x37,0x34,0x34,0x30,0x37,0x33,0x37,0x30,0x39,0x35,0x35,0x31,0x36,0x31,0x36] ]

/-- IL execution matches the reference on every case (incl. >2^32 and 64-bit wraparound). -/
theorem strtoull10_matches_spec :
    battery.all (fun inp => strtoull10Run (asBytes inp) 100000 == strtoullSpec (asBytes inp)) = true := by
  native_decide

end LowIR.Ctrl.Strtoull
