/-
  hex0 on the control-flow IL (`LowIR.Ctrl`). The point: error handling becomes a
  FLAT guard cascade with `ret`, instead of the original deeply-nested ifes + the
  `in_idx := in_len` poison-the-loop-guard hack.

  Compare `LowIR/Hex0Prog.lean`'s `body` (nested, every error leaf must be the last
  statement on its path) with `hexPath` below (a flat sequence of `ife guard (err) skip`
  then the work). `err code = seqs [set status; ret]` — `ret` exits the whole function.

  Validated at the IL level (`Ctrl.exec` directly) against `Hex0.coreSpec`.
-/
import LowIR.Ctrl
import Hex0.Spec

namespace LowIR.Ctrl.Hex0

open LowIR.Ctrl
open Rv64i (Word Byte)

-- registers: in_ptr=10 in_len=11 out_ptr=12 out_cap=13 ; in_idx=5 out_idx=6 chr=7
--            hi=28 lo=29 addr=30 tmp=31 b=8 g=15 status=14
-- consts: '0'=20 '9'=21 'A'=22 'F'=23 nl=24 sp=25 us=26 '#'=27 ';'=18 bad=19 off=17 one=16

def lit (r v : Nat) : Stmt := .addi r 0 (BitVec.ofNat 12 v)

/-- early return with a status code — replaces the old `in_idx := in_len` hack. -/
def err (code : Nat) : Stmt := .seq (lit 14 code) .ret

def pnib (dst src : Reg) : Stmt :=
  .ife .geu src 20
    (.ife .geu 21 src (.sub dst src 20)
      (.ife .geu src 22 (.ife .geu 23 src (.sub dst src 17) (lit dst 255)) (lit dst 255)))
    (lit dst 255)

def readAdv (dst : Reg) : Stmt := seqs [.add 30 10 5, .lbu dst 30 0, .addi 5 5 1]

def cgGuard : Stmt :=
  .ife .lt 5 11
    (seqs [.add 30 10 5, .lbu 8 30 0, .ife .eq 8 24 (lit 15 0) (lit 15 1)])
    (lit 15 0)

def skipComment : Stmt :=
  .seq cgGuard (.while .geu 15 16 (.seq (.addi 5 5 1) cgGuard))

/-- The hex-digit path — now a FLAT cascade: each guard `ret`s on failure (else `skip`
    and fall through), then the byte is written. No nesting, no poisoned guard. -/
def hexPath : Stmt :=
  seqs
    [ pnib 28 7,
      .ife .eq 28 19 (err 5) .skip,          -- bad high  → Unknown
      .ife .geu 5 11 (err 4) .skip,           -- no low    → Trailing
      readAdv 7,                             -- chr := low
      .ife .eq 7 24 (err 3) .skip,           -- low-stop  → Split
      .ife .eq 7 25 (err 3) .skip,
      .ife .eq 7 26 (err 3) .skip,
      .ife .eq 7 27 (err 3) .skip,
      .ife .eq 7 18 (err 3) .skip,
      pnib 29 7,
      .ife .eq 29 19 (err 5) .skip,          -- bad low   → Unknown
      .ife .geu 6 13 (err 2) .skip,           -- out full  → OutputShort
      .slli 31 28 4, .orr 31 31 29, .add 30 12 6, .sb 30 31 0, .addi 6 6 1 ]

/-- one main-loop iteration: read a char, dispatch; falling off the end = "continue". -/
def body : Stmt :=
  .seq (readAdv 7) <|
  .ife .eq 7 27 skipComment <|               -- '#'  comment
  .ife .eq 7 18 skipComment <|               -- ';'  comment
  .ife .eq 7 24 .skip <|                      -- '\n' skip
  .ife .eq 7 25 .skip <|                      -- ' '  skip
  .ife .eq 7 26 .skip <|                       -- '_'  skip
  hexPath

def hex0 : Stmt :=
  seqs
    [ lit 20 48, lit 21 57, lit 22 65, lit 23 70, lit 24 10, lit 25 32,
      lit 26 95, lit 27 35, lit 18 59, lit 19 255, lit 17 55, lit 16 1,
      lit 5 0, lit 6 0, lit 14 0,
      .while .lt 5 11 body ]

/-! ### IL-level harness + certification against `Hex0.coreSpec`. -/

def inBase  : Word := 0x1000
def outBase : Word := 0x4000

def hex0ILState (inp : List Byte) (cap : Nat) : St :=
  { regs := fun i =>
      if i = 10 then inBase else if i = 11 then BitVec.ofNat 64 inp.length
      else if i = 12 then outBase else if i = 13 then BitVec.ofNat 64 cap else 0
    mem := fun a => let ia := (a - inBase).toNat; if ia < inp.length then (inp[ia]?).getD 0 else 0 }

def outBytes (s : St) : List Nat :=
  (List.range (s.rget 6).toNat).map (fun i => (s.mem (outBase + BitVec.ofNat 64 i)).toNat)

def hex0Run (inp : List Byte) (cap fuel : Nat) : Nat × List Nat × Nat :=
  match run fuel hex0 (hex0ILState inp cap) with
  | some s => ((s.rget 14).toNat, outBytes s, (s.rget 6).toNat)
  | none   => (255, [], 0)

abbrev TC := List Nat × Nat
def asBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)

def battery : List TC :=
  [ ([], 16), ([0x34,0x31], 16), ([0x34,0x31,0x34,0x32], 16),
    ([0x34,0x31,0x5F,0x34,0x32], 16), ([0x34,0x31,0x0A,0x34,0x32], 16),
    ([0x34,0x31], 1), ([0x34,0x31,0x34,0x32], 1), ([0x34,0x31,0x34,0x32], 0),
    ([0x34], 16), ([0x34,0x20], 16), ([0x34,0x3B], 16), ([0x47], 16), ([0x34,0x47], 16),
    ([0x23,0x68,0x69,0x0A,0x34,0x31], 16), ([0x3B,0x78,0x0A,0x41,0x46], 16),
    ([0x23,0x6E,0x6F,0x6E,0x65], 16), ([0x41,0x42,0x43,0x44], 16) ]

/-- The flat-`ret` hex0, run on the IL semantics, matches the spec on every case. -/
theorem hex0_matches_spec :
    battery.all (fun (tc : TC) =>
      hex0Run (asBytes tc.1) tc.2 5000 == Hex0.coreSpec tc.1 tc.2) = true := by
  native_decide

end LowIR.Ctrl.Hex0
