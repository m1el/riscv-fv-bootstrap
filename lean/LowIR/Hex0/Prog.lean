/-
  hex0 written in LowIR — the `unhex` decoder of `hex0.c` (lines 81–123), at the
  structured altitude, compiled to RV64I by `LowIR.compile`, and certified against
  the existing functional spec `Hex0.coreSpec` on a battery of inputs.

  This shows the IL scales past `strlen` to the repo's flagship program, and that
  the *same* `compile` pipeline reproduces hex0's behaviour on the trusted machine.

  Calling convention (this program's own):
    x10 = in_ptr   x11 = in_len   x12 = out_ptr   x13 = out_cap
  Result:
    x14 = status (0 Ok · 2 OutputShort · 3 Split · 4 Trailing · 5 Unknown)
    x6  = out_len  (and out_ptr[0..out_len) holds the decoded bytes)

  "Early return" on error is encoded structurally: set the status reg and force
  `in_idx := in_len`, so the main `while in_idx < in_len` exits and no later branch
  runs (every error leaf is the last statement executed on its path).
-/
import LowIR.Core
import Spec.Hex0.Spec

namespace LowIR.Hex0Prog

open LowIR
open Rv64i (Byte Word)

/-! ### Register assignment -/
-- data:  in_ptr=10 in_len=11 out_ptr=12 out_cap=13
-- work:  in_idx=5 out_idx=6 chr=7 hi=28 lo=29 addr=30 tmp=31 b=8 g=15 status=14
-- const: '0'=20(48) '9'=21(57) 'A'=22(65) 'F'=23(70) nl=24(10) sp=25(32)
--        us=26(95) '#'=27(35) ';'=18(59) bad=19(255) off=17(55) one=16(1)

private def lit (r v : Nat) : Stmt := .addi r 0 (BitVec.ofNat 12 v)
private def seqs : List Stmt → Stmt := List.foldr .seq .skip

/-- `dst := parse_nibble(src)` (255 sentinel for non-hex), inlined. -/
def pnib (dst src : Reg) : Stmt :=
  .ife .ge src 20                              -- src >= '0'
    (.ife .ge 21 src (.sub dst src 20)         -- src <= '9' → src - 48
      (.ife .ge src 22                         -- src >= 'A'
        (.ife .ge 23 src (.sub dst src 17)     -- src <= 'F' → src - 55
          (lit dst 255))
        (lit dst 255)))
    (lit dst 255)

/-- `dst := mem[in_ptr + in_idx]; in_idx += 1`. -/
def readAdv (dst : Reg) : Stmt :=
  seqs [.add 30 10 5, .lbu dst 30 0, .addi 5 5 1]

/-- error exit: `status := code; in_idx := in_len` (forces the main loop to stop). -/
def err (code : Nat) : Stmt := seqs [lit 14 code, .addi 5 11 0]

/-- guard `g := (in_idx < in_len) && (mem[in_ptr+in_idx] != '\n')`. -/
def cgGuard : Stmt :=
  .ife .lt 5 11
    (seqs [.add 30 10 5, .lbu 8 30 0,
           .ife .eq 8 24 (lit 15 0) (lit 15 1)])
    (lit 15 0)

/-- skip a `#`/`;` comment: advance to (not past) the next newline or EOF. -/
def skipComment : Stmt :=
  .seq cgGuard (.while .geu 15 16 (.seq (.addi 5 5 1) cgGuard))

/-- one iteration of the main loop (precondition: in_idx < in_len). -/
def body : Stmt :=
  .seq (readAdv 7) <|                            -- chr := in[in_idx++]
  .ife .eq 7 27 skipComment <|                   -- '#'  → skip comment
  .ife .eq 7 18 skipComment <|                   -- ';'  → skip comment
  .ife .eq 7 24 .skip <|                          -- '\n' → continue
  .ife .eq 7 25 .skip <|                          -- ' '  → continue
  .ife .eq 7 26 .skip <|                           -- '_'  → continue
    .seq (pnib 28 7) <|                           -- hi := nibble(chr)
    .ife .eq 28 19 (err 5) <|                     -- bad high  → Unknown
    .ife .ge 5 11 (err 4) <|                      -- no low    → Trailing
      .seq (readAdv 7) <|                          -- chr := in[in_idx++]
      .ife .eq 7 24 (err 3) <|                     -- low-stop chars → Split
      .ife .eq 7 25 (err 3) <|
      .ife .eq 7 26 (err 3) <|
      .ife .eq 7 27 (err 3) <|
      .ife .eq 7 18 (err 3) <|
        .seq (pnib 29 7) <|                        -- lo := nibble(chr)
        .ife .eq 29 19 (err 5) <|                  -- bad low → Unknown
        .ife .ge 6 13 (err 2) <|                   -- out full → OutputShort
          seqs [ .slli 31 28 4,                    -- tmp := hi<<4
                 .orr 31 31 29,                    -- tmp := tmp | lo
                 .add 30 12 6,                      -- addr := out_ptr+out_idx
                 .sb 30 31 0,                        -- out[out_idx] := tmp
                 .addi 6 6 1 ]                       -- out_idx += 1

/-- The whole decoder. -/
def hex0 : Stmt :=
  seqs
    [ lit 20 48, lit 21 57, lit 22 65, lit 23 70, lit 24 10, lit 25 32,
      lit 26 95, lit 27 35, lit 18 59, lit 19 255, lit 17 55, lit 16 1,
      lit 5 0, lit 6 0, lit 14 0,                  -- in_idx=0 out_idx=0 status=Ok
      .while .lt 5 11 body ]

/-! ### Harness: assemble + run on the trusted `Rv64i`, extract (status, out, len). -/

def codeBase : Word := 0x80000000
def inBase   : Word := 0x1000
def outBase  : Word := 0x4000

def memHex0 (code : List Byte) (inp : List Byte) : Word → Byte :=
  fun a =>
    let ca := (a - codeBase).toNat
    if ca < code.length then (code[ca]?).getD 0
    else
      let ia := (a - inBase).toNat
      if ia < inp.length then (inp[ia]?).getD 0
      else 0

def hex0State (inp : List Byte) (cap : Nat) : Rv64i.State :=
  { reg := fun i =>
      if i = 10 then inBase
      else if i = 11 then BitVec.ofNat 64 inp.length
      else if i = 12 then outBase
      else if i = 13 then BitVec.ofNat 64 cap
      else 0
    pc  := codeBase
    mem := memHex0 (asmBytes (compile hex0)) inp }

/-- Run compiled hex0 on the trusted machine; return (status, output bytes, len). -/
def hex0Run (inp : List Byte) (cap fuel : Nat) : Nat × List Nat × Nat :=
  let halt := codeBase + BitVec.ofNat 64 (4 * (compile hex0).length)
  let s := Rv64i.runFuel halt fuel (hex0State inp cap)
  let status := (s.rget 14).toNat
  let outlen := (s.rget 6).toNat
  let out := (List.range outlen).map (fun i => (s.mem (outBase + BitVec.ofNat 64 i)).toNat)
  (status, out, outlen)

/-! ### Certification battery — `hex0Run` agrees with `Hex0.coreSpec`. -/

/-- A test case: (input bytes, capacity). -/
abbrev TC := List Nat × Nat

def asBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)

/-- Char-code helpers for readability. -/
private def H0 : List Nat := [0x34, 0x31]                 -- "41"
private def battery : List TC :=
  [ ([], 16),                                              -- Ok, empty
    ([0x34,0x31], 16),                                     -- "41" → 0x41
    ([0x34,0x31,0x34,0x32], 16),                           -- "4142" → 0x41 0x42
    ([0x34,0x31,0x5F,0x34,0x32], 16),                      -- "41_42" (underscore sep)
    ([0x34,0x31,0x0A,0x34,0x32], 16),                      -- "41\n42"
    ([0x34,0x31], 1),                                      -- cap 1: Ok one byte
    ([0x34,0x31,0x34,0x32], 1),                            -- cap 1: OutputShort
    ([0x34,0x31,0x34,0x32], 0),                            -- cap 0: OutputShort, 0 bytes
    ([0x34], 16),                                          -- "4" → Trailing
    ([0x34,0x20], 16),                                     -- "4 " → Split (space low)
    ([0x34,0x3B], 16),                                     -- "4;" → Split (semi low)
    ([0x47], 16),                                          -- "G" → Unknown (high)
    ([0x34,0x47], 16),                                     -- "4G" → Unknown (low)
    ([0x23,0x68,0x69,0x0A,0x34,0x31], 16),                 -- "#hi\n41" → 0x41
    ([0x3B,0x78,0x0A,0x41,0x46], 16),                      -- ";x\nAF" → 0xAF
    ([0x23,0x6E,0x6F,0x6E,0x65], 16),                      -- "#none" comment to EOF → Ok
    ([0x41,0x42,0x43,0x44], 16) ]                          -- "ABCD" → 0xAB 0xCD

/-- Every battery case: the compiled hex0 on the trusted machine equals the spec. -/
theorem hex0_matches_spec :
    battery.all (fun (tc : TC) =>
      hex0Run (asBytes tc.1) tc.2 5000 == Hex0.coreSpec tc.1 tc.2) = true := by
  native_decide

end LowIR.Hex0Prog
