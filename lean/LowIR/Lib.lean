/-
  LowIR.Prog.Lib — the library rewritten on the D7/D8 IR, as real FUNCTIONS
  (params/rets/frames), plus a driver that stages every input in its OWN
  stack frame and calls all of them:

    strlen   (p)                     → (n)              port of Ctrl strlen
    strtoull (p)                     → (val, errno)     port of CtrlStrtoull2
                                                        (conformant: saturate +
                                                        ERANGE, keep scanning)
    hex0     (in, len, out, cap)     → (status, outlen) port of CtrlHex0
                                                        (flat ret-cascade)
    hex1     (in, len, out, cap)     → (status, outlen) NEW — from HEX1.md:
                                                        labels + rel32 refs,
                                                        two-phase scan/emit
    main     ()                      → 8 observables    stages all data in its
                                                        own frame, calls all 4

  hex1's label table is the D8 frame paying off: 256 entries × 4 bytes in its
  OWN frame (frameSize 1024), entry = (position+1) as little-endian u32, 0 =
  undefined — so no separate defined-bit array, full 256-value label bytes,
  and the whole thing fits the compiler's imm12 frame budget. The table is
  zeroed by 128 unrolled `sd frameReg, x0` (frame memory is NOT implicitly
  zero). Positions are exact for outputs < 2³²−1 bytes (spec needs < 2 GiB).

  Register conventions shared with the Ctrl versions: status=14, out_len=6,
  args in 10..13. Every function is validated at the IL level against its
  spec (`Hex0.coreSpec`, `Hex1.coreSpec1`, `strtoullConfSpec`); the compiled
  differential tests live in `LowIR/CompileTests.lean`.
-/
import LowIR.Prog
import LowIR.Hex0.Ctrl        -- Hex0.coreSpec (via Hex0.Spec) + the hex0 battery
import LowIR.Strtoull.V2   -- strtoullConfSpec + the strtoull battery
import Spec.Hex1.Spec             -- Hex1.coreSpec1

namespace LowIR.Prog.Lib

open Rv64i (Word Byte)

def seqs : List Stmt → Stmt := List.foldr .seq .skip
def lit (r v : Nat) : Stmt := .addi r 0 (BitVec.ofNat 12 v)

/-- Set status (x14) and return — the flat error cascade. -/
def err (code : Nat) : Stmt := .seq (lit 14 code) .ret

/-! ## strlen(p=10) → (n=12) -/

def strlenF : FunDef :=
  { argc := 1, rvc := 1, params := #v[10], rets := #v[12]
    frameSize := 0, frameReg := 3
    body := .seq (.addi 7 0 1) <| .seq (.addi 5 10 0) <| .seq (.lbu 6 5 0) <|
            .seq (.while .geu 6 7 (.seq (.addi 5 5 1) (.lbu 6 5 0)))
                 (.sub 12 5 10) }

/-! ## strtoull(p=10) → (val=12, errno=14) — conformant base-10
    (port of `LowIR.Ctrl.Strtoull2`, statement for statement). -/

def ovf   : Stmt := seqs [ .addi 12 0 (BitVec.ofNat 12 4095), lit 14 34 ]
def accum : Stmt := seqs [ .slli 29 12 3, .slli 30 12 1, .add 12 29 30, .add 12 12 28 ]

def cbody : Stmt := seqs
  [ .lbu 7 5 0,
    .ife .geu 7 20 (.ife .geu 7 22 (.brkB 0) .skip) (.brkB 0),
    .ife .eq 14 0
      (seqs
        [ .sub 28 7 20,
          .ife .geu 12 23
            (.ife .eq 12 23 (.ife .geu 28 24 ovf accum) ovf)
            accum ])
      .skip,
    .addi 5 5 1 ]

def thresholdBuild : List Stmt :=
  (List.replicate 15 [Stmt.slli 23 23 4, Stmt.addi 23 23 (BitVec.ofNat 12 9)]).flatten

def strtoullF : FunDef :=
  { argc := 1, rvc := 2, params := #v[10], rets := #v[12, 14]
    frameSize := 0, frameReg := 3
    body := seqs
      ([ lit 20 48, lit 22 58, lit 16 1, lit 24 6, lit 23 1 ]
        ++ thresholdBuild
        ++ [ .addi 12 0 0, .addi 14 0 0, .addi 5 10 0,
             .block (.while .lt 0 16 cbody) ]) }

/-! ## hex0(in=10, len=11, out=12, cap=13) → (status=14, outlen=6)
    (port of `LowIR.Ctrl.Hex0`, statement for statement). -/

def pnib (dst src : Reg) : Stmt :=
  .ife .geu src 20
    (.ife .geu 21 src (.sub dst src 20)
      (.ife .geu src 22 (.ife .geu 23 src (.sub dst src 17) (lit dst 255)) (lit dst 255)))
    (lit dst 255)

def readAdv (dst : Reg) : Stmt := seqs [.add 30 10 5, .lbu dst 30 0, .addi 5 5 1]

/-- Comment guard, scratch byte in `b`: g := (more input ∧ next ≠ '\n'). -/
def cgGuard (b : Reg) : Stmt :=
  .ife .lt 5 11
    (seqs [.add 30 10 5, .lbu b 30 0, .ife .eq b 24 (lit 15 0) (lit 15 1)])
    (lit 15 0)

def skipComment (b : Reg) : Stmt :=
  .seq (cgGuard b) (.while .geu 15 16 (.seq (.addi 5 5 1) (cgGuard b)))

def hexPath : Stmt :=
  seqs
    [ pnib 28 7,
      .ife .eq 28 19 (err 5) .skip,
      .ife .geu 5 11 (err 4) .skip,
      readAdv 7,
      .ife .eq 7 24 (err 3) .skip,
      .ife .eq 7 25 (err 3) .skip,
      .ife .eq 7 26 (err 3) .skip,
      .ife .eq 7 27 (err 3) .skip,
      .ife .eq 7 18 (err 3) .skip,
      pnib 29 7,
      .ife .eq 29 19 (err 5) .skip,
      .ife .geu 6 13 (err 2) .skip,
      .slli 31 28 4, .orr 31 31 29, .add 30 12 6, .sb 30 31 0, .addi 6 6 1 ]

def hex0Body : Stmt :=
  .seq (readAdv 7) <|
  .ife .eq 7 27 (skipComment 8) <|
  .ife .eq 7 18 (skipComment 8) <|
  .ife .eq 7 24 .skip <|
  .ife .eq 7 25 .skip <|
  .ife .eq 7 26 .skip <|
  hexPath

def hex0F : FunDef :=
  { argc := 4, rvc := 2, params := #v[10, 11, 12, 13], rets := #v[14, 6]
    frameSize := 0, frameReg := 3
    body := seqs
      [ lit 20 48, lit 21 57, lit 22 65, lit 23 70, lit 24 10, lit 25 32,
        lit 26 95, lit 27 35, lit 18 59, lit 19 255, lit 17 55, lit 16 1,
        lit 5 0, lit 6 0, lit 14 0,
        .while .lt 5 11 hex0Body ] }

/-! ## hex1(in=10, len=11, out=12, cap=13) → (status=14, outlen=6)

    Two phases per HEX1.md: scan (tokenize, capacity, label collection —
    reports the leftmost of Split/Trailing/Unknown/TrailTok/Dup/OutputShort,
    writes nothing, x6 stays 0), then emit (writes bytes, resolves refs;
    Undef rets with out_len = the failing field's position).

    Extra registers: 35 = phase-1 virtual output position; 9 = comment/entry
    scratch; frameReg 8 = the label table (256 × 4B, entry = pos+1, LE). -/

/-- Load the 4-byte LE table entry at address x30 into x9 (clobbers x31). -/
def ldEntry : Stmt := seqs
  [ .lbu 9 30 0,
    .lbu 31 30 1, .slli 31 31 8,  .orr 9 9 31,
    .lbu 31 30 2, .slli 31 31 16, .orr 9 9 31,
    .lbu 31 30 3, .slli 31 31 24, .orr 9 9 31 ]

/-- Store x31 as the 4-byte LE table entry at address x30 (clobbers x31). -/
def stEntry : Stmt := seqs
  [ .sb 30 31 0, .srli 31 31 8, .sb 30 31 1, .srli 31 31 8,
    .sb 30 31 2, .srli 31 31 8, .sb 30 31 3 ]

/-- x30 := table address of the label byte in x7. -/
def tblAddr : Stmt := .seq (.slli 31 7 2) (.add 30 8 31)

/-- `:c` in the scan: EOF → TrailTok; dup → Dup; else bind pos+1. -/
def colonScan : Stmt := seqs
  [ .ife .geu 5 11 (err 8) .skip,
    readAdv 7, tblAddr, ldEntry,
    .ife .geu 9 16 (err 6) .skip,
    .addi 31 35 1, stEntry ]

/-- `%c` in the scan: EOF → TrailTok; capacity (needs 4 bytes); pos += 4. -/
def pctScan : Stmt := seqs
  [ .ife .geu 5 11 (err 8) .skip,
    .addi 5 5 1,
    .addi 31 35 4,
    .ife .geu 13 31 .skip (err 2),
    .addi 35 35 4 ]

/-- `<BYTE>` in the scan — hex0's cascade with the two extra stop chars
    (':' '%') and the capacity check on the virtual position x35. -/
def hexScan : Stmt := seqs
  [ pnib 28 7,
    .ife .eq 28 19 (err 5) .skip,
    .ife .geu 5 11 (err 4) .skip,
    readAdv 7,
    .ife .eq 7 24 (err 3) .skip,
    .ife .eq 7 25 (err 3) .skip,
    .ife .eq 7 26 (err 3) .skip,
    .ife .eq 7 27 (err 3) .skip,
    .ife .eq 7 18 (err 3) .skip,
    .ife .eq 7 32 (err 3) .skip,
    .ife .eq 7 33 (err 3) .skip,
    pnib 29 7,
    .ife .eq 29 19 (err 5) .skip,
    .ife .geu 35 13 (err 2) .skip,
    .addi 35 35 1 ]

def scanBody : Stmt :=
  .seq (readAdv 7) <|
  .ife .eq 7 27 (skipComment 9) <|
  .ife .eq 7 18 (skipComment 9) <|
  .ife .eq 7 24 .skip <|
  .ife .eq 7 25 .skip <|
  .ife .eq 7 26 .skip <|
  .ife .eq 7 32 colonScan <|
  .ife .eq 7 33 pctScan <|
  hexScan

/-- `%c` in the emit: resolve or Undef (x6 = field_pos stays as out_len);
    field value = (pos+1) − 1 − (field_pos + 4) in u64 = rel32 two's
    complement in the low 4 bytes, written LE. -/
def pctEmit : Stmt := seqs
  [ readAdv 7, tblAddr, ldEntry,
    .ife .geu 9 16 .skip (err 7),
    .sub 9 9 16,
    .addi 31 6 4, .sub 9 9 31,
    .add 30 12 6,
    .sb 30 9 0, .srli 9 9 8, .sb 30 9 1, .srli 9 9 8,
    .sb 30 9 2, .srli 9 9 8, .sb 30 9 3,
    .addi 6 6 4 ]

/-- `<BYTE>` in the emit — no guards (the scan validated everything). -/
def hexEmit : Stmt := seqs
  [ pnib 28 7, readAdv 7, pnib 29 7,
    .slli 31 28 4, .orr 31 31 29, .add 30 12 6, .sb 30 31 0, .addi 6 6 1 ]

def emitBody : Stmt :=
  .seq (readAdv 7) <|
  .ife .eq 7 27 (skipComment 9) <|
  .ife .eq 7 18 (skipComment 9) <|
  .ife .eq 7 24 .skip <|
  .ife .eq 7 25 .skip <|
  .ife .eq 7 26 .skip <|
  .ife .eq 7 32 (.addi 5 5 1) <|
  .ife .eq 7 33 pctEmit <|
  hexEmit

/-- Zero the label table: 128 unrolled 8-byte stores over the 1024-byte frame. -/
def zeroTable : List Stmt :=
  (List.range 128).map fun i => Stmt.sd 8 0 (BitVec.ofNat 12 (8 * i))

def hex1F : FunDef :=
  { argc := 4, rvc := 2, params := #v[10, 11, 12, 13], rets := #v[14, 6]
    frameSize := 1024, frameReg := 8
    body := seqs
      ([ lit 20 48, lit 21 57, lit 22 65, lit 23 70, lit 24 10, lit 25 32,
         lit 26 95, lit 27 35, lit 18 59, lit 19 255, lit 17 55, lit 16 1,
         lit 32 58, lit 33 37,
         lit 14 0, lit 6 0, lit 35 0, lit 5 0 ]
        ++ zeroTable
        ++ [ .while .lt 5 11 scanBody,
             lit 5 0,
             .while .lt 5 11 emitBody ]) }

/-! ## main() — stages all inputs in its OWN frame, calls all four.

    Frame (96 bytes): 0 "Hi!\0" · 8 "123456789\0" · 32 hex0 input
    "48 65 6C 6C 6F" (14 ch) · 48 hex0 out (cap 8) · 64 hex1 input
    ":A 00 %A" (8 ch) · 80 hex1 out (cap 8).

    Returns 8 observables: (strlen_n, strtoull_val, strtoull_errno,
    hex0_status, hex0_len, hex1_status, hex1_len, checksum) where checksum =
    the two output buffers read back as 64-bit words, added. -/

def sbytes (s : String) : List Nat := s.toList.map Char.toNat

/-- Store `bytes` into the frame at `off` (x7 scratch, x8 = frame base). -/
def stageBytes (off : Nat) (bytes : List Nat) : List Stmt :=
  (bytes.zipIdx.map fun bi =>
    [lit 7 bi.1, Stmt.sb 8 7 (BitVec.ofNat 12 (off + bi.2))]).flatten

def mainF : FunDef :=
  { argc := 0, rvc := 8, params := #v[], rets := #v[21, 22, 23, 24, 25, 26, 27, 28]
    frameSize := 96, frameReg := 8
    body := seqs
      (stageBytes 0  (sbytes "Hi!" ++ [0])
       ++ stageBytes 8  (sbytes "123456789" ++ [0])
       ++ stageBytes 32 (sbytes "48 65 6C 6C 6F")
       ++ stageBytes 64 (sbytes ":A 00 %A")
       ++ [ .addi 20 8 0,
            .call 1 1 "strlen" #v[20] #v[21],
            .addi 20 8 8,
            .call 1 2 "strtoull" #v[20] #v[22, 23],
            .addi 16 8 32, lit 17 14, .addi 18 8 48, lit 19 8,
            .call 4 2 "hex0" #v[16, 17, 18, 19] #v[24, 25],
            .addi 16 8 64, lit 17 8, .addi 18 8 80, lit 19 8,
            .call 4 2 "hex1" #v[16, 17, 18, 19] #v[26, 27],
            .ld 28 8 48, .ld 29 8 80, .add 28 28 29 ]) }

/-- The same driver on CONST SLICES: every input comes from the data segment
    via `cref`/`clen` (no byte-by-byte staging); the frame only holds the two
    output buffers (16 bytes). Same 8 observables as `main`. -/
def cmainF : FunDef :=
  { argc := 0, rvc := 8, params := #v[], rets := #v[21, 22, 23, 24, 25, 26, 27, 28]
    frameSize := 16, frameReg := 8
    body := seqs
      [ .cref 20 "hi",
        .call 1 1 "strlen" #v[20] #v[21],
        .cref 20 "num",
        .call 1 2 "strtoull" #v[20] #v[22, 23],
        .cref 16 "hex0src", .clen 17 "hex0src", .addi 18 8 0, lit 19 8,
        .call 4 2 "hex0" #v[16, 17, 18, 19] #v[24, 25],
        .cref 16 "hex1src", .clen 17 "hex1src", .addi 18 8 8, lit 19 8,
        .call 4 2 "hex1" #v[16, 17, 18, 19] #v[26, 27],
        .ld 28 8 0, .ld 29 8 8, .add 28 28 29 ] }

def libEnv : Env :=
  [("strlen", strlenF), ("strtoull", strtoullF), ("hex0", hex0F),
   ("hex1", hex1F), ("main", mainF), ("cmain", cmainF)]

def libData : Data :=
  [("hi",      ((sbytes "Hi!" ++ [0]).map (BitVec.ofNat 8))),
   ("num",     ((sbytes "123456789" ++ [0]).map (BitVec.ofNat 8))),
   ("hex0src", ((sbytes "48 65 6C 6C 6F").map (BitVec.ofNat 8))),
   ("hex1src", ((sbytes ":A 00 %A").map (BitVec.ofNat 8)))]

/-- The whole library as a Program (functions + rodata). -/
def libProgram : Program := { env := libEnv, data := libData }

#guard wfProgram libProgram

/-! ## IL-level validation against the specs -/

def inBase  : Word := 0x1000
def outBase : Word := 0x4000
def SP0     : Word := 0x80000

def memIn (inp : List Byte) : Word → Byte := fun a =>
  let ia := (a - inBase).toNat
  if ia < inp.length then (inp[ia]?).getD 0 else 0

def asBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)

/-- Run a hex-decoder from the library env; result (status, out bytes, len). -/
def hexRun (f : Name) (inp : List Nat) (cap fuel : Nat) : Nat × List Nat × Nat :=
  match run libProgram 0 fuel f
          [inBase, BitVec.ofNat 64 inp.length, outBase, BitVec.ofNat 64 cap]
          (memIn (asBytes inp)) SP0 with
  | some s => ((s.rget 14).toNat,
               (List.range (s.rget 6).toNat).map
                 (fun i => (s.mem (outBase + BitVec.ofNat 64 i)).toNat),
               (s.rget 6).toNat)
  | none   => (255, [], 0)

/-- hex0-as-a-function matches `Hex0.coreSpec` on the hex0 battery. -/
theorem hex0F_matches_spec :
    LowIR.Ctrl.Hex0.battery.all (fun tc =>
      hexRun "hex0" tc.1 tc.2 100000 == Hex0.coreSpec tc.1 tc.2) = true := by
  native_decide

def hex1Battery : List (List Nat × Nat) :=
  [ (sbytes "%A :A", 16), (sbytes ":A 00 %A", 16), (sbytes ":A%A", 16),
    (sbytes ":A 00 :A", 16),                      -- Dup
    (sbytes "%Z", 16),                            -- Undef (field 0)
    (sbytes "00 %Z", 16),                         -- Undef after a byte (len 1)
    (sbytes ":A 00 %A %B", 16),                   -- Undef at the 2nd field (len 5)
    (sbytes "4:", 16), (sbytes "4%", 16),         -- Split (new stop chars)
    (sbytes ":", 16), (sbytes "%", 16),           -- TrailTok
    (sbytes ":: 00 %:", 16),                      -- label byte ':'
    (sbytes ":\n 00 %\n", 16),                    -- label byte '\n'
    (sbytes "44", 16), (sbytes "4", 16), (sbytes "4G", 16), (sbytes "G", 16),
    (sbytes "48 65 6C", 2),                       -- OutputShort at a byte
    (sbytes "%A :A", 3),                          -- OutputShort at a ref
    (sbytes "%A :A", 4),                          -- exactly fits
    (sbytes "# c :X %X\n41", 16),                 -- ':'/'%' inert in comments
    (sbytes ";x\n:Q 41_42 %Q", 16),
    ([], 16), (sbytes "  \n_", 16) ]

/-- hex1 matches `Hex1.coreSpec1` on the battery. -/
theorem hex1F_matches_spec :
    hex1Battery.all (fun tc =>
      hexRun "hex1" tc.1 tc.2 100000 == Hex1.coreSpec1 tc.1 tc.2) = true := by
  native_decide

/-- Restricted to label-free inputs, hex1 ≡ hex0 (the HEX1.md promise), on
    hex0's whole battery — except the documented Split-vs-Unknown reclass. -/
theorem hex1F_extends_hex0 :
    LowIR.Ctrl.Hex0.battery.all (fun tc =>
      hexRun "hex1" tc.1 tc.2 100000 == Hex1.coreSpec1 tc.1 tc.2) = true := by
  native_decide

/-- strtoull-as-a-function matches the conformant spec on its battery. -/
theorem strtoullF_matches_spec :
    LowIR.Ctrl.Strtoull2.battery.all (fun inp =>
      (match run libProgram 0 100000 "strtoull" [inBase] (memIn (asBytes inp)) SP0 with
       | some s => (s.rget 12, (s.rget 14).toNat)
       | none   => (0xDEAD, 0))
      == LowIR.Ctrl.Strtoull2.strtoullConfSpec (asBytes inp)) = true := by
  native_decide

/-- strlen over a few strings. -/
theorem strlenF_ok :
    [("", 0), ("x", 1), ("Hello", 5), ("Hi!", 3)].all (fun tc =>
      (match run libProgram 0 1000 "strlen" [inBase]
               (memIn (asBytes (sbytes tc.1 ++ [0]))) SP0 with
       | some s => (s.rget 12).toNat
       | none   => 999)
      == tc.2) = true := by
  native_decide

/-- The driver end-to-end at the IL level: every observable as expected.
    checksum = the "Hello" buffer word + the hex1 output word
    ([00 FB FF FF FF] LE, zero-padded). -/
theorem main_il_ok :
    (run libProgram 0 100000 "main" [] (fun _ => 0) SP0).map
      (fun s => mainF.rets.toList.map s.rget)
    = some [3, 123456789, 0, 0, 5, 0, 5,
            (0x0000006F6C6C6548 : Word) + 0x000000FFFFFFFB00] := by
  native_decide

/-- The const-slice driver produces the SAME observables — inputs read from
    the data segment instead of being staged byte-by-byte into the frame. -/
theorem cmain_il_ok :
    (run libProgram 0 100000 "cmain" [] (fun _ => 0) SP0).map
      (fun s => cmainF.rets.toList.map s.rget)
    = some [3, 123456789, 0, 0, 5, 0, 5,
            (0x0000006F6C6C6548 : Word) + 0x000000FFFFFFFB00] := by
  native_decide

end LowIR.Prog.Lib
