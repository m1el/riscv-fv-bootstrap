/-
  LowIR.CompileTests — differential tests: `Prog.exec` (the D7/D8 IL semantics)
  vs the SAME program compiled by `LowIR.Compile` and executed by the trusted
  `Rv64i.step` machine on actual encoded bytes.

  Convention: code at CODE, data buffer at DATA, stack top SPTOP (all far
  apart). Machine halt = CODE+4 (the pc after the entry stub's `jal` returns).
  Observables compared: the entry function's declared return registers
  (IL rets vs machine a0..), and — where a test writes memory — the data
  region byte-for-byte. IL runs with stackLo = 0 (the machine side has no
  overflow check in this cut; overflow behavior is IL-only, tested in
  Prog.lean). All checks are `native_decide` theorems (machine runs are too
  big for kernel `#guard`).
-/
import LowIR.Compile
import LowIR.ProgLib

namespace LowIR.CompileTests

open LowIR.Prog (Env FunDef Name Program)
open LowIR.Compile
open Rv64i (Word Byte)

def CODE  : Word := 0x10000
def DATA  : Word := 0x20000
def SPTOP : Word := 0x80000
def HALT  : Word := CODE + 4

/-- Initial machine: the full blob (code + const-data segment) at CODE,
    `args` in a0.., sp = SPTOP, `data` at DATA (everything else reads 0). -/
def machineOf (blob : List Byte) (args : List Word) (data : List Byte) :
    Rv64i.State :=
  { reg := fun i =>
      if i = 2 then SPTOP
      else if 10 ≤ i ∧ i < 10 + args.length then args.getD (i - 10) 0
      else 0
    pc  := CODE
    mem := LowIR.loadMem CODE blob DATA data }

/-- IL side: final callee state of `Prog.run`. -/
def ilFinal (P : Program) (entry : Name) (args : List Word) (data : List Byte)
    (fuel : Nat) : Option LowIR.Prog.St :=
  LowIR.Prog.run P 0 fuel entry args (LowIR.memOf DATA data) SPTOP

/-- Machine side: compile, load, run to HALT (`none` if compile fails or the
    machine doesn't reach the halt pc in `fuel`). -/
def mcFinal (P : Program) (entry : Name) (args : List Word) (data : List Byte)
    (fuel : Nat) : Option Rv64i.State := do
  let blob ← progBytes P entry
  let m := Rv64i.runFuel HALT fuel (machineOf blob args data)
  if m.pc = HALT then some m else none

/-- Compare the entry's declared returns: IL ret registers vs machine a0.. -/
def diffOk (P : Program) (entry : Name) (args : List Word) (data : List Byte := [])
    (ilFuel : Nat := 1000) (mcFuel : Nat := 100000) : Bool :=
  match List.lookup entry P.env,
        ilFinal P entry args data ilFuel, mcFinal P entry args data mcFuel with
  | some fd, some s, some m =>
      fd.rets.toList.map s.rget == (List.range fd.rvc).map fun j => m.rget (A j)
  | _, _, _ => false

/-- Compare the first `n` bytes of the data region as well. -/
def memDiffOk (n : Nat) (P : Program) (entry : Name) (args : List Word)
    (data : List Byte := []) (ilFuel : Nat := 1000) (mcFuel : Nat := 100000) : Bool :=
  match ilFinal P entry args data ilFuel, mcFinal P entry args data mcFuel with
  | some s, some m =>
      (List.range n).all fun k =>
        s.mem (DATA + BitVec.ofNat 64 k) == m.mem (DATA + BitVec.ofNat 64 k)
  | _, _ => false

/-! ### Test programs (beyond the fixtures exposed by `Prog`) -/

open LowIR.Prog (sub3 sumTo frameLocal caller early chainEnv recSum)

/-- Straight-line bit ops: `(((a ||| b) <<< 3) >>> 1) + 5`. -/
def bitops : FunDef :=
  { argc := 2, rvc := 1, params := #v[10, 11], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.orr 6 10 11) <|
            .seq (.slli 6 6 3) <|
            .seq (.srli 6 6 1) <|
            (.addi 10 6 5) }

/-- `memset(p, n, v)`: fill `mem[p..p+n)` with byte `v`, return p. Countdown
    cursor loop — exercises `sb` + while at both altitudes. -/
def memsetF : FunDef :=
  { argc := 3, rvc := 1, params := #v[10, 11, 12], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.addi 6 10 0) <|                   -- cursor := p
            .seq (.addi 7 11 0) <|                   -- left := n
            .seq (.addi 9 0 1) <|                    -- one := 1
            (.while .geu 7 9                          -- while left ≥u 1:
              (.seq (.sb 6 12 0) <|                   --   mem[cursor] := v
               .seq (.addi 6 6 1) <|                  --   cursor++
               (.addi 7 7 (-1 : BitVec 12)))) }       --   left--

/-- Sum of odd `i ≤ n` (n=10 → 1+3+5+7+9 = 25): while + ife + contL + shifts. -/
def sumOdd : FunDef :=
  { argc := 1, rvc := 1, params := #v[10], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.addi 6 0 0) <|                    -- acc := 0
            .seq (.addi 7 0 1) <|                    -- i := 1
            .seq (.while .geu 10 7                   -- while n ≥u i:
              (.seq (.srli 8 7 1) <|                 --   t := (i >>> 1) <<< 1
               .seq (.slli 8 8 1) <|
               .seq (.ife .eq 8 7                    --   if t = i (even):
                      (.seq (.addi 7 7 1) (.contL 0)) --     i++; continue
                      .skip) <|
               .seq (.add 6 6 7) <|                  --   acc += i
               (.addi 7 7 1))) <|                    --   i++
            (.addi 10 6 0) }                         -- ret := acc

/-- `find(p, key)`: index of first byte = key — an "infinite" while broken out
    of with `brkB` THROUGH the loop (loops transparent to break). -/
def findByte : FunDef :=
  { argc := 2, rvc := 1, params := #v[10, 11], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.addi 5 10 0) <|                   -- cursor := p
            .seq (.block
              (.while .geu 0 0                       -- while 0 ≥u 0 (forever):
                (.seq (.lbu 6 5 0) <|                --   b := mem[cursor]
                 .seq (.ife .eq 6 11 (.brkB 0) .skip) <|  -- if b = key: break
                 (.addi 5 5 1)))) <|                 --   cursor++
            (.sub 10 5 10) }                         -- ret := cursor - p

/-- Nested-block break: brkB 1 skips the tails of BOTH blocks (result 1). -/
def brkCascade : FunDef :=
  { argc := 0, rvc := 1, params := #v[], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.block
              (.seq (.block (.seq (.addi 10 0 1) (.seq (.brkB 1) (.addi 10 0 2))))
                    (.addi 10 0 3)))
            (.addi 11 0 0) }   -- (x11 noise so the block isn't the whole body)

/-- The differentially-testable env (Prog's fixtures minus the deliberately
    uncompilable `hog`, plus the ones above). -/
def denv : Env :=
  [("sub3", sub3), ("sumTo", sumTo), ("frameLocal", frameLocal),
   ("caller", caller), ("early", early), ("bitops", bitops),
   ("memset", memsetF), ("sumOdd", sumOdd), ("findByte", findByte),
   ("brkCascade", brkCascade)]

/-! ### Stage 2 — straight-line arithmetic -/

theorem diff_sub3   : diffOk denv "sub3" [30, 12, 2] = true := by native_decide
theorem diff_sub3'  : diffOk denv "sub3" [5, 0, 100] = true := by native_decide
theorem diff_bitops : diffOk denv "bitops" [0xF0, 0x0F] = true := by native_decide

-- encoder round-trip on the WHOLE compiled program (all emitted forms decode back)
theorem denv_roundtrip :
    ((compileProg denv "caller").getD [.unknown]).all
      (fun i => Rv64i.decode (LowIR.encode i) == i) = true := by native_decide

/-! ### Stage 3 — control flow -/

theorem diff_sumTo   : diffOk denv "sumTo" [10] = true := by native_decide
theorem diff_sumTo0  : diffOk denv "sumTo" [0] = true := by native_decide
theorem diff_early   : diffOk denv "early" [] = true := by native_decide
theorem diff_sumOdd  : diffOk denv "sumOdd" [10] = true := by native_decide
theorem diff_sumOdd1 : diffOk denv "sumOdd" [1] = true := by native_decide
theorem diff_brkCasc : diffOk denv "brkCascade" [] = true := by native_decide
theorem diff_find    : diffOk denv "findByte" [DATA, 0x43]
                         (data := [0x41, 0x42, 0x43, 0x44]) = true := by native_decide
theorem diff_memset  : memDiffOk 16 denv "memset" [DATA, 10, 0xAB] = true := by
  native_decide
theorem diff_memset0 : memDiffOk 16 denv "memset" [DATA, 0, 0xAB] = true := by
  native_decide

/-! ### Stage 4 — calls, frames, recursion -/

theorem diff_frameLocal : diffOk denv "frameLocal" [0xDEAD] = true := by native_decide
theorem diff_caller     : diffOk denv "caller" [5] = true := by native_decide
theorem diff_chain3     : diffOk chainEnv "f3" [40] = true := by native_decide
theorem diff_rec10      : diffOk recSum "rec" [10] (mcFuel := 200000) = true := by
  native_decide
theorem diff_rec0       : diffOk recSum "rec" [0] = true := by native_decide

-- sanity: the pipeline REFUSES what it must (hog's frame > imm12; missing entry)
#guard LowIR.Compile.compileProg LowIR.Prog.testEnv "sub3" = none  -- hog in env
#guard LowIR.Compile.compileProg denv "nosuch" = none

/-! ### Stage 4b — const data: `cref`/`clen` through the whole pipeline
    (data segment in the blob, jal-pc-read address materialization). -/

theorem diff_sumdata : diffOk LowIR.Prog.sumData "sumd" [] = true := by
  native_decide

-- refusal: data object too large for the fixed synth/cref range
#guard LowIR.Compile.compileProg
        { env := LowIR.Prog.sumData.env,
          data := [("tbl", List.replicate (2^23) 0)] } "sumd" = none

/-! ### Stage 5 — the library (`LowIR/ProgLib.lean`) through the compiler:
    strlen, strtoull, hex0, hex1 individually (inputs staged at DATA, hex
    outputs at DATA+64, compared byte-for-byte), and the `main` driver that
    stages everything in its own frame — 8 observables at once. -/

open LowIR.Prog.Lib (libProgram sbytes asBytes)

theorem diff_lib_strlen : diffOk libProgram "strlen" [DATA]
    (data := asBytes (sbytes "Hello, differential world!" ++ [0])) = true := by
  native_decide

theorem diff_lib_strtoull_ok : diffOk libProgram "strtoull" [DATA]
    (data := asBytes (sbytes "123456789x"))
    (ilFuel := 100000) = true := by native_decide

-- 2^64 exactly: saturates to ULLONG_MAX with errno ERANGE on BOTH altitudes
theorem diff_lib_strtoull_ovf : diffOk libProgram "strtoull" [DATA]
    (data := asBytes (sbytes "18446744073709551616"))
    (ilFuel := 100000) = true := by native_decide

/-- Args for a hex-decoder call: input at DATA (length computed from the
    string — no hand-counted lengths), output at DATA+64. -/
def hexArgs (s : String) (cap : Nat) : List Word :=
  [DATA, BitVec.ofNat 64 (sbytes s).length, DATA + 64, BitVec.ofNat 64 cap]

theorem diff_lib_hex0 : memDiffOk 80 libProgram "hex0"
    (hexArgs "48 65 6C 6C 6F" 8) (data := asBytes (sbytes "48 65 6C 6C 6F"))
    (ilFuel := 100000) = true := by native_decide

theorem diff_lib_hex0_err : diffOk libProgram "hex0"
    (hexArgs "4_2" 8) (data := asBytes (sbytes "4_2"))
    (ilFuel := 100000) = true := by native_decide

theorem diff_lib_hex1 : memDiffOk 80 libProgram "hex1"
    (hexArgs ":A 00 %A" 8) (data := asBytes (sbytes ":A 00 %A"))
    (ilFuel := 100000) = true := by native_decide

-- backward AND forward refs, comments, a '\n' label — the busy case
theorem diff_lib_hex1_fwd : memDiffOk 80 libProgram "hex1"
    (hexArgs "%B 41 :B 42 #x\n:\n 00 %\n" 16)
    (data := asBytes (sbytes "%B 41 :B 42 #x\n:\n 00 %\n"))
    (ilFuel := 100000) = true := by native_decide

theorem diff_lib_hex1_undef : memDiffOk 80 libProgram "hex1"
    (hexArgs "00 %Z" 8) (data := asBytes (sbytes "00 %Z"))
    (ilFuel := 100000) = true := by native_decide

theorem diff_lib_hex1_dup : diffOk libProgram "hex1"
    (hexArgs ":A 00 :A" 8) (data := asBytes (sbytes ":A 00 :A"))
    (ilFuel := 100000) = true := by native_decide

/-- The driver: stages all inputs in its own frame, calls strlen + strtoull +
    hex0 + hex1, returns 8 observables — IL and compiled-machine agree on all. -/
theorem diff_lib_main : diffOk libProgram "main" []
    (ilFuel := 200000) (mcFuel := 1000000) = true := by native_decide

/-- The const-slice driver: same 8 observables, inputs from the blob's data
    segment via cref/clen (jal-pc-read on the machine side). -/
theorem diff_lib_cmain : diffOk libProgram "cmain" []
    (ilFuel := 200000) (mcFuel := 1000000) = true := by native_decide

end LowIR.CompileTests
