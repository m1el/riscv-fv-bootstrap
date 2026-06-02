/-
  Executable validation: run the ACTUAL binary bytes of `core` (extracted from
  bare/hex0.elf) through the Lean RV64I model, and check the model reproduces
  what QEMU produced ("Hello\n", status 0). This corroborates that `decode` +
  `step` faithfully model the hardware, BEFORE we invest in the refinement proof.

  Run with:  lake env lean Hex0/Validate.lean
-/
import Hex0.Rv64i
import Hex0.Image
import Hex0.Spec
open Rv64i Rv64i.Image

/-- Write `bytes` starting at address `base` into memory function `m`. -/
def loadBytes (base : Nat) (bytes : List Nat) (m : Word → Byte) : Word → Byte :=
  bytes.foldl (init := (m, 0))
    (fun (acc : (Word → Byte) × Nat) b =>
      let (mm, i) := acc
      let a : Word := BitVec.ofNat 64 (base + i)
      (fun x => if x = a then BitVec.ofNat 8 b else mm x, i + 1))
    |>.1

def readMem (m : Word → Byte) (base len : Nat) : List Nat :=
  (List.range len).map (fun i => (m (BitVec.ofNat 64 (base + i))).toNat)

-- registers: x1=ra x10=a0 x11=a1 x12=a2 x13=a3
def initState : State :=
  let m0 : Word → Byte := fun _ => 0
  let m1 := loadBytes coreAddr coreBytes m0
  let m2 := loadBytes inputAddr inputBytes m1
  { pc  := BitVec.ofNat 64 coreAddr
    mem := m2
    reg := fun i =>
      if i = 1  then 0                                   -- ra = 0 (sentinel)
      else if i = 10 then BitVec.ofNat 64 inputAddr      -- a0 = in_ptr
      else if i = 11 then BitVec.ofNat 64 inputLen       -- a1 = in_len
      else if i = 12 then BitVec.ofNat 64 outAddr        -- a2 = out_ptr
      else if i = 13 then 4096                           -- a3 = out_cap
      else 0 }

def final : State := runUntil 0 initState

def modelStatus : Nat := (final.rget 10).toNat
def modelOutLen : Nat := (final.rget 11).toNat
def modelOut    : List Nat := readMem final.mem outAddr modelOutLen

-- What the SPEC says for the same input + capacity:
def specResult : Nat × List Nat × Nat := Hex0.coreSpec inputBytes 4096

#eval modelStatus           -- expect 0
#eval modelOutLen           -- expect 6
#eval modelOut              -- expect [72,101,108,108,111,10] = "Hello\n"
#eval specResult            -- expect (0, [72,...,10], 6)
#eval (String.mk (modelOut.map (fun n => Char.ofNat n)))  -- expect "Hello\n"

-- The headline check: model agrees with spec on the real binary.
#eval (decide (modelStatus = (specResult.1) ∧
               modelOutLen = specResult.2.2 ∧
               modelOut   = specResult.2.1) : Bool)        -- expect true

/-! ## Differential test battery: run the real `core` bytes on many inputs,
    each compared against `coreSpec`. Exercises every error path. -/

def runOn (inp : List Nat) (cap : Nat) : Nat × List Nat × Nat :=
  let m := loadBytes inputAddr inp (loadBytes coreAddr coreBytes (fun _ => 0))
  let s0 : State :=
    { pc := BitVec.ofNat 64 coreAddr, mem := m
      reg := fun i =>
        if i = 1 then 0
        else if i = 10 then BitVec.ofNat 64 inputAddr
        else if i = 11 then BitVec.ofNat 64 inp.length
        else if i = 12 then BitVec.ofNat 64 outAddr
        else if i = 13 then BitVec.ofNat 64 cap
        else 0 }
  let f := runUntil 0 s0
  ((f.rget 10).toNat, readMem f.mem outAddr (f.rget 11).toNat, (f.rget 11).toNat)

def specOn (inp : List Nat) (cap : Nat) : Nat × List Nat × Nat :=
  let (st, bs, ln) := Hex0.coreSpec inp cap
  (st, bs, ln)

-- (description, input bytes, capacity)
def battery : List (String × List Nat × Nat) :=
  [ ("empty",            [], 4096),
    ("AB",               [65,66], 4096),
    ("trailing A",       [65], 4096),
    ("split A space",    [65,32], 4096),
    ("unknown AZ",       [65,90], 4096),
    ("unknown Z",        [90], 4096),
    ("output short",     [65,66,67,68], 1),
    ("comment",          [35,99,10,65,66], 4096),
    ("underscores 41_42",[52,49,95,52,50], 4096),
    ("lowercase ab",     [97,98], 4096),
    ("0 then a",         [48,97], 4096),
    ("semicolon cmt EOF",[59,120,121], 4096),
    ("two bytes FFaa",   [70,70,65,65], 4096) ]

def diff : List (String × Bool) :=
  battery.map (fun (d, inp, cap) =>
    (d, decide (runOn inp cap = specOn inp cap)))

#eval diff                                  -- each should be (_, true)
#eval (decide (diff.all (·.2)) : Bool)      -- expect true: model == spec on ALL
