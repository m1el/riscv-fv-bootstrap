/-
  Shared harness for running the real binary image through the model:
  loading bytes into memory, building an initial state, reading the output
  region. Used by both Validate.lean (executable diff-test) and Certify.lean
  (kernel/native-checked certification theorems).
-/
import Hex0.Rv64i
import Hex0.Image
open Rv64i

namespace Rv64i.Harness

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

/-- Initial machine state: code + `inp` loaded, registers set per the calling
    convention (a0=in_ptr, a1=in_len, a2=out_ptr, a3=cap, ra=0 sentinel),
    pc = core entry. -/
def initOn (inp : List Nat) (cap : Nat) : State :=
  { pc  := BitVec.ofNat 64 Image.coreAddr
    mem := loadBytes Image.inputAddr inp (loadBytes Image.coreAddr Image.coreBytes (fun _ => 0))
    reg := fun i =>
      if i = 1 then 0
      else if i = 10 then BitVec.ofNat 64 Image.inputAddr
      else if i = 11 then BitVec.ofNat 64 inp.length
      else if i = 12 then BitVec.ofNat 64 Image.outAddr
      else if i = 13 then BitVec.ofNat 64 cap
      else 0 }

/-- Observable result of running the real core on `inp` with capacity `cap`,
    using `fuel` steps: (status, output bytes, out_len). -/
def observe (inp : List Nat) (cap fuel : Nat) : Nat × List Nat × Nat :=
  let f := runFuel 0 fuel (initOn inp cap)
  ((f.rget 10).toNat, readMem f.mem Image.outAddr (f.rget 11).toNat, (f.rget 11).toNat)

end Rv64i.Harness
