/-
  Shared harness for running the real hex1 binary image through the model:
  loading bytes into memory, building an initial state, reading the output
  region. Used by Hex1/Validate.lean (executable diff-test) and
  Hex1/Certify.lean (native-checked certification theorems).

  Reuses Hex0's `Rv64i.Harness.loadBytes`/`readMem`; only `initOn` differs:
  core1 additionally takes a4 = label-table scratch (reg 14).
-/
import Hex0.Harness
import Hex1.Image
open Rv64i

namespace Rv64i.Harness1

/-- Initial machine state for core1: code + `inp` loaded, registers set per
    the calling convention (a0=in_ptr, a1=in_len, a2=out_ptr, a3=cap,
    a4=lbl_ptr, ra=0 sentinel), pc = core1 entry. The label table is NOT
    pre-initialized (core1 initializes it itself). -/
def initOn (inp : List Nat) (cap : Nat) : State :=
  { pc  := BitVec.ofNat 64 Image1.coreAddr
    mem := Harness.loadBytes Image1.inputAddr inp
             (Harness.loadBytes Image1.coreAddr Image1.coreBytes (fun _ => 0))
    reg := fun i =>
      if i = 1 then 0
      else if i = 10 then BitVec.ofNat 64 Image1.inputAddr
      else if i = 11 then BitVec.ofNat 64 inp.length
      else if i = 12 then BitVec.ofNat 64 Image1.outAddr
      else if i = 13 then BitVec.ofNat 64 cap
      else if i = 14 then BitVec.ofNat 64 Image1.lblAddr
      else 0 }

/-- Observable result of running the real core1 on `inp` with capacity `cap`,
    using `fuel` steps: (status, output bytes, out_len). -/
def observe (inp : List Nat) (cap fuel : Nat) : Nat × List Nat × Nat :=
  let f := runFuel 0 fuel (initOn inp cap)
  ((f.rget 10).toNat, Harness.readMem f.mem Image1.outAddr (f.rget 11).toNat,
   (f.rget 11).toNat)

end Rv64i.Harness1
