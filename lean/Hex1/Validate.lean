/-
  Executable validation: run the ACTUAL binary bytes of `core1` (extracted
  from bare/hex1.elf) through the Lean RV64I model and compare with
  `coreSpec1`. This corroborates that `decode` + `step` (including the
  SUB/SRLI/LD/SD added for hex1) faithfully model the hardware BEFORE we
  invest in the refinement proof.

  NOTE: this file uses the INTERPRETED evaluator (`#eval`), and core1's
  label-table initialization writes 2048 bytes through the closure-based
  memory, so each memory read pays ~3000 if-layers. Only SMALL inputs are
  checked here; the full battery (every status code, label shapes, the
  embedded 267-byte image input) is certified with `native_decide` in
  Hex1/Certify.lean, which compiles to native code and covers strictly more.

  (This exact setup caught a real bug: core1.s originally used `bltu`, which
  is not one of the 16 modelled encodings -- the model stuck at the first
  `bltu` while QEMU sailed through. core1.s now uses `blt`, valid under the
  documented cap < 2^63 precondition.)

  Run with:  lake env lean Hex1/Validate.lean   (~2 min, interpreted)
-/
import Hex1.Harness
import Hex1.Spec
open Rv64i Rv64i.Harness1

def runOn (inp : List Nat) (cap : Nat) : Nat × List Nat × Nat :=
  observe inp cap 20000

def specOn (inp : List Nat) (cap : Nat) : Nat × List Nat × Nat :=
  Hex1.coreSpec1 inp cap

-- (description, input bytes, capacity) — small inputs only; see header.
def battery : List (String × List Nat × Nat) :=
  [ ("empty",            [], 16),
    ("AB",               [65, 66], 16),
    ("back ref :A%A",    [58, 65, 37, 65], 16),
    ("fwd ref %A :A",    [37, 65, 32, 58, 65], 16),
    ("dup label",        [58, 65, 58, 65], 16),
    ("undef label",      [37, 90], 16),
    ("trailing colon",   [58], 16),
    ("split A colon",    [65, 58], 16),
    ("field short",      [37, 65, 58, 65], 3) ]

def diff : List (String × Bool) :=
  battery.map (fun (d, inp, cap) =>
    (d, decide (runOn inp cap = specOn inp cap)))

#eval diff                                  -- each should be (_, true)
#eval (decide (diff.all (·.2)) : Bool)      -- expect true: model == spec on ALL
