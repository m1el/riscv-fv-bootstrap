/-
  Concrete certification of the ACTUAL deployed hex1 binary against the spec.

  Complete, sorry-free theorems: the bytes of `core1` (extracted from
  bare/hex1.elf), executed by the RV64I model, produce EXACTLY what
  `coreSpec1` prescribes -- for the input embedded in the bare-metal image,
  and for a battery of inputs covering every status code and label-offset
  shape (forward/backward/adjacent references, duplicate labels, undefined
  references, exotic label bytes, capacity straddles).

  These use `native_decide` (same TCB note as Hex0/Certify.lean: trusts the
  Lean compiler + native toolchain; scoped to the concrete-input certification
  only -- the general refinement theorem uses no `native_decide`).
-/
import Hex1.Harness
import Hex1.Spec
open Rv64i Rv64i.Harness1

/-- Fuel covering every certification input (core1 takes ~5 + 256 init +
    ~10*|inp| steps; the embedded input is 267 bytes). -/
def FUEL : Nat := 40000

/-- The input physically embedded in the bare-metal image decodes to what the
    spec says. -/
theorem certify1_embedded :
    observe Image1.inputBytes 4096 FUEL = Hex1.coreSpec1 Image1.inputBytes 4096 := by
  native_decide

/-- And that value is exactly what QEMU printed (bare/run1.log):
    "Hello\n" ++ FC FF FF FF ++ 00 00 00 00. -/
theorem certify1_embedded_value :
    observe Image1.inputBytes 4096 FUEL =
      (0, [72, 101, 108, 108, 111, 10, 252, 255, 255, 255, 0, 0, 0, 0], 14) := by
  native_decide

/-- Battery 1/3: hex0-compatible statuses on hex1 (incl. the new stop chars). -/
theorem certify1_battery_hex0 :
    observe [] 4096 FUEL = Hex1.coreSpec1 [] 4096                                -- Ok, empty
  ∧ observe [65, 66] 4096 FUEL = Hex1.coreSpec1 [65, 66] 4096                    -- Ok, AB
  ∧ observe [65] 4096 FUEL = Hex1.coreSpec1 [65] 4096                            -- Trailing
  ∧ observe [65, 32] 4096 FUEL = Hex1.coreSpec1 [65, 32] 4096                    -- Split (space)
  ∧ observe [65, 58] 4096 FUEL = Hex1.coreSpec1 [65, 58] 4096                    -- Split (':')
  ∧ observe [65, 37] 4096 FUEL = Hex1.coreSpec1 [65, 37] 4096                    -- Split ('%')
  ∧ observe [65, 90] 4096 FUEL = Hex1.coreSpec1 [65, 90] 4096                    -- Unknown (low)
  ∧ observe [90] 4096 FUEL = Hex1.coreSpec1 [90] 4096                            -- Unknown (high)
  ∧ observe [65, 66, 67, 68] 1 FUEL = Hex1.coreSpec1 [65, 66, 67, 68] 1          -- OutputShort
  ∧ observe [35, 99, 10, 65, 66] 4096 FUEL = Hex1.coreSpec1 [35, 99, 10, 65, 66] 4096 := by
  native_decide

/-- Battery 2/3: label definitions and references (offset shapes). -/
theorem certify1_battery_labels :
    observe [58, 65, 32, 48, 48, 32, 37, 65] 4096 FUEL
      = Hex1.coreSpec1 [58, 65, 32, 48, 48, 32, 37, 65] 4096                     -- back ref
  ∧ observe [37, 65, 32, 58, 65] 4096 FUEL = Hex1.coreSpec1 [37, 65, 32, 58, 65] 4096 -- fwd ref
  ∧ observe [58, 65, 37, 65] 4096 FUEL = Hex1.coreSpec1 [58, 65, 37, 65] 4096    -- adjacent
  ∧ observe [37, 65, 37, 65, 58, 65] 4096 FUEL
      = Hex1.coreSpec1 [37, 65, 37, 65, 58, 65] 4096                             -- double fwd
  ∧ observe [58, 58, 32, 48, 48, 32, 37, 58] 4096 FUEL
      = Hex1.coreSpec1 [58, 58, 32, 48, 48, 32, 37, 58] 4096                     -- label ':'
  ∧ observe [58, 10, 32, 48, 48, 32, 37, 10] 4096 FUEL
      = Hex1.coreSpec1 [58, 10, 32, 48, 48, 32, 37, 10] 4096                     -- label '\n'
  ∧ observe [58, 0, 32, 48, 48, 32, 37, 0] 4096 FUEL
      = Hex1.coreSpec1 [58, 0, 32, 48, 48, 32, 37, 0] 4096                       -- label NUL
  ∧ observe [59, 58, 65, 10, 37, 65] 4096 FUEL
      = Hex1.coreSpec1 [59, 58, 65, 10, 37, 65] 4096 := by                       -- ':' in comment
  native_decide

/-- Battery 3/3: the new error classes and capacity interactions. -/
theorem certify1_battery_errors :
    observe [58, 65, 32, 58, 65] 4096 FUEL = Hex1.coreSpec1 [58, 65, 32, 58, 65] 4096 -- Dup
  ∧ observe [37, 90] 4096 FUEL = Hex1.coreSpec1 [37, 90] 4096                    -- Undef
  ∧ observe [48, 48, 32, 37, 90] 4096 FUEL = Hex1.coreSpec1 [48, 48, 32, 37, 90] 4096 -- Undef partial
  ∧ observe [37, 113, 32, 71] 4096 FUEL = Hex1.coreSpec1 [37, 113, 32, 71] 4096  -- Unknown beats Undef
  ∧ observe [58] 4096 FUEL = Hex1.coreSpec1 [58] 4096                            -- TrailTok ':'
  ∧ observe [37] 4096 FUEL = Hex1.coreSpec1 [37] 4096                            -- TrailTok '%'
  ∧ observe [37, 65, 32, 58, 65] 3 FUEL = Hex1.coreSpec1 [37, 65, 32, 58, 65] 3  -- field short
  ∧ observe [37, 65, 32, 58, 65] 4 FUEL = Hex1.coreSpec1 [37, 65, 32, 58, 65] 4  -- field exact
  ∧ observe [48, 48, 32, 37, 65, 32, 58, 65] 4 FUEL
      = Hex1.coreSpec1 [48, 48, 32, 37, 65, 32, 58, 65] 4 := by                  -- field straddle
  native_decide
