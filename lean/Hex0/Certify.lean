/-
  Concrete certification of the ACTUAL deployed binary against the spec.

  Complete, sorry-free theorems: the bytes of `core` (extracted from
  bare/hex0.elf), executed by the RV64I model, produce EXACTLY what `coreSpec`
  prescribes -- for the input embedded in the bare-metal image, and for a
  battery of inputs covering every error class.

  These use `native_decide`: the spec's `decode` is well-founded recursive and
  does not reduce in the kernel, so we evaluate both sides via Lean's compiler.
  TCB NOTE: `native_decide` trusts the Lean compiler + native toolchain. This is
  a deliberate, scoped trust choice for the *concrete-input* certification only.
  The GENERAL refinement theorem (Refine.lean) uses no `native_decide`.

  This is weaker than the general refinement (all inputs) but is a fully checked
  statement about the exact artifact that runs in QEMU.
-/
import Hex0.Harness
import Hex0.Spec
open Rv64i

/-- The input physically embedded in the bare-metal image decodes to "Hello\n". -/
theorem certify_embedded :
    Harness.observe Image.inputBytes 4096 1000
      = Hex0.coreSpec Image.inputBytes 4096 := by
  native_decide

/-- And that value is exactly ("Hello\n", Ok). -/
theorem certify_embedded_value :
    Harness.observe Image.inputBytes 4096 1000 = (0, [72, 101, 108, 108, 111, 10], 6) := by
  native_decide

/-- Battery covering every error class: the real binary matches `coreSpec`. -/
theorem certify_battery :
    Harness.observe [] 4096  1000              = Hex0.coreSpec [] 4096                 -- Ok, empty
  ∧ Harness.observe [65, 66] 4096  1000       = Hex0.coreSpec [65, 66] 4096           -- Ok, AB->0xAB
  ∧ Harness.observe [65] 4096  1000           = Hex0.coreSpec [65] 4096               -- Trailing
  ∧ Harness.observe [65, 32] 4096  1000       = Hex0.coreSpec [65, 32] 4096           -- Split
  ∧ Harness.observe [65, 90] 4096  1000       = Hex0.coreSpec [65, 90] 4096           -- Unknown (low)
  ∧ Harness.observe [90] 4096  1000           = Hex0.coreSpec [90] 4096               -- Unknown (high)
  ∧ Harness.observe [65, 66, 67, 68] 1  1000  = Hex0.coreSpec [65, 66, 67, 68] 1      -- OutputShort
  ∧ Harness.observe [35, 99, 10, 65, 66] 4096 1000 = Hex0.coreSpec [35, 99, 10, 65, 66] 4096 -- comment
  ∧ Harness.observe [52, 49, 95, 52, 50] 4096 1000 = Hex0.coreSpec [52, 49, 95, 52, 50] 4096 -- '_' spacing
  ∧ Harness.observe [97, 98] 4096  1000       = Hex0.coreSpec [97, 98] 4096           -- lowercase reject
  ∧ Harness.observe [48, 97] 4096  1000       = Hex0.coreSpec [48, 97] 4096           -- 0 then lowercase
  ∧ Harness.observe [59, 120, 121] 4096  1000 = Hex0.coreSpec [59, 120, 121] 4096     -- ';' comment to EOF
  ∧ Harness.observe [70, 70, 65, 65] 4096 1000 = Hex0.coreSpec [70, 70, 65, 65] 4096 := by -- FF AA
  native_decide
