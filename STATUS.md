# Status — verified hex0 on bare-metal RISC-V

Goal: run hex0 on bare-metal `qemu-system-riscv` **and** have a formal proof
(in both Lean and Coq) that the bytes that run implement the hex0 spec.

## What is done (and its strength)

| # | Deliverable | Strength |
|---|---|---|
| 1 | hex0 runs bare-metal on `qemu-system-riscv64 -M virt`; decodes embedded input to `Hello\n`, verified byte-for-byte | concrete, runs |
| 2 | Shared `decode` spec in **Lean + Coq**, computing identically on a battery | spec, cross-checked |
| 3 | Hand-rolled **executable RV64I** model in **Lean + Coq** (the 12 instr forms `core` uses) | model |
| 4 | Both models execute the **real binary** and match `coreSpec` (13-input differential battery, all error classes) | testing-grade, cross-validated vs QEMU |
| 5 | **Certification** theorems: deployed bytes = `coreSpec` on embedded input + battery. Lean via `native_decide`; **Coq via `vm_compute` (kernel-checked)** | **finite / testing-grade** (proved, but covers finitely many inputs) |
| 6 | **General refinement** (Lean): `core_refines : ∀ inp cap, WellFormed inp cap → ∃ fuel, observe inp cap fuel = coreSpec inp cap`, **fully proved, `sorry`-free**. `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). | **proof-grade, COMPLETE** |

### The honest epistemics (see also the conversation)

- Items 1–5 do **not** give more coverage than running tests on a good emulator.
  Their value is a *formal oracle* (`coreSpec`) and a *tiny auditable emulator*
  instead of QEMU — not universal coverage.
- The only thing that **dominates testing** is item 6, the general theorem
  `core_refines : ∀ inp cap, WellFormed inp cap → ∃ fuel, observe inp cap fuel = coreSpec inp cap`,
  established by induction over the loop. **This proof is now complete and `sorry`-free**
  (kernel-checked; only the standard `propext`/`Classical.choice`/`Quot.sound` axioms).

## Proof plan for `core_refines` (the 4 steps) and where each stands

1. **EOF base case** — ✅ `core_eof`.
2. **Loop-start state model (in_idx, out_idx)** — ✅ `LoopInv` (idx = `rget t0`,
   out_idx = `rget t1`, plus input/output memory + register facts).
3. **Token decomposition** `decode (token ++ rest) = decode token ++ decode rest`
   ≡ machine `core(in, a, b) ≡ core(in, a+Δin, b+Δout)`:
   - spec side — ✅ `decodeS_spacing / decodeS_byte / decodeS_comment_skip`.
   - machine side — ✅ **`loop_iteration`**, a dispatch on the head char's class:
     `loop_spacing` (all three spacing chars), `loop_byte` (high+low nibble parse,
     `sb` store of `hi*16+lo` with the output↔code/input disjointness frame),
     `loop_comment` (the inner `skipComment` scan, by induction — `comment_loop`),
     and the four halting classes `loop_trailing/split/unknown_high/unknown_low/short`.
     Built from reusable machine-stepping blocks (`loop_prefix`, `read_prefix`,
     `li_beq_ne/eq`, `li_blt/li_bge`, `high/low_parse`, `store_epilogue`,
     `halt_epilogue`) over the proved `step_*` engine.
4. **Induction** — ✅ **`loop_correct`** (structural induction on a fuel bound on
   `rest.length`; base = `eof_result`/`core_eof`, step = `loop_iteration`,
   chaining via `runFuel_add`, telescoping via `spec_link`). PROVED.

**`core_refines` is PROVED, `sorry`-free** — the general refinement theorem
`∀ inp cap, WellFormed inp cap → ∃ fuel, observe inp cap fuel = coreSpec inp cap`
type-checks and is kernel-checked, assembling the prologue (`loadBytes_frame`/
`loadBytes_get`, `code_initOn`/`in_initOn`, `init_loopinv`), the induction
(`loop_correct`), `runFuel_add`, and the `observe↔coreSpec` conversion
(`decode_bytes_lt`, `range_getD`, `coreSpec_props`, `toNat`/`ofNat`).
`#print axioms Hex0.Refine.core_refines` → `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`). **The entire verified-tower refinement for hex0 has no remaining
`sorry`.**

Next: **Cross-check the ISA model** (task #7): prove our decode+step of these
   instructions agrees with `sail-riscv-lean` (Lean) and `riscv-coq` (Coq). This
   removes "model = hardware" from the TCB (currently testing-backed).

## Build / reproduce

```
# bare-metal run (needs riscv64-linux-gnu-gcc, qemu-system-riscv64)
cd bare && make run                 # prints "Hello\n", exits clean

# regenerate the model image from the ELF
uv run tools/gen_image.py

# Lean (needs elan; toolchain pinned in lean/lean-toolchain)
cd lean && lake build               # spec, model, certification, refine scaffold
lake env lean Hex0/Validate.lean    # differential battery (model vs spec)

# Coq (needs opam switch with Coq 8.20 + coq-equations)
cd coq && make -j                   # all .v incl. kernel-checked certification
```

## Layout

```
bare/        core.s (PROOF TARGET) · shell.s (trusted) · link.ld · Makefile
spec ........ coq/Spec.v  · lean/Hex0/Spec.lean        (the decode meaning)
model ....... coq/Rv64i.v · lean/Hex0/Rv64i.lean       (RV64I semantics)
validate .... coq/Validate.v · lean/Hex0/Validate.lean (model vs spec on real bytes)
certify ..... coq/Certify.v · lean/Hex0/Certify.lean   (finite, proved)
refine ...... coq/Refine.v · lean/Hex0/Refine.lean     (general theorem, in progress)
tools/ ...... gen_image.py (ELF bytes -> Image.{v,lean})
TCB.md ...... the trusted base
```
