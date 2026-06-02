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
| 6 | **General refinement** scaffold: per-step reduction primitive **proved** in both; loop invariant + `WellFormed` + top-level statement pinned down | **proof-grade, in progress** |

### The honest epistemics (see also the conversation)

- Items 1–5 do **not** give more coverage than running tests on a good emulator.
  Their value is a *formal oracle* (`coreSpec`) and a *tiny auditable emulator*
  instead of QEMU — not universal coverage.
- The only thing that **dominates testing** is item 6, the general theorem
  `core_refines : ∀ inp cap, WellFormed inp cap → observe inp cap = coreSpec inp cap`,
  established by induction over the loop. **That proof is not yet finished.**

## Remaining frontier

1. **Finish `core_refines`** (Lean `Hex0/Refine.lean`, Coq `coq/Refine.v`).
   In hand: the per-step primitive (`step_li_t0`) and the `LoopInv` invariant.
   Remaining: the main-loop body as a one-iteration simulation lemma
   (case-split on the next char's class: comment / spacing / nibble → {trailing,
   split, unknown, emit}), the BitVec↔Nat index/arithmetic lemmas
   (`nibble`, `hi*16+lo` via shift/or, `ult`/`slt` vs spec compares), the
   code/output **disjointness frame**, then strong induction on remaining length.
   Estimated: a substantial proof (multi-session), but mechanical given the
   primitive.

2. **Cross-check the ISA model** (task #7): prove our decode+step of these
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
