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
| 6 | **General refinement** (Lean), built along the 4-step plan below. Proved (`sorry`-free, kernel-only): the full step-transition **engine** (`fetch_code` + all 12 instruction `step_*` lemmas), state-projection lemmas, the **EOF base case** `core_eof`, the complete **loop-state model** `LoopInv`, and the **spec-side token decomposition** (`decodeS_spacing/byte/comment_skip`). Remaining: the machine-side one-iteration lemma + the induction (`core_refines`). | **proof-grade, in progress** |

### The honest epistemics (see also the conversation)

- Items 1–5 do **not** give more coverage than running tests on a good emulator.
  Their value is a *formal oracle* (`coreSpec`) and a *tiny auditable emulator*
  instead of QEMU — not universal coverage.
- The only thing that **dominates testing** is item 6, the general theorem
  `core_refines : ∀ inp cap, WellFormed inp cap → observe inp cap = coreSpec inp cap`,
  established by induction over the loop. **That proof is not yet finished.**

## Proof plan for `core_refines` (the 4 steps) and where each stands

1. **EOF base case** — ✅ `core_eof`.
2. **Loop-start state model (in_idx, out_idx)** — ✅ `LoopInv` (idx = `rget t0`,
   out_idx = `rget t1`, plus input/output memory + register facts).
3. **Token decomposition** `decode (token ++ rest) = decode token ++ decode rest`
   ≡ machine `core(in, a, b) ≡ core(in, a+Δin, b+Δout)`:
   - spec side — ✅ `decodeS_spacing / decodeS_byte / decodeS_comment_skip`.
   - machine side — 🚧 the one-iteration lemma: from `LoopInv .. rest emitted`,
     case-split on `rest.head`'s char class and run the body (`bgeu`-not-taken,
     `lbu` input read, char-compares, then spacing→loop / nibble→`sb`+loop /
     comment→sub-loop / error→halt), landing in `LoopInv .. rest' emitted'` with
     `rest'.length < rest.length`. Needs: the input/output disjointness frame for
     the `sb` store, and BitVec↔Nat arithmetic (`nibble = c-48/-55`, `hi*16+lo`
     via `slli`+`or`, `ult/slt` vs spec compares). The engine + spec lemmas above
     reduce this to mechanical (if lengthy) case work.
4. **Induction** on `rest.length` — 🚧 base = `core_eof`, step = the iteration
   lemma; telescopes `emitted ++ decode rest` to `coreSpec inp cap`.

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
