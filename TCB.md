# Trusted Computing Base (hex0 rung)

What you must trust for "the bytes that run bare-metal on RISC-V implement the
hex0 spec" to hold. Written CompCert-style: an explicit, enumerated boundary.

## Proven (NOT in the TCB)

- **The `decode` spec** (`coq/Spec.v`, `lean/Hex0/Spec.lean`) — the meaning of
  hex0. The two definitions compute identically on a battery of inputs, and the
  Lean `decodeS` is **proved equivalent to the published BNF grammar of HEX0.md**
  (`lean/Hex0/Grammar.lean`): `decodeS .High inp = (out,st) ↔ Parse inp out st`,
  with the grammar shown total (`parse_total`) and deterministic (`parse_det`) —
  every input is *either* a valid program (→ `Ok`) *or* exactly one error class,
  and the classification matches the spec.
- **The RV64I model** (`*/Rv64i.*`) executes the *actual* `core` bytes and
  matches `coreSpec` (differential battery + the embedded input).
- **Concrete certification** (`*/Certify.*`) — the deployed bytes equal
  `coreSpec` on the embedded input and every error class. *Finite/testing-grade.*
- **General refinement** (`lean/Hex0/Refine.lean`) — `core_refines : ∀ inp cap,
  WellFormed inp cap → ∃ fuel, observe inp cap fuel = coreSpec inp cap`. **Fully
  proved, `sorry`-free** (axioms: `propext`/`Classical.choice`/`Quot.sound`).
  (Coq `Refine.v` still `Admitted` — port pending.)

## Trusted (IN the TCB)

1. **The ISA model is faithful to real RISC-V hardware.**
   Our hand-written RV64I model (decode + step) is currently justified
   *empirically* — its output matches QEMU on the battery. Making this
   proof-grade is task #7: cross-check decode+step of these instructions against
   the authoritative Sail model (`sail-riscv-lean`) and `riscv-coq`. Until then,
   "model = hardware" is testing-backed, not proved.

2. **The trusted I/O shell** (`bare/shell.s`) — NOT proven (deliberately; see
   PREV_CTX §4). We trust that it:
   - sets the stack pointer to valid RAM,
   - passes the correct `(in_ptr, in_len, out_ptr, out_cap)` to `core`,
   - locates the preloaded input region correctly,
   - streams `out_len` output bytes and signals completion.

3. **QEMU loads the image faithfully** into RAM at `0x80000000` and starts the
   hart at the entry point. (For the *certification*, we instead trust the
   extraction of bytes from the ELF — `tools/gen_image.py` — and that
   `Image.{v,lean}` matches `bare/hex0.bin`.)

4. **The assembler + linker** (`riscv64-linux-gnu-as`/`ld`) produce the bytes we
   reason about. The proof concerns the *bytes*; trust that the toolchain emitted
   the `core` we disassembled. (Mitigation: we reason about the *extracted*
   bytes, not the source `.s`, so an assembler bug shows up as a model/spec
   mismatch, not a silent hole.)

5. **The proof checkers**: the Lean kernel and the Coq kernel.
   - The general theorem (`Refine.*`) uses only the kernels.
   - The Lean *certification* additionally trusts `native_decide` (Lean compiler
     + native toolchain). The Coq certification uses `vm_compute` (kernel only),
     so it has the smaller TCB on the same statement — a deliberate cross-system
     contrast.

6. **`halt` observed correctly**: we model program end as `pc = 0` (the sentinel
   return address). The shell must actually return to that address / halt.

7. **The inductive grammar transcribes HEX0.md.** `Grammar.lean`'s `Valid`/`Parse`
   are the formal object; we trust they faithfully transcribe the prose BNF of
   `HEX0.md` (one constructor per production). This is a much smaller,
   eyeball-auditable gap than trusting `decodeS` directly — but it is still a
   human reading, not a proof. (HEX0.md was updated to match the implementation:
   EOF-terminated comments are accepted, and the `Split`/`Unknown` nibble-error
   split is spelled out.)

## Notes on deliberate definedness (deletes proof obligations)

- Output region is disjoint from code/input by construction (linker placement);
  `WellFormed` makes this a precondition rather than a runtime check.
- The proven `core` is correct for ALL `(ptr, len)`; sentinel-scanning for length
  is NOT in the proven core (it is the shell's job). See PREV_CTX §4.
