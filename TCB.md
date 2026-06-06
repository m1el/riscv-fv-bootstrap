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
  proved, `sorry`-free** (axioms: `propext`/`Quot.sound` — `Classical.choice`-free).
  The **Coq `Refine.v`** port now proves `core_refines` **fully, `Admitted`-free**
  (`Print Assumptions core_refines` ⇒ only `functional_extensionality_dep`, a
  standard consistent axiom for `mem : Z → Z` state equality). Everything
  assembling the theorem — engine, `LoopInv`, `loop_correct` (fuel-bounded
  induction), `loop_iteration` (the per-token dispatch tail), `init_loopinv`,
  conversion — is kernel-checked in both Lean and Coq.

## Trusted (IN the TCB)

1. **The ISA model is faithful to real RISC-V hardware.** (Task #7 — *largely
   discharged*.)
   - **Decode: PROVED (no longer trusted).** `coq/RvCross.v`'s `decode_agrees`
     shows our `Rv64i.decode` equals **riscv-coq**'s `Decode.decode RV64I`
     (`coq-riscv.0.0.5`, the bedrock2/`compiler` reference semantics) on all **16**
     modelled forms (hex0's 12 + `sub srli ld sd` added for hex1), for every
     32-bit word, in both directions — `Admitted`-free, **zero axioms**
     (`Print Assumptions` = *Closed under the global context*). Residual trust on
     the decode side is only that *riscv-coq* faithfully models the ISA — a large,
     externally-audited artifact.
   - **Step/execute: PROVED per-instruction, transport modulo factored
     hypotheses.** `coq/RvCrossExec.v`'s `step_agrees` is a forward simulation of
     our `step` against riscv-coq's `Run.run1` over the Minimal `OState` machine,
     for all 16 forms (`ld`/`sd` via an 8-byte little-endian memory bridge), under
     the state bridge `Rrel` + per-step side conditions `WFstep` (4-aligned
     branch/jump targets, mapped data accesses — all true of the loaded cores).
     `coq/RvCrossRun.v`'s `core_refines_riscv` lifts it over whole runs and
     composes with `core_refines`. The *honest residual*, factored as explicit
     hypotheses: (a) an `Rrel`-related riscv-coq init machine, (b) `RunWF` (the
     side conditions hold along the run). Discharging those from the loaded-image
     geometry is unfinished; plus riscv-coq fidelity itself, as above.

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

---

# Trusted Computing Base (hex1 rung)

hex1 = hex0 + label definitions (`:c`) / i32 little-endian relative references
(`%c`). Same boundary shape as hex0; deltas only.

## Proven (NOT in the TCB)

- **The hex1 spec** (`lean/Hex1/Spec.lean`, `coq/Spec1.v`) — two-pass
  `scan1`/`emit1`/`coreSpec1`, mirrored across systems; the Lean spec is proved
  ≅ HEX1.md's BNF (`lean/Hex1/Grammar.lean`: lexer sound+complete ⇒ grammar
  total + deterministic), and the Coq `Grammar1.v` mirrors those theorems
  (`functional_extensionality_dep` only).
- **General refinement, BOTH systems** — Lean: `core1_refines : ∀ inp cap,
  WellFormed1 inp cap → ∃ fuel, observe1 inp cap fuel = coreSpec1 inp cap`
  (`lean/Hex1/Refine.lean`, sorry-free, no `native_decide`). Coq:
  `core1_refines : forall inp cap, WellFormed1 inp cap -> runOn1 inp cap =
  specOn1 (zin inp) (Z.to_nat cap)` (`coq/Refine1.v`, fixed fuel 100000 +
  `runUntil_stab`; `Print Assumptions` ⇒ `functional_extensionality_dep`
  only, the same footprint as hex0's `core_refines`). All three loops
  (init / pass 1 / pass 2), the label table region, and the i32 offset-byte
  arithmetic are kernel-checked in both.
- **Concrete certification, both systems** — the deployed `core1` bytes
  (724-byte image, `bare/hex1.elf`) compute `coreSpec1` on the embedded
  267-byte input (exact output value pinned to the QEMU log) and a 27-case
  battery covering every status code and offset shape. Lean:
  `Hex1/Certify.lean` (`native_decide`). Coq: `Certify1.v` (`vm_compute`,
  **zero axioms** — *Closed under the global context*).
- **The 4 new ISA encodings are cross-checked.** `sub srli ld sd` are covered
  by the same `decode_agrees`/`step_agrees` theorems as hex0's 12 (see item 1
  above) — including the 8-byte `ld`/`sd` memory bridge. The label table is
  read/written exclusively through these proved-faithful forms.

## Trusted (IN the TCB) — deltas vs hex0

1. **The trusted I/O shell** is `bare/shell1.s` (a0..a4 convention: adds
   a4 = label-table scratch pointer; must point at 2048 writable bytes
   disjoint from code/input/output).
2. **Extraction**: `tools/gen_image1.py` (and `tools/gen_decode1.py` for the
   Lean DecodeFacts) faithfully transcribe `bare/hex1.elf` into
   `Image1.{v,lean}`/`Hex1/DecodeFacts.lean`.
3. **The grammar transcription gap**: `Hex1/Grammar.lean`'s inductive grammar
   vs HEX1.md's prose BNF — same eyeball-auditable human-reading gap as hex0
   item 7.
4. Items 3–6 of the hex0 list (QEMU image load, assembler/linker, proof
   kernels incl. the Lean-`native_decide`-vs-Coq-`vm_compute` contrast,
   `pc = 0` halt convention) carry over unchanged.
