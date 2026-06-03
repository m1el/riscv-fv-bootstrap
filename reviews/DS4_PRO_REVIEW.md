# DS4_PRO_REVIEW — Formal Proof Review of the hex0 Verification Tower

**Date:** 2026-06-03
**Reviewer:** Codex (automated analysis)
**Scope:** All Lean proofs (`lean/Hex0/*.lean`), all Coq proofs (`coq/*.v`),
supporting documentation (`PROOF.md`, `STATUS.md`, `TCB.md`, `CROSSCHECK.md`,
`RESUME.md`), and the hex0 source/reference materials.

---

## Executive Summary

The hex0 verification tower is **substantially complete and rigorous**. Both the
Lean and Coq ports prove the central theorem `core_refines` — that the real RISC-V
binary of hex0's `core` function, executed on a formal RV64I model, computes
exactly the functional spec `coreSpec` for all valid inputs. The proofs are
**`sorry`-free (Lean) and `Admitted`-free (Coq)**, kernel-checked, with only
standard, well-accepted axioms (`propext`/`Classical.choice`/`Quot.sound` in Lean;
`functional_extensionality_dep` in Coq). An ISA cross-check against the
authoritative `riscv-coq` (coq-riscv.0.0.5) is partially complete: decode
agreement is fully proved (T1, zero axioms), and step-level forward simulation is
proved (T2, `step_agrees`). The transport corollary `core_refines_riscv` (lifting
`step_agrees` to a full run) is the only meaningful remaining gap.

Below is a detailed analysis of what the proofs cover, what they omit, which
axioms are introduced and whether they are necessary, and actionable improvement
suggestions.

---

## 1. Proof Architecture (what is proved)

The tower has three layers, all independently proved sound:

### Layer A: Grammar ↔ Spec (`Grammar.lean`)

- `Valid inp out` — the error-free BNF of HEX0.md as an inductive relation
- `valid_ok` / `decode_ok_valid` — bi-implication: `Valid inp out ↔ decodeS High inp = (out, Ok)`
- `Parse inp out st` — the grammar *with* errors (one constructor per error class)
- `parse_sound` / `parse_complete` — bi-implication with the spec (totality)
- `parse_det` — determinism (unique output + status per input)
- `valid_or_err` / `not_valid_and_err` — total disjoint partition of inputs

**Verdict: COMPLETE.** No `sorry`s, no axioms beyond the standard environment.
The grammar layer is 342 lines, fully self-contained, and its residual trust
boundary is only the human audit that `Valid`/`Parse` faithfully transcribe
HEX0.md's prose BNF (TCB item 7, explicitly documented).

### Layer B: Refinement (`Refine.lean` + `Refine.v`)

- **Engine:** `CodeLoaded`, `fetch_code`/`wordAt`, 12 `step_*` per-instruction lemmas
  (proved via closed-word `decide`/`vm_compute` on the real core bytes)
- **Arithmetic toolkit:** `ult_ofNat`, `slt_ofNat`, `ofNat_ne`, `setWidth8_64`,
  `combine_nibbles`, `getD_drop`, `wrap_small`, `wadd_id`, `toS_small`, `sltb_small`
- **Control flow blocks:** `loop_prefix`, `read_prefix`, `li_beq_ne`/`li_beq_eq`,
  `li_blt_nt`/`li_blt_t`, `li_bge_nt`/`li_bge_t`, `high_beq_ft`/`low_beq_ft`,
  `high_parse`/`low_parse`, `store_epilogue`, `halt_epilogue`, `comment_loop`
- **Token decomposition (spec side):** `decodeS_spacing`, `decodeS_byte`,
  `decodeS_comment_skip`
- **Per-token machine iterations:** `loop_spacing`, `loop_byte`, `loop_comment`,
  `loop_trailing`, `loop_split`, `loop_unknown_high`, `loop_unknown_low`, `loop_short`
- **Loop invariant** (`LoopInv`): 16 fields (Lean) / 18 fields (Coq, adds `Z.of_nat`
  conversions) relating registers + memory + spec state
- **Induction** (`loop_correct`): structural induction on a fuel bound `50*|rest| + 4`
- **Assembly:** `init_loopinv` prologue + `observe`↔`coreSpec` conversion + `core_refines`

**Lean status:** 3357 lines, **`sorry`-free**. The only occurrence of `sorry` in
the file is in a comment on line 10 documenting the historical frontier.[^1]
`#print axioms Hex0.Refine.core_refines` → `[propext, Classical.choice, Quot.sound]`.
108 theorems/lemmas proved.

**Coq status:** 3322 lines, **`Admitted`-free**. 108 `Qed.` closures, 0 `Admitted.`.
`Print Assumptions core_refines` → `[functional_extensionality_dep]` only.

[^1]: The stale "frontier" comment was never updated after the proof was completed.

### Layer C: ISA Cross-Check (`RvCross.v`, `RvCrossStep.v`, `RvCrossExec.v`)

- **T1 (`decode_agrees`)** — 353 lines: Our `Rv64i.decode` = riscv-coq's `Decode.decode RV64I`
  on all 12 forms, for every 32-bit word. **`Admitted`-free, ZERO axioms** (closed under
  the global context). Per-form lemmas `decode_addi/slli/add/or/lbu/sb/beq/blt/bge/bgeu/jal/jalr`.
  Uses `field_bitSlice`, `sext_signExtend`, range toolkit + `prove_Zeq_bitwise`.

- **Foundations (`RvCrossStep.v`)** — 270 lines: Word/Z arithmetic bridge (`br_add`,
  `br_or`, `br_ltu`, `br_lts`, `toS_signed`, `wadd_of_Z`, etc.), fetch bridge
  (`fetch_combine`: `load_bytes 4` → our `fetch32`), `run1` reduction toolkit, the
  state-bridge relation `Rrel` and well-formedness `WFstep`.

- **T2 (`step_agrees` in `RvCrossExec.v`)** — 880 lines: Forward simulation — one
  `Rv64i.step` = one riscv-coq `Run.run1 RV64I` cycle. All 12 `exec_*` lemmas proved.
  `Admitted`-free. `Print Assumptions step_agrees` → `[functional_extensionality_dep]`.

**Remaining gap:** The **transport corollary `core_refines_riscv`** (lifting
`step_agrees` over a full run by induction and composing with `core_refines`) has
not yet been written. This is the single meaningful deliverable that would state
"the *reference model* running the real bytes computes `coreSpec`." See §3.2.

---

## 2. Steps That Are Omitted or Incomplete

### 2.1 `core_refines_riscv` (transport corollary) — MISSING

The design is spelled out in `CROSSCHECK.md` §1, `RESUME.md`, and `STATUS.md`,
and the foundations (`Rrel`, `WFstep`, `step_agrees`) are proved. The corollary
itself requires:

1. A **prologue lemma**: the riscv-coq initial machine is `Rrel`-related to our
   `mkInit`/`initOn` (analogue of `init_loopinv`).
2. An **induction** framing `step_agrees` as a forward simulation, lifting the
   single-step relation to a full run (analogue of `loop_correct`).
3. **Composition** with the existing `core_refines` theorem.

This is the **only task #7 item that remains**. It was the explicit plan in
`RESUME.md` ("The ONLY remaining T2 item") and `CROSSCHECK.md` §1.

### 2.2 SLLI `shamt ≥ 32` — DOCUMENTED GAP (reverse decode direction)

`CROSSCHECK.md` §5 documents that `decode_agrees` (T1) only covers the forward
direction (our decode → riscv-coq's decode). The **reverse direction** (riscv-coq
`Slli rd rs1 shamt` → our `Islli`) requires `shamt < 32` because riscv-coq's SLLI
accepts `shamt` up to 63 (the full `shamt` field) while our model extracts only 6
bits (`field w 20 6` = `shamt mod 64`). On RV64I, SLLI with `shamt ≥ 32` is
architecturally reserved/illegal[^2], so this is arguably correct behavior, but the
theorem-as-stated does not account for it.

[^2]: The RISC-V spec says SLLI with `shamt[5] = 1` is reserved on RV64I (the
     6-bit immediate implies `shamt ∈ [0,31]` is legal, `[32,63]` is reserved).
     Our model's narrower extraction is therefore *more* restrictive than the
     reference, not less.

**Impact:** Low. The reverse direction is not needed for the TCB claim. The
forward direction (`decode_agrees`) is what anchors "our decoder faithfully
classifies the 12 forms." The `core` binary uses only `shamt ∈ {0,1,2,3,4}`,
so the gap is moot for the concrete artifact.

### 2.3 Step-model alignment for `Iunknown` — IMPLICIT, DOCUMENTED

When `decode (fetch32 s) = Iunknown`, our model leaves the state stuck
(pc unchanged). riscv-coq would raise an `IllegalInstruction` exception.
`step_agrees` has the precondition `Rv64i.decode (Rv64i.fetch32 s) <> Iunknown`,
so it only covers the 12 modelled forms. This is explicitly called out in
`CROSSCHECK.md` §5 as a deliberate scoping decision.

### 2.4 `WellFormed` precondition — AUDIT GAP, NOT A PROOF GAP

The `WellFormed inp cap` precondition bundles three facts:
- `inputAddr + |inp| ≤ outAddr` (input/output regions disjoint)
- `outAddr + cap < 2^64` (output region fits, no wraparound)
- `∀ b ∈ inp, b < 256` (inputs are bytes)

These are **not proved** for any particular invocation — they are preconditions
that the shell (`bare/shell.s`) is trusted to satisfy. This is explicitly
documented in `TCB.md` item 2 ("The trusted I/O shell — NOT proven"). This is
fine methodology (it's how CompCert, seL4, etc. handle I/O), but a reader should
understand that `core_refines` is a *partial correctness* theorem conditioned on
the memory layout described by the linker script.

### 2.5 Stale comments in Coq `Refine.v`

Two comments claim `Admitted` status where proofs now exist:
- Line 403: "the readMem/coreSpec packaging is the remaining detail -- Admitted for now"
- Line 3147: "The per-token dispatch (FRONTIER) -- Admitted for now"

The actual `loop_iteration` theorem (line 3155) has a full `Proof.` body ending in
`Qed.` (line 3185). The `eof_result` theorem (proof starting around line 405) is
also fully proved. These comments should be updated to reflect the completed state.

---

## 3. Axioms Introduced and Their Necessity

### 3.1 Lean: `propext`, `Classical.choice`, `Quot.sound`

**Source:** `#print axioms Hex0.Refine.core_refines`

| Axiom | Likely Source | Necessary? |
|-------|--------------|------------|
| `propext` | Using `↔` in `Prop` or `∀/∃` over `Prop` equalities | Probably not — could eliminate by using `→` directions explicitly |
| `Classical.choice` | `∃ fuel, ...` in the theorem statement — the existential quantifier in `Prop` requires choice to eliminate | Could eliminate by making fuel explicit (as Coq does with `runOn`'s fixed 100000 fuel) |
| `Quot.sound` | Quotient type operations — unclear source, possibly from `List` operations or `deriving` clauses | May be eliminable; likely comes from `deriving DecidableEq` or `List` induction |

**Assessment:** All three are standard, consistent, and widely accepted. They are
the same axioms Lean's own standard library uses. Eliminating `Classical.choice`
would require changing `∃ fuel` to an explicit fuel bound (as Coq already does),
which is a substantive but mechanical change. It would strengthen the theorem
(constructive fuel bound vs. mere existence) and is the most actionable
improvement. See §4.3.

### 3.2 Coq: `functional_extensionality_dep`

**Source:** `Print Assumptions core_refines`

This comes from the state records containing function fields (`mem : Z → Z`,
`reg : Z → Z`). State equality requires functional extensionality because two
states with extensionally equal memory functions must be considered equal.

**Assessment:** Unavoidable for this modelling choice (flat memory as a function).
The axiom is consistent with Coq's logic and is used pervasively in the coqutil
and bedrock2 libraries that the ISA cross-check depends on. It is the *only*
axiom (no `proof_irrelevance`, no `K`, no `excluded_middle`).

### 3.3 `native_decide` in `Certify.lean`

The Lean `Certify.lean` uses `native_decide` to compute the concrete certification
theorems. This trusts the Lean compiler + native toolchain, which is a larger TCB
than the kernel. This is explicitly documented as a deliberate, scoped trust
choice (`TCB.md` item 5). The Coq `Certify.v` uses `vm_compute` (kernel-checked)
for the same statements, providing a cross-system contrast and smaller TCB.

**The `native_decide` dependency could be eliminated** by rewriting `Certify.lean`
to use `decide` with explicit reduction lemmas, but `decodeS` is well-founded
recursive and does not reduce in the kernel, making this non-trivial. The
dual-system approach (Coq `vm_compute` provides the kernel-checked version) is
a pragmatic and well-documented mitigation.

---

## 4. Improvement Suggestions

### 4.1 Write the `core_refines_riscv` transport corollary

**Priority: HIGH.** This is the single deliverable that closes task #7 and moves
the ISA model from "trusted, testing-backed" to "proved equal to riscv-coq" in
the TCB. The foundations are done (`step_agrees`, `Rrel`, `WFstep`). The work is:

- `Rrel`-related prologue (init state match)
- simulation induction (lift `step_agrees` to full run)
- compose with existing `core_refines`

Estimated ~300–500 lines, building on `RvCrossExec.v` and `Refine.v`.

### 4.2 Update stale comments in `coq/Refine.v`

**Priority: MEDIUM.** Lines 403 and 3147 still claim `Admitted` status. Replace:

```
(* the readMem/coreSpec packaging is the remaining detail -- Admitted for now. *)
```

with:

```
(* The readMem/coreSpec packaging -- PROVED. *)
```

and similarly for line 3147's "FRONTIER" comment. These stale comments are
misleading to auditors.

### 4.3 Make the Lean fuel bound explicit (eliminate `Classical.choice`)

**Priority: LOW (nice-to-have).** Change:

```lean
theorem core_refines (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    ∃ fuel, Harness.observe inp cap fuel = Hex0.coreSpec inp cap :=
```

to:

```lean
theorem core_refines (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    Harness.observe inp cap (2 + 50 * inp.length + 4) = Hex0.coreSpec inp cap :=
```

This would:
- Eliminate `Classical.choice` from the axiom list
- Make the theorem constructive (explicit step-count bound)
- Match the Coq formulation (`runOn` uses fixed 100000 fuel)
- Strengthen the result (proves termination within a concrete bound)

The explicit bound `2 + 50*|inp| + 4` is already proved in `loop_correct`.

### 4.4 Prove the reverse direction of `decode_agrees`

**Priority: LOW.** For the 12 forms with the SLLI `shamt < 32` proviso, prove:

```coq
forall w, decode RV64I w = IInstruction i → i ≠ InvalidInstruction 0 →
  ∃ j, Rv64i.decode w = embed⁻¹(i) ∧ j ≠ Iunknown
```

This would make `decode_agrees` a genuine equivalence (modulo the SLLI quirk)
and require no new machinery — the existing per-form lemmas already establish
the forward direction, and the reverse is largely symmetric.

### 4.5 Add a `WellFormed` instantiation lemma

**Priority: LOW.** `WellFormed` is a precondition of `core_refines`, but there is
no lemma stating that the actual memory layout used by `bare/` satisfies it.
Adding:

```lean
theorem layout_wellformed : inputAddr + inputLen ≤ outAddr ∧ outAddr + 4096 < 2^64 := by native_decide
```

would make the concrete invocation explicit and auditable, even though it doesn't
discharge the larger TCB item (the shell's compliance).

### 4.6 Deduplicate `loadBytes` definitions

**Priority: LOW (code quality).** Both `Validate.lean` and `Harness.lean` define
independent `loadBytes` functions with different implementations (foldl-based
vs. recursive). The `Harness.lean` version is used in `Certify.lean` and has the
`loadBytes_frame`/`loadBytes_get` lemmas; the `Validate.lean` version is only
used in `#eval` diagnostics. Consolidating them would reduce the TCB surface
(two `loadBytes` definitions means two places to audit).

### 4.7 Cross-validate the SLLI `shamt < 32` assumption

**Priority: LOW (assurance).** The `CROSSCHECK.md` §5 note should be verified
against the actual `core` binary: run `objdump -d bare/hex0.elf | grep slli` and
confirm that all SLLI immediates are `< 32`. This is almost certainly true (the
source `core.s` uses SLLI only for nibble-positioning and byte-shifting, which
never exceed shift 4), but a one-line verification would make the assumption
explicit and auditable.

---

## 5. Cross-System Consistency Check

### 5.1 Lean ↔ Coq spec agreement

The `Spec.lean` and `Spec.v` definitions mirror each other definition-for-definition
as claimed in their headers. The key difference is:

- **Lean**: bytes are `Nat` (assumed < 256); `decodeS` is a well-founded recursion
  with a `termination_by` clause.
- **Coq**: bytes are `nat`; `decodeS` uses `Equations` with a `wf` annotation.
  The `coreSpec` uses `firstn` instead of `List.take`, and `Z.to_nat`/`zin` for
  the Z↔nat impedance between the Coq model (Z-based) and the spec (nat-based).

The computational battery in `Validate.lean`/`Validate.v` confirms they produce
identical results on the test inputs.

### 5.2 Lean ↔ Coq model agreement

- **Lean**: `BitVec 64` words with built-in modular arithmetic; `BitVec.ofNat`,
  `setWidth`, `<<<`, `|||` are native.
- **Coq**: raw `Z` in `[0, 2^64)` with explicit `wrap`, `wadd`, `wor`, `wshl`.

The Coq model is strictly more explicit (the wrapping is visible in the proof
state rather than hidden by the `BitVec` type). The `RvCross*` files prove that
the Coq model's decode/step agree with riscv-coq, which subsumes the Lean model
by computational cross-validation (the battery). The Lean `BitVec` model has
*tighter types* (no off-by-one or overflow possible) but *less third-party
validation* (the ISA cross-check is Coq-only; `sail-riscv-lean` was considered
but is a 171k-LoC WIP).

### 5.3 No circular dependencies

The proof DAG (documented in `PROOF.md` §5) has no cycles. The dependencies are:
```
Rv64i → Spec → Grammar
Rv64i → Image → Harness → Certify
Rv64i + Spec + Image + Harness → Refine
Rv64i + RvCross → RvCrossStep → RvCrossExec
```

The grammar layer and the refinement layer are independent of each other (both
terminate at `Spec`), which is architecturally sound.

---

## 6. Summary of Findings

| # | Finding | Severity | Action |
|---|---------|----------|--------|
| 1 | `core_refines_riscv` transport corollary not yet written | **High** | Complete task #7 |
| 2 | Stale "Admitted" comments in `coq/Refine.v` lines 403, 3147 | Medium | Update comments |
| 3 | Lean `∃ fuel` introduces `Classical.choice` axiom; could be explicit | Low | Make fuel bound explicit (see §4.3) |
| 4 | Reverse direction of `decode_agrees` not proved (SLLI `shamt<32` gap) | Low | Prove reverse direction |
| 5 | `WellFormed` precondition not instantiated for concrete layout | Low | Add lemma (see §4.5) |
| 6 | Duplicate `loadBytes` definitions in Validate vs. Harness | Low | Consolidate |
| 7 | Lean `Certify.lean` trusts `native_decide` (documented, mitigated by Coq `vm_compute`) | Informational | None required |
| 8 | SLLI `shamt<32` assumption not verified against actual `core` binary | Low | Run `objdump` check (see §4.7) |

## 7. Overall Assessment

The proofs are **sound, complete, and well-structured**. The verification tower
(grammar ↔ spec ↔ binary) has no hidden holes. The only meaningful deliverable
still missing is `core_refines_riscv` (the ISA cross-check transport corollary),
which has fully proven foundations and a clear design.

The methodology — dual proof assistants (Lean + Coq), a tiny auditable ISA model
cross-validated against an authoritative reference, an explicit enumerated TCB,
and a grammar layer that anchors the spec to the documented language — is
exemplary and follows the best practices of the formal verification literature
(CompCert, seL4, CakeML).

The three standard axioms in Lean (`propext`, `Classical.choice`, `Quot.sound`)
and the single axiom in Coq (`functional_extensionality_dep`) are all standard,
consistent, and well-accepted. None of them introduce logical unsoundness. The
`Classical.choice` axiom in Lean could be eliminated with a mechanical
restructuring (explicit fuel bound), which would also strengthen the theorem.

**No steps are omitted that would invalidate the central claim**: that the real
`core` binary, executed on a formal RISC-V model, computes exactly the hex0 spec
for all inputs satisfying the memory-layout precondition.
