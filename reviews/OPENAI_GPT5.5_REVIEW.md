# Review of the Lean and Coq proofs

Date reviewed: 2026-06-03

Scope: repository documentation plus the Lean development under `lean/` and the
Coq development under `coq/`, with emphasis on the general refinement proofs and
the ISA cross-check.

## Summary

I did not find omitted Lean proof steps in the main refinement proof. The project
builds, the Lean tree has no `sorry`, `admit`, user-defined `axiom`, `opaque`, or
`unsafe` declarations, and `Hex0.Refine.core_refines` is kernel-checked with only
Lean's expected foundational assumptions:

```text
'Hex0.Refine.core_refines' depends on axioms: [propext, Quot.sound]
```

The main refinement theorem is therefore substantially stronger than the finite
certification tests: it proves that, for every well-formed input/capacity pair,
the fuel-bounded execution of the real `core` bytes reaches the same observable
result as `coreSpec`.

There are still trust-boundary items, but they are mostly outside this Lean proof:
the formal RV64I model's relation to real hardware/reference semantics, the shell
calling convention, and linker/image assumptions. The prose BNF in `HEX0.md`
should be treated as documentation for the formal grammar, not as an independent
source whose transcription is required for soundness.

## Commands run

```text
cd lean
lake build
lake env lean /tmp/Hex0AxiomCheck.lean
```

`lake build` completed successfully. It reported only lint warnings:

- `lean/Hex0/Refine.lean:240`: unused `simp` argument
  `List.getD_cons_zero`.
- `lean/Hex0/Refine.lean:3288`: unused `simp` argument `Hex0.decodeS`.
- `lean/Hex0/Refine.lean:3308`: unused variable `st`.

The temporary axiom check printed:

```text
'Hex0.Refine.core_refines' depends on axioms: [propext, Quot.sound]
'Hex0.valid_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hex0.parse_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hex0.parse_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hex0.parse_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hex0.valid_or_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hex0.not_valid_and_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'certify_embedded' depends on axioms: [propext, Quot.sound, certify_embedded._native.native_decide.ax_1_1]
'certify_battery' depends on axioms: [propext, Quot.sound, certify_battery._native.native_decide.ax_1_1]
```

## Findings

### 1. Main refinement proof appears complete

`Hex0.Refine.core_refines` is the core theorem:

```lean
theorem core_refines (inp : List Nat) (cap : Nat) (hwf : WellFormed inp cap) :
    ∃ fuel, Harness.observe inp cap fuel = Hex0.coreSpec inp cap
```

The proof is not a computation shortcut. It proceeds by:

- proving per-instruction transition lemmas over the actual loaded bytes;
- defining `LoopInv`, which carries code loadedness, input/output memory facts,
  register facts, bounds, suffix tracking, and the telescoping `spec_link`;
- proving EOF, spacing, byte, comment, and every error/output-short case;
- proving `loop_iteration`;
- proving `loop_correct` by induction on the remaining input length;
- assembling `init_loopinv`, `loop_correct`, `runFuel_add`, and the final
  `observe`/`coreSpec` conversion.

I did not find a hidden hole in this chain. The byte-store path explicitly proves
that the store does not clobber code or input, and the output-memory invariant is
rebuilt pointwise. The comment path also performs a real induction over the
comment scan rather than assuming termination.

### 2. No unnecessary axioms in `core_refines`

The main theorem is free of `Classical.choice` and `native_decide`. Its only
printed axioms are `propext` and `Quot.sound`, which are normal Lean foundations
rather than project-specific shortcuts.

This is an important distinction: `Certify.lean` deliberately uses
`native_decide`, but those finite certification theorems are not used to prove
`core_refines`.

### 3. Grammar layer uses `Classical.choice`

The grammar correspondence theorems in `Hex0/Grammar.lean` print
`Classical.choice`:

```text
[propext, Classical.choice, Quot.sound]
```

This is not an unsound custom axiom, but it is a stronger assumption than the
main refinement theorem needs. Given the comments in `Refine.lean` showing care
to avoid `Classical.choice` in similar arithmetic/propositional case splits, this
is probably avoidable in `Grammar.lean` too.

Recommended improvement: repeat the choice-elimination style used in
`Refine.lean`, especially around `simp`/`by_cases` on propositional formulas and
conjunction goals. Then re-run `#print axioms` on:

- `Hex0.valid_ok`
- `Hex0.parse_sound`
- `Hex0.parse_complete`
- `Hex0.parse_det`
- `Hex0.valid_or_err`
- `Hex0.not_valid_and_err`

### 4. Finite certification intentionally adds a native-code trust assumption

`certify_embedded` and `certify_battery` depend on generated
`native_decide` axioms. This is documented in `Certify.lean` and `TCB.md`, and it
does not contaminate `core_refines`.

Recommended improvement: if the finite certification is intended to be
independently strong in Lean, derive versions from `core_refines` for the tested
inputs/capacities, or keep the current `native_decide` theorems but label them
strictly as executable smoke tests/certificates. The current documentation mostly
does this correctly.

### 5. Documentation has stale or inconsistent proof-status text

There are a few comments/docs that should be cleaned up:

- `lean/Hex0/Refine.lean` near `loop_iteration` still says "THIS is the remaining
  frontier", even though `loop_iteration` is proved and used by `loop_correct`.
- `lean/Hex0/Grammar.lean`'s header still sketches a newline-only comment grammar
  and mentions `decode_ok_valid`; the actual grammar includes EOF-terminated
  comments and no theorem by that exact name exists.
- `TCB.md` says the step/execute side is still trusted/testing-backed, while
  `STATUS.md` and `RESUME.md` say the Coq `step_agrees`/transport work has been
  proved modulo explicit residual hypotheses. These should be reconciled so the
  trust boundary is not ambiguous.

These are not Lean proof omissions, but they make the audit trail harder to
follow.

### 6. Make the formal grammar the source of truth

`Grammar.lean` proves that the inductive `Valid`/`Parse` relations correspond to
`decodeS`, including totality and determinism. For this artifact, that is the
important formal fact: the implementation is proved against the chosen formal
language. The prose in `HEX0.md` is best viewed as an explanatory rendering of
that formal object.

The current docs sometimes frame the question as whether `Grammar.lean`
faithfully transcribes `HEX0.md`. That is backwards if the language is
project-defined rather than externally standardized. A cleaner approach is to
make the formal grammar canonical, then generate or mechanically check the BNF
documentation from it.

Recommended improvement: add explicit named iff/corollary theorems that expose
the formal contract:

```lean
theorem parse_iff_decodeS :
    Parse inp out st ↔ Hex0.decodeS .High inp = (out, st)
```

and, for valid programs:

```lean
theorem valid_iff_decode_ok :
    Valid inp out ↔ Hex0.decodeS .High inp = (out, .Ok)
```

The ingredients are already present (`parse_sound`, `parse_complete`,
`parse_det`, `valid_ok`, `valid_to_parse`). Adding named statements would make
the advertised claims easier to audit. A further improvement would be to export
a BNF/Markdown rendering from a small grammar data structure, or at least keep a
generated `HEX0.md` grammar block checked into the repository.

## Suggested improvements

1. Remove the three Lean lint warnings in `Refine.lean`.
2. Update stale comments in `Refine.lean` and `Grammar.lean`.
3. Reconcile `TCB.md` with the newer ISA cross-check status in `STATUS.md` and
   `RESUME.md`.
4. Add named grammar/spec equivalence corollaries that expose the formal
   language contract directly.
5. Try to eliminate `Classical.choice` from `Grammar.lean`, or explicitly
   document that the grammar layer uses it while `core_refines` does not.
6. Consider deriving concrete Lean certification corollaries from
   `core_refines`, keeping `native_decide` only as an executable validation path.
7. Treat `Grammar.lean` as the source of truth for the language and generate or
   mechanically check the human-facing BNF from that formal grammar.

## Bottom line

The main Lean refinement proof does not appear to omit proof steps or introduce
unnecessary project-specific axioms. The places to improve are proof hygiene and
auditability: reduce grammar-layer axioms if practical, add explicit equivalence
corollaries, remove stale comments, generate or check the BNF from the formal
grammar, and keep the trust-boundary docs synchronized with the current Coq/Lean
status.

## Coq Addendum

I also reviewed and checked the Coq proof stack. The short version: the Coq
general refinement proof is complete and `Admitted`-free, the finite Coq
certification is kernel-checked with `vm_compute`, and the riscv-coq
decode/step cross-check is proved. The only Coq axiom printed for the general
refinement and step/transport theorems is functional extensionality.

### Coq Commands Run

```text
cd coq
make -j2
coqc -q -R /var/data/bootstrap/coq Hex0Coq /tmp/Hex0CoqAssumptions.v
rg -n "^\s*(Admitted|admit|Axiom|Parameter|Variable)\b" coq --glob '*.v'
```

`make -j2` completed successfully and reported that there was nothing to
rebuild. The anchored search for proof holes and declarations printed no
matches.

The Coq assumption check printed, in order:

```text
core_refines          : functional_extensionality_dep
certify_embedded      : Closed under the global context
certify_battery       : Closed under the global context
decode_agrees         : Closed under the global context
decode_agrees_rev     : Closed under the global context
step_agrees           : functional_extensionality_dep
core_refines_riscv    : functional_extensionality_dep
```

### Coq General Refinement

The main Coq theorem is:

```coq
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
```

This theorem is proof-grade, not just finite computation. It mirrors the Lean
argument: concrete fetch/step lemmas, `LoopInv`, EOF and per-token cases,
`loop_iteration`, and `loop_correct`.

One Coq-specific difference is important: `runOn` uses fixed fuel `100000`,
whereas the Lean theorem returns an existential fuel. Coq discharges this by
proving a concrete bound. From `WellFormed`, the input length is at most 484
bytes because the fixed input region must fit before `outAddr`; the proof then
shows the machine halts within `2 + (50 * length inp + 4)` steps, and that this
is no more than `100000`.

I did not find an omitted step here. The fixed-fuel issue is explicitly handled
by `loop_correct`, `runUntil_stab`, and the `HF` bound in `core_refines`.

### Coq Certification

Unlike Lean's `Certify.lean`, Coq's `Certify.v` does not introduce a native-code
trust assumption. `certify_embedded` and `certify_battery` are proved by
`vm_compute; reflexivity` or repeated kernel computation, and both are closed
under the global context.

This is still finite/testing-grade coverage, but the Coq implementation has a
smaller TCB for those finite statements than Lean's `native_decide` version.

### riscv-coq Cross-Check

The decode agreement theorem is axiom-free:

```coq
Theorem decode_agrees : forall w, 0 <= w < 2 ^ 32 ->
  forall i, Rv64i.decode w = i -> i <> Iunknown -> decode RV64I w = embed i.
```

The reverse theorem `decode_agrees_rev` is also axiom-free under the documented
`Rv64i.decode w <> Iunknown` narrowing.

The one-step execution theorem is:

```coq
Theorem step_agrees : forall s (m:RMach) D,
  Rrel s m D -> WFstep s m D ->
  Rv64i.decode (Rv64i.fetch32 s) <> Iunknown ->
  exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
```

This is proved with only `functional_extensionality_dep`. It is not
unconditional: it requires `Rrel`, `WFstep`, and non-unknown decode. The `WFstep`
side conditions include executable/mapped fetch, aligned branch/jump targets,
and data-domain membership for `lbu`/`sb`.

The transport theorem is also proved with only functional extensionality:

```coq
Theorem core_refines_riscv : forall inp cap (m : RMach) D,
  WellFormed inp cap ->
  Rrel (mkInit ...) m D ->
  RunWF (mkInit ...) D (2 + (50 * length inp + 4)) ->
  exists mfin, ...
```

This is valuable: it lifts the one-step simulation over a whole run and composes
it with the model refinement. But it still has two explicit residual
hypotheses:

- `Rrel (mkInit ...) m D`: the riscv-coq initial machine matches the hand model.
- `RunWF ...`: every non-halted state along the run satisfies the per-step
  `WFstep` obligations and decodes to a modeled instruction.

So the current Coq cross-check removes a large part of the hand-model trust, but
the reference-model corollary is not yet a fully closed theorem from only
`WellFormed`.

### Coq Improvement Suggestions

1. Reconcile `TCB.md`: it currently says step/execute is still trusted, while
   `STATUS.md`, `RESUME.md`, and the Coq files show `step_agrees` and
   `core_refines_riscv` are proved under explicit residual hypotheses.
2. Add a closed init-machine construction for riscv-coq and prove the `Rrel`
   initial-state hypothesis.
3. Prove `RunWF` from the existing `CodeLoaded`/`LoopInv` geometry and memory
   layout, so `core_refines_riscv` can become an unconditional corollary of
   `WellFormed`.
4. Consider documenting the Coq fixed-fuel bound near `Harness.runOn`, since it
   is a meaningful difference from Lean's existential-fuel theorem.
5. Keep the anchored no-hole check in the build/audit instructions:
   `rg -n "^\s*(Admitted|admit|Axiom|Parameter)\b" coq --glob '*.v'`.

### Coq Bottom Line

The Coq proof stack does not appear to omit proof steps or introduce unnecessary
custom axioms. The main refinement proof and riscv-coq simulation proofs rely
only on functional extensionality. The remaining work is not a hidden proof
hole; it is explicitly factored into the `core_refines_riscv` hypotheses:
constructing/proving the riscv-coq initial machine relation and proving `RunWF`
for the whole run.
