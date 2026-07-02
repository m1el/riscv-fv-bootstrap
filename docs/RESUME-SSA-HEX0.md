# RESUME — proving hex0 correct on LowIRSSA

Plan written 2026-07-02, right after the strlen/hex0 ports landed. Read with
[LOWIR-SSA-EXPERIMENT.md](LOWIR-SSA-EXPERIMENT.md) (the IR's design record —
scopes, `defaultBody`, never/thru typing) and the baseline this campaign is
measured against: `lean/LowIR/CtrlHex0Proof.lean` (1703 lines, sorry-free,
the Ctrl-IL hex0 proof).

## STATUS (updated 2026-07-02) — Phases 0, 1 DONE; Phase 2 underway

All landed code is sorry-free, builds under `lake build LowIRSSA`, and its
axioms track the Ctrl baseline `[propext, Classical.choice, Quot.sound]`
(no `native_decide` anywhere in the chain).

- **Phase 0 DONE** — `lean/LowIR/SSAProof/ExecFacts.lean` (~640 lines). All
  one-layer unfolders (leaf ops, `seq`, `catch0`, `block`, `ife`, the
  block-parameter `while` via `exec_while_unfold` + resolved
  `cont0`/`brk0`/`ret`/`contS`/`F_*` lemmas, `call`), `exec_mono`/`_le` (P4,
  guard-agnostic while handling), `exec_frame` + `exec_frame_rget` (P2 — the
  syntactic frame theorem, `catch0_frame` factors the break-scope analysis),
  `rget`/`rset`/`bindOuts`/`storeByte` helpers (P3 support; the `Slice`/`Wf`
  borrow layer is reused from `CtrlHex0Proof`). Commit `cb04884`.
- **Phase 1 DONE — GO** — `lean/LowIR/SSAProof/StrlenProof.lean` (214 lines).
  `strlen_loop` (args-tuple invariant, induction on distance-to-NUL, `inits`
  parametrized by `inits.map (evalOpnd s) = [cur, mem cur]` so it survives the
  const-rebuilt back-edge; existential fuel + `exec_mono_le`) and the run-level
  `strlenS_correct` vs `IsLen`. **The GO/NO-GO passed**: the args-tuple
  invariant carries NO register-file clauses, exactly the experiment's claim.
  Commit `42de9b0`.
- **Phase 2 UNDERWAY** — `lean/LowIR/SSAProof/Hex0Proof.lean`. Landed:
  `pnibS_eff` (the value-producing nibble `ife` → `pnibR c` in `dst`, all 5
  leaves threaded through the nested `catch0` scopes; frame NOT baked in — it
  comes from `exec_frame`), `signExtend_ofNat_small` + `exec_lit`. Commit
  `f567a00`.

### Frontier (next, in order)
- Phase 2 tail: the read-char triple (`add`/`lbu`/`addi`), the `.ife .eq`
  char-class dispatch lemmas (restated over `Prog.St`'s `rget`).
- Phase 3 `skipCommentS_eff`: the inner scan `while`, exit via `cont 1` →
  outer `cont 0` at position `i1 + commentSkip (inp.drop i1)`. Inner induction
  on the skip distance; reuse `commentSkip`/`commentSkip_le/get/run_ne`.
- Phase 4 `body_step` (the 3 char-classes; the 12-`ife` hexPath cascade uses
  `pnibS_eff` twice + `hexbyte_val`).
- Phase 5 `main_loop` (strong induction on `|inp| − idx`; the invariant is a
  function of `(idx, olen, mem)` + the frame side-conditions discharged once by
  `exec_frame` — NO `Regs`/`Pres`, NO status register).
- Phase 6 assembly (`run` unfold, 11-`lit` prelude peel via `exec_lit`,
  `boundedRun_nil_coreSpec`, `#print axioms hex0S_correct`).

The Phase-1 pattern (existential fuel, `obtain ⟨x,h⟩ : ∃ y, y = E := ⟨_,rfl⟩`
to name states without Mathlib's `set`, `generalize … at h ⊢` for the
guard-agnostic while step) transfers directly to Phases 3–5.

## 0. Mission and the metric

Prove **`hex0S_correct`**: on the SSA IL, `hex0S` (in `lean/LowIR/SSALib.lean`)
computes `Hex0.coreSpec` — the SSA sibling of `CtrlHex0Proof.hex0_correct`.
The theorem is already executably true (`hex0S_matches_spec`: the full Ctrl
battery via `native_decide`), so nothing is being defended; what is being
*measured* is the experiment's thesis:

> SSA + valued outcomes + block-parameter loops shrink the proof — the loop
> invariant becomes a statement about the args tuple, register-footprint
> bookkeeping becomes a once-proved frame theorem, and the status-register
> plumbing disappears because returns carry values.

So this campaign has TWO deliverables: the theorem, and a like-for-like size/
effort comparison against the Ctrl baseline (per-section table, §6). If the
proof does NOT come out meaningfully smaller/cleaner, that is a finding too —
it kills the "SSA as proof surface" motivation and leaves only the
compiler-facing ones (LOWIR-SSA-EXPERIMENT.md assessment §1).

## 1. What exists (frozen inputs)

- `lean/LowIR/SSA.lean` — the IR: `exec` (clocked, valued `Outcome`,
  `catch0`, the while-rebuild iteration `inits := consts of continued vals`),
  `check`/`wfEnv` (SSA census + arity/never typing), `run` returning values.
- `lean/LowIR/SSALib.lean` — `hex0S` (loop args `5`=i, `6`=n; every failure a
  `ret [.const code, .reg 6]`; success = guard-false `defaultBody`
  `ret [.const 0, .reg 6]`; `pnibS`/`skipCommentS` parameterized by scratch
  regs), `strlenS`, and the `native_decide` batteries — the executable oracle
  for every lemma statement below.
- Baseline + reusable prior art, `CtrlHex0Proof.lean` (namespace
  `LowIR.Ctrl.Hex0`): the **spec-side layer is IL-independent and imports
  verbatim** — `decodeS_*` unfolders, `boundedRun` (+ `_cons`,
  `_nil_coreSpec`), `commentSkip` (+ `_le`, `_get`, `_run_ne`,
  `decodeS_comment_reconcile`), `regionBytes` (takes a bare `mem : Word →
  Byte`), `pnibR` + its `Hex0.nibble` bridges (`pnibR_nibble`,
  `pnibR_eq_255_iff`, `pnibR_lt_16`, `hexbyte_val`, `lowStop_iff`), and the
  BitVec/cond arithmetic (`tn`, `geuL_true/false`, `slt_true/false`). What
  does NOT transfer: everything mentioning `Ctrl.St`/`Ctrl.exec` (`Regs`,
  `Pres`, `*_eff` lemmas, the borrow layer's `storeByte_preserves`).
- Gotcha memories all apply: one-layer unfolders (never `simp [exec]` with an
  IH in context), split conjunction goals before `omega` (axiom hygiene,
  target `[propext, Quot.sound]` — so no `native_decide` anywhere in the
  `hex0S_correct` chain), commit per green item.

## 2. Design decisions (resolve in Phase 0, none block statement-writing)

- **P1 — induction form for the loop.** `exec`'s while case re-executes the
  statement with `inits := (vals.map .const)`, so the loop lemma must NOT be
  stated over a fixed syntactic `inits`. Write ONE bridging unfolder
  `exec_while_iter`: for any `inits`, one head-entry step is a function of
  `argVals := inits.map (evalOpnd s)` — guard-true ⇒ body from
  `bindOuts s args argVals`, guard-false ⇒ `dflt` from the same. Then
  `main_loop` inducts on plain Nat values `(idx, olen)` with `argVals =
  [ofNat idx, ofNat olen]`. **The invariant is a function of `(idx, olen,
  mem)` — no register-file clauses.** This is the experiment's central claim;
  it must be visible in the statement (§3).
- **P2 — the frame theorem instead of `Regs`/`Pres`.** Ctrl carries a `Regs`
  structure (11 constant registers + 4 pointers "still held") re-established
  at every loop head via `Regs.transfer` + a `Pres` footprint. In SSA this is
  a **syntactic metatheorem needing no checker hypothesis**:
  `exec_frame : exec env sl fuel stmt s = some (s', oc) → ∀ r ∉ defs stmt,
  s'.regs r = s.regs r` — `exec` only ever `rset`s registers textually in
  `defs` (call outs included; callee files are fresh; `bindOuts` targets are
  `outs`/`args` ∈ `defs`). Structural fuel induction, one case per
  constructor. Corollary in `rget` form. The constants 17–27 and params
  10–13 then transfer across the loop body for free (`defs hex0BodyS` misses
  them — dischargeable by `decide`).
- **P3 — borrow layer restatement.** `Slice`/`Borrow`/`Disjoint`/`Wf` are
  St-independent, but `storeByte_preserves` is stated over `Ctrl.St`. Do the
  overdue Ext.-7-lite factoring: restate the layer once over a bare memory
  update (`fun x => if x = a then b else mem x`) in a small shared file, or
  locally in the SSA proof (~80 lines). Third client (Ctrl, ProgSim, SSA) —
  factor if it takes < an hour, else copy and note.
- **P4 — `exec_mono`.** Port `exec_mono`/`exec_mono_le` (more fuel never
  changes a `some`). The while-rebuild case recurses on a *different
  statement at the same fuel* — the induction is on fuel alone, so this is
  the same proof shape as Ctrl's; just don't induct on the statement.
- **P5 — vertical slice = `strlenS_correct`.** Before touching hex0, run the
  whole pipeline (unfolders → `exec_while_iter` → frame theorem → invariant
  on args → `run`-level assembly) on `strlenS`, the smallest loop with a
  loop-carried result and a value-computing `defaultBody`. `StrlenProof.lean`
  (Ctrl) is the baseline for the size comparison. **Go/no-go**: if the
  args-tuple invariant or the while-iter unfolder is awkward HERE, redesign
  before paying hex0 prices.

## 3. Theorem statements (write first, `sorry`'d, `#guard`-instantiate on the battery states)

```
-- the loop workhorse; contrast Ctrl.main_loop's hypothesis list
main_loop (inp p q capN) (side conditions as Ctrl: bytes < 256, lengths < 2^63,
           Disjoint ⟨p,|inp|⟩ ⟨q,capN⟩) :
  ∀ (idx olen : Nat) (s : St) (produced : List Nat),
    -- state ↔ values: ONLY the memory clauses survive from Ctrl's list —
    -- no Regs, no rget-5/6 (they are the argVals), no rget-14 (no status reg)
    input region of s.mem = inp →
    regionBytes s.mem q olen = produced → olen = produced.length →
    idx ≤ |inp| → olen ≤ capN →
    (frame side: s.rget of consts 17..27 / params 10..13 hold their values —
     discharged ONCE by exec_frame at the call site, not carried) →
    ∃ fuel s' vs, exec env 0 fuel (hex0 while, inits := idx/olen consts) s
        = some (s', .ret vs)
      ∧ vs = [ofNat status, ofNat outlen]
      ∧ (status, regionBytes s'.mem q outlen, outlen)
          = boundedRun produced (decodeS .High (inp.drop idx)) capN
      ∧ (preservation off ⟨q,capN⟩ ∪ nothing)   -- storeByte_preserves shape

hex0S_correct (inp cap) (hin : ∀ x ∈ inp, x < 256) (…bounds…)
    (hWf : Wf [⟨⟨p,|inp|⟩,.shared⟩, ⟨⟨q,cap⟩,.uniq⟩]) :
  ∃ fuel s', run libEnvS 0 fuel "hex0" [p, ofNat |inp|, q, ofNat cap] mem sp
      = some (s', [ofNat (coreSpec inp cap).1, ofNat (coreSpec inp cap).2.2])
    ∧ regionBytes s'.mem q (coreSpec inp cap).2.2 = (coreSpec inp cap).2.1
    ∧ input/off-output preservation
```

Note what the valued outcomes buy at the STATEMENT level: results are in the
`.ret` payload and the run result list — `st'.rget 14`/`rget 6` clauses are
gone; `oc = .normal ∨ oc = .ret` disjunctions are gone (there is exactly one
exit shape). Every statement must be instantiable on the battery states
(`#guard` a decidable shadow first — a misstated lemma costs minutes here,
weeks inside the induction).

## 4. Phases (each green case = a commit)

**Phase 0 — toolbox.** `SSAProof/ExecFacts.lean`: one-layer unfolders for all
constructs (per-op equations, `seq` normal/other, `catch0` × 6 outcome
shapes, `ife` then/else through `catch0`, `exec_while_iter`, `brk/cont/ret`
value equations, `call` enter/return), `evalOpnd`/`bindOuts` simp equations;
`exec_mono`/`_le` (P4); `exec_frame` + `rget` corollary (P2); borrow layer
(P3). *Risk: low. ~500 lines, mostly mechanical; ProgSim/ExecFacts is the
template.*

**Phase 1 — `strlenS_correct` (P5 vertical slice, GO/NO-GO).** Invariant:
`cur = p + k ∧ b = mem (p+k) ∧ no NUL in inp[0..k)`; guard-false ⇒ `dflt`
computes `cur − p`. Assemble to a `run`-level theorem against the null-
terminated-string spec (Ctrl `StrlenProof.lean` shape). *Risk: medium only in
the sense that design flaws surface here — that's its job. ~250 lines.*

**Phase 2 — hex0 leaf lemmas.** The 11-`lit` prelude equation (one lemma,
concrete rgets); `pnibS_eff`: `exec (pnibS dst t1 t2 src) s = some (s.rset …
|>.rset dst (pnibR c), .normal)` via the `catch0`/`ife` unfolders + reuse the
`pnibR ↔ Hex0.nibble` bridges verbatim; the read-char triple (add/lbu/addi);
cond dispatch lemmas (`ceq`-style, restated for `Prog.St`'s `rget` — note for
the comparison table: this restatement is pure St-plumbing tax, ~40 lines).
*Risk: low-medium. ~350 lines (Ctrl's `pnib_correct` was ~45 dense lines;
expect similar).*

**Phase 3 — `skipCommentS_eff`.** Inner-loop fuel induction; conclusion is
the outcome itself: `some (s', .cont 1 [ofNat i', ofNat olen])` with
`i' = idx + commentSkip (inp.drop idx)` (reuse `commentSkip` + its lemmas).
No guard register, no `gOf` model, no poison — compare directly against
Ctrl's `cgGuard_eff` + `skip_body` + `skip_loop` + `skipComment_eff` chain
(~170 lines), which this should visibly undercut. *Risk: medium (first
cross-loop `cont 1` in a proof — the depth-indexed outcome must thread
through `catch0` cleanly). ~150 lines.*

**Phase 4 — `body_step`.** One lemma, three conclusions by char class from
the loop-head state (args bound to `[idx, olen]`):
space ⇒ `.cont 0 [idx+1, olen]`; comment ⇒ `.cont 0 [idx + 1 + skip, olen]`;
hex ⇒ `.cont 0 [idx+2, olen+1]` + `storeByte` at `q+olen`, OR
`.ret [code, olen]` matching the spec's error for each of the 5 guard exits.
The hexPath cascade is 12 sequential `ife`s — pure unfolder grinding
(Ctrl's `hexPath_eff` was ~280 lines; the SSA version drops the `Regs`
re-establishment and x14 threading but keeps all the arithmetic). *Risk:
medium-high (volume). ~450 lines.*

**Phase 5 — `main_loop`.** Strong induction on `inp.length − idx` (Ctrl's
measure), one `exec_while_iter` step + `body_step` + `exec_mono` fuel
reconciliation per case, `boundedRun_cons` on the spec side. The invariant
re-establishment after an iteration should be exactly: new values, memory
clauses, done — frame theorem covers the rest. *Risk: medium — this is where
the experiment's claim is decided. ~400 lines (Ctrl: ~380).*

**Phase 6 — assembly.** `run` unfold (frameEnter with frameSize 0, params
bound), prelude peel, `main_loop` instantiation at `idx = olen = 0`,
`boundedRun_nil_coreSpec`, `#print axioms hex0S_correct` =
`[propext, Quot.sound]`. Optional one-liner corollary: hex0S and Prog's
hex0F agree (both = `coreSpec`). *Risk: low. ~150 lines.*

## 5. File & build plan

```
lean/LowIR/SSAProof/ExecFacts.lean   Phase 0 (unfolders, mono, frame, borrows)
lean/LowIR/SSAProof/StrlenProof.lean Phase 1 (the vertical slice)
lean/LowIR/SSAProof/Hex0Proof.lean   Phases 2–6
```

Add `LowIR.SSAProof.Hex0Proof` to the `LowIRSSA` lib roots **in the same
commit that creates the first file** (build-root trap; check individual files
with `lake env lean` while working). Keep `SSADump` a root too.

## 6. The comparison table (fill as phases land — this IS the second deliverable)

| item | Ctrl baseline (lines) | SSA (lines) | notes |
|---|---|---|---|
| cond/BitVec bridges | ~90 | reused verbatim + ~16 (`geuR_*`) | Ctrl's `geuL/slt/tn/pnibR*` import as-is |
| pnib | ~45 + `pnibR` model | `pnibS_eff` ~85 (5 leaves) | ife-outs+`catch0` vs assign-and-fall-through; `pnibR` model reused |
| comment skip | ~170 (guard reg + poison) | *(pending)* | direct `cont 1`, no flag reg |
| register context | ~45 (`Regs`/`Pres`/`transfer`) | **~0** + `exec_frame` (once, in toolbox) | the headline claim — CONFIRMED so far |
| body dispatch + hexPath | ~420 | *(pending)* | status reg gone |
| main loop | ~380 | *(pending)* — Phase-1 `strlen_loop` (args-tuple) is the template | invariant has no `Regs`/`rget-5/6`/status clauses |
| assembly | ~100 | *(pending)* — Phase-1 `strlenS_correct` run-peel is the template | valued `run` results |
| one-time toolbox | (amortized in Ctrl file) | ~640 reusable (`ExecFacts.lean`) | `exec_mono`, `exec_frame`, all unfolders |
| **Phase 1 strlen (whole)** | flat `StrlenProof` ~200 | **214** | args-tuple invariant, no register-file clauses |

Early read: the frame theorem does replace the `Regs`/`Pres` machinery with a
single once-proved metatheorem (P2 confirmed). The `catch0` break-scope
threading in `pnibS_eff` is new tax the Ctrl fall-through model avoids, but the
`pnibR` decode model and all cond/decodeS/boundedRun lemmas import verbatim.
Final totals pending Phases 3–6.

Honest expectation: total in the same 1.4–1.9k band, with the *per-program*
part smaller and ~500 lines being reusable SSA infrastructure; the win, if
real, shows in the invariant hypothesis lists and in Phases 3/4 statements,
not necessarily in raw total. Record whatever comes out.

## 7. Cold-start order

- [ ] Phase 0 unfolders + `exec_mono` + `exec_frame` (+ borrow restatement).
- [ ] §3 statements sorry'd + battery `#guard` instantiations.
- [ ] Phase 1 `strlenS_correct` — GO/NO-GO on the whole approach.
- [ ] Phases 2→6 in order, comparison table updated per phase.
