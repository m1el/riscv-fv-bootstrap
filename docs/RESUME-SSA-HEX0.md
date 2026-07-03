# RESUME — proving hex0 correct on LowIRSSA

Plan written 2026-07-02, right after the strlen/hex0 ports landed. Read with
[LOWIR-SSA-EXPERIMENT.md](LOWIR-SSA-EXPERIMENT.md) (the IR's design record —
scopes, `defaultBody`, never/thru typing) and the baseline this campaign is
measured against: `lean/LowIR/CtrlHex0Proof.lean` (1703 lines, sorry-free,
the Ctrl-IL hex0 proof).

## STATUS (updated 2026-07-03) — ✅ CAMPAIGN COMPLETE, all 6 phases DONE

`LowIR.SSA.hex0S_correct` is proved sorry-free; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` — **no `native_decide`, no `sorry`**
in the chain (same axiom base as the Ctrl baseline). The whole SSA `hex0S`,
`run` on `memIn (asBytes inp)`, returns `Hex0.coreSpec`'s status and output
length as its two `.ret` values, with the output region holding `coreSpec`'s
bytes. Builds under `lake build LowIRSSA`. Both deliverables landed: (a) the
theorem, (b) the per-section comparison table (§6).

- **Phase 2 DONE** — commits `f567a00`, `a1e3095`, Phase-2-tail. `pnibS_eff`,
  `exec_lit`, the `ceqS`/`weqS`/`geu_wwS` char-class dispatch lemmas, the
  `RegsS` register-context struct + `RegsS.of_agree`/`.frame` (the frame
  theorem in action — P2), `prefSt` read-char prefix + `hexPrefix_exec`.
- **Phase 3 DONE** — `skipCommentS_eq` (defeq to the inner `scWhile`),
  `skip_loopS` (induction on the `commentSkip` distance, exit via `cont 1`).
- **Phase 4 DONE** — `hexPathS_eff` (6-arm disjunction), `hex0DispatchS` +
  `body_lift`, `body_space`/`body_comment`/`body_hex_lift`.
- **Phase 5 DONE** — `main_loop` (strong induction on `|inp|−idx`, args-tuple
  invariant, `RegsS.rset56`/`.frame` carry the const/param regs; dispatch on
  char class; connected to `boundedRun`/`decodeS`).
- **Phase 6 DONE** — `hex0S_correct` (frameEnter + 11-lit prelude peel +
  `boundedRun_nil_coreSpec`).

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

### Frontier — proof done; next is a semantics cleanup

All phases (0–6) landed and sorry-free. The proof lives in
`lean/LowIR/SSAProof/{ExecFacts,StrlenProof,Hex0Proof}.lean`; the headline
theorem is `LowIR.SSA.hex0S_correct`. See §6 for the size comparison.

**Next task (to implement): the loop-arg redesign — §8.** Switch the `while`
back-edge from *rebuilding the term* (`inits := vs.map .const`) to *rebinding in
the environment*, which deletes the one measurable proof tax (§6 tax #2). Do it
before proving the next loop on this IR.

The Phase-1 pattern that carried the whole campaign (existential fuel,
`obtain ⟨x,h⟩ : ∃ y, y = E := ⟨_,rfl⟩` to name states without Mathlib's `set`,
fuel written as `f+k` variable form to avoid corrupting register literals,
existential-fuel composition via `exec_seqE`/`exec_mono_le`, and defeq bridges
between the surface `Stmt` defs and their nested-`seq` unfoldings) is the
reusable recipe for the next SSA proof (hex1, or the ProgSim `compile_sim`).

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

Measured on the landed files (SSA `Hex0Proof.lean` = **1527**, reusable
`ExecFacts.lean` = **715**, `StrlenProof.lean` = **214**; Ctrl
`CtrlHex0Proof.lean` = **1703**, which *includes* the ~600-line spec-side layer
the SSA proof imports verbatim rather than recounting).

| item | Ctrl baseline (lines) | SSA (lines) | notes |
|---|---|---|---|
| cond/BitVec bridges | ~90 | reused verbatim + ~50 (`geuR_*`, `ceqS`/`weqS`/`geu_wwS`) | Ctrl's `geuL/slt/tn/pnibR*` import as-is; SSA restates the reg-vs-reg / byte-vs-const guards over `Prog.St` |
| pnib | ~45 + `pnibR` model | `pnibS_eff` ~85 (5 leaves) | ife-outs+`catch0` vs assign-and-fall-through; `pnibR` model reused |
| comment skip | ~170 (guard reg + poison) | **~210** (Phase 3) | direct `cont 1`, no flag reg — but the block-param `while` rebuild + `SCok`/`scWhile` defeq bridge costs back what the flag reg saved |
| register context | ~45 (`Regs`/`Pres`/`transfer`) | **~55** (`RegsS` + `of_agree` + `frame` + `rset56` + `pref`), **once** | headline CONFIRMED: `RegsS.frame` (one `exec_frame_rget` call) replaces all *per-body* `Pres`/`transfer` plumbing — the body/loop proofs carry ZERO register-preservation obligations |
| body dispatch + hexPath | ~420 | **~500** (Phase 4) | status reg gone; cost shifts to `exec_seqE`/`exec_ifeE_*_pass` straight-line composition over defeq-checked `Stmt` structure |
| main loop | ~380 | **~460** (Phase 5, `main_loop` 431 + helpers) | invariant has NO `Regs`/`rget-5/6`/status clauses — just `[ofNat idx, ofNat olen]` args-tuple + `RegsS` frame + memory; the extra lines are the 6-way hexPath arm plumbing, not invariant bookkeeping |
| assembly | ~100 | **~86** (Phase 6) | valued `run` results — returns `coreSpec`'s `(status, len)` directly, no status/len register readback |
| one-time toolbox | (amortized in Ctrl file) | **715** reusable (`ExecFacts.lean`) | `exec_mono`, `exec_frame`, all one-layer unfolders, block-param `while` lemmas — amortized across strlen/hex0/hex1/ProgSim |
| **Phase 1 strlen (whole)** | flat `StrlenProof` ~200 | **214** | args-tuple invariant, no register-file clauses |
| **hex0 per-program total** | **~1703** (incl. ~600 reused spec layer) | **1527** (`Hex0Proof.lean`) + 715 reusable toolbox | |

Final read (all phases in): the experiment's central claim (P2) is **confirmed
and visible** — the register-context row is the win. Ctrl spends `Regs`/`Pres`/
`transfer` and threads a preservation obligation through *every* body and loop
step; the SSA proof proves the frame theorem **once** (`exec_frame_rget`, in the
toolbox) and each body/loop lemma carries zero register-preservation bookkeeping.
The invariant of `main_loop` is a clean `(idx, olen, mem)` function with an
args-tuple — no `Regs`, no `rget-5/6`, no status register — exactly as predicted.

But the raw per-section line counts are **flat-to-slightly-higher**, not lower:
the SSA IR's structured control flow moves the cost rather than removing it.
Three new taxes appear that the Ctrl fall-through model avoids: (1) `catch0`
break-scope threading (`pnibS_eff`, `body_lift`, the `exec_ifeE_*_pass` chains);
(2) the block-parameter `while` rebuild — the back-edge re-executes a *rebuilt*
`while` with `inits := vals.map .const`, so every loop step carries a
`vs.map .const` normalization and a defeq bridge (`skipCommentS_eq`, `hex0WhileS`);
(3) valued outcomes (`.ret [status, olen]`) need explicit fuel-existential
composition (`exec_seqE`/`exec_mono_le`) where Ctrl's flat `exec` chained
straight. Net: hex0-specific code is **1527** vs Ctrl's ~1703 (the latter
inflated by the reused spec layer), plus **715** of genuinely reusable SSA
infrastructure — landing in the predicted 1.4–1.9k band. The win is
**structural** (no per-step register plumbing, cleaner invariants), not a raw
line-count reduction.

## 7. Cold-start order

- [ ] Phase 0 unfolders + `exec_mono` + `exec_frame` (+ borrow restatement).
- [ ] §3 statements sorry'd + battery `#guard` instantiations.
- [ ] Phase 1 `strlenS_correct` — GO/NO-GO on the whole approach.
- [ ] Phases 2→6 in order, comparison table updated per phase.

## 8. NEXT (to implement) — loop-arg redesign: rebind-in-environment, not rebuild-the-`while`

**Decision: do this before proving the next loop on this IR.** It removes the
single measurable proof tax the hex0 campaign surfaced (§6 tax #2). It is a
*semantics change*, so it is a rework, not a free refactor.

### The problem (what the current encoding costs)

The `while` back-edge steps to a **different term**. From `exec_while_cont0`:

```
exec (fuel+1) (.«while» outs inits args c ca cb body dflt) s
  = exec fuel  (.«while» outs (vs.map .const) args c ca cb body dflt) s1     -- body yielded `cont 0 vs`
```

The `inits` field is overwritten with `vs.map .const` each iteration, i.e. the
loop is defined by structural recursion that **rebuilds the `Stmt`**, carrying
the loop values *inside the term*. Because the term is not stable across
iterations, induction is over a *family* of `while` terms indexed by `inits`,
which forces two frictions (both visible in `main_loop`):

- **A per-iteration round-trip** values → `.const` → `evalOpnd` → values: the
  `rw [show ([a, b].map Opnd.const) = [.const a, .const b] from rfl]` steps and
  the `hev'` obligations `([.const a, .const b].map (evalOpnd s)) = [a, b]`.
- **Term-shape reconciliation**: `hex0WhileS` had to be parametrized by `inits`
  (the term isn't fixed), and the defeq bridge `skipCommentS_eq :
  skipCommentS i1 j j1 a b = scWhile j j1 a b [.reg i1]` exists purely to
  re-align the surface loop def with its rebuilt form.

Both are pure ceremony: they exist only because the carried values live in the
*term* instead of the *state*.

### The fix (rebind in the environment)

Keep the loop *term* fixed; thread the carried values through the **state**.
Evaluate `inits` **once** at entry to a value tuple, then iterate a primitive
that rebinds `args := vals` each time and recurses on `(state, value-list)` —
the *same* term throughout:

```
loop fuel (while outs args c ca cb body dflt) s vals =
  let s' := bindOuts s args vals            -- rebind params to carried values
  if guard s' then
    match exec fuel body s' with
    | some (s'', cont 0 vs) => loop fuel (while …) s'' vs   -- SAME term, vs threaded as values
    | …                                                     -- brk 0 / brk (k+1) / cont (k+1) / ret as today
  else exec fuel dflt s'
```

The induction hypothesis becomes "for all `vals` satisfying the invariant,
`loop … s vals = …`", and the args-tuple **is** `vals`. No `.map .const`, no
wrap/unwrap, no `hev'`, no `skipCommentS_eq`-style bridges. The `while`
constructor's surface semantics is `loop` started from `inits.map (evalOpnd s)`
evaluated once.

### Migration checklist (what it ripples through)

- [ ] `LowIR/SSA.lean` — `exec` `while` clause: split into "evaluate `inits`
      once → seed `vals`" + a `loop`/`iterate` step relation (or an inner
      recursion on a value list) that does **not** reconstruct the term.
      (Decide: separate `loop` relation vs. an internal fuel-recursion — keep
      `while` as the single *surface* constructor either way.)
- [ ] `LowIR/SSAProof/ExecFacts.lean` — restate the `exec_while_*` family
      (`_unfold`, `_cont0`/`_contS`/`_brk0`/`_brkS`/`_ret`/`_F_*`, `_badlen`)
      against the fixed-term/value-list form; `exec_mono`/`_le` and
      `exec_frame`/`_frame_rget` should carry over (the frame theorem is
      orthogonal to this change).
- [ ] Reprove the three loop clients: `StrlenProof.strlen_loop`,
      `Hex0Proof.skip_loopS`, `Hex0Proof.main_loop`. Expect each to **shrink** —
      delete the `.map .const` `rw`s and the `hev'`/`skipCommentS_eq`/`hex0WhileS`
      scaffolding; the invariant is stated directly over the value tuple.
- [ ] Keep the `native_decide` batteries (`hex0S_matches_spec`, `strlenS_ok`)
      green — the *surface* `run` behaviour must be unchanged (this is a proof-
      side/semantics-cleanliness change, not a language change).
- [ ] Re-check `#print axioms hex0S_correct` = `[propext, Classical.choice,
      Quot.sound]` after the rework.

### Success criterion

`main_loop` + `skip_loopS` + `strlen_loop` reprove with the per-iteration
`.map .const` round-trips and the `skipCommentS_eq`/`hex0WhileS` bridges gone,
and the §6 "comment skip" / "main loop" rows drop. If the loop lemmas do **not**
get simpler, the redesign didn't pay — revert.
