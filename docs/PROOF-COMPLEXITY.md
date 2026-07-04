# Proof complexity & redundancy — measured assessment and the priority ladder

Assessed 2026-07-04 over the full `lean/` corpus (~27k lines), mid-ProgSim
campaign. Read with [LEAN-LAYOUT.md](LEAN-LAYOUT.md) (what the files are),
[RESUME-PROGSIM.md](RESUME-PROGSIM.md) (the active campaign this re-prioritizes),
[RESUME-SSA-HEX0.md](RESUME-SSA-HEX0.md) §6 (the measured SSA-vs-Ctrl table this
extends), and [DESIGN-THESES.md](DESIGN-THESES.md) (the target the ladder climbs
toward). Purpose: record where the proof lines actually go, which of them are
redundant, and the resulting plan — so the next campaign choice is made from
measurement, not vibes.

## 1. Where the lines go

| Rung | Files | Lines | Share |
|---|---|---|---|
| RawAsm flat-PC proofs | `Hex0/Refine` 3377; `Hex1/{Refine,RefineBase,DecodeFacts}` 9564 | ~12.9k | **~48%** |
| LowIR Ctrl/Prog program proofs | `Hex0/CtrlProof` 1703, strlen 298, strtoull 308, `Hex0/ProgProof` 81 (sorry) | ~2.4k | ~9% |
| LowSSA program proofs | `Hex0/Proof` 1519, `Strlen/Proof` 214 | ~1.7k | ~6% |
| Shared proof foundations | `CtrlFacts` 292, `LowSSA/ExecFacts` 736 | ~1.0k | ~4% |
| ProgSim campaign (in flight) | `ProgSim/*` | ~3.1k | ~11% |
| Definitions/compiler/libs/specs/harness | everything else | ~5.9k | ~22% |

Two programs at the flat-PC altitude cost as much as everything else combined.

## 2. Findings

### F1. The flat-PC method scales super-linearly — retire it

hex0→hex1: code grew 2.23× (81→181 instructions), proof grew 2.83×
(3377→9564). Only ~15% (~1.4k lines) of hex1's proof is re-instantiation of
machinery hex0 already proved (`step_*`, the `li_*` branch blocks, comment/
spacing loops — generic in structure but bound to the concrete `Image`
predicate, so copied). The dominant growth is what the methodology *forces*:
the two-pass structure duplicates every per-token lemma family (`p1_*`/`p2_*`;
the comment loop is ported twice *within* hex1), and the label subsystem is
~2.5k lines with no hex0 analog — `p2_ref` alone is ~919 lines, the largest
lemma in the corpus. Lemma density: hex1 ~89 lines/lemma vs hex0 ~32. A
hex2-class program at this altitude would be a 20k-line proof. Conclusion:
**no program is ever hand-proved at the flat-PC altitude again**; finishing
`compile_sim` is what retires the method (its ~5–7k one-time cost is roughly
half of one hex1 and is paid once for every program forever).

### F2. The same spec↔program argument is proved three times, heading for four

The hex0 decoder-correctness argument (High/Low state machine ≡ `decodeS`,
comment skip, capacity) exists at RawAsm (inside `Refine.lean`), at Ctrl
(`CtrlProof.lean`, 1703), and at SSA (`LowSSA/Hex0/Proof.lean`, 1519);
`LowIR/Hex0/ProgProof.lean` is an 81-line statement whose prose plan is a
re-transcription of `CtrlProof.main_loop` — a planned fourth. Per re-proof only
~20–25% is rung-specific glue (PC/decode at RawAsm, outcome threading at Ctrl,
`catch0`/`iterWhile` at SSA); the other ~75–80% — `main_loop` (~380–420 lines),
`hexPath_eff` (~280), the spec bridges (~230) — is the same argument re-cast
against a different `exec`. This cross-rung repetition, not intra-file bloat,
is the largest redundancy in the corpus. Policy consequence: **one program,
one altitude** (see the ladder, §3 rung 2).

### F3. The IL rungs are well-factored; three leaks remain

`CtrlFacts.lean` (292 lines; 92 call sites in the Ctrl hex0 proof alone) and
`LowSSA/ExecFacts.lean` (736) successfully hoist the exec/outcome/mono
plumbing — the strlen pair measures the payoff directly (198-line pre-CtrlFacts
`CoreProof` vs 100-line post-CtrlFacts `Ctrl.lean`). Program proofs are
~20–25% plumbing / ~75–80% genuine spec reasoning. The residual leaks:

1. **Guard-bridge lemmas** (`geuL/slt/ceq/weq_true/false` families) are
   copy-pasted near-identically into Ctrl-hex0, SSA-hex0, and strtoull —
   three clients; wants a shared condition-facts module.
2. **Ctrl has no frame theorem.** Its `Regs`/`Pres`/`transfer` register-context
   plumbing (ten `by decide` side-goals) is hand-rolled per program, whereas
   SSA proved `exec_frame` once and its per-proof context carries zero
   preservation obligations — the SSA campaign's confirmed headline
   (RESUME-SSA-HEX0 §6). A syntactic `defs`-based frame theorem holds for
   Prog's mutable registers too (exec only writes textually-assigned
   registers); prove it in `ProgSim/ExecFacts.lean` (~120 lines by the SSA
   precedent) **before** writing any Prog-altitude program proof.
3. **Local unfolders never promoted** (`exec_lit`, `exec_err`,
   `ife_*_pass` variants live inside program proofs), and the borrow layer's
   `storeByte_preserves` restatement (RESUME-SSA-HEX0 P3) is on its third
   client — both overdue for the shared Facts files.

### F4. ProgSim carries dead weight; the real frontier is one `sorry`

`StmtSim.lean`'s `lower_sim` was the Phase-4.1 prototype. Its straight-line/
memory leaf cases are live (`lower_sim_cf` delegates to them), but its `seq`
case and its nine-constructor `all_goals sorry` tail (`StmtSim.lean:1003`)
have no consumer — `lower_sim_cf` (outcome-carrying, strictly more general)
supersedes them and already proves block/ife/seq/ret/brk/cont. Prune the tail;
that leaves `CtrlSim.lean:603` (while, call, cref, clen) as the single honest
statement-level frontier, plus `prog_sim` (`Defs.lean:432`) and the
Phase-1/2/5/6 stack. Also noted: `Emitted` is currently connected to the real
`layoutOf` pipeline only by `#guard` validation — Phase 2 (AsmFacts) is what
makes it a theorem.

## 3. The priority ladder (agreed 2026-07-04)

Each rung strictly shrinks what the next program proof has to say.

1. **Close `compile_sim`** — not a new rung; finish the current one.
   Order: prune the `lower_sim` dead tail (F4) → `lower_sim_cf` `while`
   (design confirmed, RESUME-PROGSIM Phase-4.3 entry) → `cref`/`clen` (needs
   the `emitCF` extension — currently stubbed) → Phase 5 `call` (the summit,
   genuinely new work) → Phases 1/2 (encode/decode, AsmFacts) → Phase 6
   `prog_sim`.
2. **One proof per program, at the Prog altitude.** First the Prog frame
   theorem (F3.2), then `ProgProof.hex0_correct` by porting
   `CtrlProof.main_loop`, then hex1F; compose each with `prog_sim` for the
   bytes-level corollary. Policy: RawAsm `Refine.lean` files become frozen
   legacy certification artifacts; the Ctrl and SSA hex0 proofs are retained
   as experiment records, not maintained rungs. Expected per-program cost
   after this rung: ~1.5–1.7k lines for hex0-class, ~100–200 for
   strlen-class — a 5–6× reduction against flat-PC, more for hex1-class.
3. **Graduate the SSA experiment: the SSA→Prog lowering + simulation proof.**
   The recorded keeper (LOWIR-SSA-EXPERIMENT assessment §1: lower, don't fork
   the compiler; ProgSim is reused unchanged). The §8 `iterWhile` rework fixed
   the loop terms on both sides, so the lowering's `while` case is a
   per-head-entry correspondence with `iterWhile_mono`/`iterWhile_frame` as
   the ready-made interface. Payoff: programs are *authored and proved* at the
   SSA altitude — where the measured evidence says invariants are args-tuples
   with no register bookkeeping — and transported SSA→Prog→RV64I without
   re-litigating either pass.
4. **The borrow checker over the SSA IR** (LOWIR-DESIGN Ext. 5;
   DESIGN-THESES thesis 6) — the first genuinely new component. It turns
   ProgSim's *assumed* side conditions into *discharged* ones: the footprint
   hypotheses (`MemAccOff`, `execT`'s `ws.all (¬ MachPriv ·)`) and the
   `Wf`/`Disjoint` hypotheses the IL program proofs take as inputs become the
   checker's output (the N3 checker-produces-the-hypothesis pattern). The
   hooks are already in place (RESUME-PROGSIM §7.4: footprint as a def).

**Hygiene backlog** (do opportunistically, each < a session): shared
condition-facts module (F3.1); promote the local unfolders and the P3 borrow
restatement into the Facts files (F3.3); prune `StmtSim.lean:1003` (F4 —
part of ladder rung 1).
