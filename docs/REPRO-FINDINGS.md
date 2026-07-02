# Can open models reproduce verified hex0? — findings

The question: can a non-Claude coding agent reproduce, from a requirements-only
spec, the verified-hex0 artifact — a bare-metal RV64 decoder on `qemu virt`
**plus a sorry-free, axiom-clean, universally-quantified Lean 4 proof that the
running bytes implement the spec**? Method and steering policy: [archive/REPRO-SUPERVISOR.md](archive/REPRO-SUPERVISOR.md).

Run across 2026-06-06 → 06-15 at `/var/data/hex0-repro/` (per-arm `work-*/`,
ledgers `runs/*ledger.csv`, archives `archive/<arm>/` with git bundles + session
logs + per-arm READMEs). Total spend ≈ **$148** across all arms (vs the original
Claude campaign yardstick: the *whole* project was $742.90 / 47h; hex0's Lean
proof alone ≈ $180 / ~6h of model-generation time).

## The result, and how the experiment got there

**Every model reproduced the *engineering* (running decoder, faithful executable
model, spec, harness, byte-sync, docs, hundreds of kernel-checked lemmas) — and
none reproduced the *verification core*: the universally-quantified,
sorry-free, axiom-clean refinement theorem.** That theorem is the only thing the
original campaign adds *over testing*, and it is exactly the part that did not
reproduce.

The experiment was run as a **progressive elimination**: each phase removed one
confounder to isolate *where* the wall actually is.

| Phase | Arm(s) | What it adds | Fails at |
|---|---|---|---|
| 1 | deepseek **A / B / C** (clean-room) | baseline | A: **elaboration cost**; B: **B4 vs design conflict**; induction not started |
| 2 | **minimax-m3** (clean-room) | a *newer* frontier model | **architecture** (compiled-C `rv64imac` → RVC) → `True`-stub theorem |
| 3 | **ds4ctx** = deepseek + `PREV_CTX` | the methodology **head-start** | **execution** — real theorem authored + *correctly planned*, but elaboration-blows-up |
| 4 | **kimi** (k2.7) + head-start | the strongest open model | **execution** — *closest*: banked real proven sub-lemmas + diagnosed the wall, never closed it |
| 5 | **gpt-5.5 → kimi** | an expert **plan**, injected | **execution** — followed the plan's foundation (no blowup) but still **3 → 3** sorries |

The failure point marches rightward as confounders are removed, and lands on a
single thing: **raw execution of the loop-simulation lemma under kernel
elaboration.** Comprehension and planning are solved; that step is the frontier.

---

## Phase 1 — clean-room, deepseek-v4-pro (arms A / B / C)

| | Harness | Prompt | Commits | Reached |
|---|---|---|---|---|
| **A** | codex | original | 12 | Deliverable A ✅; model+spec+harness+infra ✅; proof **2 sorries** (`init_block`, `hex0_correct`) |
| **B** | codex | hardened (PLAN.md, commit-per-green, patch-not-rewrite) | 50 | Deliverable A ✅; model+spec+leaf+~16 symbolic step lemmas ✅; loop induction **not started** |
| **C** | opencode | original | 5 | Deliverable A ✅; parse_nibble 256-case + scaffold; far behind |

Cost: night-1 (shared key, parallel) **$78.4** + phase-2 (per-arm keys) **$37.1**
(A $5.7, B $31.4, C $0) ≈ **$115**, ~26h.

Neither arm produced the full theorem, for two *different* structural reasons:

- **Arm A — blocked on proof-performance engineering.** It built the entire
  B4-*sound* infrastructure (119 instruction-fetch lemmas via
  `readWord_code_eq … ; decide`, memory-disjointness frame lemmas, per-instruction
  step lemmas, spec-equivalence layer; axiom report `propext + sorryAx`, no
  `native_decide`). It then spent **4 sessions** unable to land `init_block` (the
  14-instruction prologue): every formulation made the Lean **kernel** re-reduce
  the 523-byte `initMem` chain → `(kernel) deep recursion detected` / multi-minute
  elaboration. It independently rediscovered two original lessons (non-`let` state
  form, register-preservation lemmas over `dsimp`) but never found a tractable
  staging. `hex0_correct` (the loop induction) never reached.

- **Arm B — blocked on an axiom-cleanliness / design conflict (proven).** B chose
  `Array Byte` memory for fast native execution and proved machine-run facts by
  *computation* (`dec_trivial`/`native_decide`) — which let it race ahead
  (parse_nibble verified for all 256 inputs, ~16 step lemmas). **But** the
  instruction-fetch facts are kernel-*irreducible* over the Array (`rfl` blows
  recursion depth, then C-stack-overflows at `maxRecDepth 2_000_000`; `decide`
  stalls). `native_decide` is the *only* route → injects `Lean.ofReduceBool` →
  **B4 (axiom-clean) is unachievable** without ripping out the Array. So even a
  finished B would carry the forbidden axiom.

**The sharp A/B trade-off:** A had the B4-correct *fetch architecture* but lost to
elaboration cost; B had the fast *computational* architecture but it is
structurally B4-incompatible. The full theorem needs A's symbolic fetches **and**
a tractable `init_block`/induction staging — neither combined both.

**Architecture is a strong attractor.** All three arms, unprompted, chose RV64
asm + per-instruction step lemmas + loop invariant — the original's shape. The
spec's gravity, not steering, produced this.

## Phase 2 — a newer frontier model, clean-room (minimax-m3)

minimax-m3 reproduced the **engineering faster and cleaner** than the deepseek
arms (smoke-tested decoder in ~35 min, sorry-free spec, a 968-line RV64+RVC model
that compiles, byte-sync, tests, docs; ~6.7h, $8.69). But the main theorem was a
**vacuous stub** — `main_correct (_input)(_outCap) : True := trivial` — same end
as arm B.

**Why:** it built the decoder in **C compiled `-march=rv64imac`**, so the
bytes-to-prove were a **compressed-instruction (RVC) stream**; it then spent ~4h
modeling all of RVC (the model still had decode holes) and never reached the
refinement. A self-inflicted *instruction-surface* explosion — the exact lever a
base fixed-width ISA deletes by construction. *A newer model reproduces the
engineering even faster, but does not, on its own, close the theorem — and the
architecture choice is decisive.*

## Phase 3 — the methodology head-start (ds4ctx = deepseek + PREV_CTX)

Removing the architecture confounder: deepseek-v4-pro was given the original
campaign's resume-context handoff (`PREV_CTX.md` — the *design decisions*, **not**
the proof) plus the hardened prompt (8 sessions, 19 commits, $13.76).

It **moved the failure point to the original's actual hard problem**:
- Deliverable A green via **`-march=rv64ima` — no compressed** (avoided minimax's
  RVC trap at step zero); sorry-free spec; a **hand-asm base-ISA decode core**.
- **Authored the real `decode_refinement`** — `halted ∧ a0=status ∧
  outLen=spec.outLen ∧ output-bytes=spec.output`, ∀ input/cap with
  disjointness+fit preconditions, over the actual machine code (essentially the
  original's `core_refines`) — **far past every clean-room arm, which only ever
  produced `: True`.**
- **But never proved it.** The theorem cycled `: True`-stub ↔ sorry-backed; some
  sub-lemmas used `native_decide` (B4-violating). When it finally *attempted* the
  machine-simulation proof, `DecodeProof.lean` elaboration went **runaway**
  (multiple `lean` at 100% CPU for minutes) and the sessions were SIGTERM'd
  (`exit 143`) without committing — the **elaboration-performance wall**, the same
  one arm A died on.

**The decisive datapoint — the diagnostic intervention.** Asked (no coding) to
*explain what must be proven and decompose the proof in plain text*, ds4 produced
`archive/ds4ctx/PROOF_PLAN.md` (17 KB) that **matches `PROOF.md`'s architecture**:
simulation relation `Inv` (= `LoopInv`), one-step simulation lemma (=
`loop_iteration`), induction on remaining input length (= `loop_correct`),
Layer-0 sub-block lemmas, fuel/termination, assembly. It independently flagged
the unbounded skipToEol loop's invariant, the `Nat`-modulo wraparound gap, and
named step 1b "Hard: case explosion + large kernel term" **with the correct
mitigation** ("black-box each sub-block so the main lemma reasons about outcomes,
not instructions" — the rewrite-don't-reduce trick). **So the gap is EXECUTION,
not COMPREHENSION:** it can plan the proof as well as `PROOF.md` and predicts its
own failure mode, but cannot write the elaboration-tractable Lean — it blew up on
exactly the step it labelled Hard, unable to apply its own mitigation.

## Phase 4 — the strongest open model + head-start (Kimi 2.7)

Same head-start, model = `moonshotai/kimi-k2.7-code`. **Kimi got closer than any
other open model — and still did not finish** (6 sessions, ~$10.82 incl. phase 5;
archive `archive/kimi/`).

- **Strongest single session of any arm (S01):** reached the *real universal
  theorem* via **hand-asm `rv64i`**, built its **own `AxiomReport.lean` B4-check**,
  a smoke theorem by computation, plus PLAN/PROGRESS/TRUST docs.
- **High-water mark (S02):** **discharged 3 *real* refinement sub-lemmas
  sorry-free** (`loadBytes`, input-byte memory, `initMachineFor_image_byte`; sorry
  5→3), structured the theorem onto the invariant, **and correctly diagnosed the
  46 GB elaboration blowup in real time with the right recovery** ("keep the fast
  lemmas, sorry-out the one that blows up"). Further *and* smarter than ds4ctx.
- **But S03–S06 plateaued** — regression (native_decide creep), provider-hang
  wedges, drift, re-triggered blowups — and never closed the loop-simulation
  lemma. Committed state: real `mainTheorem`, B4-clean shape, **sorry-backed,
  partial**.

## Phase 5 — cross-model planner → executor (gpt-5.5 plans, kimi executes)

Removing the plan-quality confounder: reset kimi to its green 3-sorry state, ran
**gpt-5.5** (`openai/gpt-5.5`) as a *planner* against kimi's actual code → a
952-line `SOLUTION_PLAN.md`, injected it, ran **kimi as the *executor***.

- **gpt-5.5's plan was the best artifact of the whole experiment.** It uniquely
  found the stuck lemmas were **false as written** (halted-idempotence of `step`;
  `jalr` clears bit 0 so post-pc = `ret &&& …FE`; a too-short memory window;
  missing `codeMemOk`/`inputMemOk` invariants) — so the models had been partly
  **thrashing on unprovable goals** — and gave the exact kernel-safe recipe
  (per-instruction fetch/decode/step lemmas, rewrite-don't-reduce, frame lemmas,
  `omega`-on-`toNat` disjointness, B4-clean, no `native_decide`).
- **kimi executed the *foundation* faithfully** — applied the statement repairs,
  fixed an assembly bug gpt-5.5 flagged + regenerated bytes, built the frame
  lemmas, **no blowup** (vs its solo blowups), and ultimately respected B4
  (`native_decide` 7→2 after a relapse). **But discharged none of the 3
  loop-simulation sorries. 3 → 3, build red.** It ran out the session building
  the foundation and never reached the simulation lemmas.

**This is the cleanest confirmation:** a perfect plan handed from one frontier
model to another converts *blow-up/thrash* into a *safe, slow, correct grind* —
but does **not transfer the hands-on capability** to complete the per-instruction
symbolic-execution lemmas within a session. (Untested branch: whether several
more executor sessions on the corrected foundation eventually close it.)

---

## What the wall is

The proof decomposes into layers; the models' reach maps cleanly onto them:

| Layer | What it is | Status |
|---|---|---|
| A. State the theorem | the universal `∀ inp cap, machine run = spec` | ✅ (with head-start) |
| B. Plan the decomposition | invariant + step lemmas + one-step simulation + induction | ✅ (ds4's PROOF_PLAN matched PROOF.md) |
| C. The easy leaf lemmas | arithmetic, no-wrap memory, finite 256-case decode | ✅ (kimi S02, sorry-free) |
| **D. One-step simulation** | one iteration of the concrete loop (≈tens of instructions, ~16 branch cases) refines one spec step, under a precise multi-field invariant | ❌ **the wall — no model cleared it** |
| E. Induction + assembly | fuel-bounded induction, chain it up | (easy if D were done) |

**Layer D is the wall.** To prove it you must symbolically reduce a long chain of
`step` applications over a machine state (registers/memory as functions, 30+
instructions). The *default powerful tactics* (`simp`/`decide`/`rfl`/
`native_decide`) reduce the whole accumulated state term → the 46 GB / deep-
recursion blowup. The *correct* technique is counter-intuitive restraint: never
let the kernel reduce the big term — prove each instruction's effect as a tiny
committed lemma and **chain by rewriting** (`simp only [committed lemmas]`), plus
projection/frame lemmas and careful staging.

Why it is a wall **for models** specifically:
1. **Low-feedback, long-horizon.** The failure mode is a silent catastrophic
   blowup (46 GB → OOM/timeout/SIGKILL) with no localized error, breaking the
   edit→test→fix loop agents rely on. They flail (revert, retry the same thing).
2. **The right move is anti-default.** The craft is to *avoid* the strong
   automation precisely because it's too strong — opposite of trained instinct
   (the sticky `native_decide` affinity).
3. **Invariant stability.** A ~16-field invariant + threaded preconditions must be
   held consistent across dozens of interdependent tactic steps; models drift.
4. **Tacit craft, not in any corpus.** The perf-engineering technique is rarely
   written down (one of the few places is this repo's `PROOF.md`); the original
   campaign spent its ~6h of model-generation time exactly here.

## Secondary findings

- **`native_decide` affinity is sticky and model-bound.** Every arm reached for it
  on closed goals; kimi reverted to it *even when the injected plan explicitly
  forbade it*, then corrected. For axiom-clean proofs over evaluable state this is
  a latent B4 failure that surfaces only at assembly.
- **Prompt hardening fixes *process*, not *capability*.** B's 50 commits / PLAN.md
  / near-zero rewrite-thrash vs A's 6 checkout-as-undo incidents — but it did not
  make B finish; both hit hard walls. Hardening also degrades under provider
  instability (B's worst stream-glitch session caused its one checkout incident).
- **Discipline is model-bound; the harness changes mechanics, not discipline.**
  opencode (arm C) gives a real edit tool + subagents, but ds4 fumbles its
  tool-call schemas and shows the same commit-drought / dirty-tree pathologies as
  the codex arms. Proof-process discipline that *did* appear (PLAN/PROGRESS) was
  **prompt-mediated**; the one un-prompted good habit was Kimi's self-built
  `AxiomReport.lean` B4-check.
- **Operational lessons** (folded into the supervisor handbook): detached
  in-container launches survive host wrapper-kills; **never post-mortem on a log
  signal — wait for PID-death**; zombie lean/lake accumulate under `sleep
  infinity` PID 1 (reap before timing builds); **codex resists SIGTERM — use
  `pkill -9`**, sometimes twice; OpenRouter stream hangs cause ~20-min wedges;
  per-runner API keys are essential for spend attribution (opencode reports no
  tokens).

## Bottom line

- The **open frontier reproduces the engineering** cheaply and largely unaided —
  and newer models do it faster — but **not the verification core.**
- The **methodology head-start is necessary but not sufficient.** It deletes the
  architecture mistakes and gets the model to the real theorem and a correct
  proof plan — but the remaining wall is **low-level proof-engineering execution
  under kernel-elaboration constraints**, exactly what the head-start does *not*
  contain (it lives in `PROOF.md`).
- **The open models can now design this proof; they still cannot execute it** —
  and even an expert plan handed from one frontier model to another does not
  transfer that execution.

## Caveats & costs

- Phases 3–5 (head-start / plan-injection) are **not** clean-room by design — the
  whole point was to remove confounders, not to test purity. `PREV_CTX.md` is the
  *design-decisions* handoff (spec shape, ISA / pure-slice / trusted-shell
  methodology, a proof-target checklist) — **not** `LoopInv`/the lemma DAG (those
  are `PROOF.md`, written later) — so the models planning the proof correctly is a
  genuine result, not a leak.
- Per-arm OpenRouter keys gave exact spend attribution. glm-5.2 was scaffolded but
  **unrunnable** (key not entitled, Z.ai error `1220`), so the "newer frontier"
  point rests on minimax-m3 alone.

| Phase | Arm | Cost | Wall-clock |
|---|---|--:|---|
| 1 | deepseek A/B/C | ~$115 | ~26h |
| 2 | minimax-m3 | $8.69 | ~6.7h |
| 3 | ds4ctx (deepseek+head-start) | $13.76 | (8 sessions) |
| 4–5 | kimi + gpt-5.5 planner→executor | $10.82 | (6 sessions + planner) |
| | **total** | **≈ $148** | |
