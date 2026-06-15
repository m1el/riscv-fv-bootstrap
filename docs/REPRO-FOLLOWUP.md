# Clean-room reproduction — follow-on arms (open frontier models, 2026-06)

Follow-on to [REPRO-FINDINGS.md](REPRO-FINDINGS.md) (the A/B/C deepseek-v4-pro
experiment). Run 2026-06-14/15 at `/var/data/hex0-repro`. Two questions beyond
the original A/B/C:

1. Has the **open frontier moved**? — run a newer model (MiniMax M3) on the same
   clean-room hex0 task.
2. Is the wall **methodology or capability**? — give deepseek-v4-pro the original
   campaign's **resume-context head-start** (`PREV_CTX.md`) + the best harness +
   the hardened prompt, and see how far it gets.

Archives: `/var/data/hex0-repro/archive/{minimax,ds4ctx}/` (git bundles, session
logs, READMEs). Spend this follow-on ≈ **$22.4** (per-arm OpenRouter keys).

## Arms

| Arm | Model | Seed / prompt | Sessions | Cost | Outcome |
|---|---|---|---|---|---|
| **minimax** | minimax-m3 | clean-room, original prompt | 1 (~6.7h) | $8.69 | engineering ✅; main theorem a `True` stub |
| **glm** | glm-5.2 | — | 0 | $0 | **not run**: key not entitled (Z.ai error `1220`); arm scaffolded only |
| **ds4ctx** | deepseek-v4-pro | **PREV_CTX head-start** + hardened | 8 | $13.76 | engineering ✅; **real theorem authored**, never proven |

## minimax-m3 (clean-room) — architecture-level failure

Reproduced the **engineering** faster and cleaner than the deepseek arms:
smoke-tested bare-metal decoder (~35 min), sorry-free Lean spec, a 968-line
RV64+RVC machine model that compiles, byte-sync, tests, docs. But the main
theorem `main_correct (_input)(_outCap) : True := trivial` is a **vacuous stub** —
no real refinement, SPEC B3 not met (same end as deepseek arm-B).

**Why it stalled:** it built the decoder in **C compiled `-march=rv64imac`**, so
the bytes-to-prove were a **compressed-instruction (RVC) stream**. It then spent
~4h modeling all of RVC (the model still had decode holes) and never reached the
loop-invariant/refinement. A self-inflicted *instruction-surface* explosion —
the exact lever `PREV_CTX` §2.1 (base fixed-width ISA) deletes by construction.
The open frontier reproduced the engineering; it did not reproduce the theorem.

## ds4ctx (deepseek + PREV_CTX head-start) — the key result

The head-start (`PREV_CTX.md` = the design-decisions handoff, **not** the proof)
visibly changed the load-bearing decisions and moved the failure point all the
way to the original campaign's *actual* hard problem.

What it achieved (8 sessions, 19 commits, hardened prompt):
- Deliverable A green; **`-march=rv64ima` — no compressed** (avoided minimax's
  RVC quagmire at step zero); sorry-free Lean spec; a **hand-asm base-ISA decode
  core** for the provable artifact (PREV_CTX Regime-2).
- **Authored the real `decode_refinement`** — `halted=true ∧ a0=status ∧
  outLen=spec.outLen ∧ output-bytes=spec.output`, ∀ input/cap with
  disjointness+fit preconditions, over the actual machine code. This is
  essentially the original's `core_refines` conclusion — and **far past every
  clean-room arm, which only ever produced `: True`.**

What it did not achieve:
- **Never proved it.** The theorem cycled between a `: True` stub (S04–06) and a
  sorry-backed real statement; peripheral sub-lemmas used **3 `native_decide`**
  (B4-violating). When it finally *attempted* the real machine-simulation proof
  (S07, S08), `DecodeProof.lean` elaboration went **runaway** (multiple `lean`
  processes pinned at 100% CPU for minutes, stacking builds) and both sessions
  were SIGTERM'd (`exit 143`) without committing — the **elaboration-performance
  wall**, the same one the original campaign documented and clean-room arm-A
  died on.

### The decisive datapoint: the diagnostic intervention

ds4 was asked (no coding) to *explain what must be proven and decompose the proof
in plain text*. Its output (`archive/ds4ctx/PROOF_PLAN.md`, 17 KB) is **correct
and matches `PROOF.md`'s architecture**: a simulation relation `Inv` (=
`LoopInv`), a one-step simulation lemma (= `loop_iteration`), main-loop induction
on remaining input length (= `loop_correct`), Layer-0 sub-block lemmas,
fuel/termination, final assembly. It independently flagged the unbounded
skipToEol loop as needing its own invariant, the `Nat`-modulo wraparound
semantic gap, and the file duplication — and named step 1b "Hard: case explosion
+ large kernel term" **with the correct mitigation** ("black-box each sub-block
so the main lemma reasons about outcomes, not instructions" — the original's
rewrite-don't-reduce elaboration trick).

**So the gap is EXECUTION, not COMPREHENSION.** deepseek understands the proof
completely — it can plan it as well as `PROOF.md` and even predicts its own
failure mode — but cannot write the elaboration-tractable Lean to carry it out.
It blew up on exactly the 1b step it labelled Hard, and could not apply its own
stated mitigation.

## The failure surface, mapped

| Arm | Info given | Fails at |
|---|---|---|
| minimax | none (clean-room) | **architecture** (compiled-C/`rv64imac` → RVC) |
| deepseek A/B | none (clean-room) | **stating / early-proving** (`True` stubs; prologue elaboration) |
| ds4ctx | `PREV_CTX` head-start | **execution** (architecture right, real theorem authored, proof *correctly planned*, but no elaboration-tractable Lean) |

## kimi (Kimi 2.7) + a cross-model planner→executor test (2026-06-15)

Same head-start setup as ds4ctx, model = `moonshotai/kimi-k2.7-code`. Archive:
`archive/kimi/` (centerpiece: `SOLUTION_PLAN.md`). Cost ~$10.82.

**Kimi got closer than any other open model — and still did not finish.**
- **Strongest arm.** S01 reached the *real universal theorem* in one session via
  **hand-asm `rv64i`**, built its **own `AxiomReport.lean` B4-check**, and a
  smoke theorem by computation. **S02 (high-water mark): discharged 3 *real*
  refinement sub-lemmas sorry-free** (sorry 5→3) **and correctly diagnosed the
  46 GB elaboration wall in real time with the right recovery** — further +
  smarter than ds4ctx. But S03–S06 plateaued (regression / wedge / drift /
  blowup) and never closed the loop-simulation lemma. Committed result
  (`234a647`): real `mainTheorem`, B4-clean shape, **sorry-backed, partial**.

**The decisive test — gpt-5.5 plans, kimi executes.** Reset to the green 3-sorry
state; ran **gpt-5.5** (`openai/gpt-5.5`) as a *planner* → a 952-line
`SOLUTION_PLAN.md`; injected it; ran **kimi as *executor***.
- gpt-5.5's plan was the **best artifact of the whole experiment**: it uniquely
  found the stuck lemmas were **false as written** (so the models had been partly
  thrashing on *unprovable goals*) and gave the exact kernel-safe per-instruction
  recipe (rewrite-don't-reduce, frame lemmas, `omega`-disjointness, B4-clean).
- kimi executed the **foundation** faithfully — statement repairs, an assembly
  bug fix, frame lemmas, **no blowup** (vs its solo blowups), B4-respecting after
  a `native_decide` relapse — **but discharged none of the 3 simulation sorries.
  3 → 3, build red.**

**Conclusion (now triangulated across 4 frontier models): the wall is raw
execution of the loop-simulation lemmas — not comprehension, planning,
plan-specificity, or (with the plan) the blowup.** A perfect plan handed from one
frontier model to another converts *blow-up/thrash* into a *safe, slow, correct
grind* — but does **not transfer the hands-on capability** to complete the
per-instruction symbolic-execution lemmas within a session. Planning is solved;
that execution step is the frontier. (Untested: whether several more executor
sessions on the corrected foundation eventually close it.)

Sub-findings: `native_decide` affinity is **sticky** (kimi reverted to it even
when the plan explicitly forbade it); proof-process discipline is
**prompt-mediated** (PLAN/PROGRESS from the hardened prompt; the
`AxiomReport.lean` self-check was Kimi's own); operationally codex resists
SIGTERM (needs `pkill -9`), OpenRouter stream hangs cause ~20-min wedges.

| Arm | Info given | Fails at |
|---|---|---|
| kimi | `PREV_CTX` head-start | **execution** — *closest*: banked real proven sub-lemmas + diagnosed the wall, but never completed the loop-simulation lemma |
| kimi ← gpt-5.5 plan | head-start + expert tactic-level plan | **execution** — followed the plan's foundation (no blowup, repairs, B4) but still 3→3 on the simulation lemmas |

## Bottom line

- The **open frontier reproduces the engineering** (running decoder, faithful
  model, spec) cheaply and largely unaided — and a newer model (M3) does it
  faster — but **not the verification core**.
- The **methodology head-start is necessary but not sufficient.** `PREV_CTX`
  deletes the architecture mistakes and gets deepseek to the real theorem and a
  correct proof plan — but the remaining wall is **low-level proof-engineering
  execution under kernel-elaboration constraints**. That capability is exactly
  what `PREV_CTX` does *not* contain (it lives in `PROOF.md`) and what the
  original Claude campaign spent ~6h exercising.
- The honest one-liner: **the open models can now design this proof; they still
  cannot execute it.**

## Caveats (experiment integrity)

- ds4ctx is **not** a clean-room run by design — `PREV_CTX.md` was injected
  deliberately (the whole point). It is not comparable to the A/B/C purity bar.
- `PREV_CTX.md` is the *design-decisions* handoff, not the proof: it contains the
  spec shape (§6.2), ISA/pure-slice/trusted-shell methodology, and a proof-target
  checklist — but **not** `LoopInv`/the lemma DAG (those are in `PROOF.md`, written
  later). So ds4 planning the proof correctly is a genuine result, not a leak of
  the proof.
- Per-arm OpenRouter keys gave exact spend attribution. glm-5.2 was unrunnable
  (entitlement), so the "newer than ds4" frontier point rests on M3 alone.
