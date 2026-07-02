# Archive — completed / superseded documentation

Documents whose work is finished or that were superseded by newer docs. Nothing
here is *wrong* — these are historical records (handoffs, plans, status
snapshots for completed campaigns) kept for audit and provenance. The active
index is [docs/README.md](../README.md).

## Original project context

- [PREV_CTX.md](PREV_CTX.md) — the original project handoff: goals of the
  bottom-up verified tower, the two verification regimes, the pure-slice
  discipline, hex0 as the first rung. *Archived: the design decisions it
  records were executed (hex0/hex1 campaigns complete); current design lives in
  [LOWIR-DESIGN.md](../LOWIR-DESIGN.md) and [DESIGN-THESES.md](../DESIGN-THESES.md).*

## Completed-campaign handoffs (resume docs)

- [RESUME.md](RESUME.md) — handoff for task #7 (ISA cross-check vs `riscv-coq`).
  *Archived: T1 (decode), T2 (`step_agrees`) and the `core_refines_riscv`
  transport corollary are all proved (two factored hypotheses remain explicit).*
- [RESUME-HEX1.md](RESUME-HEX1.md) — hex1 campaign handoff + wrap-up.
  *Archived: campaign complete — `core1_refines` proved in both Lean and Coq.*
- [RESUME-LOWIR.md](RESUME-LOWIR.md) — LowIR structured-IL handoff + the hex0
  functional proof (`hex0_correct`); proof toolbox and gotcha notes.
  *Archived: superseded by [RESUME-LOWIR-COMPILER.md](../RESUME-LOWIR-COMPILER.md);
  the gotchas also live in the memory/gotcha log.*
- [RESUME-IR-DESIGN-SESSION.md](RESUME-IR-DESIGN-SESSION.md) — resume for the
  session that finished `hex0_correct`, added `call` + cross-call disjointness,
  and worked the IR design arc. *Archived: the design arc concluded — its
  outcomes are recorded as D7/D8 in [LOWIR-DESIGN.md](../LOWIR-DESIGN.md), and
  the live handoff is [RESUME-LOWIR-COMPILER.md](../RESUME-LOWIR-COMPILER.md).*

## Completed plans & status snapshots

- [STATUS.md](STATUS.md) — hex0/hex1 campaign status table with the honest
  epistemics ladder (items 1–7b), plus the LowIR §status table. *Archived:
  frozen at campaign completion; ongoing work is logged in
  [PROGRESS.md](../PROGRESS.md).*
- [CROSSCHECK.md](CROSSCHECK.md) — the task-#7 plan: cross-checking our RV64I
  model against `riscv-coq`, with the per-instruction mapping. *Archived: task
  complete (`decode_agrees`, `step_agrees`, `core_refines_riscv` all proved).*
- [REFINE1.md](REFINE1.md) — plan and progress for `core1_refines` (hex1
  general refinement), including the Coq-port gotcha log (clia/lia-OOM,
  Equations traps). *Archived: proof complete in both systems; the gotchas are
  preserved here and in the memory log.*

## Concluded experiments & one-shot reviews

- [REPRO-SUPERVISOR.md](REPRO-SUPERVISOR.md) — supervisor handbook for the
  clean-room hex0 reproduction experiment (codex + open models in docker).
  *Archived: experiment concluded 2026-06-15; findings in
  [REPRO-FINDINGS.md](../REPRO-FINDINGS.md). Still useful as a template for
  driving long proof campaigns in an agent.*
- [PITCH-REVIEW.md](PITCH-REVIEW.md) — proofread/review of the root `pitch.md`.
  *Archived: one-shot review; a revised `pitch-v2.md` exists at the repo root.*
