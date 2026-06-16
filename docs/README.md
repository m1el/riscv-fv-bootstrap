# Project documentation index

Documentation for the verified bootstrap tower (`/var/data/bootstrap`).
New docs go in this directory; add a line for each new doc below.

## Specs

- [HEX0.md](HEX0.md) — hex0, the minimal bootstrap seed: language grammar and error taxonomy (the spec the proofs are anchored to).
- [HEX1.md](HEX1.md) — hex1, the second rung: hex0 plus single-character labels and 32-bit relative references.

## Proof methodology & plans

- [PROOF.md](PROOF.md) — how the hex0 verification is structured (refinement methodology; served as the Coq-port blueprint).
- [REFINE1.md](REFINE1.md) — plan and progress for `core1_refines` (hex1 general refinement), including the Coq-port gotcha log (lia/OOM, `clia`, Equations traps).
- [CROSSCHECK.md](CROSSCHECK.md) — task #7: cross-checking the ISA model against `riscv-coq` (decode + step agreement, transport corollary).
- [TCB.md](TCB.md) — the Trusted Computing Base: what you must trust for the bare-metal bytes to implement the spec.
- [LIBC-FORMALIZE.md](LIBC-FORMALIZE.md) — exploration + plan for formalizing & verifying libc: survey of the `third-party/` substrate (CompCert, Frama-C, CakeML/Pancake, Tree Borrows, POSIX spec, fv-libc partition), the design space, and the recommended path.

## Status & handoffs

- [STATUS.md](STATUS.md) — hex0 campaign status (bare-metal run + formal proof).
- [RESUME.md](RESUME.md) — handoff for task #7 (ISA cross-check vs `riscv-coq`).
- [RESUME-HEX1.md](RESUME-HEX1.md) — hex1 campaign handoff and wrap-up (campaign complete: `core1_refines` proved in both systems).
- [PREV_CTX.md](PREV_CTX.md) — original project handoff context (goals of the bottom-up verified tower).

## Experiments

- [REPRO-FINDINGS.md](REPRO-FINDINGS.md) — the full reproduction study: can open models reproduce verified hex0? Five phases (deepseek A/B/C clean-room → minimax-m3 → deepseek+`PREV_CTX` head-start → Kimi 2.7 → gpt-5.5-plans-kimi-executes) that progressively isolate the wall. Result: every model reproduces the engineering and (with the head-start) can *plan* the proof, but **none executes** the loop-simulation lemma — the wall is **raw proof-engineering execution under kernel-elaboration**, not comprehension.
- [REPRO-SUPERVISOR.md](REPRO-SUPERVISOR.md) — supervisor handbook for the clean-room hex0 reproduction (codex + ds4-pro in docker): session loop, steering-integrity levels, acceptance gate, stop conditions.

## Analyses

- [LEAN-VS-COQ.md](LEAN-VS-COQ.md) — implementation-difficulty comparison of the Lean vs Coq proofs, measured from the recorded [agent sessions](../sessions/README.md).
- [PITCH-REVIEW.md](PITCH-REVIEW.md) — proofread and review of the root `pitch.md` (spelling/grammar fixes, argument clarity, structural suggestions).
