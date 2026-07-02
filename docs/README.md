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
- [PROGRESS.md](PROGRESS.md) — LowIR & libc-formalize execution log (reverse-chronological).
- [LIBC-FORMALIZE.md](LIBC-FORMALIZE.md) — exploration + plan for formalizing & verifying libc: survey of the `third-party/` substrate (CompCert, Frama-C, CakeML/Pancake, Tree Borrows, POSIX spec, fv-libc partition), the design space, and the recommended path.
- [MEMORY-BORROWS.md](MEMORY-BORROWS.md) — the separation discipline for libc specs: shared-input / unique-output borrows (Tree-Borrows residue), the single-threaded-errno assumption, and the `Slice`/`Borrow`/`Wf`/`Disjoint` layer.
- [LOWIR-DESIGN.md](LOWIR-DESIGN.md) — design record for the lower IR: the decisions made (structured IL, unbounded registers + flat byte memory, non-local control flow, clocked semantics, borrows-not-blocks, single-threaded errno), the alternatives rejected, and the likely extensions (wider load/store, stack/frames, calls, `alloca`, borrow-typed higher IRs, `Ctrl` `compile_sim`).

## Status & handoffs

- [STATUS.md](STATUS.md) — hex0 campaign status (bare-metal run + formal proof).
- [RESUME.md](RESUME.md) — handoff for task #7 (ISA cross-check vs `riscv-coq`).
- [RESUME-HEX1.md](RESUME-HEX1.md) — hex1 campaign handoff and wrap-up (campaign complete: `core1_refines` proved in both systems).
- [RESUME-LOWIR.md](RESUME-LOWIR.md) — **handoff for the LowIR structured-IL effort + the (now complete) hex0 functional proof** (toolbox, gotchas).
- [RESUME-IR-DESIGN-SESSION.md](RESUME-IR-DESIGN-SESSION.md) — resume for the session that finished `hex0_correct`, added the `call` construct + cross-call-disjointness demo, and worked the IR design arc (memory model, borrows vs provenance/FilC/CHERI, calling conventions, `compile_sim` passes); has the open **frame-based call specs** next-step.
- [PREV_CTX.md](PREV_CTX.md) — original project handoff context (goals of the bottom-up verified tower).

## Experiments

- [REPRO-FINDINGS.md](REPRO-FINDINGS.md) — the full reproduction study: can open models reproduce verified hex0? Five phases (deepseek A/B/C clean-room → minimax-m3 → deepseek+`PREV_CTX` head-start → Kimi 2.7 → gpt-5.5-plans-kimi-executes) that progressively isolate the wall. Result: every model reproduces the engineering and (with the head-start) can *plan* the proof, but **none executes** the loop-simulation lemma — the wall is **raw proof-engineering execution under kernel-elaboration**, not comprehension.
- [REPRO-SUPERVISOR.md](REPRO-SUPERVISOR.md) — supervisor handbook for the clean-room hex0 reproduction (codex + ds4-pro in docker): session loop, steering-integrity levels, acceptance gate, stop conditions.

## Analyses

- [LEAN-VS-COQ.md](LEAN-VS-COQ.md) — implementation-difficulty comparison of the Lean vs Coq proofs, measured from the recorded [agent sessions](../sessions/README.md).
- [PITCH-REVIEW.md](PITCH-REVIEW.md) — proofread and review of the root `pitch.md` (spelling/grammar fixes, argument clarity, structural suggestions).

## Third-party design reviews

Design-choice analyses of the verification projects vendored under `third-party/`.

- [third-party/RADIX-DESIGN.md](third-party/RADIX-DESIGN.md) — `third-party/RadixExperiment` (Radix, the AI-built verified DSL in Lean 4): proof-shaped language design, two-semantics bridge, soundness-first optimizations, linear ownership layer, Verso deck.
- [third-party/VERUS-DESIGN.md](third-party/VERUS-DESIGN.md) — `third-party/verus` (the SMT-based Rust verifier): spec/proof/exec modes, rustc-as-front-end (forked THIR erasure + real borrowck on ghost code), VIR/AIR pipeline, quantifier-hygiene SMT encoding (Poly boxing, fuel, triggers), linearity-instead-of-separation-logic, tokenized state machines, trust story.
- [third-party/COMPCERT-DESIGN.md](third-party/COMPCERT-DESIGN.md) — `third-party/CompCert` (the verified C compiler, v3.17): behavior-improvement correctness contract around UB, forward-then-flip simulation architecture, block/permission memory model with `extends`/`inject`, the 11-rung IR ladder, prove-the-checker-not-the-heuristic translation validation, separate-compilation linking theorem, TCB.
