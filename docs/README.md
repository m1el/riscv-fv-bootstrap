# Project documentation index

Documentation for the verified bootstrap tower (this repository).
New docs go in this directory; add a line for each new doc below.
Outdated/inactive docs (completed handoffs, superseded plans, frozen status
snapshots) move to [archive/](archive/README.md) — see the archive index there.
Run `./docs/check_docs.py` to validate the corpus: link/anchor integrity,
reachability from this index via down-links only, and that every doc is
indexed by the README.md of its own directory.

## Specs

- [HEX0.md](HEX0.md) — hex0, the minimal bootstrap seed: language grammar and error taxonomy (the spec the proofs are anchored to).
- [HEX1.md](HEX1.md) — hex1, the second rung: hex0 plus single-character labels and 32-bit relative references.

## Proof methodology & plans

- [PROOF.md](PROOF.md) — how the hex0 verification is structured (refinement methodology; served as the Coq-port blueprint).
- [TCB.md](TCB.md) — the Trusted Computing Base: what you must trust for the bare-metal bytes to implement the spec.
- [PROGRESS.md](PROGRESS.md) — LowIR & libc-formalize execution log (reverse-chronological).
- [LIBC-FORMALIZE.md](LIBC-FORMALIZE.md) — exploration + plan for formalizing & verifying libc: survey of the `third-party/` substrate (CompCert, Frama-C, CakeML/Pancake, Tree Borrows, POSIX spec, fv-libc partition), the design space, and the recommended path.
- [MEMORY-BORROWS.md](MEMORY-BORROWS.md) — the separation discipline for libc specs: shared-input / unique-output borrows (Tree-Borrows residue), the single-threaded-errno assumption, and the `Slice`/`Borrow`/`Wf`/`Disjoint` layer.
- [LOWIR-DESIGN.md](LOWIR-DESIGN.md) — design record for the lower IR: the decisions made (structured IL, unbounded registers + flat byte memory, non-local control flow, clocked semantics, borrows-not-blocks, single-threaded errno), the alternatives rejected, and the likely extensions (wider load/store, stack/frames, calls, `alloca`, borrow-typed higher IRs, `Ctrl` `compile_sim`).
- [DESIGN-THESES.md](DESIGN-THESES.md) — ten design theses distilled from the third-party review series, culminating in the target: a borrow-checked, GC-free, C-power language verified down to machine code (the "empty cell" no surveyed project fills), and the composition that would fill it (borrow gate → prophecies → verified backend).

## Status & handoffs

- [RESUME-PROGSIM.md](RESUME-PROGSIM.md) — **the ACTIVE handoff: proving `compile_sim` for Prog** (compiler correctness for the D7/D8 IR): the address-divergence obstacle and the P1 frame-padding-oracle decision, the simulation relation and theorem statements, the footprint side-condition design, six proof phases with risk/size estimates, file/build plan, the vertical-slice go/no-go checkpoint, and the SSA→Prog composability notes (§7.6, on the `iterWhile` semantics).
- [RESUME-SSA-HEX0.md](RESUME-SSA-HEX0.md) — the hex0-on-LowIRSSA campaign (**COMPLETE**, incl. the §8 rebind-in-env `while` rework): the args-tuple loop invariant, the syntactic frame theorem replacing `Regs`/`Pres`, what imports verbatim from the Ctrl proof, the per-section size-comparison table against `CtrlHex0Proof.lean` (the second deliverable), and the §8 loop-arg redesign record (`iterWhile` semantics + measured outcome).
- [RESUME-LOWIR-COMPILER.md](RESUME-LOWIR-COMPILER.md) — handoff for the executable LowIR compiler cut (**DONE 2026-07-02**; kept for the design rationale): survey findings, Prog.lean IR core, memory-locals compilation strategy, differential-testing regime.

(Handoffs for completed campaigns — hex0/hex1 status, task-#7 cross-check, the
LowIR structured-IL effort, the IR design session, and the original project
context — are in [archive/](archive/README.md).)

## Experiments

- [LOWIR-SSA-EXPERIMENT.md](LOWIR-SSA-EXPERIMENT.md) — LowIRSSA (`lean/LowIR/SSA.lean`): an SSA/value-flavored variant of the Prog IR — valued outcomes, value-binding `block`/`ife`, block-parameter `while` loops with a guard-false `defaultBody`, never/thru typing, a decidable SSA checker. Design record, ambiguity resolutions, and the assessment (headline: lower SSA→Prog, don't fork the compiler).
- [REPRO-FINDINGS.md](REPRO-FINDINGS.md) — the full reproduction study: can open models reproduce verified hex0? Five phases (deepseek A/B/C clean-room → minimax-m3 → deepseek+`PREV_CTX` head-start → Kimi 2.7 → gpt-5.5-plans-kimi-executes) that progressively isolate the wall. Result: every model reproduces the engineering and (with the head-start) can *plan* the proof, but **none executes** the loop-simulation lemma — the wall is **raw proof-engineering execution under kernel-elaboration**, not comprehension. (Method/steering handbook: [archive/REPRO-SUPERVISOR.md](archive/REPRO-SUPERVISOR.md).)

## Analyses

- [LEAN-VS-COQ.md](LEAN-VS-COQ.md) — implementation-difficulty comparison of the Lean vs Coq proofs, measured from the recorded [agent sessions](../sessions/README.md).

## Archive

- [archive/README.md](archive/README.md) — index of outdated/inactive docs: the original project context (`PREV_CTX.md`), handoffs and plans for the completed hex0/hex1/cross-check campaigns, frozen status snapshots, the concluded reproduction experiment's supervisor handbook, and one-shot reviews.

## Third-party design reviews

Design-choice analyses of the verification projects vendored under `third-party/`
(12 reviews: Radix, Verus, CompCert, CakeML, bedrock2, rustc borrowck, Creusot,
Prusti, RefinedC, Frama-C, lean-mlir, seL4). Indexed in
[third-party/README.md](third-party/README.md).
