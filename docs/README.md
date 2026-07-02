# Project documentation index

Documentation for the verified bootstrap tower (`/var/data/bootstrap`).
New docs go in this directory; add a line for each new doc below.
Outdated/inactive docs (completed handoffs, superseded plans, frozen status
snapshots) move to [archive/](archive/README.md) — see the archive index there.
Run `./docs/check_docs.py` to validate the corpus: link/anchor integrity,
reachability from this index via down-links only, archive-index completeness,
and that every active doc is indexed here.

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

- [RESUME-LOWIR-COMPILER.md](RESUME-LOWIR-COMPILER.md) — **the ACTIVE handoff: the executable LowIR compiler cut** (post-D7/D8 design session): survey findings (Rv64i model already has all 16 needed encodings; build-root trap), and the detailed plan — Prog.lean IR core, memory-locals compilation strategy, differential-testing regime, commit milestones.

(Handoffs for completed campaigns — hex0/hex1 status, task-#7 cross-check, the
LowIR structured-IL effort, the IR design session, and the original project
context — are in [archive/](archive/README.md).)

## Experiments

- [REPRO-FINDINGS.md](REPRO-FINDINGS.md) — the full reproduction study: can open models reproduce verified hex0? Five phases (deepseek A/B/C clean-room → minimax-m3 → deepseek+`PREV_CTX` head-start → Kimi 2.7 → gpt-5.5-plans-kimi-executes) that progressively isolate the wall. Result: every model reproduces the engineering and (with the head-start) can *plan* the proof, but **none executes** the loop-simulation lemma — the wall is **raw proof-engineering execution under kernel-elaboration**, not comprehension. (Method/steering handbook: [archive/REPRO-SUPERVISOR.md](archive/REPRO-SUPERVISOR.md).)

## Analyses

- [LEAN-VS-COQ.md](LEAN-VS-COQ.md) — implementation-difficulty comparison of the Lean vs Coq proofs, measured from the recorded [agent sessions](../sessions/README.md).

## Archive

- [archive/README.md](archive/README.md) — index of outdated/inactive docs: the original project context (`PREV_CTX.md`), handoffs and plans for the completed hex0/hex1/cross-check campaigns, frozen status snapshots, the concluded reproduction experiment's supervisor handbook, and one-shot reviews.

## Third-party design reviews

Design-choice analyses of the verification projects vendored under `third-party/`.

- [third-party/RADIX-DESIGN.md](third-party/RADIX-DESIGN.md) — `third-party/RadixExperiment` (Radix, the AI-built verified DSL in Lean 4): proof-shaped language design, two-semantics bridge, soundness-first optimizations, linear ownership layer, Verso deck.
- [third-party/VERUS-DESIGN.md](third-party/VERUS-DESIGN.md) — `third-party/verus` (the SMT-based Rust verifier): spec/proof/exec modes, rustc-as-front-end (forked THIR erasure + real borrowck on ghost code), VIR/AIR pipeline, quantifier-hygiene SMT encoding (Poly boxing, fuel, triggers), linearity-instead-of-separation-logic, tokenized state machines, trust story.
- [third-party/COMPCERT-DESIGN.md](third-party/COMPCERT-DESIGN.md) — `third-party/CompCert` (the verified C compiler, v3.17): behavior-improvement correctness contract around UB, forward-then-flip simulation architecture, block/permission memory model with `extends`/`inject`, the 11-rung IR ladder, prove-the-checker-not-the-heuristic translation validation, separate-compilation linking theorem, TCB.
- [third-party/CAKEML-DESIGN.md](third-party/CAKEML-DESIGN.md) — `third-party/cakeml` (the verified SML compiler in HOL4, plus the Pancake C-like systems compiler): functional big-step semantics with clock, oracle FFI, `extend_with_resource_limit` correctness down to bytes, verified GC/regalloc/assembler, in-logic bootstrap (cv_compute), translator/CF/Candle ecosystem; Pancake's shape discipline, no-GC pipeline, and shared-memory-as-FFI device I/O.
- [third-party/BEDROCK2-DESIGN.md](third-party/BEDROCK2-DESIGN.md) — `third-party/bedrock2` (MIT PLV's verified low-level programming stack): omnisemantics, WP-as-Gallina-function program logic, heaplet-wise separation logic, leakage/metric strata transported through the verified RISC-V compiler, unverified-allocator+verified-checker regalloc, event-loop liveness invariant, the Kami processor proof down to gates, and LiveVerif program derivation.
- [third-party/RUSTC-BORROWCK-DESIGN.md](third-party/RUSTC-BORROWCK-DESIGN.md) — `third-party/rust` (rustc), scoped to the IR ladder (AST→HIR→THIR→MIR phases) and the borrow checker: how borrow info flows down (planted analysis-only MIR constructs, user-type ascriptions), NLL region inference internals, closure-requirement propagation upward, and where it all dies (CleanupPostBorrowck, region erasure) — with takeaways for a LowIR borrow checker.
- [third-party/CREUSOT-DESIGN.md](third-party/CREUSOT-DESIGN.md) — `third-party/creusot` (the deductive verifier for safe Rust): the RustHorn prophecy encoding of `&mut` ({current, final} pairs, resolve-on-death), consuming rustc borrowck facts, the three-dataflow resolve-point recipe, Pearlite HOAS specs, ownership-checked ghost code with verified erasure, the Coma IVL with BlackBox barriers, why3find proof workflow.
- [third-party/PRUSTI-DESIGN.md](third-party/PRUSTI-DESIGN.md) — `third-party/prusti-dev` (ETH's Viper-based Rust verifier): the "core proof" derived from types (structs as recursive Viper predicates), automatic fold/unfold permission solving, Polonius reborrowing DAG + magic-wand pledges, dual heap/snapshot encoding, layered code-generated VIR, JNI/JVM Viper bridge with warm-server caching — completing the four-way `&mut` design-space comparison.
- [third-party/REFINEDC-DESIGN.md](third-party/REFINEDC-DESIGN.md) — `third-party/refinedC` (MPI-SWS's foundational automated C verifier): the Caesium/Lithium/typing three-layer architecture, PNVI/VIP byte-provenance C semantics, ownership/refinement types as Iris predicates (`x @ ty`, Own/Shr), deterministic no-backtracking separation-logic proof search, the `[[rc::…]]` annotation ladder, pKVM/Linux case studies — the blueprint for our libc-formalization direction.
- [third-party/FRAMAC-DESIGN.md](third-party/FRAMAC-DESIGN.md) — `third-party/frama-c` (CEA's industrial C analysis platform): kernel+plugins over one normalized AST, ACSL as the lingua franca (assigns `\from`, check/assert/admit), the property-status consolidation ledger (statuses with hypotheses, cycle detection), Eva's domain-product abstract interpreter (garbled mix, offsetmaps), WP's per-function memory-model selection, alarms-as-annotations, E-ACSL runtime checks, and the ACSL-specified libc in `share/libc`.
- [third-party/LEAN-MLIR-DESIGN.md](third-party/LEAN-MLIR-DESIGN.md) — `third-party/lean-mlir` (opencompl's SSA theory in Lean 4): intrinsically typed dialects, the verified peephole rewriter with machine-enforced axiom hygiene, the LLVM dialect (PoisonOr + refinement) with the 93-pattern Alive corpus and the bv_decide tactic ladder, verified LLVM→RISC-V instruction selection via a hybrid dialect, the dialect zoo (FHE/CIRCT/Scf), and parametric-bitvector solvers — the one survey subject on our own toolchain.
- [third-party/SEL4-DESIGN.md](third-party/SEL4-DESIGN.md) — `third-party/seL4` + `third-party/l4v` (the verified microkernel and its 880k-line Isabelle proof stack): kernel/proof co-design (event kernel, preemption points, untyped retype, proof-carrying bitfield generator), the Haskell-prototype design layer, the corres/ccorres refinement calculus with assertion transport, crunch, integrity + noninterference theorems, binary translation validation, and 15 years of proof-engineering discipline.
