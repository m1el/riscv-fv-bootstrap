# lean-mlir — design choices

An analysis of `third-party/lean-mlir/` (opencompl, checkout `96baaa07c`,
Lean toolchain `nightly-2025-12-01`): **Lean-MLIR**, "a theory of SSA
developed in the Lean proof assistant" (ITP'24 paper *Verifying Peephole
Rewriting in SSA Compiler IRs*, plus two OOPSLA'25 artifact lines), grown
into an ecosystem: a generic verified peephole-rewriting framework over
MLIR-style dialects, an LLVM dialect with the Alive/InstCombine corpus, a
**verified LLVM→RISC-V instruction selector**, a dialect zoo (FHE, CIRCT
hardware, structured control flow, tensors), and bitvector decision
procedures. Two facts frame the review: it is the only project in this
survey **on our exact toolchain** (Lean 4 nightly + Mathlib), and it is
precisely the "rung 1, foundationally" project from our clang-passes
discussion — verified InstCombine-style rewriting — already built, so any
pilot on our side starts from *consume/contribute*, not *build*.

## 1. The core framework: intrinsically typed SSA

(`LeanMLIR/LeanMLIR/Framework/Basic.lean`)

The IR is a **deep embedding, intrinsically well-formed**: no raw terms plus
a well-formedness predicate, but indexed inductives —

- `Expr d Γ eff ty`: one operation, indexed by dialect `d`, context `Γ`
  (a list of types; variables are *typed de Bruijn indices*
  `Ctxt.Var Γ t = { i // Γ[i]? = some t }`), an effect bound, and result
  types. The constructor carries proofs that the op's signature matches
  (`ty_eq`, `eff_le`); arguments are an `HVector` of typed variables;
  region arguments are nested `Com`s.
- `Com d Γ eff ty`: a sequence of let-bindings ending in a return of
  variables; each binding extends the context.

A **dialect** is a bundle of typeclass instances: `Dialect` (`Op`, `Ty`,
and a carrier monad `m`), `DialectSignature` (per-op argument/region/return
types and an `EffectKind`), `TyDenote` (types → Lean types), and
`DialectDenote` (per-op semantics into `eff.toMonad m`). `EffectKind` is a
two-point lattice `pure ≤ impure` with `pure.toMonad m = Id` — so pure
dialects denote as plain functions and impure ones monadically, with
`liftEffect` mediating. Denotation is a straightforward mutual recursion
into valuations (`Ctxt.Valuation Γ = ∀ t, Γ.Var t → ⟦t⟧`).

Design commitments stated in the source: **decidable equality** of ops and
types is demanded (the rewriter's matcher needs it); effects are *uniform*
per `Com` and regions are always impure (effect polymorphism is sketched as
future work); contexts are a newtype over `List Ty` to keep universes tame;
theorems are stated point-free in the last argument for monadic rewriting.
This is the opposite encoding choice from our LowIR (plain first-order
terms + separate well-formedness) — and lean-mlir honestly documents the
price (§3).

## 2. The verified rewriter

(`LeanMLIR/Transforms/Rewrite/`)

```lean
structure PeepholeRewrite (Γ : List d.Ty) (ts : List d.Ty) where
  lhs rhs : Com d (.ofList Γ) .pure ts
  correct : lhs.denote = rhs.denote
```

The engine: `splitProgramAt` (a zipper with a denotation-preservation
lemma), a **syntactic matcher** running in `StateT (Mapping Δ Γ) Option`
that unifies the pattern against the target's let-chain (pure bindings
only), substitution via context morphisms (`Ctxt.Hom`, weakening lemmas),
and re-insertion (`Zipper.insertPureCom`). The headline theorem:

```lean
theorem denote_rewritePeepholeAt (pr : PeepholeRewrite d Γ t)
    (pos : ℕ) (target : Com d Γ₂ eff t₂) :
    (rewritePeepholeAt pr pos target).denote = target.denote
```

with a fuel-based driver on top, and **axiom hygiene enforced in CI**:
`#guard_msgs in #print axioms` pins every core theorem to
`{propext, Classical.choice, Quot.sound}` — the README's "we never use
sorry for a core theorem" made machine-checked. The core also ships
verified **DCE** and **CSE** (context-shrinking with denotation-preserving
morphisms) — so "one verified engine, many cheap rules" is a working
pattern, not a slogan. MLIR concrete syntax enters via a generic MLIR AST +
parser and an elaborator (`elabIntoCom`, per-dialect `[foo_com| ...]`
macros, a `def_signature` macro for op signatures) — programs are written
in MLIR textual syntax *inside Lean files* and elaborated to intrinsically
typed terms at compile time.

## 3. The LLVM dialect and the Alive corpus

(`LeanMLIR/Dialects/LLVM/Semantics.lean`, `SSA/Projects/InstCombine/`)

Values are `LLVM.IntW w := PoisonOr (BitVec w)` — a newtype over `Option`
with `poison` as the UB-carrier: `nsw`/`nuw` overflow, division by zero,
`INT_MIN / -1`, oversized shifts all yield `poison`; `select`/binops thread
it monadically. **Refinement**, not equality, is the correctness relation:
`poison ⊑ anything`, `value a ⊑ value b ↔ a = b` — the same shape as
CompCert's `Vundef`/`lessdef` and Alive2's semantics, landed in Lean.

The Alive transfer: **93 InstCombine patterns** auto-translated from the
Alive suite (`update_alive_statements.py`) into paired theorems — an
MLIR-level SSA refinement (`src ⊑ tgt`, discharged by `simp_peephole`
plus a bitvector lemma) and the underlying pure `BitVec` statement. The
proof recipe is a tactic ladder (`TacticAuto.lean`): `simp_alive_undef`
(poison case-bash) → `simp_alive_ops` (dialect semantics → `BitVec`
goals) → `bv_auto` (bitwise/ring/AC normalizers) → **`bv_decide`**,
Lean's *kernel-verified* bitblaster. Roughly half the auto-generated
low-level statements still fall back to `sorry` when the ladder fails —
quantified honestly in `AliveStatements_sorry.lean`, with `Broken.lean` and
`Slow.lean` as a curated museum of failure modes, and `ScalingTest.lean`
measuring the elaborator cost of the intrinsic encoding (heartbeat budgets
growing super-linearly with nesting depth — the price tag on §1's encoding
choice, published rather than hidden).

The `bv-evaluation/` + `TacBench/` harnesses benchmark `bv_decide` against
external SMT (Bitwuzla) over the Alive, Hacker's Delight, and LLVM corpora
— this repo is simultaneously the main stress-test feeding Lean's
kernel-verified bitblasting upstream.

## 4. Verified instruction selection: LLVM → RISC-V

(`SSA/Projects/{RISCV64,SLLVM,LLVMRiscV}/`)

The most consequential recent growth — a verified lowering built *as*
peephole rewriting:

- **RISCV64 dialect**: RV64I+M+B (~80 ops) over a single type `BitVec 64`,
  SSA-level (no registers); instruction semantics imported from a
  **Sail-derived Lean library** (`SailRV64` in the lakefile), pseudo-ops
  hand-written against the ISA manual.
- **SLLVM** ("structured LLVM"): the LLVM dialect extended with memory —
  pointers, `load`/`store`/`alloca` over a block-indexed heap, and a proper
  side-effecting UB model: `EffectM := StateT GlobalState PoisonOr`,
  out-of-bounds/freed-block access → UB, division marked impure. This is
  the pure-bitvector dialect growing toward a real C-level IR, with
  refinement extended pointwise.
- **The lowering** (`LLVMRiscV`): a **hybrid dialect** whose ops and types
  are the disjoint union of LLVM's and RISC-V's, glued by
  `unrealized_conversion_cast` ops — exactly MLIR's idiom for progressive
  lowering, formalized. Each selection rule is a

  ```lean
  structure LLVMPeepholeRewriteRefine … where
    lhs rhs : Com LLVMPlusRiscV Γ .pure [Ty.llvm (.bitvec w)]
    correct : ∀ V, (lhs.denote V).getN 0 ⊑ (rhs.denote V).getN 0
      := by simp_lowering <;> bv_decide
  ```

  — LLVM op(s) on the left, cast-wrapped RISC-V instruction sequence on
  the right, correctness by refinement, discharged by the same tactic
  ladder. The pipeline is `DCE → constant matching → two pattern banks
  (all LLVM integer ops at i1/i8/16/32/64) → cast reconciliation → DCE →
  CSE`, fuel-bounded, with an optional GlobalISel-inspired pre/post
  combiner stage. One flagged wart: the equality-based rewriter interface
  is bridged to refinement rules via a `refinement_correctness` axiom —
  the framework's `correct : lhs.denote = rhs.denote` field hasn't yet been
  generalized to `⊑`, so the lowering's trust story has one axiom the core
  doesn't.
- **Evaluation**: thousands of mlir-fuzz-generated programs lowered by
  lean-mlir vs LLVM's `llc` (both SelectionDAG and GlobalISel), assembly
  compared, plus `llvm-mca` latency/throughput comparisons; register
  allocation and beyond are deliberately delegated to downstream (xDSL)
  tooling. In survey terms: CompCert's per-target `SelectOp` smart
  constructors, rebuilt as a *modular, automation-discharged rule set* over
  a hybrid dialect — a miniature verified -O0 backend in Lean.

## 5. The dialect zoo and solver tools

Breadth as an existence proof that the framework generalizes: **FHE**
(polynomials over `Z_q[X]/(X^(2^n)+1)` via Mathlib ring theory, modeling
HEIR's Poly dialect, with verified rewrites), **Scf** (structured `for`/
`if`/`while` as a dialect *functor* over a base dialect — regions in
action, loop-invariant and iteration-composition theorems), **CIRCT**
(Handshake dataflow circuits with `Stream α := ℕ → Option α` corecursive
semantics, determinacy analysis of `merge`, and a verified
Handshake-to-HW `fork` lowering), tensors (`Tensor1D/2D`, `Holor`
rank-polymorphic skeleton), `ModArith`, ISL/polyhedral stubs. Alongside:
**Blase** (a sound-and-complete decision procedure for *parametric-width*
bitvector formulas — width-independent reasoning, the OOPSLA'25 line),
**Medusa** (formula generalization), **SexprPBV** (the shared PBV AST).
Engineering discipline is explicit: a core-vs-projects "research codebase
manifesto" (core is CI-guarded and axiom-checked; projects may be rough),
auto-generated docs, Mathlib nightly tracking.

## 6. Trust story

The framework core is axiom-clean (machine-enforced). What's trusted:
**semantics faithfulness** — the LLVM dialect's poison/overflow rules are
aligned with Alive2 and the LangRef by inspection, not by proof (same gap
every LLVM formalization has); the **Alive→Lean translation** scripts; the
Sail-to-Lean provenance of RISC-V semantics; `bv_automata`-style external
backends where used (unlike `bv_decide`, not kernel-checked); the
`refinement_correctness` bridging axiom in the lowering; and every
remaining `sorry` in the auto-generated Alive files (tracked, not hidden).

## 7. Takeaways

1. **This is a dependency candidate, not just a reference.** Same
   toolchain, Mathlib-compatible, axiom-audited core. The clang-side pilot
   we sketched ("one InstCombine family, a Lean semantics, a verified
   checker") exists here at 93-pattern scale with its automation ladder —
   the realistic move is contributing patterns/proofs or reusing
   `PoisonOr`+`bv_decide` recipes, not rebuilding.
2. **The rewriter-as-framework pattern** — one verified engine
   (`denote_rewritePeepholeAt`) + rules as `{lhs, rhs, proof}` records +
   tactic-automated rule proofs — is the cleanest instance in this survey
   of "prove the engine once, make each optimization a lemma." If LowIR
   grows a rewrite-based optimizer, this is the architecture, and
   `bv_decide` is the workhorse for its word-level side conditions.
3. **Encoding economics, measured**: intrinsic typing buys a
   no-well-formedness-lemmas rewriter but costs elaborator time
   (`ScalingTest`'s heartbeat curves) and ergonomic wrappers. Our
   extrinsic LowIR encoding sits on the other side of exactly this trade;
   lean-mlir is the data point to cite when the question resurfaces.
4. **Refinement vs equality in the rewriter interface** — the
   `refinement_correctness` axiom wart is a design lesson for our
   `compile_sim`: build the engine on the *order* (refinement), not the
   equivalence, from day one; equalities embed trivially, the converse
   needs an axiom.
5. **The hybrid-dialect lowering idiom** (union dialect +
   conversion casts + progressive rewriting + cast reconciliation) is a
   modular alternative to monolithic instruction-selection passes, and it
   composes with fuzz-based differential testing against the production
   compiler — the same validate-against-reality instinct as our QEMU
   cross-checks.
6. **A Lean-side Sail RISC-V semantics exists** (`SailRV64`). Our ISA
   cross-check program (task #7: riscv-coq agreement) has a natural third
   leg: Lean model ↔ SailRV64 ↔ riscv-coq — worth an exploratory look
   before we ever hand-extend our 16-encoding surface.
