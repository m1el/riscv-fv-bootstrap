# RadixExperiment — design choices

An analysis of `third-party/RadixExperiment/`: **Radix**, a verified imperative DSL
embedded in Lean 4, plus a [Verso](https://github.com/leanprover/verso)-based slide
deck ("Lean for AI, AI for Lean") presenting it. Per its README, the DSL was built
entirely by 10 Claude agents in a single weekend, with zero human-written lines and
zero `sorry`s (52 theorems). The git history in the checkout is the *slides* repo
(all commits by Leonardo de Moura / Lean FRO); the Radix sources were developed
elsewhere and copied in at commit `af10f68` ("Copy Radix source into slides project").
Toolchain: `leanprover/lean4:v4.29.0-rc1`.

This document records the design decisions visible in the code and, where the
sources say so, the rationale. The overarching theme: **every language-design
decision is bent toward making the correctness proofs tractable**. Radix is a
proof-shaped language.

## 1. Architecture

Classic compiler pipeline — AST → type check → optimize → interpret — one Lean
module per stage:

| Module | Role |
|---|---|
| `Radix/AST.lean` | Types, values, operators, `Expr`, `Stmt`, `FunDecl`, `Program` |
| `Radix/Env.lean`, `Heap.lean`, `State.lean` | Runtime: variable env, heap, frame-stack state |
| `Radix/Eval/Expr.lean` | Pure expression evaluator (`Option Value`) |
| `Radix/Eval/Stmt.lean` | Relational big-step semantics (`BigStep`, 16 rules) |
| `Radix/Eval/Interp.lean` | Executable fuel-based interpreter |
| `Radix/TypeCheck.lean` | Expression-level type inference |
| `Radix/Syntax.lean` | Concrete-syntax macros `` `[RExpr\|…] ``, `` `[RStmt\|…] `` |
| `Radix/Opt/*.lean` | 5 verified passes: const fold, DCE, copy prop, const prop, inlining |
| `Radix/Proofs/*.lean` | Determinism, type safety, memory safety, interpreter correctness |
| `Radix/Linear.lean` | Linear ownership typing + soundness (the largest single file, 643 lines) |
| `Radix/Tests/*.lean` | `#guard`-based test suite |
| `Slides.lean`, `Main.lean`, `static/` | Verso/reveal.js deck + HTML post-processing |

## 2. Language design

### Expressions are pure; function calls are statements only

`Expr` has no call constructor; calls exist only as `Stmt.callStmt` (which discards
the return value into the frame machinery). The AST header states the rationale
explicitly: expression purity "simplifies the semantics considerably". Concretely:

- `Expr.eval : PState → Expr → Option Value` is a plain total function — no fuel,
  no state threading, no mutual recursion with statements.
- Every expression-level rewrite (const fold, copy prop, const prop) only has to
  preserve `Expr.eval`, a first-order equation, instead of a simulation over the
  full `BigStep` relation.
- The big-step rules can take `e.eval σ = some v` as a premise rather than a
  sub-derivation.

The cost is expressiveness (no `y := f(x) + 1`), accepted deliberately.

### Partiality via `Option`, uniformly

There is no distinguished error value and no exceptions: every partial operation
(`Expr.eval`, `Heap.read/write/free`, `PState.setVar`, `BinOp.eval`) returns
`Option`, with `none` covering type mismatch, division by zero, out-of-bounds
access, invalid free, and missing frames alike. Errors are not distinguished from
each other at the semantics level — a program with a runtime error simply has *no*
`BigStep` derivation. Only the executable interpreter refines `none` into
human-readable `Except String` messages. This makes "the optimizer must not turn a
failing program into a succeeding one" the central soundness concern (see §5,
constant folding).

### Value representation borrows the host

- `uint64` wraps Lean's `UInt64`, so wrap-around machine arithmetic (including
  `neg` as `0 - n`) comes for free instead of being axiomatized.
- `str` wraps Lean's `String`; string ops use the host implementation directly.
- `addr : Nat` is a **runtime-only** value: there is no source-level address type,
  `Ty` has `array` instead, and the type checker rejects address literals
  (`typeOf (.lit (.addr _)) = none`). Addresses arise only from `alloc`.
- `Ty.fn` exists in the type grammar but is unused ("for potential future use") —
  there are no function values or closures.

### The `scope` construct: inlining without substitution

`Stmt.scope params args body` is an internal statement form — not producible from
concrete syntax — representing an inlined call: push a fresh frame binding
`params` to the evaluated `args`, run `body`, pop. The inliner rewrites
`callStmt f args` into `scope f.params args f.body` **without substituting
arguments into the body**. A capture-avoiding substitution (`substParams`) exists
in `Opt/Inline.lean` but is not used on the main path.

This is the clearest example of proof-shaped design: because `scope`'s big-step
rule is field-for-field identical to `callStmt`'s minus the table lookup, the
inlining correctness proof for the call case is a one-line rule swap. The price is
that "inlining" removes only the function-table indirection, not the frame
push/pop — it is semantically honest but yields little real optimization. The
alternative (true substitution) would have required a capture/freshness story and
a much harder proof.

## 3. Runtime-state design

### Frame stack, no lexical scoping

`PState` = list of `Frame`s (head = current) + `Heap` + function table. Variable
lookup and mutation touch **only the topmost frame**: no closure capture, no
access to outer frames, no globals. Callee and caller communicate only via
by-value arguments and the shared heap (the README's `zeroArray` example
demonstrates heap communication deliberately). `Stmt.decl` and `Stmt.assign` have
*identical* semantics (both are `setVar`); declarations exist only for future
statement-level type checking. `Frame.retVar` is reserved-but-unused — calls
cannot yet deliver a return value to the caller.

Payoff in the proofs: `BigStep.frames_tail` (execution never touches frames below
the top) and `PState.getVar_scope` (a call/scope leaves every caller variable
unchanged) are the two lemmas that make the linear-ownership call cases go
through.

### Heap: bump allocator that never reuses addresses

`Heap` = `HashMap Nat (Array Value)` + monotone `nextAddr`. `free` erases the
mapping but never decrements or recycles the counter. The header is explicit that
this is for the proofs: freshness of a new allocation (`alloc_fresh`) follows from
the single well-formedness invariant `∀ a ∈ store, a < nextAddr`, and
`no_use_after_free` / `no_double_free` become one-lemma facts about `HashMap.erase`.
A realistic allocator with reuse would destroy the "freed addresses stay dead"
property that the memory-safety theorems state.

Note the honest scoping in `Proofs/MemorySafety.lean`: the three theorems there
(`no_use_after_free`, `no_double_free`, `read_within_bounds`) are properties **of
the heap API**, not of programs — the header says so and defers program-level
memory safety to the linear ownership layer (§6).

### `block` as a fold

`Stmt.block stmts` has a single big-step rule that delegates to
`stmts.foldl (· ;; ·) .skip`. Blocks are thus semantically *defined* as
right-nested sequencing with a leading `skip`, avoiding a list-indexed inductive
rule. The recurring cost shows up in every optimization proof as `foldl`-shuffling
lemmas (`BigStep.foldl_seq_mono`, `inline_foldl_seq`, `dce_foldl_gen`).

## 4. Two semantics, connected

The reference semantics is the relational `BigStep : PState → Stmt → StmtResult →
Prop` (16 rules). Alongside it, `Stmt.interp : Nat → Stmt → PState →
Except String (Option Value) × PState` is a fuel-based executable interpreter
(default fuel 1000). They are formally connected in
`Proofs/InterpCorrectness.lean`:

- **Fuel monotonicity** (`interp_fuel_mono`): success at fuel `n` is preserved at
  any `m ≥ n` — the lemma that makes "∃ fuel" statements composable.
- **Completeness** (`interp_complete`): a `BigStep` derivation yields *some*
  sufficient fuel.
- **Soundness** (`interp_sound`): interpreter success yields a `BigStep`
  derivation.

Two supporting choices:

- **Early return** is encoded in the result type: `StmtResult = normal σ ∣
  returned v σ`, with `seqReturn` short-circuiting sequences and three `while`
  rules (`whileTrue`/`whileReturn`/`whileFalse`). The interpreter mirrors this
  with `.ok none` vs `.ok (some v)` and an `andThen` combinator, giving a clean
  bisimulation between the two shapes.
- **Determinism** (`BigStep.det`) is proved first and framed as the theorem that
  *upgrades* every optimization result: `BigStep σ s r → BigStep σ s.opt r` alone
  only says the optimized program *can* behave like the original; determinism
  makes that observational equivalence. The determinism proof is also the
  showcase for `grind` (all equational/injectivity cases), with manual induction
  only for the recursive rules.

## 5. Verified optimizations: soundness-first, precision-second

All five passes share one correctness contract, `BigStep σ s r → BigStep σ (opt s)
r`, and one design ethic: **when a transformation's soundness would need an
analysis the project doesn't have, drop the transformation, not the theorem.**
Instances:

- **Constant folding** (`Opt/ConstFold.lean`) implements identity rules
  (`e + 0 → e`, `true && e → e`) but *refuses* absorb rules (`e * 0 → 0`). The
  header explains why: if `e.eval σ = none`, the original fails but the rewrite
  succeeds with `0` — unsound under Option-partiality. Identity rules are instead
  guarded by a small structural type inference (`Expr.inferTag` with soundness
  lemma "if `e` evaluates at all, the value has this tag"), which is exactly
  strong enough to justify them. Absorb rules are documented as requiring a
  totality-guaranteeing type system.
- **Dead code elimination** (`Opt/DeadCode.lean`) only simplifies control flow
  (`if (true/false)`, `while (false)`, `skip` elimination in `seq`/`ite`). A
  `readVars` analysis is fully implemented but *unused*: dead-*store* elimination
  would need liveness reasoning, so it was built up to the sound boundary and
  stopped.
- **Copy propagation** and **constant propagation** (`Opt/CopyProp.lean`,
  `Opt/ConstProp.lean`) are forward dataflow passes threading a
  `HashMap`-based fact map through statements. At every control-flow join
  (`if`/`else` merge, `while` body, calls) the map is **reset to empty** rather
  than intersected — losing precision, keeping the invariant trivially valid on
  both paths. Both proofs follow the same template: define an `agrees` predicate
  (`CopyMap.agrees m σ`: every `x ↦ y` in the map satisfies `σ.getVar x =
  σ.getVar y`; analogously for constants), prove expression-level substitution
  correct under `agrees`, then induct over `BigStep` showing `agrees` is
  maintained. ConstProp additionally runs constFold on each rewritten expression,
  so `x := 5; y := x + 1` folds to `y := 6`.
- **Inlining** (`Opt/Inline.lean`) is heuristic (body size ≤ 10, non-recursive by
  a syntactic `containsCall` check) and **depth-bounded** — the `depth` parameter
  is what makes the inliner terminate, since it recurses into the inlined body.
  The correctness theorem is quantified over all depths and needs one extra
  hypothesis, `σ.funs = funs`, tying the static function table used by the pass
  to the runtime one; the supporting invariant `BigStep.funs_preserved` (the
  function table is never mutated by execution) is proved alongside. As noted in
  §2, inlining targets `scope`, so no substitution lemma is needed.

## 6. Type system: two disconnected layers

### Expression typing + preservation only

`TypeCheck.lean` provides `Expr.typeOf : TyEnv → FunSigs → Expr → Option Ty` —
expression-level inference only; statement-level checking is explicitly "not
implemented". `Proofs/TypeSafety.lean` proves **preservation** (a well-typed
expression that evaluates yields a value of the inferred type), parameterized by
two semantic hypotheses instead of full judgments: a well-typed-environment
assumption and a heap-typing assumption `hheapTy` (heap cells of an
array-typed expression have the element type) — i.e. heap typing is assumed at
the theorem boundary rather than defined and threaded as its own invariant.

**Progress is deliberately absent**, with counterexamples documented in-file:
`e / 0`, out-of-bounds `arr[i]`, out-of-bounds `s[i]` are all well-typed yet
evaluate to `none`. The file notes a correct formulation would need totality
judgments or strengthened preconditions. Same ethic as §5: state exactly what is
true, don't force the classical theorem-pair.

### Linear ownership as an opt-in second type system

`Linear.lean` layers a flow-sensitive judgment `LinearOk O s O'` ("statement `s`
transforms owned-variable-set `O` into `O'`") *on top of* the untyped semantics,
rather than integrating ownership into `Ty`. Its rules are deliberately
restrictive and syntactic:

- `alloc x` requires `x ∉ O` and adds it; `free` applies only to the syntactic
  form `free (.var x)` with `x ∈ O` and removes it; `arrSet` requires the base to
  be a syntactically owned variable.
- Plain `assign`/`decl` require the target `x ∉ O` — you cannot overwrite (and
  thereby leak or alias) an owned pointer.
- Branches must agree on the outgoing set (`ite` rule forces both arms `O → O'`);
  `while` bodies must be ownership-neutral (`O → O`).
- Calls: `callStmt` leaves `O` untouched but the soundness theorem requires
  `WellTypedFuns` — every function body in the table is *balanced* (`∅ → ∅`,
  every alloc matched by a free). `scope` likewise requires a balanced body.

The soundness invariant `OwnershipInv σ O` has three conjuncts: heap
well-formedness (`a < nextAddr` for all stored `a`), **liveness** (every owned
variable holds an address that is live in the heap), and **pairwise
non-aliasing** (distinct owned variables hold distinct addresses). The
non-aliasing conjunct is what makes the `free` case work: freeing `x`'s address
cannot kill any other owned variable's address.

The proof (`soundness_core`, the bulk of the 643-line file) is a textbook
**strengthened induction**: the naive statement (invariant in ⇒ invariant out)
isn't inductive, so it is proved as a three-part conjunction — (A) `OwnershipInv`
preserved on normal termination, (B) heap well-formedness preserved for *all*
results including returns, (C) a frame property: any live address separated from
all owned variables stays live and stays separated. Part C is precisely what the
call/scope cases need — the callee runs with `O = ∅`, so the caller's owned
addresses are "non-owned live addresses" from the callee's perspective and
survive by (C), then `getVar_scope`/`popFrame_heap` transport the invariant back.
User-facing corollaries: `LinearOk.soundness`, `live_access` (owned ⇒
dereferenceable), and `balanced` (∅→∅ programs preserve heap well-formedness).

This is the project's answer to the gap admitted in `MemorySafety.lean`:
program-level no-use-after-free is obtained not from the simple type system but
from this linear layer, and only for programs that pass the (restrictive)
`LinearOk` judgment.

## 7. Concrete syntax: macros over a fresh grammar

`Syntax.lean` embeds Radix's surface syntax with Lean 4 `macro_rules`, using a
hybrid grammar strategy:

- **Expressions reuse Lean's `term` grammar**: `` `[RExpr| x + y * 2] `` pattern-
  matches on ordinary Lean terms (`$x + $y`, `$a[$i]`, numeric/string literals,
  identifiers) and re-quotes recursively. Radix inherits Lean's precedence and
  parenthesization for free; no expression grammar is declared. Helper macros
  (`arrLen(…)`, `strLen(…)`, `strGet(…,…)`) cover forms with no Lean-term analog.
- **Statements get a dedicated syntax category** (`rstmt`) with C-like forms:
  `x := e;`, `let x : T = e;`, `let x := new T[n];`, `if (c) {…} else {…}`,
  `while (c) {…}`, `return e;`, `f(a, b);`, `arr[i] := v;`. A `rty` category
  handles types (`uint64`, `bool`, `string`, `unit`, postfix `[]` for arrays).
- `free(e)` is not a keyword: the generic call macro string-matches the callee
  name `"free"` and emits `Stmt.free` (checking arity at macro-expansion time) —
  a pragmatic special case that keeps the grammar small.
- Statement sequences are assembled by a right-recursive rule (`$s $ss*` →
  `seq`), and array-write targets are restricted to identifiers.

Because the macros elaborate to plain AST constructors, every README/slide
example is type-checked and (via `#eval!`/`#guard`) *executed* by the Lean
elaborator itself.

## 8. Testing and verification methodology

- **Tests are `#guard`s** (143 across `Tests/*.lean`), i.e. decidable assertions
  checked at elaboration time: `lake build` succeeding *is* the test run. Tests
  compare `Stmt.run`/`Program.run` output values against expected `Value`s, per
  feature area (basic, functions, arrays, strings, opts, linear).
- **Proof style**: `@[simp]` on the evaluators (`BinOp.eval`, `UnaryOp.eval`,
  the tag machinery) so concrete cases discharge automatically; `grind` for
  equational/injectivity case-bashing (determinism); structured `induction …
  with` and explicit lemma chains for the real content (Linear, InterpCorrectness,
  CopyProp). Helper lemmas consistently come in `unfold`-style pairs
  (`setVar_unfold`, `alloc_unfold`, `free_unfold`) that convert opaque
  `Option`/`Prod` equations into structural facts once, then get reused.
- **Scoping honesty as a discipline**: every theorem that is *weaker* than its
  textbook name suggests says so in a docstring (heap-API-only memory safety, no
  progress theorem, absorb rules omitted, statement typing missing). For a
  fully-AI-written artifact this is notable: the limits are documented in-repo,
  not just claimed.

## 9. The slide deck (Verso)

The deck (`Slides.lean`) is the actual deliverable — "Lean for AI, AI for Lean" —
and its build is itself a design point:

- Slides are written in Verso markup with **embedded real Radix code**: the code
  blocks are elaborated against the actual library (commit `6de9628` "all code
  blocks reference actual theorems"), so the presentation cannot drift from the
  code. This mirrors the project's thesis (AI produces machine-checked artifacts;
  Verso as the authoring layer).
- `Main.lean` is the build entry point and does aggressive **HTML
  post-processing** on the reveal.js output: injecting custom CSS and a logo
  header per slide, setting `disableLayout` in `Reveal.initialize`, and inlining
  the Verso hover-info JSON directly into `highlighting.js`/`panel.js` so the
  deck works when opened as a local `file://` page (no fetch/CORS). String
  `replace` on generated HTML/JS is fragile but pragmatic for a one-off deck.
- Lake setup: `require «verso-slides»` from git; two libs (`Radix`, `Slides`) and
  one default exe (`radix-slides`) that renders to `_out/`.

## 10. Takeaways

Recurring moves worth stealing (several rhyme with this repo's own methodology):

1. **Shape the language around the proof**: pure expressions, statement-level
   calls, no-reuse bump heap, `scope` instead of substitution — each removes a
   whole lemma family. Radix shows how far that gets you in a weekend (52
   theorems) and what it costs (a language you couldn't ship).
2. **Reference relation + executable interpreter + sound/complete bridge** is the
   same two-semantics pattern as our `BigStep`/fuel splits; fuel monotonicity is
   the load-bearing composition lemma there too.
3. **Precision is negotiable, soundness is not**: reset dataflow maps at joins,
   drop absorb rules, skip dead-store elimination. Every pass ships with its
   theorem because the pass was weakened until the theorem held.
4. **Strengthened-conjunction induction** (`soundness_core`'s A/B/C split, with a
   frame-style part C for calls) is the standard trick for ownership/heap
   invariants across frame push/pop.
5. **Balanced-callee obligations** (`WellTypedFuns`: all bodies `∅ → ∅`) are how
   the linear system gets modular calls without interprocedural analysis —
   compare our frame-based cross-call disjointness treatment in LowIR.
