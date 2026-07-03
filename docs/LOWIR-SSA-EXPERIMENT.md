# LowIRSSA — SSA/value-flavored variant of the Prog IR (experiment)

Status: **design experiment**, user-directed, 2026-07-02. Code:
`lean/LowIR/SSA.lean` (lib `LowIRSSA`, in `defaultTargets`; executable `#guard`
battery, no proofs). Companions: [LOWIR-DESIGN.md](LOWIR-DESIGN.md) (D7/D8 and
the explicit not-SSA decision this experiment probes),
[RESUME-PROGSIM.md](RESUME-PROGSIM.md) (the campaign this must not disturb).

## What it is

`LowIR.SSA` is `LowIR.Prog` (D7 calls + D8 frames) re-shaped so that control
constructs *produce values* and registers are single-assignment:

| Piece | Prog (D7/D8) | SSA experiment |
|---|---|---|
| registers | mutable locals | defined once per function (params, frameReg, op dests, `outs`, loop `args`); enforced by a decidable checker |
| outcomes | `brk k / cont k / ret` bare | **carry `List Word`** — jumps transport values |
| function results | `rets : Vector Reg rvc` read at the boundary | **arity only** (`rvc`); `ret [operands]` carries the values; `run` returns them directly |
| `block` | pure break scope | `block (outs) body` — `brk 0 [vs]` binds `outs`; body must not fall through (except `outs = []`) |
| `ife` | transparent to brk indices | **its own break scope** (Wasm-style): arms deliver `outs` via `brk 0 [vs]`, or are `.never` (e.g. `ret`) — then `outs` need no initialization on that path |
| `while` | cond over mutable regs, body falls through and re-loops | **block-parameter loop**: `while (outs) (inits) (args) c a b body dflt` — `args` are the φ-nodes, bound to `inits` on entry and rebound by `cont 0 [vs]` ("iteration is a tail call"); exits deliver `outs` |
| operands | registers only (+ x0) | `Opnd = .reg r \| .const v` at value-flow sites (brk/cont/ret args, inits, call args) |
| statement type | — | `.never` (fall-through unreachable) vs `.thru`, computed by the checker |

Omitted as orthogonal (would port verbatim from Prog): const data
(`cref`/`clen`/`Program.data`), the P1 `pad` oracle, `execT` footprints.

Tooling: `lean/LowIR/SSADump.lean` (the `LowIR.Dump` sibling, reusing its
rendering helpers) pretty-prints SSA functions/envs as WAST-flavoured
s-expressions — `brk`/`ret` as multi-value `(br k v…)`/`(return v…)`,
`block`/`if` results as named `(outs $rN…)` binders, `while` with its
`(init …) (args …)` block-parameter plumbing and `(default …)` body. The
SSA IR sits noticeably closer to the Wasm text idiom than Prog does.

## Decisions made where the sketch was ambiguous

1. **`defaultBody` runs on EVERY guard-false, with the current `args` in
   scope** — not only when the loop is never entered. The user's first sketch
   had `defaultOut : List Opnd` (outer-scope values); that design *discards
   loop-carried values on a guard exit* — a sum loop exiting via `i > n` would
   return the outer default, not the accumulated sum, so every value-carrying
   loop would be forced onto explicit `brk` exits and the guard would be dead
   weight. The mid-flight switch to a `defaultBody` *statement*, given `args`
   in scope, fixes this: the guard exit runs `dflt`, which can
   `brk 0 [.reg acc]`. This is exactly MLIR `scf.while`'s before-region /
   Cranelift's block-param shape. The zero-trip case falls out: `dflt` then
   sees `args = inits`. (`sumTo`/`sumCap` in the battery exercise both.)
   `dflt` shares the loop's scopes, so it may even `cont 0` to restart.
2. **Loop bodies are `.never`-typed**: `body` and `dflt` must end in
   `cont`/`brk`/`ret`. There is no implicit fall-through-and-loop (it couldn't
   rebind `args` anyway). `ife`/`block` arms may fall through only when
   `outs = []` (the user's "`.value 0` doesn't need destructuring").
3. **Scope shape**: `ife` shifts brk indices (it catches `brk 0`), unlike
   Prog; `while` is now *both* a break scope (`brk 0` exits with `outs`) and a
   continue scope (`cont 0` re-enters) — in Prog/Ctrl it was continue-only,
   with breaks targeting an enclosing `block`.
4. **SSA is a checker, not intrinsic typing** (the N3 "checker produces the
   hypothesis" pattern): the semantics stays a total, clocked, mutable-file
   big-step (`exec`, Prog's exact shape); `wfFun` = definition census (each
   register textually defined at most once; x0 exempt as a discard) + a
   use/arity/type pass (`check`) threading the dominance-approximating
   `avail` set and the label contexts `brks`/`conts : List Nat` (the arity of
   each enclosing break/continue target). The user's `.value (Vect n Word)`
   type lives in those arity contexts; the statement type proper is just
   `.never | .thru`.
5. **Never-detection needs may-brk information**: an `ife` whose arms are both
   `.never` can still be fallen out of *via its own `brk 0`*. This is the Wasm
   validator's "unreachable polymorphism" in miniature; approximated here by
   the syntactic `mayBrk` over-approximation (cheap, admits some dead code,
   never rejects live code).
6. **Loop iteration in `exec` rebinds in the environment** (reworked
   2026-07-03, RESUME-SSA-HEX0.md §8; originally it *rebuilt the term* with
   `inits := consts of the continued values`, which forced while-lemmas to
   quantify over `inits` and pay a `.map .const` round-trip per iteration).
   Now `exec` evaluates `inits` ONCE and hands off to `iterWhile`, a budgeted
   iterator that rebinds `args := vals` per head entry and recurses on the
   SAME term with the continued values — loop lemmas are stated directly over
   the value tuple; `iterWhile_mono`/`iterWhile_frame` give the loop halves of
   `exec_mono`/`exec_frame`.

## What the battery validates (all `#guard`, executable)

The user's exact `if` example (a `.never` arm returning directly, out register
uninitialized on that path); value-producing blocks; `sumTo` with a
guard-exit that *carries* the loop-carried accumulator + the zero-trip case;
`brk 1` escaping an `ife` into the enclosing `while` while `cont 0` passes
through the `ife` unshifted; multi-value returns with no return registers;
D8 frames + recursion + stack-overflow trip under SSA names; and 7 checker
negatives (double def, use-before-def, arm-local escaping its join, brk arity
mismatch, fall-through loop body, missing return, dead code after `.never`).

## Port pilot: strlen and hex0 from ProgLib (2026-07-02)

`lean/LowIR/SSALib.lean` ports `strlenF`/`hex0F` from `ProgLib.lean` onto the
SSA IR, validated the same way as the originals: the SSA checker passes
(`wfEnv`), and `native_decide` confirms hex0 ≡ `Hex0.coreSpec` on the full
Ctrl battery and strlen on the string battery — results read from the
returned value list, no boundary register convention. What the port showed:

- **The error cascade dissolves.** Prog's `err code = (x14 := code); ret`
  plus "x14 initialized 0, read at the boundary" becomes a literal
  `ret [.const code, .reg n]` at each failure site; the success exit is the
  loop guard's `defaultBody` returning `[.const 0, .reg n]`. Registers x14
  (status), x15 (comment-guard flag) and x16 (the constant 1) vanish from
  hex0 entirely.
- **`pnib` becomes a value-producing `ife`.** The 5-leaf decision tree that
  in Prog assigns its dst on every leaf and falls through now `brk k [v]`s
  each leaf to the outs-carrying root; the 255 sentinel leaves are `.const`
  operands — no register holds them (x19 remains only for the *comparison*
  against the sentinel, since `Cond` is register-only).
- **`skipComment` is the design's best moment.** Prog computes a guard bit
  into x15 (`cgGuard`, duplicated before the loop and in the body) and loops
  on `x15 ≥u 1`; the SSA version is an always-true inner loop whose two exits
  `cont 1 [pos, n]` — continuing the OUTER scan loop directly across the
  inner one, the tail-call framing made literal. No flag, no re-computed
  guard, and EOF needs no poison: the outer guard just fails.
- **strlen's load-bearing guard survives**: the guard can't do a load, so the
  current byte rides as a second loop arg, loaded before each `cont` and
  seeded before the loop — the standard block-param idiom, and the guard-exit
  `defaultBody` computes `cur − p` from the final args.
- **The honest cost is scratch-register naming.** Prog reuses x30/x31 at
  every site; textual def-once forces a fresh name per site, so helpers
  (`pnibS`, `skipCommentS`) take their scratch registers as parameters and
  hex0 allocates ~20 extra names. Every dispatch arm must end in an explicit
  `cont`/`ret`. A `seqs` variant without the trailing `.skip` was needed too
  (`seqs1`) — dead code after a `.never` tail is rejected by design.
- Net size: comparable to the Prog version (the removed status/guard plumbing
  roughly pays for the explicit continues).

## Assessment — suggestions and criticism

1. **The keeper: lower SSA → Prog; do not fork the compiler.** With Prog's
   unbounded registers, out-of-SSA is nearly syntactic: give every SSA name a
   Prog register; a `cont 0 [vs]` edge becomes a parallel copy into the `args`
   registers, and the classic lost-copy/swap hazard dissolves by staging
   through fresh temporaries (always available — registers are infinite).
   Register *pressure* stays where it already lives, in Prog's future
   allocator (`compile_sim` pass 3). So LowIRSSA's right position is the first
   rung of the **higher-IR ladder** (LOWIR-DESIGN Ext. 5/10), lowering to Prog
   by a structural, machine-free pass — and the entire ProgSim campaign is
   reused unchanged. Building a second Stmt→RV64I compiler for it would be a
   mistake.
2. **What SSA actually buys at proof time**: loop invariants become *local* —
   the induction hypothesis of a `while` proof is a statement about the `args`
   tuple, read off the `cont` sites, instead of an invariant over a mutable
   register file plus a per-proof "all other registers unchanged" frame
   clause. Outer-name immutability is a **once-proved SSA frame theorem**
   ("exec of a checked statement changes only its `defs`"), the same
   pay-once economics as `compile_sim`. That, plus valued returns killing the
   rets-register convention, is the real ergonomic content of the experiment.
3. **Severable pieces** — worth taking even if SSA itself is not:
   - *Valued `ret`* (outcome carries the results): removes the "read the
     callee's `rets` registers at the boundary" convention from D7 with no SSA
     needed. Cost: touches `exec`/ExecFacts/StmtSim in the live campaign — a
     post-campaign retrofit, not a now one.
   - *`Opnd .const` operands* at jump/call sites (kills addi-a-constant
     staging), and `Cond` over operands.
   - *`.never` typing* as an extension of Ext. 8's `wf`: even on Prog it would
     give "all paths return" and dead-code rejection.
4. **Honest costs**: textual def-once means sibling `ife` arms cannot reuse a
   name (stricter than dominance-SSA; irrelevant for generated code, mildly
   annoying handwritten); `mayBrk` over-approximation types some dead joins
   `.thru` (accepts dead code — harmless, semantics is total); the `check`
   pass carries more moving parts than Prog's `wf` (label arities + avail
   threading), which a soundness proof will have to pay for once.
5. **Where it earns its keep / trigger to graduate**: if the borrow-checker
   layer (Ext. 5) lands, its natural carrier is exactly this IR — borrow
   signatures attach to single-assignment names far more cleanly than to
   mutable registers (no reborrow-vs-overwrite ambiguity). Graduation =
   (a) the SSA frame theorem + checker soundness lemma, (b) the SSA→Prog
   lowering + its simulation proof, (c) porting one ProgLib function as the
   pilot. Until something needs (a)–(c), this stays a frozen experiment;
   D7's "explicitly not SSA" decision for *Prog itself* stands unrevised.
   The proof half of the graduation test now has a written plan:
   [RESUME-SSA-HEX0.md](RESUME-SSA-HEX0.md) — prove `hex0S` ≡ `Hex0.coreSpec`
   and measure the proof section-by-section against `CtrlHex0Proof.lean`.
