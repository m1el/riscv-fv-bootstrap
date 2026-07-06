# Build profile — where the proof compile spends its time

Measured 2026-07-06 at commit `e3a4300`, Lean 4.30.0 / Lake 5.0.0, on a 64-core
box. The `lean/` corpus has **no external dependencies** (no Mathlib/Batteries),
so every number below is pure project cost. Reproduce with:

```sh
cd lean && lake clean
/usr/bin/time -v lake build > ../runs_tmp/full-build.log 2>&1   # per-module wall times
# per-tactic/phase breakdown for one module (oleans of its deps must exist):
lake env lean -Dprofiler=true -Dprofiler.threshold=200 <Module.lean>
```

`lake build`'s `✔ [n/65] Built X (Ns)` lines give per-module wall time; the
`-Dprofiler` `cumulative profiling times:` block gives the per-phase breakdown
(those totals are summed across Lean's intra-file elaboration threads, so they
exceed the module's own wall time — read them for *ratios*, not absolutes).

## Headline

- **Clean build: ~149 s wall** (2:29), **644 s CPU**, peak RSS ~2.0 GB.
- Incremental rebuild with no source changes: near-instant (olean cache).
- **Avg parallelism ≈ 4.3× of 64 cores.** The build is **critical-path /
  dependency bound, not core bound** — more cores barely help. A long serial
  chain in the Hex1 rung sets the wall-clock floor.

## Where the time goes — by module

| Module | Wall | What dominates |
|---|--:|---|
| `RawAsm/Hex1/Refine.lean` | **104 s** | 1943 `decide` + 837 `omega` + 594 `simp` |
| `RawAsm/Hex1/Certify.lean` | **99 s** | 7 `native_decide` (compile-to-native + run) |
| `RawAsm/Hex1/Validate.lean` | 38 s | 1 `native_decide` |
| `LowIR/ProgSim/CtrlSim.lean` | 23 s | 323 `omega` + 206 `simp` |
| `LowIR/CompileTests.lean` | 23 s | differential `native_decide` |
| `RawAsm/Hex1/RefineBase.lean` | 17 s | 204 `decide` + 196 `omega` |
| `RawAsm/Hex1/DecodeFacts.lean` | 14 s | 182 `decide` (decode table) |
| `LowIR/ProgSim/EncodeFacts.lean` | 12 s | typeclass inference + type checking |
| `RawAsm/Hex0/Refine.lean` | 10 s | `decide`/`omega` (hex0 analogue) |

Everything below this is ≤10 s. The **Hex1 rung** (`RefineBase → Refine →
Certify → Validate`, plus `DecodeFacts`) is ≈272 s CPU — ~42% of the whole
build — and because those modules form a dependency chain they run essentially
serially. That chain, not core count, is what pins the 149 s wall.

## Where the time goes — by tactic / phase

Three cost centers, in order of impact:

1. **`decide` at scale** — `Refine`, `DecodeFacts`, `RefineBase`. Thousands of
   kernel-checked decidable goals (decode-table exhaustiveness, per-instruction
   encoding). Each is ~200–400 ms; the *count* is the problem. In `DecodeFacts`,
   ~92 `decide` calls are the entire 14 s (profiler: `tactic execution` 38.6 s
   summed, `type checking` 14.3 s).

2. **`native_decide`** — `Certify` (99 s), `Validate` (38 s), `CompileTests`.
   Very few calls, but each **compiles the decidable instance to native code and
   runs it** (here: running the whole hex1 assembler over the program and
   byte-checking the output). Cost is compilation + execution, not elaboration.
   Note this puts the compiler/interpreter in the TCB, unlike `decide` — see
   [TCB.md](TCB.md).

3. **`omega`** — `CtrlSim` (323 calls), `Refine` (837). Layout/offset
   arithmetic side-goals. Mostly fast, but the tail is brutal: one `omega` in
   `CtrlSim` took **2.85 s**, several 0.7–1.0 s — usually a symptom of a large
   hypothesis context.

Pervasive underneath all of the above: **kernel type-checking** of large proof
terms (`Main.lean` is ~100% type-checking; `CtrlSim` 19.4 s, `EncodeFacts` 10 s
of the summed totals). One anomaly worth a look: **10.6 s of typeclass
inference** in `EncodeFacts`, high for its size — often a missing/ambiguous
instance causing repeated search.

## Optimization levers (highest to lowest leverage)

1. **Break the Hex1 serial chain.** `Refine.lean` (8700 lines, 104 s) is a
   single module on the critical path. Splitting it into independent
   per-lemma-group modules would let the 64 cores actually parallelize it —
   likely the single biggest wall-clock win.
2. **Thin the `decide` swarm** in `Refine`/`DecodeFacts`/`RefineBase`. Replace
   repetitive `decide` goals with one reusable decision lemma or a simp-normal
   rewrite; 1943 `decide` calls in `Refine` is the dominant elaboration cost.
3. **Audit the slow `omega` tail** in `CtrlSim`. Prune irrelevant hypotheses
   before `omega` (or use omega-free arithmetic lemmas) to kill the multi-second
   calls.
4. **Investigate `EncodeFacts` typeclass inference** (10.6 s) — anomalous for
   its size.

Raw logs from the measured run: `runs_tmp/full-build.log` (per-module) and
`runs_tmp/profile.log` (per-tactic, for `DecodeFacts`/`EncodeFacts`/`CtrlSim`/
`Main`). These are gitignored scratch; re-generate with the commands above.

See also [PROOF-COMPLEXITY.md](PROOF-COMPLEXITY.md) (proof-corpus size/redundancy
assessment) and [LEAN-LAYOUT.md](LEAN-LAYOUT.md) (module map and build targets).
