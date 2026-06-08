# Clean-room hex0 reproduction — findings (codex/opencode + deepseek-v4-pro)

Result of the A/B/C experiment driven per `REPRO-SUPERVISOR.md`. Question:
can a non-Claude agent (codex/opencode + `deepseek-v4-pro` over OpenRouter)
reproduce, from a requirements-only spec, the verified-hex0 artifact — a
bare-metal RV64 decoder on `qemu virt` **plus a sorry-free, axiom-clean,
universally-quantified Lean 4 proof that the running bytes implement the spec**?

Workspace: `/var/data/hex0-repro/` (`work/` = A, `work-b/` = B, `work-c/` = C),
ledgers in `runs/*ledger.csv`, backups in `runs/backups/`.

## Arms

| | Harness | Prompt | Commits | Reached |
|---|---|---|---|---|
| **A** | codex | original | 12 | Deliverable A ✅; model+spec+harness+infra ✅; proof **2 sorries** (`init_block`, `hex0_correct`) |
| **B** | codex | hardened (PLAN.md, commit-per-green, patch-not-rewrite) | 50 | Deliverable A ✅; model+spec+leaf+~16 symbolic step lemmas ✅; loop induction **not started** |
| **C** | opencode | original | 5 | Deliverable A ✅; parse_nibble 256-case + scaffold; far behind |

Cost: night-1 (shared key, all three from scratch in parallel) **$78.4**;
phase-2 (per-arm keys, resumed one-by-one) **$37.1** (A $5.7, B $31.4, C $0).
Total ≈ **$115**, ~26h wall. (Original Claude campaign yardstick: hex1 at
$742.90 / 47h.)

## Headline result: neither arm produced the full theorem, for two *different* structural reasons

**Arm A — blocked on proof-performance engineering.** A built the entire
B4-*sound* infrastructure: 119 instruction-fetch lemmas via
`readWord_code_eq … ; decide` over the symbolic code-region structure,
memory-disjointness frame lemmas, per-instruction step lemmas, spec-equivalence
layer — axiom report `propext + sorryAx` only (no `native_decide`). It then
spent **4 sessions** unable to land `init_block` (the 14-instruction prologue):
every formulation made the Lean **kernel** re-reduce the 523-byte `initMem`
chain → `(kernel) deep recursion detected` / multi-minute elaboration. It
independently rediscovered two original-campaign lessons (non-`let` state form,
register-preservation lemmas over `dsimp`) but never found a tractable staging.
`hex0_correct` (the loop induction) never reached. **2 sorries remain.**

**Arm B — blocked on an axiom-cleanliness / design conflict (proven).** B chose
an `Array Byte` memory for fast native execution and proved machine-run facts by
*computation* (`dec_trivial` / `native_decide`) — which let it race far ahead:
it verified the whole `parse_nibble` subroutine for all 256 inputs by kernel
`decide` on an 11-step run, and committed ~16 symbolic per-instruction step
lemmas. **But** the instruction-fetch facts (`memReadW execMem <addr> = <word>`)
are kernel-*irreducible* over the Array. Tested directly (supervisor diagnostic):

| route | result |
|---|---|
| `rfl` @ `maxRecDepth 10000` | recursion-depth blown |
| `rfl` @ `maxRecDepth 2_000_000` | **C stack overflow** |
| `decide` @ `maxRecDepth 100000` | **stuck** (reduction makes no progress) |

`native_decide` (compiled) is the *only* route → injects `Lean.ofReduceBool` →
**SPEC B4 (axiom-clean) is unachievable** without ripping out the Array memory
and re-proving fetches symbolically (i.e. adopting **arm A's** approach). So even
a fully finished B — all step lemmas + induction + assembly — would carry the
forbidden axiom. The very design that let B race ahead is what dooms its axiom
report. (B also never started the loop induction; that hard math is untouched.)

**The sharp A/B trade-off:** A had the B4-correct *fetch architecture* but lost
to elaboration cost; B had the fast *computational* architecture but it is
structurally B4-incompatible. Getting the full theorem needs A's symbolic
fetches **and** a tractable `init_block`/induction staging — neither arm
combined both.

## Secondary findings

- **Architecture is a strong attractor.** All three arms, unprompted, chose
  RV64 asm + per-instruction step lemmas + loop invariant — the original
  campaign's shape. The spec's gravity, not steering, produced this.
- **Prompt hardening fixes *process*, not *capability* (A vs B).** B: 50 commits,
  PLAN.md lemma tree, self-built `make verify`, near-zero rewrite thrash — vs
  A's 6 checkout-as-undo incidents and dirty-tree deaths. But it did **not** make
  B able to finish; both hit hard walls. Hardening also **degrades under provider
  instability**: B's one checkout-incident (session 10, ~2 lost sessions)
  happened in its worst stream-glitch session.
- **Harness changes mechanics, not discipline (A vs C).** opencode gives ds4 a
  real edit tool (vs codex's whole-file rewrites) and subagents, but ds4 fumbles
  its tool-call schemas (write/edit/bash "missing key" errors) and the
  commit-drought / dirty-tree pathologies are identical to the codex arms —
  discipline is **model-bound**.
- **`native_decide` affinity is model-bound and dangerous for B4.** Every arm
  reached for `native_decide` on closed-term goals; only when explicitly steered
  did they convert to kernel `decide`. For axiom-clean proofs over evaluable
  state this is a latent failure that surfaces only at assembly.
- **Operational lessons** (folded into the supervisor handbook): detached
  in-container launches survive host wrapper-kills; **never post-mortem on a log
  signal — wait for PID-death** (a stack-overflow log line was recovered-from and
  the session ran on); zombie lean/lake accumulate under a `sleep infinity` PID 1
  (harmless, but reap before timing builds); per-runner API keys are essential
  for spend attribution (opencode reports no tokens).

## Bottom line

ds4-pro **reproduced the engineering** (running bare-metal decoder, faithful
executable model, spec, harness, byte-sync, docs, hundreds of kernel-checked
lemmas) cheaply and largely unaided — the architecture converged on the
original's. It did **not** reproduce the **hard verification core**: the
loop-refinement induction was never structured, and each arm hit a distinct
structural wall (A: kernel elaboration cost on the prologue; B: an
axiom-cleanliness/design conflict that makes B4 unreachable as-built). The
honest reading: the value the original campaign's proof adds *over testing* —
the universally-quantified theorem — is exactly the part that did not reproduce.
