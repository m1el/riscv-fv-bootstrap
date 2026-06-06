# Supervisor handbook — driving a clean-room reimplementation in an agent

How to drive the hex0 (implementation + Lean refinement proof) reproduction with
a coding agent (currently codex + `deepseek/deepseek-v4-pro` via OpenRouter),
while keeping the experiment clean. This is the **supervisor-side** doc: the
worker agent must never see it (it names the original artifacts and the
steering policy). It doubles as a template for driving any long proof campaign
in an agent.

Live experiment: `/var/data/hex0-repro/` (started 2026-06-06).

## 1. The experiment

**Question.** Can a non-Claude agent reproduce, from a requirements-only spec,
what the original campaign produced: a bare-metal RV64 hex0 decoder running
under `qemu -machine virt -bios none`, plus a sorry-free Lean 4 theorem that
the *actual built bytes*, universally quantified over inputs, implement the
spec?

**Clean-room rules.**
- The worker sees exactly two seed files: `SPEC.txt` (requirements only: BNF,
  normative status codes, acceptance criteria — no proof methodology, no ISA
  subset hint, no memory layout hint) and `hex0.c` (the reference decoder).
- The worker runs inside a docker container; only the clean workspace
  (`work/` → `/work`) and its own codex home are mounted. The original repo
  (`/var/data/bootstrap`) is not reachable from inside.
- Every piece of supervisor help is recorded (§5). The final claim is only as
  strong as the steering log is clean.

**Original-campaign yardsticks** (for the eventual comparison, never for
steering): `bare/core.s` 118 lines; `lean/Hex0/Refine.lean` 3377 lines;
hex1 campaign cost $742.90 / 47h of Claude sessions (`sessions/`).

## 2. Harness layout

```
/var/data/hex0-repro/
  Dockerfile            ubuntu 24.04 + riscv64-linux-gnu-gcc + qemu-system-riscv64
                        + elan/Lean v4.30.0 (baked) + static codex binary
  codex-home/           mounted at /root/.codex (config: openrouter + ds4-pro,
                        trust /work; codex session rollouts persist here)
  work/                 THE CLEAN ROOM. git repo, mounted at /work.
  runs/                 session logs + ledger (host-side only, never mounted)
  run-session.sh        drive one codex exec session (standing prompt below)
  drive.sh              auto-chaining driver (§4)            [to build]
  check-acceptance.sh   objective acceptance gate (§4)       [to build]
```

Sessions run `codex exec --dangerously-bypass-approvals-and-sandbox -C /work`
(approval-free; containment is the container, not codex's sandbox). Each
session gets the same standing prompt: *read SPEC.txt, PROGRESS.md, git log;
push the highest-value step; commit green checkpoints; leave PROGRESS.md
resumable; don't ask questions.* Fresh session each time — **no `resume`** —
so the worker is forced to keep its own state resumable (same discipline the
original campaign used across context windows). Steering, when needed, is
appended to the prompt and (preferably) written to `/work/SUPERVISOR.md` so it
lands in the clean-room git history.

## 3. The supervision loop

Per session N:

1. **Launch** `run-session.sh N [steering]` in the background.
2. **On exit** (notification), review in this order:
   - `git -C work log --oneline` + `git diff` of the session's commits — what
     actually changed (the log narrates; the diff doesn't lie).
   - `work/PROGRESS.md` — does it match the diff? Flag fabrication immediately.
   - `runs/session-NN.log` tail — how it ended (clean wrap-up vs mid-thought).
3. **Gate**: run `check-acceptance.sh` (§4) and append a ledger row (§6).
4. **Decide steering** for N+1 per the policy (§5). Default: none.
5. **Launch N+1.**

Mid-session: check every ~10 min (log mtime + tail + `ps` in container). A
session whose log hasn't grown in ~20 min is wedged (openrouter hang, qemu
waiting on stdin, interactive prompt) — kill the codex process, log it, start
the next session.

**Worker failure modes to watch for** (all observed in agent campaigns):
- *Fabricated status*: PROGRESS.md claims green that doesn't reproduce. The
  acceptance gate exists for this; also spot-check `lake build` output in logs.
- *Theorem weakening*: quantifying over tested inputs only, assuming away the
  loop, `axiom`/`sorry` smuggled into a helper file the build root doesn't
  elaborate. Check: the **build root imports every proof file** (a `lake build`
  that skips the main proof file is green and meaningless — this exact gotcha
  bit the original campaign), `grep -rn 'sorry\|axiom'` over the Lean tree,
  `#print axioms` output in the log.
- *Acceptance drift*: smoke test rewritten to match buggy output instead of
  fixing the decoder; status codes renumbered. The normative codes are in
  SPEC.txt §1 — diff tests against it, not against the worker's claims.
- *Grind loops*: repeating the same failed tactic/build for a whole session.
  One session of honest grinding is fine; two identical ones get steering
  ("try a different decomposition; record the obstacle").

## 4. Automation (the improvements)

- **`drive.sh` — auto-chaining.** Loop: run session N; on exit run the gate,
  append ledger, `git bundle` backup; if `STOP` file absent and N < cap (5
  sessions per supervisor review), launch N+1. Removes dead time between
  sessions while keeping a human/Claude review every few sessions. Drop
  `runs/STOP` to pause the loop at the next boundary.
- **`check-acceptance.sh` — the objective gate.** In a *throwaway container*,
  `git clone` the workspace fresh (catches uncommitted-state dependence) and
  run: `make build`, `make run`, `make verify`; then independently
  `grep -rn sorry` the Lean tree, check the axiom report, and re-check the
  embedded-bytes-vs-binary sync. Emit one pass/fail line per acceptance item.
  PROGRESS.md is narrative; this is the truth.
- **Ledger** (`runs/ledger.csv`): session, wall time, tokens (codex prints
  them), commits, LOC delta, gate results, steering level (§5). Poll the
  OpenRouter usage API for $ spend. This is what makes the final
  cost/capability comparison against `sessions/` (Claude) meaningful.
- **Safety nets**: `git bundle` of `work/` into `runs/backups/` after every
  session (agent `rm -rf` / force-push can't lose the campaign);
  `docker update --memory 64g --memory-swap 64g hex0-repro` (Lean/Coq proof
  search can OOM at 128GB — protect the host); stall detection as in §3.
- **Reasoning-effort knob**: `-c model_reasoning_effort=medium` for mechanical
  sessions (build plumbing, harness debugging), `high` for proof sessions.
  Set per launch in `drive.sh`; default high.

## 5. Steering policy (the integrity boundary)

Levels — **every steering ≥ L1 gets a ledger entry quoting the exact text**:

- **L0 — process discipline.** Always allowed: "commit green checkpoints",
  "update PROGRESS.md", "make verify must pass from a fresh clone", "stop
  repeating the failed approach, record the obstacle". Also infrastructure
  unsticking that has nothing to do with the problem (wedged qemu process,
  openrouter outage).
- **L1 — public tool knowledge.** Allowed sparingly: generic Lean/toolchain
  facts a worker could get from documentation ("Lean structural recursion
  needs a decreasing measure; see `termination_by`"). Nothing
  hex0-specific.
- **L2 — design hints.** Avoid; spends the experiment's purity ("model only
  the instructions you actually use", "rv64imac compressed encodings will
  hurt your formal decode"). Only if the campaign is otherwise dead, and the
  hint must be quoted in the final writeup.
- **L3 — proof structure.** Never ("use a loop invariant relating partial
  machine state to a partial spec run", anything echoing PROOF.md/Refine.lean).
  Crossing this makes the result "Claude dictating the proof through a proxy".

Design choices the worker should discover unaided (current open bets):
ISA-subset choice vs compressed instructions; trusted-shell/proven-core split;
fuel-based termination for the machine run; the loop-invariant shape; keeping
the embedded bytes in sync with the build.

**When the worker is stuck** (≥2 sessions, no gate progress): first try L0
("different decomposition"), then L1 if it's a tool issue. If only L2/L3 would
unstick it, stop and report to the user — "stuck without leaking" is a valid
and interesting experimental result, not a failure of supervision.

## 6. Stop conditions & reporting

- **Success**: all `check-acceptance.sh` items pass from a fresh clone, and a
  supervisor audit of the main theorem statement confirms it says what SPEC.txt
  §B3 demands (universally quantified, actual bytes, right contract) with a
  clean axiom report.
- **Budget**: ask the user for a $ cap on the OpenRouter key; track in the
  ledger. Pause the loop at 80%.
- **Stuck**: 3 consecutive supervisor reviews (≈15 sessions) without gate
  progress → report to user with the obstacle analysis; decide jointly
  whether to spend an L2 hint or call it.
- **Final writeup** (goes in `docs/`): per-deliverable outcome, total
  cost/wall-time vs the Claude campaign, the full steering log with levels,
  and a diff-level comparison of the designs (decoder structure, model shape,
  proof architecture vs `core.s`/`Rv64i.lean`/`Refine.lean`).

## 7. Current state (update as the campaign moves)

- 2026-06-06: harness live; session 01 produced a committed, smoke-tested
  bare-metal RV64 decoder (`hex0.S`, `rv64imac`!) in ~30 min unsteered, then
  started `hex0_proof/` (Spec.lean, Machine.lean) and hit its first Lean
  termination-proof obstacle on the comment-skip recursion. §4 automation not
  yet built; sessions driven manually. Steering so far: none (L0 prompt only).
