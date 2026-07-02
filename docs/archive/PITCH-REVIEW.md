# Proofread & review — `pitch.md`

Review of the root `pitch.md` (the funding/research pitch). Organized as: (1) spelling &
grammar fixes, (2) clarity/argument suggestions, (3) structural notes.

## 1. Spelling & grammar (mechanical — fix these)

| Line | Current | Fix |
|------|---------|-----|
| 7  | `Previosuly` | `Previously` |
| 7  | `sucessfully` | `successfully` |
| 7  | `some of IT infrastructure of the US` | `some of the US's IT infrastructure` |
| 10 | `Previoulsy` | `Previously` |
| 11 | `the attacking side has a limited speed of discovery was considered slow and low stakes` | broken sentence — see §2 |
| 31 | `they fall short when trying to formally verify hex0` | OK, but tighten — see §2 |
| 36 | `[it's kinda important today]` | informal register clashes with the rest; rephrase, e.g. *"(a national-security priority as of 2026)"* |
| 56 | `which will get subsidized with high quality data` | `high-quality` (hyphenate compound modifier) |
| 5  | `it's quite clear AI will increase its impact` | `it is clear that AI's impact on cyber security will grow` |

## 2. Clarity & argument

**Line 11 is the most important fix.** The sentence is broken and it carries the core
economic thesis:

> *"...formal verification takes approximately 20 lines of proof code per single line of
> source code. To add to that, the attacking side has a limited speed of discovery was
> considered slow and low stakes."*

Suggested rewrite:

> Formal verification has historically been rare for economic reasons: it costs roughly
> 20 lines of proof for every line of source. The payoff was also low — attackers
> discovered vulnerabilities slowly, so the expected loss from an unverified bug was
> small. Both halves of that calculus have now flipped: AI makes attackers far faster at
> finding bugs (raising the payoff of verification), *and* AI makes proofs far cheaper to
> write (lowering its cost).

That two-sided "cost down, stakes up" framing is your strongest argument and right now
it's buried in a malformed sentence. Lines 13–18 then restate it more loosely; consider
merging 11–18 into a single tight paragraph so the thesis lands once, cleanly.

**Lines 14–16** — `But what's most important, formal verification is also cheaper. If
writing proofs required math grad students... you now have infinite "grad students"...`
Drop "infinite" (overclaim — and your own repro study shows current OSS models *fail* at
hex0). Something like: *"the proof labor that once required scarce specialists is
increasingly automatable by language models."* Honest and still strong.

**Line 30** — `all work under Claude-4.8 model` → `all succeed using the Claude Opus 4.8
model`. (Also the project's own model id is `claude-opus-4-8`; "Claude-4.8" is informal.)

**Line 31** — this is a great, credible, falsifiable claim — lead into it more
deliberately. The repro finding is more nuanced than "they fall short": per
`docs/REPRO-FINDINGS.md`, the open models *reproduce the engineering and can plan the
proof*, but none *executes* the key loop-simulation lemma. That nuance is more impressive
and more honest than a flat "fall short." Suggest:

> Open frontier models (DeepSeek4-Pro, Minimax-M3, Kimi-k2.7) reproduce the engineering
> and can even plan the proof, but none completes the proof execution — locating the
> capability frontier precisely.

**Line 52 (P3)** — define TCB on first use *before* the parenthetical, or move the
expansion earlier. Reader hits "Trusted Computing Base (TCB)" with no prior context.
Also tie P3 back to what this repo already demonstrates (the hex0/hex1 verified bootstrap
tower) — that's your proof-of-concept for the "ecosystem that verifies itself" claim and
it makes P3 read as a roadmap, not a wish.

**Line 62** — the "high-quality, novel, auto-verified training data" point is one of your
strongest economic arguments (it turns the token cost into an asset). Consider promoting
it out of "Expected costs" into its own short section or the motivation, because it
changes the cost/benefit story qualitatively.

## 3. Structure & framing

- **Add a one-or-two-sentence lede/abstract** at the very top, before "Motivation." A
  funder should grasp the ask in 15 seconds: *what you'll do, why now, what it costs.*
- **The title** is a full sentence without a verb agreement issue but reads as a heading
  fragment. Consider: *"Formally verified software for cyber security in the age of
  capable AI."*
- **Citations are strong** — real, linked, recent. Good. One caution: the Mythos and
  Firefox-150 references (lines 66–70) appear to be near-future/dated 2026 sources; make
  sure each URL resolves, since a dead link in a pitch undercuts credibility fast. Verify
  before sending.
- **`[m1el-fv]` / `[m1el-fv-repro]`** point at the public GitHub repo — good, the repro
  doc is exactly the kind of receipts a skeptical reviewer wants. Link the
  `REPRO-FINDINGS.md` claim (line 31) directly to the doc so the nuance is one click away.
- **Quantify "Current work."** You have recorded sessions with real dollar costs (the repo
  notes 24 sessions, $744.42). A concrete "we verified hex0 + hex1 end-to-end for $X in
  model spend" is far more persuasive to a budget-holder than a qualitative claim, and you
  already have the number.
- **"Expected costs" needs an actual number range.** Right now it says "researcher salary
  + inference" but gives no figure. Even a rough order-of-magnitude (e.g. "$X/yr for one
  researcher + $Y in tokens for Z proof-targets") makes the ask actionable. Pitches that
  don't name a number make funders nervous.

## Bottom line

The substance is good and the two-sided economic thesis (AI raises attack stakes *and*
lowers proof cost) is genuinely compelling, backed by a real verified artifact and an
honest repro study. The main weaknesses are mechanical: several typos, one broken
load-bearing sentence (line 11), an informal register in a couple of spots, and the
absence of concrete numbers (cost of work done, cost of work proposed). Fix line 11, add
the dollar figures you already have, and tighten the register, and this is a strong pitch.
