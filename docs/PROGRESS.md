# PROGRESS — LowIR & libc-formalize

## 2026-07-06 (compile_sim campaign) — Phase 6: the `prog_sim` summit SKELETON (`Main.lean`)

**`prog_sim` is now PROVEN modulo one well-specified machine-side lemma.** The
lone campaign sorry moves from `Defs.prog_sim` to `Main.entry_run_sim`; the
summit's outer structure + the halt bridge are axiom-clean. Full `lake build`
green. New file `LowIR/ProgSim/Main.lean` (new `LowIRProgSim` root — prog_sim
needs `lower_sim_cf`/`prologue_sim`/`epilogue_sim` (CtrlSim) AND `fn_hfn`/
`stub_emitted` (LayoutFacts), which import `Defs`, so it can't live in `Defs`).

Decomposition: **`prog_sim = entry_run_sim ∘ runFuel_eq_stepN`.**
- **`run_inv`** (ExecFacts, PROVEN, axiom-clean) — the IL-side inversion:
  `run … = some s'` ⇒ `lookup entry = some fd ∧ frameEnter … = some st0 ∧ exec
  fd.body st0 = some (s', oc) ∧ oc ∈ {normal, ret}`. Note s' IS the body's final
  state (`run` does NOT remarshal rets) — so `epilogue_sim`'s `rget (A j) =
  s1.rget rets[j]` matches the conclusion directly.
- **`runFuel_eq_stepN`** (Main, PROVEN, `[propext, Quot.sound]`) — the RESUME §3.2
  bridge: if the machine first reaches `halt` at exactly step K (the `hne`
  no-early-halt clause), plain iteration `stepN K` equals `runFuel halt K`. Nat
  induction; no global pc-invariant needed (`hne` is a hypothesis).
- **`entry_run_sim`** (Main, SORRY, fully specified) — the machine run in `stepN`
  form: stub `jal` → `prologue_sim` → `lower_sim_cf` on `fd.body` (`hfn` ←
  `fn_hfn`; flat obligations ← `SimPre` + layout) → `epilogue_sim` → halt, plus
  the `hne` clause (`fnPos entry ≥ 8 > 4`, so pc stays above `codeBase+4` until
  the final `jalr`).
- **`prog_sim`** (Main, PROVEN modulo `entry_run_sim`) — obtains the `stepN`
  result and rewrites through the bridge. `#print axioms prog_sim` = `[propext,
  sorryAx, Quot.sound]` (sorryAx solely via `entry_run_sim`).

REMAINING = `entry_run_sim` alone: the machine-side assembly (stub step +
`prologue_sim` + `lower_sim_cf` + `epilogue_sim` + the `hne` monotone-pc clause),
all atoms in hand (the call case of `lower_sim_cf` is the worked template, minus
marshalling and minus a caller frame — holes start `[]`).

## 2026-07-06 (compile_sim campaign) — Phase 2: `hblob` wrap-freedom plumbing (`SimPre.blobBelowStack`)

`hblob` (`codeBase.toNat + blobLen ≤ 2^64`, the last placement obligation of
`lower_sim_cf`) is now discharged from a single geometric `SimPre` primitive. All
axiom-clean (`[propext, Quot.sound]`), full `lake build` green (still the 3 known
sorries; SimPre is used only by prog_sim, so nothing constructs it).

- **`SimPre`** — the `blobStackDisjoint` field is replaced by the stronger
  `blobBelowStack : L.codeBase.toNat + L.blobLen ≤ stackLo.toNat` (the loader
  places code+data at low addresses, below the stack).
- **`SimPre.blobStackDisjoint`** (now a THEOREM, same name/shape — callers'
  `hpre.blobStackDisjoint` still resolve): anything in the blob is strictly below
  `stackLo`, hence outside `[stackLo, sp0)`.
- **`SimPre.blobWrap`** = **`hblob`**: the blob sits below `stackLo`, itself
  `< 2^64` (`BitVec.isLt`), so `codeBase.toNat + blobLen ≤ 2^64`.

`blobBelowStack` ALSO yields `hbd`'s blob-below-stack disjunct (with
`stackNonEmpty`). Validated end-to-end (scratch): `SimPre L + layoutOf` discharges
`halign ∧ hdpos ∧ hcode ∧ hblob ∧ disjointness ∧ hbd-left` together. **Every
flat/placement input `lower_sim_cf` takes is now discharged from the real layout
+ SimPre** (`hdat`/`hdbase`/`hdpos`/`hpad`/`halign`/`hstackLo`/`hfn`/`hblob`/`hbd`)
plus `hem`; the remaining work is the Phase 6 `prog_sim` summit assembly
(entry-stub step + `call_sim` into `entry` + body via `lower_sim_cf` +
halt-pad bridge to `runFuel`).

## 2026-07-06 (compile_sim campaign) — Phase 2: `hdpos`/`halign` plumbing (blob bound ⇒ dpos, SimPre)

The last flat compile-time obligations of `lower_sim_cf` (`hdpos`, `halign`, and
`fn_hfn`'s `hcode`) are now wired so Phase 6 `prog_sim` discharges them from ONE
program-level bound plus a loader precondition. All axiom-clean (`[propext,
Quot.sound]`), full `lake build` green (still exactly the 3 known sorries).

- **`dataOffsetsFrom_off_le`** (Prog.lean) — every object offset lies within the
  data segment: `off ≤ start + |dataSegment|` (list induction, sibling of
  `dataOffsetsFrom_le`/`_fits`/`_shift`).
- **`dposOf_le_blobLen`/`dposOf_lt`** (AsmFacts) — hence `dposOf L d ≤ L.blobLen`,
  and `< 2^20` given the blob bound = **`hdpos`**.
- **`codeLen_le_blobLen`/`codeLen_lt`** (AsmFacts) — `4·|instrs| ≤ blobLen` (via
  `hseg`), so `< 2^20` given the blob bound = **`hcode`** (fn_hfn / `hbnd`).
- **`SimPre`** gains two fields: `codeAligned` (`codeBase % 4 = 0` = **`halign`**,
  a loader precondition) and `blobFits` (`blobLen < 2^20`, powering hdpos/hcode).
  SimPre is used only by prog_sim, so no construction breaks.

Validated end-to-end (scratch): `SimPre L + layoutOf` ⇒ `halign ∧ (∀ d, dposOf L
d < 2^20) ∧ 4·|instrs| < 2^20`, with `hseg` from `layoutOf_decomp` (`segStart =
pad8 (4·|instrs|)`) + `pad8_ge`. All of `lower_sim_cf`'s flat obligations
(`hdat`/`hdbase`/`hdpos`/`hpad`/`halign`/`hstackLo`/`hfn`) plus `hem` are now
discharged from the real layout + SimPre; the remaining prog_sim inputs are
`hblob` (`codeBase.toNat + blobLen ≤ 2^64` wrap-freedom) and the summit assembly
itself (entry-stub step + `call_sim` into `entry` + body + halt-pad bridge).

## 2026-07-06 (compile_sim campaign) — Phase 2: the entry-stub `Emitted` (`hem`, `stub_emitted`)

The `hem` half of the Phase-2 payload is now in hand, mirroring `fn_hfn` but for
the entry stub. The resolved stub `[jal ra, entry; jal x0, 0]` is `Emitted L 0`
— the length-2 prefix of `L.instrs`. `prog_sim` will step the first to enter
`entry` (ra := codeBase+4) and spin on the second at the halt PC `codeBase + 4`.
All axiom-clean (`[propext, Quot.sound]`), full `lake build` green (still exactly
the 3 known sorries). In `LayoutFacts.lean`:
- **`compileProgT_entry`** — the guard's 3rd clause: `entry ∈ P.env` (⇒ `entry ≠
  ""` via the tightened `wfProgram`, routed through `fn_guard_facts`).
- **`mapM_single_nonlabel`** — resolving a single non-label positioned item: its
  layout is `[(pos, si)]`, so `mapM` returns `[v]` with `resolveOne (pos,si) =
  some v`.
- **`stub_emitted`** (payoff) — peels the stub off `progLayout.1`
  (`mapM_append_inv`), splits its two items (`resolve_flatten_append`), resolves
  `.ins (jal0 0) → [jal0 0]` (rfl) and `.callf entry → [jal RA (ofInt 21 (fnPosOf
  L entry))]` (fn-table lookup tied to `fnPosOf` via `lookup_filter_ne` + the
  `L.fnTab` filter; the resolve's own success discharges the 21-bit range check),
  then `Emitted_of_slice` at position 0.

REMAINING for Phase 6 `prog_sim` (Defs.lean:471, the lone campaign `sorry`): the
`hdpos`/blob-size bound + `halign` (codeBase 4-alignment) plumbing, then the
summit assembly — entry-stub step (via `stub_emitted`) + `call_sim` into `entry`
+ body via `lower_sim_cf` (with `hfn` from `fn_hfn`) + halt-pad bridge to
`runFuel`.

## 2026-07-06 (compile_sim campaign) — Phase 2: the FULL per-function `hfn` bundle (`fn_hfn`)

The complete six-conjunct `hfn` fact that `lower_sim_cf` (CtrlSim.lean:1479) and
`prog_sim` take is now discharged from the real layout for every function of a
successfully-compiled program. All axiom-clean (`[propext, Quot.sound]`), full
`lake build` green (still exactly the 3 known sorries: `Core.compile_sim`,
`Hex0/ProgProof`, `Defs.prog_sim`).

Two **compiler guard tightenings** first (commit `b095917`, same class as the
2^22 data tightening — both close real soundness gaps surfaced while assembling
the bundle; every real program already satisfies both, all tests re-green):
- `fnOk` now requires `frameSize % 8 == 0` — the prologue zeroes the user frame
  in 8-byte words (`List.range (frameSize/8)`), so a non-8-multiple would leave a
  tail unzeroed (machine vs IL `zeroRange` disagree). → `hfn` conjunct 5.
- `wfProgram` now requires each function name non-empty — the entry stub reserves
  the `""` key and `fns.filter (·.1 != "")` silently drops a `""`-named function.
  → `fn_emitted`'s `g ≠ ""` premise.

Then `fn_hfn` (commit `bd0bb21`, `LayoutFacts.lean`):
- **`compileProgT_wfProgram`/`compileProgT_fnOkAll`** — guard extractors (1st/2nd
  clauses of `compileProgT`'s conjunction; twins of `compileProgT_dataBound`).
- **`fn_guard_facts`** — per-function facts for `(g,gd) ∈ P.env`: body `wf`,
  `g ≠ ""`, `totalFrame ≤ 2000`, `frameSize % 8 = 0`.
- **`epilogueI_length`** — resolved epilogue = `rvc + 3` instrs (`rets : Vector
  Reg rvc`, each ret one `loadSlotI`, + ld/addi/jalr).
- **`fn_hfn`** (payoff) — for any `List.lookup g P.env = some gd`: conjunct 1
  (`Emitted`) via `fn_emitted`; conjunct 2 (the `< 2^20` end position) from ONE
  program-level blob bound `4·|L.instrs| < 2^20` + the Brick-2 slice (`fnPos =
  4·|preF.flatten|`, `preF+rsg ≤ |instrs|`, `|rsg.flatten| = prologueSize + csize
  body + epilogueSize`); 4/5 from `fn_guard_facts`; 6 (`fnPos % 4 = 0`) from the
  tie. `BranchOk gd.body` is threaded as `hbr` (the per-program structural
  hypothesis `lower_sim_cf` itself carries; `decide`-checkable per program).

REMAINING for Phase 6 `prog_sim` (Defs.lean:471, the lone campaign `sorry`): the
entry-stub `Emitted` (`hem` — the `[jal ra entry; jal0]` at position 0, a small
`fn_emitted`-analog on `stubSeg`), the blob-size/`hdpos` bound plumbing, `halign`
(codeBase 4-alignment), then the summit assembly — entry-stub step + `call_sim`
into `entry` + body via `lower_sim_cf` + halt-pad bridge to `runFuel`.

## 2026-07-06 (compile_sim campaign) — Phase 2: `hfn`/`hem` Emitted payload ASSEMBLED (Bricks 1–4)

The `layout`↔`Emitted` correspondence — "the big one" flagged STILL OWED in
`AsmFacts.lean` §6 — is closed. Four bricks in `LayoutFacts.lean`, full
`LowIRProgSim` green (still exactly the 2 known sorries: `Core.compile_sim`,
`Defs.prog_sim`), all axiom-clean:

- **Brick 1** (`compileProgT_decomp`/`layoutOf_decomp`, `[propext]`) — a successful
  compile exposes the internal resolve structure: `L.instrs = rs.flatten` with the
  whole positioned stream (`progLayout`) resolving to `rs`; `L.fnTab = layout fns
  minus the stub`; data table `= dataOffsetsFrom (pad8 codeEnd)`; `segStart = pad8
  (4·#instrs)`. New defs: `stubSeg`, `progLayout`, `fnPosOf`.
- **Brick 2** (`fn_resolve_slice`, `[propext,Quot.sound]`) — the flat resolve split:
  for `g` at env split `envPre ++ (g,gd) :: envSuf`, `L.instrs = pre ++ rsg.flatten
  ++ suf` with `rsg` = g's compiled segment resolved at its byte position `pp`
  (feeds `compileFun_resolves`' `hres`) and `4·|pre.flatten| = pp`. Composes
  `layout_flat_append` + `mapM_append_inv` (×2) + new `resolve_length_layout` +
  `layout_end`.
- **Brick 3** (`tabOk_discharge` + `fnPosOf_tie` + `instrs_len_codeEnd`) — `TabOk
  dposOf fnPosOf fns dats` (fn clause UNCONDITIONAL: stub sits first + non-stub keys
  survive the `L.fnTab` filter; data clause from `segStart = pad8 codeEnd`); the
  `fnPosOf` tie (`fnPosOf L g` = g's layout byte position, at g's FIRST env
  occurrence, `g ≠ ""`). Helpers: `lookup_split`, `mapSegs_keys`,
  `layout_fns_lookup_none`, and `lc_self`/`lc_ne` (clean lookup — ⚠ `beq_self_eq_true`
  on `String` is **`Classical.choice`-tainted** via its `ReflBEq` instance;
  `beq_iff_eq.mpr rfl` is the clean route).
- **Brick 4** (`fn_emitted` — the payoff, `[propext,Quot.sound]`) — each function `g`
  (first env occurrence, `g ≠ ""`, body `wf`) is `Emitted` at `fnPosOf L g` as
  `prologueI gd ++ emitCF … gd.body ++ epilogueI gd` — the exact `hfn`/`hem`
  `Emitted` payload `lower_sim_cf`/`prog_sim` consume. Composes Brick 2 +
  `compileFun_resolves` (label premises via `env_fn_lbls_discharge`, tables via
  `tabOk_discharge`) + Brick 3. Helper `Emitted_of_slice` (via `getElem_of_eq` +
  `getElem_append`).

REMAINING for a full `hfn` (per-`g` bundle, still Phase 2, mostly independent):
the `Emitted` conjunct is DONE; the remaining conjuncts are `fnPos g % 4 = 0`
(cheap, from `4·|pre| = pp`), `totalFrame gd ≤ 2000` (from `fnOk`, in the guard),
`BranchOk gd.body` (needs a `BranchOk_of_wf`), `gd.frameSize % 8 = 0` (NOT currently
checked by `fnOk`/`wfProgram` — a guard-design gap, like the 2^22 tightening), and
the `< 2^20` end-position bound (needs a **blob-size bound** hypothesis — the same
`hdpos`/`hblob` blob bound noted REMAINING in RESUME-PROGSIM §Phase-2). Then wire
`fn_emitted` over all `g` via `lookup_split` (first-occurrence env split), and Phase 6
`prog_sim` (Defs.lean:471, one of the two lone sorries).

## 2026-07-06 (compile_sim campaign) — Phase 2: the `fnPos g` tie (label-premise side)

Three more `LayoutFacts.lean` lemmas close the `fnPos g` tie for the label premises,
all axiom-clean (`layout_fns_decomp`: `[propext]`; the others `[propext, Quot.sound]`),
full `lake build` green (still exactly the 3 pre-existing sorries):

- **`layout_fns_decomp`** — a `mem` in the layout's function table decomposes the
  segment list: `(g, p) ∈ (layout segs pos).2.2.1` ⇒ `segs = pre ++ (g, items) :: suf`
  with `(layout pre pos).2.2.2 = p`. `layout` records one `(name, startPos)` per
  segment in order, so the recorded position IS the prefix's end. List induction on segs.
- **`mapSegs_append`** — the counter-threading twin of `layout_flat_append`: `mapSegs`
  over an env append compiles the second group from the fresh-label counter the first
  ends at (`(mapSegs (a++b) c).1 = (mapSegs a c).1 ++ (mapSegs b (mapSegs a c).2).1`,
  and the end counters compose).
- **`env_fn_lbls_discharge`** (the payoff) — keyed on an env split `envPre ++ (g,gd)::
  envSuf`: `g`'s counter is `(mapSegs dat envPre 0).2`, its byte position is the layout
  end of `("", stub) :: (mapSegs dat envPre 0).1`, and at those BOTH `compileFun_resolves`
  label premises hold. Composes `mapSegs_append` + `mapSegs_cons` (segment decomposition)
  with `compileFun_lbls_discharge`.

Remaining for `hfn`/`hem` (assembly only): the caller identifies `env_fn_lbls_discharge`'s
byte position with `g`'s `fnTab` entry (via `layout_fns_decomp` + env-name uniqueness);
the **flat resolve split** at each `fnPos g` (`layout_flat_append` + `resolve_length`)
placing each function's resolved-instruction slice — feeds `compileFun_resolves`' `hres`;
`TabOk` from `dposOf`/`fnPosOf`; assemble the per-function `Emitted` from `layoutOf` (the
`hfn` fact). Then `hdpos`/`halign` + Phase 6 `prog_sim` (Defs.lean:491, the lone `sorry`).

## 2026-07-06 (compile_sim campaign) — Phase 2: position-membership + per-function `hepi`/`hlc` discharge

Three new `LayoutFacts.lean` lemmas close the "position-membership" step (the first
of the four assembly obligations named below), all axiom-clean (`layout_lbls_mem`:
`[propext]`; the other two `[propext, Quot.sound]`), full `lake build` green (still
exactly the 3 known pre-existing sorries: `Core.compile_sim`, `Defs.prog_sim`,
`Hex0/ProgProof`):

- **`layout_lbls_mem`** — a segment's `layoutItems` label entries lift into the global
  `layout` table: the global table is the positional concatenation of the per-segment
  tables (the `layout` cons def), so any `mem` on one segment's slice (laid out at the
  end position of its prefix `pre`) is a `mem` of the whole. List induction on `pre`.
- **`compileFun_lbltab`** — the exact label table `layoutItems` records for a function's
  compiled stream at absolute position `p`: the body's internal labels (at `bodyPos =
  p + 4·|prologueI|`) followed by the single epilogue-label entry `(c, bodyPos +
  4·csize body)`. Peels prologue/`[.label c]`/epilogue via `layoutItems_append`, kills
  the all-`.ins` prologue/epilogue tables (`layoutItems_lbltab_nil` from `labelIds_*`),
  pins positions with `tss_prologue` + `lower_totalSymSize`.
- **`compileFun_lbls_discharge`** (the payoff) — given the global layout and that `g`'s
  compiled segment sits at absolute `p` (`hseg`/`hp`), produces BOTH `compileFun_resolves`
  label premises: `hepi` (epilogue-label lookup = its byte position) and `hlc`
  (`LblConsistent` for the body labels). Chains `compileFun_lbltab` (what the labels are)
  → `layout_lbls_mem` (they're in the global table) → `lbls_lookup` (nodup keys ⇒
  membership determines lookup).

Remaining for a complete `hfn`/`hem` (still assembly only): **the `fnPos g` tie** —
discharge `compileFun_lbls_discharge`'s `hseg`/`hp` from the global layout's function
table (each `(g, p) ∈ (layout …).2.2.1` ⇒ `g`'s segment decomposes as `pre ++ (g,·)::suf`
with `(layout pre 0).2.2.2 = p`); the **flat resolve split** at each `fnPos g`
(`layout_flat_append` + `resolve_length`) placing each function's slice; `TabOk` from
`dposOf`/`fnPosOf`; assemble the per-function `Emitted` from `layoutOf`. Then `hdpos`/
`halign` + Phase 6 `prog_sim` (Defs.lean:491, the lone campaign `sorry`).

## 2026-07-06 (compile_sim campaign) — Phase 2: `LayoutFacts.lean` — the hfn/hem glue underway

New library module `LowIR/ProgSim/LayoutFacts.lean` (lakefile root
`LowIR.ProgSim.LayoutFacts`) builds the layout↔`Emitted` half of `hfn`/`hem` on top
of `lower_resolve`. Four reusable layers, all `[propext, Quot.sound]`, full build
green:

- **Resolve-length bridge** (`resolveOne_length`, `resolve_length`): a laid-out
  symbolic item resolves to `symSize/4` instructions, so `4·(resolved instr count) =
  totalSymSize` — the byte-position ↔ instruction-index conversion.
- **`layout` algebra** (`layout_end`, `layout_flat_append`, `layout_fns_append`):
  the layout pass distributes over a segment-list append; the second group is laid
  out starting where the first ended.
- **Per-function slice** (`compileFun_resolves`, the payoff): resolving
  `compileFun`'s byte stream at position `p` yields exactly `prologueI ++ emitCF …
  body ++ epilogueI`, composing `prologue_resolves` + `lower_resolve` +
  `epilogue_resolves`. Supporting: `totalSymSize_allins`, `tss_prologue`,
  `tss_epilogue`, `compileFun_stream`. Takes the label premises (`hepi`: epilogue-label
  lookup; `hlc`: body `LblConsistent`) + `TabOk` as **hypotheses** — the last unmet
  obligations, which the global label-nodup / table-agreement discharge.
- **`lower` label distinctness** (`labelIds` + algebra; `lower_snd_ge`,
  `lower_labels_range`, `lower_labels_nodup`): every label `lower` emits sits in
  `[cnt, finalCnt)` and they are pairwise distinct — the per-function foundation the
  global nodup lifts from (through `compileFun` then the fresh-counter-threaded
  segment `mapM`).

**Global label nodup — now DONE** (all `[propext, Quot.sound]`): `compileFun_labels_range`/
`_nodup`/`_snd`/`_snd_gt` lift the per-`lower` label range/nodup through `compileFun`
(epilogue label `= c`, body labels `≥ c+1`); `mapSegs`(`_nil`/`_cons`/`_labels`)
threads the fresh-label counter through the segment `mapM` so the per-function ranges
`[c_i, c_{i+1})` are disjoint, giving the whole program's label flatMap `Nodup`;
`layoutItems_lbls_keys`/`layout_lbls_keys` identify the layout's recorded keys with the
per-segment `labelIds`; `lookup_of_nodup_mem` + the assembled `global_lbls_nodup` /
`lbls_lookup` conclude that any `(l, p)` in the global label table is looked up to
exactly `p`. (Mathlib-free gotcha: `beq_self_eq_true`/`List.lookup` on Nat keys pull
`Classical.choice` via Nat's `LawfulBEq` — use `rw [beq_iff_eq]`.)

Remaining for a complete `hfn`/`hem` (assembly only — the hard machinery is all in
place): **position-membership** (each function's body + epilogue labels sit in the
global table at their absolute byte positions, via a `layoutItems` label-position
lemma threaded through `layout_flat_append`/`layout_fns_append` — feeds `lbls_lookup`
to discharge `compileFun_resolves`' `hepi`/`hlc`); the **flat resolve split** at each
`fnPos g` (`layout_flat_append` + `resolve_length`) placing each function's slice;
`TabOk` from `dposOf`/`fnPosOf`; assemble from `layoutOf`. Then `hdpos`/`halign` +
Phase 6 `prog_sim` (Defs.lean:491, the lone remaining `sorry`).

## 2026-07-06 (compile_sim campaign) — Phase 2: `LowerFacts` layer 3 — `lower_resolve` DONE

The correspondence induction is closed: resolving (`resolveOne` over `layoutItems`)
the compiler's laid-out symbolic body stream flattens to exactly `emitCF` at the
same byte position, for ALL 22 statement constructors. `#print axioms
lower_resolve = [propext, Quot.sound]`; full `lake build` green. This was the crux
of `hfn`/`hem` (the `matchesRealProg` #guard is its decidable shadow, now a
theorem for every program).

Statement (structural induction on `stmt`, threading three consistency relations):
```
lower_resolve (dat P dpos fnPos lbls fns dats) (htab : TabOk dpos fnPos fns dats) :
  ∀ stmt bs cs epi cnt here bp cp ep r,
    (layoutItems (lower dat bs cs epi stmt cnt).1 here).1.mapM (resolveOne lbls fns dats) = some r →
    Prog.wf P bs.length cs.length stmt = true →
    LEnvOk lbls bs cs epi bp cp ep →
    LblConsistent lbls (layoutItems (lower dat bs cs epi stmt cnt).1 here).2.1 →
    r.flatten = emitCF dat dpos fnPos bp cp ep here stmt
```
with the three predicates now real defs: `LEnvOk` (enclosing brk/cont label stacks
+ epilogue resolve to their byte positions), `LblConsistent` (every internal label
resolves to its layout position), `TabOk` (data/function tables agree with
`dpos`/`fnPos`). `wf` is used only for the `brkB`/`contL` index bounds.

Proof structure (all `[propext, Quot.sound]`):
- **Resolve atoms**: `resolveOne_{jmp,br,cref,callf}_eq` (the value a laid-out symbolic
  item resolves to, given a successful lookup — the uniform `simp only [resolveOne,
  hlk, bind, Option.bind]` reducer exposes the range-check `if`); `resolveOne_{cref,
  callf}_lookup` (lookup existence from a successful resolve).
- **Peeling primitive** `split2`: splits BOTH the resolve (`resolve_flatten_append`)
  and the label-consistency of a stream append at once. Straight-line/leaf pieces go
  through `allins_resolve` (all-`.ins`/`.label` ⇒ `flatMap insUnwrap`) or
  `resolve_singleton_flatten` (a singleton characterized by the `_eq` lemmas);
  the compound cases (seq/block/ife/while/call) peel into pieces, extract the internal
  label lookups from the piece `LblConsistent`s (`lblLookup_{singleton,jmplabel}`,
  `layoutItems_brjmplabel`), and reassemble. Jump/branch offsets: the label position
  minus the branch position equals `emitCF`'s size-relative offset, closed by
  `push_cast; omega` over the `lower_totalSymSize`-pinned positions.
- **Segment runners** for the two compound jump-clusters: `resolve_jmplabel_flatten`
  (`[.jmp,.label]`), `resolve_brjmp`/`resolve_brjmplabel` (the while guard `[.br,.jmp
  (,.label)]`). `LEnvOk_push_{brk,cont}` extend the label environment at block/while
  body entry.

⚠ **Mathlib-free gotchas hit** (for the next session): `ring_nf`/`norm_num` are
UNAVAILABLE (`push_cast` + `omega` are; do the Int-cast offset identities as an
explicit `have … := by push_cast; omega` then `rw`, never `congr; push_cast; omega`
— `congr` over-decomposes lists and leaves omega a mangled goal or "no goals").
`cases hv : e with …` SUBSTITUTES `e` in the goal (so an `∃`-goal's witness clause
becomes `some v = some v` — provide `rfl`, not the equation). The Option `do`/`>>=`
is NOT syntactic `Option.bind` (so `Option.bind_some`/`rw [Option.bind_some]` miss);
`simp only [resolveOne, hlk, bind, Option.bind]` reduces it. Position associativity:
`rw [s_i]` yields `here + (12 + 4·csize e)`; left-associate with `simp only [←
Nat.add_assoc]` before matching `emitCF`'s `here + 12 + …`.

STILL OWED for `hfn`/`hem`: (a) the `layout`/`layoutItems` position arithmetic tying
`fnPos g` to the resolved-stream slice, then glue `lower_resolve` with §6's
`prologue_resolves`/`epilogue_resolves` per function; discharge `LEnvOk`/
`LblConsistent`/`TabOk` from the global `layout`/`fnTab`/`dataOffsets` construction
(`fresh`-monotonicity label nodup is the remaining plumbing). Then `hdpos`/`halign`
and Phase 6 (`prog_sim`).

## 2026-07-05 (compile_sim campaign) — Phase 2: `LowerFacts` layers 1–2 (the `lower`↔`emitCF` infrastructure)

New file `LowIR/ProgSim/LowerFacts.lean` (in the `LowIRProgSim` lake target),
building toward the last big piece of `hfn`/`hem`: the correspondence between the
compiler's RESOLVED per-function body stream (`resolveOne` over `layoutItems` of
`lower dat [] [] epi gd.body`) and `emitCF P.data dpos fnPos [] [] epiPos bodyPos
gd.body`. `matchesRealProg` (CtrlSim) is its decidable shadow. Everything
`[propext, Quot.sound]`.

- **Layer 1** — structural `layoutItems` algebra: `totalSymSize`, `layoutItems_pos`
  (end position = pos + total size), `layoutItems_append` (flat/label lists
  concatenate; the second stream starts where the first ends); plus the resolve
  composition `mapM_append_inv` (a successful Option `mapM` over an append splits
  into successful halves that concatenate) and `resolve_flatten_append`. These
  let the correspondence induction split a `lower` output (built by `++`) into
  positioned, resolved pieces.
- **Layer 2** — `lower_{skip,annot,ret,brkB,contL,seq,block,ife,while,cref,clen}`
  unfolding equations (all `rfl`; the `StateM Nat` fresh-label counter threading
  is definitional, including the ife/while/block internal-label allocation order),
  and `lower_totalSymSize`: `totalSymSize (lower … stmt) = 4·csize stmt` over all
  22 constructors. This is the POSITION BRIDGE — every construct's lowering has
  byte size `4·csize`, so (with `layoutItems_pos`/`_append`) each internal label's
  layout byte position is pinned, letting the induction's compound cases match
  `resolveOne`'s computed jump offsets to `emitCF`'s size-relative ones.

**Layer 3 — the correspondence induction `lower_resolve` (STILL OWED; design fully
worked out this session).** Statement (structural induction on `stmt`, threading a
"resolution succeeds" hypothesis so range-checks are inherited from the global
`compileProgT = some`, never re-proved):
```
theorem lower_resolve (dat) (dpos fnPos) (lbls fns dats) (htab : TabOk dpos fnPos fns dats) :
  ∀ stmt bs cs epi cnt here bp cp ep r,
    (layoutItems (lower dat bs cs epi stmt cnt).1 here).1.mapM (resolveOne lbls fns dats) = some r →
    wf P bs.length cs.length stmt = true →                       -- brk/cont indices in range
    LEnvOk lbls bs cs epi bp cp ep →                             -- enclosing labels ↦ positions
    LblConsistent lbls (layoutItems (lower dat bs cs epi stmt cnt).1 here).2.1 →  -- internal labels
    r.flatten = emitCF dat dpos fnPos bp cp ep here stmt
```
with the consistency predicates (to be added to LowerFacts):
- `LEnvOk lbls bs cs epi bp cp ep` : `lbls.lookup epi = some ep`; `∀ k < bs.length,
  lbls.lookup (bs.getD k 0) = some (bp.getD k 0)` (ditto conts); `bs.length =
  bp.length`, `cs.length = cp.length`.
- `LblConsistent lbls local` := `∀ l p, (l,p) ∈ local → lbls.lookup l = some p`.
- `TabOk dpos fnPos fns dats` := `∀ d off, dats.lookup d = some off → off = dpos d`
  and `∀ f p, fns.lookup f = some p → p = fnPos f` (for cref/callf).

Per-case plan (all pieces exist):
- **straight-line ops** (10) + **skip/annot**: `lower … op` is all-`.ins`; use
  `AsmFacts.resolve_ins_mapM` (`r = sym.map insUnwrap`, so `r.flatten =
  sym.flatMap insUnwrap`) + the `AsmFacts.{store,load}Slot_unwrap` lemmas to get
  `emit op`; `emitCF … op = emit op` (rfl catch-all).
- **seq**: `lower_seq` + `resolve_flatten_append`; two IHs; `emitCF seq = emitCF a
  ++ emitCF b`. (Second half positioned at `here + 4·csize a` via
  `lower_totalSymSize` = `totalSymSize (lower a)`.)
- **ret/brkB/contL**: `lower_* = [.jmp x]`; singleton `mapM`; the resolve helper
  `resolveOne_jmp_eq` (already drafted: given `lbls.lookup l = some tgt` and
  success, the result is `[jal0 (tgt−pos)]`) with `tgt` from `LEnvOk`
  (`epiOk`/`brkOk`/`contOk`; `wf` gives the index `< length`). Matches
  `emitCF = [jal0 (ep−here)]` since the jmp sits at `pos = here`.
- **cref/clen**: `lower_cref`/`lower_clen`; `.cref d` resolves (via `htab.datOk`)
  to `crefI T0 T1 (dpos d − (here+4))` = `emitCF`'s crefI; `storeSlot`→`storeSlotI`;
  `clen`'s `synthConst` is all-`.ins` = `synthI`.
- **call**: marshal loads (all-`.ins`) + `.callf f` (resolve via `htab.fnOk` to
  `jal RA (fnPos f − (here+4·argc))`) + ret stores (all-`.ins`).
- **block/ife/while**: the position arithmetic. Decompose `lower_*` into `++`
  pieces, resolve each via `resolve_flatten_append`, recurse with IHs on the
  sub-statements. The internal `.label`s (lEnd / lT,lEnd / lTop,lBody,lEnd) sit at
  positions computed from `layoutItems_pos` + `lower_totalSymSize` (e.g. ife's `lT`
  = `here + 16 + 4·csize e`); `LblConsistent` turns those into `lbls.lookup`
  values, and the emitted `.br`/`.jmp` offsets (`resolveOne_br_eq`/`_jmp_eq`) then
  equal `emitCF`'s size-relative offsets by arithmetic. For while's body, build the
  new `LEnvOk` with cont-head `cnt ↦ here` (from `LblConsistent` on the leading
  `.label cnt`); for block, brk-head `cnt ↦ here + 4·csize body`.

Then `hfn`/`hem` follows: instantiate `lower_resolve` at each function's body with
`lbls`/`fns`/`dats` = the global `layout`/`fnTab`/`dataOffsets` tables, discharging
`LEnvOk`/`LblConsistent` from `layout`'s construction + `fresh`-monotonicity label
nodup (the remaining plumbing), and glue with §6's `prologue_resolves`/
`epilogue_resolves`.

## 2026-07-05 (compile_sim campaign) — Phase 2: prologue/epilogue resolve correspondence (`hfn` foundation)

`AsmFacts.lean` §6 (new): the two SELF-CONTAINED halves of the `hfn`/`hem`
layout↔`Emitted` correspondence that need neither the `layout`-flatten position
arithmetic nor the `lower`↔`emitCF` label-resolution induction. The machine
`resolveOne` over `Compile.prologue`/`epilogue` (both all-`.ins`,
position-independent) flattens to exactly `prologueI`/`epilogueI`:
- `resolve_ins_mapM` — for an all-`.ins`/`.label` stream, `resolveOne` is
  position-independent and maps each item to its `insUnwrap` (labels → `[]`,
  `.ins i → [i]`); the load-bearing structural lemma.
- Unwrap algebra: `insUnwrap_flatMap_append`/`_map_ins`/`_flatMap_flatMap`,
  `storeSlot_unwrap`/`loadSlot_unwrap` (the symbolic builder's `flatMap insUnwrap`
  = the resolved `storeSlotI`/`loadSlotI`).
- `prologue_unwrap`/`epilogue_unwrap` (segment-by-segment) + `*_all_ins`, giving
  the payoffs **`prologue_resolves`** / **`epilogue_resolves`**, both axiom-clean
  `[propext, Quot.sound]`.

STILL OWED for the full `hfn`/`hem` (the big one, next session): (a) the
`layout`/`layoutItems` position arithmetic tying `fnPos g` to the resolved-stream
slice, and (b) `resolveOne`-over-`lower dat [] [] epi gd.body` = `emitCF … gd.body`
— the label-resolution induction (`matchesRealProg` is its decidable shadow).

## 2026-07-05 (compile_sim campaign) — Phase 2: three flat obligations discharged + a real compiler-guard fix

Progress on `AsmFacts.lean` (Phase 2, the assembler layer). Three of the flat
compile-time hypotheses that `lower_sim_cf`/`prog_sim` take are now discharged
from the real `layoutOf`/compiler, all axiom-clean (`[propext]` or `[propext,
Quot.sound]`):
- `layoutOf_stackLo` → `hstackLo`;
- `clen_synthOk` → `hdat` (with `lookup_len_lt`, `BEq`-agnostic; and
  `compileProgT_dataBound` extracting the data guard);
- `dbaseOf_dposOf` → `hdbase` (+ the `dposOf L` def), via `dataOffsetsFrom_shift`.

**A genuine narrow soundness gap fixed.** Verifying `hdat` surfaced that
`clen`'s constant synthesis (`synthConst`, unchecked) needs a data length
`< 2^23−2048` — `synthHi = ⌊(len+2048)/4096⌋` reaches 2048 for `len ∈
[2^23−2048, 2^23)`, overflowing the 12-bit signed hi immediate (`BitVec.ofInt
12 2048` wraps to −2048 ⇒ the compiled `clen` loads a garbage length). The
compiler's guard was `length < 2^23` (`Compile.lean:313`) — too loose by 2048.
`cref` is safe (its `resolveOne` explicitly range-checks); only `clen` was
exposed. Fixed by tightening the guard to `< 2^22` (user-chosen round bound,
well inside the synthesizable band). All differential tests re-green — no real
program is near 4 MB of const data.

REMAINING in Phase 2: `hfn`/`hem` (the layout↔`Emitted` per-function
correspondence — the big volume piece), `hdpos` (blob-size bound), `halign`
(a `prog_sim` codeBase-alignment hypothesis). Then Phase 6 (`prog_sim`).

## 2026-07-05 (compile_sim campaign) — Phase 5 COMPLETE: `lower_sim_cf` call case closed, axiom-clean

The `call` case of `lower_sim_cf` (the last statement-level `sorry`) is proved.
`lean/LowIR/ProgSim/CtrlSim.lean` now has **no `sorry`**, and `#print axioms
lower_sim_cf = [propext, Quot.sound]` (no `sorryAx`, no `Classical.choice`). Plan
+ design record: [RESUME-CALL.md](RESUME-CALL.md) (W1–W8 all done).

This session closed segs 3–6 of the six-segment call assembly on top of the
committed segs 1–2:
- **Seg 3 (prologue).** Instantiated `prologue_sim` at the call boundary. The
  zero-init `hmemF` blocker (RESUME-CALL ★/§6) cleared: off the callee user
  frame, IL↔machine agreement comes from the caller's c4, and the region
  `[stackLo, s.sp)` is tiled by the free stack below the callee, the callee
  hole, and the user frame — an entirely `L.stackLo` argument (no `stackLo`
  link needed here). `hcmemZ` from `frameEnter`'s `zeroRange`.
- **Seg 4 (body).** The fuel IH applied to the callee body — recursion for free,
  both `.normal`/`.ret` land at `epiPos'`.
- **Seg 5 (epilogue).** `epilogue_sim`; the saved return address transported
  through the body via `hBodFr` + `State_loadWord_congr8` (`s1.sp = callee.sp`
  from StInv c5), `ra'` evenness from `halign` + `hhere4`.
- **Seg 6 + assembly.** `run_retStoresFrom` for the ret-stores (its over-strong
  `∀ s` no-wrap hypothesis fixed to a threaded per-state bound); the caller
  StInv rebuilt against the exit state (slots survive via an `m ↔ m_epi`
  frame-agreement chain + `loadWord_congr_range`); six-segment clock
  composition with `FramesPres` carried at the caller level.

New statement hypothesis `hstackLo : stackLo = L.stackLo` (true by construction —
`layoutOf` sets the field; needed only for the c4 callee-hole/free-stack
reconciliation). New reusable atoms: `State_loadWord_congr8`/`loadWord_congr_range`
(MemFacts), `not_memRange`/`memRange_or_not` (Defs). `set_option maxHeartbeats
400000` for the call case's large defeqs.

**Axiom hygiene.** Reaching `[propext, Quot.sound]` also required fixing
**pre-existing** `Classical.choice` taint introduced by the zero-init rework
(commits `ec60b1a`/`53948c9`): `storeWord_zero_mem_inside` (`simp` →
`simp only [...]; rfl` over the concrete byte window), `run_zeroFrame` (an
`omega` on a negated `memRange` conjunction — split via `not_memRange` — plus a
base-case `simpa`), and `prologue_sim` (`by_cases` on `memRange`, which has no
`Decidable` instance and fell back to `Classical` — replaced with the
constructive `memRange_or_not`). Lesson reinforced: never hand `omega` a
`¬(P ∧ Q)`, and never `by_cases` an instance-less `Prop`.

Campaign frontier now: Phases 1/2 (encode/decode + AsmFacts discharging the flat
layout obligations `hdat`/`hdbase`/`hdpos`/`hpad`/`hfn`/`halign`/`hstackLo`) and
Phase 6 (`prog_sim`, the lone remaining `sorry`, in `Defs.lean`).

## 2026-07-02 (compile_sim campaign) — Phase 0.1: the P1 frame-padding oracle

First step of the `compile_sim`-for-Prog campaign (docs/RESUME-PROGSIM.md).
Implemented decision **P1** (§2): `Prog.frameEnter`/`exec`/`run` gain a
`pad : Name → Nat` semantics oracle (∀-quantifiable like `dbase`/`sp₀`). The
IL-observable frame base (`frameReg`) stays at `spCaller − frameSize`
UNCHANGED; the propagated `sp` drops an extra `pad` bytes — the hole the IL
skips so that, at `pad := userOff`, IL `sp` coincides with the machine `x2` at
every call depth. The IL overflow check absorbs the hole (stack budget
subsumed). **Compiler/shim/QEMU untouched (FROZEN)**; `pad = fun _ => 0`
reproduces the old semantics exactly — the entire differential suite +
`Prog.lean` #guards re-green unchanged.

New executable validation in `CompileTests.lean` (Stage 4c): `framesAgree`
checks that every stack byte the IL wrote agrees with the machine
byte-for-byte. `p1_chain_userPad`/`p1_rec_userPad` pass at `pad = userPad`;
`p1_chain_pad0_diverges`/`p1_rec_pad0_diverges` show the OLD `pad = 0` IL
diverges from the machine as soon as a callee (depth ≥ 1) writes its frame —
the address gap P1 closes is thus real, not vacuous.

**`ProgSim/Defs.lean` (commits 2fa8faf + this):** the relation scaffold, all
`sorry`-free defs + `sorry`'d statements, in the new `LowIRProgSim` lib target
(rooted at `Defs`, in `defaultTargets`; build-root trap handled up front).
- §3.1/§3.4: `Layout` + `layoutOf` (from the FROZEN `compileProgT`),
  `Installed` (+ computable `codeInstalledB`/`dataInstalledB`, #guard'd by
  loading real blobs into the trusted `Rv64i` machine), `execT` (write-
  footprint instrumentation) + `runT`. Footprints #guard'd exactly: sub3→0,
  frameLocal's sd→its 8 frame addresses, caller inherits them.
- **`execT_erase` PROVED** (via `execT_map_exec`: erasing the footprint by
  `Option.map` yields `exec` exactly — a structural fuel induction, both
  functions recursing only at `fuel`). Axioms: `[propext, Quot.sound]` only,
  no `sorryAx`. The Phase 0.3 footprint-erasure obligation is discharged.

**Phase 0.2 — `ProgSim/ExecFacts.lean`:** 42 one-layer `exec_*` unfolder lemmas
for `Prog.exec` (ported from the Ctrl set, retargeted for dbase/pad/the real
`call`/ld/sd/cref/clen), each a one-line `simp [exec, …]`, in `namespace
LowIR.Prog`. They peel exactly one fuel layer so no downstream proof runs
`simp [exec]` with an IH in scope (the OOM trap).

**Phase 3 (start) — `ProgSim/WordMem.lean`:** the 64-bit LE load/store algebra
on the trusted `Rv64i.State` — the reusable heart of the frame-slot facts.
`loadWord_storeWord_same` (round-trip, no overflow hypothesis: the 8 byte
addresses differ by distinct literals), `storeWord_mem_of_ne`/`_outside`, and
`loadWord_storeWord_disjoint` (a store to `[a,a+8)` leaves a load at a
non-overlapping `[a',a'+8)` untouched). Proof note: `bv_decide` can't handle
`>>>` in this toolchain, so byte reconstruction goes via `getLsbD`
extensionality. Factored through one reusable lemma `byte_bit` (bit `i` of the
shifted byte `c` = `v`'s bit `i` iff `i ∈ [c,c+8)`); the round-trip is then the
OR of eight windows tiling `[0,64)`, closed by `omega`. Two toolchain gotchas
the speed turns on: `omega` rejects a *Bool*-valued goal (convert via
`Bool.eq_iff_iff` first) and that `rw` leaves an `↔ True` wrapper `omega` can't
strip (`iff_true` in the `simp` set). ~sub-second, no raised heartbeats
(down from a 12 s / 128-way bit-blast first cut).
- §3.1 relation: `memRange`/`MachPriv` (+ computable `machPrivB`, #guard'd:
  blob byte private, slot byte private, user-frame byte NOT — and the P1
  tiling `sp + userOff = sp0 − frameSize`), `MachStack`, `StInv` (sp≡x2,
  registers-in-slots, Installed, memory-off-private, current-hole shape,
  8-align), `SimPre`, `userPad`.
- §3.3: `prog_sim` fully stated (sorry) — the self-contained payoff every
  ProgLib function composes with (const data at `codeBase+segStart` both
  sides; rets in a-regs; memory agrees off blob+stack).

`lower_sim`/`call_sim` (§3.2) are DEFERRED to the StmtSim/CallSim phases: their
statements need the compile-time `Emitted` predicate that Phase 2 characterizes
and the Phase 4.1 vertical slice validates — stating them blind is the
expensive failure mode. Next: port the one-layer `exec_*` unfolder lemmas
(Phase 0.2), then the vertical slice.

## 2026-07-02 (later still) — Ext. 12: const data segment + cref/clen

Commits ff8867c + (this): `Program := { env, data }`; `cref`/`clen` give
reference-to-const-slice (ptr+len), addresses ∀-quantified via `dbase` (the
D8 `sp₀` move). Compiler appends the data segment to the blob; `cref` lowers
to a `jal t0,+4` pc-read + fixed delta synth — NO auipc, the 16-encoding
surface and position-independence survive. `cmain` re-drives the whole
library off const slices (inputs from rodata, frame holds only the output
buffers) with the same 8 observables as the staged `main`; validated at all
three altitudes again (IL `cmain_il_ok`, differential `diff_lib_cmain` +
`diff_sumdata`, QEMU byte-for-byte). `make dismain` now labels data objects
too (`<hex1src>` shows its ASCII in place). Design record: LOWIR-DESIGN.md
Ext. 12.

**Layout convention discharged (same day):** the data-segment layout is now
ONE definition (`Prog.dataOffsetsFrom`/`dataSegment`) consumed by both the
IL harness and the compiler, with the correspondence PROVED
(`dataSegment_at`, `installData_at`, `dataOffsetsFrom_shift` — the first
sorry-free theorems about the Prog layer; blob byte-identical before/after
the refactor).

## 2026-07-02 (later) — the library on Prog: strlen/strtoull/hex0/hex1 + driver

`lean/LowIR/Lib.lean` (commit 8ba9a8f): the four programs as real D7/D8
FUNCTIONS (params/rets/frames) + a `main` driver staging all inputs in its own
frame and calling all of them (8 observables). hex0/strtoull/strlen are ports
of the Ctrl versions; **hex1 is new, written from HEX1.md** — two-phase
scan/emit, rel32 refs, and the 256-entry label table in hex1's OWN frame
(4-byte LE entries = pos+1; 0 = undefined; zeroed by unrolled `sd x0` since
frame memory is not implicitly zero) — the D8 frame design carrying real
weight for the first time. Validation both ways: IL vs specs
(`Hex0.coreSpec` full battery, `Hex1.coreSpec1` 23-case battery + hex0's
battery for the shared-input promise, `strtoullConfSpec` incl. 2⁶⁴
saturation), and differential through the compiler onto `Rv64i.step` bytes
(each function + byte-for-byte output regions + the whole driver). All
green, sorry-free, in the default build. This is the pre-verification
baseline the correctness work will target.

**QEMU smoke test (aa76f9d):** the compiled blob also runs on real
`qemu-system-riscv64 -M virt -bios none` — `lean/DumpProgMain.lean` emits
`bare/progmain.{bin,inc,expected}`, `bare/shellmain.s` (unverified shell)
calls `main` inside the blob (it's position-independent) and prints the 8
observables over the UART: output matches the IL-computed expectation byte
for byte (`cd bare && make run-progmain`). Three altitudes now agree on the
full library run: IL semantics ≡ compiled bytes on the Lean Rv64i model ≡
QEMU.

Reverse-chronological execution log for the libc-formalization effort (design doc:
[LIBC-FORMALIZE.md](LIBC-FORMALIZE.md); status: [archive/STATUS.md](archive/STATUS.md) §LowIR).

## 2026-07-02 — D7/D8 compiler cut: Prog IR + executable compiler + differential tests

The [RESUME-LOWIR-COMPILER.md](RESUME-LOWIR-COMPILER.md) mandate, all landed
(commits 16b7296, 1be7e63; build target `LowIRCompile`, in `defaultTargets`):

- **`LowIR/Prog.lean`** — the D7/D8 IR, executable: named activation-local
  calls (fresh zero-init regs, params-only binding, rets-only copyback,
  arity-indexed `Vector`s, `wf`/`wfEnv` Ext. 8), D8 frames (semantic
  unwritable `sp`, `frameEnter` overflow → `none`, `frameReg` binding,
  structural sp restore), `ld`/`sd` (Rv64i byte order), `annot`. 18 `#guard`s
  incl. rec(3000) tripping the overflow check.
- **`LowIR/Compile.lean`** — memory-locals (-O0) compiler to RV64I: frame
  `[ra | slot per IL reg | user frame]`, t0/t1 lowering, SymInstr label
  streams, two-pass layout+resolve (range-checked imm12/B/J), a0..a7 call
  marshalling, prologue `sd x0` zeroing to match IL zero-init exactly.
  Entry stub `jal ra, entry`; halt pc = codeBase+4 backed by a self-loop
  landing pad — **differential testing caught the pad's absence**: the first
  function sat AT the halt address, so entering it silently stopped the
  machine (rec(0) passed by coincidence — the classic reason diff tests
  need non-trivial expected values).
- **`LowIR/CompileTests.lean`** — 16 `native_decide` differential theorems
  (IL `Prog.exec` vs compiled bytes on `Rv64i.step`): arith, bitops,
  whole-program encode/decode round-trip, sumOdd (while+ife+contL),
  findByte (brk-through-loop), nested brkB 1, early ret, memset with
  byte-for-byte data-region comparison, frame-local ld/sd, 2-function and
  3-deep chains, rec(10); + compile-refusal guards (frame > imm12, missing
  entry).

Not in this cut (per plan): verification of the compiler (`compile_sim`-style
theorem for Prog), definite-assignment optimization, >imm12 frame offsets,
recursion policy C5 (executably: it just works on fuel + overflow check).

## Previous turn

Items, in order: (a) `strtoull10_correct` sorry-free · (b) label-based compiler so
`LowIR.Ctrl` programs reach real RV64I bytes · (c) re-prove hex0 on the flat ret-cascade.

- **(a) — DONE.** `strtoull10_correct` proved sorry-free (`CtrlStrtoull10Proof.lean`): the IL
  computes the leading-digit left-fold for all inputs (geu digit loop; body_digit/body_break/
  digit_loop + prelude peel + block-catch). The geu/threshold foundation is reused. Earlier note: The wrapping `strtoull10_correct` proof fought
  signed (`slt`) comparisons under `bv_omega`, so it's scaffolded (`sorry`). Per the
  overflow discussion, built the **conformant `strtoull`** instead (`CtrlStrtoull2.lean`):
  C/POSIX overflow — saturate to ULLONG_MAX + `errno=ERANGE`, returned as `(x12,x14)`
  (no globals). Threshold `0x1999999999999999` built in-prelude; unsigned (`geu`)
  comparisons. **Validated** vs a conformant reference (value+errno, `native_decide`),
  incl. exact 2⁶⁴−1, 2⁶⁴ overflow, 20-nines overflow. The functional *proof* (of either
  version) remains: the tractable path is the **geu-based** digit loop (same shape as
  `strlen_loop` + the accumulator), since `geu`/`ult` are `bv_omega`-friendly.
- **(b), (c)** — not yet started.

## Done

- **Control-flow IL `LowIR.Ctrl`** (`lean/LowIR/Ctrl.lean`) — LowIR extended with
  `block`/`while`/`brkB k`/`contL k`/`ret` and an `Outcome`-threaded clocked big-step
  `exec`. `ret` absolute (caught at the function boundary); `brkB` counts blocks,
  `contL` counts loops (two de Bruijn spaces, CompCert-style). 3 `#guard` sanity checks.
  - **Design decisions** (recorded from the design discussion): unify break with
    block-exit; `continue` the lone loop-targeted exception; `break-loop` unnecessary
    (wrap loop in a block); `ret` kept as its own *absolute* outcome (not encoded as
    `brkB N`) — position-independent, generic at the future call boundary, trivial in
    proofs; the compiler lowers all three to scope-boundary-label jumps.
  - **strlen re-proved** (`CtrlStrlen.lean`, sorry-free). Finding: *no* ergonomic
    change — strlen has no early exits, so the outcome is pure `.normal` plumbing.
  - **hex0 with flat `ret` cascade** (`CtrlHex0.lean`) — errors are `set status; ret`;
    the hex-digit path is a flat `ife guard (err) skip` sequence, replacing the nested
    ifes + `in_idx := in_len` poison hack. Validated vs `Hex0.coreSpec` (17 cases, IL level).
  - **strtoull base-10** (`CtrlStrtoull.lean`) — `block { while(true) { … brkB 0 … } }`
    (break-out-of-loop), `acc*10 = (acc<<3)+(acc<<1)`. Validated vs a Lean reference
    incl. >2³² and 2⁶⁴ wraparound.
  - **break/block proof primitives** (`CtrlStrtoullProof.lean`) — `exec_block_catch`,
    `exec_while_brk`, `exec_seq_brk`, `exec_ret`, … each a one-line `by simp [exec]`.
    **Ergonomics result: the control-flow machinery is nearly free to reason about.**

- **Original LowIR + verified-compile pipeline** (`lean/LowIR.lean`) — structured
  three-address IL, `compile : Stmt → List Rv64i.Instr` (to the 16-instr trusted
  surface), `encode` (byte-exact inverse of `Rv64i.decode`). `strlen` end-to-end on the
  real `Rv64i.step` machine + hex0 ≡ `coreSpec` battery (`native_decide`).
  - **strlen_correct** (`StrlenProof.lean`) — functional correctness for all strings,
    sorry-free, structured induction.
  - **T1 framework** — `Layout`/`Installed`/`Agree`/`NoSelfModify` + `compile_sim`
    (statement; proof deferred per instruction).
  - **hex0_correct** (`Hex0Proof.lean`) — IL ≡ `coreSpec` stated with proof plan (deferred).

- **IL-altitude survey + plan** (`LIBC-FORMALIZE.md` §6) — CompCert/CakeML/Frama-C/
  Tree-Borrows/POSIX; the structured↔flat boundary; LowIR at the Cminor altitude.
