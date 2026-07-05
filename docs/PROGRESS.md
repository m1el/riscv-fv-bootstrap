# PROGRESS — LowIR & libc-formalize

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
