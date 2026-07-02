# Resume — hex0 completion + IL calls + IR design arc

Handoff for the session that (1) finished the hex0 functional-correctness proof, (2) added a
`call` construct to `LowIR.Ctrl` with a worked cross-call-disjointness example, and (3) worked
through a long design discussion on the memory model, borrows vs provenance, calling
conventions, the stack, and the `compile_sim` pass decomposition.

Companions: [LOWIR-DESIGN.md](../LOWIR-DESIGN.md) (decisions/alternatives/extensions + §4 compiler
passes), [MEMORY-BORROWS.md](../MEMORY-BORROWS.md) (separation discipline), [RESUME-LOWIR.md](RESUME-LOWIR.md)
(proof toolbox/gotchas). Build (from `lean/`): `lake build LowIR.CtrlHex0Proof LowIR.CtrlCall`.
Everything below is **sorry-free** (only sanctioned `sorry`: `compile_sim` in `LowIR.lean:370`).

## 1. Code that landed

**hex0 functional correctness — COMPLETE.** `LowIR/CtrlHex0Proof.lean`:
`hex0_correct : ∀ inp cap, (∀x∈inp, x<256) → inp.length<2^63 → cap<2^63 →
  Wf [⟨⟨inBase,inp.length⟩,.shared⟩, ⟨⟨outBase,cap⟩,.uniq⟩] →
  ∃ fuel, hex0Run (asBytes inp) cap fuel = Hex0.coreSpec inp cap`.
- Item A `body_step`: `body_space`, `body_comment`, `hexPath_eff` (6 arms) + `body_hex`.
- Item B `main_loop`: strong induction on `len−idx`, while-loop ≡ `decodeS` via `boundedRun`
  (per-byte capacity); composes the body lemmas + `decodeS_*` unfolders + bridges + comment
  reconciliation (`commentSkip`/`skipComment_run`) + borrow disjointness (`storeByte_preserves`).
- Item C: `boundedRun_nil_coreSpec`, `exec_lit`, `hex0_setup` (peels the 15-instr prelude), assembly.
- Infrastructure (reusable): `exec_mono`/`exec_mono_le` + one-layer `exec_*` eqns (in
  `CtrlStrtoullProof.lean`); the borrow layer `Slice`/`Perm`/`Borrow`/`Wf`/`Disjoint`/
  `storeByte_preserves`/`Disjoint.not_left`/`Wf.disjoint`; bridges `pnibR_eq_255_iff`/
  `pnibR_nibble`/`pnibR_lt_16`/`hexbyte_val`/`lowStop_iff`; `regionBytes`(+`_snoc`/`_store_self`);
  `ofNat_succ`.

**`call` construct — ADDED.** `LowIR/Ctrl.lean`: `Stmt.call (g : Stmt)` runs the callee body and
catches its `.ret`→`.normal` (a real function-return boundary, not inlining):
`exec (f+1) (.call g) s = match exec f g s with | some(s',.ret) => some(s',.normal) | other => other`.
`exec_mono` extended; one-layer `exec_call_{normal,ret,brk,cont,none}` in `CtrlStrtoullProof.lean`.
Existing hex0/strtoull proofs unaffected (purely additive).

**Worked example — `LowIR/CtrlCall.lean`.** `loadByteFn := .lbu 12 10 0` (leaf; `loadByteFn_spec`);
`writeThenLoad := .seq (.sb 11 13 0) (.call loadByteFn)` (writes `dst`, then calls callee to read
`src`); `writeThenLoad_spec`: given `Disjoint ⟨src,1⟩ ⟨dst,1⟩`, the callee loads the *original* `src`
byte — discharged by `storeByte_preserves`, callee used only via its spec. Demonstrates modular,
disjointness-aware reasoning across a call. **Caveat surfaced (see §4):** its spec is a *full-state
transformer*, which is non-modular for larger callees — the fix is frame-based specs.

**Docs added:** `MEMORY-BORROWS.md`, `LOWIR-DESIGN.md` (incl. §4 `compile_sim` pass decomposition).

## 2. Design decisions reached (recorded in LOWIR-DESIGN.md)

- **Memory = flat `Word→Byte` + borrows-as-contract**, NOT block-structured. Separation lives in
  *types/contracts*, threaded down to `Wf`/`Disjoint` hypotheses; keep the bottom flat & machine-faithful.
- **Single-threaded ⇒ `errno` is a plain global** (not TLS); recorded as a TCB assumption.
- **Calling convention split:** the *contract* (which registers/memory a function preserves) lives in
  the IL spec; the *enforcement* (save/restore + the explicit stack) lives in `compile_sim`, with the
  **ABI as a parameter**. The stack becomes explicit at the convention lowering (CakeML `stackLang` analog).
- **Unbounded register file (`Reg=Nat`)** ⇒ register spilling is a `compile_sim` obligation; isolation
  across calls is achievable by *register-set disjointness* (no convention needed at the IL).
- **`compile_sim` decomposition** (CompCert many-small-passes + CakeML to-the-bytes): 6 passes each a
  forward simulation with explicit `match_states`, composed by transitivity. Hard passes: (2)
  control-flow lowering `while/block/ret/call`→CFG — factor 2a/2b; (3) register allocation — use
  *translation validation* (untrusted allocator + verified checker). **Restricted-fragment-first**
  (structured control only, leaf/inlined calls, ≤31 regs) gets hex0/strlen to verified bytes early.
- **CompCert/CakeML lessons to copy:** small per-pass simulations; one shared memory model across all
  IRs; event/trace output (for I/O libc); external/unverified functions via pre/post+frame specs;
  verify the encoder to actual bytes; clocked functional big-step (already used — `exec_mono` is the cost).

## 3. Conceptual threads (for context)

- **Did the IL simplify the proof?** Yes for the functional layer (structured `ret` → flat error
  cascades; `exec` equations abstract PC/encoding), but it *relocates* machine complexity into the
  (unwritten) `Ctrl` `compile_sim`; pay-once and reused across the libc.
- **LLVM IR & stack:** `alloca` is explicit (program-visible stack), but SP/frame/save-restore/regalloc
  are backend; calling convention is an *attribute*; `noalias` ≈ uniqueness-in-signature; provenance
  rides in the pointer.
- **Borrows vs LLVM provenance:** a borrow = region (≈ provenance) + permission (shared/unique ≈
  `noalias`, NOT in provenance) + lifetime. Axes: spatial-only vs +exclusivity; copyable vs **affine**;
  operational-enforced vs logical-proved. Project pointers carry *no* provenance (flat `Word` +
  disjointness-in-contract) ⇒ dodges the int↔ptr-cast provenance quagmire; gives *soundly* what LLVM
  provenance gives heuristically.
- **FilC/CHERI:** "provenance in parallel RAM, cleared by non-pointer stores" = CHERI tagged memory /
  FilC InvisiCaps — the sane *operational* provenance model (clear-on-write = unforgeability theorem).
  Recommendation: if you ever go operational, **provenance → shadow/parallel RAM (CHERI/FilC)**, but
  **borrows → logical ghost state (RustBelt/Iris)** — two concerns, two homes. The `Word→Option(state,byte)`
  idea is the operational/instrumented variant: a single per-cell state can't represent full TB (needs a
  per-location *tree*); keep the `Option` (validity) if useful, keep permissions logical.
- **Can the models be mapped?** Yes, as interpretation/soundness theorems, not identity. Operational
  shadow ↔ logical ghost: Iris `state_interp` + adequacy (RustBelt). Provenance ↔ borrows: modulo the
  affine axis — **linear capabilities ↔ unique borrows; ordinary caps ↔ shared refs**. Borrows are the
  more expressive coordinate (subsume provenance's region + add exclusivity) and can *generate* the
  provenance/`noalias`/capability facts a lower level wants.

## 4. Open threads / next steps

**(A) Frame-based call specs — the main unfinished thread.** The critique: zero *operational* isolation
+ full-state-transformer specs (as in `writeThenLoad_spec`) forces reasoning across two functions' full
states — non-modular. The fix is NOT operational isolation (the machine has one shared store) but
**separation-logic frame-based specs**: state only the callee's footprint + declare its frame
(`∀ r ∉ W, st'.rget r = s.rget r` for registers; `∀ a, ¬S.has a → st'.mem a = s.mem a` for memory),
then a caller frames its disjoint state through untouched. The disjointness the frame rule needs IS the
borrow `Slice`/`Disjoint` contract; `hex0`'s `body_*` lemmas already carry exactly these preservation/
frame clauses (`Regs` preservation, "input unchanged"). **Outstanding offer:** recast `CtrlCall.lean`'s
specs into footprint+frame form and prove a generic *frame lemma* ("anything disjoint from a function's
declared footprint is preserved across a call to it"), as the concrete "is calls-reasoning doable or
needs more factoring" test. *Do this next.*

**(B) Return values / register convention at the IL:** currently no first-class return value — the
callee leaves results in spec-designated register(s) (demo: `x12`); register sharing is full (zero
isolation), survival known only from the callee's spec footprint. Consider a structured
`call g (args) (results)` (LLVM-style) if you want footprints partly enforced by the IL. ABI return
register / `ra` only appear at `compile_sim`.

**(C) Other extensions (from LOWIR-DESIGN.md §3):** wider load/store (`lw/sw/ld/sd` — the one true
expressiveness gap for structs); stack-as-`mem`-region + SP (each frame a unique `Slice`); `alloca`/
fresh-region primitive; ABI-parameterized `compile_sim` (the 6 passes); event traces for I/O libc;
factor the toolbox (`exec_mono`, borrow layer, region helpers) into shared files.

**(D) Pre-existing TODO:** conformant `strtoull` functional proof (foundation in `CtrlStrtoull2Proof`);
the original `LowIR` `compile_sim` sorry.
