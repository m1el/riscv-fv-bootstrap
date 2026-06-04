# RESUME — hex1 campaign handoff (written 2026-06-04, pre context-clear)

Read together with **REFINE1.md** (the Refine1 proof plan: offset map,
architecture, gotchas — keep it updated as you go). This file is the
session-state handoff: what is done, what is literally mid-flight, and the
exact workflow being used.

## TL;DR

hex1 = hex0 + `:<label-byte>` (define) / `%<label-byte>` (emit i32 LE,
end-relative `label − (field_pos+4)`, x86 rel32 convention). Separate program,
separate proof; shares lemmas with hex0. All decisions live in HEX1.md.

DONE and committed (everything green at HEAD):
- **Program**: HEX1.md, hex1.c (two-pass scan/emit), bare/core1.s
  (181 instrs, 16-encoding ISA: hex0's 12 + SUB SRLI LD SD; `blt` not `bltu`
  — see isa-surface-discipline memory), shell1.s, input1.hex, Makefile
  targets hex1.elf/run1.
- **Testing**: tools/test_hex1.py — python oracle vs hex1.c vs core1.s under
  qemu-riscv64 (tools/hex1_drv, tools/core1_drv), 36 pinned + 22k fuzz, ALL
  green; bare-metal `make run1` byte-identical to C output.
- **Lean spec layer** (sorry-free): Hex1/Spec.lean (scan1/emit1/coreSpec1,
  flat St1 machine, capacity factorization `short ⟺ cap < m`),
  Hex1/Grammar.lean (Lex ≅ HEX1.md BNF; lexer sound+complete ⇒
  total+deterministic; collect/emitT; scan1_parses/emit1_parses/
  decode1_grammar/valid_coreSpec1).
- **Model**: Rv64i.lean extended (+sub/srli/ld/sd, loadWord/storeWord in
  explicit 8-read form). hex0 proofs unaffected.
- **Certification**: Hex1/Certify.lean — native_decide, deployed bytes ≡
  coreSpec1 (embedded 267-byte input + 27-case battery).
- **Coq spec layer**: Spec1.v + Grammar1.v proved (mirror of the Lean
  theorems; Print Assumptions ⇒ only functional_extensionality_dep).
  Registered in _CoqProject with Image1.v; `make` green in coq/.
- **Refine1 (Lean)**: lean/Hex1/{RefineBase,DecodeFacts,Refine}.lean — see
  REFINE1.md "Files" for the chunk-by-chunk DONE list. 1830 lines green
  through chunk 7 (comment inner loop).

## MID-FLIGHT: none (chunks 8-11 landed; see REFINE1.md DONE list)

Pass-1 iteration lemmas are ALL proved: p1_spacing, p1_comment, p1_labelDef,
p1_ref, p1_byte (+ the chain tails p1_colon_tail/p1_pct_tail/p1_fall_tail/
p1_high_ok/p1_high_unk/p1_low_read/p1_stop_split/p1_stop_fall/p1_low_ok/
p1_low_unk, the Result1 builders error_result1/short_result1, scan1_pos_le,
sub_ofNat, decode1_m, corePc_ne_zero). Next: pass1_correct (item 4 below).

Build check: `cd lean && lake env lean Hex1/Refine.lean` (NOT lake build).
Chunk workflow unchanged (python append scripts to /tmp, compile, commit
per green chunk).

## The established chunk workflow (IMPORTANT)

1. Write each chunk as a python append-script via the Write tool to
   /tmp/apply_chunkN.py (heredocs in Bash LOSE cwd — the shell resets to
   /var/data/bootstrap between calls; scripts use the absolute path).
2. `cd /var/data/bootstrap/lean && python3 /tmp/apply_chunkN.py && lake env
   lean Hex1/Refine.lean ...` — compile, iterate with small patch scripts.
3. Commit per green chunk (user explicitly wants intermediate checkpoints).
4. Port hex0 idioms VERBATIM where a corresponding lemma exists
   (Hex0/Refine.lean) — first-try success rate is far higher than inventing.
   Mapping: CodeLoaded→CodeLoaded1, wordAt→wordAt1, Image→Image1, 324→724,
   `(by decide)` decode args → named dec_<off> facts (Hex1/DecodeFacts.lean),
   `(by decide)` length bounds → `(by rw [coreBytes_len]; omega)`.

## Remaining work, in order (after chunk 8)

1. **p1_labelDef** (offsets 92/96 dispatch → 264..300): li_beq_ne×5 then
   li_beq_eq → 264; then bgeu (EOF → exit_zero at 712 TrailTok — build
   Result1 via spec: scan1 (c::[]) = (lab,pos,.TrailTok), coreSpec1 = (8,[],0)
   needs pos ≤ cap ⇒ not short); else add/lbu/addi reads label byte ℓ;
   slli/add (slot_addr lemma, needs ℓ<256 from bytes_ok); ld (loadWord_slot
   via inv.tbl); bge sign test (encodeSlot_some_nonneg p<2^63 from lab_le +
   pos_le + cap63 → DUP exit 688 / encodeSlot_none_neg → continue); sd
   (storeWord_slot ⇒ TableLoaded (setLabel lab ℓ pos)); j 36. New P1Inv with
   lab2 = setLabel lab ℓ pos, same pos; spec step: scan1 unfold (.Col path):
   scan1 .High lab pos (58::ℓ::rest₂) = scan1 .Col lab pos (ℓ::rest₂) =
   match lab ℓ … (use Hex1.scan1 equations; dup case gives .Dup exit).
   lab_le extends: setLabel … pos maps ℓ↦pos ≤ pos ✓.
2. **p1_ref** (100/104 → 304..328): bgeu EOF → TrailTok exit; addi consumes
   label byte; sub t3=cap−t1 (BitVec sub of ofNat: cap,pos ≤ … need value
   lemma ofNat cap − ofNat pos = ofNat (cap−pos) given pos ≤ cap — prove via
   toNat/omega); li t4,4; blt (slt_ofNat, both < 2^63 via cap63) → Short exit
   640 (spec: scan1 stops … careful: SHORT is the cap-crossing case — spec
   scan1 is CAP-FREE, the machine shorts iff cap−pos < 4; Result1 via
   coreSpec1: m ≥ pos+4 > cap ⇒ `if cap < m` true ⇒ (2,[],0); need
   scan1-monotonicity lemma: scan1 .High lab pos rest = (lab',m,st) → pos ≤ m
   — prove by functional induction or strong induction on rest length, for
   all St1 states — REQUIRED also for byte-short and final conversion);
   else addi t1+=4, j 36; new P1Inv pos+4, spec .Pct step.
3. **p1_byte** + errors (108..156, 160..212 stop-chain, 216..248, 252..260):
   port hex0 high_parse/low_parse/li_blt_t/li_bge_t chains. Pass-1 computes
   NO values (range checks only) — simpler than hex0. Errors: Unknown (676),
   Split (652), Trailing (664) exits via exit_zero + spec scan1 error steps;
   capacity check at 252: bgeu t1,a3 — Short(640) iff pos ≥ cap (machine
   bgeu unsigned; pos,cap < 2^63 ✓ ult_ofNat both ways), else t1++ j 36.
4. **pass1_correct**: strong induction on rest.length from P1Inv; EOF base:
   bgeu taken at 36 → 360 gives P2Start (scan1 [] = (lab,pos,.Ok)).
   Combines p1_spacing/p1_comment/p1_labelDef/p1_ref/p1_byte + error exits;
   conclusion: ∃ fuel s', runFuel = s' ∧ (Result1 s' inp cap ∨
   ∃ labF m, P2Start inp cap s' labF m).
5. **Pass 2**: two li steps 360/364 → P2Inv (define: pc 368, t0/t1, out
   region = emitted bytes via `∀ j < emitted.length, mem(outAddr+j) =
   ofNat 8 (emitted.getD j 0)`, TableLoaded labF unchanged, scan-validity
   side condition `Hex1.scan1 .High labNow (emitted.length) rest =
   (labF, m, .Ok)` to rule error paths out, emit telescope
   `Hex1.emit1 .High labF 0 inp = (emitted ++ (emit1 .High labF
   emitted.length rest).1, (emit1 …).2)`). Iterations: spacing (same
   dispatch offsets 384..420), comment (600..624 inner loop — port
   comment_loop1 with exit→628), labelDef skip (516/520), byte
   (440..512: nibble VALUE chains — port hex0 high_parse/low_parse +
   combine_nibbles + sb store; out-region write: storeByte at outAddr+pos,
   preserves code/input/table via disjointness incl. out_fits), ref
   (524..596: ld slot → bge sign → UNDEF exit 700 via exit_t1 (a1 = t1 =
   field_pos = emitted.length; coreSpec1 undef branch) / defined: addi
   t5=t1+4, sub off64 = ofNat p − (ofNat pos + 4), 4×(sb;srli) — THE
   offBytes VALUE LEMMA: bytes stored equal Hex1.offBytes p pos as
   BitVec 8s; statement ≈
   `((BitVec.ofNat 64 p - (BitVec.ofNat 64 pos + 4)) >>> (8*k)).setWidth 8
    = BitVec.ofNat 8 ((Hex1.offBytes p pos).getD k 0)` for k<4, p,pos+4 <
   2^63; prove via toNat + Int.emod arithmetic (offBytes uses Int emod
   2^32; BitVec sub = (p − pos−4) mod 2^64; (x mod 2^64) mod 2^32 … =
   (x mod 2^32) since 2^32 ∣ 2^64; byte k = /2^(8k) mod 256 — fiddly,
   do it as its own lemma with omega+Int lemmas).
6. **pass2_correct** (induction like pass1; EOF → bgeu taken at 368 → Ok
   exit 628 via exit_t1: a0=0, a1=t1=|out|; Result1 needs the emit telescope
   collapsed: emit1 [] = ([], .Ok) so emit1 whole = (emitted, .Ok); then
   coreSpec1: scan_ok ⇒ decode1 = (emitted, m, .Ok); `if cap < m` false via
   m_le; out region matches via P2Inv out field; ALSO needs
   |emitted| = … the machine a1 = ofNat |emitted| and spec out.length —
   equal by the telescope (emit output IS emitted)).
7. **core1_refines**: define observe1 := Harness1.observe; compose
   init_phase + 2-step pass1 entry (28/32: li t0,0; li t1,0 → P1Inv
   noLabels 0 inp with spec := rfl; note Pass1Entry ALREADY has tbl
   noLabels) + pass1_correct + pass2_correct; convert Result1 to the
   observe/coreSpec1 tuple equality like hex0's core_refines conversion
   (readMem/range_getD/decode bytes <256 lemmas — port coreSpec_props
   analog: bytes of emit1 < 256: byte case hi*16+lo < 256 via nibble_lt;
   offBytes entries < 256 by construction %256).

## Key landmarks

- lean/Hex1/Refine.lean structure (1830 lines): blocks li_beq_ne/eq,
  li_blt_nt/t, li_bge_nt/t → WellFormed1/cap63 → encodeSlot/TableLoaded/
  sign tests → shl3_ofNat/slot_addr/loadWord_slot/storeWord_slot/
  tableLoaded_storeByte → region preds InputLoaded + preservation
  (codeLoaded1/inputLoaded × setPc/rset/storeByte/storeWord) → InitInv/
  Pass1Entry/init_iter/init_loop → code_initOn1/in_initOn1/entry_block/
  init_phase (fuel 772) → Result1/exit_zero/exit_t1 → P1Inv/p1_prefix →
  suffix_step/p1_spacing_tail/p1_spacing → bgeu_eq_taken/comment_read1/
  comment_loop1.
- Build: `export PATH=~/.elan/bin:$PATH; cd lean; lake build` (Refine.lean
  NOT yet in Hex1.lean root imports — add `import Hex1.Refine` when
  core1_refines lands; check directly via `lake env lean Hex1/Refine.lean`).
- Coq: `export PATH=~/.opam/CP.2025.01.0~8.20~2025.01/bin:$PATH; cd coq;
  make -j6`.
- Regen pipeline after ANY core1.s change: rebuild bare (`make hex1.elf
  hex1.bin`), re-fuzz (`python3 tools/test_hex1.py`), `python3
  tools/gen_image1.py`, `python3 tools/gen_decode1.py`, `lake build` —
  offsets in REFINE1.md/Refine.lean proofs assume the CURRENT 724-byte core1.

## Task list state

#5/#6 (Refine1 Lean) in progress as above. #7 (Coq side) untouched:
extend coq/Rv64i.v (+4 instrs — BREAKS RvCross.v embed: must extend embed,
decode_agrees (4 new decode lemmas), RvCrossExec step_agrees (4 exec lemmas;
ld/sd need an 8-byte memory bridge — reuse fetch32 bridge machinery in
RvCrossStep.v)), then Harness1.v/Certify1.v (vm_compute), then Refine1.v
port. TCB.md needs a hex1 section when the dust settles (new trust: shell1.s,
gen_image1.py/gen_decode1.py extraction, ld/sd/sub/srli vs riscv-coq until
the cross-check is extended).
