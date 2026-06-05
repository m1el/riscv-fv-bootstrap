# Refine1 — plan and progress for `core1_refines` (hex1 general refinement)

## COQ PORT (coq/Refine1.v) — IN PROGRESS (2026-06-04)

Chunk-by-chunk port of the (COMPLETE) Lean proof below, in hex0's
coq/Refine.v idiom (Z model; step lemmas via `ltac:(vm_compute;
reflexivity)` decode at concrete offsets — NO DecodeFacts needed; fixed
fuel + runUntil_stab at the end). DONE so far (each committed):
- chunk 1: engine — nthb1/wordAt1/CodeLoaded1/fetch_code1, 16 step1_*
  lemmas, storeWord projections/mem-map/frame/get + digits8 +
  loadWord_storeWord, wsub_id/wshr_div. Generic toolkit reused from
  Hex0Coq.Refine (wrap_small/wadd_id/toS_small/sltb_small/runUntil_*/
  rset_rget/li_block_frame/isSpace_cases...).
- chunk 2: li1_{beq_ne,beq_eq,blt_nt,blt_t,bge_nt,bge_t}; WellFormed1
  (+_cap63); encodeSlot/TableLoaded + sign tests; wshl3/loadWord_slot/
  storeWord_slot/tableLoaded_storeByte/_eqmem; InputLoaded + code/input
  × storeByte/storeWord preservation.
- chunk 3: InitInv/Pass1Entry records; init_iter/init_loop;
  code_initOn1/in_initOn1/entry_block/init_phase (772 steps).
- chunk 4: rset_zero, Result1(+_pc), exit_zero/exit_t1, P1Inv (17
  fields), p1_prefix (36..48 → 52), suffix_step1.
- chunk 5: scan1_spacing, p1_spacing_tail (52..88), p1_spacing.

Coq-port gotchas (beyond the Lean list at the bottom):
- NEVER leave `_` holes in `rewrite (lemma _ _ ltac:(lia))` — evars make
  lia fail ("Cannot find witness"); give explicit arguments.
- `f_equal. lia.` breaks when f_equal closes everything → use
  `f_equal; lia` (vacuously fine) and NEVER f_equal on `(a+72)+(-36) =
  a+36` shapes (mismatched structure) — plain lia handles atom-linear.
- `unfold Image1.xxx in *` does NOT reach inside defined predicates
  (InputLoaded etc.) — specialize the hypothesis first, then unfold in
  the result (see hbyteIn in p1_prefix).
- `subst c` may pick a wrong-direction equation (ht2 : rget s4 7 = c) —
  use `rewrite H` with the case-split equation instead.
- ltac:() holes inside long `rewrite (step1_x ...), a, b` chains can
  die with "No such goal" — pre-assert the side conditions (see hb3 in
  exit_zero) and split the rewrite chain.
- `cbn [LittleEndian.split_deprecated]`-style cbn-with-list does not
  reduce nat-indexed fixpoints; use cbv [name] (RvCrossExec split8).
- NEVER `simp scan1 in heq` when an induction hypothesis (IHn) is in
  context: simp's trailing eauto pass tries `apply IHn`, and unifying
  the evar goal `scan1 ?st ?lab ?pos ?l = ...` against heq's stuck
  `if`/`match` forces conversion to unfold the wf-recursion fixpoint
  (`by wf (length l) lt`) divergently — ~0.5 GB/s until OOM (killed
  three tmux sessions at 128 GB before diagnosis). Use
  `autorewrite with scan1 in heq` instead — identical rewriting, no
  eauto pass (0.7s). Goal-position `simp scan1` is fine.
  Bonus: `destruct (cond) eqn:E` DOES substitute+reduce cond inside
  hypotheses too, so no `rewrite E in heq` is needed after it.

NEXT (mirroring the Lean chunk order below): comment iteration
(bgeu_eq_taken port at 332..356 / scan1 comment unfolds / comment_read1/
comment_loop1 / P2Start / p1_comment), then labelDef (264..300, needs
loadWord_slot/storeWord_slot + error_result1/corePc_ne_zero), ref
(304..328 + scan1_pos_le/short_result1), byte path (108..260), p1_eof +
pass1_correct, pass 2 (P2Inv, ~7 iteration lemmas + offBytes value
lemmas — in Z these are MUCH lighter than the Lean BitVec versions),
pass2_correct, conversion + core1_refines (mirror hex0 core_refines:
fuel bound 772 + 50*|inp|·2 + slack <= 100000, |inp| <= 668).

Target theorem (lean/Hex1/Refine.lean):
```
core1_refines : ∀ inp cap, WellFormed1 inp cap →
  ∃ fuel, observe1 inp cap fuel = Hex1.coreSpec1 inp cap
```
sorry-free, no native_decide. Mirrors hex0's `core_refines` (Hex0/Refine.lean)
but with THREE loops (init / pass1 / pass2) and the label table region.

## Files

- `Hex1/RefineBase.lean` — DONE. Engine: CodeLoaded1/wordAt1/fetch_code1,
  16 step lemmas, storeWord frame + per-byte gets, `assemble_bytes`.
- `Hex1/DecodeFacts.lean` — DONE (auto-generated, tools/gen_decode1.py):
  `dec_<off>` for all 181 instructions + `coreBytes_len`.
- `Hex1/Refine.lean` — IN PROGRESS (the main proof). DONE so far:
  - li_beq_ne/eq, li_blt_nt/t, li_bge_nt/t blocks; WellFormed1 (+cap63);
    encodeSlot/TableLoaded + sign-test lemmas (chunk 1)
  - shl3_ofNat/slot_addr, loadWord_slot, storeWord_slot,
    tableLoaded_storeByte (chunk 2)
  - Region predicates InputLoaded + preservation lemmas
    (codeLoaded1/inputLoaded × setPc/rset/storeByte/storeWord);
    InitInv/Pass1Entry; init_iter/init_loop (chunk 3)
  - code_initOn1/in_initOn1, entry_block, init_phase:
    `runFuel 0 772 (initOn inp cap) = s' ∧ Pass1Entry s'` (chunk 4)
  - Result1, exit_zero/exit_t1 epilogues, P1Inv, p1_prefix (chunk 5)
  - suffix_step, p1_spacing_tail, p1_spacing -- the first COMPLETE pass-1
    iteration, validating the whole pattern (chunk 6)
  - bgeu_eq_taken, comment_read1, comment_loop1 (chunk 7)
  - P2Start structure + p1_comment: complete comment iteration, lands at
    loop head on drop q or P2Start at EOF (chunk 8)
  - corePc_ne_zero, error_result1 (Result1 builder for empty-output error
    exits, evaluates coreSpec1 by cases on Status), p1_colon_tail
    (dispatch 52->264), p1_labelDef ok/dup/eof (chunk 9)
  - sub_ofNat, scan1_pos_le (monotonicity, induction on length bound),
    decode1_m, short_result1 (Result1 builder for the Short exit),
    p1_pct_tail (dispatch 52->304), p1_ref ok/short/eof (chunk 10)
  - byte-path chain tails: p1_fall_tail (52->108), p1_high_ok/p1_high_unk
    (108->144/676), p1_low_read (144->160), p1_stop_split/p1_stop_fall
    (160->652/216), p1_low_ok/p1_low_unk (216->252/676) (chunk 11a,
    generated by python -- li-chain blocks only touch t3/pc)
  - p1_byte assembled: ok (pos+1) / Unknown / Trailing / Split / Short
    (chunk 11b)
  - p1_eof (bgeu taken at 36 -> P2Start) + pass1_correct: strong induction
    on the suffix-length bound, dispatch by char class over the five
    iteration lemmas; conclusion Result1 OR P2Start (chunk 12).
    PASS 1 IS DONE.
  - P2Inv (incl. scan_inp whole-scan field, residual scan_ok for
    control-flow totality + write bounds, emit telescope spec), p2_entry,
    emit_result1, p2_ok_exit, p2_prefix, p2_spacing_tail/p2_spacing
    (chunk 13a); comment_read2/comment_loop2 (textual port of pass 1's,
    offsets 600..624, exits 368/628) + p2_comment (chunk 13b)
  - p2_byte_fall (384->440), p2_hi_value/p2_lo_value (440/472, nibble
    VALUES via nibble_addi), p2_read2 (460..468, no EOF check) (chunk 14a);
    p2_byte assembled -- token shape DERIVED from scan_ok by contradiction,
    combine_nibbles + sb + out_mem extension via getElem?_append (chunk 14b)
  - offBytes_b0..b3 (the i32 LE value lemmas: BitVec sub/srli/setWidth vs
    Int emod 2^32 -- one omega each after toNat-ification), offBytes_len,
    p2_undef_exit (exit_t1 at 700), p2_lbl_tail, p2_labelDef (labNow l
    = none derived from scan_ok; labNow' = setLabel) (chunk 15a)
  - getD_append, p2_ref_tail (384->524), p2_ref: slot ld + blt sign test ->
    Undef exit (emit telescope collapse) / 4x(sb;srli) stores with
    offBytes_b0..b3, 4-way out_mem case split (chunk 15b)
  - p2_eof (bgeu at 368 -> Ok exit via p2_ok_exit) + pass2_correct
    (chunk 16). PASS 2 IS DONE.
  - offBytes_lt, emit1_props (joint scan/emit walk: emit stays <= m, bytes
    < 256; .Low-state precondition hi < 16 like hex0's decodeS_bytes_lt),
    coreSpec1_props, p1_entry (28/32), observe1, CORE1_REFINES (chunk 17).
  THE CAMPAIGN TARGET IS PROVED (sorry-free, no native_decide);
  Hex1.Refine is imported from Hex1.lean (full lake build green).
  Remaining (separate effort): the Coq side -- RESUME-HEX1.md item "#7".
  OLD plan notes below for reference: P2Inv,
  pass-2 lemmas (incl. offBytes value lemma vs sb/srli chain at 556..588),
  pass2_correct; observe1/coreSpec1 conversion; core1_refines.
  PROOF-STYLE GOTCHAS hit so far (beyond hex0's):
  - `set ... with` is Mathlib — use `let x := e; have hx : x = e := rfl;
    try rw [← hx] at hu` (hex0 idiom).
  - Apply region lemmas through `codeLoaded1_setPc`-style wrappers; a bare
    application against a let-bound state forces whole-State unification
    (setPc vs storeWord chains) → whnf timeout.
  - `congr 1 <;> omega` (robust whether congr closes or not); after branch
    `rw [hslt]`, resolve pc with `rw [show s.pc + imm = target from by
    rw [hpc]; decide]`, never `congr 1` on a deep state.
  - decides on wordAt1/getD need maxRecDepth 8000; heavy haves need
    maxHeartbeats 1000000.

## core1 offset map (from DecodeFacts; addresses = coreAddr+off, coreAddr=0x80000090)

```
INIT:   0 t3=a4; 4,8 t4=a4+2048; 12 t5=-1
        16 sd t5,0(t3); 20 t3+=8; 24 blt t3,t4→16        (init loop, 256×)
PASS1:  28 t0=0; 32 t1=0
  P1LOOP=36 bgeu t0,a1→360(P2 init)
        40 add t3,a0,t0; 44 lbu t2; 48 t0++
        52/56 #→332; 60/64 ;→332; 68/72 \n→36; 76/80 ␣→36; 84/88 _→36
        92/96 :→264; 100/104 %→304
        108/112 blt48→676(unk); 116/120 bge58→128; 124 j144
        128/132 blt65→676; 136/140 bge71→676
        144 bgeu t0,a1→664(trail); 148 add; 152 lbu; 156 t0++
        160..212 7×(li;beq stop→652(split))  [10,32,95,35,59,58,37]
        216/220 blt48→676; 224/228 bge58→236; 232 j252
        236/240 blt65→676; 244/248 bge71→676
        252 bgeu t1,a3→640(short); 256 t1++; 260 j36
  LBL:  264 bgeu t0,a1→712(trailtok); 268 add; 272 lbu t2; 276 t0++
        280 slli t3,t2,3; 284 add t3,t3,a4; 288 ld t4,0(t3)
        292 bge t4,x0→688(dup); 296 sd t1,0(t3); 300 j36
  REF:  304 bgeu t0,a1→712; 308 t0++; 312 sub t3,a3,t1; 316 li t4,4
        320 blt t3,t4→640(short); 324 t1+=4; 328 j36
  CMT:  332 bgeu t0,a1→360; 336 add; 340 lbu; 344/348 beq\n→36; 352 t0++; 356 j332
PASS2:  360 t0=0; 364 t1=0
  P2LOOP=368 bgeu t0,a1→628(Ok)
        372 add; 376 lbu; 380 t0++
        384/388 #→600; 392/396 ;→600; 400..420 spacing→368
        424/428 :→516; 432/436 %→524
        440/444 blt58→456; 448 t4=t2-55; 452 j460; 456 t4=t2-48
        460 add; 464 lbu; 468 t0++
        472/476 blt58→488; 480 t5=t2-55; 484 j492; 488 t5=t2-48
        492 slli t4,4; 496 or; 500 add t3,a2,t1; 504 sb; 508 t1++; 512 j368
  LBL:  516 t0++; 520 j368
  REF:  524 add; 528 lbu; 532 t0++; 536 slli; 540 add; 544 ld t4
        548 blt t4,x0→700(undef); 552 t5=t1+4; 556 sub t4,t4,t5
        560 add t3,a2,t1; 564 sb 0; 568 srli8; 572 sb 1; 576 srli8;
        580 sb 2; 584 srli8; 588 sb 3; 592 t1+=4; 596 j368
  CMT:  600 bgeu→628; 604 add; 608 lbu; 612/616 beq\n→368; 620 t0++; 624 j600
EXITS:  628 Ok(a0=0,a1=t1); 640 short(2,0); 652 split(3,0); 664 trailing(4,0)
        676 unknown(5,0); 688 dup(6,0); 700 undef(7,a1=t1); 712 trailtok(8,0)
        each: addi a0; addi a1; jalr x0,0(x1)
```

## Proof architecture

1. **Block helpers** (port of hex0's li_beq_ne/li_beq_eq/li_blt_nt/li_blt_t/
   li_bge_nt/li_bge_t under CodeLoaded1). Mechanical.
2. **WellFormed1** `inp cap`: regions
   code[0x80000090,+724) | input[inputAddr,+len) ≤ outAddr | out[outAddr,+cap)
   ≤ lblAddr | lbl[lblAddr,+2048), with `lblAddr + 2048 < 2^63` (signed `blt`
   on table addresses + sign-tested slots) and `bytes_ok`.
3. **Table encoding**: `encodeSlot : Option Nat → Word` (none ↦ -1#64,
   some p ↦ ofNat p); `TableLoaded s lab := ∀ c<256, ∀ k<8,
   mem(lblAddr+8c+k) = (encodeSlot (lab c) >>> 8k).setWidth 8`.
   - ld at slot c + `assemble_bytes` ⇒ reads `encodeSlot (lab c)`.
   - sd at slot c ⇒ TableLoaded (setLabel lab c pos) via storeWord_get0..7 +
     storeWord_frame.
   - dup test `bge t4,x0`: encodeSlot(some p).slt 0 = false for p<2^63;
     encodeSlot(none).slt 0 = true.
4. **Init loop**: InitInv j (pc=16, t3=lblAddr+8j, partial table 0xFF);
   induction 256× ⇒ from entry, fuel 4+3·256+? reaches pc=28 with
   TableLoaded s noLabels, all argument registers intact.
5. **P1Inv lab pos rest** at pc=36: t0=len−|rest|, t1=pos, suffix, TableLoaded
   lab, pos ≤ cap, (∀ c p, lab c = some p → p ≤ pos), spec telescope
   `scan1 .High lab pos rest = scan1 .High noLabels 0 inp`, input/code intact.
   Per-token iteration lemmas (~14: spacing×3 via one lemma, comment,
   def-ok/dup/eof, ref-ok/short/eof, byte-ok/short, split, unk-high, unk-low,
   trailing) + fuel induction `pass1_correct`.
6. **P2Inv emitted rest labF labNow** at pc=368: t1=|emitted|, out region =
   emitted, TableLoaded labF (UNchanged in pass2), scan-validity side
   condition `scan1 .High labNow |emitted| rest = (labF, m, .Ok)` (m ≤ cap,
   monotone) for control-flow totality, spec telescope on `emit1 .High labF`.
   Iteration lemmas (~7) + `pass2_correct`.
7. **Offset bytes**: machine computes t4 = encodeSlot(some p) − (t1+4) and
   stores 4 LE bytes via sb/srli — value lemma vs `Hex1.offBytes p pos`
   (Int emod 2^32 ↔ BitVec truncation; p, pos+4 < 2^63).
8. **Exit epilogues** (2 shapes: a1=0 / a1=t1), `Result1` def, conversion
   `observe1`/`coreSpec1` (incl. the cap-factorization: machine shorts iff
   cap < m — falls out of P1 iteration lemmas: crossing token exits Short;
   spec-side m ≥ pos+width monotonicity).
9. **Prologue**: initOn1 → 2 steps (28,32) → P1Inv noLabels 0 inp.
   (After init loop; entry: pc=coreAddr=offset 0.)
10. **core1_refines** assembly.

## Conventions / gotchas

- Reuse Hex0.Refine's generic lemmas (they're CodeLoaded-independent):
  addr_ofNat_succ, ult_ofNat, ofNat_ne, getD_drop, setWidth8_64,
  rset_rget, storeByte_mem, li_block_frame, runFuel_halt/one/add,
  loadBytes_frame/get, rget_zero/setPc_*/rset_* simp lemmas, rset_zero.
- decide on wordAt1/getD needs `set_option maxRecDepth 8000`.
- `decide` cannot evaluate scan1/emit1 (WF recursion) — use the Grammar
  unfolding lemmas (Hex1/Grammar.lean) on the spec side.
- bare/core1.s gotcha: only the 16 modelled encodings (see
  isa-surface-discipline memory); core1.s uses blt (NOT bltu) by design.
