# Refine1 — plan and progress for `core1_refines` (hex1 general refinement)

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
- `Hex1/Refine.lean` — IN PROGRESS (the main proof).

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
