# RESUME — session handoff for closing the last `sorry`

Read this together with `STATUS.md` (high-level state) and `TCB.md` (trusted base).
This file is the **technical** handoff: environment gotchas, the proof
architecture as built, the exact remaining work, and the recipes that work.

## TL;DR of where we are

- **Everything builds green**: `cd lean && lake build`; `cd coq && make -jN`;
  `cd bare && make run` → prints `Hello\n`.
- The Lean general refinement **`core_refines` is FULLY PROVED, `sorry`-free**
  (`lean/Hex0/Refine.lean`). `loop_iteration` is discharged via a head-char
  dispatch (`loop_spacing`/`loop_byte`/`loop_comment` + the halting classes
  `loop_trailing/split/unknown_high/unknown_low/short`).
  `#print axioms Hex0.Refine.core_refines` → `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`). `grep -c '  sorry' lean/Hex0/Refine.lean` → 0.
- **BUILD GOTCHA (cost real time):** `lake build`'s default target only built
  what `lean/Hex0.lean` imports. That root did NOT import `Refine`, so
  `lake build` reported success *without ever type-checking `Refine.lean`* (and
  served a stale `.olean`). Fixed: `Hex0.lean` now imports `Refine`/`Image`/
  `Harness`/`Certify`. **To validate `Refine` directly without cache, use
  `lake env lean Hex0/Refine.lean`** (errors print top-down; exit 0 = clean).
  Also note `set`/`List.getD_eq_getElem` are Mathlib/Batteries-only — unavailable
  here; use `let x := e; have h : x = e := rfl; rw [← h] at <hyp>` and
  `(List.getElem_eq_getD 0)` instead.
- The remaining frontier is now **task #7** (ISA cross-check) and the single
  Coq `Refine.v` hole `loop_iteration` (the per-token dispatch; `core_refines`
  itself is proved modulo it).

## Environment gotchas (these cost real time — don't rediscover)

- **Lean is 4.30.0 via elan; there is NO Mathlib.** Consequences:
  - **Banned tactics/lemmas**: `norm_num`, `ring`/`ring_nf`, `set ... with`,
    `omega` does NOT evaluate `2^64` reliably as a bound unless the other facts
    pin it (it's usually fine, but for `a < 2^64` from `a < small` it works).
    `le_refl` unqualified is absent → use `Nat.le_refl`.
  - **Use instead**: `decide` (for closed nat/BitVec goals incl. `2 < 2^64`),
    `omega` (linear nat), `simp`, `Nat.le_refl`, `List.ext_getElem`.
  - `set x := e with h` → replace with `let x := e` + `have h : x = e := rfl` +
    `rw [← h] at <hyps mentioning e>`.
- **`set_option maxRecDepth 4000 in` MUST come BEFORE the doc comment**, not
  between the doc comment and the `theorem`. `/-- … -/ set_option … in theorem`
  is a parse error ("unexpected token set_option").
- **`decide` chokes on free variables.** `(by decide)` proving e.g.
  `BitVec.ofNat 64 (coreAddr + off) ≠ 0` fails when `off` is symbolic. Use
  `ofNat_ne` (proved) with explicit bound proofs, or reduce to a closed term
  first (`simp only [Image.coreAddr]; omega`).
- `decide` needs `maxRecDepth ~4000` whenever it evaluates `Image.coreBytes.length`
  (a 324-element list) or 64-bit BitVec arithmetic with ~2³¹ addresses.
- **`by` inside an anonymous constructor `⟨…⟩` is greedy** — it swallows the
  following tuple elements. Always parenthesize: `⟨(by decide), …⟩`.
- `simp` will collapse `x = x` to `True`; then provide `trivial`, not `rfl`.
- **`native_decide` works but adds the Lean compiler to the TCB** — used only in
  `lean/Hex0/Certify.lean` (the finite cert). Coq's `Certify.v` is kernel-checked
  via `vm_compute` (smaller TCB) — keep that contrast.
- **`Harness.loadBytes` was rewritten recursively** (not `foldl`) so it's provable
  by induction; semantics identical, certs still pass.
- Namespace clash: inside `namespace Hex0.Refine` with `open Rv64i`, plain
  `decode` = `Rv64i.decode`; the spec's is `Hex0.decode`. **Qualify `Hex0.…`**
  for spec stuff (`Hex0.decodeS`, `Hex0.nibble`, `Hex0.coreSpec`, …).
- qemu needs a `libcapstone.so.4` shim (`.libshim/`, baked into `bare/Makefile`);
  capstone is disasm-only, inert at runtime. No qemu rebuild needed.
- Python: always `uv run` (see `tools/gen_image.py`).

## The proof architecture (what's proved, in dependency order)

In `lean/Hex0/Refine.lean` (56 proved decls, 1 sorry):

1. **ISA-step engine** (all proved): `fetch_code` (decode instr at a code offset
   from memory, handles BitVec address arithmetic via `addr_ofNat_succ`), and
   `step_addi/add/or/slli/lbu/sb/beq/blt/bge/jal/jalr` (one-step transition per
   instruction form). Recipe to step one instr at concrete offset `off`:
   ```
   step_<op> s off … hcode (by decide /-off+3<len-/) hpc (by decide /-decode=…-/)
   ```
2. **State-projection simp lemmas**: `rget_zero`, `setPc_pc/mem/rget`,
   `rset_pc/mem`, `rset_rget` (needs `rd≠0 ∧ i≠0`), `rset_zero`.
3. **Arithmetic toolkit**: `ult_ofNat`, `ofNat_ne`, `getD_drop`, `setWidth8_64`.
4. **runFuel**: `runFuel_halt`, `runFuel_add` (composition; the induction backbone).
5. **Spec decomposition**: `decodeS_spacing/byte/comment_skip`.
6. **Invariant** `LoopInv` (16 fields, incl. `spec_link`, `in_mem`, `in_lt`,
   `bytes_lt`) and `Result`.
7. **Base case** `core_eof`, **induction** `loop_correct` (fuel-bounded structural
   induction on `rest.length`).
8. **Prologue**: `loadBytes_frame/get`, `code_initOn`, `in_initOn`, `init_loopinv`.
9. **Conversion**: `decode_bytes_lt`, `range_getD`, `coreSpec_props`.
10. **`core_refines`** — assembled. PROVED.
11. **`loop_iteration`** — the ONE `sorry`. Proven sub-pieces toward it:
    `loop_prefix` (the shared `bgeu;add;lbu;addi` head incl. the input read),
    `spacing_tail_nl` (the `beq` dispatch chain → LOOP, newline char),
    `spacing_loopinv` (rebuild `LoopInv` after a spacing token),
    `loop_spacing_nl` (= a COMPLETE iteration for `'\n'`),
    `li_beq_ne` (reusable `li;beq`-not-taken 2-step block).

## `loop_iteration` — the statement and the plan

```lean
theorem loop_iteration (inp cap rest emitted s) (hne : rest ≠ [])
    (inv : LoopInv inp cap s rest emitted) :
    ∃ k, (∃ rest' emitted', rest'.length < rest.length ∧
            LoopInv inp cap (runFuel 0 k s) rest' emitted')   -- "continue"
         ∨ Result (runFuel 0 k s) inp cap                     -- "halt"
```
Dispatch on `rest = c :: rest''`, by the char class of `c`:
- **spacing** (`c ∈ {10,32,95}`) → left, `rest'=rest''`, `emitted'=emitted`.
- **comment** (`c ∈ {35,59}`) → left, `rest'=skipComment rest''`, `emitted'=emitted`.
- **nibble `c` (high)**: need `rest'' = l :: rest'''`:
  - `rest''=[]` → trailing error (code 4) → right.
  - `l` is low-stop (`{10,32,95,35,59}`) → split (3) → right.
  - `l` not nibble → unknown (5) → right.
  - `l` nibble: if `emitted.length < cap` → byte emit, left (`emitted'=emitted++[byte]`);
    else output-short (2) → right.
- **else** (`c` not special, not nibble) → unknown-high (5) → right.

For the **right (halt)** cases, `Result` follows from `inv.spec_link`: e.g. an
error means `decodeS High (c::rest'') = ([], ErrX)`, so `decode inp =
(emitted, ErrX)`, and `coreSpec inp cap = (errcode, emitted, emitted.length)`
(using `emitted.length ≤ cap`); the machine halts with exactly `a0=errcode`,
`a1=emitted.length`, output region = `emitted` (via `inv.out_mem`, mem unchanged
on error paths). Output-short: `emitted.length = cap`, `coreSpec = (2, emitted, cap)`.

For the **left (continue)** cases, build the new `LoopInv` with `spec_link`
advanced by the matching `decodeS_*` decomposition lemma (already proved).

### `core` instruction offset map (offset = addr − 0x80000088)

Verify any specific instr/imm with `#eval Rv64i.decode (wordAt <off>)`.
```
  0 li t0,0      4 li t1,0
  8 LOOP: bgeu t0,a1  -> .Lok(264) if t0>=a1
 12 add t3,a0,t0   16 lbu t2,0(t3)   20 addi t0,t0,1     -- loop_prefix (off 8..24)
 24..60  beq-chain: (li K; beq t2,t3) for K = 35,59,10,32,95
         35,59 -> .Lcomment(236);  10,32,95 -> LOOP(8);  fall-through -> 64
 64..104 high-nibble parse (li/blt/li/bge/addi ...); bad -> .Lunknown(312)
108 have_high: bgeu t0,a1 -> .Ltrailing(300) if t0>=a1     (EXPECT_LOW EOF check)
112 add 116 lbu 120 addi                                   -- low prefix, reads l
124..160 low-stop beq-chain K = 10,32,95,35,59 -> .Lsplit(288)
164..204 low-nibble parse; bad -> .Lunknown(312)
208 have_low: bgeu t1,a3 -> .Lshort(276) if t1>=a3         (capacity check)
212 slli t4,4  216 or t4,t5  220 add t3,a2,t1  224 sb t4,0(t3)  228 addi t1  232 j LOOP
236 .Lcomment: bgeu t0,a1 -> .Lok(264); 240 add 244 lbu 248 li10 252 beq ->LOOP; 256 addi 260 j 236
264 .Lok(a0=0) 276 .Lshort(2) 288 .Lsplit(3) 300 .Ltrailing(4) 312 .Lunknown(5)
    each: li a0,code; mv a1,t1; ret
```

### Remaining lemmas to build (mechanical; reuse the proven recipes)

1. **`li_beq_eq`** — `li K; beq`-TAKEN block (mirror of `li_beq_ne`, `if_pos`,
   pc → `off+4 + signExtend imm`). Then **`spacing_tail_sp`/`_us`** (or one
   `spacing_tail` casing `c ∈ {10,32,95}`) using `li_beq_ne` × (1..3) + `li_beq_eq`,
   chained with `runFuel_add`. Then **`loop_spacing`** (all 3) → the spacing case.
2. **`li_blt_*` / `li_bge_*` blocks** — for the nibble-parse chains (analogous to
   `li_beq_ne` but `step_blt`/`step_bge`, signed compare via `BitVec.slt`; note
   `c < 256` so `slt`/`ult` agree and `decide`/`ult_ofNat`-style facts close them).
3. **`storeByte_frame`** (the one genuinely new piece) — storing at
   `outAddr + j` (`j < cap`) leaves code & input memory unchanged (region
   disjointness from `WellFormed.in_fits` + concrete addresses: code
   `[0x88,0x1cc)`, input `[0x1cc, 0x1cc+len)`, output `[0x3b0, 0x3b0+cap)`), and
   updates `out_mem` (earlier output bytes preserved since `j' < j` ⇒ different
   address). Pattern: like `loadBytes_frame`, an `if x = addr` case split + `ofNat_ne`.
4. **byte case** — `loop_prefix` → beq fall-through → high parse → `have_high`
   (`rest''≠[]`) → low prefix → low-stop fall-through → low parse → capacity OK →
   `slli;or;add;sb;addi;j` → LOOP. Rebuild `LoopInv` with `emitted++[hi*16+lo]`,
   `out_idx+1`, `out_mem` via `storeByte_frame`, `spec_link` via `decodeS_byte`.
   The byte value: `(t4<<4) ||| t5` with `t4=hi,t5=lo` — prove `= hi*16+lo` as
   `BitVec.ofNat 64 (hi*16+lo)` (try `bv_decide`? not available — do it by
   `BitVec.toNat` + the fact `hi,lo<16`; or keep as `<<<`/`|||` and match a
   `decodeS_byte`-shaped output, adjusting `decodeS_byte` to emit the same form).
5. **comment case** — inner loop `skipComment`; prove a small `comment_tail`
   reaching LOOP at the char after `\n` (or EOF→`.Lok`), by induction on the
   span to the newline. Rebuild via `decodeS_comment_skip`.
6. **error cases** (trailing/split/unknown/short) — each: parse to the failing
   branch → error epilogue (`li a0,code; mv a1,t1; ret` → pc=0, like `core_eof`),
   then `Result` from `spec_link`+`coreSpec_props`.
7. **dispatch** — `loop_iteration` cases on `c` (use `Hex0.isComment`,
   `Hex0.isSpace`, `Hex0.nibble c`, `Hex0.isLowStop`) and dispatches to the above.

Estimated ~400–600 lines. Suggested order: `li_beq_eq`+spacing (quick win,
finishes that branch) → `storeByte_frame` (the new technique) → byte → errors →
comment → dispatch. Keep it building at each step; commit per lemma.

## Build / check commands

```
export PATH="$HOME/.elan/bin:$PATH"
cd lean && lake build                         # whole Lean dev (1 sorry in Refine)
grep -c '  sorry' lean/Hex0/Refine.lean       # should be 1 until loop_iteration closes
lake env lean Hex0/Validate.lean              # model-vs-spec differential battery

eval $(opam env); cd coq && make -j64          # Coq dev (Refine.v: only loop_iteration Admitted)
cd bare && make run                            # bare-metal hex0 -> "Hello\n"
uv run tools/gen_image.py                      # regen Image.{lean,v} from the ELF
```

## Things NOT yet done (beyond the one sorry)

- **Coq `core_refines` is PROVED modulo the single `Admitted` `loop_iteration`.**
  `Print Assumptions core_refines` ⇒ `loop_iteration` + `functional_extensionality_dep`
  (standard consistent axiom, for `mem : Z → Z` state equality). Kernel-checked and
  assembling the theorem: `fetch_code` + all 12 `step_*` + projections, the
  arithmetic toolkit, `runUntil` composition (incl. new `runUntil_stab`), the
  `decodeS_*` decomposition, `core_eof`, `LoopInv` (18 fields), `eof_result`,
  `loop_correct` (fuel-bounded induction `50*|rest|+4`), `init_loopinv` (prologue),
  and the `runOn↔coreSpec` conversion. **The only remaining Coq hole is
  `loop_iteration`** — the per-token dispatch (spacing/byte/comment + 4 error
  classes), the ~2500-line Lean tail to port (mirror `lean/Hex0/Refine.lean`'s
  `loop_*` blocks). Coq gotchas already resolved (see `coq/Refine.v` header):
  `set (..) in *` (not goal-only) so `step` eqns fold; **avoid `simpl andb` over
  `nth .. coreBytes`** (full simpl traversal + huge `coreAddr` literal ⇒ coqc
  hangs — use `replace (guard) with true/false` + `cbv iota`); **`lia` cannot
  reason about the nat literal `100000`** (`Nat.of_num_uint`) so bound it through
  `Z` (`Nat2Z.inj_le` + `vm_compute (Z.of_nat 100000)`) and absorb fuel slack via
  `runUntil_stab`; the `Z`-bytes/`nat`-spec gap needs `zin`/`Z.to_nat` threaded
  through `LoopInv`/dispatch.
- **Task #7 (ISA cross-check)**: prove our `decode`+`step` agree with
  `sail-riscv-lean` (opencompl) / `riscv-coq`, to remove "model = hardware" from
  the TCB (currently testing-backed). `sail-riscv-lean` is 171k LoC, WIP,
  "not executable" — use it as an oracle for the ~12 instrs only; or hand-audit.
