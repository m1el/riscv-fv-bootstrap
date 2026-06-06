# Proof outline — verified hex0 (the refinement methodology)

This documents *how* the hex0 verification is structured, so the proof can be
audited, maintained, and **re-implemented in another proof assistant** (the Coq
port follows this outline verbatim). Read with `STATUS.md` (state), `TCB.md`
(trust boundary), `HEX0.md` (the language).

## 1. The verification tower

```
   HEX0.md BNF  ⟺  decodeS / coreSpec  ⟸  RV64I model running the real bytes
   (grammar)        (functional spec)       (binary, byte-for-byte)
   └─ Grammar.lean ─┘└──────────── Refine.lean (core_refines) ───────────┘
```

Two independent proofs meet at the functional spec:

- **`Grammar.lean`** — the published BNF (`HEX0.md`) `⟺` the spec `decodeS`
  (sound + complete; the grammar is total and deterministic). Anchors "is the
  spec the language we documented?".
- **`Refine.lean`** — `core_refines`: for **all** inputs, the real `core` bytes
  executed on the RV64I model compute exactly `coreSpec`. Anchors "do the bytes
  that run implement the spec?".

Everything below is the structure of `Refine.lean` (the hard half), then the
`Grammar.lean` layer, then the Coq port plan.

## 2. Objects

- **Model** (`Rv64i`): `State = (reg, pc, mem)`, a pure `step : State → State`
  over the 12 instruction forms `core` uses (`addi add or slli lbu sb beq blt
  bge bgeu jal jalr`), `runFuel`/`runUntil` to iterate. No CSRs, traps,
  privilege, or stack (`core` is a leaf function — see TCB / the input contract).
- **Spec** (`Spec`): `decodeS : St → List Nat → (List Nat × Status)`, a two-state
  (`High`/`Low`) functional decoder; `coreSpec` wraps it with the output-capacity
  (`OutputShort`) bound.
- **Harness**: `initOn`/`mkInit` (the entry state: code+input loaded, `a0..a3`
  set, `ra=0`), `observe`/`runOn` (run and read back `a0`,`a1`, output region).

## 3. The theorem and its preconditions

```
core_refines : ∀ inp cap, WellFormed inp cap →
                 ∃ fuel, observe inp cap fuel = coreSpec inp cap
```
`WellFormed inp cap` (the input contract):
- `in_fits  : inputAddr + |inp| ≤ outAddr`   — input/output regions disjoint.
- `out_fits : outAddr + cap < 2^64`           — output region fits, no wraparound.
- `bytes_ok : ∀ b ∈ inp, b < 256`             — inputs are bytes.

Implicit (in `initOn`): fixed memory layout (code abuts input: `coreAddr+324 =
inputAddr`), `ra=0` with "return = halt (pc→0)", no stack used. (See TCB.)

## 4. Methodology — refinement by loop invariant + induction (4 steps)

1. **Base case** (`core_eof`): from the loop head with input exhausted, the
   machine runs `bgeu(taken);li a0,0;mv a1,t1;ret`, halting `Ok` with output
   preserved.
2. **Loop-state model** (`LoopInv inp cap s rest emitted`): a 16-field invariant
   relating a mid-execution state to a *partial* run of `decodeS` — `rest` is the
   unconsumed input suffix, `emitted` the bytes written, with the telescoping
   field `spec_link : decodeS High inp = (emitted ++ (decodeS High rest).1, …)`,
   plus register/memory facts and the static region bounds (`in_fits`,`out_lt`).
3. **Token decomposition**:
   - *spec side* (`decodeS_spacing/byte/comment_skip`): one `decodeS` step per
     token class.
   - *machine side* (`loop_iteration`): from a non-empty `rest`, the machine
     either returns to the loop head with a strictly shorter `rest` and `LoopInv`
     preserved, or halts in a `coreSpec`-correct error state. A **dispatch on the
     head char's class** (see §6).
4. **Induction** (`loop_correct`): structural induction on a fuel bound on
   `|rest|`; base = `core_eof`, step = `loop_iteration`, chained by `runFuel_add`,
   telescoped by `spec_link`. Then assemble with the **prologue**
   (`init_loopinv`) and the **`observe↔coreSpec` conversion**.

## 5. The lemma DAG (dependency order, as in `Refine.lean`)

```
fetch_code                      decode at a concrete code offset = wordAt off
  step_addi/bgeu/add/or/slli/    one-step transition per instruction form
    lbu/sb/beq/blt/bge/jal/jalr  (the "engine")
state projections               setPc_*/rset_*/rget_zero/rset_rget/li_block_frame
arithmetic toolkit              ult_ofNat, slt_ofNat, ofNat_ne, setWidth8_64,
                                nibble_addi, combine_nibbles, getD_drop
runFuel                         runFuel_halt, runFuel_one, runFuel_add
core_eof                        the EOF base case (§4.1)
LoopInv                         the invariant (§4.2)
decodeS_spacing/byte/comment    spec-side token decomposition (§4.3)
─ reusable machine blocks ─
  loop_prefix / read_prefix     the bgeu;add;lbu;addi input-read head (off 8/108)
  li_beq_ne / li_beq_eq         li K; beq (not-taken / taken) 2-step blocks
  li_blt_nt/_t, li_bge_nt/_t     li K; blt|bge (signed) blocks
  high_beq_ft / low_beq_ft      the beq fall-through chains (→64 / →164)
  high_parse / low_parse        nibble parse (digit/letter) → t4=hi / t5=lo
  store_epilogue                bgeu(ok); slli;or;add;sb;addi;jal (emit a byte)
  halt_epilogue                 li a0,code; mv a1,t1; ret  (any error exit)
  comment_read / comment_loop   the inner skipComment scan (induction)
─ per-token iterations (§6) ─
  loop_spacing  loop_byte  loop_comment
  loop_trailing loop_split loop_unknown_high loop_unknown_low loop_short
loop_iteration                  the dispatch combining all of the above
eof_result / loop_correct       induction
init_loopinv + conversion       prologue + observe↔coreSpec
core_refines                    assembled
```

## 6. The `loop_iteration` dispatch (offset map in `RESUME.md`)

`rest = c :: rest''`; case on `c`:

- **spacing** (`isSpace c`): `loop_spacing` — read `c`, beq-chain to LOOP,
  rebuild `LoopInv` (suffix shorter, `emitted` unchanged) via `decodeS_spacing`.
- **comment** (`isComment c`): `loop_comment` — read `c`, dispatch to `.Lcomment`,
  scan to the newline (`comment_loop`, induction over the span). Newline ⇒ back to
  LOOP on the newline (then handled as spacing); EOF ⇒ halt `Ok`. Rebuild via
  `decodeS_comment_skip` + the newline being a space.
- **byte** (high nibble `c`, low nibble `l`, capacity to spare): `loop_byte` —
  read `c`, `high_parse`, read `l`, `low_parse`, `store_epilogue` (emit
  `hi*16+lo`), rebuild via `decodeS_byte` + the store-disjointness frame.
- **errors** → halt with the matching status, `Result` from `spec_link` +
  `coreSpec_props`: `loop_trailing` (high nibble at EOF → 4), `loop_split`
  (low char is a stop char → 3), `loop_unknown_high`/`loop_unknown_low`
  (non-hex → 5), `loop_short` (`|emitted| = cap` → 2, `coreSpec` truncates).

## 7. The grammar layer (`Grammar.lean`)

- `Valid inp out` — the error-free BNF as an inductive (one constructor per
  production). `valid_ok` : valid ⟹ `decodeS = (out, Ok)`.
- `Parse inp out st` — the grammar **with** the error taxonomy. `parse_sound` :
  `Parse ⟹ decodeS`. `parse_complete` : every input is derivable with the spec's
  result (**totality**) ⇒ `decodeS = Parse` iff. `parse_det` : unique `(out,st)`
  (**non-intersection**). `valid_or_err` / `not_valid_and_err` : inputs partition
  into valid / erroneous (total + disjoint).
- Residual trust: that the inductive transcribes `HEX0.md`'s BNF (TCB item 7).

## 8. Coq port plan (`coq/Refine.v`) — same methodology

The Coq model/spec/harness already mirror Lean (`coq/Rv64i.v`, `Spec.v`,
`Harness.v`, `Image.v`; `Certify.v` is kernel-checked). Differences from Lean,
and how each lemma class maps:

| Lean | Coq |
|---|---|
| `BitVec 64`, `BitVec.ofNat`, `+`/`<<<`/`|||` | `Z` in `[0,2^64)`; `wrap = mod 2^64`, `wadd`, `wshl`, `Z.lor` |
| `by decide` on closed `BitVec`/`decode` | `cbn` / `vm_compute` on closed `Z` (`decode 659` reduces) |
| `omega` (linear nat) | `lia` (linear `Z`/`nat`) |
| `BitVec.ofNat_add` / `addr_ofNat_succ` | `wadd`/`wrap` `mod` lemmas (`Z.add_mod`, `lia`) |
| `ofNat_ne` (injective `<2^64`) | `a ≠ b` on in-range `Z` (`lia`) — *easier* |
| `ult_ofNat` / `slt_ofNat` | `ultb`/`sltb` unfold + `lia` (signed via `toS`) |
| `combine_nibbles` (256-case `decide`) | `Z.lor (Z.shiftl hi 4) lo = hi*16+lo`, `hi,lo<16` (bit lemma / `lia` after `Z.lor` disjointness, or `vm_compute`-free `Z.shiftl_mul_pow2`) |
| `runFuel` (fuel `halt=0`) | `runUntil 0` (already defined) — same `_add`/`_halt`/`_one` lemmas |
| `decide` choking on free vars | same caveat; reduce to closed `Z` first |

**Port order** = §5 top-to-bottom: `wordAt`/`CodeLoaded`/`fetch_code` → the 12
`step_*` → projections → toolkit → `runUntil` composition → `core_eof` →
`LoopInv` → `decodeS_*` → reusable blocks → per-token iterations → `loop_iteration`
→ `loop_correct` → prologue/conversion → `core_refines`. Each `step_*` proof is:
`unfold step, fetch32; rewrite the 4 CodeLoaded byte reads; vm_compute the decode;
cbn`. The control-flow/offset bookkeeping is identical; the only genuinely
different work is the bitvector→`Z` arithmetic (mostly *simpler* under `lia`).

A note learned the hard way (see `lean-build-root` memory): validate each module
directly (`coqc`/`make` here actually compiles `Refine.v` — unlike `lake build`,
which only built what the root imported). Keep `core_refines` `Admitted` only
until the last per-token case lands; check no `Admitted` remain with
`grep -rn Admitted coq/`.

## 9. Build / check

```
cd lean && lake build                       # full Lean dev (Refine + Grammar), sorry-free
lake env lean Hex0/Refine.lean              # type-check Refine directly (no cache)
#print axioms Hex0.Refine.core_refines      # ⇒ [propext, Quot.sound]  (Classical.choice-free)
eval $(opam env); cd coq && make -jN        # Coq dev (Refine.v: port in progress)
grep -rn 'Admitted\|sorry' coq/ lean/       # remaining holes
```
