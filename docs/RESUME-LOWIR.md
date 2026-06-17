# RESUME — LowIR & the hex0 functional proof

Handoff for the **LowIR structured-IL** effort (prove libc functions, compile to RV64I)
and specifically the **in-progress hex0 functional-correctness proof**. Read with
[LIBC-FORMALIZE.md](LIBC-FORMALIZE.md) (design/altitude survey), [PROGRESS.md](PROGRESS.md)
(log), [STATUS.md](STATUS.md) §LowIR (table). HEAD at handoff: `body_step` (item A) complete.

Build everything: `cd lean && lake build LowIR.CtrlHex0Proof LowIR.CtrlStrtoull10Proof`.
All 12 `LowIR*` modules build green (0 errors). Toolchain: `leanprover/lean4:v4.30.0`,
**no Mathlib/Batteries** (core Lean only — this constrains tactics, see Gotchas).

---

## 1. What exists, and its status

The IL lives in `lean/LowIR.lean` (original) and `lean/LowIR/Ctrl.lean` (the control-flow
version we now use). `Ctrl` adds `block`/`while`/`brkB`/`contL`/`ret` with an `Outcome`-threaded
clocked big-step `exec : Nat → Stmt → St → Option (St × Outcome)`. State `St` = register file
`regs : Reg → Word` (x0=0) + total byte memory `mem : Word → Byte` (Word=BitVec 64, Byte=BitVec 8).

| File | Contents | Status |
|---|---|---|
| `LowIR.lean` | original structured IL + `compile`+`encode` to RV64I + T1 framework | ✅ except `compile_sim` = **sorry** (sanctioned) |
| `LowIR/StrlenProof.lean` | `strlen_correct` + the **register lemmas** | ✅ sorry-free |
| `LowIR/Ctrl.lean` | control-flow IL (`block/brkB/contL/ret`, outcome exec) | ✅ |
| `LowIR/CtrlStrlen.lean` | strlen on Ctrl + the **exec equation lemmas** (`exec_seq_normal`, `exec_addi`, …) | ✅ sorry-free |
| `LowIR/CtrlHex0.lean` | **hex0** on Ctrl (flat `ret` cascade); `hex0_matches_spec` battery | ✅ validated (`native_decide`) |
| `LowIR/CtrlStrtoull.lean` | wrapping strtoull10 (geu) + spec | ✅ validated |
| `LowIR/CtrlStrtoull10Proof.lean` | **`strtoull10_correct`** | ✅ **proved sorry-free** |
| `LowIR/CtrlStrtoull2.lean` | **conformant** strtoull (overflow→ULLONG_MAX+errno) | ✅ validated |
| `LowIR/CtrlStrtoull2Proof.lean` | conformant foundation: `geu_true/false`, `digit_val`, **threshold proved** (`build_step`,`nib_15`) | ✅ sorry-free; full conformant proof TODO |
| `LowIR/CtrlStrtoullProof.lean` | the break/block exec primitives (`exec_block_catch`,`exec_while_brk`,`exec_seq_brk`,`acc_times_ten`,…) | ✅ sorry-free |
| `LowIR/CtrlHex0Proof.lean` | **hex0 proof — IN PROGRESS**; `body_step` (item A) DONE (see §3) | partial, sorry-free |
| `LowIR/Hex0Proof.lean` | the *original-IL* `hex0_correct` statement | **sorry** (superseded by Ctrl work) |

**Proved sorry-free, all inputs:** `strlen_correct` (both ILs), `strtoull10_correct`.
**Deferred sorries:** `compile_sim` (T1, sanctioned), `Hex0Proof.hex0_correct` (old statement),
conformant-strtoull functional proof (foundation done).

---

## 2. The reusable toolbox (USE THESE — don't reprove)

All in `namespace LowIR.Ctrl` (or `LowIR`), accessible from `LowIR.Ctrl.Hex0`.

**Register lemmas** (`StrlenProof.lean`, `@[simp]`): `rget_rset_eq` (i≠0), `rget_rset_ne` (j≠i),
`rset_mem`, `rget_zero`. Plus `cur_zero` (`cur + ofNat 0 = cur`), `cur_step`
(`cur + ofNat(k+1) = (cur+1) + ofNat k`), `wadd_zero`, `wzero_add`, `zero_signExtend`,
`one_signExtend`.

**exec equations** (`CtrlStrlen.lean` + `CtrlStrtoullProof.lean`): `exec_addi`, `exec_lbu`,
`exec_sub`, `exec_add`, `exec_orr`, `exec_slli` (each `exec (f+1) op s = some (s.rset …, .normal)`);
`exec_seq_normal` (peel a seq whose head is `.normal`); `exec_seq_brk`/`exec_seq_ret` (head
short-circuits); `exec_block_catch` (`block` catches `brk 0` → normal); `exec_while_step`/
`exec_while_done`/`exec_while_brk`; `exec_ife_then`/`exec_ife_else`; `exec_brkB`/`exec_ret`;
`acc_times_ten` (`(acc<<<3)+(acc<<<1)=acc*10`).

**Condition lemmas** (`CtrlStrtoull2Proof` + `CtrlHex0Proof`):
- `Strtoull2.geu_true (hm : (ofNat 64 m).toNat = m) (h : m ≤ b.toNat) : evalCond .geu (b.setWidth 64) (ofNat 64 m) = true`; `geu_false` symmetric.
- `geuL_true/geuL_false` — same but **const on the left** (`evalCond .geu (ofNat 64 m) (b.setWidth 64)`).
- `slt_true/slt_false` — signed `<` on indices (`x.toNat,y.toNat < 2^63`). **bv_omega CANNOT do slt**; these go via `x.slt y = decide (x.toInt < y.toInt)` [rfl] + `BitVec.toInt_eq_toNat_of_lt`.
- `Strtoull2.digit_val`, `tn/c48/c57/c65/c70` (constant `.toNat` facts).

---

## 3. hex0 proof — current state and the remaining plan

Target: `CtrlHex0.hex0` (the program) computes `Hex0.coreSpec` (= `decodeS` two-state recursion
+ capacity). hex0 was switched to **unsigned `geu`** comparisons (commit `e1fb037`) for provability.

### Proved so far (`CtrlHex0Proof.lean`, sorry-free)
- **`pnib_correct`** — `pnib dst 7` ≡ `Hex0.nibble` (writes `pnibR b`: `b-48` on [48,57], `b-55`
  on [65,70], else 255). 5-region case split.
- **`cgGuard_eff`** — comment-loop guard; **`skip_body`/`skip_loop`/`skipComment_eff`** (full skip;
  now each also exposes a **register-preservation clause** `∀ r ∉ {5,8,15,30}, st'.rget r = st.rget r`).
- **`readAdv_eff`** — `readAdv dst` loads `mem[p+i]`→dst, `x30=p+i`, `x5=i+1`, preserves the rest.
- **Fuel monotonicity** (in `CtrlStrtoullProof.lean`): `exec_mono` / `exec_mono_le` — more fuel never
  changes a `some` result. THE enabler: every lemma returns an *existential* fuel and `exec_mono_le`
  bumps results to a common fuel before composing. Also added the missing one-layer exec eqns
  (`exec_seq_cont/none`, `exec_block_*`, `exec_while_none/cont0/contS/ret`).
- **Dispatch helpers**: `ceq_true/ceq_false` (`.eq` against a byte, takes explicit `n`),
  `weq_true/false` (raw word `.eq` of two regs), `geu_ww_true/false` (unsigned `≥` of two regs),
  `ife_skip_false`/`ife_err_true` (navigate an `ife _ _ _ t .skip` — take an explicit fuel `n` ≥ 2/4,
  mono baked in), `exec_err`/`exec_sb`/`exec_skip`, `@[simp] rget_storeByte`/`mem_storeByte_self`.
- **`Regs` struct** (the 16 const/pointer regs at every loop head: 10–13, 16–27) + **`Regs.transfer`**
  (re-establish `Regs` across any change touching only scratch `{5,6,7,8,14,15,28,29,30,31}`; the
  caller supplies a `Pres st' st` = preservation on the complement). `lowStop : Byte → Prop`.
- **`body_step` — DONE (item A, all cases, sorry-free):**
  - **`body_space`** — `chr ∈ {\n,sp,_}` → `.normal`, `x5=i+1`, rest unchanged, `Regs` preserved.
  - **`body_comment`** — `chr ∈ {#,;}` → `skipComment_eff`, `.normal`, `x5=(i+1)+d`; takes the skip
    distance `d` + `gOf` hyps; preserves `Regs`/`x6`/`x14`/mem.
  - **`hexPath_eff`** — the hex path alone (6 mutually-exclusive outcomes, each carrying its
    defining condition): badHi→ret5, trailing(`L≤i+1`)→ret4, split(lowStop)→ret3, badLo→ret5,
    outFull(`cap≤out_idx`)→ret2, OK→`.normal` (writes byte `((pnibR c<<<4)|||pnibR c2).setWidth 8`
    at `out[out_idx]`, `x5=i+2`, `x6=out_idx+1`, `Regs` preserved). **`body_hex`** lifts it through
    `readAdv`+dispatch onto `body` (same 6 arms, on the loop-head state; `chr` not space/comment).

### Remaining (the semantic core)

**(A) body-dispatch step — ✅ DONE** (`body_space` + `body_comment` + `body_hex`).

**(B) main-loop invariant** (`while .lt 5 11 body`). At each loop head the IL is at a *High*
position, so `decodeS High input` splits there:
- `in_idx = i`, `out_idx = |produced|`, `x14 = 0` (Ok so far);
- output region `[out_ptr, out_ptr+out_idx)` = the bytes decoded from `input[0..i)`;
- `decodeS High input = (produced ++ rest, finalStatus)` where `(rest, finalStatus) = decodeS High (input.drop i)`;
- `i ≤ in_len`, `out_idx ≤ cap`, input memory unchanged.
Induct (like `digit_loop`) on `in_len - i` (or on `(input.drop i).length`). The main loop uses
`.lt 5 11` (signed) → use `slt_true/slt_false` with `i ≤ in_len < 2^63` carried in the invariant.
**Comment subtlety:** IL `skipComment` stops *at* the `\n` (doesn't consume it); the spec
`Hex0.skipComment` consumes *through* the `\n`. They reconcile because the *next* main-loop
iteration reads that `\n` as a space and skips it — so the per-token correspondence for a comment
spans `skipComment_eff` + one more space iteration. Handle this in the invariant/induction.

**(C) coreSpec assembly.** `coreSpec` computes the *full* decode bytes then checks `cap < bytes.length`;
the IL checks capacity per byte and `ret`s `OutputShort` on the first overflow. These agree because
the IL hits whichever of {capacity, decode-error} comes first, left-to-right, and "capacity on full
length applied after" is equivalent (if `bytes.length > cap`, capacity is hit before any later error;
else the decode status stands). Prove this equivalence, then peel hex0's 15-instruction const/init
prelude into the loop-entry state and apply the invariant; relate `x14`/output/`x6` to `coreSpec`.

The IL harness for the spec relation is `CtrlHex0.hex0ILState`/`hex0Run` (input at `inBase=0x1000`,
output at `outBase=0x4000`, regs 10–13). Memory past `inp.length` reads 0.

---

## 4. Gotchas / hard-won knowledge (READ before grinding)

- **No Mathlib.** `set`, `ring`, `eq_or_ne`, `norm_num` are UNAVAILABLE. Use `by_cases`, `bv_omega`,
  `omega`, `decide`, inline. `bv_omega` evaluates `2^k` for literal `k`.
- **`bv_omega` cannot discharge signed `slt`** (even with `<2^63` bounds — it treats slt opaquely).
  Use `slt_true/slt_false`. It *can* do `geu`/`ult`/`setWidth`/`ofNat`/`<<<`/`*`/`-`.
- **OfNat vs ofNat literal matching.** `.addi r s 1`'s imm is `(1 : BitVec 12)` (OfNat), not
  `BitVec.ofNat 12 1` — `rw` patterns must match the literal form (`(1 : BitVec 12).signExtend 64`).
  Full `simp` normalizes `(1:Word)` → `1#64`; match accordingly.
- **`simp only` does NOT discharge the conditional `rget_rset_eq/ne` side-conditions** (`i≠0`/`j≠i`).
  Use full `simp` (its `Nat.reduceEq` simproc + discharger handle numeral `≠`), or apply the lemma
  explicitly: `rget_rset_ne _ _ _ _ (by decide : (12:Reg) ≠ 5)`.
- **`seqs` must be unfolded** to expose `.seq` for `exec_seq_normal`: after peeling into a `seqs [...]`
  branch, do `simp only [seqs, List.foldr_cons, List.foldr_nil]`.
- **Exact-fuel induction** (no monotonicity lemma): pick the loop lemma's fuel so the recursive
  `while`/loop call lands on *exactly* the IH's fuel (e.g. `strlen` `n+2`, `digit_loop` `d+12`,
  `skip_loop` `d+9`). Fuel splits like `n+1+C = (n+C)+1` are `rfl`.
- **Existential witness from a deferred exec proof:** `refine ⟨_, ?_, …⟩` fails to synthesize the
  witness when later conjuncts reference it — **provide the witness explicitly** (the post-step state),
  as in `cgGuard_eff`/`body_digit`.
- **Trailing `skip`** in a `seqs` body leaves a goal `exec (f+k) .skip s' = some (s', .normal)` →
  close with `rfl`.
- **`slt`/`toInt`:** `x.slt y = decide (x.toInt < y.toInt)` is `rfl`; `BitVec.toInt_eq_toNat_of_lt`
  wants `2*x.toNat < 2^64` (derive from `<2^63` by `omega`).
- **Linter:** files set `set_option linter.unusedSimpArgs false`. The harness's "file modified since
  read" can race the Edit tool while a linter touches the file — append via a script if Edit fails twice.
- Commit at each green milestone (project convention). Forks (for background grinding) inherit context
  but were **rate-limited** repeatedly this session — grinding in the main thread was more reliable.

---

## 5. Suggested next session

`body_step` (item A) is **DONE**. Next:

1. **Nibble bridge lemmas** (small, do first — item B needs them):
   - `pnibR c = 255 ↔ Hex0.nibble c.toNat = none` (case split mirrors `pnib_correct`'s regions).
   - for hex `c`: `(pnibR c).toNat = (Hex0.nibble c.toNat).get` (the nibble value), and
     `(((pnibR c)<<<4) ||| pnibR c2).setWidth 8).toNat = hi*16+lo` (orr = + since `hi*16` has low
     nibble 0 and `lo<16`; `bv_omega` after relating `pnibR` to the nibble Nat values).
   - `lowStop c ↔ Hex0.isLowStop c.toNat`; `c not space/comment ↔ ¬isComment ∧ ¬isSpace`.
2. **main invariant** (item B) by induction on the input suffix (decreasing `decodeS` recursion).
   Compose `body_space`/`body_comment`/`body_hex`, mapping each arm to the matching `decodeS` branch
   via the bridge lemmas. Carry: `Regs`, `x5=i`, `x6=out_idx`, `x14=0`, output region = decoded
   prefix, `i ≤ L < 2^63` (for the signed `.lt 5 11` guard → `slt_true/slt_false`), and the
   capacity relation. **Comment subtlety** (see below) — the comment iteration lands the IL *at* the
   `\n`; the next iteration's space-skip consumes it, so a comment spans `body_comment`+1 space step.
   Everything is **existential fuel** now (use `exec_mono_le` + `exec_while_step`/`exec_while_done`).
3. **coreSpec assembly** (item C) + prelude peel (15 `lit`/init instrs → loop-entry `Regs`+state).
4. Optionally: conformant strtoull functional proof; **`compile_sim`** (T1) to real RV64I bytes.
