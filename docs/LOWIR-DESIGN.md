# LowIR — design decisions, alternatives, and likely extensions

Status: design record. Captures *why* the lower IR looks the way it does, what was rejected,
and where it's expected to grow. Companions: [LIBC-FORMALIZE.md](LIBC-FORMALIZE.md) (altitude
survey), [MEMORY-BORROWS.md](MEMORY-BORROWS.md) (separation discipline),
[RESUME-LOWIR.md](RESUME-LOWIR.md) (proof status), [TCB.md](TCB.md) (trust base).

## Purpose

LowIR is a small intermediate language sitting between a libc function's functional spec and
RISC-V bytes. The bet is CompCert's: prove each function correct against its spec *on the IL*
(clean, control-structured), and prove the IL→RV64I compiler correct **once** (`compile_sim`),
so every function's theorem transports to the machine for free. The first full instance is
`CtrlHex0Proof.hex0_correct` (hex0 ≡ `Hex0.coreSpec`, sorry-free).

Two flavors exist:
- **`LowIR.lean`** — original structured IL (`skip/seq/addi/add/sub/orr/slli/srli/lbu/sb/ife/while`),
  with `compile` + `encode` to RV64I and the T1 simulation framework. `compile_sim` is a
  **sanctioned `sorry`** (the only one in the tree).
- **`LowIR/Ctrl.lean`** — adds non-local control flow (`block/while/brkB/contL/ret`) over an
  outcome-threaded `exec`. Reuses `St`/`Cond`/`evalCond`. **Has no compiler yet** (see Ext. 6).
  The hex0/strlen/strtoull proofs are on `Ctrl`.

---

## 1. Decisions made

### D1. A structured IL, not direct bare-RISC-V proofs
- **Decision.** Prove functional correctness against `exec` on a structured IL; defer the machine
  (PC, fetch/decode, instruction encoding, the 16 modelled encodings) to `compile`/`encode`/`compile_sim`.
- **Rationale.** Per-construct `exec` equation lemmas (`exec_addi`, `exec_seq_normal`, `exec_ife_then`, …)
  turn proofs into rewriting. No PC arithmetic, no branch-offset/encoding reasoning at the spec level.
- **Alternatives.** (a) Prove hex0 directly on the bare RISC-V model — viable for one tiny program,
  but every proof re-pays the machine reasoning and there's no amortization. (b) Use an existing
  verified IR (CompCert Cminor/RTL, CakeML) — heavyweight to import and to connect to this project's
  bespoke RV64I model.
- **Status / caveat.** Win is real but **relocates** machine complexity into `compile_sim`, which is
  paid once and reused. Until `compile_sim` (for the IL actually used, `Ctrl`) is discharged, the
  end-to-end story has a gap.

### D2. State = unbounded register file + flat byte memory
- **Decision.** `structure St where regs : Reg → Word; mem : Word → Byte`, with `Reg = Nat`
  (so **infinitely many registers**), `Word = BitVec 64`, `Byte = BitVec 8`. `x0` reads as 0
  (`rget`/`rset` special-case it). `mem` is a **total** function over the whole 2⁶⁴ address space.
- **Rationale.** Unbounded registers ⇒ functional proofs never spill; locals just live in registers
  (hex0 uses x5–x31). Total flat `mem` ⇒ any address is loadable/storable, so memory regions
  (input/output buffers, and in principle stack structs) are *representable* with plain address
  arithmetic — no allocation primitive needed to write such code.
- **Alternatives.**
  - *Bounded 32 GPRs* (match the machine): forces spilling into the spec-level proof. Rejected —
    spilling is a compiler concern; keep it out of functional proofs.
  - *Block-structured memory* (CompCert: `block → offset → byte`, `alloc` returns a fresh block):
    freshness gives object disjointness *for free*, matching C's UB model. **Rejected for this
    project** (see D5) — it complicates pointer arithmetic and adds a refine-to-flat-RV64I obligation;
    we recover separation differently.
- **Status / caveat.** The unbounded register file is a fiction the compiler must reconcile with
  RV64I's 32 GPRs ⇒ `compile_sim` owns register allocation + spill-to-stack. So the stack is *implicitly*
  deferred to the compiler even though the IL has no stack (hex0 fits in 32, so it dodges this).

### D3. Non-local control flow (`ret`/`block`/`brkB`/`contL`) in `Ctrl`
- **Decision.** `Ctrl` threads an `Outcome` (`normal/brk k/cont k/ret`) through a clocked big-step
  `exec : Nat → Stmt → St → Option (St × Outcome)`. `ret` is maximally non-local (caught only at the
  function boundary by `run`); `block` catches `brkB 0`; `while` is a continue scope. de-Bruijn indices
  for `brkB`/`contL`.
- **Rationale.** hex0's five error exits become a **flat guard cascade**: `err code = seq (lit 14 code) ret`,
  and `seq` short-circuits on `ret`. The reasoning primitives (`exec_seq_ret`, `exec_block_catch`,
  `exec_while_ret`, …) are one-line `by simp [exec, h]`. Measured win over the original IL, which had to
  nest every error leaf as the last statement on its path **plus** an `in_idx := in_len`
  "poison-the-loop-guard" hack.
- **Alternatives.** (a) Original `LowIR` (structured ife/while only) — usable but the nesting+poison-guard
  is painful for early-exit-heavy code. (b) Flat branches/jumps with labels — that's the *compile target*,
  not a good proof surface. (c) Continuation/monadic encoding — heavier semantics.
- **Status / caveat.** The simplification is **paid back** in the (unwritten) `Ctrl`→RV64I compiler:
  lowering `while/block/ret` to flat jumps with label resolution is the hard control-flow pass. Also, for
  straight-line loops with no early exit (strlen), the outcome machinery is *pure overhead* — same proof
  shape, just carrying `.normal` (recorded in `CtrlStrlen`).

### D4. Clocked big-step semantics (explicit fuel)
- **Decision.** `exec` takes a `fuel : Nat`; every recursive call is at `fuel` from `fuel+1`
  (structurally terminating, directly executable → `#guard`/`native_decide` validation).
- **Rationale.** Executability (validate programs by running them) + structural termination (no
  well-founded-recursion ceremony) + a clean induction handle.
- **Alternatives.** (a) Relational big-step (`⇓`, no fuel) — no fuel bookkeeping, but not executable and
  needs explicit induction principles. (b) Small-step / trace semantics — closer to the machine but more
  painful for functional proofs.
- **Status / caveat.** Fuel composition across variable-cost loops was friction; neutralized **once** by
  `exec_mono`/`exec_mono_le` (more fuel never changes a `some` result), after which every lemma returns an
  *existential* fuel and results are bumped to a common fuel before combining. With that lemma the clocked
  choice costs little.

### D5. Separation via a borrow discipline on flat memory (not block memory)
- **Decision.** Keep `mem` flat; recover non-aliasing with a lightweight **Tree-Borrows-residue** layer:
  `Slice (base,len)`, `Perm = shared | uniq`, `Borrow`, `Disjoint`, `Wf` (a unique borrow is disjoint from
  every other), and `storeByte_preserves`. Function specs take a `Wf` precondition; e.g.
  `hex0_correct` assumes `Wf [⟨⟨inBase,len⟩,.shared⟩, ⟨⟨outBase,cap⟩,.uniq⟩]`, from which input/output
  disjointness (and "output writes don't perturb input") follows.
- **Rationale.** A libc needs *asymmetric* aliasing: shared (read) borrows may overlap (two readers of one
  `const char*`); a unique (write) borrow must be disjoint from everything. Raw "all regions disjoint" is
  both too weak (ad-hoc) and too strong (forbids shared overlap). TB also gives dynamic ranges and interior
  pointers (the `strtoull`-walks-`nptr` idiom). See [MEMORY-BORROWS.md](MEMORY-BORROWS.md).
- **Alternatives.** (a) Block-structured memory — freshness gives disjointness for free, but bakes
  separation into the *memory model* and needs a refine-to-flat-RV64I proof. (b) Full separation logic
  (VST/Iris-style) — powerful but heavy. (c) No separation, prove with concrete addresses + size bounds —
  brittle, doesn't compose.
- **Status / caveat.** We take the **separation *consequence*** of TB, not its operational model (no
  per-location permission automaton, no derivation tree). Disjointness is *asserted* per object as a
  precondition and maintained as an invariant — fine while live objects are few (hex0: input vs output).

### D6. Single-threaded; `errno` is a plain global
- **Decision.** Assume the bootstrap is single-threaded (no `pthread_create`/`clone(CLONE_VM)`/TLS), so
  `errno` is a global `int` at a fixed address, modelled as a unique borrow disjoint from caller buffers —
  *not* thread-local storage. Recorded as a TCB assumption.
- **Rationale.** Faithful for a hex0 bootstrap; avoids modelling TLS/`%fs`-relative addressing. `sprintf(&errno,…)`
  is then *precisely* illegal: it would need a second unique borrow overlapping libc's → ill-formed.
- **Alternative.** Model TLS / `__errno_location` returning a per-thread pointer. Deferred until threads exist.

---

## 2. Current non-features (deliberate gaps)

- **No stack / SP / frames / `alloca`.** Stack data is *representable* (a `mem` region off a chosen SP
  register, addressed by arithmetic) but unsupported by convention or sugar. Address-taken/aggregate locals
  would have to be placed in `mem` by hand.
- **No `call`/return-address.** `Ctrl.ret` returns to the function boundary; there is no call instruction,
  no `ra` save/restore, no nesting. The model is whole-program / inlined.
- **Byte-only memory ops.** Only `lbu` (byte load) and `sb` (byte store). Wider accesses must be synthesized
  from byte ops + `slli`/`srli`/`orr` (hex0 builds a byte from two nibbles this way).
- **No register-count limit.** Spilling to stack for >31 live registers is a `compile_sim` obligation, not
  expressible/relevant at the IL.
- **Separation is manual.** `Disjoint`/`Wf` are per-object hypotheses; nothing produces them automatically
  (no borrow checker yet — see Ext. 5).
- **No `compile_sim` for `Ctrl`.** Only the original `LowIR` has a compiler (with the sorry); `Ctrl`
  theorems have no path to bytes yet.

---

## 3. Likely extensions (roughly in order of when they'll be forced)

1. **Wider load/store** (`lw/lh/ld/sw/sh/sd`). The one genuine *expressiveness* gap for structs/aggregates:
   multi-byte fields are miserable to synthesize from bytes. Additive constructors, one-line `exec`
   equations, direct RV64I mapping. Add when the first multi-byte field appears.
2. **Stack as a `mem` region + SP convention.** Pick a register as SP; frames are decrements. Each frame /
   stack struct is a **unique `Slice`** in the borrow layer — disjoint from heap, caller buffers, and
   sibling frames. Then "the callee's locals don't alias the caller's `&out`" is the *same* separation
   theorem as hex0's input/output disjointness — no new machinery. Forced by the first address-taken local
   or non-caller-provided buffer.
3. **`call`/return with return-address** (vs. whole-program inlining). Needed for *compositional*
   per-function verification of non-leaf functions. Brings a calling convention; locals-as-stack-slots
   becomes natural. Until then, inline.
4. **`alloca` / fresh-region primitive.** If manual per-frame/per-object disjointness bookkeeping comes to
   dominate proofs (it will, once many frames + heap objects coexist), add a primitive that mints a
   *provably-fresh, disjoint* `Slice` — recovering block-memory's "freshness ⇒ disjointness for free"
   *locally*, without switching the whole memory model. The escape hatch toward block memory if D5 strains.
5. **Borrow-typed higher IRs (the strategic direction).** Promote the `Wf` precondition from a loose `Prop`
   into pointer *types*. Pipeline:
   - **HIR (Tree Borrows, temporal):** `&'a [u8]` / `&'a mut [u8]`; validity time-varying (reborrow,
     reservation→activation).
   - **MIR (regions, spatial):** lifetimes erased; pointer carries a region (slice); context carries
     disjointness obligations — TB's temporal discipline *flattened to the call's extent*.
   - **LowIR (flat memory):** region = `Slice`, disjointness = `Wf`/`Disjoint` hypotheses (today's hex0).

   So a pointer's "what it's valid for + disjoint with" travels as **type index → region+`Wf` side-condition
   → `Slice`+`Disjoint` hypothesis**, each lowering pass transporting the guarantee into the lower vocabulary.
   *Key subtlety:* TB is temporal; the function-boundary contract is its **spatial shadow** ("these regions
   disjoint for this call") — lossy but sound and exactly what a callee consumes (why hex0's spatial `Wf`
   sufficed). Rigor levels: (a) refinement-as-`Prop` (today); (b) **indexed pointers** `Ptr (s : Slice) perm`
   with disjointness in a live-borrows context — the recommended sweet spot, loads carry within-slice proofs
   (memory safety falls out); (c) full borrow type system with a **soundness theorem proved once**
   (RustBelt/λRust style) so well-typedness *produces* the `Wf`/`Disjoint` facts — same "pay once" economics
   as `compile_sim`, but a large effort. Build (b) with a small once-proved soundness lemma; grow toward (c)
   only if in-body reborrowing forces it.
6. **`compile_sim` for `Ctrl`.** The outstanding pay-once cost: a verified `Ctrl`→RV64I compiler, whose hard
   part is exactly the control-flow lowering (`while/block/ret` → jumps + label resolution) and register
   allocation/spilling (D2 caveat). Either compile `Ctrl` directly, or lower `Ctrl`→`LowIR` (eliminating
   `block/brk/cont/ret`) and reuse the existing compiler.
7. **Toolbox factoring.** Promote the now-substantial reusable pieces — `exec_mono`/one-layer `exec_*`
   equations, the `Slice`/`Borrow`/`Wf` layer, `regionBytes` — out of `CtrlHex0Proof`/`CtrlStrtoullProof`
   into shared files (`LowIR/ExecMono.lean`, `LowIR/Borrow.lean`) for the rest of the libc.

---

## 4. The architecture in one line

Separation does **not** live in the memory model (no block structure); it lives in the **type system /
function contracts** at the higher IRs and is threaded down as data + proofs, bottoming out as `Wf`/`Disjoint`
hypotheses on flat-memory functional theorems. Keep LowIR flat and machine-faithful; pay for the IL→RV64I
compiler once; let the (future) borrow type system *produce* the disjointness that LowIR proofs assume.
