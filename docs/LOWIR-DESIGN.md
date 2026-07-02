# LowIR — design decisions, alternatives, and likely extensions

Status: design record. Captures *why* the lower IR looks the way it does, what was rejected,
and where it's expected to grow. Companions: [LIBC-FORMALIZE.md](LIBC-FORMALIZE.md) (altitude
survey), [MEMORY-BORROWS.md](MEMORY-BORROWS.md) (separation discipline),
[RESUME-LOWIR.md](archive/RESUME-LOWIR.md) (proof status), [TCB.md](TCB.md) (trust base).

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

### D7. Activation-local calls: `rets := call f args` over an env-threaded `exec` — not SSA
- **Decision** (2026-07, not yet implemented). Calls are **by name** against a function
  environment `Env : Name → FunDef` threaded through `exec` (or fixed as a parameter).
  **Arities are static**: a function's signature is part of its definition,

  ```
  FunDef := { argc rvc : Nat
            ; params : Vect argc Reg          -- registers receiving the arguments
            ; rets   : Vect rvc Reg           -- registers read at the ret boundary
            ; sig    : BorrowSig argc         -- boundary borrow contract (see below)
            ; body   : Stmt }
  ```

  and a call site is `(rets : Vect rvc Reg) := call f (args : Vect argc Reg)` — **arity
  mismatch is unrepresentable by construction** (intrinsic *arity*, the one narrow slice of
  lean-mlir-style intrinsic typing worth taking here; full intrinsic typing stays rejected on
  elaborator-cost grounds). The call evaluates `args` in the caller's registers, runs the body
  in a **fresh register file** (params bound to argument values, all other registers
  **zero-initialized**), reads the callee's `rets` registers at its `ret` boundary, and binds
  them at the call site — the caller's register file is otherwise *untouched by construction*.
  `BorrowSig argc` names the callee's borrowed regions **in terms of its parameters** ("slice
  based at arg 0, length arg 1, shared") so that one generic call rule — caller's `Wf` context
  + args satisfy `sig` ⇒ callee spec applies + frame over everything disjoint from `sig` —
  replaces per-call manual `Disjoint` threading; the future borrow checker *emits* `sig`,
  higher-IR pointer types lower to it, LowIR proofs consume it (cf. Ext. 5). **Registers are function-local; memory stays shared** (the `Slice`/`Wf` borrow
  discipline is unchanged — by-reference data crosses as addresses). Zero-init is made
  semantically irrelevant by a **definite-assignment check** (no local read before written,
  except parameters) plus a once-proved lemma that `exec` of a definitely-assigned body does not
  depend on unread registers — another checker-produces-the-hypothesis instance (cf. N3).
  Explicitly **not SSA**: registers stay mutable, `while` keeps its state-invariant proof shape;
  no φ-nodes, no out-of-SSA pass. SSA is reserved for a possible future rewrite-engine IR (N9).
- **Rationale.** Register preservation across calls becomes a **non-theorem** at the IL; callee
  specs shrink to relations between `(args, mem)` and `(rets, mem')` with no register-footprint
  clauses and no global register-naming convention; the calling convention lives *solely* in
  `compile_sim` pass 4 (N2). This is the survey-standard design above the allocation boundary
  (CompCert RTL `Icall`, bedrock2 `cmd.call`, CakeML wordLang, Pancake). Pleasant side effect:
  env-based calls consume fuel per activation, so recursive semantics are well-defined for free
  (whether the verified fragment *allows* recursion remains a separate, open policy decision).
- **Alternatives rejected.** (a) Shared-register `.call g` (the `d7f8298` ret-catch construct):
  makes every callee spec carry its full register footprint and register naming a whole-program
  obligation — may survive only as inline-expansion sugar. (b) Full SSA: buys rewriting
  ergonomics we don't need here, costs φ-semantics and an out-of-SSA pass + proof, and conflicts
  with `while` + mutation. (c) Junk (nondeterministic) init of the fresh file: honest to the
  machine but breaks the deterministic `Option`-based `exec`; the definite-assignment check
  recovers the same effect deterministically.
- **Status / caveat.** `CtrlCall.lean` (shared-register call + cross-call disjointness example)
  is to be reworked onto D7; the memory-side reasoning carries over verbatim. If the inline
  ret-catch `.call g` survives as sugar, it is **expanded in pass 1** so compile passes 2–4 see
  only env-calls (one call shape per pass, one proof case). The compiler must realize the
  fiction — argument passing, callee-saved discipline, frame slots — which is exactly pass 4's
  job and is now *located* there rather than added.

### D8. Per-function frames: `frameSize` in `FunDef`, semantic `sp` in `St` — no alloca statement
- **Decision** (2026-07, not yet implemented). `FunDef` gains `frameSize : Nat`. `St` gains
  `sp : Word` — a **semantic component programs cannot write** (it is not a register). Call
  semantics: check `sp − frameSize ≥ stackLo` (else `none` — the same "didn't complete" channel
  as fuel exhaustion), run the body with `sp := sp − frameSize` and the **frame base bound into
  a designated register** of the fresh file (an implicit extra parameter alongside `params`);
  on `ret` the caller resumes with its own `sp` — restoration is structural, never
  program-visible. **No new statements**: the frame is accessed through the existing
  loads/stores (Ext. 1's `ld/sd` included) off the frame-base register, by plain address
  arithmetic. **Dynamic-size stack allocation (`alloca`/VLAs) is explicitly disallowed**; heap
  allocation (`malloc`/`calloc`/`free`) remains non-primitive per N7 — libc functions verified
  on top, never IR constructs.
- **Rationale.**
  - *Frame lifetime = activation* ⇒ deallocation coincides with the existing `ret` boundary —
    zero interaction with the `Outcome` machinery. (A scoped `stackalloc` statement would put a
    pop obligation into every early-exit case: `ret`/`brkB`/`contL` crossing the scope.)
  - *Freshness ⇒ disjointness by construction*: a once-proved **stack-discipline lemma** (frames
    nest downward from `sp₀`; live frames are pairwise-disjoint unique `Slice`s) plus one global
    hypothesis "the stack region `[stackLo, sp₀)` is disjoint from program data" (bedrock2's
    `machine_ok` has literally this conjunct) makes every frame automatically disjoint from
    heap, caller buffers, and sibling frames — Ext. 4's goal, without block memory and without
    per-call proofs.
  - *Address-independence without nondeterminism*: `sp₀` is **universally quantified in every
    theorem** (as all of `St` already is — hex0 quantifies `inBase`/`outBase` the same way), so
    programs provably cannot depend on concrete frame addresses. bedrock2 buys this guarantee
    with a nondeterministic address pick; ∀-quantification buys it while keeping `exec`
    deterministic.
  - *Precedents*: CompCert Cminor's `fn_stackspace` and Caesium's `CallS` stack blocks
    (per-function, signature-declared); bedrock2's statement-level `stackalloc` rejected here
    for its nondeterminism (breaks `Option`-deterministic `exec`) and scope/outcome
    interactions.
- **Alternatives rejected.** (a) SP-as-register convention (Ext. 2's original sketch) — dead
  after D7: registers are function-local, so an SP would be an explicit argument to every
  function and frame disjointness manual bookkeeping. (b) Statement-level scoped `stackalloc` —
  see above. (c) Dynamic `alloca` — excluded outright.
- **Status / caveat.** End-to-end theorems gain the static precondition "total frame usage
  along the call tree ≤ stack size" — computable without recursion (the recursion policy itself
  is still the open C5 decision). Compile-side: pass 4 lays out **one** physical frame =
  `frameSize` + spill slots + saved `ra`; `match_states` relates semantic `sp` to the real `sp`
  register; passes 2–3 never see frames at all.

---

## 2. Current non-features (deliberate gaps)

- **No stack / SP / frames / `alloca`.** Stack data is *representable* (a `mem` region off a chosen SP
  register, addressed by arithmetic) but unsupported by convention or sugar. Address-taken/aggregate locals
  would have to be placed in `mem` by hand. **Decided (D8):** per-function frames via
  `FunDef.frameSize` + a semantic, program-unwritable `sp` in `St`; awaiting implementation.
- **`call` is a `ret`-boundary, not an activation boundary.** `Ctrl.call g` (added `d7f8298`,
  worked example in `CtrlCall.lean`) runs the callee body in the *same* state — shared register
  file, shared memory — and catches the callee's `ret`. There is no argument passing, no fresh
  locals, no `ra`. Consequence: register discipline across calls is whole-program — callee specs
  state their full register footprint, and register *naming* is a global convention. **Decided
  (D7): `call` becomes activation-local** — fresh register file + explicit args/rets, register
  preservation a non-theorem at the IL. `CtrlCall.lean` awaits rework onto D7.
- **Byte-only memory ops.** Only `lbu` (byte load) and `sb` (byte store). Wider accesses must be synthesized
  from byte ops + `slli`/`srli`/`orr` (hex0 builds a byte from two nibbles this way).
- **No register-count limit.** Spilling to stack for >31 live registers is a `compile_sim` obligation, not
  expressible/relevant at the IL.
- **Separation is manual.** `Disjoint`/`Wf` are per-object hypotheses; nothing produces them automatically
  (no borrow checker yet — see Ext. 5).
- **No `compile_sim` for `Ctrl`.** Only the original `LowIR` has a compiler (with the sorry); `Ctrl`
  theorems have no path to bytes yet.

---

## 2b. Non-goals — and where each one lives instead

Unlike §2 (features the IL will likely grow), these are **permanent** exclusions: things LowIR
should *never* do, each pushed to a specific other layer. The IL stays small because every one of
these has a designated home. (Informed by the [third-party review series](README.md#third-party-design-reviews)
and [DESIGN-THESES.md](DESIGN-THESES.md).)

| # | Non-goal for the IR | Where it lives instead | Notes / trigger to revisit |
|---|---|---|---|
| N1 | Finite registers, register allocation, spilling | `compile_sim` pass 3, as an untrusted allocator + **verified checker** (translation validation) | Never expressible at the IL — that's the point of `Reg = Nat` (D2). |
| N2 | Calling convention: stack layout, `sp`/`ra`, prologue/epilogue, **callee-saved preservation** | `compile_sim` pass 4, with the ABI as a *parameter record*; stated once as a per-compiled-function contract ("only caller-saved + results differ, `sp` restored, `pc = ra`", bedrock2's `only_differ` shape) | At the IL, register preservation across calls is a **non-theorem** by D7 (activation-local `call`). Tail calls are the one place the convention leaks upward (CompCert `tailcall_possible`). |
| N3 | Separation / aliasing **enforcement** | *Above* the IL: borrow-typed higher IRs / future borrow checker (Ext. 5) *produce* `Wf`/`Disjoint`; LowIR proofs only *consume* them as hypotheses | Never into the memory model (D5). The checker is a pure gate whose output is hypotheses — rustc's architecture. |
| N4 | Pointer provenance, int↔ptr cast semantics | The borrow layer above (spatial shadow of Tree Borrows); flat `mem`, addresses are integers | Revisit only if `container_of`/pointer-tagging idioms are ever required — then RefinedC's PNVI/VIP is the reference, *paid per function*, not globally. |
| N5 | Undefined behavior | Nowhere — **UB does not exist at this level by construction**: `exec` is total modulo fuel; `mem` is total. "Going wrong" is a C-level notion, and LowIR is not C | If a C-like surface is ever built above, *its* UB is discharged by *its* checker/verifier before reaching LowIR (thesis 9: no UB nooks). |
| N6 | Concurrency, threads, TLS, atomics | Out of scope entirely; single-threaded is a **TCB assumption** (D6); `errno` is a global unique borrow | Revisit only if the bootstrap ever grows threads — then `__errno_location`/TLS modelling and a memory model decision (big lock à la seL4 SMP, or oracle traces). |
| N7 | Heap allocation, GC | No IR primitive. `malloc`/`free` are *libc functions verified on top of* the IL; freshness bookkeeping via the Ext. 4 `alloca`-style fresh-`Slice` primitive if manual disjointness dominates | Pancake's lesson: no GC anywhere in the pipeline. Allocator verification is a program proof, not a language feature. |
| N8 | I/O, syscalls | The external-call spec interface (§4): pre/post + frame per external, at every pass level; observable behavior via (future) event traces | Today the boundary is memory pre/post (hex0). **Known retrofit debt**: `exec` has no trace/oracle component yet — decide before I/O-bearing libc functions (see review note C2). |
| N9 | Optimization | Not in `compile_sim` (passes stay dumb and small). If optimization is ever wanted: a verified rewrite engine over the IL, lean-mlir style — engine proved once, rules as lemmas | Re-running verified passes is free (composition); resist smartness inside lowering passes. |
| N10 | Termination proofs, WCET / cost | Theorems are partial correctness with **existential fuel**; "`∃ fuel, exec fuel …`" *is* the termination statement per function. Cost/WCET: non-goal | bedrock2's metric/leakage strata are the reference design if cost or constant-time claims are ever needed — they'd thread through `compile_sim` phase records, a large retrofit. |
| N11 | Instruction encoding, PC arithmetic, branch offsets | `compile_sim` passes 5–6; encoder verified to bytes (the TCB point) | Cross-check opportunity: riscv-coq (task #7) and SailRV64 (lean-mlir's Sail-derived Lean semantics) as independent legs. |
| N12 | Floating point | Absent — RV64I integer subset only | Until forced; then it's new ops + Flocq-class semantics work, a separate campaign. |

One-line summary: **the IL owns functional meaning over flat state; everything about *machines*
(N1, N2, N11), everything about *discipline* (N3, N4, N5), and everything about the *world*
(N6, N8) is someone else's job, on purpose.**

## 2c. Low-level boundary catalog — where machine magic is still needed

Cases the D7/D8 fiction cannot express, each handled by one of three mechanisms — none of which
is an IL statement: **(a)** a hand-verified machine-level stub below `compile_sim` with an
IL-visible spec (the seL4 `MachineOps` pattern); **(b)** an external-call node with
pre/post + frame + event spec (the CompCert `external_call` / CakeML FFI / bedrock2
`mGive`/`mReceive` pattern, §4); **(c)** a design dodge that converts the hard case into an easy
one (seL4's signature move). The IL's job is to make these *inexpressible*; the boundary's job
is to make them *specifiable*.

| # | Case | Mechanism | Precedent | Status / trigger |
|---|---|---|---|---|
| B1 | **Program entry** (`_start`): convention established out of nothing — no caller, junk registers, no `sp` yet | (a) one verified prologue stub: from loader guarantees, establish `machine_ok` + D8's stack hypothesis, enter `main` under the `cc_spec` contract | bedrock2 `ToplevelLoop` preamble; CakeML startup/heap init | needed with `compile_sim` passes 4–5 |
| B2 | **Syscalls** (`ecall`) | (b) external-call node; the *world-fixed* register convention (`a7` number, args `a0..a5`, result `a0`) is marshalled in the lowering, proved once per external. "Kernel touches only the passed buffers" is a **named TCB axiom**. Nondeterministic results (`read`) need the oracle (C2 retrofit) | CompCert `external_call`; CakeML FFI oracle; bedrock2 `mGive`/`mReceive` | needed with the first I/O-bearing libc function |
| B3 | **Interrupt handlers**: async entry at arbitrary machine state, no caller-saved contract, CSRs, `mret` | (c) **dodge**: interrupts disabled during verified execution — a config-level TCB assumption (seL4-style). If ever needed: (a) a save-everything trampoline whose *body* is an ordinary IL function. Handler/main **interleaving is concurrency** — out of scope with N6 | seL4 preemption points + verified-config matrix | keep interrupts off; revisit never, ideally |
| B4 | **Context capture** — `setjmp`/`longjmp`, coroutines, OS context switch: reifies exactly what D7/D8 made fictional (activation-local registers, LIFO frames) | refuse at the IL. Legal-`longjmp` error unwinding and generators get **structured, correct-by-construction replacements** — Ext. 11. A scheduler's context switch, if ever, is an (a) stub with a save-exactly-these-registers spec | rustc coroutine transform; seL4 TCB switch | Ext. 11, later; variadics/stack-walking stay non-goals |
| B5 | **MMIO / volatile device access**: two reads of a device register disagree — plain `lbu` on it violates `mem`-purity | (b) event-bearing external ops, *never* raw loads/stores. Sharpest near-term item if bare-metal I/O appears; blocked on the C2 oracle/trace retrofit | Pancake ShMem-as-FFI; bedrock2 MMIO → exactly one instruction | before any device code exists |
| B6 | **Executing emitted code** — the bootstrap's own case: hex0 writes bytes that later run | (c) **separate-runs assumption**: emitted code executes in a fresh machine run; theorem composition is meta-level. Same-run execution would need the CakeML-`Install` problem set (`fence.i`, W^X, code memory in `match_states`) | CakeML `Install` (the hard version we avoid) | name the separate-runs assumption in [TCB.md](TCB.md) now |
| B7 | **Privileged/CSR/cache ops** (`csrr/csrw`, `fence`, `sfence.vma`) | (a) an axiomatized machine-ops module: each op a verified stub or a named assumption | seL4 `MachineOps` / `machine_op_lift` | only if machine mode / paging ever |

---

## 3. Likely extensions (roughly in order of when they'll be forced)

1. **Wider load/store** (`lw/lh/ld/sw/sh/sd`). The one genuine *expressiveness* gap for structs/aggregates:
   multi-byte fields are miserable to synthesize from bytes. Additive constructors, one-line `exec`
   equations, direct RV64I mapping. ~~Add when the first multi-byte field appears.~~
   **Priority bump (2026-07): compiler-forced.** `compile_sim` pass 4 spills 64-bit registers;
   synthesizing an 8-byte spill from eight `sb`s is absurd, so `ld`/`sd` must exist in the IL
   *before* pass 4 regardless of what source programs need.
2. **Stack as a `mem` region + SP convention.** ~~Pick a register as SP; frames are decrements.~~
   **Resolved by D8** (the register-convention sketch died with D7's function-local registers):
   per-function `frameSize` + semantic `sp` in `St`; each frame is a unique `Slice` minted by the
   call rule, disjoint by the once-proved stack-discipline lemma. Implementation forced by the
   first address-taken local or non-caller-provided buffer.
3. **`call`/return with return-address** (vs. whole-program inlining). Needed for *compositional*
   per-function verification of non-leaf functions. Brings a calling convention; locals-as-stack-slots
   becomes natural. Until then, inline.
4. **`alloca` / fresh-region primitive.** ~~Add a primitive that mints a provably-fresh, disjoint
   `Slice`.~~ **Resolved by D8 for stack objects**: the call rule mints the frame as a fresh
   unique `Slice`, disjointness from the once-proved stack-discipline lemma + the single
   stack-region-⊥-data hypothesis — block-memory's "freshness ⇒ disjointness" recovered locally,
   no new statement. **Residual scope: heap objects** — when a verified `malloc` arrives (a libc
   function per N7, not a primitive), *its spec* plays this role (returns a fresh unique `Slice`
   disjoint from all live borrows); if that spec's bookkeeping strains D5, this entry revives as
   the escape hatch toward block memory.
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
6. **`compile_sim` for `Ctrl`.** The outstanding pay-once cost: a verified `Ctrl`→RV64I compiler. **Do not
   make it one proof** — decompose it into small per-pass simulations (see §5). Hard parts: control-flow
   lowering and register allocation/spilling (D2 caveat); the rest is mechanical.
7. **Toolbox factoring.** Promote the now-substantial reusable pieces — `exec_mono`/one-layer `exec_*`
   equations, the `Slice`/`Borrow`/`Wf` layer, `regionBytes` — out of `CtrlHex0Proof`/`CtrlStrtoullProof`
   into shared files (`LowIR/ExecMono.lean`, `LowIR/Borrow.lean`) for the rest of the libc.
   Includes the `lit` helper, currently defined identically in four files (and superseded by
   Ext. 10's `set r (imm v)`, which also removes the 12-bit ceiling on literals).
8. **Well-formedness checker `Stmt.wf` + boundary lemma.** A decidable
   `wf (blockDepth loopDepth : Nat) : Stmt → Bool`: `brkB`/`contL` indices in range, shift
   amounts `< 64` (RV64I shamt is 6 bits — today `slli/srli (sh : Nat)` is unconstrained and
   unencodable for `sh ≥ 64`), call names resolve in `Env` (post-D7), definite assignment (D7).
   Once-proved boundary lemma: `wf` programs never surface `brk`/`cont` at the function boundary
   — today an escaping `brkB` makes `run` return `none`, **indistinguishable from fuel
   exhaustion**, and `.call`'s semantics merely *comments* "well-formed: no free brk/cont".
   Payoffs: generic outcome-dismissal lemmas in every proof (e.g. "wf body ⇒ `block body`
   yields only normal/ret"), higher IRs discharge `wf` by construction, and pass 2's label
   resolution becomes *total* on wf programs. Checker-produces-hypothesis instances #2/#3
   (with the borrow checker as #1) — house them in one static-checks module.
9. **`annot` — a semantically-inert annotation statement.** `exec (annot a) s = some (s, .normal)`;
   erased in pass 1. The carrier higher IRs need: borrow events (the checker's
   reborrow/resolve points), loop-invariant anchors, spec labels. Planted intent *in the
   program* beats position-keyed side tables — positions don't survive transformations,
   statements do (rustc's `FakeRead`/`AscribeUserType` lesson). Near-zero cost now, painful
   retrofit after more passes exist.
10. **Pure expression trees: `set (rd : Reg) (e : Expr)`.** `Expr` = reg / imm / binop / shift —
    **no memory reads**. One `exec_set` equation collapses today's `slli`/`orr`/`addi` chains
    (hex0's nibble-building, every address computation) into one `simp`; gives the HIR→LowIR
    lowering its natural target (bedrock2's expr/statement split); lets `Cond` become an `Expr`
    (deduplicating the `(c, a, b)` triples in `ife`/`while`); subsumes `lit` at arbitrary width.
    Compile cost: a verified LowIR→LowIR flattening pass — structural induction, no
    temp-freshness subtleties thanks to infinite registers. Comfort until the HIR exists;
    schedule together with Ext. 5.

11. **Structured replacements for `setjmp`/`longjmp` (B4) — not now, maybe later.** Two halves,
    for the two features hiding inside `setjmp`/`longjmp`:
    - *Unwind outcomes* (the error-handling 90%): defined-behavior `longjmp` only jumps *up* to a
      live activation — "return through k frames at once". Add an `Outcome.throw` that (unlike
      `brk`/`cont`, which `wf` bans from crossing calls) **propagates through `call` boundaries**
      until absorbed by a `catch` construct. The D8 payoff: `sp` restoration is structural in the
      call semantics, so a throw crossing k frames restores `sp` k times **by construction** —
      resuming a dead frame or corrupting the stack is unrepresentable. Cost: one outcome
      constructor + one catch construct + propagation cases, same shape as the existing `ret`
      plumbing.
    - *Stackless coroutines* (`co_suspend`/`co_resume` — generators, cooperative scheduling):
      **zero new IL semantics.** IL-level suspension would force `exec` to return a reified
      continuation (statement context + register file + frame chain) — precisely the machinery
      D7/D8 keep fictional. Instead, the rustc coroutine transform at a higher IR: liveness
      across suspension points determines a **state struct**; suspended-live locals move into a
      caller-provided unique `Slice` in `mem` (*off* the stack — the LIFO discipline never sees
      them); `co_resume` lowers to an ordinary D7 call `resume(statePtr, input) → output ⊕ Done`;
      soundness is one checker rule — **no borrows of coroutine-locals across a suspension
      point** (rustc's movable-coroutine rule) — emitted by the future borrow checker like any
      other hypothesis. Verified once as a higher-IR lowering (engine × instances).
    - *Rejected*: stackful fibers (per-coroutine stacks + machine-level context switch) — breaks
      the single-`sp` model, needs per-stack discipline lemmas and a B7-style switch stub; no
      libc-relevant benefit.

**Priorities (agreed 2026-07):** Ext. 8 first (cheapest, pays in every proof *and* in pass 2);
then D7's `FunDef` implementation including the `Vect` arities and `BorrowSig` (the scaling
decision — design the env once); then Ext. 1 (`ld`/`sd`, compiler-forced). Ext. 9 is the
"cheap now, expensive later" sleeper — do it alongside Ext. 8. Ext. 10 waits for the HIR.
Ext. 11 is explicitly *later* — the unwind-outcome half is cheap and may come early if error-path
ergonomics demand it; the coroutine half waits for the HIR + borrow checker.

---

## 4. Compiler-side architecture — decomposing `compile_sim` (CompCert/CakeML-informed)

`compile_sim` (`Ctrl` → RV64I bytes) must **not** be a monolith. Following CompCert (many small IRs,
each a forward simulation with an explicit `match_states` source↔target relation, composed by
transitivity) and CakeML (verify down to the *bytes* incl. the encoder; make the stack explicit only in
a low IR), factor it into passes. Each pass: a `match_states` relation + a step-preservation lemma;
chain them. Lessons adopted:

- **One shared memory model** (flat bytes + the `Slice`/borrow layer) across *all* levels — disjointness
  facts transport down without re-translation (CompCert reuses its `Mem` from top to bottom).
- **Event/trace output threaded through every level** — so I/O-bearing libc (`read`/`write`/`printf`) is
  even *statable*; correctness is trace-preservation, not just final memory (CompCert behaviors).
- **External / not-yet-verified functions (and syscalls) via a pre/post + frame spec interface**
  (CompCert `external_call`) — the bootstrap boundary, and the same interface `.call` already uses.
- **ABI and ISA are *parameters*** (CakeML retargeting) — the calling convention (callee-saved set, `sp`,
  `ra`) is a parameter to the frame pass; the encoder/ISA a parameter to the last pass. Not baked in.
- **Verify the encoder to actual bytes** (CakeML) — the bytes are the deliverable; this is the TCB point.
- The **clocked functional big-step** semantics is the validated style (CakeML/Owens); `exec_mono` is the
  known one-time cost. Already in place.

Pass pipeline (`from→to` / job / `match_states` / template / difficulty):

| # | from → to | job | match_states | template | difficulty |
|---|---|---|---|---|---|
| 1 | Ctrl → Ctrl | normalize/desugar (`seqs`/`block_`, flatten) | ≈ identity | — | trivial |
| 2 | Ctrl → CFG | structured control (`while/block/brkB/contL/ret`) → basic blocks + (cond) branches + labels; `.call` → call node | Ctrl outcome/continuation ↔ current-block + pc | CompCert RTLgen | **hard** — factor: (2a) eliminate `block/brk/cont`; (2b) `while/ret/call` → CFG |
| 3 | CFG(∞ regs) → CFG(32 phys + spills) | register allocation + spilling | virtual-reg state ↔ phys-reg + spill-memory, via the allocation map | CompCert RTL→LTL→Linear | **hard** — copy CompCert **translation validation**: untrusted allocator + *verified checker* |
| 4 | → stack IR | ABI frame: prologue/epilogue (save `ra` + callee-saved used), caller-save spills, `sp` arithmetic | abstract-call state ↔ machine state with concrete frame; invariant "callee-saved + `ra` restored on return, frame ⊥ program data" | CompCert Stacking; CakeML `stackLang` | mechanical (ABI = param) |
| 5 | stack IR → linear asm | linearize blocks; resolve labels → PC offsets | block + pc ↔ instruction index | CompCert Mach→Asm; CakeML `labLang` | mechanical |
| 6 | asm → bytes | encode (the 16 RV64I encodings) | `fetch/decode(bytes) = instr` | CakeML encoder; project `encode` | mechanical, **must-do** (TCB point) |

Cross-cutting: shared `mem` + borrow model across passes 1–4 (passes 3–4 add stack regions to the *same*
`mem`); traces threaded through all; external-call specs at every level; ABI param at pass 4, ISA/encoder
param at pass 6. The stack becomes *explicit* exactly at pass 4 — the convention-establishing lowering
(matching CakeML's `stackLang`), and that frame also holds the `alloca`-style address-taken locals (Ext. 1).

**Feasibility.** Mechanical / well-templated: passes 1, 4, 5, 6. The two **hard** passes are CompCert's
hard passes too — done before, but real work:

- **Pass 2 (control-flow lowering)** is the highest single risk *here*, because `Ctrl`'s non-local control
  (`block/brk/cont/ret` + `call`) is richer than a plain while-language — and it's the very feature that
  *simplified* the functional proofs (D3), so the complexity reappears here. Mitigation: factor into 2a/2b.
- **Pass 3 (register allocation)** — don't verify the allocator algorithm; verify a *validator* that a
  given allocation is correct (CompCert's translation-validation trick). Big factoring win.

**Bootstrap shortcut (the key feasibility lever).** Because we control the source and libc functions are
small, first prove `compile_sim` for a **restricted fragment**: structured control only (no `block/brk/cont`;
`ret` at tail or removed by 2a), leaf-or-inlined calls, ≤31 live registers (no spilling). That collapses
pass 2 to near-trivial and *removes* pass 3 entirely — giving an end-to-end-to-bytes result for
`hex0`/`strlen` early, which you then generalize one fragment-feature at a time.

**Verdict: doable.** It's the CompCert/CakeML recipe, and both hard passes have verified precedents. The
factoring that makes it tractable for a small effort is exactly: split pass 2 into 2a/2b, translation-
validate pass 3, and start from the restricted fragment. The residual research-grade risk is concentrated
in pass 2 — worth a paper-design spike before committing.

## 5. The architecture in one line

Separation does **not** live in the memory model (no block structure); it lives in the **type system /
function contracts** at the higher IRs and is threaded down as data + proofs, bottoming out as `Wf`/`Disjoint`
hypotheses on flat-memory functional theorems. Keep LowIR flat and machine-faithful; pay for the IL→RV64I
compiler once; let the (future) borrow type system *produce* the disjointness that LowIR proofs assume.
