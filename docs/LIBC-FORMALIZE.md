# Formalizing & verifying libc — exploration and plan

Goal: a libc that **compiles with a normal C compiler** *and* has **parts formally
proven correct**. This doc surveys the available substrate (the `third-party/` stack)
and lays out a path. It is the libc analogue of the hex0/hex1 work: a spec proved
faithful to an external standard, connected by refinement to an executable model —
extended from "bytes on RISC-V" up to "C source against POSIX".

Status: **exploration + architecture decision** (no proofs written yet).

---

## 1. What we already have in-repo

- **`third-party/fv-libc/libc_functions.csv`** — every public musl function (1477)
  classified into verification partitions with header, source, deps, and the
  transitive syscall set. This is the **work-breakdown structure** for any libc
  effort. Counts: `pure 431 · math 280 · alloc 9 · sys 456 · io 157 ·
  pthread_core 77 · pthread_sys 67`.
- **The hex0/hex1 method** (`lean/`, `coq/`, `docs/TCB.md`) — a proven template:
  a spec proved equivalent to a *published grammar*, refined by a fuel-bounded
  simulation down to the *actual executed RISC-V bytes*, with an explicit
  enumerated TCB and minimal axioms. The libc plan should preserve this ethos
  (small TCB, refinement to real bytes).

> **Proof-assistant policy (2026-06-16):** new development is **Lean-only**. Coq is
> kept as a *reference* (definitions, proof directions, intermediate lemmas) — we do
> not write/maintain new Coq. The hex0/hex1 "mirrored Lean **and** Coq" signature
> does **not** carry forward. This rules out any route whose only kernel-checked
> discharge path is Coq export (notably Frama-C/WP → Coq).

The natural **beachhead is the `pure` partition** (431 fns: `string.h`,
memory ops, `ctype`, broken-down-time math, `setjmp`): no syscalls, no allocator,
no global state — *memory-in, value/memory-out*. Spec-simple, implementation-tricky.

---

## 2. The substrate (third-party survey)

### CompCert — *reference only* (C semantics + IL inspiration)
Per steer: **not a stack we build on**, a reference for how to model C.
- IL pipeline: **Clight** → Csharpminor → Cminor → CminorSel → RTL → LTL →
  Linear → Mach → Asm. **Clight** (`cfrontend/Clight.v`) is the right altitude
  for stating C-function correctness (C-level, typed, explicit memory ops).
- Memory model (`common/Memory.v`): block/offset, `Vptr block ofs`, permissions
  (Cur/Max × Read/Write/Free), `load/store/alloc/free`. Provenance = abstract
  block ids. This block-offset model is the standard, C-appropriate base.
- Reusable as *design templates*: `lib/Integers.v` (machine ints, fully proved),
  `common/Values.v`, `common/Memdata.v` (byte encode/decode), `cfrontend/Cop.v`
  (operator/cast semantics), `cfrontend/Ctypes.v` (layout/`sizeof`/alignment).
- CompCert itself is **compiler-correctness only** — no functional-spec logic,
  and **VST is not bundled**. It has a riscV backend (`riscV/`) but that's not
  our concern here.

### Frama-C — the only tool that verifies *real C source* directly
- **ACSL** function contracts: `requires`/`ensures`/`assigns`/`\separated`/
  `\old`, behaviors, loop invariants, logic predicates + axioms.
- **Ships a ready-made spec layer for our beachhead.** `share/libc/string.h`
  carries full ACSL contracts for `memcpy, memmove, memset, memcmp, memchr,
  mempcpy, strlen, strnlen, strcmp, strncmp, strchr, strstr, strtok, strsep, …`
  with an axiomatic foundation in `share/libc/__fc_string_axiomatic.h`
  (`strlen{L}`, `memcmp{L1,L2}`, `strchr{L}` as logic functions + axioms).
  This is a **free, expert-written formal spec** for ~all pure string/mem fns —
  but Frama-C provides **specs only, no implementation proofs**.
- **WP plugin** (`src/plugins/wp/`): weakest-precondition VC-gen, memory models
  Hoare / **Typed** (default; pointers as (base,offset)) / **Bytes** (byte array,
  for type-punning, slow). Discharges via **Why3 → Alt-Ergo/Z3/CVC5** (SMT) **or
  exports to Coq** (`share/coqwp/Memory.v` etc.).
- **TCB knob:** SMT route = fast but trusts Why3 + the SMT solver + WP's VC-gen
  + ACSL axioms. Coq-export route = kernel-checked obligations (much smaller TCB),
  more labor.
- **Hard limit:** **no inline asm**, and musl's `may_alias`/word-at-a-time/
  pointer-cast tricks stress the memory model (Bytes model needed, slow). → points
  at *clean verifiable C* rather than musl-as-written for the implementation.

### CakeML / Pancake — verified compile-to-RISC-V, but ML/HOL4, not C
- **Pancake** (`pancake/`): a C-*like* imperative language (vars, while, load/store,
  structs, FFI) with formal HOL4 semantics and a **verified compiler to riscv64**,
  plus **Characteristic Formulae** separation logic (`characteristic/`) for proofs.
  End-to-end "verified program + verified compiler → machine code" is real here.
- Mismatch: Pancake is **not C** (won't satisfy "compiles with a C compiler"
  without a C twin), and the ecosystem is **HOL4**, not this repo's Lean+Coq.
  Best treated as a model for the *verified-compilation* methodology, and a
  fallback if we want verified lowering without building our own.

### Tree Borrows (PLDI'25) — inspiration, not substrate
- A **Rust** aliasing model (provenance-as-tag over a CompCert-style block memory;
  per-location Reserved/Unique/Frozen/Disabled state machine). Its rules encode
  Rust's mutable-xor-shared discipline, which **C does not have** — C pointers map
  to its inert "raw pointer" case. So the model can't be lifted to C.
- What *does* transfer: the **provenance-as-tag** idea and block/offset memory
  (better taken from CompCert/Cerberus, already C-mature), and it explicitly
  **proposes itself as a basis for formalizing C `restrict`** — relevant later for
  the `restrict`-annotated functions (memcpy). Mechanized in Rocq (~32k LOC,
  Iris/Simuliris) but as an *optimization-soundness* logic, not a reusable C model.
- It signposts the right **C-provenance** literature for our memory model:
  **Cerberus/PNVI** (Memarian et al.), **Krebbers' C-in-Coq**.

### POSIX spec (`third-party/posix-spec`) — the spec source of truth
- IEEE 1003.1-2024, full HTML: per-function pages with a **consistent, mechanically
  extractable** structure (NAME/SYNOPSIS/DESCRIPTION/RETURN VALUE/ERRORS via
  `<h4 class="mansect">` + `<blockquote>`). 100% coverage of the pure string/mem
  targets. A spec-skeleton extractor is straightforward.
- Caveat: POSIX prose **defers low-level semantics to ISO C** and leaves UB cases
  open (`memcpy` overlap = UB; `strlen` assumes a valid NUL-terminated string).
  So POSIX gives the *shape*; the formal pre/postconditions get pinned down by us
  (and cross-checked against Frama-C's ACSL, which already made these choices).

---

## 3. The design space (how to actually verify a libc function)

Every route shares the same two halves: a **formal spec** (POSIX-derived, cross-checked
against Frama-C ACSL) and an **executable model of the implementation** they're proved
to agree on. They differ in *what models the implementation* and *what's in the TCB*.

| Route | Implementation modelled as | Proof engine | TCB | "Compiles w/ C compiler?" | Fit w/ repo |
|---|---|---|---|---|---|
| **A. Frama-C/WP (SMT)** | real C source | WP + SMT | WP VC-gen + Why3 + SMT + ACSL | ✅ the C *is* the artifact | new tool |
| **B. Frama-C/WP (→Coq)** | real C source | WP, VCs discharged in Coq | WP VC-gen + Coq kernel | ✅ | ✗ **excluded** — Coq dev |
| **C. Custom Lean refinement** | a small **verifiable-C** subset w/ our own mechanized semantics | Lean, hex0-style simulation | Lean kernel + our C-semantics faithfulness | ✅ (subset is real C) | **native** |
| **D. Pancake + CF** | Pancake program (C-like) | HOL4 / CF | HOL4 kernel + CakeML compiler (verified) | ⚠️ needs a C twin | HOL4, not Lean |

Per the Lean-only policy, **B is out** (its kernel-checked path is Coq), and **D**
(HOL4) is a non-native fallback. The live choices are **A** (breadth, SMT TCB) and
**C** (foundational, Lean kernel) — or an **A+C hybrid**.

Two further axes cut across all routes:

- **Source posture** — verify **musl as-written** (clever `may_alias`/word-at-a-time/
  inline-asm code: hostile to *every* foundational tool, marginal even for WP) vs
  write **clean-room verifiable C** (plain byte loops; compiles fine with gcc/clang;
  tractable to prove; the deliverable is *our* libc, proven). The clever code is a
  performance optimization, not a correctness requirement.
- **Proof depth** — stop at **C-level functional correctness** (A/B/C/D all do this)
  vs carry the proof **down to the compiled RISC-V bytes** (the hex0/hex1 signature:
  reuse `Rv64i` + the `riscv-coq` cross-check). The latter is the full-stack TCB
  story but multiplies the work per function.

---

## 4. Recommended shape (pending your decisions in §5)

Default recommendation, optimizing for *consistency with the existing foundational
work* while staying pragmatic:

1. **Beachhead = the `pure` string/mem subset** (~30 flagship fns: `memcpy memmove
   memset memcmp memchr strlen strnlen strcmp strncmp strcpy strncpy strchr strrchr
   strcat strncat strspn strcspn strpbrk strstr`).
2. **Spec layer:** mechanically extract POSIX skeletons → formalize as Lean/Coq
   predicates; cross-check the pre/postconditions against Frama-C's bundled ACSL.
3. **Source:** write **clean-room verifiable C** for each (compiles with gcc/clang,
   lands in a small analyzable subset) — *not* musl's optimized bodies.
4. **Two complementary proof tracks**, so we get both breadth and a small-TCB flagship:
   - **Track A (breadth, fast):** Frama-C/WP over the clean C against the ACSL specs,
     SMT-discharged — covers many functions cheaply, validates the spec choices.
   - **Track C (depth, foundational):** a minimal **MiniC** operational semantics in
     **Lean**, and a hex0-style refinement proof that each flagship implementation
     meets its POSIX spec — kernel-checked, our signature. (Coq's CompCert `Clight`/
     `Memory`/`Integers` consulted as *design references* for the semantics, not ported.)
5. **Memory model:** CompCert/Cerberus-style block+offset with provenance; Tree
   Borrows held in reserve for a future `restrict` formalization.
6. **Later:** extend Track C down to the compiled RISC-V bytes for full-stack TCB;
   then climb the partition ladder (`alloc` → `io` → `sys`), each new partition
   adding exactly one assumption (allocator → stream model → ecall/MMIO axiom).

---

## 5. Open decisions (for the user)

See the questions posed alongside this doc. The three load-bearing forks:
1. **Primary proof stack / trust posture** — foundational custom **Lean** (route C)
   vs Frama-C/WP-SMT (A); or the A+C hybrid. (B excluded by Lean-only; D is HOL4.)
2. **Source posture** — clean-room verifiable C vs verify musl as-written.
3. **Proof depth** — C-level functional correctness vs carry down to RISC-V bytes.

(Once chosen, §4 is rewritten as a concrete milestone plan with first targets.)

---

## 6. Verified compilation — the IL-altitude finding + a working prototype

Driving question (user): *what is the most straightforward way to prove software that
gets compiled to native code?* Approach: (1) survey the ILs of CakeML, CompCert,
Frama-C; (2) re-express a tiny program in a **new IL** with verifiable compilation to
RISC-V; (3/4) climb toward an IL that is easy to verify *and* translatable to C.

### The finding (CakeML + CompCert IL surveys agree)

There is a sharp **structured → flat boundary** in every compiler stack, and it is
exactly where proof difficulty changes regime:

| Altitude | Examples | Control flow | How you prove a program | Cost |
|---|---|---|---|---|
| **Structured** | CompCert **Cminor**; CakeML **wordLang/stackLang**; Pancake **crep/loopLang** | `Seq`/`If`/`While`, **no PC** | **structural induction** on the program / big-step eval | **easy** |
| **Flat** | CompCert RTL→LTL→Mach→Linear→**Asm**; CakeML **labLang**; this repo's **`Rv64i`** | program counter / CFG nodes + label lookup | **per-instruction PC-simulation** matching each decoded step | **hard** |

- CompCert's RISC-V `Asm.v` is a flat PC machine — *the same shape* as this repo's
  hand-rolled `Rv64i` (PC register, fetch, branch-offset targets). So our existing
  model already sits at the hard altitude — which is why `RawAsm/Hex0/Refine.lean` is ~3400
  lines, almost all the loop-simulation lemma.
- **Sweet spot = Cminor altitude:** structured statements + big-step semantics, yet
  three-address and close to the machine. CakeML's lowest *still-structured* IL is
  stackLang; Pancake's loopLang is the post-allocation equivalent.
- The flat-PC simulation cost doesn't vanish — it moves into the **verified compiler
  pass** (proved once: e.g. CompCert `RTLgenproof`, CakeML `stack_to_lab`), and is
  then reused by every program. That is the leverage.

### The prototype: `lean/LowIR.lean` (builds green, Lean-only)

A new IL at the sweet-spot altitude, with a verified-compilation path to the repo's
trusted RV64I model:

- **`LowIR.Stmt`** — three-address ops (`addi add sub orr slli srli lbu sb`, mapping
  1:1 to RV64I) with **structured** control (`ife`, `while`); no PC. Big-step clocked
  semantics `exec : Nat → Stmt → St → Option St` — executable and proved by structural
  induction.
- **`compile : Stmt → List Rv64i.Instr`** — lowers `ife`/`while` to the **exact 16-instr
  trusted surface** (the four branches `beq/blt/bge/bgeu` + `jal`; the excluded
  `bne`/`bltu` are avoided by branch-target swapping). The flat-PC burden lives here.
- **`encode : Instr → BitVec 32`** — the byte-exact inverse of the trusted
  `Rv64i.decode`; assembled to little-endian bytes and run on the genuine `Rv64i.step`.
- **Demonstrated on a real libc function — `strlen`** — written in `LowIR`, and
  machine-checked (`native_decide`, certification-grade):
  - `strlen_roundtrip` — every emitted instruction decodes back to itself.
  - `strlen_rv_abc/_hello/_empty` — compiled `strlen`, executed as bytes by `Rv64i.step`,
    returns 3 / 5 / 0. End-to-end: structured IL → RISC-V bytes → trusted machine.
- **T1 — compiler correctness (stated; proof deferred).** `lean/LowIR.lean` defines
  the forward-simulation relation (`Layout`/`Installed`/`Agree`/`NoSelfModify`) and the
  theorem `compile_sim`: `exec` of any program ⇒ the trusted machine runs the compiled
  bytes to the fall-through PC in an agreeing state. Proof is `sorry` for now (sanctioned)
  — once proved (by structural induction, *once*), it amortises the `Refine.lean` cost
  for every program.
- **T2 — `strlen` proved correct, sorry-free** (`lean/LowIR/Strlen/CoreProof.lean`):
  `strlen_correct` shows `strlen` computes the first-NUL offset for **all** strings, by a
  `while`-invariant + induction on the distance to the NUL — no PC, no decode, no offsets
  (core Lean only: `simp`/`omega`/`bv_omega`/`decide`). This is the concrete demonstration
  that program proofs are *easy* at the structured altitude. `T1 ∘ T2` will transport it to
  the real RV64I bytes.
- **In progress:** hex0 functional correctness at the IL level (`hex0` ≡ `coreSpec`), the
  larger analogue of `strlen_correct` (two-state machine, comment-skip inner loop, capacity).

### Roadmap up the abstraction ladder (steps 3–4)

1. **Now:** prove **T1** (LowIR → RV64I forward simulation) once. This is the rung that
   makes every subsequent program proof cheap, and the analogue of CompCert's
   `Asmgenproof` / CakeML's `stack_to_lab` — but small, Lean-only, against our `Rv64i`.
2. **Climb:** add a structured layer *above* LowIR with locals/expressions/typed
   memory (Cminor-altitude) and a verified LowIR-targeting pass — so programs are
   written and proved even more abstractly.
3. **Toward C:** define a small **verifiable-C subset** whose semantics matches the
   structured IL, with a (verified or validated) C→IL front. Then a clean libc function
   is: written once in the C subset (compiles with gcc/clang), proved at the structured
   altitude, and carried to RISC-V bytes by the verified pipeline. This is where the
   libc plan (§4) and the IL track converge.

