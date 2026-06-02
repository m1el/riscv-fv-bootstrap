# Verified Tower — Project Handoff

A context-transfer document. The goal: build a **bottom-up formally verified
toolchain tower**, verified in **Lean**, bottoming out in a formal ISA model,
producing a **native binary that runs bare-metal** (no OS). This README captures
the design decisions and reasoning so a fresh session can continue without
re-deriving them.

---

## 1. The overall goal

Build levels of abstraction, each with its own formal semantics in Lean and a
**per-pass refinement/simulation proof** to the level below, composing into an
end-to-end correctness theorem.

Planned tower (bottom to top):

```
hex0  (text hex -> bytes)            <-- START HERE (scaffolding, not a real component)
  |
verified assembler                   <-- first real component (encoder + relocation)
  |
typed IR (references, slices, types instead of raw pointers)
  |
small C  /  smaller Rust
```

The architectural template is **CakeML** (HOL4): many small intermediate
languages, each with operational semantics, each lowering proved to preserve
behaviour, composed into one end-to-end theorem. We are NOT translating CakeML's
HOL4 proofs — we reuse the **design/methodology**, build natively in Lean.

Relevant external reference points:
- **CakeML** — IL-stack architecture, FFI oracle boundary, in-logic bootstrap.
- **CompCert** — memory model / provenance design (the *model* is the reusable
  part, not the Coq proofs). Draws an explicit trusted boundary at its parser
  and assembler/linker.
- **L3 / Sail** — ISA specification languages. CakeML uses L3. We want a
  **Sail-derived or hand-written RISC-V model in Lean**. Prefer reuse over
  hand-rolling to keep the trusted base small.
- **stage0 / GNU Mes / live-bootstrap / Guix full-source bootstrap** — the
  hex0 -> asm -> M2-Planet -> mescc -> tcc -> gcc chain. Inspiration for the
  lower rungs. Note: proofs are tractable only up through *small-C*; TCC and
  especially GCC were never built to have a semantics — the verified world goes
  *around* GCC (that's what CompCert is), not through it.

---

## 2. Key design decisions already made

### 2.1 Target ISA: RISC-V (lean toward RV32I/RV64I base)
Fixed-width, orthogonal, clean decode, best Lean-side model momentum. x86-64's
variable-length encoding would eat the schedule before reaching interesting
layers. **Open task:** survey what RISC-V-in-Lean models exist and whether they
provide a Hoare/program-logic layer over the bare `step` relation, or only raw
operational semantics. If only raw `step`, building a program logic over it is
*step zero* for the assembly-first regime.

### 2.2 Two verification regimes (pick deliberately per component)
- **Regime 1 — assembler is a Lean function.** Implementation structs (`Token`,
  `Hole`, `Label`, `ByteVec`) become Lean `structure`s; field access/meaning is
  supplied by Lean's type theory for free. Cheap. Compile to native via Lean's
  normal Lean->C->native path; that toolchain is **unverified TCB**. Good for a
  fast running v1; *not* end-to-end.
- **Regime 2 — verified artifact IS the machine code.** No structs at runtime,
  just registers + flat byte memory. Each implementation struct needs a
  **representation predicate** (separation-logic-style) relating bytes-at-address
  to the abstract record. Needs a program logic over the ISA model. This is the
  end-to-end regime and the only one that achieves "native verified binary, no
  big compiler in TCB."

**Recommended path:** start Regime 1 to get plumbing + a running tool, migrate
toward Regime 2 (self-hosting bootstrap) for the parts where end-to-end matters.
Structure the repo so the bootstrap is *possible later*: make the pure
`bytes -> bytes` core the thing every layer agrees on.

### 2.3 The "pure slice" discipline (central cost-control lever)
Every verified core is a pure function: **input slice in, output slice out,
scratch slice provided by caller.** No malloc, no growable buffers, no
pointer-linked structures, no global state. Reasons:
- Bans exactly the constructs (heap alloc, growth, aliasing) that make
  representation predicates expensive (freshness/disjointness obligations).
- Flat fixed-size records in a caller-provided slice become **decidable indexing
  arithmetic**, not heap reasoning.
- Output sizing: use a **sizing pass** (the two-pass structure makes this
  natural) — pass 0 computes total output size, caller provides that slice,
  later passes fill it. Cleaner than realloc loops.

### 2.4 Where the trusted/proven boundary sits
- Parsing/lexing of *text* can be **pushed up** the tower (verified in the
  smallest tower language) rather than verified as raw machine code at the base.
  The **encoder must** be at the base (everything compiles to it); the parser
  need not be.
- Draw an explicit, written-down TCB list at the boundary, CompCert-style.

### 2.5 Lookup tables: prefer static data + finite check
For instruction-mnemonic lookup, do NOT verify a runtime-built hash table
(verifying *construction* is the expensive half). Two good options:
- **Precomputed perfect hash baked as static data:** table-contents correctness
  becomes a finite `decide`/`native_decide` injectivity check. BUT you still must
  (a) prove the executed asm hash == the spec hash (keep them the SAME Lean
  definition; generate the table from it), and (b) prove **soundness on
  non-keys** — a perfect hash sends garbage input to *some* valid slot, so the
  probe must do a confirming compare and you must prove misspelled mnemonics
  return INVALID. The not-found case is the half people forget.
- **Static sorted table + verified binary search** (RECOMMENDED): same O(log n)
  probe, no separate hash function to verify, and not-found soundness falls out
  of the search invariant. Likely *less* total proof effort. Runtime constant
  factors are irrelevant for once-per-line mnemonic lookup.

General principle: **move structure construction to compile time so runtime
verification reduces to "probe a constant correctly."**

### 2.6 Struct modeling (clarification of a confusion)
Two unrelated meanings of "struct":
- **Layout-only** (assembler/data-definition level): struct = recipe to place
  bytes. Need a total `layout : Decl -> (offsets, size, alignment)` and prove
  injectivity/non-overlap. Cheap, same flavor as the encoder.
- **Value-level** (typed IR and up): struct = typed value with a memory rep.
  This is where the **memory model** enters the tower — read-field / take-address
  -of-field is the operation that turns a typed value into an offset into raw
  memory. This is the hardest refinement in the stack. Define layout ONCE and
  have both the assembler's emit and the IR's semantics refer to the SAME
  `layout` function. Make things **defined** where C left them unspecified
  (defined-zero padding, fixed alignment, a deliberately chosen provenance rule
  e.g. field pointers inherit parent allocation provenance) — each deletes a
  category of proof obligation.

### 2.7 Implementation structs (the literal "tell Lean what the structs are")
- Regime 1: one-line `structure` per type, meaning free.
- Regime 2: one **representation predicate** per *distinct fixed layout*. For the
  descoped v1 this is ~2 predicates (a `ByteVec`-as-slice predicate, and a
  fixed-layout record-array predicate for the holes/labels arrays). The scary
  structs (`Token`, the hash table) live in layers kept out of the machine-code
  base. Phrase to use: **"representation predicate"**, not "struct semantics".

### 2.8 C preprocessor — keep OUT of the verified core
C-the-language has multiple formal semantics (CompCert/Clight, Krebbers' C11,
K-framework, Cerberus) but they all start at translation phase 7
(post-preprocessing). The **C preprocessor has no mechanized formal semantics** —
only operational tooling treatments (SuperC by Gazzillo & Grimm is the one to
read; TypeChef too). Rescanning + "blue paint" self-reference suppression + `##`
paste + `#` stringize form an underspecified text-rewriting fixpoint that real
preprocessors disagree on. **Decision:** do not put textual preprocessing in the
trusted core. Either keep it upstream of the theorem (untrusted front-end, like
CompCert calling external cpp) or design a **hygienic AST-level macro system**
that *has* a semantics. We are not obligated to inherit cpp's 1970s text-hack
design.

---

## 3. Lexer/tokenizer verifiability (resolved discussion)

The existing `token.c` (from the holey-toys `hbas` assembler — see section 5) is
a **single-pass, monotone-advancing, bounded, no-backtracking** scanner that
dispatches on first char. This class of lexer is **verify-EASY**, contrary to a
too-broad early warning. What makes lexers *hard* in general — backtracking,
generated transition tables, regex-derivatives, lexer/parser feedback — is
ABSENT here.

The real residual cost is **authoring the spec**, not discharging the proof: a
lexer encodes silent conventions (maximal munch, identifier alphabet via the
`& ~0x20` upcasing trick, "bad digit terminates vs poisons", `ndata` =
decoded-length-not-span). Each is one line of spec you must write and then show
the code meets. The ONE part with real mathematical content is
`token_number`: prove it computes the value sum(digit_i * base^i) AND reports
overflow **exactly** when that value >= 2^64. Its overflow predicate uses
`pre_overflow = UINT64_MAX / base` plus a wraparound check `next < rv`; prove
that test is neither too strict nor too lax. Use uniform u64 in the spec (the C
`size_t` for `pre_overflow` is a C-ism / noise). Single source of truth for
char-class predicates so lexer's notion of identifier == parser's.

---

## 4. Bare-metal I/O model (resolved)

Running the binary as a QEMU `-kernel` with no OS is the CLEANEST setting and
*narrows* the TCB vs hosted.

- With an OS you'd model syscalls as an FFI **oracle** (CakeML style) — a wide
  trusted surface (kernel, libc, ABI).
- Bare-metal: "I/O" becomes **loads/stores to distinguished addresses** —
  absorbed into the same `step` relation you already trust. Strict TCB reduction.

**For a batch transformer like an assembler, use the simplest model:**
preload input into a known memory region, run `step` to halt, **output is the
bytes in a designated output region of the halted state.** Then I/O is not even
an effect — the top-level theorem is a pure relation between initial and final
memory: "if input region holds `inp`, halted state's output region holds
`spec(inp)`." No oracle, no MMIO, no streaming.

(Only reach for MMIO/streaming — UART RX/TX as state-advancing `step` cases — if
a later component must react to input it hasn't seen yet. The assembler does not.)

**Architecture:** thin **trusted I/O shell** (bare-metal asm: set up stack,
locate preloaded input at known address, call core with
`(in_ptr, in_len, out_ptr, scratch_ptr)`, signal output length, halt) + **pure
verified core** operating only on the slices it's handed. Prove the core; trust
the shell. The buffer is the interface between trusted shell and proven core —
"read into a buffer, reason about the small part" is exactly right.

**Explicit TCB to write down:** (1) QEMU loaded input faithfully into the region,
(2) shell passed correct addresses/length, (3) halt observed correctly. Decide
deliberately: the **shell provides `(ptr, len)`**; prove the core correct for ALL
`len`. Do NOT bake sentinel-scanning for length into the proven core.

CakeML note: its *semantics* is OS-agnostic (FFI oracle) but its *usual*
deployment is hosted via trusted glue. It HAS gone freestanding (Silver verified
processor; Pancake systems language). Our setting is the freestanding
instantiation, in an even simpler batch-only form than CakeML's general FFI.

---

## 5. Source material

The starting code is from `m1el/holey-toys` (the user's own repo; MIT,
"Igor null"), an assembler `hbas` for the **holey-bytes VM** — a bytecode VM with
fixed-shape instructions (opcode byte + operands laid out by a `type_str`
descriptor). NO variable-length encoding, NO branch relaxation — a big
simplification vs real ISAs. Files reviewed: `src/hbas.c`, `src/token.c`.

Key structures in `hbas.c`: `Token`, `Hole` (forward ref / relocation),
`Label`, `HoleVec`/`LabelVec`, `ByteVec` (growable buffer). `assemble()` does a
main pass (tokenize, collect labels, emit instructions, record holes) then a
second pass patching holes from the label table. `assemble_instr()` +
`push_int_le()` are the pure encoder core. `build_lookup()` builds a hash table
(the thing to replace with static data — see 2.5).

---

## 6. CONCRETE NEXT STEP — hex0

hex0 is **scaffolding, not a real component** (it's ~the "hello world" of the
verification stack). Its value: debug the methodology (Lean ISA model,
representation predicates, machine-code reasoning, I/O shell boundary,
refinement theorem) on a problem where the spec is unarguable, AND it's the one
rung small enough to BOTH hand-audit AND fully prove — the single point where the
"tiny seed" trust axis and the "proof" trust axis can be exhibited meeting.

**Write the proof plumbing over-engineered** (caller-provided output slice with
proven bound, arbitrary-length input) even though hex0 barely needs it — the
point is reusable plumbing cut to the shape the *assembler's* proof will need.

### 6.1 Candidate C (`unhex`) — HAS BUGS, fix before using as reference

The user's candidate `unhex` (parse `#`-comments, skip non-hex in high position,
require hex in low position, emit `(high<<4)|low`) has issues found by scrutiny:

- **BUG 1 (rejects all input, off-by-one):** after reading high nibble `in_idx`
  already points at the low nibble; the check `if (in_idx + 1 >= in_len) return
  ErrTrailingNibble;` is wrong. For `"AB"` (len 2): high at idx0, idx->1, then
  `1+1>=2` true -> error, though `B` is right there. **Fix:** `if (in_idx >=
  in_len) return ErrTrailingNibble;`
- **BUG 2 (in-band sentinel, unsound in principle):** `parse_nibble` smuggles
  `ErrBadNibble` through a `char` return, detected by `(uint8_t)x ==
  ErrBadNibble`. Works only if `ErrBadNibble & 0xff >= 16`. **Fix for spec:**
  return `Option (Fin 16)`, no in-band sentinel.
- **Spec ambiguity — `#` only starts a comment in HIGH-nibble position.** A `#`
  where a low nibble is expected -> `ErrSplitNibble`, not a comment. Likely
  intended (comments only on byte boundaries) but must be stated. (stage0 hex0
  conventionally treats `#`/`;` comments as skippable anywhere — differs.)
- **Spec ambiguity — whitespace** is skipped only in high position (via
  bad-nibble `continue`); in low position any non-hex (incl. space) is
  `ErrSplitNibble`. So `"A B"` errors, `"AB CD"` is fine. State it.
- **Edge cases to enumerate in spec:** empty input; lone high nibble at EOF
  (-> ErrTrailingNibble = "odd nibble count"); high + bad low; comment-at-EOF
  (no newline); output buffer exactly full; partial-output-on-error semantics
  (decide whether output on error is observable).

### 6.2 The spec to write FIRST (the refinement target)

hex0 is a **two-state machine**. Writing it this way forces every ambiguity above
to be an explicit transition.

```
nibble : Byte -> Option (Fin 16)
  '0'..'9' -> some (c - '0')
  'A'..'F' -> some (c - 'A' + 10)     -- decide: also accept 'a'..'f'? (C doesn't here)
  else     -> none

decode : List Byte -> Sum Error (List Byte)
  state EXPECT_HIGH:
    '#'            -> skip to '\n' (or end), stay EXPECT_HIGH
    nibble d       -> remember d, go EXPECT_LOW
    else           -> skip, stay EXPECT_HIGH        -- whitespace/junk skipped
  state EXPECT_LOW:
    nibble e       -> emit (d<<4 | e), go EXPECT_HIGH
    else (incl '#', ws, EOF) -> Error (ErrSplitNibble)
  at EOF in EXPECT_LOW  -> Error ErrTrailingNibble
  at EOF in EXPECT_HIGH -> Ok
```

The C inlines the EXPECT_LOW state; making it explicit in the spec is what lets
the correspondence proof close cleanly.

### 6.3 hex0 task checklist
- [ ] Decide ISA (RV32I likely) and obtain/identify a Lean ISA model; check for a
      program-logic layer over `step`.
- [ ] Write `nibble` + `decode` Lean spec (section 6.2). Decide lowercase accept,
      `#`-anywhere vs boundary-only, partial-output-on-error.
- [ ] Define the bare-metal machine state + halt condition + input/output region
      convention (section 4).
- [ ] Define representation predicate(s): input slice, output slice w/ bound
      (over-engineer per 6.1 intro).
- [ ] Implement hex0 (fixed BUG 1 + BUG 2) either as Lean function (Regime 1) or
      machine code (Regime 2 — needs the program logic).
- [ ] Prove refinement: executed thing computes `decode` on the input region;
      output region holds the result; bound respected.
- [ ] Write down the explicit TCB list (the 3 items in section 4).
- [ ] Write the thin trusted asm shell + run under QEMU `-kernel` as smoke test.

---

## 7. The "how far up the tower" honest frontier
- hex0, assembler, small-C: genuine machine-code-grounded proofs on a fixed ISA
  are PLAUSIBLE. This IS the tower being designed (hex0 as bottom rung instead of
  a hand-written encoder; typed-IR/small-Rust as the verified analogue of
  M2-Planet/mescc).
- TCC, GCC: out of reach — never built to have a semantics. Verified world goes
  *around* GCC (CompCert), not through it. Mark this as an explicit
  theorem-boundary: "proven below, audited-but-unproven above."
- The genuinely NEW research bit: connect the **tiny-auditable-seed** trust axis
  (read 357 bytes) to the **proof** trust axis at a single point — prove the
  hand-auditable hex0 seed *implements* the bottom of the verified tower. Nobody
  has built this fusion.