# Memory borrows — separation discipline for the libc specs

Status: design note. Applies to all LowIR libc function specs (hex0, strtoull, …).

## The problem

LowIR memory is a single flat map `mem : Word → Byte`. The moment a function both
mutates memory and reads/writes caller-provided pointers, its postcondition is only
true under **non-aliasing** preconditions. Two instances already live in this repo:

- **hex0**: reads the input region `[inBase, inBase+len)` and writes the output region
  `[outBase, outBase+cap)`. The spec `Hex0.coreSpec` is a pure function of the input
  *list*; for the IL to match it, an output write must never perturb an input byte the
  parser has not yet read — i.e. input and output regions must be disjoint.
- **errno** (conformant `strtoull`, deferred): a global the function writes; must be
  disjoint from the caller's buffers, and `strtoull` also writing `*endptr` needs
  `endptr ≠ &errno`.

## The discipline: Tree-Borrows-style borrows (see `third-party/2025-pldi-treeborrows.pdf`)

We phrase each function's memory contract in **borrow** vocabulary:

- **shared borrow** (`&[u8]`, e.g. the input `nptr`/`input`): read-only; the bytes are
  stable for its lifetime; *may overlap other shared borrows* (two readers of the same
  `const char *` is fine).
- **unique borrow** (`&mut [u8]`, e.g. the output buffer, or `errno`): exclusive; must be
  disjoint from **every** other live borrow (shared or unique).

`hex0 : (input : &[u8]) → (out : &mut [u8]) → Status`. From "`out` is unique" the
disjointness `Disjoint input out` is a *theorem about borrow well-formedness*, not an
ad-hoc hypothesis. `errno` is a libc-held unique borrow, disjoint from caller borrows by
the same rule; `sprintf(&errno, …)` is illegal precisely because it would need a second
unique borrow overlapping libc's → two overlapping uniques → ill-formed.

Tree Borrows (vs Stacked Borrows / raw disjointness) is the right justification because a
libc needs: shared borrows that *overlap* (read-read), **dynamic ranges** (a pointer
derived from `&arr[0]` may walk the whole slice — what `strtoull` does to `nptr`), and
interior pointers. We cite TB as the semantic justification.

## Scope: contract residue, NOT the operational model

We do **not** port the Tree Borrows operational semantics (per-location permission state
machines, the derivation tree, UB triggers — a research-scale effort, and unnecessary:
hex0 creates no derived pointers, never reborrows, is single-threaded). We take only the
**separation consequence** — a well-formedness predicate and the disjointness it implies:

```lean
structure Slice where base : Word; len : Nat
def Slice.has (s : Slice) (a : Word) : Prop := ∃ k, k < s.len ∧ a = s.base + BitVec.ofNat 64 k
inductive Perm | shared | uniq
structure Borrow where slice : Slice; perm : Perm
def Disjoint (s t : Slice) : Prop := ∀ a, s.has a → t.has a → False
def Wf (bs : List Borrow) : Prop :=                 -- a unique borrow is disjoint from all others
  ∀ b ∈ bs, ∀ b' ∈ bs, b ≠ b' → (b.perm = .uniq ∨ b'.perm = .uniq) → Disjoint b.slice b'.slice
```

(currently in `LowIR/CtrlHex0Proof.lean`; promote to `LowIR/Borrow.lean` for libc-wide reuse.)

## Standing assumption (record in TCB)

The bootstrap is **single-threaded**: there is no `pthread_create`/`clone(CLONE_VM)`/TLS
setup. Therefore `errno` is a plain global `int` at a fixed address (as minimal/bootstrap
libcs implement it), not thread-local storage. If threading is ever added, `errno`
graduates to TLS and this assumption must be revisited.
