# Creusot — design choices

An analysis of `third-party/creusot/` (checkout `c35b5d371`, 2026 master):
**Creusot**, the deductive verifier for safe Rust, built on Why3/Coma. This
completes a triangle with two earlier reviews: rustc's borrow checker
([RUSTC-BORROWCK-DESIGN.md](RUSTC-BORROWCK-DESIGN.md)) enforces aliasing
discipline and throws the information away; Verus
([VERUS-DESIGN.md](VERUS-DESIGN.md)) reuses the borrow checker to make
*linear ghost tokens* checkable and keeps the SMT encoding first-order that
way; Creusot reuses the borrow checker to justify an entirely different
move — the **prophecy encoding** of RustHorn/RustHornBelt:

> mutable borrows become pure pairs `{current, final}`, where `final` is a
> prophecy variable resolved (`final = current`) at the moment the borrow
> dies — so the whole program translates to a **pure functional program**,
> and "mutable borrows can be represented efficiently without separation
> logic" (ARCHITECTURE.md).

Verification conditions are then discharged by Why3's prover portfolio.
The thesis stated in ARCHITECTURE.md: this yields "an asymptotic improvement
to the difficulty of verifying pointer programs."

## 1. The prophecy encoding

The Coma prelude defines the model directly
(`prelude-generator/prelude.coma`):

```
type t 'a = { current : 'a; final : 'a; id : int }
let borrow_final <'a> (a : 'a) (id : int) (ret (result : t 'a)) =
  any [ k (fin : 'a) -> (! ret { current = a; final = fin; id = id }) ]
```

Creating a borrow *nondeterministically guesses* the final value; the guess
is discharged when the borrow expires by assuming `resolve`: `current =
final`. Everything in between is functional: writing through a borrow
updates `current` (`*p = v` ⇒ `{ current = v; final = p.final }`); the
Pearlite operators `*` and `^` read `current` and `final`. Subtleties the
implementation carries:

- **Reborrows**: a "final" reborrow (source dead immediately after) inherits
  the parent's prophecy identity (`fmir::BorrowKind::Final(depth)`,
  `analysis/not_final_places.rs`); field reborrows derive ids
  deterministically. The guide documents why the `id` component exists at
  all — without it, prophecy aliasing admits `**evil == !**evil`-style
  unsoundness (`guide/src/representation_of_types/mutable_borrows.md`).
- **Where to resolve** is a genuine static analysis (§3).
- **Soundness** rests on the RustHornBelt paper (Iris/Coq proof of the
  encoding against a realistic Rust semantics) — cited, not mechanized
  in-repo. The encoding is only sound for *safe* Rust: unsafe code is
  rejected (raw-pointer deref forbidden; a `Perm<*const T>`-style ghost
  permission type is the sanctioned workaround), and destructors are
  assumed unobservable — a code comment honestly flags that the
  liveness-modulo-drop choice is "unclear that this can be sound" if a
  `Drop` impl mutates through borrows (`analysis/resolve.rs`).

## 2. rustc integration: verify after the borrow checker

Creusot is a rustc driver (flowistry-style binary split: `cargo-creusot` /
`creusot-rustc` / driver) that hooks queries surgically
(`creusot/src/callbacks.rs`):

- `mir_built`: *deletes the MIR of specification code* (Pearlite closures,
  contracts, snapshots) before drop insertion, so logic code never has to
  satisfy `Drop`;
- `mir_borrowck`: **steals `BodyWithBorrowckFacts`** — Creusot's input is
  the borrow-checked MIR *plus* rustc's borrow set and region data. This is
  the concrete sense in which borrowck information, discarded by rustc's own
  pipeline, is *consumed* here: the loans feed the resolve-point analysis;
- `mir_drops_elaborated…`: removes ghost closures so `cargo build` artifacts
  never contain ghost-only code.

Notably it also *removes match false edges* from the stolen MIR
(pattern-lowering artifacts create places that are simultaneously live and
uninitialized, which the resolve analysis can't tolerate) — a nice example
of one tool's precision hack being another tool's poison.

## 3. Resolve points: a three-dataflow recipe

The heart of the translation (`creusot/src/analysis/`): deciding *where* to
assume `final = current`. Three dataflow analyses (all built on rustc's own
`rustc_mir_dataflow` framework) run to fixpoint:

1. `MaybeLiveExceptDrop` — backward liveness that ignores pure drops;
2. `MaybeUninitializedPlaces` — forward initialization (with inactive enum
   variants marked uninitialized, for variant-precise resolution);
3. `Borrows` — rustc's own loans-in-scope analysis over the stolen borrow
   set ("frozen" places).

A place **needs resolution** while `(live ∪ frozen) ∩ initialized`; it **is
resolved** at the transition into `¬live ∩ ¬frozen ∩ initialized`. Resolve
statements are emitted at exactly those statement/edge boundaries (including
mid-statement states around assignments and call returns, synthesized by
manually applying transfer functions). Two-phase borrows get their own
tracked creation/activation points. This is the single most reusable
artifact in the codebase: a *complete, executable definition of "where
borrows die"* in terms of standard dataflow.

Translation then goes MIR → **fMIR** (a functional MIR: `Ident`-named
places, explicit `MutBorrow` statements, assertions/invariants attached to
blocks, spec-closure locals erased) → Coma. Deep place updates use a lazy
**focus/constructor** pair (read-thunk + rebuild-thunk composed per
projection), implementing ARCHITECTURE.md's accessor/writer scheme; enum
field access goes through generated eliminators; array updates through
`SliceOps.get/set`.

## 4. Pearlite: specs as Rust, typechecked by rustc

The spec language is embedded with the same trick Verus uses, implemented
differently: a **forked-`syn` grammar** (`pearlite-syn`) adds `forall<x>`/
`exists<x>` (with `#[trigger]`s), `==>` implication, `^` (final), `@`
(view/model), logical `==`, `seq![…]`, `dead`. The proc macros then
re-print the parsed term as ordinary Rust in **HOAS style** — quantifiers
become closures passed to stub functions (`creusot_std::__stubs::exists(|i:
Int| …)`) — so *rustc itself* name-resolves and typechecks every spec.
Creusot later recovers the THIR of these stub-riddled bodies and pattern-
matches the stubs back into logical operators. Two design points differ
from Verus: Pearlite has **no ownership** ("values aren't machine resources
anymore" — the borrow checker is disabled on spec code), and there is no
`verus!{}` block — everything rides on attribute macros over plain Rust
files, with a dual proc-macro backend (`creusot` cfg vs. `dummy`) so the
same crate builds normally without the toolchain.

The logic layer (`creusot-std`): mathematical `Int`, `Seq`, `FSet`, `FMap`,
total `Mapping<A,B>` (backed by Why3 theories via `#[builtin]`); the
**`View`/`@` pattern** — every specced data structure gets a shallow
mathematical model (`Vec<T>@ : Seq<T>`), and specifications are stated
against models, not representations; `DeepModel` for recursive model
lifting. Logic functions are `#[logic]` with orthogonal flags: `open(vis)`
(body transparency follows a *visibility-like* opacity discipline),
`prophetic` (may use `^`; not callable from non-prophetic logic or
snapshots), `law` (auto-loaded axioms attached to traits — e.g. the iterator
laws), `sealed`, plus `#[variant]` termination obligations — logic functions
are *always* termination-checked, for soundness.

## 5. Ghost code and the purity ladder

Creusot splits what Verus fuses into modes into a **purity hierarchy**
(`validate/purity.rs`): logic (non-prophetic ⊂ prophetic), and program code
at three levels — ghost ⊂ terminates ⊂ impure — with call edges only down
the ladder. Two ghost constructs:

- **`Snapshot<T>`** — zero-sized, `Copy`, purely logical photograph of a
  value (`snapshot!(expr)`); the escape hatch *out of* ownership.
- **`Ghost<T>`** — the opposite: ghost data that **keeps Rust's ownership
  discipline**. `ghost!{}` blocks are borrow-checked like real code (the
  validator rejects moving/mutating non-ghost data inside them), may
  allocate unbounded `Seq`/`FMap` structures, and must provably terminate.
  This gives Creusot linear ghost state (permissions, model fields) without
  separation logic — the same instinct as Verus's `Tracked<T>`, arrived at
  independently.

Erasure is *checked, not assumed*: an A-normal-form comparison of THIR
(`validate/erasure.rs`) verifies that the program with ghost code erased is
compositionally equivalent to the plain build.

Type invariants (`Invariant` trait) are injected at function boundaries
(`inv(arg)` required, `inv(result)` ensured), elaborated structurally
through types (with private fields axiomatized rather than exposed —
visibility-aware, like the opacity story), and for `&mut T` cover **both**
`*self` and `^self`. Within a function, invariants may be temporarily
broken — the boundary discipline plus resolution makes that sound. Closures
get the full treatment: per-`Fn`/`FnMut`/`FnOnce` precondition/
postcondition templates plus a **history invariant** (`hist_inv`)
constraining what a `FnMut` closure may do to its captures across calls;
iterators get the **`produces`/`completed` protocol** — `produces(self,
visited, next_state)` as a transitive, reflexive law-governed relation —
which is the de-facto standard spec pattern Creusot contributed to the
field. External code is specced by `extern_spec!` (a wrapper-function
desugaring with generics-permutation checking) — pure trusted axioms, same
role as Verus's `assume_specification` and vstd's `std_specs`.

## 6. Coma and the proof pipeline

Since v0.2 Creusot targets **Coma**, Why3's new kernel IVL, instead of
WhyML/MLCFG. Coma is a minimal higher-order CPS language (handlers,
`Defn`, `Assert`/`Assume`, backward `Assign`) whose signature feature is
the **`BlackBox` barrier** (`! e`): "everything under an abstraction is
opaque to the outside world, whereas from the inside, we can suppose any
surrounding assertions hold" — caller/callee proof responsibility drawn
syntactically, giving first-order VCs from higher-order programs and
avoiding exponential WP blowup (the stated motivation was specifying
closures without VC explosion). Program functions become one Coma handler
per Rust function; logic functions get a custom VC generator ("a cross
between a WP and an evaluator" that validates preconditions along the
lemma's own evaluation order — lemma-function structure as proof skeleton).

Machine integers are **range types** generated per width (8–128 bit,
signed/unsigned) by `prelude-generator`, with overflow obligations as VCs
(and bitwise variants available); `char` is axiomatized as a Unicode scalar;
pointers carry logical addresses. The toolchain: `cargo creusot` emits
`.coma`, `cargo creusot prove` drives **why3find** (portfolio: Alt-Ergo,
Z3, CVC5, CVC4; split/compute tactics; per-prover time profiles;
`-i` drops into the Why3 IDE on failure). Proof state is replayable and
CI-tested: 283 should-succeed + 116 should-fail test directories with
golden `.coma` outputs, plus a why3-replay suite. Flagship examples:
`IterMut`, red-black trees, union-find, a verified SAT solver (CreuSAT)
downstream.

TCB: rustc (typeck + borrowck), the Creusot translation (justified on paper
by RustHornBelt, not mechanized), Why3 + Coma's VC generation, the SMT
portfolio, the axiomatized prelude and every `extern_spec`/`#[trusted]`
item.

## 7. Takeaways

For our tower — where MEMORY-BORROWS.md already commits to a borrows-based
separation discipline and a LowIR borrow checker is on the table
(cf. the rustc review) — Creusot supplies the missing third corner of the
design space:

1. **Prophecies are the payoff of a borrow checker.** Once uniqueness of
   `&mut` is enforced, mutation becomes *functional*: a borrow is a pair,
   its final value a prophecy, and no separation logic or heap reasoning
   survives into the VCs. If LowIR grows checked borrows, the RustHorn
   translation is the cheapest route from borrow-checked programs to
   first-order proof obligations — strictly simpler targets than our
   current explicit-disjointness call specs.
2. **The resolve-point recipe is directly liftable**: `(live ∪ frozen) ∩
   initialized` over three standard dataflows, with mid-statement state
   synthesis. This is the executable answer to "when does a borrow end" —
   the same question our frame-based call spec design has to answer at
   call boundaries.
3. **Split ghost from spec.** Creusot's ladder — unrestricted logic
   (Pearlite, no ownership) vs. ownership-respecting, terminating ghost
   code (`Ghost<T>`) vs. program — with *checked* erasure, is cleaner than
   a single ghost mode; the ANF-equivalence erasure check is a verifiable
   statement of "specs don't change the program" we could imitate.
4. **Opacity as visibility** (`#[logic(open(pub(crate)))]`, private fields
   axiomatized) is an elegant unification of proof-abstraction with the
   language's existing modularity mechanism — same family as Verus's
   broadcast groups and CompCert's per-module pruning, but keyed to `pub`.
5. **Coma's BlackBox barrier** is an IVL-level answer to VC blowup that our
   own factored-lemma discipline mirrors manually; if we ever generate VCs
   from LowIR, a barrier operator in the VC language beats post-hoc goal
   splitting.
6. Cross-review: Verus and Creusot chose the **same front-end trick**
   (specs as macro-mangled Rust so rustc typechecks them) and the **same
   ghost-linearity insight**, but opposite proof backends (in-house SMT
   encoding vs. Why3 portfolio) and opposite `&mut` stories (linear tokens
   + first-order heap vs. prophecy pairs + no heap at all). The pair of
   docs is the honest comparison of those trade-offs.
