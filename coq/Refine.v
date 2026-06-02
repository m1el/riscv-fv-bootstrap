(** * General refinement (T1) in Coq -- mirror of lean/Hex0/Refine.lean.

    Proof-grade theorem: for ALL inputs, the real `core` computes `coreSpec`.
    No vm_compute on the general statement -- it is genuine induction.

    STATUS: scaffold. The per-step reduction primitive is proved (`step_li_t0`);
    the top-level statement and well-formedness are pinned down; the inductive
    loop body is the remaining frontier (`Admitted`). See STATUS.md. *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec Rv64i Image Harness.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Per-step reduction primitive (PROVED).
    `core`'s first instruction `li t0,0` = `addi x5,x0,0`, bytes 93 02 00 00,
    word 0x293 = 659. One [step] computes its effect; data stays symbolic. *)
Theorem step_li_t0 : forall s,
  s.(mem) s.(pc) = 147 ->
  s.(mem) (s.(pc) + 1) = 2 ->
  s.(mem) (s.(pc) + 2) = 0 ->
  s.(mem) (s.(pc) + 3) = 0 ->
  s.(pc) = 2147483784 ->
  (step s).(pc) = 2147483788 /\ rget (step s) 5 = 0.
Proof.
  intros s h0 h1 h2 h3 hpc.
  unfold step, fetch32.
  rewrite h0, h1, h2, h3.
  (* fetched word is now the closed value 659; decode + effect compute *)
  change (147 + 2 * 256 + 0 * 65536 + 0 * 16777216) with 659.
  rewrite hpc. cbn. split; reflexivity.
Qed.

(** ** Well-formedness: input region fits before the output region, etc. *)
Record WellFormed (inp : list Z) (cap : Z) : Prop := {
  in_fits  : inputAddr + Z.of_nat (length inp) <= outAddr;
  out_fits : outAddr + cap < 2 ^ 64;
  bytes_ok : forall b, In b inp -> 0 <= b < 256
}.

(** ** The general refinement theorem (FRONTIER).
    Proof outline (mirrors the Lean file): establish the main-loop invariant from
    the initial state, prove one iteration preserves it or halts correctly (case
    analysis on the next char's class), induct on the remaining input length. *)
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
Proof.
Admitted.
