(** * Shared Coq harness: run the real binary image through the model.
    Used by Validate.v (Eval diff-test) and Certify.v (kernel-checked proofs). *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec Rv64i Image.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint readMem (m : Z -> Z) (base : Z) (len : nat) : list nat :=
  match len with
  | O => []
  | S k => Z.to_nat (m base) :: readMem m (base + 1) k
  end.

Definition memWith (inp : list Z) (inpAddr : Z) : Z -> Z :=
  fun a =>
    if (coreAddr <=? a) && (a <? coreAddr + Z.of_nat (length coreBytes))
    then nth (Z.to_nat (a - coreAddr)) coreBytes 0
    else if (inpAddr <=? a) && (a <? inpAddr + Z.of_nat (length inp))
    then nth (Z.to_nat (a - inpAddr)) inp 0
    else 0.

Definition mkInit (inpLen cap : Z) (m : Z -> Z) : State :=
  mkState
    (fun i => if i =? 1 then 0
              else if i =? 10 then inputAddr
              else if i =? 11 then inpLen
              else if i =? 12 then outAddr
              else if i =? 13 then cap
              else 0)
    coreAddr m.

(* Observable result of running the real core on [inp] with capacity [cap]. *)
Definition runOn (inp : list Z) (cap : Z) : Z * list nat * Z :=
  let s0 := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr) in
  let f := runUntil 0 100000 s0 in
  (rget f 10, readMem f.(mem) outAddr (Z.to_nat (rget f 11)), rget f 11).

Definition zin (l : list Z) : list nat := map Z.to_nat l.

(* The spec's answer, packaged in the same shape. *)
Definition specOn (inp : list nat) (cap : nat) : Z * list nat * Z :=
  let '(st, bs, ln) := coreSpec inp cap in
  (Z.of_nat st, bs, Z.of_nat ln).
