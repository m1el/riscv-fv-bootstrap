(** * Shared Coq harness for hex1: run the real core1 image through the model.
    Mirror of lean/Hex1/Harness.lean (and of Harness.v for hex0). Used by
    Certify1.v (kernel-checked vm_compute certification).

    Differences vs hex0's harness: core1 additionally takes a4 = label-table
    scratch pointer (reg 14); the label table region is NOT pre-initialized
    (core1's init loop fills it with -1 itself). *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec1 Rv64i Harness.
From Hex0Coq Require Image1.
Import ListNotations.
Local Open Scope Z_scope.

(* core1 + input loaded at their hex1 image addresses; rest of memory 0. *)
Definition memWith1 (inp : list Z) (inpAddr : Z) : Z -> Z :=
  fun a =>
    if (Image1.coreAddr <=? a) && (a <? Image1.coreAddr + Z.of_nat (length Image1.coreBytes))
    then nth (Z.to_nat (a - Image1.coreAddr)) Image1.coreBytes 0
    else if (inpAddr <=? a) && (a <? inpAddr + Z.of_nat (length inp))
    then nth (Z.to_nat (a - inpAddr)) inp 0
    else 0.

(* Initial state per core1's calling convention: a0=in_ptr, a1=in_len,
   a2=out_ptr, a3=cap, a4=lbl_ptr, ra=0 sentinel; pc = core1 entry. *)
Definition mkInit1 (inpLen cap : Z) (m : Z -> Z) : State :=
  mkState
    (fun i => if i =? 1 then 0
              else if i =? 10 then Image1.inputAddr
              else if i =? 11 then inpLen
              else if i =? 12 then Image1.outAddr
              else if i =? 13 then cap
              else if i =? 14 then Image1.lblAddr
              else 0)
    Image1.coreAddr m.

(* Observable result of running the real core1 on [inp] with capacity [cap]:
   (status, output bytes, out_len). Fuel 100000 covers the embedded input
   (256 init iterations + 2 passes over <=267 bytes ~ 7000 steps). *)
Definition runOn1 (inp : list Z) (cap : Z) : Z * list nat * Z :=
  let s0 := mkInit1 (Z.of_nat (length inp)) cap (memWith1 inp Image1.inputAddr) in
  let f := runUntil 0 100000 s0 in
  (rget f 10, readMem f.(mem) Image1.outAddr (Z.to_nat (rget f 11)), rget f 11).

(* The spec's answer, packaged in the same shape. *)
Definition specOn1 (inp : list nat) (cap : nat) : Z * list nat * Z :=
  let '(st, bs, ln) := coreSpec1 inp cap in
  (Z.of_nat st, bs, Z.of_nat ln).
