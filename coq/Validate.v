(** * Executable validation of the Coq RV64I model against the real binary.
    Mirror of lean/Hex0/Validate.lean. Runs the ACTUAL bytes of `core` through
    [step] and checks the result matches [coreSpec]. Uses [vm_compute]. *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec Rv64i Image.
Import ListNotations.
Local Open Scope Z_scope.

(* membership-by-range reader over the two byte blobs *)
Definition memOf (a : Z) : Z :=
  if (coreAddr <=? a) && (a <? coreAddr + Z.of_nat (length coreBytes))
  then nth (Z.to_nat (a - coreAddr)) coreBytes 0
  else if (inputAddr <=? a) && (a <? inputAddr + Z.of_nat (length inputBytes))
  then nth (Z.to_nat (a - inputAddr)) inputBytes 0
  else 0.

(* read [len] bytes from a state's memory starting at [base] as nats (for Spec) *)
Fixpoint readMem (m : Z -> Z) (base : Z) (len : nat) : list nat :=
  match len with
  | O => []
  | S k => Z.to_nat (m base) :: readMem m (base + 1) k
  end.

Definition mkInit (inpAddr inpLen cap : Z) (m : Z -> Z) : State :=
  mkState
    (fun i => if i =? 1 then 0
              else if i =? 10 then inpAddr
              else if i =? 11 then inpLen
              else if i =? 12 then outAddr
              else if i =? 13 then cap
              else 0)
    coreAddr m.

Definition memWith (inp : list Z) (inpAddr : Z) : Z -> Z :=
  fun a =>
    if (coreAddr <=? a) && (a <? coreAddr + Z.of_nat (length coreBytes))
    then nth (Z.to_nat (a - coreAddr)) coreBytes 0
    else if (inpAddr <=? a) && (a <? inpAddr + Z.of_nat (length inp))
    then nth (Z.to_nat (a - inpAddr)) inp 0
    else 0.

(* run the real core on input bytes [inp] with capacity [cap] *)
Definition runOn (inp : list Z) (cap : Z) : Z * list nat * Z :=
  let s0 := mkInit inputAddr (Z.of_nat (length inp)) cap (memWith inp inputAddr) in
  let f := runUntil 0 100000 s0 in
  (rget f 10, readMem f.(mem) outAddr (Z.to_nat (rget f 11)), rget f 11).

(* the spec's answer, packaged in the same shape (status as Z, out as list nat) *)
Definition specOn (inp : list nat) (cap : nat) : Z * list nat * Z :=
  let '(st, bs, ln) := coreSpec inp cap in
  (Z.of_nat st, bs, Z.of_nat ln).

Definition zin (l : list Z) : list nat := map Z.to_nat l.

(* headline: the smoke-test input *)
Eval vm_compute in runOn inputBytes 4096.
(* expect (0, [72;101;108;108;111;10], 6) *)
Eval vm_compute in specOn (zin inputBytes) 4096.

(* differential battery, mirroring the Lean one *)
Definition battery : list (list Z * Z) :=
  [ ([], 4096);
    ([65;66], 4096);
    ([65], 4096);
    ([65;32], 4096);
    ([65;90], 4096);
    ([90], 4096);
    ([65;66;67;68], 1);
    ([35;99;10;65;66], 4096);
    ([52;49;95;52;50], 4096);
    ([97;98], 4096);
    ([48;97], 4096);
    ([59;120;121], 4096);
    ([70;70;65;65], 4096) ].

Definition eqRes (a b : Z * list nat * Z) : bool :=
  let '(s1,o1,l1) := a in let '(s2,o2,l2) := b in
  (s1 =? s2) && (l1 =? l2) && (if list_eq_dec Nat.eq_dec o1 o2 then true else false).

Definition diff : list bool :=
  map (fun '(inp, cap) => eqRes (runOn inp cap) (specOn (zin inp) (Z.to_nat cap))) battery.

Eval vm_compute in diff.                       (* expect all true *)
Eval vm_compute in forallb (fun b => b) diff.  (* expect true *)
