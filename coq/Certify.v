(** * Kernel-checked certification of the deployed binary against the spec.

    Mirror of lean/Hex0/Certify.lean. Unlike the Lean side (which needs
    [native_decide] because its `decode` is blocked from kernel reduction),
    Coq's `coreSpec` reduces under [vm_compute], so these are proved by
    [vm_compute; reflexivity] -- checked by the Coq kernel, NO native compiler
    in the TCB. (vm_compute is part of Coq's trusted kernel.)

    Weaker than the general refinement (Refine.v) but a fully checked statement
    about the exact bytes that run in QEMU. *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec Rv64i Image Harness.
Import ListNotations.
Local Open Scope Z_scope.

(* The input embedded in the bare-metal image matches the spec ... *)
Theorem certify_embedded :
  runOn inputBytes 4096 = specOn (zin inputBytes) 4096.
Proof. vm_compute. reflexivity. Qed.

(* ... and that value is exactly ("Hello\n", Ok). *)
Theorem certify_embedded_value :
  runOn inputBytes 4096 = (0, [72; 101; 108; 108; 111; 10]%nat, 6).
Proof. vm_compute. reflexivity. Qed.

(* Battery covering every error class. *)
Theorem certify_battery :
  runOn [] 4096                = specOn (zin []) 4096
  /\ runOn [65;66] 4096        = specOn (zin [65;66]) 4096          (* Ok AB->0xAB *)
  /\ runOn [65] 4096           = specOn (zin [65]) 4096             (* Trailing *)
  /\ runOn [65;32] 4096        = specOn (zin [65;32]) 4096          (* Split *)
  /\ runOn [65;90] 4096        = specOn (zin [65;90]) 4096          (* Unknown low *)
  /\ runOn [90] 4096           = specOn (zin [90]) 4096             (* Unknown high *)
  /\ runOn [65;66;67;68] 1     = specOn (zin [65;66;67;68]) 1       (* OutputShort *)
  /\ runOn [35;99;10;65;66] 4096 = specOn (zin [35;99;10;65;66]) 4096 (* comment *)
  /\ runOn [52;49;95;52;50] 4096 = specOn (zin [52;49;95;52;50]) 4096 (* '_' spacing *)
  /\ runOn [97;98] 4096        = specOn (zin [97;98]) 4096          (* lowercase reject *)
  /\ runOn [48;97] 4096        = specOn (zin [48;97]) 4096          (* 0 then lowercase *)
  /\ runOn [59;120;121] 4096   = specOn (zin [59;120;121]) 4096     (* ';' comment EOF *)
  /\ runOn [70;70;65;65] 4096  = specOn (zin [70;70;65;65]) 4096.   (* FF AA *)
Proof. repeat split; vm_compute; reflexivity. Qed.
