(** * Kernel-checked certification of the deployed hex1 binary against the spec.

    Mirror of lean/Hex1/Certify.lean (which needs [native_decide]); here
    [coreSpec1]/[runUntil] reduce under [vm_compute], so these are proved by
    [vm_compute; reflexivity] -- checked by the Coq kernel, NO native compiler
    in the TCB.

    Weaker than the general refinement (the Refine1.v port) but a fully checked
    statement about the exact bytes that run in QEMU: the embedded 267-byte
    input plus a battery covering every status code and label-offset shape
    (forward/backward/adjacent references, duplicate labels, undefined
    references, exotic label bytes, capacity straddles). *)

From Coq Require Import ZArith List Lia Bool.
From Hex0Coq Require Import Spec1 Rv64i Harness Harness1.
From Hex0Coq Require Image1.
Import ListNotations.
Local Open Scope Z_scope.

(* The input physically embedded in the bare-metal image decodes to what the
   spec says ... *)
Theorem certify1_embedded :
  runOn1 Image1.inputBytes 4096 = specOn1 (zin Image1.inputBytes) 4096.
Proof. vm_compute. reflexivity. Qed.

(* ... and that value is exactly what QEMU printed (bare/run1.log):
   "Hello\n" ++ FC FF FF FF ++ 00 00 00 00. *)
Theorem certify1_embedded_value :
  runOn1 Image1.inputBytes 4096
    = (0, [72; 101; 108; 108; 111; 10; 252; 255; 255; 255; 0; 0; 0; 0]%nat, 14).
Proof. vm_compute. reflexivity. Qed.

(* Battery 1/3: hex0-compatible statuses on hex1 (incl. the new stop chars). *)
Theorem certify1_battery_hex0 :
  runOn1 [] 4096                  = specOn1 (zin []) 4096                  (* Ok, empty *)
  /\ runOn1 [65;66] 4096          = specOn1 (zin [65;66]) 4096            (* Ok, AB *)
  /\ runOn1 [65] 4096             = specOn1 (zin [65]) 4096               (* Trailing *)
  /\ runOn1 [65;32] 4096          = specOn1 (zin [65;32]) 4096            (* Split (space) *)
  /\ runOn1 [65;58] 4096          = specOn1 (zin [65;58]) 4096            (* Split (':') *)
  /\ runOn1 [65;37] 4096          = specOn1 (zin [65;37]) 4096            (* Split ('%') *)
  /\ runOn1 [65;90] 4096          = specOn1 (zin [65;90]) 4096            (* Unknown (low) *)
  /\ runOn1 [90] 4096             = specOn1 (zin [90]) 4096               (* Unknown (high) *)
  /\ runOn1 [65;66;67;68] 1       = specOn1 (zin [65;66;67;68]) 1         (* OutputShort *)
  /\ runOn1 [35;99;10;65;66] 4096 = specOn1 (zin [35;99;10;65;66]) 4096.  (* comment *)
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(* Battery 2/3: label definitions and references (offset shapes). *)
Theorem certify1_battery_labels :
  runOn1 [58;65;32;48;48;32;37;65] 4096
    = specOn1 (zin [58;65;32;48;48;32;37;65]) 4096                        (* back ref *)
  /\ runOn1 [37;65;32;58;65] 4096 = specOn1 (zin [37;65;32;58;65]) 4096   (* fwd ref *)
  /\ runOn1 [58;65;37;65] 4096    = specOn1 (zin [58;65;37;65]) 4096      (* adjacent *)
  /\ runOn1 [37;65;37;65;58;65] 4096
    = specOn1 (zin [37;65;37;65;58;65]) 4096                              (* double fwd *)
  /\ runOn1 [58;58;32;48;48;32;37;58] 4096
    = specOn1 (zin [58;58;32;48;48;32;37;58]) 4096                        (* label ':' *)
  /\ runOn1 [58;10;32;48;48;32;37;10] 4096
    = specOn1 (zin [58;10;32;48;48;32;37;10]) 4096                        (* label '\n' *)
  /\ runOn1 [58;0;32;48;48;32;37;0] 4096
    = specOn1 (zin [58;0;32;48;48;32;37;0]) 4096                          (* label NUL *)
  /\ runOn1 [59;58;65;10;37;65] 4096
    = specOn1 (zin [59;58;65;10;37;65]) 4096.                             (* ':' in comment *)
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(* Battery 3/3: the new error classes and capacity interactions. *)
Theorem certify1_battery_errors :
  runOn1 [58;65;32;58;65] 4096    = specOn1 (zin [58;65;32;58;65]) 4096   (* Dup *)
  /\ runOn1 [37;90] 4096          = specOn1 (zin [37;90]) 4096            (* Undef *)
  /\ runOn1 [48;48;32;37;90] 4096 = specOn1 (zin [48;48;32;37;90]) 4096   (* Undef partial *)
  /\ runOn1 [37;113;32;71] 4096   = specOn1 (zin [37;113;32;71]) 4096     (* Unknown beats Undef *)
  /\ runOn1 [58] 4096             = specOn1 (zin [58]) 4096               (* TrailTok ':' *)
  /\ runOn1 [37] 4096             = specOn1 (zin [37]) 4096               (* TrailTok '%' *)
  /\ runOn1 [37;65;32;58;65] 3    = specOn1 (zin [37;65;32;58;65]) 3      (* field short *)
  /\ runOn1 [37;65;32;58;65] 4    = specOn1 (zin [37;65;32;58;65]) 4      (* field exact *)
  /\ runOn1 [48;48;32;37;65;32;58;65] 4
    = specOn1 (zin [48;48;32;37;65;32;58;65]) 4.                          (* field straddle *)
Proof. repeat apply conj; vm_compute; reflexivity. Qed.
