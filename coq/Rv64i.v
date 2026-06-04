(** * A minimal, executable RV64I model in Coq -- mirror of lean/Hex0/Rv64i.lean.

    Exactly the 16 instruction encodings used by bare/core.s (hex0) and
    bare/core1.s (hex1):
      ADDI ADD OR SLLI LBU SB BEQ BLT BGE BGEU JAL JALR   (hex0's 12)
      SUB SRLI LD SD                                       (added for hex1)
    64-bit words are [Z] kept in [0, 2^64); operations wrap explicitly. Memory
    is byte-addressed ([Z -> Z], bytes in [0,256)). The model computes under
    [vm_compute] so it can be run on the real binary bytes (see Validate.v). *)

From Coq Require Import ZArith List Lia Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition w64 : Z := 2 ^ 64.

Definition wrap (z : Z) : Z := z mod w64.
Definition wadd (a b : Z) : Z := wrap (a + b).
Definition wor  (a b : Z) : Z := Z.lor a b.
Definition wshl (a : Z) (n : Z) : Z := wrap (Z.shiftl a n).
Definition wsub (a b : Z) : Z := wrap (a - b).
(* logical shift right; in-range arguments stay in range *)
Definition wshr (a : Z) (n : Z) : Z := Z.shiftr a n.

(* sign-extend a [k]-bit raw value to a (possibly negative) Z *)
Definition sext (k raw : Z) : Z :=
  if raw >=? 2 ^ (k - 1) then raw - 2 ^ k else raw.

(* unsigned / signed comparisons on in-range words *)
Definition toS (x : Z) : Z := if x >=? 2 ^ 63 then x - w64 else x.
Definition ultb (a b : Z) : bool := a <? b.
Definition sltb (a b : Z) : bool := toS a <? toS b.

(* extract [len] bits at offset [lo] from a 32-bit value *)
Definition field (w lo len : Z) : Z := (w / 2 ^ lo) mod 2 ^ len.

Record State := mkState {
  reg : Z -> Z;     (* x0..x31 ; x0 forced to 0 by rget/rset *)
  pc  : Z;
  mem : Z -> Z      (* byte-addressed *)
}.

Definition rget (s : State) (i : Z) : Z := if i =? 0 then 0 else s.(reg) i.

Definition rset (s : State) (i : Z) (v : Z) : State :=
  if i =? 0 then s
  else mkState (fun j => if j =? i then v else s.(reg) j) s.(pc) s.(mem).

Definition setPc (s : State) (p : Z) : State := mkState s.(reg) p s.(mem).

Definition storeByte (s : State) (a b : Z) : State :=
  mkState s.(reg) s.(pc) (fun x => if x =? a then b mod 256 else s.(mem) x).

Definition fetch32 (s : State) : Z :=
  let b0 := s.(mem) s.(pc) in
  let b1 := s.(mem) (s.(pc) + 1) in
  let b2 := s.(mem) (s.(pc) + 2) in
  let b3 := s.(mem) (s.(pc) + 3) in
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216.

(** Load the little-endian 64-bit word at address [a] (8 byte reads,
    mirror of lean Rv64i.State.loadWord). *)
Definition loadWord (s : State) (a : Z) : Z :=
  s.(mem) a
  + s.(mem) (a + 1) * 2 ^ 8
  + s.(mem) (a + 2) * 2 ^ 16
  + s.(mem) (a + 3) * 2 ^ 24
  + s.(mem) (a + 4) * 2 ^ 32
  + s.(mem) (a + 5) * 2 ^ 40
  + s.(mem) (a + 6) * 2 ^ 48
  + s.(mem) (a + 7) * 2 ^ 56.

(** Store the 64-bit word [v] at address [a], little-endian (8 byte stores,
    low byte first -- compositional for the proof side; [storeByte] keeps
    each byte in [0,256)). *)
Definition storeWord (s : State) (a v : Z) : State :=
  storeByte (storeByte (storeByte (storeByte (storeByte (storeByte (storeByte (storeByte
    s a v)
    (a + 1) (v / 2 ^ 8))
    (a + 2) (v / 2 ^ 16))
    (a + 3) (v / 2 ^ 24))
    (a + 4) (v / 2 ^ 32))
    (a + 5) (v / 2 ^ 40))
    (a + 6) (v / 2 ^ 48))
    (a + 7) (v / 2 ^ 56).

Inductive Instr :=
  | Iaddi (rd rs1 : Z) (imm : Z)
  | Iadd  (rd rs1 rs2 : Z)
  | Isub  (rd rs1 rs2 : Z)
  | Ior   (rd rs1 rs2 : Z)
  | Islli (rd rs1 : Z) (shamt : Z)
  | Isrli (rd rs1 : Z) (shamt : Z)
  | Ilbu  (rd rs1 : Z) (imm : Z)
  | Ild   (rd rs1 : Z) (imm : Z)
  | Isb   (rs1 rs2 : Z) (imm : Z)
  | Isd   (rs1 rs2 : Z) (imm : Z)
  | Ibeq  (rs1 rs2 : Z) (imm : Z)
  | Iblt  (rs1 rs2 : Z) (imm : Z)
  | Ibge  (rs1 rs2 : Z) (imm : Z)
  | Ibgeu (rs1 rs2 : Z) (imm : Z)
  | Ijal  (rd : Z) (imm : Z)
  | Ijalr (rd rs1 : Z) (imm : Z)
  | Iunknown.

(* immediates are stored as sign-extended Z, ready to feed into wadd *)
Definition decode (w : Z) : Instr :=
  let opcode := field w 0 7 in
  let rd     := field w 7 5 in
  let funct3 := field w 12 3 in
  let rs1    := field w 15 5 in
  let rs2    := field w 20 5 in
  let funct7 := field w 25 7 in
  let immI   := sext 12 (field w 20 12) in
  let shamt  := field w 20 6 in
  let immS   := sext 12 (Z.lor (Z.shiftl funct7 5) rd) in
  let immB   := sext 13 (Z.lor (Z.lor (Z.shiftl (field w 31 1) 12) (Z.shiftl (field w 7 1) 11))
                               (Z.lor (Z.shiftl (field w 25 6) 5) (Z.shiftl (field w 8 4) 1))) in
  let immJ   := sext 21 (Z.lor (Z.lor (Z.shiftl (field w 31 1) 20) (Z.shiftl (field w 12 8) 12))
                               (Z.lor (Z.shiftl (field w 20 1) 11) (Z.shiftl (field w 21 10) 1))) in
  if opcode =? 19 then            (* 0x13 OP-IMM *)
    if funct3 =? 0 then Iaddi rd rs1 immI
    else if funct3 =? 1 then (if funct7 =? 0 then Islli rd rs1 shamt else Iunknown)
    else if funct3 =? 5 then (if funct7 =? 0 then Isrli rd rs1 shamt else Iunknown)
    else Iunknown
  else if opcode =? 51 then       (* 0x33 OP *)
    if funct7 =? 0 then
      (if funct3 =? 0 then Iadd rd rs1 rs2
       else if funct3 =? 6 then Ior rd rs1 rs2 else Iunknown)
    else if funct7 =? 32 then
      (if funct3 =? 0 then Isub rd rs1 rs2 else Iunknown)
    else Iunknown
  else if opcode =? 3 then        (* 0x03 LOAD *)
    (if funct3 =? 4 then Ilbu rd rs1 immI
     else if funct3 =? 3 then Ild rd rs1 immI else Iunknown)
  else if opcode =? 35 then       (* 0x23 STORE *)
    (if funct3 =? 0 then Isb rs1 rs2 immS
     else if funct3 =? 3 then Isd rs1 rs2 immS else Iunknown)
  else if opcode =? 99 then       (* 0x63 BRANCH *)
    (if funct3 =? 0 then Ibeq rs1 rs2 immB
     else if funct3 =? 4 then Iblt rs1 rs2 immB
     else if funct3 =? 5 then Ibge rs1 rs2 immB
     else if funct3 =? 7 then Ibgeu rs1 rs2 immB
     else Iunknown)
  else if opcode =? 111 then Ijal rd immJ          (* 0x6f JAL *)
  else if opcode =? 103 then                        (* 0x67 JALR *)
    (if funct3 =? 0 then Ijalr rd rs1 immI else Iunknown)
  else Iunknown.

Definition step (s : State) : State :=
  let next := wadd s.(pc) 4 in
  match decode (fetch32 s) with
  | Iaddi rd rs1 imm => setPc (rset s rd (wadd (rget s rs1) imm)) next
  | Iadd  rd rs1 rs2 => setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) next
  | Isub  rd rs1 rs2 => setPc (rset s rd (wsub (rget s rs1) (rget s rs2))) next
  | Ior   rd rs1 rs2 => setPc (rset s rd (wor (rget s rs1) (rget s rs2))) next
  | Islli rd rs1 sh  => setPc (rset s rd (wshl (rget s rs1) sh)) next
  | Isrli rd rs1 sh  => setPc (rset s rd (wshr (rget s rs1) sh)) next
  | Ilbu  rd rs1 imm => let a := wadd (rget s rs1) imm in
                        setPc (rset s rd ((s.(mem) a) mod 256)) next
  | Ild   rd rs1 imm => let a := wadd (rget s rs1) imm in
                        setPc (rset s rd (loadWord s a)) next
  | Isb   rs1 rs2 imm => let a := wadd (rget s rs1) imm in
                         setPc (storeByte s a (rget s rs2)) next
  | Isd   rs1 rs2 imm => let a := wadd (rget s rs1) imm in
                         setPc (storeWord s a (rget s rs2)) next
  | Ibeq  rs1 rs2 imm => setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else next)
  | Iblt  rs1 rs2 imm => setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else next)
  | Ibge  rs1 rs2 imm => setPc s (if sltb (rget s rs1) (rget s rs2) then next else wadd s.(pc) imm)
  | Ibgeu rs1 rs2 imm => setPc s (if ultb (rget s rs1) (rget s rs2) then next else wadd s.(pc) imm)
  | Ijal  rd imm => setPc (rset s rd next) (wadd s.(pc) imm)
  | Ijalr rd rs1 imm => let t := let a := wadd (rget s rs1) imm in a - (a mod 2) in
                        setPc (rset s rd next) t
  | Iunknown => s
  end.

(* Run [fuel] steps or until pc = halt (for executable validation). *)
Fixpoint runUntil (halt : Z) (fuel : nat) (s : State) : State :=
  match fuel with
  | O => s
  | S k => if s.(pc) =? halt then s else runUntil halt k (step s)
  end.
