(** * hex0 functional specification (the refinement target)

    This is the SHARED spec: the Lean file Hex0/Spec.lean mirrors it
    definition-for-definition. Bytes are modelled as [nat] (assumed < 256);
    the input is a [list nat].

    The spec is a two-state machine (EXPECT_HIGH / EXPECT_LOW), written as a
    single well-founded recursion [decodeS] over an explicit state [St], so
    there is exactly one termination argument (decreasing on input length).

    Reconciliation of sources:
      - HEX0.md gives the grammar + error names.
      - hex0.c (`unhex`) is the executable reference.
      - bare/core.s is the artifact the refinement proof concerns.
    In LOW position the five "stop" characters (\n ' ' '_' '#' ';') yield
    [Split]; any other non-hex character yields [Unknown]; EOF yields
    [Trailing]. Capacity (OutputShort) is NOT part of [decode] -- it is a
    property of the bounded machine, applied separately in [coreSpec]. *)

From Coq Require Import List Arith Lia Bool.
From Equations Require Import Equations.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(* Character codes used by hex0. *)
Definition c_nl    := 10.   (* '\n' *)
Definition c_sp    := 32.   (* ' '  *)
Definition c_us    := 95.   (* '_'  *)
Definition c_hash  := 35.   (* '#'  *)
Definition c_semi  := 59.   (* ';'  *)

Definition isSpace   (c:nat) : bool := (c =? c_nl) || (c =? c_sp) || (c =? c_us).
Definition isComment (c:nat) : bool := (c =? c_hash) || (c =? c_semi).
(* the characters that, seen where a low nibble is expected, give Split *)
Definition isLowStop (c:nat) : bool := isSpace c || isComment c.

(* nibble value 0..15, or None if c is not an uppercase hex digit. *)
Definition nibble (c:nat) : option nat :=
  if (48 <=? c) && (c <=? 57) then Some (c - 48)        (* '0'..'9' *)
  else if (65 <=? c) && (c <=? 70) then Some (c - 55)   (* 'A'..'F' -> 10..15 *)
  else None.

(* Terminal status of a decode (capacity-independent). *)
Inductive Status := Ok | Split | Trailing | Unknown.

(* Skip a comment body: drop characters up to and including the first '\n'.
   (In core.s the '\n' is left for the main loop and skipped there as spacing;
   the net effect is the same -- continue at the character after the newline.) *)
Fixpoint skipComment (l:list nat) : list nat :=
  match l with
  | [] => []
  | c :: rest => if c =? c_nl then rest else skipComment rest
  end.

Lemma skipComment_len : forall l, length (skipComment l) <= length l.
Proof.
  induction l as [|c rest IH]; simpl; [lia|].
  destruct (c =? c_nl); simpl; lia.
Qed.

(* Decoder state. *)
Inductive St := High | Low (hi:nat).

Equations? decodeS (s:St) (l:list nat) : (list nat * Status) by wf (length l) lt :=
  decodeS High [] := ([], Ok);
  decodeS (Low _) [] := ([], Trailing);
  decodeS High (c :: rest) :=
    if isComment c then decodeS High (skipComment rest)
    else if isSpace c then decodeS High rest
    else match nibble c with
         | None => ([], Unknown)
         | Some hi => decodeS (Low hi) rest
         end;
  decodeS (Low hi) (c :: rest) :=
    if isLowStop c then ([], Split)
    else match nibble c with
         | None => ([], Unknown)
         | Some lo => let '(out, st) := decodeS High rest in
                      (hi * 16 + lo :: out, st)
         end.
Proof.
  all: simpl in *; try lia.
  all: match goal with
       | [ |- context[length (skipComment ?l)] ] =>
           pose proof (skipComment_len l); lia
       end.
Qed.

Definition decode (l:list nat) : (list nat * Status) := decodeS High l.

(* Numeric status codes, matching the Error enum in hex0.c / core.s. *)
Definition statusCode (s:Status) : nat :=
  match s with Ok => 0 | Split => 3 | Trailing => 4 | Unknown => 5 end.

(* Behaviour of the bounded machine `core` with output capacity [cap]:
   capacity is checked just before each store, so if the decode would emit
   more than [cap] bytes, the machine stops with OutputShort (code 2) having
   written exactly the first [cap] bytes. Returns (status, output, out_len). *)
Definition coreSpec (input:list nat) (cap:nat) : (nat * list nat * nat) :=
  let '(bs, st) := decode input in
  if cap <? length bs
  then (2, firstn cap bs, cap)
  else (statusCode st, bs, length bs).
