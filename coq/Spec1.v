(** * hex1 functional specification (the refinement target). Spec: HEX1.md.

    This is the SHARED spec: the Lean file Hex1/Spec.lean mirrors it
    definition-for-definition. Bytes are modelled as [nat] (assumed < 256);
    the input is a [list nat].

    hex1 = hex0 + single-character labels:
      [:c]  binds label [c] to the current output position (no repeats);
      [%c]  emits 4 bytes: (pos(c) - (field_pos + 4)) as a little-endian
            two's-complement i32 (end-relative, x86 rel32 convention).

    The spec is TWO capacity-free phases over the input, mirroring the
    two-pass implementations (hex1.c / bare/core1.s):

      [scan1] -- tokenization + label collection. Returns (labels, m, status)
                 where [m] is the virtual output length at the error site
                 (or the total output length when status = Ok1).
      [emit1] -- byte emission + reference resolution. Under a clean scan the
                 only reachable error is [Undef1].

    Both are flat one-character-per-step state machines over [St1]
    (High1 / Low1 hi / Col1 / Pct1), matching core1.s's control flow.

    Capacity is applied afterwards in [coreSpec1], like hex0's [coreSpec]:
    the machine's capacity-threaded pass 1 reports OutputShort iff [cap < m].
    (Error tokens emit nothing, so the first capacity-crossing token always
    strictly precedes the first scan-error token; hence the factorization is
    exact. See HEX1.md "Error precedence".) *)

From Coq Require Import List Arith Lia Bool ZArith.
From Equations Require Import Equations.
Require Import Hex0Coq.Spec.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(* New token-starting character codes. *)
Definition c_colon := 58.   (* ':' *)
Definition c_pct   := 37.   (* '%' *)

(* hex1 stop characters: hex0's five plus ':' and '%'. *)
Definition isLowStop1 (c:nat) : bool := isLowStop c || (c =? c_colon) || (c =? c_pct).

(* Terminal status of a decode (capacity-independent). *)
Inductive Status1 := Ok1 | Split1 | Trailing1 | Unknown1 | Dup1 | Undef1 | TrailTok1.

(* Numeric status codes, matching the Error enum in hex1.c / core1.s. *)
Definition statusCode1 (s:Status1) : nat :=
  match s with
  | Ok1 => 0 | Split1 => 3 | Trailing1 => 4 | Unknown1 => 5
  | Dup1 => 6 | Undef1 => 7 | TrailTok1 => 8
  end.

(* The label map: label byte |-> output position. *)
Definition Labels := nat -> option nat.

Definition noLabels : Labels := fun _ => None.

Definition setLabel (lab:Labels) (l pos:nat) : Labels :=
  fun x => if x =? l then Some pos else lab x.

(* Decoder state: expecting a high nibble / a low nibble (after high [hi]) /
   the label byte of a ':' definition / the label byte of a '%' reference. *)
Inductive St1 := High1 | Low1 (hi:nat) | Col1 | Pct1.

(* Phase 1 (scan): tokenize, collect label positions, track the virtual
   output position. Returns (labels, m, status); [m] is the output position
   reached when the scan stops (the error site's position, or the total).
   Mirrors [scan] in hex1.c statement-for-statement. *)
Equations? scan1 (s:St1) (lab:Labels) (pos:nat) (l:list nat)
    : (Labels * nat * Status1) by wf (length l) lt :=
  scan1 High1 lab pos [] := (lab, pos, Ok1);
  scan1 (Low1 _) lab pos [] := (lab, pos, Trailing1);
  scan1 Col1 lab pos [] := (lab, pos, TrailTok1);
  scan1 Pct1 lab pos [] := (lab, pos, TrailTok1);
  scan1 High1 lab pos (c :: rest) :=
    if isComment c then scan1 High1 lab pos (skipComment rest)
    else if isSpace c then scan1 High1 lab pos rest
    else if c =? c_colon then scan1 Col1 lab pos rest
    else if c =? c_pct then scan1 Pct1 lab pos rest
    else match nibble c with
         | None => (lab, pos, Unknown1)
         | Some hi => scan1 (Low1 hi) lab pos rest
         end;
  scan1 (Low1 _) lab pos (c :: rest) :=
    if isLowStop1 c then (lab, pos, Split1)
    else match nibble c with
         | None => (lab, pos, Unknown1)
         | Some _ => scan1 High1 lab (pos + 1) rest
         end;
  scan1 Col1 lab pos (lc :: rest) :=
    match lab lc with
    | Some _ => (lab, pos, Dup1)
    | None => scan1 High1 (setLabel lab lc pos) pos rest
    end;
  scan1 Pct1 lab pos (_ :: rest) := scan1 High1 lab (pos + 4) rest.
Proof.
  all: cbn [length]; try lia.
  all: match goal with
       | [ |- context[length (skipComment ?l)] ] =>
           pose proof (skipComment_len l); cbn [length]; lia
       end.
Qed.

(* The 4 little-endian bytes of the i32 relative offset [p - (pos + 4)]
   (label position [p], field position [pos]), reduced mod 2^32 (two's
   complement truncation; exact for outputs < 2 GiB).

   The byte arithmetic is done in [Z] and only the final (<256) bytes are
   converted to [nat]: the intermediate offset can be ~2^32, and a unary-
   [nat] value that size is uncomputable ([vm_compute] in Certify1.v would
   materialize 4e9 [S] constructors). Values are unchanged ([Z] div/mod on
   non-negatives = [nat] div/mod). *)
Definition offWord (p pos : nat) : nat :=
  Z.to_nat (((Z.of_nat p - (Z.of_nat pos + 4)) mod (2^32))%Z).
Definition offBytes (p pos : nat) : list nat :=
  let off := ((Z.of_nat p - (Z.of_nat pos + 4)) mod (2^32))%Z in
  [Z.to_nat (off mod 256)%Z; Z.to_nat (off / 2^8 mod 256)%Z;
   Z.to_nat (off / 2^16 mod 256)%Z; Z.to_nat (off / 2^24 mod 256)%Z].

(* Nat division/mod by large literals must never be unfolded by simpl/cbn:
   Nat.divmod recurses on the literal (2^24 deep) and overflows the stack. *)
Global Arguments offWord : simpl never.
Global Arguments offBytes : simpl never.

(* Phase 2 (emit): emit bytes and resolve references against the collected
   label map. Total (defined on all inputs); under a clean scan the only
   reachable stop is [Undef1] (or [Ok1] at EOF). [pos] is the output
   position = length of output emitted so far. Mirrors [emit] in hex1.c. *)
(* Phase-2 helpers: cons/append onto the first component of a result pair.
   (Equations' derivation stack-overflows on let-'(a,b) destructuring of the
   recursive call here; fst/snd projections elaborate fine and are
   definitionally equal.) *)
Definition consOut (b:nat) (r:list nat * Status1) : list nat * Status1 :=
  (b :: fst r, snd r).
Definition appOut (bs:list nat) (r:list nat * Status1) : list nat * Status1 :=
  (bs ++ fst r, snd r).

Equations? emit1 (s:St1) (lab:Labels) (pos:nat) (l:list nat)
    : (list nat * Status1) by wf (length l) lt :=
  emit1 High1 _ _ [] := ([], Ok1);
  emit1 (Low1 _) _ _ [] := ([], Trailing1);
  emit1 Col1 _ _ [] := ([], TrailTok1);
  emit1 Pct1 _ _ [] := ([], TrailTok1);
  emit1 High1 lab pos (c :: rest) :=
    if isComment c then emit1 High1 lab pos (skipComment rest)
    else if isSpace c then emit1 High1 lab pos rest
    else if c =? c_colon then emit1 Col1 lab pos rest
    else if c =? c_pct then emit1 Pct1 lab pos rest
    else match nibble c with
         | None => ([], Unknown1)
         | Some hi => emit1 (Low1 hi) lab pos rest
         end;
  emit1 (Low1 hi) lab pos (c :: rest) :=
    if isLowStop1 c then ([], Split1)
    else match nibble c with
         | None => ([], Unknown1)
         | Some lo => consOut (hi * 16 + lo) (emit1 High1 lab (pos + 1) rest)
         end;
  emit1 Col1 lab pos (_ :: rest) := emit1 High1 lab pos rest;
  emit1 Pct1 lab pos (lc :: rest) :=
    match lab lc with
    | None => ([], Undef1)
    | Some p => appOut (offBytes p pos) (emit1 High1 lab (pos + 4) rest)
    end.
Proof.
  all: cbn [length]; try lia.
  all: match goal with
       | [ |- context[length (skipComment ?l)] ] =>
           pose proof (skipComment_len l); cbn [length]; lia
       end.
Qed.

(* Capacity-free decode: (output bytes, scan length m, status).
   On a scan error the output is empty and the status is the scan's;
   otherwise the emit phase's output and status (Ok1 or Undef1). *)
Definition decode1 (inp:list nat) : (list nat * nat * Status1) :=
  let '(lab, m, st) := scan1 High1 noLabels 0 inp in
  match st with
  | Ok1 => let '(out, st') := emit1 High1 lab 0 inp in
           (out, m, st')
  | e => ([], m, e)
  end.

(* Behaviour of the bounded machine `core1` with output capacity [cap]:
   (status, output, out_len). Phase-1 errors (including OutputShort) write
   nothing; an undefined reference stops at the failing field. *)
Definition coreSpec1 (input:list nat) (cap:nat) : (nat * list nat * nat) :=
  let '(out, m, st) := decode1 input in
  if cap <? m then (2, [], 0)
  else match st with
       | Ok1    => (0, out, length out)
       | Undef1 => (7, out, length out)
       | e      => (statusCode1 e, [], 0)
       end.
