(** * Grammar.v -- faithful port of [Hex0/Grammar.lean].

    Faithful port of the hex0 grammar from [HEX0.md], and its correspondence to
    the functional spec [decodeS] ([Spec.v]). This is the Coq twin of the Lean
    file [lean/Hex0/Grammar.lean]; theorem-for-theorem the same.

    HEX0.md:
      GRAMMAR ::= <TOKEN>*
      TOKEN   ::= <BYTE> | <COMMENT> | <SPACING>
      BYTE    ::= <NIBBLE><NIBBLE>
      NIBBLE  ::= "0".."9" | "A".."F"
      COMMENT ::= ("#" | ";") (ALL_CHARS - "\n")* "\n"
      SPACING ::= " " | "_" | "\n"
      Each <BYTE> emits one output byte = high*16 + low.

    Plan (this file):
      1. [Valid inp out] -- the grammar as an inductive relation (the *valid*,
         error-free language), one constructor per production.
      2. [valid_ok] -- every valid program decodes to exactly [(out, Ok)].
      3. [Parse]/[parse_sound]/[parse_complete] -- the full grammar with errors,
         sound and complete w.r.t. [decodeS].
      4. Determinism, totality, and the valid/error partition. *)

From Coq Require Import List Arith Lia Bool.
From Equations Require Import Equations.
Require Import Hex0Coq.Spec.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(** ** Small spec lemmas (local; depend only on [Spec]).               *)
(* ------------------------------------------------------------------ *)

(** A nibble character lies in one of the two hex ranges. *)
Lemma nibble_range : forall c v, nibble c = Some v -> 48 <= c <= 57 \/ 65 <= c <= 70.
Proof.
  intros c v. unfold nibble.
  destruct (48 <=? c) eqn:E1; destruct (c <=? 57) eqn:E2;
  destruct (65 <=? c) eqn:E3; destruct (c <=? 70) eqn:E4;
  simpl; intro H; try discriminate;
  repeat match goal with
  | [ E : (_ <=? _) = true  |- _ ] => apply Nat.leb_le in E
  | [ E : (_ <=? _) = false |- _ ] => apply Nat.leb_gt in E
  end; lia.
Qed.

(** A hex digit is neither a comment nor a spacing char. *)
Lemma nibble_not_comment : forall c v, nibble c = Some v -> isComment c = false.
Proof.
  intros c v h. apply nibble_range in h.
  unfold isComment, c_hash, c_semi.
  apply orb_false_intro; apply Nat.eqb_neq; lia.
Qed.

Lemma nibble_not_space : forall c v, nibble c = Some v -> isSpace c = false.
Proof.
  intros c v h. apply nibble_range in h.
  unfold isSpace, c_nl, c_sp, c_us.
  apply orb_false_intro; [apply orb_false_intro|]; apply Nat.eqb_neq; lia.
Qed.

Lemma nibble_not_lowstop : forall c v, nibble c = Some v -> isLowStop c = false.
Proof.
  intros c v h. unfold isLowStop.
  rewrite (nibble_not_space c v h), (nibble_not_comment c v h). reflexivity.
Qed.

(** A spacing char is not a comment char. *)
Lemma space_not_comment : forall c, isSpace c = true -> isComment c = false.
Proof.
  intros c h. unfold isSpace, isComment, c_nl, c_sp, c_us, c_hash, c_semi in *.
  destruct (Nat.eqb_spec c 10); destruct (Nat.eqb_spec c 32); destruct (Nat.eqb_spec c 95);
    subst; simpl in *; try discriminate; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [decodeS] token-decomposition lemmas (one per token class).     *)
(* ------------------------------------------------------------------ *)

Lemma decodeS_nil : decodeS High [] = ([], Ok).
Proof. now simp decodeS. Qed.

Lemma decodeS_spacing c rest : isComment c = false -> isSpace c = true ->
  decodeS High (c :: rest) = decodeS High rest.
Proof. intros hc hs. simp decodeS. rewrite hc, hs. reflexivity. Qed.

Lemma decodeS_byte chi clo rest hi lo :
  isComment chi = false -> isSpace chi = false -> nibble chi = Some hi ->
  isLowStop clo = false -> nibble clo = Some lo ->
  decodeS High (chi :: clo :: rest) =
    ((hi * 16 + lo)%nat :: fst (decodeS High rest), snd (decodeS High rest)).
Proof.
  intros hc hs hh hlc hl. simp decodeS. rewrite hc, hs, hh. simp decodeS. rewrite hlc, hl.
  destruct (decodeS High rest) as [out st]. reflexivity.
Qed.

Lemma decodeS_comment c rest : isComment c = true ->
  decodeS High (c :: rest) = decodeS High (skipComment rest).
Proof. intros hc. simp decodeS. rewrite hc. reflexivity. Qed.

(** [skipComment] over a newline-free body terminated by a newline yields the tail. *)
Lemma skipComment_body body rest : (forall b, In b body -> b <> c_nl) ->
  skipComment (body ++ c_nl :: rest) = rest.
Proof.
  induction body as [|b bs IH]; intro h; cbn [skipComment app].
  - rewrite Nat.eqb_refl. reflexivity.
  - assert (hb : b <> c_nl) by (apply h; left; reflexivity).
    apply Nat.eqb_neq in hb. rewrite hb.
    apply IH. intros x hx. apply h. right. exact hx.
Qed.

(** [skipComment] over a newline-free list runs to the end (EOF-terminated comment). *)
Lemma skipComment_no_nl rest : (forall b, In b rest -> b <> c_nl) ->
  skipComment rest = [].
Proof.
  induction rest as [|b bs IH]; intro h; cbn [skipComment].
  - reflexivity.
  - assert (hb : b <> c_nl) by (apply h; left; reflexivity).
    apply Nat.eqb_neq in hb. rewrite hb.
    apply IH. intros x hx. apply h. right. exact hx.
Qed.

(** Every list either splits at its first newline, or contains none. *)
Lemma newline_split (l : list nat) :
  (exists body suf, l = body ++ c_nl :: suf /\ (forall b, In b body -> b <> c_nl))
  \/ (forall b, In b l -> b <> c_nl).
Proof.
  induction l as [|c rest IH].
  - right. intros b [].
  - destruct (Nat.eq_dec c c_nl) as [hc|hc].
    + left. exists [], rest. split; [ rewrite hc; reflexivity | intros b [] ].
    + destruct IH as [(body & suf & hsplit & hbody) | hnone].
      * left. exists (c :: body), suf. split.
        -- rewrite hsplit. reflexivity.
        -- intros x hx. destruct hx as [hx|hx]; [ subst x; exact hc | apply hbody; exact hx ].
      * right. intros x hx. destruct hx as [hx|hx]; [ subst x; exact hc | apply hnone; exact hx ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The valid (error-free) grammar.                                 *)
(* ------------------------------------------------------------------ *)

(** [Valid inp out]: [inp] is a well-formed [GRAMMAR] (a sequence of [TOKEN]s
    with no error) emitting output bytes [out]. One constructor per BNF
    production. *)
Inductive Valid : list nat -> list nat -> Prop :=
  (** [GRAMMAR ::= ] (empty: zero tokens). *)
  | Valid_nil : Valid [] []
  (** [TOKEN ::= BYTE], [BYTE ::= NIBBLE NIBBLE], emitting [hi*16+lo]. *)
  | Valid_byte chi clo hi lo rest out :
      nibble chi = Some hi -> nibble clo = Some lo -> Valid rest out ->
      Valid (chi :: clo :: rest) ((hi * 16 + lo) :: out)
  (** [TOKEN ::= SPACING], emitting nothing. *)
  | Valid_spacing c rest out :
      isSpace c = true -> Valid rest out -> Valid (c :: rest) out
  (** [TOKEN ::= COMMENT ::= (#|;) (¬\n)* \n], newline-terminated, emitting nothing. *)
  | Valid_commentNl c body rest out :
      isComment c = true -> (forall b, In b body -> b <> c_nl) -> Valid rest out ->
      Valid (c :: (body ++ c_nl :: rest)) out
  (** [COMMENT ::= (#|;) (¬\n)* EOF], EOF-terminated trailing comment (the last
      token; consumes the rest of the input), emitting nothing. *)
  | Valid_commentEof c body :
      isComment c = true -> (forall b, In b body -> b <> c_nl) -> Valid (c :: body) [].

(** **Soundness of the valid grammar**: every grammatically-valid program decodes
    to exactly its output bytes with terminal status [Ok]. *)
Theorem valid_ok : forall inp out, Valid inp out -> decodeS High inp = (out, Ok).
Proof.
  intros inp out h.
  induction h as [
    | chi clo hi lo rest out Hhi Hlo Hv IH
    | c rest out Hs Hv IH
    | c body rest out Hc Hbody Hv IH
    | c body Hc Hbody ].
  - apply decodeS_nil.
  - rewrite (decodeS_byte chi clo rest hi lo
      (nibble_not_comment _ _ Hhi) (nibble_not_space _ _ Hhi) Hhi
      (nibble_not_lowstop _ _ Hlo) Hlo).
    rewrite IH. reflexivity.
  - rewrite (decodeS_spacing c rest (space_not_comment _ Hs) Hs). exact IH.
  - rewrite (decodeS_comment c (body ++ c_nl :: rest) Hc).
    rewrite (skipComment_body body rest Hbody). exact IH.
  - rewrite (decodeS_comment c body Hc).
    rewrite (skipComment_no_nl body Hbody). apply decodeS_nil.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Error-side [decodeS] lemmas (one per HEX0.md error).            *)
(* ------------------------------------------------------------------ *)

(** Non-matching character at the start of <TOKEN> -> [Unknown]. *)
Lemma decodeS_unknown_high c rest : isComment c = false -> isSpace c = false ->
  nibble c = None -> decodeS High (c :: rest) = ([], Unknown).
Proof. intros hc hs hn. simp decodeS. rewrite hc, hs, hn. reflexivity. Qed.

(** <NIBBLE> followed by EOF -> [Trailing]. *)
Lemma decodeS_trailing chi hi : nibble chi = Some hi ->
  decodeS High (chi :: []) = ([], Trailing).
Proof.
  intros hh. simp decodeS.
  rewrite (nibble_not_comment _ _ hh), (nibble_not_space _ _ hh), hh.
  simp decodeS. reflexivity.
Qed.

(** <NIBBLE> followed by a token-starting (low-stop) char -> [Split]. *)
Lemma decodeS_split chi clo hi rest : nibble chi = Some hi -> isLowStop clo = true ->
  decodeS High (chi :: clo :: rest) = ([], Split).
Proof.
  intros hh hlc. simp decodeS.
  rewrite (nibble_not_comment _ _ hh), (nibble_not_space _ _ hh), hh.
  simp decodeS. rewrite hlc. reflexivity.
Qed.

(** <NIBBLE> followed by a non-nibble, non-stop ("non-matching") char -> [Unknown]. *)
Lemma decodeS_unknown_low chi clo hi rest : nibble chi = Some hi ->
  isLowStop clo = false -> nibble clo = None ->
  decodeS High (chi :: clo :: rest) = ([], Unknown).
Proof.
  intros hh hlc hl. simp decodeS.
  rewrite (nibble_not_comment _ _ hh), (nibble_not_space _ _ hh), hh.
  simp decodeS. rewrite hlc, hl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The full grammar *with errors*.

    [Parse inp out st] extends [Valid] with the HEX0.md error taxonomy: a run of
    valid tokens (emitting [out]) followed optionally by one error token (setting
    [st]). *)
(* ------------------------------------------------------------------ *)

Inductive Parse : list nat -> list nat -> Status -> Prop :=
  | Parse_ok : Parse [] [] Ok
  | Parse_byte chi clo hi lo rest out st :
      nibble chi = Some hi -> nibble clo = Some lo -> Parse rest out st ->
      Parse (chi :: clo :: rest) ((hi * 16 + lo) :: out) st
  | Parse_spacing c rest out st :
      isSpace c = true -> Parse rest out st -> Parse (c :: rest) out st
  | Parse_commentNl c body rest out st :
      isComment c = true -> (forall b, In b body -> b <> c_nl) -> Parse rest out st ->
      Parse (c :: (body ++ c_nl :: rest)) out st
  | Parse_commentEof c body :
      isComment c = true -> (forall b, In b body -> b <> c_nl) -> Parse (c :: body) [] Ok
  (** error: char that starts no token. *)
  | Parse_errUnknownHigh c rest :
      isComment c = false -> isSpace c = false -> nibble c = None ->
      Parse (c :: rest) [] Unknown
  (** error: high nibble then EOF. *)
  | Parse_errTrailing chi hi :
      nibble chi = Some hi -> Parse (chi :: []) [] Trailing
  (** error: high nibble then a token-starter (low-stop) char. *)
  | Parse_errSplit chi clo hi rest :
      nibble chi = Some hi -> isLowStop clo = true -> Parse (chi :: clo :: rest) [] Split
  (** error: high nibble then a non-nibble, non-stop char. *)
  | Parse_errUnknownLow chi clo hi rest :
      nibble chi = Some hi -> isLowStop clo = false -> nibble clo = None ->
      Parse (chi :: clo :: rest) [] Unknown.

(** **Soundness of the grammar with errors**: whatever the grammar derives, the
    spec computes -- output bytes and terminal status both. *)
Theorem parse_sound : forall inp out st, Parse inp out st -> decodeS High inp = (out, st).
Proof.
  intros inp out st h.
  induction h as [
    | chi clo hi lo rest out st Hhi Hlo Hp IH
    | c rest out st Hs Hp IH
    | c body rest out st Hc Hbody Hp IH
    | c body Hc Hbody
    | c rest Hc Hs Hn
    | chi hi Hh
    | chi clo hi rest Hh Hls
    | chi clo hi rest Hh Hls Hl ].
  - apply decodeS_nil.
  - rewrite (decodeS_byte chi clo rest hi lo
      (nibble_not_comment _ _ Hhi) (nibble_not_space _ _ Hhi) Hhi
      (nibble_not_lowstop _ _ Hlo) Hlo).
    rewrite IH. reflexivity.
  - rewrite (decodeS_spacing c rest (space_not_comment _ Hs) Hs). exact IH.
  - rewrite (decodeS_comment c (body ++ c_nl :: rest) Hc).
    rewrite (skipComment_body body rest Hbody). exact IH.
  - rewrite (decodeS_comment c body Hc).
    rewrite (skipComment_no_nl body Hbody). apply decodeS_nil.
  - apply (decodeS_unknown_high c rest Hc Hs Hn).
  - apply (decodeS_trailing chi hi Hh).
  - apply (decodeS_split chi clo hi rest Hh Hls).
  - apply (decodeS_unknown_low chi clo hi rest Hh Hls Hl).
Qed.

(** A valid program is the [Ok] fragment of the grammar with errors. *)
Theorem valid_to_parse : forall inp out, Valid inp out -> Parse inp out Ok.
Proof.
  intros inp out h.
  induction h as [
    | chi clo hi lo rest out Hhi Hlo Hv IH
    | c rest out Hs Hv IH
    | c body rest out Hc Hbody Hv IH
    | c body Hc Hbody ].
  - apply Parse_ok.
  - apply Parse_byte; assumption.
  - apply Parse_spacing; assumption.
  - apply (Parse_commentNl c body rest out Ok Hc Hbody IH).
  - apply Parse_commentEof; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Completeness / totality: the grammar covers every input.

    Every input is derivable in the grammar-with-errors, with exactly the output
    and status the spec computes. Combined with [parse_sound], this gives
    [decodeS High inp = (out, st) <-> Parse inp out st]. *)
(* ------------------------------------------------------------------ *)

Theorem parse_complete : forall n inp, length inp <= n ->
  Parse inp (fst (decodeS High inp)) (snd (decodeS High inp)).
Proof.
  induction n as [|n IHn]; intros inp Hn.
  - assert (Hnil : inp = []) by (destruct inp; [reflexivity | simpl in Hn; lia]).
    subst inp. rewrite decodeS_nil. cbn [fst snd]. apply Parse_ok.
  - destruct inp as [|c rest].
    + rewrite decodeS_nil. cbn [fst snd]. apply Parse_ok.
    + simpl in Hn. assert (Hrest : length rest <= n) by lia.
      destruct (isComment c) eqn:Hcm.
      * rewrite (decodeS_comment c rest Hcm).
        destruct (newline_split rest) as [(body & suf & Hsplit & Hbody) | Hnone].
        -- subst rest. rewrite (skipComment_body body suf Hbody).
           rewrite length_app in Hrest. simpl in Hrest.
           assert (Hsuf : length suf <= n) by lia.
           apply (Parse_commentNl c body suf _ _ Hcm Hbody (IHn suf Hsuf)).
        -- rewrite (skipComment_no_nl rest Hnone). rewrite decodeS_nil. cbn [fst snd].
           apply (Parse_commentEof c rest Hcm Hnone).
      * destruct (isSpace c) eqn:Hsp.
        -- rewrite (decodeS_spacing c rest Hcm Hsp).
           apply (Parse_spacing c rest _ _ Hsp (IHn rest Hrest)).
        -- destruct (nibble c) as [hi|] eqn:Hnb.
           ++ destruct rest as [|clo rest'].
              ** rewrite (decodeS_trailing c hi Hnb). cbn [fst snd].
                 apply (Parse_errTrailing c hi Hnb).
              ** destruct (isLowStop clo) eqn:Hls.
                 --- rewrite (decodeS_split c clo hi rest' Hnb Hls). cbn [fst snd].
                     apply (Parse_errSplit c clo hi rest' Hnb Hls).
                 --- destruct (nibble clo) as [lo|] eqn:Hnl.
                     +++ rewrite (decodeS_byte c clo rest' hi lo Hcm Hsp Hnb Hls Hnl).
                         cbn [fst snd].
                         simpl in Hrest. assert (Hrest' : length rest' <= n) by lia.
                         apply (Parse_byte c clo hi lo rest' _ _ Hnb Hnl (IHn rest' Hrest')).
                     +++ rewrite (decodeS_unknown_low c clo hi rest' Hnb Hls Hnl). cbn [fst snd].
                         apply (Parse_errUnknownLow c clo hi rest' Hnb Hls Hnl).
           ++ rewrite (decodeS_unknown_high c rest Hcm Hsp Hnb). cbn [fst snd].
              apply (Parse_errUnknownHigh c rest Hcm Hsp Hnb).
Qed.

(** **Totality**: every input is derivable in the grammar (valid or some error). *)
Theorem parse_total : forall inp, exists out st, Parse inp out st.
Proof.
  intros inp. exists (fst (decodeS High inp)), (snd (decodeS High inp)).
  apply (parse_complete (length inp) inp (le_n _)).
Qed.

(** **Determinism / non-intersection**: the grammar assigns a unique output and
    status to each input (so the valid and error derivations can never disagree). *)
Theorem parse_det : forall inp o1 o2 s1 s2,
  Parse inp o1 s1 -> Parse inp o2 s2 -> o1 = o2 /\ s1 = s2.
Proof.
  intros inp o1 o2 s1 s2 h1 h2.
  pose proof (parse_sound _ _ _ h1) as e1.
  pose proof (parse_sound _ _ _ h2) as e2.
  rewrite e1 in e2. injection e2 as Ho Hs. split; [exact Ho | exact Hs].
Qed.

(** An input is *valid* if it parses with status [Ok]. *)
Definition IsValid (inp : list nat) : Prop := exists out, Parse inp out Ok.
(** An input is *erroneous* if it parses with a non-[Ok] status. *)
Definition IsErr (inp : list nat) : Prop := exists out st, Parse inp out st /\ st <> Ok.

(** **Total partition**: every input is valid or erroneous. *)
Theorem valid_or_err : forall inp, IsValid inp \/ IsErr inp.
Proof.
  intros inp. destruct (parse_total inp) as (out & st & h).
  destruct st.
  - left. exists out. exact h.
  - right. exists out, Split. split; [exact h | discriminate].
  - right. exists out, Trailing. split; [exact h | discriminate].
  - right. exists out, Unknown. split; [exact h | discriminate].
Qed.

(** **Disjoint partition**: no input is both valid and erroneous. *)
Theorem not_valid_and_err : forall inp, ~ (IsValid inp /\ IsErr inp).
Proof.
  intros inp [(o1 & h1) (o2 & st & h2 & hst)].
  apply hst. exact (proj2 (parse_det _ _ _ _ _ h2 h1)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Sanity examples (consistent with HEX0.md).                      *)
(* ------------------------------------------------------------------ *)

(** An EOF-terminated comment is a valid program ([COMMENT ::= ... (\n|EOF)]). *)
Example valid_hash : Valid [c_hash] [].
Proof. apply (Valid_commentEof c_hash []); [ reflexivity | intros b [] ]. Qed.

(** The two nibble error classes are genuinely distinct: a nibble + a stop char
    ("_") is [Split]; a nibble + other garbage ("G") is [Unknown]. *)
Theorem split_vs_unknown_distinct :
  decodeS High [48; c_us] = ([], Split) /\ decodeS High [48; 71] = ([], Unknown).
Proof.
  split.
  - apply (decodeS_split 48 c_us 0 []); reflexivity.
  - apply (decodeS_unknown_low 48 71 0 []); reflexivity.
Qed.
