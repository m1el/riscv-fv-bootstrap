(** * Faithful port of the hex1 grammar from HEX1.md, and its correspondence
    to the functional spec [scan1]/[emit1]/[decode1] (Spec1.v).

    This MIRRORS lean/Hex1/Grammar.lean theorem-for-theorem. See that file's
    header for the full plan:
      1. [Token]/[Lex] -- the LEXICAL grammar as an inductive relation, one
         constructor per HEX1.md production / lexical error class.
      2. [lexF] -- the executable lexer; soundness/completeness give totality
         and determinism.
      3. [collect]/[emitT] -- the prose "Semantics" section as primitive
         recursions over the token stream.
      4. [scan1_parses]/[emit1_parses]/[decode1_grammar]/[valid_coreSpec1] --
         the functional spec is exactly lexing + token semantics. *)

From Coq Require Import List Arith Lia Bool.
From Equations Require Import Equations.
Require Import Hex0Coq.Spec.
Require Import Hex0Coq.Grammar.
Require Import Hex0Coq.Spec1.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(** ** Small character lemmas (extending Grammar.v's).                 *)
(* ------------------------------------------------------------------ *)

(** A hex digit is not ':' (58 sits in the gap between '9'=57 and 'A'=65). *)
Lemma nibble_ne_colon : forall c v, nibble c = Some v -> (c =? c_colon) = false.
Proof.
  intros c v h. apply Nat.eqb_neq. unfold c_colon.
  destruct (nibble_range _ _ h); lia.
Qed.

(** A hex digit is not '%' (37 < '0'=48). *)
Lemma nibble_ne_pct : forall c v, nibble c = Some v -> (c =? c_pct) = false.
Proof.
  intros c v h. apply Nat.eqb_neq. unfold c_pct.
  destruct (nibble_range _ _ h); lia.
Qed.

(** A hex digit is not a hex1 stop character. *)
Lemma nibble_not_lowstop1 : forall c v, nibble c = Some v -> isLowStop1 c = false.
Proof.
  intros c v h. unfold isLowStop1.
  rewrite (nibble_not_lowstop _ _ h), (nibble_ne_colon _ _ h), (nibble_ne_pct _ _ h).
  reflexivity.
Qed.

Lemma colon_not_comment : isComment c_colon = false.
Proof. reflexivity. Qed.
Lemma colon_not_space : isSpace c_colon = false.
Proof. reflexivity. Qed.
Lemma pct_not_comment : isComment c_pct = false.
Proof. reflexivity. Qed.
Lemma pct_not_space : isSpace c_pct = false.
Proof. reflexivity. Qed.
Lemma pct_ne_colon : (c_pct =? c_colon) = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** The semantic token stream.                                      *)
(* ------------------------------------------------------------------ *)

(** Output-relevant tokens. <SPACING>/<COMMENT> produce none. *)
Inductive Token :=
  | Tbyte (hi lo : nat)
  | TlabelDef (l : nat)
  | TlabelRef (l : nat).

(* ------------------------------------------------------------------ *)
(** ** The lexical grammar (one constructor per production/error).     *)
(* ------------------------------------------------------------------ *)

(** [Lex inp toks st]: [inp] lexes into the token stream [toks], terminating
    with lexical status [st] ([Ok1] = the whole input is a <TOKEN>*; anything
    else = a run of tokens followed by one lexical error). The statuses
    [Dup1]/[Undef1] are NOT lexical: they live in the semantic layer. *)
Inductive Lex : list nat -> list Token -> Status1 -> Prop :=
  (** GRAMMAR ::=  (empty: zero tokens). *)
  | Lex_nil : Lex [] [] Ok1
  (** TOKEN ::= BYTE, BYTE ::= NIBBLE NIBBLE. *)
  | Lex_byte chi clo hi lo rest toks st :
      nibble chi = Some hi -> nibble clo = Some lo -> Lex rest toks st ->
      Lex (chi :: clo :: rest) (Tbyte hi lo :: toks) st
  (** TOKEN ::= SPACING. *)
  | Lex_spacing c rest toks st :
      isSpace c = true -> Lex rest toks st -> Lex (c :: rest) toks st
  (** TOKEN ::= COMMENT ::= (#|;) (~\n)* \n, newline-terminated. *)
  | Lex_commentNl c body rest toks st :
      isComment c = true -> (forall b, In b body -> b <> c_nl) ->
      Lex rest toks st -> Lex (c :: (body ++ c_nl :: rest)) toks st
  (** COMMENT ::= (#|;) (~\n)* EOF, EOF-terminated trailing comment. *)
  | Lex_commentEof c body :
      isComment c = true -> (forall b, In b body -> b <> c_nl) ->
      Lex (c :: body) [] Ok1
  (** TOKEN ::= LABELDEF ::= ":" <ANY_BYTE> -- the label byte is consumed
      unconditionally (any of the 256 values). *)
  | Lex_labelDef l rest toks st :
      Lex rest toks st -> Lex (c_colon :: l :: rest) (TlabelDef l :: toks) st
  (** TOKEN ::= LABELREF ::= "%" <ANY_BYTE>. *)
  | Lex_labelRef l rest toks st :
      Lex rest toks st -> Lex (c_pct :: l :: rest) (TlabelRef l :: toks) st
  (** error: char that starts no token. *)
  | Lex_errUnknownHigh c rest :
      isComment c = false -> isSpace c = false -> (c =? c_colon) = false ->
      (c =? c_pct) = false -> nibble c = None -> Lex (c :: rest) [] Unknown1
  (** error: high nibble then EOF. *)
  | Lex_errTrailing chi hi :
      nibble chi = Some hi -> Lex [chi] [] Trailing1
  (** error: high nibble then a stop character (hex1's seven). *)
  | Lex_errSplit chi clo hi rest :
      nibble chi = Some hi -> isLowStop1 clo = true ->
      Lex (chi :: clo :: rest) [] Split1
  (** error: high nibble then a non-nibble, non-stop char. *)
  | Lex_errUnknownLow chi clo hi rest :
      nibble chi = Some hi -> isLowStop1 clo = false -> nibble clo = None ->
      Lex (chi :: clo :: rest) [] Unknown1
  (** error: EOF right after ':'. *)
  | Lex_errTrailColon : Lex [c_colon] [] TrailTok1
  (** error: EOF right after '%'. *)
  | Lex_errTrailPct : Lex [c_pct] [] TrailTok1.

(* ------------------------------------------------------------------ *)
(** ** The executable lexer (same flat state machine as scan1/emit1).  *)
(* ------------------------------------------------------------------ *)

Equations? lexF (s:St1) (l:list nat) : (list Token * Status1) by wf (length l) lt :=
  lexF High1 [] := ([], Ok1);
  lexF (Low1 _) [] := ([], Trailing1);
  lexF Col1 [] := ([], TrailTok1);
  lexF Pct1 [] := ([], TrailTok1);
  lexF High1 (c :: rest) :=
    if isComment c then lexF High1 (skipComment rest)
    else if isSpace c then lexF High1 rest
    else if c =? c_colon then lexF Col1 rest
    else if c =? c_pct then lexF Pct1 rest
    else match nibble c with
         | None => ([], Unknown1)
         | Some hi => lexF (Low1 hi) rest
         end;
  lexF (Low1 hi) (c :: rest) :=
    if isLowStop1 c then ([], Split1)
    else match nibble c with
         | None => ([], Unknown1)
         | Some lo => let '(ts, st) := lexF High1 rest in
                      (Tbyte hi lo :: ts, st)
         end;
  lexF Col1 (lc :: rest) := let '(ts, st) := lexF High1 rest in
                            (TlabelDef lc :: ts, st);
  lexF Pct1 (lc :: rest) := let '(ts, st) := lexF High1 rest in
                            (TlabelRef lc :: ts, st).
Proof.
  all: simpl in *; try lia.
  all: match goal with
       | [ |- context[length (skipComment ?l)] ] =>
           pose proof (skipComment_len l); lia
       end.
Qed.

(* ------------------------------------------------------------------ *)
(** ** lexF unfolding lemmas (one per token class).                    *)
(* ------------------------------------------------------------------ *)

Lemma lexF_nil : lexF High1 [] = ([], Ok1).
Proof. now simp lexF. Qed.

Lemma lexF_comment c rest : isComment c = true ->
  lexF High1 (c :: rest) = lexF High1 (skipComment rest).
Proof. intros hc. simp lexF. rewrite hc. reflexivity. Qed.

Lemma lexF_spacing c rest : isComment c = false -> isSpace c = true ->
  lexF High1 (c :: rest) = lexF High1 rest.
Proof. intros hc hs. simp lexF. rewrite hc, hs. reflexivity. Qed.

Lemma lexF_colon rest : lexF High1 (c_colon :: rest) = lexF Col1 rest.
Proof. simp lexF. rewrite colon_not_comment, colon_not_space, Nat.eqb_refl. reflexivity. Qed.

Lemma lexF_pct rest : lexF High1 (c_pct :: rest) = lexF Pct1 rest.
Proof.
  simp lexF. rewrite pct_not_comment, pct_not_space, pct_ne_colon, Nat.eqb_refl.
  reflexivity.
Qed.

Lemma lexF_high c hi rest : nibble c = Some hi ->
  lexF High1 (c :: rest) = lexF (Low1 hi) rest.
Proof.
  intros hh. simp lexF.
  rewrite (nibble_not_comment _ _ hh), (nibble_not_space _ _ hh),
    (nibble_ne_colon _ _ hh), (nibble_ne_pct _ _ hh), hh.
  reflexivity.
Qed.

Lemma lexF_byte c lc hi lo rest :
  nibble c = Some hi -> isLowStop1 lc = false -> nibble lc = Some lo ->
  lexF High1 (c :: lc :: rest) =
    (Tbyte hi lo :: fst (lexF High1 rest), snd (lexF High1 rest)).
Proof.
  intros hh hls hl. rewrite (lexF_high _ _ _ hh). simp lexF. rewrite hls, hl.
  destruct (lexF High1 rest) as [ts st]. reflexivity.
Qed.

Lemma lexF_unknown_high c rest :
  isComment c = false -> isSpace c = false -> (c =? c_colon) = false ->
  (c =? c_pct) = false -> nibble c = None ->
  lexF High1 (c :: rest) = ([], Unknown1).
Proof. intros hc hs hcol hpct hn. simp lexF. rewrite hc, hs, hcol, hpct, hn. reflexivity. Qed.

Lemma lexF_trailing c hi : nibble c = Some hi -> lexF High1 [c] = ([], Trailing1).
Proof. intros hh. rewrite (lexF_high _ _ _ hh). now simp lexF. Qed.

Lemma lexF_split c lc hi rest : nibble c = Some hi -> isLowStop1 lc = true ->
  lexF High1 (c :: lc :: rest) = ([], Split1).
Proof. intros hh hls. rewrite (lexF_high _ _ _ hh). simp lexF. rewrite hls. reflexivity. Qed.

Lemma lexF_unknown_low c lc hi rest :
  nibble c = Some hi -> isLowStop1 lc = false -> nibble lc = None ->
  lexF High1 (c :: lc :: rest) = ([], Unknown1).
Proof. intros hh hls hl. rewrite (lexF_high _ _ _ hh). simp lexF. rewrite hls, hl. reflexivity. Qed.

Lemma lexF_labelDef lc rest :
  lexF High1 (c_colon :: lc :: rest) =
    (TlabelDef lc :: fst (lexF High1 rest), snd (lexF High1 rest)).
Proof.
  rewrite lexF_colon. simp lexF. destruct (lexF High1 rest) as [ts st]. reflexivity.
Qed.

Lemma lexF_labelRef lc rest :
  lexF High1 (c_pct :: lc :: rest) =
    (TlabelRef lc :: fst (lexF High1 rest), snd (lexF High1 rest)).
Proof.
  rewrite lexF_pct. simp lexF. destruct (lexF High1 rest) as [ts st]. reflexivity.
Qed.

Lemma lexF_trailColon : lexF High1 [c_colon] = ([], TrailTok1).
Proof. rewrite lexF_colon. now simp lexF. Qed.

Lemma lexF_trailPct : lexF High1 [c_pct] = ([], TrailTok1).
Proof. rewrite lexF_pct. now simp lexF. Qed.

(* ------------------------------------------------------------------ *)
(** ** Soundness and completeness of the lexical grammar.              *)
(* ------------------------------------------------------------------ *)

(** Soundness: whatever the grammar derives, the lexer computes. *)
Theorem lex_sound : forall inp toks st, Lex inp toks st -> lexF High1 inp = (toks, st).
Proof.
  intros inp toks st h. induction h.
  - exact lexF_nil.
  - rewrite (lexF_byte _ _ _ _ _ H (nibble_not_lowstop1 _ _ H0) H0), IHh. reflexivity.
  - rewrite (lexF_spacing _ _ (space_not_comment _ H) H). exact IHh.
  - rewrite (lexF_comment _ _ H), (skipComment_body _ _ H0). exact IHh.
  - rewrite (lexF_comment _ _ H), (skipComment_no_nl _ H0). exact lexF_nil.
  - rewrite lexF_labelDef, IHh. reflexivity.
  - rewrite lexF_labelRef, IHh. reflexivity.
  - exact (lexF_unknown_high _ _ H H0 H1 H2 H3).
  - exact (lexF_trailing _ _ H).
  - exact (lexF_split _ _ _ _ H H0).
  - exact (lexF_unknown_low _ _ _ _ H H0 H1).
  - exact lexF_trailColon.
  - exact lexF_trailPct.
Qed.

(** Completeness: every input is derivable, with exactly the lexer's tokens
    and status. *)
Theorem lex_complete : forall n inp, length inp <= n ->
  Lex inp (fst (lexF High1 inp)) (snd (lexF High1 inp)).
Proof.
  induction n as [|n IH]; intros inp hn.
  - assert (h0 : inp = []) by (destruct inp; simpl in hn; [reflexivity | lia]).
    subst inp. rewrite lexF_nil. exact Lex_nil.
  - destruct inp as [|c rest]; [ rewrite lexF_nil; exact Lex_nil |].
    assert (hrest : length rest <= n) by (simpl in hn; lia).
    destruct (isComment c) eqn:hcm.
    + rewrite (lexF_comment _ _ hcm).
      destruct (newline_split rest) as [(body & suf & hsplit & hbody) | hnone].
      * subst rest. rewrite (skipComment_body _ _ hbody).
        assert (hsuf : length suf <= n)
          by (rewrite length_app in hrest; simpl in hrest; lia).
        exact (Lex_commentNl _ _ _ _ _ hcm hbody (IH suf hsuf)).
      * rewrite (skipComment_no_nl _ hnone), lexF_nil.
        exact (Lex_commentEof _ _ hcm hnone).
    + destruct (isSpace c) eqn:hsp.
      * rewrite (lexF_spacing _ _ hcm hsp). exact (Lex_spacing _ _ _ _ hsp (IH rest hrest)).
      * destruct (c =? c_colon) eqn:hcol.
        { apply Nat.eqb_eq in hcol. subst c.
          destruct rest as [|lc rest'].
          - rewrite lexF_trailColon. exact Lex_errTrailColon.
          - assert (hrest' : length rest' <= n) by (simpl in hrest; lia).
            rewrite lexF_labelDef. exact (Lex_labelDef _ _ _ _ (IH rest' hrest')). }
        destruct (c =? c_pct) eqn:hpct.
        { apply Nat.eqb_eq in hpct. subst c.
          destruct rest as [|lc rest'].
          - rewrite lexF_trailPct. exact Lex_errTrailPct.
          - assert (hrest' : length rest' <= n) by (simpl in hrest; lia).
            rewrite lexF_labelRef. exact (Lex_labelRef _ _ _ _ (IH rest' hrest')). }
        destruct (nibble c) as [hi|] eqn:hn2.
        2: { rewrite (lexF_unknown_high _ _ hcm hsp hcol hpct hn2).
             exact (Lex_errUnknownHigh _ _ hcm hsp hcol hpct hn2). }
        destruct rest as [|clo rest'].
        { rewrite (lexF_trailing _ _ hn2). exact (Lex_errTrailing _ _ hn2). }
        destruct (isLowStop1 clo) eqn:hls.
        { rewrite (lexF_split _ _ _ _ hn2 hls). exact (Lex_errSplit _ _ _ _ hn2 hls). }
        destruct (nibble clo) as [lo|] eqn:hn3.
        2: { rewrite (lexF_unknown_low _ _ _ _ hn2 hls hn3).
             exact (Lex_errUnknownLow _ _ _ _ hn2 hls hn3). }
        rewrite (lexF_byte _ _ _ _ _ hn2 hls hn3).
        assert (hrest' : length rest' <= n) by (simpl in hrest; lia).
        exact (Lex_byte _ _ _ _ _ _ _ hn2 hn3 (IH rest' hrest')).
Qed.

(** Totality: every input lexes (valid or some lexical error). *)
Theorem lex_total : forall inp, exists toks st, Lex inp toks st.
Proof.
  intro inp. exists (fst (lexF High1 inp)), (snd (lexF High1 inp)).
  exact (lex_complete (length inp) inp (Nat.le_refl _)).
Qed.

(** Determinism: the grammar assigns unique tokens and status. *)
Theorem lex_det : forall inp t1 t2 s1 s2,
  Lex inp t1 s1 -> Lex inp t2 s2 -> t1 = t2 /\ s1 = s2.
Proof.
  intros inp t1 t2 s1 s2 h1 h2.
  pose proof (lex_sound _ _ _ h1) as e1. pose proof (lex_sound _ _ _ h2) as e2.
  rewrite e1 in e2. injection e2 as -> ->. auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Token semantics (the prose "Semantics" section of HEX1.md).     *)
(* ------------------------------------------------------------------ *)

(** Label collection: walk the token stream tracking the output position
    (<BYTE> = 1 byte, <LABELREF> = 4 bytes); bind each <LABELDEF> to the
    current position; stop at the first duplicate. Returns
    (labels, position reached, duplicate?). *)
Fixpoint collect (ts:list Token) (lab:Labels) (pos:nat) : (Labels * nat * bool) :=
  match ts with
  | [] => (lab, pos, false)
  | Tbyte _ _ :: ts' => collect ts' lab (pos + 1)
  | TlabelRef _ :: ts' => collect ts' lab (pos + 4)
  | TlabelDef l :: ts' =>
      match lab l with
      | Some _ => (lab, pos, true)
      | None => collect ts' (setLabel lab l pos) pos
      end
  end.

(** Emission: emit each <BYTE>; emit 4 offset bytes per <LABELREF>
    ([offBytes] = i32 LE of pos(label) - (field_pos + 4)); stop at the first
    reference to an unbound label. Returns (output, undefined-ref?). *)
Fixpoint emitT (ts:list Token) (lab:Labels) (pos:nat) : (list nat * bool) :=
  match ts with
  | [] => ([], false)
  | Tbyte hi lo :: ts' =>
      let '(out, u) := emitT ts' lab (pos + 1) in
      (hi * 16 + lo :: out, u)
  | TlabelDef _ :: ts' => emitT ts' lab pos
  | TlabelRef l :: ts' =>
      match lab l with
      | None => ([], true)
      | Some p => let '(out, u) := emitT ts' lab (pos + 4) in
                  (offBytes p pos ++ out, u)
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** The functional spec = lexing + token semantics.                 *)
(* ------------------------------------------------------------------ *)

(** Phase 1 against the grammar: [scan1] is [collect] over the lexed tokens;
    a duplicate label preempts the lexical status (it is detected earlier in
    the input -- labels are bound left to right), otherwise the lexical
    status stands. *)
Theorem scan1_parses : forall inp toks lst, Lex inp toks lst ->
  forall lab pos,
    scan1 High1 lab pos inp =
      (let '(lab', m, dup) := collect toks lab pos in
       (lab', m, if dup then Dup1 else lst)).
Proof.
  intros inp toks lst h. induction h; intros lab pos; simpl.
  - (* nil *) now simp scan1.
  - (* byte *)
    simp scan1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    simp scan1. rewrite (nibble_not_lowstop1 _ _ H0), H0.
    rewrite IHh. reflexivity.
  - (* spacing *)
    simp scan1. rewrite (space_not_comment _ H), H. apply IHh.
  - (* commentNl *)
    simp scan1. rewrite H, (skipComment_body _ _ H0). apply IHh.
  - (* commentEof *)
    simp scan1. rewrite H, (skipComment_no_nl _ H0). now simp scan1.
  - (* labelDef *)
    simp scan1. rewrite colon_not_comment, colon_not_space, Nat.eqb_refl.
    simp scan1.
    destruct (lab l) eqn:hL.
    + reflexivity.
    + apply IHh.
  - (* labelRef *)
    simp scan1. rewrite pct_not_comment, pct_not_space, pct_ne_colon, Nat.eqb_refl.
    apply IHh.
  - (* errUnknownHigh *)
    simp scan1. rewrite H, H0, H1, H2, H3. reflexivity.
  - (* errTrailing *)
    simp scan1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    now simp scan1.
  - (* errSplit *)
    simp scan1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    simp scan1. rewrite H0. reflexivity.
  - (* errUnknownLow *)
    simp scan1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    simp scan1. rewrite H0, H1. reflexivity.
  - (* errTrailColon *)
    simp scan1. rewrite colon_not_comment, colon_not_space, Nat.eqb_refl.
    now simp scan1.
  - (* errTrailPct *)
    simp scan1. rewrite pct_not_comment, pct_not_space, pct_ne_colon, Nat.eqb_refl.
    now simp scan1.
Qed.

(** Phase 2 against the grammar: [emit1] is [emitT] over the lexed tokens;
    an undefined reference preempts the lexical status, otherwise the lexical
    status stands. *)
Theorem emit1_parses : forall inp toks lst, Lex inp toks lst ->
  forall lab pos,
    emit1 High1 lab pos inp =
      (let '(out, u) := emitT toks lab pos in
       (out, if u then Undef1 else lst)).
Proof.
  intros inp toks lst h. induction h; intros lab pos; cbn [emitT].
  - now simp emit1.
  - (* byte *)
    simp emit1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    simp emit1. rewrite (nibble_not_lowstop1 _ _ H0), H0.
    rewrite IHh. destruct (emitT toks lab (pos + 1)) as [out u].
    destruct u; reflexivity.
  - simp emit1. rewrite (space_not_comment _ H), H. apply IHh.
  - simp emit1. rewrite H, (skipComment_body _ _ H0). apply IHh.
  - simp emit1. rewrite H, (skipComment_no_nl _ H0). now simp emit1.
  - (* labelDef *)
    simp emit1. rewrite colon_not_comment, colon_not_space, Nat.eqb_refl.
    apply IHh.
  - (* labelRef *)
    simp emit1. rewrite pct_not_comment, pct_not_space, pct_ne_colon, Nat.eqb_refl.
    destruct (lab l) eqn:hL.
    + rewrite IHh. destruct (emitT toks lab (pos + 4)) as [out u].
      destruct u; reflexivity.
    + reflexivity.
  - simp emit1. rewrite H, H0, H1, H2, H3. reflexivity.
  - simp emit1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    now simp emit1.
  - simp emit1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    simp emit1. rewrite H0. reflexivity.
  - simp emit1.
    rewrite (nibble_not_comment _ _ H), (nibble_not_space _ _ H),
      (nibble_ne_colon _ _ H), (nibble_ne_pct _ _ H), H.
    simp emit1. rewrite H0, H1. reflexivity.
  - simp emit1. rewrite colon_not_comment, colon_not_space, Nat.eqb_refl.
    now simp emit1.
  - simp emit1. rewrite pct_not_comment, pct_not_space, pct_ne_colon, Nat.eqb_refl.
    now simp emit1.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The headline: decode1 is exactly grammar lexing + semantics.    *)
(* ------------------------------------------------------------------ *)

(** Full grammar characterization of [decode1]. Error precedence is visible
    in the shape: a duplicate label (semantic, detected during the scan)
    beats the lexical status; the lexical status beats an undefined
    reference (semantic, detected during emission); emission output survives
    only when the scan was wholly clean. *)
Theorem decode1_grammar : forall inp toks lst, Lex inp toks lst ->
  decode1 inp =
    (let '(lab, m, dup) := collect toks noLabels 0 in
     if dup then ([], m, Dup1)
     else match lst with
          | Ok1 => let '(out, u) := emitT toks lab 0 in
                   (out, m, if u then Undef1 else Ok1)
          | e => ([], m, e)
          end).
Proof.
  intros inp toks lst h. unfold decode1.
  rewrite (scan1_parses _ _ _ h noLabels 0).
  destruct (collect toks noLabels 0) as [[lab' m] dup].
  destruct dup.
  - reflexivity.
  - destruct lst; try reflexivity.
    rewrite (emit1_parses _ _ _ h lab' 0).
    destruct (emitT toks lab' 0) as [out u]. destruct u; reflexivity.
Qed.

(** The valid fragment, end to end: a lexically-valid input with no duplicate
    labels and no undefined references, whose output fits, decodes Ok to the
    grammar's emission. *)
Theorem valid_coreSpec1 : forall inp toks lab m out cap,
  Lex inp toks Ok1 ->
  collect toks noLabels 0 = (lab, m, false) ->
  emitT toks lab 0 = (out, false) ->
  m <= cap ->
  coreSpec1 inp cap = (0, out, length out).
Proof.
  intros inp toks lab m out cap h hc he hcap. unfold coreSpec1.
  rewrite (decode1_grammar _ _ _ h), hc, he.
  destruct (cap <? m) eqn:hlt.
  - apply Nat.ltb_lt in hlt. lia.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Sanity examples (consistent with HEX1.md).                      *)
(* ------------------------------------------------------------------ *)

(** ":A 00 %A" lexes to labelDef A; byte 0 0; labelRef A. *)
Example lex_example_1 :
  Lex [58; 65; 32; 48; 48; 32; 37; 65]
      [TlabelDef 65; Tbyte 0 0; TlabelRef 65] Ok1.
Proof.
  apply (Lex_labelDef 65 _ _ _).
  apply (Lex_spacing 32 _ _ _); [reflexivity|].
  apply (Lex_byte 48 48 0 0 _ _ _); [reflexivity|reflexivity|].
  apply (Lex_spacing 32 _ _ _); [reflexivity|].
  apply (Lex_labelRef 65 _ _ _). exact Lex_nil.
Qed.

(** "4:": ':' is a stop character, so it splits a nibble (HEX1.md). *)
Example lex_example_2 : Lex [52; 58] [] Split1.
Proof. apply (Lex_errSplit 52 58 4 []); reflexivity. Qed.

(** ":" at EOF: TrailTok, distinct from hex0's taxonomy. *)
Example lex_example_3 : Lex [58] [] TrailTok1.
Proof. exact Lex_errTrailColon. Qed.

(** A comment hides ':'/'%' (they are comment text, not tokens). *)
Example lex_example_4 : Lex [59; 58; 65; 10] [] Ok1.
Proof.
  apply (Lex_commentNl 59 [58; 65] [] [] Ok1); [reflexivity| |exact Lex_nil].
  intros b hb. simpl in hb. destruct hb as [h|[h|[]]]; subst b; discriminate.
Qed.
