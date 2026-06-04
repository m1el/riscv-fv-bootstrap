/-
  Faithful port of the hex1 grammar from `HEX1.md`, and its correspondence to
  the functional spec `scan1`/`emit1`/`decode1` (`Hex1/Spec.lean`).

  HEX1.md:
    GRAMMAR  ::= <TOKEN>*
    TOKEN    ::= <BYTE> | <COMMENT> | <SPACING> | <LABELDEF> | <LABELREF>
    BYTE     ::= <NIBBLE><NIBBLE>
    NIBBLE   ::= "0".."9" | "A".."F"
    COMMENT  ::= ("#" | ";") (ALL_CHARS - "\n")* ("\n" | EOF)
    SPACING  ::= " " | "_" | "\n"
    LABELDEF ::= ":" <ANY_BYTE>
    LABELREF ::= "%" <ANY_BYTE>
  Each <BYTE> emits one byte; <LABELDEF> binds its label to the current output
  position (no repeats); <LABELREF> emits 4 bytes (i32 LE, end-relative).

  Plan (this file):
    1. `Token` / `Lex inp toks st` — the LEXICAL grammar as an inductive
       relation, one constructor per production and per lexical error class.
       Spacing and comments produce no token; the semantic token stream is
       <BYTE>/<LABELDEF>/<LABELREF> only. The statuses `Dup`/`Undef` are NOT
       lexical: they appear in the *semantic* layer below.
    2. `lexF` — the executable lexer; `lex_sound`/`lex_complete` give
       totality and determinism of the grammar.
    3. `collect`/`emitT` — the prose "Semantics" section of HEX1.md as
       primitive recursions over the token stream: label collection (with
       duplicate detection) and emission (with undefined-reference
       detection).
    4. `scan1_parses`/`emit1_parses`/`decode1_grammar` — the functional spec
       is exactly lexing + token semantics; error precedence (`Dup` cuts the
       scan; phase-1 statuses beat `Undef`) falls out of the composition.
-/
import Hex0.Grammar
import Hex1.Spec

namespace Hex1
open Hex0 (c_nl isSpace isComment nibble skipComment)

/-! ## Small character lemmas (extending Hex0/Grammar's). -/

/-- A hex digit lies in `'0'..'9'` or `'A'..'F'`. -/
theorem nibble_range {c v : Nat} (h : nibble c = some v) :
    (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) := by
  simp only [nibble] at h
  by_cases hd : 48 ≤ c ∧ c ≤ 57
  · exact Or.inl hd
  · rw [if_neg hd] at h
    by_cases hl : 65 ≤ c ∧ c ≤ 70
    · exact Or.inr hl
    · rw [if_neg hl] at h; exact absurd h (by simp)

/-- A hex digit is not `':'` (58 sits in the gap between '9'=57 and 'A'=65). -/
theorem nibble_ne_colon {c v : Nat} (h : nibble c = some v) : (c == c_colon) = false := by
  rcases nibble_range h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [c_colon, beq_eq_false_iff_ne] <;> omega

/-- A hex digit is not `'%'` (37 < '0'=48). -/
theorem nibble_ne_pct {c v : Nat} (h : nibble c = some v) : (c == c_pct) = false := by
  rcases nibble_range h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [c_pct, beq_eq_false_iff_ne] <;> omega

/-- A hex digit is not a hex1 stop character. -/
theorem nibble_not_lowstop1 {c v : Nat} (h : nibble c = some v) : isLowStop c = false := by
  simp only [isLowStop, Hex0.nibble_not_lowstop h, nibble_ne_colon h, nibble_ne_pct h,
    Bool.or_self]

/-- A spacing char is not `':'` or `'%'`. -/
theorem space_ne_colon {c : Nat} (h : isSpace c = true) : (c == c_colon) = false := by
  simp only [isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, beq_iff_eq, Bool.or_eq_true] at h
  simp only [c_colon, beq_eq_false_iff_ne]; omega

theorem space_ne_pct {c : Nat} (h : isSpace c = true) : (c == c_pct) = false := by
  simp only [isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, beq_iff_eq, Bool.or_eq_true] at h
  simp only [c_pct, beq_eq_false_iff_ne]; omega

/-! ## The semantic token stream. -/

/-- Output-relevant tokens. `<SPACING>`/`<COMMENT>` produce none. -/
inductive Token where
  | byte (hi lo : Nat)
  | labelDef (l : Nat)
  | labelRef (l : Nat)
deriving Repr, DecidableEq

/-! ## The lexical grammar (one constructor per HEX1.md production/error). -/

/-- `Lex inp toks st`: `inp` lexes into the token stream `toks`, terminating
    with lexical status `st` (`Ok` = the whole input is a `<TOKEN>*`; anything
    else = a run of tokens followed by one lexical error). -/
inductive Lex : List Nat → List Token → Status → Prop
  /-- `GRAMMAR ::= ` (empty: zero tokens). -/
  | nil : Lex [] [] .Ok
  /-- `TOKEN ::= BYTE`, `BYTE ::= NIBBLE NIBBLE`. -/
  | byte {chi clo hi lo : Nat} {rest : List Nat} {toks : List Token} {st : Status} :
      nibble chi = some hi → nibble clo = some lo → Lex rest toks st →
      Lex (chi :: clo :: rest) (.byte hi lo :: toks) st
  /-- `TOKEN ::= SPACING`. -/
  | spacing {c : Nat} {rest : List Nat} {toks : List Token} {st : Status} :
      isSpace c = true → Lex rest toks st → Lex (c :: rest) toks st
  /-- `TOKEN ::= COMMENT ::= (#|;) (¬\n)* \n`, newline-terminated. -/
  | commentNl {c : Nat} {body rest : List Nat} {toks : List Token} {st : Status} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Lex rest toks st →
      Lex (c :: (body ++ c_nl :: rest)) toks st
  /-- `COMMENT ::= (#|;) (¬\n)* EOF`, EOF-terminated trailing comment. -/
  | commentEof {c : Nat} {body : List Nat} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Lex (c :: body) [] .Ok
  /-- `TOKEN ::= LABELDEF ::= ":" <ANY_BYTE>` — the label byte is consumed
      unconditionally (any of the 256 values). -/
  | labelDef {l : Nat} {rest : List Nat} {toks : List Token} {st : Status} :
      Lex rest toks st → Lex (c_colon :: l :: rest) (.labelDef l :: toks) st
  /-- `TOKEN ::= LABELREF ::= "%" <ANY_BYTE>`. -/
  | labelRef {l : Nat} {rest : List Nat} {toks : List Token} {st : Status} :
      Lex rest toks st → Lex (c_pct :: l :: rest) (.labelRef l :: toks) st
  /-- error: char that starts no token. -/
  | errUnknownHigh {c : Nat} {rest : List Nat} :
      isComment c = false → isSpace c = false → (c == c_colon) = false →
      (c == c_pct) = false → nibble c = none → Lex (c :: rest) [] .Unknown
  /-- error: high nibble then EOF. -/
  | errTrailing {chi hi : Nat} :
      nibble chi = some hi → Lex [chi] [] .Trailing
  /-- error: high nibble then a stop character (hex1's seven). -/
  | errSplit {chi clo hi : Nat} {rest : List Nat} :
      nibble chi = some hi → isLowStop clo = true → Lex (chi :: clo :: rest) [] .Split
  /-- error: high nibble then a non-nibble, non-stop char. -/
  | errUnknownLow {chi clo hi : Nat} {rest : List Nat} :
      nibble chi = some hi → isLowStop clo = false → nibble clo = none →
      Lex (chi :: clo :: rest) [] .Unknown
  /-- error: EOF right after `:`. -/
  | errTrailColon : Lex [c_colon] [] .TrailTok
  /-- error: EOF right after `%`. -/
  | errTrailPct : Lex [c_pct] [] .TrailTok

/-! ## The executable lexer (same flat state machine as `scan1`/`emit1`). -/

def lexF : St1 → List Nat → (List Token × Status)
  | .High, [] => ([], .Ok)
  | .Low _, [] => ([], .Trailing)
  | .Col, [] => ([], .TrailTok)
  | .Pct, [] => ([], .TrailTok)
  | .High, c :: rest =>
      if isComment c then lexF .High (skipComment rest)
      else if isSpace c then lexF .High rest
      else if c == c_colon then lexF .Col rest
      else if c == c_pct then lexF .Pct rest
      else match nibble c with
           | none => ([], .Unknown)
           | some hi => lexF (.Low hi) rest
  | .Low hi, c :: rest =>
      if isLowStop c then ([], .Split)
      else match nibble c with
           | none => ([], .Unknown)
           | some lo =>
               let (ts, st) := lexF .High rest
               (.byte hi lo :: ts, st)
  | .Col, l :: rest =>
      let (ts, st) := lexF .High rest
      (.labelDef l :: ts, st)
  | .Pct, l :: rest =>
      let (ts, st) := lexF .High rest
      (.labelRef l :: ts, st)
  termination_by _ l => l.length
  decreasing_by
    all_goals simp_wf
    · have h := Hex0.skipComment_len rest; omega
    all_goals omega

/-! ## `lexF` unfolding lemmas (one per token class). -/

theorem lexF_comment (c : Nat) (rest : List Nat) (hc : isComment c = true) :
    lexF .High (c :: rest) = lexF .High (skipComment rest) := by
  rw [lexF]; simp [hc]

theorem lexF_spacing (c : Nat) (rest : List Nat)
    (hc : isComment c = false) (hs : isSpace c = true) :
    lexF .High (c :: rest) = lexF .High rest := by
  rw [lexF]; simp [hc, hs]

theorem lexF_colon (rest : List Nat) :
    lexF .High (c_colon :: rest) = lexF .Col rest := by
  rw [lexF]; simp [isComment, isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Hex0.c_hash,
    Hex0.c_semi, c_colon]

theorem lexF_pct (rest : List Nat) :
    lexF .High (c_pct :: rest) = lexF .Pct rest := by
  rw [lexF]; simp [isComment, isSpace, Hex0.c_nl, Hex0.c_sp, Hex0.c_us, Hex0.c_hash,
    Hex0.c_semi, c_colon, c_pct]

theorem lexF_high (c hi : Nat) (rest : List Nat) (hh : nibble c = some hi) :
    lexF .High (c :: rest) = lexF (.Low hi) rest := by
  rw [lexF]; simp [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh,
    nibble_ne_colon hh, nibble_ne_pct hh, hh]

theorem lexF_byte (c l hi lo : Nat) (rest : List Nat)
    (hh : nibble c = some hi) (hls : isLowStop l = false) (hl : nibble l = some lo) :
    lexF .High (c :: l :: rest) =
      ((.byte hi lo) :: (lexF .High rest).1, (lexF .High rest).2) := by
  rw [lexF_high c hi _ hh, lexF]; simp [hls, hl]

theorem lexF_unknown_high (c : Nat) (rest : List Nat)
    (hc : isComment c = false) (hs : isSpace c = false) (hcol : (c == c_colon) = false)
    (hpct : (c == c_pct) = false) (hn : nibble c = none) :
    lexF .High (c :: rest) = ([], .Unknown) := by
  rw [lexF]; simp [hc, hs, hcol, hpct, hn]

theorem lexF_trailing (c hi : Nat) (hh : nibble c = some hi) :
    lexF .High [c] = ([], .Trailing) := by
  rw [lexF_high c hi _ hh, lexF]

theorem lexF_split (c l hi : Nat) (rest : List Nat)
    (hh : nibble c = some hi) (hls : isLowStop l = true) :
    lexF .High (c :: l :: rest) = ([], .Split) := by
  rw [lexF_high c hi _ hh, lexF]; simp [hls]

theorem lexF_unknown_low (c l hi : Nat) (rest : List Nat)
    (hh : nibble c = some hi) (hls : isLowStop l = false) (hl : nibble l = none) :
    lexF .High (c :: l :: rest) = ([], .Unknown) := by
  rw [lexF_high c hi _ hh, lexF]; simp [hls, hl]

theorem lexF_labelDef (l : Nat) (rest : List Nat) :
    lexF .High (c_colon :: l :: rest) =
      ((.labelDef l) :: (lexF .High rest).1, (lexF .High rest).2) := by
  rw [lexF_colon, lexF]

theorem lexF_labelRef (l : Nat) (rest : List Nat) :
    lexF .High (c_pct :: l :: rest) =
      ((.labelRef l) :: (lexF .High rest).1, (lexF .High rest).2) := by
  rw [lexF_pct, lexF]

theorem lexF_trailColon : lexF .High [c_colon] = ([], .TrailTok) := by
  rw [lexF_colon, lexF]

theorem lexF_trailPct : lexF .High [c_pct] = ([], .TrailTok) := by
  rw [lexF_pct, lexF]

theorem lexF_nil : lexF .High [] = ([], .Ok) := by rw [lexF]

/-! ## Soundness and completeness of the lexical grammar. -/

/-- **Soundness**: whatever the grammar derives, the lexer computes. -/
theorem lex_sound {inp : List Nat} {toks : List Token} {st : Status}
    (h : Lex inp toks st) : lexF .High inp = (toks, st) := by
  induction h with
  | nil => exact lexF_nil
  | @byte chi clo hi lo rest toks st hh hl _ ih =>
    rw [lexF_byte chi clo hi lo rest hh (nibble_not_lowstop1 hl) hl, ih]
  | @spacing c rest toks st hs _ ih =>
    rw [lexF_spacing c rest (Hex0.space_not_comment hs) hs, ih]
  | @commentNl c body rest toks st hc hbody _ ih =>
    rw [lexF_comment c _ hc, Hex0.skipComment_body body rest hbody, ih]
  | @commentEof c body hc hbody =>
    rw [lexF_comment c _ hc, Hex0.skipComment_no_nl body hbody, lexF_nil]
  | @labelDef l rest toks st _ ih => rw [lexF_labelDef, ih]
  | @labelRef l rest toks st _ ih => rw [lexF_labelRef, ih]
  | errUnknownHigh hc hs hcol hpct hn => exact lexF_unknown_high _ _ hc hs hcol hpct hn
  | errTrailing hh => exact lexF_trailing _ _ hh
  | errSplit hh hls => exact lexF_split _ _ _ _ hh hls
  | errUnknownLow hh hls hl => exact lexF_unknown_low _ _ _ _ hh hls hl
  | errTrailColon => exact lexF_trailColon
  | errTrailPct => exact lexF_trailPct

/-- **Completeness**: every input is derivable, with exactly the lexer's
    tokens and status. -/
theorem lex_complete : ∀ (n : Nat) (inp : List Nat), inp.length ≤ n →
    Lex inp (lexF .High inp).1 (lexF .High inp).2 := by
  intro n
  induction n with
  | zero =>
    intro inp hn
    have h0 : inp = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    subst h0; rw [lexF_nil]; exact .nil
  | succ n ih =>
    intro inp hn
    cases inp with
    | nil => rw [lexF_nil]; exact .nil
    | cons c rest =>
      have hrest : rest.length ≤ n := by simp only [List.length_cons] at hn; omega
      cases hcm : isComment c with
      | true =>
        rw [lexF_comment c rest hcm]
        rcases Hex0.newline_split rest with ⟨body, suf, hsplit, hbody⟩ | hnone
        · subst hsplit
          rw [Hex0.skipComment_body body suf hbody]
          have hsuf : suf.length ≤ n := by
            simp only [List.length_append, List.length_cons] at hrest; omega
          exact Lex.commentNl hcm hbody (ih suf hsuf)
        · rw [Hex0.skipComment_no_nl rest hnone, lexF_nil]
          exact Lex.commentEof hcm hnone
      | false =>
        cases hsp : isSpace c with
        | true => rw [lexF_spacing c rest hcm hsp]; exact Lex.spacing hsp (ih rest hrest)
        | false =>
          cases hcol : c == c_colon with
          | true =>
            have hc : c = c_colon := beq_iff_eq.mp hcol
            subst hc
            cases rest with
            | nil => rw [lexF_trailColon]; exact .errTrailColon
            | cons l rest' =>
              have hrest' : rest'.length ≤ n := by
                simp only [List.length_cons] at hrest; omega
              rw [lexF_labelDef]; exact Lex.labelDef (ih rest' hrest')
          | false =>
            cases hpct : c == c_pct with
            | true =>
              have hc : c = c_pct := beq_iff_eq.mp hpct
              subst hc
              cases rest with
              | nil => rw [lexF_trailPct]; exact .errTrailPct
              | cons l rest' =>
                have hrest' : rest'.length ≤ n := by
                  simp only [List.length_cons] at hrest; omega
                rw [lexF_labelRef]; exact Lex.labelRef (ih rest' hrest')
            | false =>
              cases hn2 : nibble c with
              | none =>
                rw [lexF_unknown_high c rest hcm hsp hcol hpct hn2]
                exact Lex.errUnknownHigh hcm hsp hcol hpct hn2
              | some hi =>
                cases rest with
                | nil => rw [lexF_trailing c hi hn2]; exact Lex.errTrailing hn2
                | cons clo rest' =>
                  cases hls : isLowStop clo with
                  | true => rw [lexF_split c clo hi rest' hn2 hls]; exact Lex.errSplit hn2 hls
                  | false =>
                    cases hn3 : nibble clo with
                    | none =>
                      rw [lexF_unknown_low c clo hi rest' hn2 hls hn3]
                      exact Lex.errUnknownLow hn2 hls hn3
                    | some lo =>
                      rw [lexF_byte c clo hi lo rest' hn2 hls hn3]
                      have hrest' : rest'.length ≤ n := by
                        simp only [List.length_cons] at hrest; omega
                      exact Lex.byte hn2 hn3 (ih rest' hrest')

/-- **Totality**: every input lexes (valid or some lexical error). -/
theorem lex_total (inp : List Nat) : ∃ toks st, Lex inp toks st :=
  ⟨_, _, lex_complete inp.length inp (Nat.le_refl _)⟩

/-- **Determinism**: the grammar assigns unique tokens and status. -/
theorem lex_det {inp : List Nat} {t1 t2 : List Token} {s1 s2 : Status}
    (h1 : Lex inp t1 s1) (h2 : Lex inp t2 s2) : t1 = t2 ∧ s1 = s2 := by
  have e := (lex_sound h1).symm.trans (lex_sound h2)
  injection e with ht hs; exact ⟨ht, hs⟩

/-! ## Token semantics (the prose "Semantics" section of HEX1.md). -/

/-- Label collection: walk the token stream tracking the output position
    (`<BYTE>` = 1 byte, `<LABELREF>` = 4 bytes); bind each `<LABELDEF>` to the
    current position; stop at the first duplicate. Returns
    (labels, position reached, duplicate?). -/
def collect : List Token → Labels → Nat → (Labels × Nat × Bool)
  | [], lab, pos => (lab, pos, false)
  | .byte _ _ :: ts, lab, pos => collect ts lab (pos + 1)
  | .labelRef _ :: ts, lab, pos => collect ts lab (pos + 4)
  | .labelDef l :: ts, lab, pos =>
      match lab l with
      | some _ => (lab, pos, true)
      | none => collect ts (setLabel lab l pos) pos

/-- Emission: emit each `<BYTE>`; emit 4 offset bytes per `<LABELREF>`
    (`offBytes` = i32 LE of `pos(label) − (field_pos + 4)`); stop at the first
    reference to an unbound label. Returns (output, undefined-ref?). -/
def emitT : List Token → Labels → Nat → (List Nat × Bool)
  | [], _, _ => ([], false)
  | .byte hi lo :: ts, lab, pos =>
      let (out, u) := emitT ts lab (pos + 1)
      ((hi * 16 + lo) :: out, u)
  | .labelDef _ :: ts, lab, pos => emitT ts lab pos
  | .labelRef l :: ts, lab, pos =>
      match lab l with
      | none => ([], true)
      | some p =>
          let (out, u) := emitT ts lab (pos + 4)
          (offBytes p pos ++ out, u)

/-! ## The functional spec = lexing + token semantics. -/

/-- Phase 1 against the grammar: `scan1` is `collect` over the lexed tokens;
    a duplicate label preempts the lexical status (it is detected earlier in
    the input — labels are bound left to right), otherwise the lexical status
    stands. -/
theorem scan1_parses {inp : List Nat} {toks : List Token} {lst : Status}
    (h : Lex inp toks lst) : ∀ (lab : Labels) (pos : Nat),
    scan1 .High lab pos inp =
      (match collect toks lab pos with
       | (lab', m, true) => (lab', m, .Dup)
       | (lab', m, false) => (lab', m, lst)) := by
  induction h with
  | nil => intro lab pos; rw [scan1]; rfl
  | @byte chi clo hi lo rest toks st hh hl _ ih =>
    intro lab pos
    rw [scan1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [scan1]
    simp only [nibble_not_lowstop1 hl, hl, Bool.false_eq_true, if_false]
    rw [ih lab (pos + 1)]; rfl
  | @spacing c rest toks st hs _ ih =>
    intro lab pos
    rw [scan1]
    simp only [Hex0.space_not_comment hs, hs, Bool.false_eq_true, if_false, if_true]
    exact ih lab pos
  | @commentNl c body rest toks st hc hbody _ ih =>
    intro lab pos
    rw [scan1]
    simp only [hc, if_true, Hex0.skipComment_body body rest hbody]
    exact ih lab pos
  | @commentEof c body hc hbody =>
    intro lab pos
    rw [scan1]
    simp only [hc, if_true, Hex0.skipComment_no_nl body hbody]
    rw [scan1]; rfl
  | @labelDef l rest toks st _ ih =>
    intro lab pos
    rw [scan1]
    simp only [show isComment c_colon = false by decide, show isSpace c_colon = false by decide,
      beq_self_eq_true, Bool.false_eq_true, if_false, if_true]
    rw [scan1]
    cases h : lab l with
    | some p => simp only [collect, h]
    | none => simp only [collect, h]; exact ih _ pos
  | @labelRef l rest toks st _ ih =>
    intro lab pos
    rw [scan1]
    simp only [show isComment c_pct = false by decide, show isSpace c_pct = false by decide,
      show (c_pct == c_colon) = false by decide, beq_self_eq_true, Bool.false_eq_true,
      if_false, if_true]
    rw [scan1]
    simp only [collect]
    exact ih lab (pos + 4)
  | errUnknownHigh hc hs hcol hpct hn =>
    intro lab pos
    rw [scan1]; simp [hc, hs, hcol, hpct, hn, collect]
  | errTrailing hh =>
    intro lab pos
    rw [scan1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [scan1]; rfl
  | @errSplit chi clo hi rest hh hls =>
    intro lab pos
    rw [scan1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [scan1]
    rw [if_pos hls]
    simp [collect]
  | @errUnknownLow chi clo hi rest hh hls hl =>
    intro lab pos
    rw [scan1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [scan1]
    rw [if_neg (by simp [hls])]
    simp [hl, collect]
  | errTrailColon =>
    intro lab pos
    rw [scan1]
    simp only [show isComment c_colon = false by decide, show isSpace c_colon = false by decide,
      beq_self_eq_true, Bool.false_eq_true, if_false, if_true]
    rw [scan1]
    simp [collect]
  | errTrailPct =>
    intro lab pos
    rw [scan1]
    simp only [show isComment c_pct = false by decide, show isSpace c_pct = false by decide,
      show (c_pct == c_colon) = false by decide, beq_self_eq_true, Bool.false_eq_true,
      if_false, if_true]
    rw [scan1]
    simp [collect]

/-- Phase 2 against the grammar: `emit1` is `emitT` over the lexed tokens;
    an undefined reference preempts the lexical status, otherwise the lexical
    status stands. (Outside `decode1` this holds for ALL inputs, including
    lexically-erroneous ones: `emit1` emits the bytes of the tokens before
    the lexical error and then reports it.) -/
theorem emit1_parses {inp : List Nat} {toks : List Token} {lst : Status}
    (h : Lex inp toks lst) : ∀ (lab : Labels) (pos : Nat),
    emit1 .High lab pos inp =
      (match emitT toks lab pos with
       | (out, true) => (out, .Undef)
       | (out, false) => (out, lst)) := by
  induction h with
  | nil => intro lab pos; rw [emit1]; rfl
  | @byte chi clo hi lo rest toks st hh hl _ ih =>
    intro lab pos
    rw [emit1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [emit1]
    rw [if_neg (by simp [nibble_not_lowstop1 hl])]
    simp only [hl]
    rw [ih lab (pos + 1)]
    cases hET : emitT toks lab (pos + 1) with
    | mk o u => cases u <;> simp [emitT, hET]
  | @spacing c rest toks st hs _ ih =>
    intro lab pos
    rw [emit1]
    simp only [Hex0.space_not_comment hs, hs, Bool.false_eq_true, if_false, if_true]
    exact ih lab pos
  | @commentNl c body rest toks st hc hbody _ ih =>
    intro lab pos
    rw [emit1]
    simp only [hc, if_true, Hex0.skipComment_body body rest hbody]
    exact ih lab pos
  | @commentEof c body hc hbody =>
    intro lab pos
    rw [emit1]
    simp only [hc, if_true, Hex0.skipComment_no_nl body hbody]
    rw [emit1]; rfl
  | @labelDef l rest toks st _ ih =>
    intro lab pos
    rw [emit1]
    simp only [show isComment c_colon = false by decide, show isSpace c_colon = false by decide,
      beq_self_eq_true, Bool.false_eq_true, if_false, if_true]
    rw [emit1]
    simp only [emitT]
    exact ih lab pos
  | @labelRef l rest toks st _ ih =>
    intro lab pos
    rw [emit1]
    simp only [show isComment c_pct = false by decide, show isSpace c_pct = false by decide,
      show (c_pct == c_colon) = false by decide, beq_self_eq_true, Bool.false_eq_true,
      if_false, if_true]
    rw [emit1]
    cases hL : lab l with
    | none => simp only [emitT, hL]
    | some p =>
      simp only [emitT, hL]
      rw [ih lab (pos + 4)]
      cases hET : emitT toks lab (pos + 4) with
      | mk o u => cases u <;> simp
  | errUnknownHigh hc hs hcol hpct hn =>
    intro lab pos
    rw [emit1]; simp [hc, hs, hcol, hpct, hn, emitT]
  | errTrailing hh =>
    intro lab pos
    rw [emit1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [emit1]; rfl
  | @errSplit chi clo hi rest hh hls =>
    intro lab pos
    rw [emit1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [emit1]
    rw [if_pos hls]
    simp [emitT]
  | @errUnknownLow chi clo hi rest hh hls hl =>
    intro lab pos
    rw [emit1]
    simp only [Hex0.nibble_not_comment hh, Hex0.nibble_not_space hh, nibble_ne_colon hh,
      nibble_ne_pct hh, hh, Bool.false_eq_true, if_false]
    rw [emit1]
    rw [if_neg (by simp [hls])]
    simp [hl, emitT]
  | errTrailColon =>
    intro lab pos
    rw [emit1]
    simp only [show isComment c_colon = false by decide, show isSpace c_colon = false by decide,
      beq_self_eq_true, Bool.false_eq_true, if_false, if_true]
    rw [emit1]
    simp [emitT]
  | errTrailPct =>
    intro lab pos
    rw [emit1]
    simp only [show isComment c_pct = false by decide, show isSpace c_pct = false by decide,
      show (c_pct == c_colon) = false by decide, beq_self_eq_true, Bool.false_eq_true,
      if_false, if_true]
    rw [emit1]
    simp [emitT]

/-! ## The headline: `decode1` is exactly grammar lexing + token semantics. -/

/-- Full grammar characterization of `decode1`. Error precedence is visible in
    the shape: a duplicate label (semantic, detected during the scan) beats the
    lexical status; the lexical status beats an undefined reference (semantic,
    detected during emission); emission output survives only when the scan was
    wholly clean. -/
theorem decode1_grammar {inp : List Nat} {toks : List Token} {lst : Status}
    (h : Lex inp toks lst) :
    decode1 inp =
      (match collect toks noLabels 0 with
       | (_, m, true) => ([], m, .Dup)
       | (lab, m, false) =>
           match lst with
           | .Ok => (match emitT toks lab 0 with
                     | (out, true) => (out, m, .Undef)
                     | (out, false) => (out, m, .Ok))
           | e => ([], m, e)) := by
  unfold decode1
  rw [scan1_parses h noLabels 0]
  cases hC : collect toks noLabels 0 with
  | mk lab' rest =>
    cases rest with
    | mk m dup =>
      cases dup with
      | true => rfl
      | false =>
        cases lst with
        | Ok =>
          simp only []
          rw [emit1_parses h lab' 0]
          cases hET : emitT toks lab' 0 with
          | mk out u => cases u <;> rfl
        | Split => rfl
        | Trailing => rfl
        | Unknown => rfl
        | Dup => rfl
        | Undef => rfl
        | TrailTok => rfl

/-- The valid fragment, end to end: a lexically-valid input with no duplicate
    labels and no undefined references, whose output fits, decodes Ok to the
    grammar's emission. -/
theorem valid_coreSpec1 {inp : List Nat} {toks : List Token} {lab : Labels}
    {m : Nat} {out : List Nat} {cap : Nat}
    (h : Lex inp toks .Ok)
    (hc : collect toks noLabels 0 = (lab, m, false))
    (he : emitT toks lab 0 = (out, false))
    (hcap : m ≤ cap) :
    coreSpec1 inp cap = (0, out, out.length) := by
  unfold coreSpec1
  rw [decode1_grammar h, hc]
  simp only [he]
  rw [if_neg (by omega)]

/-! ## Sanity examples (consistent with HEX1.md). -/

/-- `":A 00 %A"` lexes to `labelDef A; byte 0 0; labelRef A`. -/
example : Lex [58, 65, 32, 48, 48, 32, 37, 65]
    [.labelDef 65, .byte 0 0, .labelRef 65] .Ok :=
  .labelDef (.spacing (by decide) (.byte (by decide) (by decide)
    (.spacing (by decide) (.labelRef .nil))))

/-- `"4:"`: `':'` is a stop character, so it splits a nibble (HEX1.md). -/
example : Lex [52, 58] [] .Split :=
  .errSplit (chi := 52) (clo := 58) (hi := 4) (rest := []) (by decide) (by decide)

/-- `":"` at EOF: `TrailTok`, distinct from hex0's taxonomy. -/
example : Lex [58] [] .TrailTok := .errTrailColon

/-- A comment hides `:`/`%` (they are comment text, not tokens). -/
example : Lex [59, 58, 65, 10] [] .Ok :=
  .commentNl (body := [58, 65]) (by decide) (by decide) .nil

end Hex1
