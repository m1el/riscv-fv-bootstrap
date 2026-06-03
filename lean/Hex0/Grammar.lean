/-
  Faithful port of the hex0 grammar from `HEX0.md`, and its correspondence to
  the functional spec `decodeS` (`Hex0/Spec.lean`).

  HEX0.md:
    GRAMMAR ::= <TOKEN>*
    TOKEN   ::= <BYTE> | <COMMENT> | <SPACING>
    BYTE    ::= <NIBBLE><NIBBLE>
    NIBBLE  ::= "0".."9" | "A".."F"
    COMMENT ::= ("#" | ";") (ALL_CHARS - "\n")* "\n"
    SPACING ::= " " | "_" | "\n"
    Each <BYTE> emits one output byte = high*16 + low.

  Plan (this file):
    1. `Valid inp out` — the grammar as an inductive relation (the *valid*,
       error-free language), one constructor per production.
    2. `valid_ok` — every valid program decodes to exactly `(out, Ok)`.
    3. `decode_ok_valid` — the converse: if `decodeS` says `Ok`, the input was
       valid. Together: `decodeS .High inp = (out, Ok)  ↔  Valid inp out`.
    4. Error characterization + the divergences from HEX0.md's prose.
-/
import Hex0.Spec

namespace Hex0

/-! ## Small spec lemmas (local copies; depend only on `Spec`). -/

/-- A hex digit is neither a comment nor a spacing char. -/
theorem nibble_not_comment {c v : Nat} (h : nibble c = some v) : isComment c = false := by
  simp only [nibble] at h
  by_cases hd : 48 ≤ c ∧ c ≤ 57
  · obtain ⟨h1, h2⟩ := hd; simp only [isComment, c_hash, c_semi, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne]; refine ⟨?_, ?_⟩ <;> omega
  · rw [if_neg hd] at h
    by_cases hl : 65 ≤ c ∧ c ≤ 70
    · obtain ⟨h1, h2⟩ := hl; simp only [isComment, c_hash, c_semi, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne]; refine ⟨?_, ?_⟩ <;> omega
    · rw [if_neg hl] at h; exact absurd h (by simp)

theorem nibble_not_space {c v : Nat} (h : nibble c = some v) : isSpace c = false := by
  simp only [nibble] at h
  by_cases hd : 48 ≤ c ∧ c ≤ 57
  · obtain ⟨h1, h2⟩ := hd; simp only [isSpace, c_nl, c_sp, c_us, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne]; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rw [if_neg hd] at h
    by_cases hl : 65 ≤ c ∧ c ≤ 70
    · obtain ⟨h1, h2⟩ := hl; simp only [isSpace, c_nl, c_sp, c_us, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne]; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
    · rw [if_neg hl] at h; exact absurd h (by simp)

theorem nibble_not_lowstop {c v : Nat} (h : nibble c = some v) : isLowStop c = false := by
  simp only [isLowStop, nibble_not_space h, nibble_not_comment h, Bool.or_self]

/-- A spacing char is not a comment char. -/
theorem space_not_comment {c : Nat} (h : isSpace c = true) : isComment c = false := by
  simp only [isSpace, c_nl, c_sp, c_us, beq_iff_eq, Bool.or_eq_true] at h
  simp only [isComment, c_hash, c_semi, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  refine ⟨?_, ?_⟩ <;> omega

/-! ## `decodeS` token-decomposition lemmas (one per token class). -/

theorem decodeS_spacing (c : Nat) (rest : List Nat)
    (hc : isComment c = false) (hs : isSpace c = true) :
    decodeS .High (c :: rest) = decodeS .High rest := by
  rw [decodeS]; simp [hc, hs]

theorem decodeS_byte (chi clo : Nat) (rest : List Nat) (hi lo : Nat)
    (hc : isComment chi = false) (hs : isSpace chi = false) (hh : nibble chi = some hi)
    (hlc : isLowStop clo = false) (hl : nibble clo = some lo) :
    decodeS .High (chi :: clo :: rest) =
      ((hi * 16 + lo) :: (decodeS .High rest).1, (decodeS .High rest).2) := by
  rw [decodeS]; simp only [hc, hs, hh, Bool.false_eq_true, if_false]
  rw [decodeS]; simp [hlc, hl]

theorem decodeS_comment (c : Nat) (rest : List Nat) (hc : isComment c = true) :
    decodeS .High (c :: rest) = decodeS .High (skipComment rest) := by
  rw [decodeS]; simp [hc]

/-- `skipComment` over a newline-free body terminated by a newline yields the tail. -/
theorem skipComment_body (body rest : List Nat) (h : ∀ b ∈ body, b ≠ c_nl) :
    skipComment (body ++ c_nl :: rest) = rest := by
  induction body with
  | nil => show skipComment (c_nl :: rest) = rest; rfl
  | cons b bs ih =>
    have hb : b ≠ c_nl := h b List.mem_cons_self
    show skipComment (b :: (bs ++ c_nl :: rest)) = rest
    rw [skipComment, if_neg (by simp only [beq_iff_eq]; exact hb)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `skipComment` over a newline-free list runs to the end (EOF-terminated comment). -/
theorem skipComment_no_nl (rest : List Nat) (h : ∀ b ∈ rest, b ≠ c_nl) :
    skipComment rest = [] := by
  induction rest with
  | nil => rfl
  | cons b bs ih =>
    have hb : b ≠ c_nl := h b List.mem_cons_self
    rw [skipComment, if_neg (by simp only [beq_iff_eq]; exact hb)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `decodeS` on empty input. -/
theorem decodeS_nil : decodeS .High [] = ([], .Ok) := by simp [decodeS]

/-- Every list either splits at its first newline, or contains none. -/
theorem newline_split (l : List Nat) :
    (∃ body suf, l = body ++ c_nl :: suf ∧ (∀ b ∈ body, b ≠ c_nl)) ∨ (∀ b ∈ l, b ≠ c_nl) := by
  induction l with
  | nil => exact Or.inr (by simp)
  | cons c rest ih =>
    by_cases hc : c = c_nl
    · exact Or.inl ⟨[], rest, by rw [hc]; rfl, by simp⟩
    · rcases ih with ⟨body, suf, hsplit, hbody⟩ | hnone
      · exact Or.inl ⟨c :: body, suf, by rw [hsplit]; rfl,
          fun x hx => by rcases List.mem_cons.mp hx with h | h; · rw [h]; exact hc
                         · exact hbody x h⟩
      · exact Or.inr (fun x hx => by rcases List.mem_cons.mp hx with h | h; · rw [h]; exact hc
                                     · exact hnone x h)

/-! ## The valid (error-free) grammar. -/

/-- `Valid inp out`: `inp` is a well-formed `GRAMMAR` (a sequence of `TOKEN`s with
    no error) emitting output bytes `out`. One constructor per BNF production. -/
inductive Valid : List Nat → List Nat → Prop
  /-- `GRAMMAR ::= ` (empty: zero tokens). -/
  | nil : Valid [] []
  /-- `TOKEN ::= BYTE`, `BYTE ::= NIBBLE NIBBLE`, emitting `hi*16+lo`. -/
  | byte {chi clo hi lo : Nat} {rest out : List Nat} :
      nibble chi = some hi → nibble clo = some lo → Valid rest out →
      Valid (chi :: clo :: rest) ((hi * 16 + lo) :: out)
  /-- `TOKEN ::= SPACING`, emitting nothing. -/
  | spacing {c : Nat} {rest out : List Nat} :
      isSpace c = true → Valid rest out → Valid (c :: rest) out
  /-- `TOKEN ::= COMMENT ::= (#|;) (¬\n)* \n`, newline-terminated, emitting nothing. -/
  | commentNl {c : Nat} {body rest out : List Nat} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Valid rest out →
      Valid (c :: (body ++ c_nl :: rest)) out
  /-- `COMMENT ::= (#|;) (¬\n)* EOF`, EOF-terminated trailing comment (the last
      token; consumes the rest of the input), emitting nothing. -/
  | commentEof {c : Nat} {body : List Nat} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Valid (c :: body) []

/-- **Soundness of the valid grammar**: every grammatically-valid program decodes
    to exactly its output bytes with terminal status `Ok`. -/
theorem valid_ok {inp out : List Nat} (h : Valid inp out) : decodeS .High inp = (out, .Ok) := by
  induction h with
  | nil => simp [decodeS]
  | @byte chi clo hi lo rest out hh hl _ ih =>
    rw [decodeS_byte chi clo rest hi lo (nibble_not_comment hh) (nibble_not_space hh) hh
      (nibble_not_lowstop hl) hl, ih]
  | @spacing c rest out hs _ ih =>
    rw [decodeS_spacing c rest (space_not_comment hs) hs, ih]
  | @commentNl c body rest out hc hbody _ ih =>
    rw [decodeS_comment c (body ++ c_nl :: rest) hc, skipComment_body body rest hbody, ih]
  | @commentEof c body hc hbody =>
    rw [decodeS_comment c body hc, skipComment_no_nl body hbody, decodeS_nil]

/-! ## Error-side `decodeS` lemmas (one per HEX0.md error). -/

/-- `Non-matching character at the start of <TOKEN>` → `Unknown` (HEX0.md, last bullet). -/
theorem decodeS_unknown_high (c : Nat) (rest : List Nat)
    (hc : isComment c = false) (hs : isSpace c = false) (hn : nibble c = none) :
    decodeS .High (c :: rest) = ([], .Unknown) := by
  rw [decodeS]; simp [hc, hs, hn]

/-- `<NIBBLE>` followed by `EOF` → `Trailing` (HEX0.md). -/
theorem decodeS_trailing (chi hi : Nat) (hh : nibble chi = some hi) :
    decodeS .High (chi :: []) = ([], .Trailing) := by
  rw [decodeS]; simp only [nibble_not_comment hh, nibble_not_space hh, hh, Bool.false_eq_true,
    if_false]
  simp [decodeS]

/-- `<NIBBLE>` followed by a token-starting (low-stop) char → `Split`.
    (HEX0.md line "non-`<NIBBLE>`": read as "a char that begins another token".) -/
theorem decodeS_split (chi clo hi : Nat) (rest : List Nat)
    (hh : nibble chi = some hi) (hlc : isLowStop clo = true) :
    decodeS .High (chi :: clo :: rest) = ([], .Split) := by
  rw [decodeS]; simp only [nibble_not_comment hh, nibble_not_space hh, hh, Bool.false_eq_true,
    if_false]
  rw [decodeS]; simp [hlc]

/-- `<NIBBLE>` followed by a non-nibble, non-stop ("non-matching") char → `Unknown`. -/
theorem decodeS_unknown_low (chi clo hi : Nat) (rest : List Nat)
    (hh : nibble chi = some hi) (hlc : isLowStop clo = false) (hl : nibble clo = none) :
    decodeS .High (chi :: clo :: rest) = ([], .Unknown) := by
  rw [decodeS]; simp only [nibble_not_comment hh, nibble_not_space hh, hh, Bool.false_eq_true,
    if_false]
  rw [decodeS]; simp [hlc, hl]

/-! ## The full grammar *with errors*.

    `Parse inp out st` extends `Valid` with the HEX0.md error taxonomy: a run of
    valid tokens (emitting `out`) followed optionally by one error token (setting
    `st`). The error bases below encode the *disambiguated* reading of HEX0.md's
    error section (see the divergence notes at the end). -/
inductive Parse : List Nat → List Nat → Status → Prop
  | ok : Parse [] [] .Ok
  | byte {chi clo hi lo : Nat} {rest out : List Nat} {st : Status} :
      nibble chi = some hi → nibble clo = some lo → Parse rest out st →
      Parse (chi :: clo :: rest) ((hi * 16 + lo) :: out) st
  | spacing {c : Nat} {rest out : List Nat} {st : Status} :
      isSpace c = true → Parse rest out st → Parse (c :: rest) out st
  | commentNl {c : Nat} {body rest out : List Nat} {st : Status} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Parse rest out st →
      Parse (c :: (body ++ c_nl :: rest)) out st
  | commentEof {c : Nat} {body : List Nat} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Parse (c :: body) [] .Ok
  /-- error: char that starts no token. -/
  | errUnknownHigh {c : Nat} {rest : List Nat} :
      isComment c = false → isSpace c = false → nibble c = none →
      Parse (c :: rest) [] .Unknown
  /-- error: high nibble then EOF. -/
  | errTrailing {chi hi : Nat} :
      nibble chi = some hi → Parse (chi :: []) [] .Trailing
  /-- error: high nibble then a token-starter (low-stop) char. -/
  | errSplit {chi clo hi : Nat} {rest : List Nat} :
      nibble chi = some hi → isLowStop clo = true → Parse (chi :: clo :: rest) [] .Split
  /-- error: high nibble then a non-nibble, non-stop char. -/
  | errUnknownLow {chi clo hi : Nat} {rest : List Nat} :
      nibble chi = some hi → isLowStop clo = false → nibble clo = none →
      Parse (chi :: clo :: rest) [] .Unknown

/-- **Soundness of the grammar with errors**: whatever the grammar derives, the
    spec computes — output bytes and terminal status both. -/
theorem parse_sound {inp out : List Nat} {st : Status} (h : Parse inp out st) :
    decodeS .High inp = (out, st) := by
  induction h with
  | ok => simp [decodeS]
  | @byte chi clo hi lo rest out st hh hl _ ih =>
    rw [decodeS_byte chi clo rest hi lo (nibble_not_comment hh) (nibble_not_space hh) hh
      (nibble_not_lowstop hl) hl, ih]
  | @spacing c rest out st hs _ ih => rw [decodeS_spacing c rest (space_not_comment hs) hs, ih]
  | @commentNl c body rest out st hc hbody _ ih =>
    rw [decodeS_comment c (body ++ c_nl :: rest) hc, skipComment_body body rest hbody, ih]
  | @commentEof c body hc hbody =>
    rw [decodeS_comment c body hc, skipComment_no_nl body hbody, decodeS_nil]
  | errUnknownHigh hc hs hn => exact decodeS_unknown_high _ _ hc hs hn
  | errTrailing hh => exact decodeS_trailing _ _ hh
  | errSplit hh hlc => exact decodeS_split _ _ _ _ hh hlc
  | errUnknownLow hh hlc hl => exact decodeS_unknown_low _ _ _ _ hh hlc hl

/-- A valid program is the `Ok` fragment of the grammar with errors. -/
theorem valid_to_parse {inp out : List Nat} (h : Valid inp out) : Parse inp out .Ok := by
  induction h with
  | nil => exact .ok
  | byte hh hl _ ih => exact .byte hh hl ih
  | spacing hs _ ih => exact .spacing hs ih
  | commentNl hc hb _ ih => exact .commentNl hc hb ih
  | commentEof hc hb => exact .commentEof hc hb

/-! ## Completeness / totality: the grammar covers every input.

    Every input is derivable in the grammar-with-errors, with exactly the output
    and status the spec computes. Combined with `parse_sound`, this gives
    `decodeS .High inp = (out, st) ↔ Parse inp out st`. -/
theorem parse_complete : ∀ (n : Nat) (inp : List Nat), inp.length ≤ n →
    Parse inp (decodeS .High inp).1 (decodeS .High inp).2 := by
  intro n
  induction n with
  | zero =>
    intro inp hn
    have h0 : inp = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    subst h0; rw [decodeS_nil]; exact .ok
  | succ n ih =>
    intro inp hn
    cases inp with
    | nil => rw [decodeS_nil]; exact .ok
    | cons c rest =>
      have hrest : rest.length ≤ n := by simp only [List.length_cons] at hn; omega
      cases hcm : isComment c with
      | true =>
        rw [decodeS_comment c rest hcm]
        rcases newline_split rest with ⟨body, suf, hsplit, hbody⟩ | hnone
        · subst hsplit
          rw [skipComment_body body suf hbody]
          have hsuf : suf.length ≤ n := by
            simp only [List.length_append, List.length_cons] at hrest; omega
          exact Parse.commentNl hcm hbody (ih suf hsuf)
        · rw [skipComment_no_nl rest hnone, decodeS_nil]
          exact Parse.commentEof hcm hnone
      | false =>
        cases hsp : isSpace c with
        | true => rw [decodeS_spacing c rest hcm hsp]; exact Parse.spacing hsp (ih rest hrest)
        | false =>
          cases hn2 : nibble c with
          | none => rw [decodeS_unknown_high c rest hcm hsp hn2]; exact Parse.errUnknownHigh hcm hsp hn2
          | some hi =>
            cases rest with
            | nil => rw [decodeS_trailing c hi hn2]; exact Parse.errTrailing hn2
            | cons clo rest' =>
              cases hls : isLowStop clo with
              | true => rw [decodeS_split c clo hi rest' hn2 hls]; exact Parse.errSplit hn2 hls
              | false =>
                cases hn3 : nibble clo with
                | none =>
                  rw [decodeS_unknown_low c clo hi rest' hn2 hls hn3]
                  exact Parse.errUnknownLow hn2 hls hn3
                | some lo =>
                  rw [decodeS_byte c clo rest' hi lo hcm hsp hn2 hls hn3]
                  have hrest' : rest'.length ≤ n := by simp only [List.length_cons] at hrest; omega
                  exact Parse.byte hn2 hn3 (ih rest' hrest')

/-- **Totality**: every input is derivable in the grammar (valid or some error). -/
theorem parse_total (inp : List Nat) : ∃ out st, Parse inp out st :=
  ⟨_, _, parse_complete inp.length inp (Nat.le_refl _)⟩

/-- **Determinism / non-intersection**: the grammar assigns a unique output and
    status to each input (so the valid and error derivations can never disagree). -/
theorem parse_det {inp o1 o2 : List Nat} {s1 s2 : Status}
    (h1 : Parse inp o1 s1) (h2 : Parse inp o2 s2) : o1 = o2 ∧ s1 = s2 := by
  have e := (parse_sound h1).symm.trans (parse_sound h2)
  injection e with ho hs; exact ⟨ho, hs⟩

/-- An input is *valid* if it parses with status `Ok`. -/
def IsValid (inp : List Nat) : Prop := ∃ out, Parse inp out .Ok
/-- An input is *erroneous* if it parses with a non-`Ok` status. -/
def IsErr (inp : List Nat) : Prop := ∃ out st, Parse inp out st ∧ st ≠ .Ok

/-- **Total partition**: every input is valid or erroneous. -/
theorem valid_or_err (inp : List Nat) : IsValid inp ∨ IsErr inp := by
  obtain ⟨out, st, h⟩ := parse_total inp
  by_cases hs : st = .Ok
  · exact Or.inl ⟨out, hs ▸ h⟩
  · exact Or.inr ⟨out, st, h, hs⟩

/-- **Disjoint partition**: no input is both valid and erroneous. -/
theorem not_valid_and_err (inp : List Nat) : ¬ (IsValid inp ∧ IsErr inp) := by
  rintro ⟨⟨o1, h1⟩, ⟨o2, st, h2, hst⟩⟩
  exact hst (parse_det h2 h1).2

/-! ## Sanity examples (consistent with the updated HEX0.md). -/

/-- An EOF-terminated comment is a valid program (HEX0.md `COMMENT ::= … (\n|EOF)`). -/
example : Valid [c_hash] [] := .commentEof (by decide) (by simp)

/-- The two nibble error classes are genuinely distinct (the basis for HEX0.md's
    `ErrSplitNibble` vs `ErrUnknownChar` split): a nibble + a stop char (`"_"`) is
    `Split`; a nibble + other garbage (`"G"`) is `Unknown`. -/
theorem split_vs_unknown_distinct :
    decodeS .High [48, c_us] = ([], .Split) ∧ decodeS .High [48, 71] = ([], .Unknown) :=
  ⟨decodeS_split 48 c_us 0 [] (by decide) (by decide),
   decodeS_unknown_low 48 71 0 [] (by decide) (by decide) (by decide)⟩

end Hex0

