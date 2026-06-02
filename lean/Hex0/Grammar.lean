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
      beq_eq_false_iff_ne]; omega
  · rw [if_neg hd] at h
    by_cases hl : 65 ≤ c ∧ c ≤ 70
    · obtain ⟨h1, h2⟩ := hl; simp only [isComment, c_hash, c_semi, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne]; omega
    · rw [if_neg hl] at h; exact absurd h (by simp)

theorem nibble_not_space {c v : Nat} (h : nibble c = some v) : isSpace c = false := by
  simp only [nibble] at h
  by_cases hd : 48 ≤ c ∧ c ≤ 57
  · obtain ⟨h1, h2⟩ := hd; simp only [isSpace, c_nl, c_sp, c_us, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne]; omega
  · rw [if_neg hd] at h
    by_cases hl : 65 ≤ c ∧ c ≤ 70
    · obtain ⟨h1, h2⟩ := hl; simp only [isSpace, c_nl, c_sp, c_us, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne]; omega
    · rw [if_neg hl] at h; exact absurd h (by simp)

theorem nibble_not_lowstop {c v : Nat} (h : nibble c = some v) : isLowStop c = false := by
  simp only [isLowStop, nibble_not_space h, nibble_not_comment h, Bool.or_self]

/-- A spacing char is not a comment char. -/
theorem space_not_comment {c : Nat} (h : isSpace c = true) : isComment c = false := by
  simp only [isSpace, c_nl, c_sp, c_us, beq_iff_eq, Bool.or_eq_true] at h
  simp only [isComment, c_hash, c_semi, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega

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
  /-- `TOKEN ::= COMMENT ::= (#|;) (¬\n)* \n`, emitting nothing. -/
  | comment {c : Nat} {body rest out : List Nat} :
      isComment c = true → (∀ b ∈ body, b ≠ c_nl) → Valid rest out →
      Valid (c :: (body ++ c_nl :: rest)) out

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
  | @comment c body rest out hc hbody _ ih =>
    rw [decodeS_comment c (body ++ c_nl :: rest) hc, skipComment_body body rest hbody, ih]

end Hex0
