/-
  hex0 functional specification (the refinement target).

  This MIRRORS coq/Spec.v definition-for-definition. Bytes are modelled as
  `Nat` (assumed < 256); the input is a `List Nat`.

  The spec is a two-state machine (EXPECT_HIGH / EXPECT_LOW), written as a
  single well-founded recursion `decodeS` over an explicit state `St`, so there
  is exactly one termination argument (decreasing on input length).

  In LOW position the five "stop" characters (\n ' ' '_' '#' ';') yield `Split`;
  any other non-hex character yields `Unknown`; EOF yields `Trailing`. Capacity
  (OutputShort) is NOT part of `decode` -- it is applied separately in `coreSpec`.
-/

namespace Hex0

/-- Character codes used by hex0. -/
def c_nl   : Nat := 10   -- '\n'
def c_sp   : Nat := 32   -- ' '
def c_us   : Nat := 95   -- '_'
def c_hash : Nat := 35   -- '#'
def c_semi : Nat := 59   -- ';'

def isSpace   (c : Nat) : Bool := c == c_nl || c == c_sp || c == c_us
def isComment (c : Nat) : Bool := c == c_hash || c == c_semi
/-- characters that, where a low nibble is expected, give `Split`. -/
def isLowStop (c : Nat) : Bool := isSpace c || isComment c

/-- nibble value 0..15, or `none` if `c` is not an uppercase hex digit. -/
def nibble (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)        -- '0'..'9'
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)   -- 'A'..'F' -> 10..15
  else none

/-- Terminal status of a decode (capacity-independent). -/
inductive Status where
  | Ok | Split | Trailing | Unknown
deriving DecidableEq, Repr

/-- Drop characters up to and including the first '\n'. -/
def skipComment : List Nat → List Nat
  | [] => []
  | c :: rest => if c == c_nl then rest else skipComment rest

theorem skipComment_len : ∀ l, (skipComment l).length ≤ l.length
  | [] => Nat.le_refl 0
  | c :: rest => by
      simp only [skipComment]
      split
      · exact Nat.le_succ_of_le (Nat.le_refl _)
      · exact Nat.le_succ_of_le (skipComment_len rest)

/-- Decoder state. -/
inductive St where
  | High | Low (hi : Nat)

def decodeS : St → List Nat → (List Nat × Status)
  | .High, [] => ([], .Ok)
  | .Low _, [] => ([], .Trailing)
  | .High, c :: rest =>
      if isComment c then decodeS .High (skipComment rest)
      else if isSpace c then decodeS .High rest
      else match nibble c with
           | none => ([], .Unknown)
           | some hi => decodeS (.Low hi) rest
  | .Low hi, c :: rest =>
      if isLowStop c then ([], .Split)
      else match nibble c with
           | none => ([], .Unknown)
           | some lo =>
               let (out, st) := decodeS .High rest
               ((hi * 16 + lo) :: out, st)
  termination_by _ l => l.length
  decreasing_by
    all_goals simp_wf
    · have h := skipComment_len rest; omega
    all_goals omega

def decode (l : List Nat) : List Nat × Status := decodeS .High l

/-- Numeric status codes, matching the Error enum in hex0.c / core.s. -/
def statusCode : Status → Nat
  | .Ok => 0 | .Split => 3 | .Trailing => 4 | .Unknown => 5

/-- Behaviour of the bounded machine `core` with output capacity `cap`:
    if the decode would emit more than `cap` bytes, the machine stops with
    OutputShort (code 2) having written exactly the first `cap` bytes.
    Returns (status, output, out_len). -/
def coreSpec (input : List Nat) (cap : Nat) : Nat × List Nat × Nat :=
  let (bs, st) := decode input
  if cap < bs.length then (2, bs.take cap, cap)
  else (statusCode st, bs, bs.length)

end Hex0
