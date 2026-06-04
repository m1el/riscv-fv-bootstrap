/-
  hex1 functional specification (the refinement target). Spec: HEX1.md.

  This MIRRORS coq/Spec1.v definition-for-definition. Bytes are modelled as
  `Nat` (assumed < 256); the input is a `List Nat`.

  hex1 = hex0 + single-character labels:
    `:c`  binds label `c` to the current output position (no repeats);
    `%c`  emits 4 bytes: (pos(c) - (field_pos + 4)) as a little-endian
          two's-complement i32 (end-relative, x86 rel32 convention).

  The spec is TWO capacity-free phases over the input, mirroring the two-pass
  implementations (hex1.c / bare/core1.s):

    `scan1`  -- tokenization + label collection. Returns (labels, m, status)
               where `m` is the virtual output length at the error site
               (or the total output length when status = Ok).
    `emit1`  -- byte emission + reference resolution. Under a clean scan the
               only reachable error is `Undef`.

  Both are flat one-character-per-step state machines over `St1`
  (High / Low hi / Col / Pct), matching core1.s's control flow.

  Capacity is applied afterwards in `coreSpec1`, like hex0's `coreSpec`:
  the machine's capacity-threaded pass 1 reports OutputShort iff `cap < m`.
  (Error tokens emit nothing, so the first capacity-crossing token always
  strictly precedes the first scan-error token; hence the factorization is
  exact. See HEX1.md "Error precedence".)
-/
import Hex0.Spec

namespace Hex1
open Hex0 (isSpace isComment nibble skipComment)

/-- New token-starting character codes. -/
def c_colon : Nat := 58  -- ':'
def c_pct   : Nat := 37  -- '%'

/-- hex1 stop characters: hex0's five plus ':' and '%'. -/
def isLowStop (c : Nat) : Bool := Hex0.isLowStop c || c == c_colon || c == c_pct

/-- Terminal status of a decode (capacity-independent). -/
inductive Status where
  | Ok | Split | Trailing | Unknown | Dup | Undef | TrailTok
deriving DecidableEq, Repr

/-- Numeric status codes, matching the Error enum in hex1.c / core1.s. -/
def statusCode : Status → Nat
  | .Ok => 0 | .Split => 3 | .Trailing => 4 | .Unknown => 5
  | .Dup => 6 | .Undef => 7 | .TrailTok => 8

/-- The label map: label byte ↦ output position. -/
abbrev Labels := Nat → Option Nat

def noLabels : Labels := fun _ => none

def setLabel (lab : Labels) (l pos : Nat) : Labels :=
  fun x => if x = l then some pos else lab x

/-- Decoder state: expecting a high nibble / a low nibble (after high `hi`) /
    the label byte of a `:` definition / the label byte of a `%` reference. -/
inductive St1 where
  | High | Low (hi : Nat) | Col | Pct

/-- Phase 1 (scan): tokenize, collect label positions, track the virtual
    output position. Returns (labels, m, status); `m` is the output position
    reached when the scan stops (the error site's position, or the total).
    Mirrors `scan` in hex1.c statement-for-statement. -/
def scan1 : St1 → Labels → Nat → List Nat → (Labels × Nat × Status)
  | .High, lab, pos, [] => (lab, pos, .Ok)
  | .Low _, lab, pos, [] => (lab, pos, .Trailing)
  | .Col, lab, pos, [] => (lab, pos, .TrailTok)
  | .Pct, lab, pos, [] => (lab, pos, .TrailTok)
  | .High, lab, pos, c :: rest =>
      if isComment c then scan1 .High lab pos (skipComment rest)
      else if isSpace c then scan1 .High lab pos rest
      else if c == c_colon then scan1 .Col lab pos rest
      else if c == c_pct then scan1 .Pct lab pos rest
      else match nibble c with
           | none => (lab, pos, .Unknown)
           | some hi => scan1 (.Low hi) lab pos rest
  | .Low _, lab, pos, c :: rest =>
      if isLowStop c then (lab, pos, .Split)
      else match nibble c with
           | none => (lab, pos, .Unknown)
           | some _ => scan1 .High lab (pos + 1) rest
  | .Col, lab, pos, l :: rest =>
      match lab l with
      | some _ => (lab, pos, .Dup)
      | none => scan1 .High (setLabel lab l pos) pos rest
  | .Pct, lab, pos, _ :: rest => scan1 .High lab (pos + 4) rest
  termination_by _ _ _ l => l.length
  decreasing_by
    all_goals simp_wf
    · have h := Hex0.skipComment_len rest; omega
    all_goals omega

/-- The 4 little-endian bytes of the i32 relative offset
    `p - (pos + 4)` (label position `p`, field position `pos`), reduced
    mod 2^32 (two's complement truncation; exact for outputs < 2 GiB). -/
def offBytes (p pos : Nat) : List Nat :=
  let off : Nat := ((((p : Int) - ((pos : Int) + 4)) % ((2^32 : Nat) : Int))).toNat
  [off % 256, off / 2^8 % 256, off / 2^16 % 256, off / 2^24 % 256]

/-- Phase 2 (emit): emit bytes and resolve references against the collected
    label map. Total (defined on all inputs); under a clean scan the only
    reachable stop is `.Undef` (or `.Ok` at EOF). `pos` is the output
    position = length of output emitted so far. Mirrors `emit` in hex1.c. -/
def emit1 : St1 → Labels → Nat → List Nat → (List Nat × Status)
  | .High, _, _, [] => ([], .Ok)
  | .Low _, _, _, [] => ([], .Trailing)
  | .Col, _, _, [] => ([], .TrailTok)
  | .Pct, _, _, [] => ([], .TrailTok)
  | .High, lab, pos, c :: rest =>
      if isComment c then emit1 .High lab pos (skipComment rest)
      else if isSpace c then emit1 .High lab pos rest
      else if c == c_colon then emit1 .Col lab pos rest
      else if c == c_pct then emit1 .Pct lab pos rest
      else match nibble c with
           | none => ([], .Unknown)
           | some hi => emit1 (.Low hi) lab pos rest
  | .Low hi, lab, pos, c :: rest =>
      if isLowStop c then ([], .Split)
      else match nibble c with
           | none => ([], .Unknown)
           | some lo =>
               let (out, st) := emit1 .High lab (pos + 1) rest
               ((hi * 16 + lo) :: out, st)
  | .Col, lab, pos, _ :: rest => emit1 .High lab pos rest
  | .Pct, lab, pos, l :: rest =>
      match lab l with
      | none => ([], .Undef)
      | some p =>
          let (out, st) := emit1 .High lab (pos + 4) rest
          (offBytes p pos ++ out, st)
  termination_by _ _ _ l => l.length
  decreasing_by
    all_goals simp_wf
    · have h := Hex0.skipComment_len rest; omega
    all_goals omega

/-- Capacity-free decode: (output bytes, scan length m, status).
    On a scan error the output is empty and the status is the scan's;
    otherwise the emit phase's output and status (Ok or Undef). -/
def decode1 (inp : List Nat) : List Nat × Nat × Status :=
  let (lab, m, st) := scan1 .High noLabels 0 inp
  match st with
  | .Ok => let (out, st') := emit1 .High lab 0 inp
           (out, m, st')
  | e => ([], m, e)

/-- Behaviour of the bounded machine `core1` with output capacity `cap`:
    (status, output, out_len). Phase-1 errors (including OutputShort) write
    nothing; an undefined reference stops at the failing field. -/
def coreSpec1 (input : List Nat) (cap : Nat) : Nat × List Nat × Nat :=
  let (out, m, st) := decode1 input
  if cap < m then (2, [], 0)
  else match st with
       | .Ok    => (0, out, out.length)
       | .Undef => (7, out, out.length)
       | e      => (statusCode e, [], 0)

end Hex1
