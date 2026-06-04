# hex1, the second bootstrap rung

hex1 is hex0 plus single-character labels and 32-bit relative references. It is
a **separate program** with a separate proof; the proofs may share lemmas with
hex0's. Restricted to inputs containing no `:` or `%` outside comments, hex1
behaves **identically** to hex0 (same output bytes, same error classification).

## Language:

```bnf
GRAMMAR  ::= <TOKEN>*
TOKEN    ::= <BYTE> | <COMMENT> | <SPACING> | <LABELDEF> | <LABELREF>
BYTE     ::= <NIBBLE><NIBBLE>
NIBBLE   ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
          | "A" | "B" | "C" | "D" | "E" | "F"
COMMENT  ::= ("#" | ";") (ALL_CHARS - "\n")* ("\n" | EOF)
SPACING  ::= " " | "_" | "\n"
LABELDEF ::= ":" <ANY_BYTE>
LABELREF ::= "%" <ANY_BYTE>
```

`<ANY_BYTE>` is **any** of the 256 byte values, with no exceptions — including
space, `_`, newline, `#`, `;`, `:`, `%`, hex digits, and non-printable bytes.
So `:#` defines the label `#` (it does **not** start a comment), `:\n` defines
the label `\n`, and `::` defines the label `:`. The byte after `:` or `%` is
consumed unconditionally.

Define the **stop characters** as the characters that begin a non-`<BYTE>`
token: `" "`, `"_"`, `"\n"`, `"#"`, `";"`, `":"`, `"%"` (hex0's set plus `:`
and `%`).

## Semantics

Output positions are 0-based byte offsets into the output (not memory
addresses; all references are relative, so no base address exists or is
needed).

- `<BYTE>` emits one byte: first `<NIBBLE>` is the high nibble, second the low.
- `<COMMENT>` and `<SPACING>` emit nothing.
- `<LABELDEF>` (`:c`) emits nothing and binds label `c` to the current output
  position. Each label may be defined **at most once** in the program.
- `<LABELREF>` (`%c`) emits **4 bytes**: the offset

  ```
  off = pos(c) − (field_pos + 4)
  ```

  as a little-endian two's-complement i32, where `field_pos` is the output
  position where the 4-byte field begins and `pos(c)` is the position bound to
  label `c`. I.e. the offset is relative to the **end** of the 4-byte field
  (x86 `call`/`jmp` rel32 convention: `E8 %f` is exactly `call f`). A label
  defined immediately after the field yields offset `0`.

  References may point **forward or backward**; a label may be referenced any
  number of times (including zero).

  The stored value is `off mod 2^32`. This is exact whenever the offset fits
  in an i32, which is guaranteed for outputs shorter than 2 GiB.

## Errors:

Status codes (hex0's, plus three new ones):

| code | name              | meaning |
|------|-------------------|---------|
| 0    | `Ok`              | |
| 2    | `ErrOutputShort`  | not enough space for output |
| 3    | `ErrSplitNibble`  | `<NIBBLE>` followed by a **stop character** |
| 4    | `ErrTrailingNibble` | `<NIBBLE>` followed by `EOF` |
| 5    | `ErrUnknownChar`  | non-token character (at token start, or after a `<NIBBLE>`) |
| 6    | `ErrDuplicateLabel` | second `<LABELDEF>` for the same label byte |
| 7    | `ErrUndefinedLabel` | `<LABELREF>` to a label defined nowhere in the program |
| 8    | `ErrTrailingToken`  | `EOF` immediately after `:` or `%` |

Note `:` and `%` are stop characters, so in the low-nibble position they give
`ErrSplitNibble` (e.g. input `4:`), extending hex0's rule uniformly. (This is
the one classification change vs hex0 on shared inputs: hex0 reported
`ErrUnknownChar` there.)

### Error precedence (two-phase semantics)

Decoding is specified as two left-to-right phases over the input:

1. **Scan**: tokenization, capacity tracking, and label collection. Reports
   the **leftmost** of `ErrSplitNibble`, `ErrTrailingNibble`,
   `ErrUnknownChar`, `ErrTrailingToken`, `ErrDuplicateLabel`,
   `ErrOutputShort`. (`ErrOutputShort` is charged where the emission would
   occur: at the `<BYTE>` if `out_pos ≥ cap`, at the `<LABELREF>` if
   `cap − out_pos < 4`.)
2. **Emit**: byte emission and reference resolution. Reports the leftmost
   `ErrUndefinedLabel`.

Phase-1 errors take precedence over `ErrUndefinedLabel` **even when the
undefined reference occurs earlier in the input**: `%q G` (with `q` never
defined) is `ErrUnknownChar`, not `ErrUndefinedLabel` — whether `q` is
"undefined" is only knowable at `EOF` anyway.

On success, `out_len` is the total bytes emitted. On a phase-1 error, no
output bytes are written (`out_len = 0`). On `ErrUndefinedLabel`, the bytes
preceding the failing field have been written (`out_len = field_pos`).

## Examples

```
%A :A          → 00 00 00 00            (label right after field: off = 4 − 4 = 0)
:A 00 %A       → 00 FB FF FF FF         (off = 0 − (1+4) = −5)
:A%A           → FC FF FF FF            (off = 0 − 4 = −4)
:A ... :A      → ErrDuplicateLabel
%Z             → ErrUndefinedLabel      (Z defined nowhere)
4:             → ErrSplitNibble         (: is a stop character)
:              → ErrTrailingToken       (EOF after :)
:: 00 %:       → 00 FB FF FF FF         (the label byte is ':')
```
