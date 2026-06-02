# hex0, the minimal bootstrap seed

## Language:

```bnf
GRAMMAR ::= <TOKEN>*
TOKEN   ::= <BYTE> | <COMMENT> | <SPACING>
BYTE    ::= <NIBBLE><NIBBLE>
NIBBLE  ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
         | "A" | "B" | "C" | "D" | "E" | "F"
COMMENT ::= ("#" | ";") (ALL_CHARS - "\n")* ("\n" | EOF)
SPACING ::= " " | "_" | "\n"
```

Each `<BYTE>` corresponds to one output byte, treating the first `<NIBBLE>` as the high nibble, and the second `<NIBBLE>` as the low nibble.

A `<COMMENT>` runs from `#`/`;` up to **and including** the next `"\n"`, or to **end of input** if no `"\n"` follows (an unterminated trailing comment is accepted). Comments and spacing produce no output.

Define the **stop characters** as the characters that begin a `<SPACING>` or `<COMMENT>` token: `" "`, `"_"`, `"\n"`, `"#"`, `";"`.

## Errors:

- `<NIBBLE>` followed by `EOF`: `ErrTrailingNibble`
- `<NIBBLE>` followed by a **stop character** (i.e. a char that begins another token): `ErrSplitNibble`
- `<NIBBLE>` followed by any **other** non-`<NIBBLE>` character (a char that begins no token): `ErrUnknownChar`
- Non-matching character at the start of a `<TOKEN>` (not a `<NIBBLE>`, `<SPACING>`, or `<COMMENT>` start): `ErrUnknownChar`
- Not enough space for output: `ErrOutputShort`

The grammar and error classification are formally machine-checked against the
spec `decodeS` in `lean/Hex0/Grammar.lean`: every input matches exactly one of
"valid program" (→ `Ok`) or one error class (totality + disjointness), and the
classification agrees with the implementation.
