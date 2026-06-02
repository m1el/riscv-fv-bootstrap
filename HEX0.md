# hex0, the minimal bootstrap seed

## Language:

```bnf
GRAMMAR ::= <TOKEN>*
TOKEN ::= <BYTE> | <COMMENT> | <SPACING>
BYTE ::= <NIBBLE><NIBBLE>
NIBBLE ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
        | "A" | "B" | "C" | "D" | "E" | "F"
COMMENT ::= ("#" | ";") (ALL_CHARS - "\n")* "\n"
SPACING ::= " " | "_" | "\n"
```

Each `<BYTE>` corresponds to one output byte, treating the first `<NIBBLE>` as the high nibble, and the second `<NIBBLE>` as the low nibble.

## Errors:

- `<NIBBLE>` followed by non-matching char: `ErrUnknownChar`
- `<NIBBLE>` followed by non-`<NIBBLE>`: `ErrSplitNibble`
- `<NIBBLE>` followed by `EOF`: `ErrTrailingNibble`
- Non-matching character at the start of `<TOKEN>`: `ErrUnknownChar`
- Not enough space for output: `ErrOutputShort`