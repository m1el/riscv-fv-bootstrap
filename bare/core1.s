# core1.s -- the hex1 PROOF TARGET: hex0 + labels/relative refs, RV64I,
# no compressed instrs. Spec: ../HEX1.md. Reference impl: ../hex1.c.
#
# Pure function over caller-provided slices. No memory allocation, no globals,
# no CSRs, leaf function (uses ra only to return). Two passes over the input:
# pass 1 scans (grammar + capacity + label collection, writes nothing to out),
# pass 2 emits (bytes + reference resolution; cannot fail except UndefinedLabel).
#
# Contract:
#   a0 = in_ptr   (input bytes, ASCII hex1 text)
#   a1 = in_len   (length of input, any value >= 0)
#   a2 = out_ptr  (output buffer)
#   a3 = out_cap  (capacity of output buffer)
#   a4 = lbl_ptr  (label table scratch, 256 * 8 bytes; core1 initializes it;
#                  slot c = output position of label c, or -1 if undefined)
# Returns:
#   a0 = status   (0=Ok 2=OutputShort 3=SplitNibble 4=TrailingNibble
#                  5=UnknownChar 6=DuplicateLabel 7=UndefinedLabel
#                  8=TrailingToken)
#   a1 = out_len  (bytes written: 0 on pass-1 errors, field_pos on
#                  UndefinedLabel, total on Ok)
#
# Precondition (WellFormed): out_cap < 2^63 and lbl_ptr + 2048 < 2^63.
# (Label positions are stored as i64 with -1 = undefined, tested by sign;
# the two `blt`s rely on their operands being < 2^63. Keeps the ISA surface
# to 16 instructions -- no bltu.)
#
# Scratch: t0=in_idx, t1=out_idx, t2=chr, t3=tmp, t4=high/tmp, t5=low/tmp
# Character codes: '\n'=10 ' '=32 '#'=35 '%'=37 ':'=58 ';'=59
#                  '0'=48 '9'=57 'A'=65 'F'=70 '_'=95

        .option norvc
        .section .text.core1,"ax",@progbits
        .globl  core1
core1:
        # ---- init label table: 256 slots of -1 ----
        mv      t3, a4
        addi    t4, a4, 2047            # last byte of the table
        addi    t4, t4, 1               # a4 + 2048 (addi imm range is +-2048)
        li      t5, -1
.Linit:
        sd      t5, 0(t3)
        addi    t3, t3, 8
        blt     t3, t4, .Linit          # addresses < 2^63: signed == unsigned

        # =====================================================================
        # PASS 1: scan. t1 = virtual out position; nothing is written to out.
        # Invariant: t1 <= a3 (out_cap).
        # =====================================================================
        li      t0, 0                   # in_idx = 0
        li      t1, 0                   # out_idx = 0
.L1loop:
        bgeu    t0, a1, .L1done         # in_idx >= in_len -> pass 1 ok
        add     t3, a0, t0
        lbu     t2, 0(t3)               # chr = in[in_idx]
        addi    t0, t0, 1               # in_idx++
        li      t3, 35
        beq     t2, t3, .L1comment      # '#'
        li      t3, 59
        beq     t2, t3, .L1comment      # ';'
        li      t3, 10
        beq     t2, t3, .L1loop         # '\n' spacing
        li      t3, 32
        beq     t2, t3, .L1loop         # ' ' spacing
        li      t3, 95
        beq     t2, t3, .L1loop         # '_' spacing
        li      t3, 58
        beq     t2, t3, .L1label        # ':'
        li      t3, 37
        beq     t2, t3, .L1ref          # '%'
        # parse high nibble of t2 -> t4, bad -> UnknownChar
        li      t3, 48
        blt     t2, t3, .Lunknown       # chr < '0'
        li      t3, 58
        bge     t2, t3, .L1high_af      # chr >= '9'+1 -> try A-F
        j       .L1have_high
.L1high_af:
        li      t3, 65
        blt     t2, t3, .Lunknown       # chr < 'A'
        li      t3, 71
        bge     t2, t3, .Lunknown       # chr >= 'F'+1
.L1have_high:
        # EXPECT_LOW: need a low nibble
        bgeu    t0, a1, .Ltrailing      # EOF after high nibble
        add     t3, a0, t0
        lbu     t2, 0(t3)               # chr = in[in_idx]
        addi    t0, t0, 1               # in_idx++
        # stop chars in low position -> SplitNibble
        li      t3, 10
        beq     t2, t3, .Lsplit         # '\n'
        li      t3, 32
        beq     t2, t3, .Lsplit         # ' '
        li      t3, 95
        beq     t2, t3, .Lsplit         # '_'
        li      t3, 35
        beq     t2, t3, .Lsplit         # '#'
        li      t3, 59
        beq     t2, t3, .Lsplit         # ';'
        li      t3, 58
        beq     t2, t3, .Lsplit         # ':'
        li      t3, 37
        beq     t2, t3, .Lsplit         # '%'
        # parse low nibble of t2, bad -> UnknownChar (value unused in pass 1)
        li      t3, 48
        blt     t2, t3, .Lunknown
        li      t3, 58
        bge     t2, t3, .L1low_af
        j       .L1have_low
.L1low_af:
        li      t3, 65
        blt     t2, t3, .Lunknown
        li      t3, 71
        bge     t2, t3, .Lunknown
.L1have_low:
        bgeu    t1, a3, .Lshort         # out_idx >= out_cap -> OutputShort
        addi    t1, t1, 1               # out_idx++ (virtual)
        j       .L1loop
.L1label:                               # ':' -- define label
        bgeu    t0, a1, .Ltrailtok      # EOF after ':'
        add     t3, a0, t0
        lbu     t2, 0(t3)               # label byte (consumed unconditionally)
        addi    t0, t0, 1
        slli    t3, t2, 3
        add     t3, t3, a4              # &labels[c]
        ld      t4, 0(t3)
        bgez    t4, .Ldup               # slot >= 0 -> already defined
        sd      t1, 0(t3)               # labels[c] = out_idx
        j       .L1loop
.L1ref:                                 # '%' -- reference site
        bgeu    t0, a1, .Ltrailtok      # EOF after '%'
        addi    t0, t0, 1               # consume label byte (checked in pass 2)
        sub     t3, a3, t1              # out_cap - out_idx  (t1 <= a3)
        li      t4, 4
        blt     t3, t4, .Lshort         # < 4 bytes left -> OutputShort
                                        # (cap < 2^63 precondition: signed == unsigned)
        addi    t1, t1, 4               # out_idx += 4 (virtual)
        j       .L1loop
.L1comment:
        bgeu    t0, a1, .L1done         # comment runs to EOF -> pass 1 ok
        add     t3, a0, t0
        lbu     t2, 0(t3)               # peek in[in_idx]
        li      t3, 10
        beq     t2, t3, .L1loop         # newline ends comment; leave for spacing
        addi    t0, t0, 1               # consume comment char
        j       .L1comment
.L1done:

        # =====================================================================
        # PASS 2: emit. Grammar and capacity hold by pass 1; only error left
        # is UndefinedLabel. Nibble parses are check-free.
        # =====================================================================
        li      t0, 0                   # in_idx = 0
        li      t1, 0                   # out_idx = 0
.L2loop:
        bgeu    t0, a1, .Lok            # in_idx >= in_len -> Ok
        add     t3, a0, t0
        lbu     t2, 0(t3)               # chr = in[in_idx]
        addi    t0, t0, 1
        li      t3, 35
        beq     t2, t3, .L2comment      # '#'
        li      t3, 59
        beq     t2, t3, .L2comment      # ';'
        li      t3, 10
        beq     t2, t3, .L2loop         # '\n'
        li      t3, 32
        beq     t2, t3, .L2loop         # ' '
        li      t3, 95
        beq     t2, t3, .L2loop         # '_'
        li      t3, 58
        beq     t2, t3, .L2label        # ':'
        li      t3, 37
        beq     t2, t3, .L2ref          # '%'
        # nibble pair (valid by pass 1): high -> t4
        li      t3, 58
        blt     t2, t3, .L2high_09
        addi    t4, t2, -55             # 'A'-'F' -> 10..15
        j       .L2have_high
.L2high_09:
        addi    t4, t2, -48             # '0'-'9' -> 0..9
.L2have_high:
        add     t3, a0, t0
        lbu     t2, 0(t3)               # low char (in bounds by pass 1)
        addi    t0, t0, 1
        li      t3, 58
        blt     t2, t3, .L2low_09
        addi    t5, t2, -55
        j       .L2have_low
.L2low_09:
        addi    t5, t2, -48
.L2have_low:
        slli    t4, t4, 4
        or      t4, t4, t5              # byte = (high<<4)|low
        add     t3, a2, t1
        sb      t4, 0(t3)
        addi    t1, t1, 1               # out_idx++ (t1 < a3 by pass 1)
        j       .L2loop
.L2label:                               # ':' -- skip label byte
        addi    t0, t0, 1
        j       .L2loop
.L2ref:                                 # '%' -- emit i32 LE relative offset
        add     t3, a0, t0
        lbu     t2, 0(t3)               # label byte (in bounds by pass 1)
        addi    t0, t0, 1
        slli    t3, t2, 3
        add     t3, t3, a4
        ld      t4, 0(t3)               # labels[c]
        bltz    t4, .Lundef             # -1 -> UndefinedLabel
        addi    t5, t1, 4
        sub     t4, t4, t5              # off = labels[c] - (out_idx + 4)
        add     t3, a2, t1
        sb      t4, 0(t3)               # 4 bytes, little-endian
        srli    t4, t4, 8
        sb      t4, 1(t3)
        srli    t4, t4, 8
        sb      t4, 2(t3)
        srli    t4, t4, 8
        sb      t4, 3(t3)
        addi    t1, t1, 4               # out_idx += 4 (fits by pass 1)
        j       .L2loop
.L2comment:
        bgeu    t0, a1, .Lok            # comment runs to EOF -> Ok
        add     t3, a0, t0
        lbu     t2, 0(t3)
        li      t3, 10
        beq     t2, t3, .L2loop         # newline ends comment
        addi    t0, t0, 1
        j       .L2comment

        # ---- exits ----
.Lok:
        li      a0, 0
        mv      a1, t1
        ret
.Lshort:
        li      a0, 2
        li      a1, 0
        ret
.Lsplit:
        li      a0, 3
        li      a1, 0
        ret
.Ltrailing:
        li      a0, 4
        li      a1, 0
        ret
.Lunknown:
        li      a0, 5
        li      a1, 0
        ret
.Ldup:
        li      a0, 6
        li      a1, 0
        ret
.Lundef:
        li      a0, 7
        mv      a1, t1                  # field_pos: bytes written so far
        ret
.Ltrailtok:
        li      a0, 8
        li      a1, 0
        ret
