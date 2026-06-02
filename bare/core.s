# core.s -- the PROOF TARGET: pure hex0 decode, RV64I, no compressed instrs.
#
# Pure function over caller-provided slices. No memory allocation, no globals,
# no CSRs, leaf function (uses ra only to return). This is the artifact the
# Lean and Coq refinement proofs reason about, byte for byte.
#
# Contract:
#   a0 = in_ptr   (input bytes, ASCII hex text)
#   a1 = in_len   (length of input, any value >= 0)
#   a2 = out_ptr  (output buffer)
#   a3 = out_cap  (capacity of output buffer)
# Returns:
#   a0 = status   (0=Ok 2=OutputShort 3=SplitNibble 4=TrailingNibble 5=UnknownChar)
#   a1 = out_len  (number of bytes written)
#
# Scratch: t0=in_idx, t1=out_idx, t2=chr, t3=tmp, t4=high, t5=low
# Character codes: '\n'=10 ' '=32 '#'=35 ';'=59 '0'=48 '9'=57 'A'=65 'F'=70 '_'=95

        .option norvc
        .section .text.core,"ax",@progbits
        .globl  core
core:
        li      t0, 0                   # in_idx = 0
        li      t1, 0                   # out_idx = 0
.Lloop:
        bgeu    t0, a1, .Lok            # in_idx >= in_len -> Ok (EXPECT_HIGH at EOF)
        add     t3, a0, t0
        lbu     t2, 0(t3)               # chr = in[in_idx]
        addi    t0, t0, 1               # in_idx++
        li      t3, 35
        beq     t2, t3, .Lcomment       # '#'
        li      t3, 59
        beq     t2, t3, .Lcomment       # ';'
        li      t3, 10
        beq     t2, t3, .Lloop          # '\n' spacing
        li      t3, 32
        beq     t2, t3, .Lloop          # ' ' spacing
        li      t3, 95
        beq     t2, t3, .Lloop          # '_' spacing
        # parse high nibble of t2 -> t4, bad -> UnknownChar
        li      t3, 48
        blt     t2, t3, .Lunknown       # chr < '0'
        li      t3, 58
        bge     t2, t3, .Lhigh_af       # chr >= '9'+1 -> try A-F
        addi    t4, t2, -48
        j       .Lhave_high
.Lhigh_af:
        li      t3, 65
        blt     t2, t3, .Lunknown       # chr < 'A'
        li      t3, 71
        bge     t2, t3, .Lunknown       # chr >= 'F'+1
        addi    t4, t2, -55             # 'A'->10
.Lhave_high:
        # EXPECT_LOW: need a low nibble
        bgeu    t0, a1, .Ltrailing      # EOF after high nibble
        add     t3, a0, t0
        lbu     t2, 0(t3)               # chr = in[in_idx]
        addi    t0, t0, 1               # in_idx++
        # spacing/comment chars in low position -> SplitNibble
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
        # parse low nibble of t2 -> t5, bad -> UnknownChar
        li      t3, 48
        blt     t2, t3, .Lunknown
        li      t3, 58
        bge     t2, t3, .Llow_af
        addi    t5, t2, -48
        j       .Lhave_low
.Llow_af:
        li      t3, 65
        blt     t2, t3, .Lunknown
        li      t3, 71
        bge     t2, t3, .Lunknown
        addi    t5, t2, -55
.Lhave_low:
        bgeu    t1, a3, .Lshort         # out_idx >= out_cap -> OutputShort
        slli    t4, t4, 4
        or      t4, t4, t5              # byte = (high<<4)|low
        add     t3, a2, t1
        sb      t4, 0(t3)
        addi    t1, t1, 1               # out_idx++
        j       .Lloop
.Lcomment:
        bgeu    t0, a1, .Lok            # comment runs to EOF -> Ok
        add     t3, a0, t0
        lbu     t2, 0(t3)               # peek in[in_idx]
        li      t3, 10
        beq     t2, t3, .Lloop          # newline ends comment; leave it for spacing
        addi    t0, t0, 1               # consume comment char
        j       .Lcomment
.Lok:
        li      a0, 0
        mv      a1, t1
        ret
.Lshort:
        li      a0, 2
        mv      a1, t1
        ret
.Lsplit:
        li      a0, 3
        mv      a1, t1
        ret
.Ltrailing:
        li      a0, 4
        mv      a1, t1
        ret
.Lunknown:
        li      a0, 5
        mv      a1, t1
        ret
