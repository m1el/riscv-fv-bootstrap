# shellmain.s -- UNVERIFIED harness shell (like shell.s): run the
# LowIR-COMPILED library blob (progmain.bin, emitted by
# lean/DumpProgMain.lean) on bare metal and print its 8 observable
# registers over the UART, one per line as 16 uppercase hex digits.
#
# The blob is position-independent (all control flow pc-relative, all data
# in stack frames). Its own entry stub ends in a self-loop, so the shim
# calls `main` INSIDE the blob directly (byte offset MAIN_OFF from
# progmain.inc); main returns its 8 observables in a0..a7 per the
# compiler's calling convention.
#
# Expected output: bare/progmain.expected (computed from the IL semantics).

        .option norvc
        .equ    UART,      0x10000000
        .equ    UART_LSR,  5
        .equ    UART_THRE, 0x20
        .equ    TEST_DEV,  0x00100000
        .equ    TEST_PASS, 0x5555
        .include "progmain.inc"

        .section .text._start,"ax",@progbits
        .globl  _start
_start:
        la      sp, _stack_top
        la      t0, blob
        li      t1, MAIN_OFF
        add     t0, t0, t1
        jalr    ra, t0, 0               # call main() inside the blob
        # a0..a7 = the 8 observables; park them (print clobbers a0/t*)
        mv      s2, a0
        mv      s3, a1
        mv      s4, a2
        mv      s5, a3
        mv      s6, a4
        mv      s7, a5
        mv      s8, a6
        mv      s9, a7
        mv      a0, s2
        call    print_hex64
        mv      a0, s3
        call    print_hex64
        mv      a0, s4
        call    print_hex64
        mv      a0, s5
        call    print_hex64
        mv      a0, s6
        call    print_hex64
        mv      a0, s7
        call    print_hex64
        mv      a0, s8
        call    print_hex64
        mv      a0, s9
        call    print_hex64
        # power off QEMU
        li      t0, TEST_DEV
        li      t1, TEST_PASS
        sw      t1, 0(t0)
.Lhang:
        j       .Lhang

# print a0 as 16 uppercase hex digits + '\n'. Clobbers t0..t5.
print_hex64:
        mv      t2, a0
        li      t3, 60
.Lnib:
        srl     t0, t2, t3
        andi    t0, t0, 0xF
        li      t1, 10
        blt     t0, t1, .Ldigit
        addi    t0, t0, 55              # 'A' - 10
        j       .Lputc
.Ldigit:
        addi    t0, t0, 48              # '0'
.Lputc:
        li      t4, UART
.Lwait1:
        lbu     t5, UART_LSR(t4)
        andi    t5, t5, UART_THRE
        beqz    t5, .Lwait1
        sb      t0, 0(t4)
        addi    t3, t3, -4
        bgez    t3, .Lnib
        li      t0, 10                  # '\n'
        li      t4, UART
.Lwait2:
        lbu     t5, UART_LSR(t4)
        andi    t5, t5, UART_THRE
        beqz    t5, .Lwait2
        sb      t0, 0(t4)
        ret

        # The compiled blob, verbatim, 4-aligned.
        .balign 4
        .globl  blob
blob:
        .incbin "progmain.bin"

        # Stack in RAM.
        .section .bss,"aw",@nobits
        .align  4
        .space  0x10000                 # 64 KiB
_stack_top:
