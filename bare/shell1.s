# shell1.s -- the TRUSTED I/O shell for the hex1 rung (bare-metal, NOT proven).
# Identical in structure to shell.s (the hex0 shell); the only differences:
#   - calls `core1` instead of `core`,
#   - additionally passes a4 = label-table scratch (256 * 8 bytes in .bss).
#
# QEMU virt machine memory map used here:
#   NS16550A UART : 0x10000000  (THR @ +0, LSR @ +5, LSR.THRE = 0x20)
#   SiFive test   : 0x00100000  (write 0x5555 to power off)
#   RAM base      : 0x80000000  (image is loaded here; PC starts here)

        .option norvc
        .equ    UART,      0x10000000
        .equ    UART_LSR,  5
        .equ    UART_THRE, 0x20
        .equ    TEST_DEV,  0x00100000
        .equ    TEST_PASS, 0x5555
        .equ    OUT_CAP,   4096

        .section .text._start,"ax",@progbits
        .globl  _start
_start:
        la      sp, _stack_top
        la      a0, input_start
        la      t0, input_end
        sub     a1, t0, a0              # in_len = input_end - input_start
        la      a2, out_buf
        li      a3, OUT_CAP
        la      a4, lbl_buf
        call    core1                   # -> a0=status, a1=out_len

        # Print exactly out_len bytes of out_buf to the UART.
        mv      s1, a1                  # out_len
        la      s2, out_buf
        li      s3, 0                   # i
.Lprint:
        bgeu    s3, s1, .Ldone
        add     t0, s2, s3
        lbu     a0, 0(t0)
        call    uart_putc
        addi    s3, s3, 1
        j       .Lprint
.Ldone:
        # power off QEMU
        li      t0, TEST_DEV
        li      t1, TEST_PASS
        sw      t1, 0(t0)
.Lhang:
        j       .Lhang

# uart_putc: a0 = byte to send (low 8 bits). Clobbers t0,t1.
uart_putc:
        li      t0, UART
.Lwait:
        lbu     t1, UART_LSR(t0)
        andi    t1, t1, UART_THRE
        beqz    t1, .Lwait
        sb      a0, 0(t0)
        ret

        # Preloaded input region: an ASCII hex1 program, embedded at link time.
        .section .rodata.input,"a",@progbits
        .globl  input_start
input_start:
        .incbin "input1.hex"
        .globl  input_end
input_end:

        # Output buffer + label table + stack live in RAM (.bss).
        .section .bss,"aw",@nobits
        .align  4
out_buf:
        .space  OUT_CAP
        .align  4
lbl_buf:
        .space  2048                    # 256 labels * 8 bytes
        .align  4
        .space  0x10000                 # 64 KiB stack
_stack_top:
