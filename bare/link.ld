OUTPUT_ARCH(riscv)
ENTRY(_start)

/* QEMU virt loads the kernel image at 0x80000000 and starts the hart there. */
SECTIONS
{
  . = 0x80000000;

  .text : {
    *(.text._start)        /* entry must be first, at 0x80000000 */
    *(.text.core)
    *(.text*)
  }

  .rodata : { *(.rodata*) }
  .data   : { *(.data*) }

  .bss : {
    *(.bss*)
    *(COMMON)
  }

  /* drop anything we don't expect */
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.riscv.attributes) }
}
