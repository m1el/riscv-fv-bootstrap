CROSS   := riscv64-linux-gnu-
CC      := $(CROSS)gcc
OBJDUMP := $(CROSS)objdump
OBJCOPY := $(CROSS)objcopy

# RV64I, no compressed instructions (every instruction is 4 bytes -> simple
# formal decode). Freestanding, no std runtime.
ASFLAGS := -march=rv64i -mabi=lp64 -nostdlib -nostartfiles -ffreestanding -fno-pic
LDFLAGS := -Wl,-T,link.ld -Wl,--no-relax

QEMU    := qemu-system-riscv64
QFLAGS  := -machine virt -nographic -bios none -kernel

# This QEMU build links libcapstone.so.4 (disassembly only; never touched during
# execution), but the system ships capstone .so.5. Shim the SONAME so the dynamic
# loader is satisfied. Execution never calls capstone, so the 4->5 mismatch is inert.
SHIM    := $(CURDIR)/../.libshim
RUNENV  := LD_LIBRARY_PATH=$(SHIM)

all: hex0.elf hex1.elf

hex0.elf: shell.s core.s link.ld input.hex
	$(CC) $(ASFLAGS) $(LDFLAGS) -o $@ shell.s core.s

hex1.elf: shell1.s core1.s link.ld input1.hex
	$(CC) $(ASFLAGS) $(LDFLAGS) -o $@ shell1.s core1.s

# Raw bytes of the loaded image (what the proof ultimately concerns).
hex0.bin: hex0.elf
	$(OBJCOPY) -O binary $< $@

hex1.bin: hex1.elf
	$(OBJCOPY) -O binary $< $@

# Disassembly of the proof target only.
dis: hex0.elf
	$(OBJDUMP) -d $< --section=.text

dis1: hex1.elf
	$(OBJDUMP) -d $< --section=.text

run: hex0.elf
	$(RUNENV) $(QEMU) $(QFLAGS) hex0.elf

run1: hex1.elf
	$(RUNENV) $(QEMU) $(QFLAGS) hex1.elf

# The LowIR-compiled library blob. progmain.bin/.inc/.expected are emitted by
#   cd ../lean && lake env lean --run DumpProgMain.lean
progmain.elf: shellmain.s progmain.bin progmain.inc link.ld
	$(CC) $(ASFLAGS) $(LDFLAGS) -o $@ shellmain.s

run-progmain: progmain.elf
	$(RUNENV) $(QEMU) $(QFLAGS) progmain.elf

# Disassemble the compiled blob as raw code (gas marks .incbin data with a
# $d mapping symbol, so objdump -d on the ELF renders it as .word). Raw-bin
# addresses = blob byte offsets = the Lean fn table (progmain.inc MAIN_OFF).
# no-aliases so the mnemonics can be eyeballed against the 16-encoding
# trusted surface. For the (unverified) shim: $(OBJDUMP) -d progmain.elf.
dismain: progmain.bin
	$(OBJDUMP) -D -b binary -m riscv:rv64 -M no-aliases progmain.bin

clean:
	rm -f hex0.elf hex0.bin hex1.elf hex1.bin progmain.elf

.PHONY: all dis dis1 dismain run run1 run-progmain clean
