#!/usr/bin/env python3
"""Generate lean/Hex1/DecodeFacts.lean: one kernel-checked decode fact per
core1 instruction, parsed from objdump. Auto-generated; do not edit output."""
import re
import subprocess

ELF = '/var/data/bootstrap/bare/hex1.elf'
CORE_ADDR = None

out = subprocess.run(
    ['riscv64-linux-gnu-objdump', '-d', '-M', 'no-aliases,numeric', ELF,
     '--section=.text'],
    capture_output=True, text=True).stdout

# find core1 start
for line in out.splitlines():
    m = re.match(r'^([0-9a-f]+) <core1>:', line)
    if m:
        CORE_ADDR = int(m.group(1), 16)
assert CORE_ADDR is not None

X = r'x(\d+)'


def bv(width, value):
    return f"(BitVec.ofNat {width} {value % (1 << width)})"


insns = []
in_core = False
for line in out.splitlines():
    if re.match(r'^[0-9a-f]+ <core1>:', line):
        in_core = True
        continue
    if re.match(r'^[0-9a-f]+ <\w+>:', line):
        in_core = False
        continue
    if not in_core:
        continue
    m = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S+)\s*(.*)$', line)
    if not m:
        continue
    addr, word, mnem, ops = int(m.group(1), 16), m.group(2), m.group(3), m.group(4).strip()
    off = addr - CORE_ADDR
    ops = ops.split('#')[0].strip()  # strip objdump comments
    term = None
    if mnem == 'addi':
        rd, rs1, imm = re.match(rf'{X},{X},(-?\d+)', ops).groups()
        term = f"Rv64i.Instr.addi {rd} {rs1} {bv(12, int(imm))}"
    elif mnem in ('add', 'sub', 'or'):
        rd, rs1, rs2 = re.match(rf'{X},{X},{X}', ops).groups()
        term = f"Rv64i.Instr.{mnem} {rd} {rs1} {rs2}"
    elif mnem in ('slli', 'srli'):
        rd, rs1, sh = re.match(rf'{X},{X},0x([0-9a-f]+)', ops).groups()
        term = f"Rv64i.Instr.{mnem} {rd} {rs1} {int(sh, 16)}"
    elif mnem in ('lbu', 'ld'):
        rd, imm, rs1 = re.match(rf'{X},(-?\d+)\({X}\)', ops).groups()
        term = f"Rv64i.Instr.{mnem} {rd} {rs1} {bv(12, int(imm))}"
    elif mnem in ('sb', 'sd'):
        rs2, imm, rs1 = re.match(rf'{X},(-?\d+)\({X}\)', ops).groups()
        # model order: sb rs1 rs2 imm (rs1 = base)
        term = f"Rv64i.Instr.{mnem} {rs1} {rs2} {bv(12, int(imm))}"
    elif mnem in ('beq', 'blt', 'bge', 'bgeu'):
        rs1, rs2, tgt = re.match(rf'{X},{X},([0-9a-f]+)', ops).groups()
        delta = int(tgt, 16) - addr
        term = f"Rv64i.Instr.{mnem} {rs1} {rs2} {bv(13, delta)}"
    elif mnem == 'jal':
        rd, tgt = re.match(rf'{X},([0-9a-f]+)', ops).groups()
        delta = int(tgt, 16) - addr
        term = f"Rv64i.Instr.jal {rd} {bv(21, delta)}"
    elif mnem == 'jalr':
        rd, imm, rs1 = re.match(rf'{X},(-?\d+)\({X}\)', ops).groups()
        term = f"Rv64i.Instr.jalr {rd} {rs1} {bv(12, int(imm))}"
    else:
        raise SystemExit(f"unhandled mnemonic {mnem!r} at {addr:#x}: {line}")
    insns.append((off, word, mnem, ops, term))

lines = [
    "/- AUTO-GENERATED from bare/hex1.elf by tools/gen_decode1.py. Do not edit.",
    "   One kernel-checked decode fact per core1 instruction. -/",
    "import Hex1.RefineBase",
    "open Rv64i",
    "",
    "namespace Hex1.Refine",
    "",
    "set_option maxRecDepth 8000",
    "",
    "theorem coreBytes_len : Image1.coreBytes.length = 724 := by decide",
    "",
]
for off, word, mnem, ops, term in insns:
    lines.append(f"/-- `{off:4d}: {word}  {mnem} {ops}` -/")
    lines.append(f"theorem dec_{off} : Rv64i.decode (wordAt1 {off}) = {term} := by decide")
lines.append("")
lines.append("end Hex1.Refine")
open('/var/data/bootstrap/lean/Hex1/DecodeFacts.lean', 'w').write("\n".join(lines) + "\n")
print(f"core1 at {CORE_ADDR:#x}: {len(insns)} instructions, "
      f"{len(insns)*4} bytes")
