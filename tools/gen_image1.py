#!/usr/bin/env python3
"""Extract core1+input bytes/addresses from bare/hex1.elf and emit the Lean and
Coq image modules used by the hex1 validation harnesses. Addresses are read
from the ELF symbol table (objdump -t). Auto-generated outputs; do not edit
them by hand."""
import subprocess

BASE = 0x80000000
ELF = '/var/data/bootstrap/bare/hex1.elf'

syms = {}
for line in subprocess.run(['riscv64-linux-gnu-objdump', '-t', ELF],
                           capture_output=True, text=True).stdout.splitlines():
    parts = line.split()
    if len(parts) >= 4 and all(ch in '0123456789abcdef' for ch in parts[0]):
        syms[parts[-1]] = int(parts[0], 16)

core_addr = syms['core1']
in_addr, in_end = syms['input_start'], syms['input_end']
out_addr = syms['out_buf']
lbl_addr = syms['lbl_buf']
# core1 runs from its symbol to the start of .rodata (end of .text contents).
sections = subprocess.run(['riscv64-linux-gnu-objdump', '-h', ELF],
                          capture_output=True, text=True).stdout
text_end = None
for line in sections.splitlines():
    parts = line.split()
    if len(parts) >= 5 and parts[1] == '.text':
        text_end = int(parts[3], 16) + int(parts[2], 16)
core_len = text_end - core_addr

data = open('/var/data/bootstrap/bare/hex1.bin', 'rb').read()
core = data[core_addr - BASE: core_addr - BASE + core_len]
inp = data[in_addr - BASE: in_end - BASE]


def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"


def zlst(b):
    return "[" + "; ".join(str(x) for x in b) + "]"


lean = f'''/- AUTO-GENERATED from bare/hex1.elf by tools/gen_image1.py. Do not edit. -/
namespace Rv64i.Image1
def coreAddr  : Nat := {core_addr}
def inputAddr : Nat := {in_addr}
def inputLen  : Nat := {in_end - in_addr}
def outAddr   : Nat := {out_addr}
def lblAddr   : Nat := {lbl_addr}
def coreBytes  : List Nat := {lst(core)}
def inputBytes : List Nat := {lst(inp)}
end Rv64i.Image1
'''
open('/var/data/bootstrap/lean/Hex1/Image.lean', 'w').write(lean)

coq = f'''(* AUTO-GENERATED from bare/hex1.elf by tools/gen_image1.py. Do not edit. *)
From Coq Require Import ZArith List. Import ListNotations.
Local Open Scope Z_scope.
Definition coreAddr  : Z := {core_addr}.
Definition inputAddr : Z := {in_addr}.
Definition inputLen  : Z := {in_end - in_addr}.
Definition outAddr   : Z := {out_addr}.
Definition lblAddr   : Z := {lbl_addr}.
Definition coreBytes  : list Z := {zlst(core)}.
Definition inputBytes : list Z := {zlst(inp)}.
'''
open('/var/data/bootstrap/coq/Image1.v', 'w').write(coq)

print(f"core1: addr={core_addr:#x} len={len(core)} "
      f"input: addr={in_addr:#x} len={len(inp)} out={out_addr:#x} lbl={lbl_addr:#x}")
