#!/usr/bin/env python3
"""Extract core+input bytes/addresses from bare/hex0.elf and emit the Lean and
Coq image modules used by the validation harnesses. Auto-generated outputs; do
not edit them by hand."""
data = open('/var/data/bootstrap/bare/hex0.bin', 'rb').read()
base = 0x80000000
core_addr, core_len = 0x80000088, 0x144
in_addr, in_end = 0x800001cc, 0x8000021c
out_addr = 0x800003b0
core = data[core_addr - base: core_addr - base + core_len]
inp = data[in_addr - base: in_end - base]

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def zlst(b):
    return "[" + "; ".join(str(x) for x in b) + "]"

# ---- Lean ----
lean = f'''/- AUTO-GENERATED from bare/hex0.elf by tools/gen_image.py. Do not edit. -/
namespace Rv64i.Image
def coreAddr  : Nat := {core_addr}
def inputAddr : Nat := {in_addr}
def inputLen  : Nat := {in_end - in_addr}
def outAddr   : Nat := {out_addr}
def coreBytes  : List Nat := {lst(core)}
def inputBytes : List Nat := {lst(inp)}
end Rv64i.Image
'''
open('/var/data/bootstrap/lean/Hex0/Image.lean', 'w').write(lean)

# ---- Coq ----
coq = f'''(* AUTO-GENERATED from bare/hex0.elf by tools/gen_image.py. Do not edit. *)
From Coq Require Import ZArith List. Import ListNotations.
Local Open Scope Z_scope.
Definition coreAddr  : Z := {core_addr}.
Definition inputAddr : Z := {in_addr}.
Definition inputLen  : Z := {in_end - in_addr}.
Definition outAddr   : Z := {out_addr}.
Definition coreBytes  : list Z := {zlst(core)}.
Definition inputBytes : list Z := {zlst(inp)}.
'''
open('/var/data/bootstrap/coq/Image.v', 'w').write(coq)

print(f"core_len={len(core)} input_len={len(inp)} input={inp!r}")
