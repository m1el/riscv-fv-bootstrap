data = open('/var/data/bootstrap/bare/hex0.bin','rb').read()
base = 0x80000000
core_addr, core_len = 0x80000088, 0x144
in_addr,  in_end    = 0x800001cc, 0x8000021c
out_addr            = 0x800003b0
core = data[core_addr-base : core_addr-base+core_len]
inp  = data[in_addr-base   : in_end-base]
def lst(b): return "[" + ", ".join(str(x) for x in b) + "]"
out = f'''/- AUTO-GENERATED from bare/hex0.elf by tools/gen_image.py. Do not edit. -/
namespace Rv64i.Image
def coreAddr  : Nat := {core_addr}
def inputAddr : Nat := {in_addr}
def inputLen  : Nat := {in_end-in_addr}
def outAddr   : Nat := {out_addr}
def coreBytes  : List Nat := {lst(core)}
def inputBytes : List Nat := {lst(inp)}
end Rv64i.Image
'''
open('/var/data/bootstrap/lean/Hex0/Image.lean','w').write(out)
print(f"core_len={len(core)} input_len={len(inp)} input={inp!r}")
