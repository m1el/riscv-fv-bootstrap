#!/usr/bin/env python3
"""Differential tests for hex1 (HEX1.md): an independent Python oracle vs
   1. the C reference (tools/hex1_drv), and
   2. the ASSEMBLY proof target bare/core1.s (tools/core1_drv via qemu-riscv64).

Usage: python3 tools/test_hex1.py [--quick]
Build first:
  gcc -O2 -o tools/hex1_drv tools/hex1_drv.c
  riscv64-linux-gnu-gcc -O2 -static -o tools/core1_drv tools/core1_drv.c bare/core1.s
"""
import os
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENV = dict(os.environ, LD_LIBRARY_PATH=str(ROOT / ".libshim"))
IMPLS = [
    ("c", [str(ROOT / "tools" / "hex1_drv")]),
    ("asm", ["qemu-riscv64", str(ROOT / "tools" / "core1_drv")]),
]

OK, SHORT, SPLIT, TRAILNIB, UNKNOWN, DUP, UNDEF, TRAILTOK = 0, 2, 3, 4, 5, 6, 7, 8
STOP = frozenset(b" _\n#;:%")


def is_nib(c: int) -> bool:
    return 0x30 <= c <= 0x39 or 0x41 <= c <= 0x46


def nib(c: int) -> int:
    return c - 0x30 if c <= 0x39 else c - 0x37


def oracle(inp: bytes, cap: int):
    """Two-phase spec from HEX1.md. Returns (status, output_bytes)."""
    # Phase 1: scan -- grammar, capacity, labels.
    labels = {}
    i, pos = 0, 0
    while i < len(inp):
        c = inp[i]
        i += 1
        if c in b"#;":
            while i < len(inp) and inp[i] != 0x0A:
                i += 1
            continue
        if c in b" _\n":
            continue
        if c == 0x3A:  # ':'
            if i >= len(inp):
                return TRAILTOK, b""
            lbl = inp[i]
            i += 1
            if lbl in labels:
                return DUP, b""
            labels[lbl] = pos
            continue
        if c == 0x25:  # '%'
            if i >= len(inp):
                return TRAILTOK, b""
            i += 1
            if cap - pos < 4:
                return SHORT, b""
            pos += 4
            continue
        if not is_nib(c):
            return UNKNOWN, b""
        if i >= len(inp):
            return TRAILNIB, b""
        c2 = inp[i]
        i += 1
        if c2 in STOP:
            return SPLIT, b""
        if not is_nib(c2):
            return UNKNOWN, b""
        if pos >= cap:
            return SHORT, b""
        pos += 1
    # Phase 2: emit -- bytes + reference resolution.
    out = bytearray()
    i = 0
    while i < len(inp):
        c = inp[i]
        i += 1
        if c in b"#;":
            while i < len(inp) and inp[i] != 0x0A:
                i += 1
            continue
        if c in b" _\n":
            continue
        if c == 0x3A:
            i += 1
            continue
        if c == 0x25:
            lbl = inp[i]
            i += 1
            if lbl not in labels:
                return UNDEF, bytes(out)
            off = (labels[lbl] - (len(out) + 4)) & 0xFFFFFFFF
            out += off.to_bytes(4, "little")
            continue
        out.append((nib(c) << 4) | nib(inp[i]))
        i += 1
    return OK, bytes(out)


def run_impl(cmd, inp: bytes, cap: int):
    p = subprocess.run(cmd + [str(cap)], input=inp, capture_output=True, env=ENV)
    return p.returncode, p.stdout


def check(inp: bytes, cap: int, tag: str = ""):
    want = oracle(inp, cap)
    msgs = []
    for name, cmd in IMPLS:
        got = run_impl(cmd, inp, cap)
        if want != got:
            msgs.append(
                f"FAIL[{name}] {tag} inp={inp!r} cap={cap}\n"
                f"  want={want}\n  got ={got}"
            )
    return msgs


def le32(v: int) -> bytes:
    return (v & 0xFFFFFFFF).to_bytes(4, "little")


def expect(inp: bytes, cap: int, status: int, out: bytes, tag: str):
    """Pin oracle AND both implementations to a hand-computed expectation."""
    msgs = []
    o = oracle(inp, cap)
    if o != (status, out):
        msgs.append(f"FAIL[oracle] {tag}: want {(status, out)}, got {o}")
    msgs.extend(check(inp, cap, tag))
    return msgs


def main():
    quick = "--quick" in sys.argv
    for _, cmd in IMPLS:
        if not Path(cmd[-1]).exists():
            sys.exit(f"missing {cmd[-1]}; see module docstring for build lines")

    fails = []
    # --- Hand-computed expectations (spec examples + error classes) ---
    pinned = [
        (b"", 16, OK, b"", "empty"),
        (b"48 65 6C 6C 6F 0A", 16, OK, b"Hello\n", "plain hex0"),
        (b"# only a comment", 16, OK, b"", "comment only"),
        (b"%A :A", 16, OK, le32(0), "fwd ref, label at field end"),
        (b":A 00 %A", 16, OK, b"\x00" + le32(-5), "back ref"),
        (b":A%A", 16, OK, le32(-4), "back ref, adjacent"),
        (b":: 00 %:", 16, OK, b"\x00" + le32(-5), "label byte is ':'"),
        (b":% 00 %%", 16, OK, b"\x00" + le32(-5), "label byte is '%'"),
        (b":# 00 %#", 16, OK, b"\x00" + le32(-5), "label byte is '#'"),
        (b":\n 00 %\n", 16, OK, b"\x00" + le32(-5), "label byte is newline"),
        (b":\x00 00 %\x00", 16, OK, b"\x00" + le32(-5), "label byte is NUL"),
        (b":A 00 :B %B", 16, OK, b"\x00" + le32(-4), "two labels"),
        (b"%A 00 :A %A", 16, OK, le32(1) + b"\x00" + le32(-4), "fwd+back"),
        (b"%A%A:A", 16, OK, le32(4) + le32(0), "double fwd ref"),
        (b":A :A", 16, DUP, b"", "duplicate label"),
        (b":A 00 :A", 16, DUP, b"", "duplicate label after byte"),
        (b"%Z", 16, UNDEF, b"", "undefined label"),
        (b"00 %Z", 16, UNDEF, b"\x00", "undefined label, partial out"),
        (b"%q G", 16, UNKNOWN, b"", "phase-1 beats UndefinedLabel"),
        (b"4:", 16, SPLIT, b"", "':' splits nibble"),
        (b"4%", 16, SPLIT, b"", "'%' splits nibble"),
        (b"4 ", 16, SPLIT, b"", "space splits nibble"),
        (b"4", 16, TRAILNIB, b"", "trailing nibble"),
        (b":", 16, TRAILTOK, b"", "EOF after ':'"),
        (b"%", 16, TRAILTOK, b"", "EOF after '%'"),
        (b"G", 16, UNKNOWN, b"", "unknown char"),
        (b"4G", 16, UNKNOWN, b"", "unknown low nibble"),
        (b"00 11", 1, SHORT, b"", "byte capacity"),
        (b"%A :A", 3, SHORT, b"", "field capacity"),
        (b"00 %A :A", 4, SHORT, b"", "field capacity straddles"),
        (b"%A :A", 4, OK, le32(0), "field exactly fits"),
        (b"# x\n:A 00 %A ; y", 16, OK, b"\x00" + le32(-5), "comments"),
        (b";:A\n%A", 16, UNDEF, b"", "':A' inside comment is text"),
        (b":A;def\n%A", 16, OK, le32(-4), "comment between def and ref"),
        (b":G%G", 16, OK, le32(-4), "non-hex label byte"),
        (b"".join(b":" + bytes([c]) for c in range(256)) + b"%\xff",
         16, OK, le32(-4), "all 256 labels definable"),
    ]

    # --- Fuzz: random inputs over a hostile alphabet, random caps ---
    rng = random.Random(0x4845_5831)
    cases = []
    alphabet = b"0123456789ABCDEF" b"Ga\x00\xff\x80" b" _\n#;:%" b"45"
    n_fuzz = 2000 if quick else 20000
    for trial in range(n_fuzz):
        n = rng.randrange(0, 32)
        inp = bytes(rng.choice(alphabet) for _ in range(n))
        cap = rng.choice([0, 1, 2, 3, 4, 5, 7, 8, 64, 64, 64])
        cases.append((inp, cap, f"fuzz{trial}"))
    n_long = 200 if quick else 2000
    for trial in range(n_long):
        n = rng.randrange(0, 200)
        inp = bytes(rng.choice(b"0F:%AB \n#;") for _ in range(n))
        cap = rng.choice([0, 5, 16, 4096])
        cases.append((inp, cap, f"fuzzL{trial}"))

    with ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        for msgs in pool.map(lambda a: expect(*a), pinned):
            fails.extend(msgs)
        for msgs in pool.map(lambda a: check(*a), cases):
            fails.extend(msgs)

    for m in fails[:40]:
        print(m)
    if fails:
        sys.exit(f"{len(fails)} FAILURES")
    print(f"all hex1 tests passed on {[n for n, _ in IMPLS]}: "
          f"{len(pinned)} pinned + {len(cases)} fuzz")


if __name__ == "__main__":
    main()
