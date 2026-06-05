#!/usr/bin/env python3
"""Generate the regular li-chain lemmas for coq/Refine1.v chunk 10 (pass-1
byte path): p1_fall_tail, p1_high_ok/unk, p1_stop_split, p1_stop_fall,
p1_low_ok/unk.  Mirrors the hand-written p1_pct_tail / p1_colon_tail idiom:
li1_{beq,blt,bge}_{ne,eq,nt,t} blocks chained through states sB, sC, ...
with per-state CodeLoaded1/pc/rget-7 asserts, runUntil composition, and the
mem/frame epilogue.  Output: Coq text on stdout (paste into Refine1.v)."""

STATE = "BCDEFGHIJK"


def z(i):
    return f"({i})" if i < 0 else str(i)


def chain(s0, blocks, bullet):
    """Emit the block chain.  blocks: (kind, off, K, imm, tgt_or_None).
    Returns (lines, hbs, states, Ks, final_expr)."""
    L, hbs, states, Ks = [], [], [], []
    cur, hc, hpc, h7 = s0, "hcode", "hpc", "h7"
    for j, (kind, off, K, imm, tgt) in enumerate(blocks):
        hb = f"hb{j+1}"
        hbs.append(hb)
        Ks.append(K)
        lem = {"beq_ne": "li1_beq_ne", "beq_eq": "li1_beq_eq",
               "blt_nt": "li1_blt_nt", "blt_t": "li1_blt_t",
               "bge_nt": "li1_bge_nt", "bge_t": "li1_bge_t"}[kind]
        if kind == "beq_ne":
            tail = "ltac:(lia) ltac:(lia)"
        elif kind == "beq_eq":
            tail = "ltac:(lia) He"
        else:
            tail = "ltac:(lia) ltac:(lia) ltac:(lia)"
        tgt_arg = f" (Image1.coreAddr + {tgt})" if tgt is not None else ""
        line = (f"pose proof ({lem} {cur} {off} {K} c {z(imm)}{tgt_arg} {hc} ltac:(lia)\n"
                f"  ltac:(rewrite coreBytes1_len; lia) {hpc} {h7} ltac:(vm_compute; reflexivity)\n"
                f"  ltac:(vm_compute; reflexivity) {tail}")
        if tgt is not None:
            line += (f"\n  ltac:(rewrite (wadd_id (Image1.coreAddr + ({off} + 4)) {z(imm)}\n"
                     f"          ltac:(unfold Image1.coreAddr; lia)); lia)) as {hb}.")
            ex = f"setPc (rset {cur} 28 {K}) (Image1.coreAddr + {tgt})"
            npc_val = tgt
        else:
            line += f") as {hb}."
            ex = f"setPc (rset {cur} 28 {K}) (Image1.coreAddr + ({off} + 8))"
            npc_val = off + 8
        L.append(line)
        if j == len(blocks) - 1:
            return L, hbs, states, Ks, ex
        nxt = f"s{STATE[j]}"
        states.append(nxt)
        L.append(f"set ({nxt} := {ex}) in *.")
        nhc, nhpc, nh7 = f"hc{STATE[j]}", f"hpc{STATE[j]}", f"h7{STATE[j]}"
        L.append(f"assert ({nhc} : CodeLoaded1 {nxt}) by\n"
                 f"  (apply (CodeLoaded1_eqmem {cur}); [unfold {nxt}; rewrite setPc_mem, rset_mem; reflexivity| exact {hc}]).")
        L.append(f"assert ({nhpc} : {nxt}.(pc) = Image1.coreAddr + {npc_val}) by (unfold {nxt}; cbn; lia).")
        L.append(f"assert ({nh7} : rget {nxt} 7 = c) by\n"
                 f"  (unfold {nxt}; rewrite (li_block_frame {cur} {K} _ 7 ltac:(lia)); exact {h7}).")
        cur, hc, hpc, h7 = nxt, nhc, nhpc, nh7


def sum_expr(parts):
    e = parts[-1]
    for p in reversed(parts[:-1]):
        e = f"{p} + ({e})"
    return e


def mem_lines(states, jal_state=None):
    L = []
    if jal_state is not None:
        L.append("rewrite setPc_mem.")
        L.append(f"unfold {jal_state}. rewrite setPc_mem, rset_mem.")
    else:
        L.append("rewrite setPc_mem, rset_mem.")
    for st in reversed(states):
        L.append(f"unfold {st}. rewrite setPc_mem, rset_mem.")
    L.append("reflexivity.")
    return L


def frame_lines(s0, states, Ks, jal_state=None):
    """states: intermediate states (set'd), Ks: all block Ks."""
    L = ["intros i hir."]
    allst = states + ([jal_state] if jal_state else [])
    if jal_state is not None:
        L.append("rewrite setPc_rget.")
    # outermost: last block's rset
    prevs = ([s0] + states)  # prev state of block j is prevs[j]
    if jal_state is not None:
        # jal_state := setPc (rset prevs[-1] 28 Ks[-1]) _
        L.append(f"unfold {jal_state}. rewrite (li_block_frame {prevs[-1]} {Ks[-1]} _ i hir).")
    else:
        L.append(f"rewrite (li_block_frame {prevs[-1]} {Ks[-1]} _ i hir).")
    for j in range(len(states) - 1, -1, -1):
        L.append(f"unfold {states[j]}. rewrite (li_block_frame {prevs[j]} {Ks[j]} _ i hir).")
    L.append("reflexivity.")
    return L


def indent(lines, pad):
    return "\n".join(pad + ln.replace("\n", "\n" + pad) for ln in lines)


def gen_fixed(name, comment, start, target, blocks, nes):
    nsteps = 2 * len(blocks)
    body, hbs, states, Ks, final = chain("s4", blocks, "-")
    txt = [f"(* {comment} *)"]
    txt.append(f"Lemma {name} s4 c :")
    txt.append(f"  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + {start} -> rget s4 7 = c ->")
    txt.append("  0 <= c < 256 ->")
    txt.append("  " + " -> ".join(f"c <> {k}" for k in nes) + " ->")
    txt.append(f"  exists s', runUntil 0 {nsteps} s4 = s' /\\")
    txt.append(f"    s'.(pc) = Image1.coreAddr + {target} /\\ s'.(mem) = s4.(mem) /\\ CodeLoaded1 s' /\\")
    txt.append("    (forall i, i <> 28 -> rget s' i = rget s4 i).")
    txt.append("Proof.")
    txt.append("  intros hcode hpc h7 hcr " + " ".join(f"hne{j+1}" for j in range(len(nes))) + ".")
    txt.append(indent(body, "  "))
    txt.append(f"  exists ({final}).")
    txt.append("  split.")
    txt.append(f"  {{ replace {nsteps}%nat with ({sum_expr(['2']*len(blocks))})%nat by lia.")
    rw = ", ".join([f"runUntil_add, {h}" for h in hbs[:-1]] + [hbs[-1]])
    txt.append(f"    rewrite {rw}. reflexivity. }}")
    txt.append("  repeat apply conj.")
    txt.append("  - apply setPc_pc.")
    txt.append("  - " + indent(mem_lines(states), "    ").lstrip())
    last_hc = "hc" + STATE[len(states) - 1]
    txt.append(f"  - apply (CodeLoaded1_eqmem {states[-1]});")
    txt.append(f"      [rewrite setPc_mem, rset_mem; reflexivity| exact {last_hc}].")
    txt.append("  - " + indent(frame_lines("s4", states, Ks), "    ").lstrip())
    txt.append("Qed.")
    return "\n".join(txt) + "\n"


def gen_arm(blocks, target, jal=None, pad="    "):
    """One arm (inside a `-` bullet) of a variable-k lemma.  Inner bullets `+`."""
    body, hbs, states, Ks, final = chain("s4", blocks, "+")
    L = list(body)
    n = len(blocks)
    k = 2 * n + (1 if jal else 0)
    if jal is not None:
        joff, jimm = jal
        sJ = f"s{STATE[n-1]}"
        last_hc = ("hc" + STATE[n - 2]) if n >= 2 else "hcode"
        last_st = states[-1] if states else "s4"
        L.append(f"set ({sJ} := {final}) in *.")
        L.append(f"assert (hcJ : CodeLoaded1 {sJ}) by\n"
                 f"  (apply (CodeLoaded1_eqmem {last_st}); [unfold {sJ}; rewrite setPc_mem, rset_mem; reflexivity| exact {last_hc}]).")
        L.append(f"assert (hpcJ : {sJ}.(pc) = Image1.coreAddr + {joff}) by (unfold {sJ}; cbn; lia).")
        L.append(f"assert (huJ : step {sJ} = setPc {sJ} (Image1.coreAddr + {target})).")
        L.append(f"{{ rewrite (step1_jal {sJ} {joff} 0 {jimm} hcJ ltac:(lia)\n"
                 f"    ltac:(rewrite coreBytes1_len; lia) hpcJ ltac:(vm_compute; reflexivity)),\n"
                 f"    rset_zero, hpcJ, (wadd_id (Image1.coreAddr + {joff}) {jimm}\n"
                 f"      ltac:(unfold Image1.coreAddr; lia)).\n"
                 f"  f_equal; lia. }}")
        L.append(f"assert (hpJ : {sJ}.(pc) <> 0) by (rewrite hpcJ; unfold Image1.coreAddr; lia).")
        L.append(f"exists {k}%nat. split; [lia|].")
        L.append(f"replace {k}%nat with ({sum_expr(['2']*n + ['1'])})%nat by lia.")
        rw = ", ".join(f"runUntil_add, {h}" for h in hbs)
        L.append(f"rewrite {rw}, (runUntil_one {sJ} hpJ), huJ.")
        L.append("repeat apply conj.")
        L.append("+ apply setPc_pc.")
        L.append("+ " + "\n  ".join(mem_lines(states, jal_state=sJ)))
        L.append("+ " + "\n  ".join(frame_lines("s4", states, Ks, jal_state=sJ)))
    else:
        L.append(f"exists {k}%nat. split; [lia|].")
        se = sum_expr(['2']*n)
        if se != str(k):
            L.append(f"replace {k}%nat with ({se})%nat by lia.")
        rw = ", ".join([f"runUntil_add, {h}" for h in hbs[:-1]] + [hbs[-1]])
        L.append(f"rewrite {rw}.")
        L.append("repeat apply conj.")
        L.append("+ apply setPc_pc.")
        L.append("+ " + "\n  ".join(mem_lines(states)))
        L.append("+ " + "\n  ".join(frame_lines("s4", states, Ks)))
    return indent(L, pad)


def var_lemma_header(name, comment, base, hyp, kmax, target):
    txt = [f"(* {comment} *)"]
    txt.append(f"Lemma {name} s4 c{' hi' if 'Some' in hyp else ''} :")
    txt.append(f"  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + {base} -> rget s4 7 = c ->")
    txt.append(f"  0 <= c < 256 -> {hyp} ->")
    txt.append(f"  exists k, (0 < k <= {kmax})%nat /\\")
    txt.append(f"    (runUntil 0 k s4).(pc) = Image1.coreAddr + {target} /\\")
    txt.append(f"    (runUntil 0 k s4).(mem) = s4.(mem) /\\")
    txt.append(f"    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).")
    txt.append("Proof.")
    return txt


def gen_ok(name, comment, base):
    i48 = 676 - (base + 4)
    i65 = 676 - (base + 24)
    i71 = 676 - (base + 32)
    txt = var_lemma_header(name, comment, base, "nibble (Z.to_nat c) = Some hi", 8, base + 36)
    txt.append("  intros hcode hpc h7 hcr hn.")
    txt.append("  destruct (nibble_cases c hi ltac:(lia) hn) as [[Hr _]|[Hr _]].")
    txt.append("  - (* digit: blt48 nt, bge58 nt, jal *)")
    txt.append(gen_arm([("blt_nt", base, 48, i48, None),
                        ("bge_nt", base + 8, 58, 8, None)],
                       base + 36, jal=(base + 16, 20)))
    txt.append("  - (* letter: blt48 nt, bge58 taken, blt65 nt, bge71 nt *)")
    txt.append(gen_arm([("blt_nt", base, 48, i48, None),
                        ("bge_t", base + 8, 58, 8, base + 20),
                        ("blt_nt", base + 20, 65, i65, None),
                        ("bge_nt", base + 28, 71, i71, None)],
                       base + 36))
    txt.append("Qed.")
    return "\n".join(txt) + "\n"


def gen_unk(name, comment, base):
    i48 = 676 - (base + 4)
    i65 = 676 - (base + 24)
    i71 = 676 - (base + 32)
    txt = var_lemma_header(name, comment, base, "nibble (Z.to_nat c) = None", 8, 676)
    txt.append("  intros hcode hpc h7 hcr hn.")
    txt.append("  destruct (nibble_none_cases c ltac:(lia) hn) as [Hr|[Hr|Hr]].")
    txt.append("  - (* c < 48: blt48 taken *)")
    txt.append(gen_arm([("blt_t", base, 48, i48, 676)], 676))
    txt.append("  - (* 57 < c < 65: blt48 nt, bge58 taken, blt65 taken *)")
    txt.append(gen_arm([("blt_nt", base, 48, i48, None),
                        ("bge_t", base + 8, 58, 8, base + 20),
                        ("blt_t", base + 20, 65, i65, 676)], 676))
    txt.append("  - (* 70 < c: blt48 nt, bge58 taken, blt65 nt, bge71 taken *)")
    txt.append(gen_arm([("blt_nt", base, 48, i48, None),
                        ("bge_t", base + 8, 58, 8, base + 20),
                        ("blt_nt", base + 20, 65, i65, None),
                        ("bge_t", base + 28, 71, i71, 676)], 676))
    txt.append("Qed.")
    return "\n".join(txt) + "\n"


def gen_stop_split():
    offs = [160, 168, 176, 184, 192, 200, 208]
    Ks = [10, 32, 95, 35, 59, 58, 37]
    txt = ["(* low-char stop check (160..212), stop case: the matching beq fires",
           "   -> split exit 652. *)"]
    txt.append("Lemma p1_stop_split s4 c :")
    txt.append("  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 160 -> rget s4 7 = c ->")
    txt.append("  0 <= c < 256 -> isLowStop1 (Z.to_nat c) = true ->")
    txt.append("  exists k, (0 < k <= 14)%nat /\\")
    txt.append("    (runUntil 0 k s4).(pc) = Image1.coreAddr + 652 /\\")
    txt.append("    (runUntil 0 k s4).(mem) = s4.(mem) /\\")
    txt.append("    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).")
    txt.append("Proof.")
    txt.append("  intros hcode hpc h7 hcr hstop.")
    txt.append("  destruct (isLowStop1_cases c ltac:(lia) hstop)")
    txt.append("    as [He|[He|[He|[He|[He|[He|He]]]]]].")
    for j in range(7):
        txt.append(f"  - (* c = {Ks[j]} *)")
        blocks = [("beq_ne", offs[i], Ks[i], 652 - (offs[i] + 4), None) for i in range(j)]
        blocks.append(("beq_eq", offs[j], Ks[j], 652 - (offs[j] + 4), 652))
        txt.append(gen_arm(blocks, 652))
    txt.append("Qed.")
    return "\n".join(txt) + "\n"


parts = [
    gen_fixed("p1_fall_tail",
              "dispatch 52 -> 108 for a hex-digit first char (7 not-taken blocks): 14 steps",
              52, 108,
              [("beq_ne", 52, 35, 276, None), ("beq_ne", 60, 59, 268, None),
               ("beq_ne", 68, 10, -36, None), ("beq_ne", 76, 32, -44, None),
               ("beq_ne", 84, 95, -52, None), ("beq_ne", 92, 58, 168, None),
               ("beq_ne", 100, 37, 200, None)],
              [35, 59, 10, 32, 95, 58, 37]),
    gen_ok("p1_high_ok",
           "high-nibble range check (108..140), valid: fall to the low read at 144", 108),
    gen_unk("p1_high_unk",
            "high-nibble range check (108..140), invalid: Unknown exit 676", 108),
    gen_stop_split(),
    gen_fixed("p1_stop_fall",
              "low-char stop check (160..212), no stop matches (7 not-taken blocks): 14 steps",
              160, 216,
              [("beq_ne", 160, 10, 488, None), ("beq_ne", 168, 32, 480, None),
               ("beq_ne", 176, 95, 472, None), ("beq_ne", 184, 35, 464, None),
               ("beq_ne", 192, 59, 456, None), ("beq_ne", 200, 58, 448, None),
               ("beq_ne", 208, 37, 440, None)],
              [10, 32, 95, 35, 59, 58, 37]),
    gen_ok("p1_low_ok",
           "low-nibble range check (216..248), valid: fall to the count at 252", 216),
    gen_unk("p1_low_unk",
            "low-nibble range check (216..248), invalid: Unknown exit 676", 216),
]

print("\n".join(parts))
