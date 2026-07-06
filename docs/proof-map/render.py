#!/usr/bin/env python3
"""Render contracted.json + layout.json -> progsim-map.html (narrow vertical)."""
import json, html, math

C = json.load(open('contracted.json'))
L = json.load(open('layout.json'))
boxes = L['boxes']; edges = L['edges']
majors = {m['name']: m for m in C['majors']}
stats = C['stats']

GROUPS = [
    ('StmtSim',      ['LowIR.ProgSim.StmtSim']),
    ('CtrlSim',      ['LowIR.ProgSim.CtrlSim']),
    ('ExecFacts',    ['LowIR.ProgSim.ExecFacts']),
    ('LowerFacts',   ['LowIR.ProgSim.LowerFacts']),
    ('Layout/Slots', ['LowIR.ProgSim.LayoutFacts', 'LowIR.ProgSim.SlotFacts']),
    ('AsmFacts',     ['LowIR.ProgSim.AsmFacts', 'LowIR.ProgSim.EncodeFacts']),
    ('Memory',       ['LowIR.ProgSim.MemFacts', 'LowIR.ProgSim.WordMem']),
    ('IL / Defs',    ['LowIR.ProgSim.Defs', 'LowIR.Prog']),
    ('Summit',       ['LowIR.ProgSim.Main']),
]
MOD2G = {m: gi for gi, (_, mods) in enumerate(GROUPS) for m in mods}
def grp(module): return MOD2G.get(module, 7)

def short(n):
    for pre in ('LowIR.ProgSim.LowerFacts.', 'LowIR.ProgSim.LayoutFacts.',
                'LowIR.ProgSim.', 'LowIR.Prog.', 'LowIR.', 'Rv64i.'):
        if n.startswith(pre):
            return n[len(pre):]
    return n

def filetag(module):
    return module.replace('LowIR.ProgSim.', '') + '.lean'

MARG = 30
minx = min(b['x'] - b['w']/2 for b in boxes.values())
maxx = max(b['x'] + b['w']/2 for b in boxes.values())
miny = min(b['y'] - b['h']/2 for b in boxes.values())
maxy = max(b['y'] + b['h']/2 for b in boxes.values())
def X(x): return x - minx + MARG
def Y(y): return y - miny + MARG
W = maxx - minx + 2*MARG
H = maxy - miny + 2*MARG

STARSET = {m['name'] for m in C['majors'] if m['star']}

# ---------- edges ----------
def path(e):
    (x0, y0), (x1, y1) = e['pts']
    y0 += boxes[e['a']]['h']/2 - 2
    y1 -= boxes[e['b']]['h']/2 - 2
    ym = (y0 + y1) / 2
    return (f"M{X(x0):.0f},{Y(y0):.0f}"
            f"C{X(x0):.0f},{Y(ym):.0f} {X(x1):.0f},{Y(ym):.0f} {X(x1):.0f},{Y(y1):.0f}")

edge_svg = []
for e in edges:
    spine = e['a'] in STARSET and e['b'] in STARSET
    cls = 'edge spine' if spine else 'edge mm'
    edge_svg.append(f'<path class="{cls}" data-a="{e["a"]}" data-b="{e["b"]}" d="{path(e)}"/>')

# ---------- major boxes ----------
DOT_PITCH = 10.0
node_svg = []
for name, b in boxes.items():
    m = majors[name]
    g = grp(m['module'])
    x0, y0 = X(b['x'] - b['w']/2), Y(b['y'] - b['h']/2)
    nid = html.escape(name, quote=True)
    star = ' star' if m['star'] else ''
    parts = [f'<g class="major g{g}{star}" data-n="{nid}">']
    parts.append(f'<rect class="mbox" x="{x0:.0f}" y="{y0:.0f}" width="{b["w"]:.0f}" height="{b["h"]:.0f}" rx="9"/>')
    tx = x0 + 12
    if m['star']:
        parts.append(f'<circle class="mnum" cx="{tx+8:.0f}" cy="{y0+15:.0f}" r="8"/>'
                     f'<text class="mnumt" x="{tx+8:.0f}" y="{y0+18.5:.0f}">{m["num"]}</text>')
        tx += 22
    parts.append(f'<text class="mtitle" x="{tx:.0f}" y="{y0+19:.0f}">{html.escape(short(name))}</text>')
    parts.append(f'<text class="msub" x="{x0+12:.0f}" y="{y0+33:.0f}">{html.escape(filetag(m["module"]))} · {m["lines"]}L</text>')
    n = len(m['bag'])
    if n:
        cols = b['cols']
        gw = cols * DOT_PITCH
        gx = x0 + (b['w'] - gw) / 2 + DOT_PITCH/2
        gy = y0 + 42 + DOT_PITCH/2
        for i, mm in enumerate(m['bag']):
            cx = gx + (i % cols) * DOT_PITCH
            cy = gy + (i // cols) * DOT_PITCH
            r = min(2.2 + 0.5 * math.sqrt(mm['lines']), 4.6)
            did = html.escape(mm['name'], quote=True)
            parts.append(f'<circle class="dot dg{grp(mm["module"])}" data-d="{did}" cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}"/>')
    if m['shared']:
        ty = y0 + b['h'] - 22
        parts.append(f'<g class="stab" data-s="{nid}">'
                     f'<rect x="{x0+7:.0f}" y="{ty:.0f}" width="{b["w"]-14:.0f}" height="18" rx="9"/>'
                     f'<text x="{X(b["x"]):.0f}" y="{ty+12.5:.0f}">+{len(m["shared"])} shared</text></g>')
    parts.append('</g>')
    node_svg.append(''.join(parts))

# ---------- JS data ----------
adj = {}
for e in edges:
    adj.setdefault(e['a'], [[], []])[0].append(e['b'])
    adj.setdefault(e['b'], [[], []])[1].append(e['a'])

star_desc = {
    'prog_sim': 'The summit — the compiled RV64I blob computes what the IL says entry(args) computes',
    'entry_run_sim': 'Whole-run assembly: stub jal → prologue → body → epilogue → halt (stepN form)',
    'runFuel_eq_stepN': 'Fuel bridge: halt-checking runFuel ≡ plain iteration, given NoHalt before K',
    'prologue_sim': 'Call entry: park params, zero frame, establish the callee StInv (W5)',
    'lower_sim_cf': 'The 1148-line monster: outcome-carrying simulator for all control flow',
    'epilogue_sim': 'Callee exit: marshal rets to a0.., restore ra/sp, jalr home (W6)',
    'lower_sim': 'Straight-line simulator: skip/arith/mem statements preserve StInv',
    'fn_hfn': 'Per-function bundle: the six-conjunct hfn fact for every compiled function',
    'lower_resolve': 'lower ↔ emitCF: symbolic layout resolves to exactly the emitted stream',
    'two_op_sim': 'The op-atom template: load slots → compute → store slot, StInv in, StInv out',
    'NoHalt_chain': 'Safety composes: k safe steps then k′ safe steps = k+k′ safe steps',
    'decode_at': 'Fetch bridge: decode(fetch32) at instruction j of any Emitted stream',
}
META = {}
for name, m in majors.items():
    META[name] = {'s': short(name), 'f': filetag(m['module']),
                  'l': m['lines'], 'bag': len(m['bag']),
                  'sh': [[short(x['name']), x['lines'], [short(c) for c in x['co']]] for x in m['shared']],
                  'd': star_desc.get(short(name), '')}
DOTMETA = {}
for m in C['majors']:
    for x in m['bag']:
        DOTMETA[x['name']] = [short(x['name']), filetag(x['module']), x['lines']]

# ---------- legend / lists ----------
gcount = {}
def bump(mod):
    gcount[grp(mod)] = gcount.get(grp(mod), 0) + 1
for m in C['majors']:
    bump(m['module'])
    for x in m['bag']:
        bump(x['module'])
for c in C['clusters']:
    for x in c['members']:
        bump(x['module'])
for x in C['toolbox']:
    bump(x['module'])

legend = ''.join(
    f'<span class="lg"><i class="sw g{i}"></i>{html.escape(gn)}<em>{gcount.get(i,0)}</em></span>'
    for i, (gn, _) in enumerate(GROUPS) if gcount.get(i))

story = sorted((m for m in C['majors'] if m['star']), key=lambda m: m['num'])
spine_list = ''.join(
    f'<li><b class="num">{m["num"]}</b><div><code>{html.escape(short(m["name"]))}</code>'
    f'<span class="fl">{html.escape(filetag(m["module"]))} · {m["lines"]} lines'
    f'{" · holds " + str(len(m["bag"])) + " private lemmas" if m["bag"] else ""}</span>'
    f'<p>{html.escape(star_desc.get(short(m["name"]), ""))}</p></div></li>'
    for m in story)

toolbox_html = ''.join(
    f'<span class="chip tb" title="{html.escape(x["name"])} — {x["lines"]} lines, used under {x["owners"]} boxes">'
    f'<i class="sw g{grp(x["module"])}"></i><code>{html.escape(short(x["name"]))}</code><em>×{x["owners"]}</em></span>'
    for x in C['toolbox'])

key_rows = sorted(C['majors'], key=lambda m: -m['lines'])
tbl = ''.join(
    f'<tr><td><code>{html.escape(short(m["name"]))}</code></td><td>{html.escape(filetag(m["module"]))}</td>'
    f'<td class="r">{m["lines"]}</td><td class="r">{len(m["bag"])}</td><td class="r">{len(m["shared"])}</td><td class="r">{m["indeg"]}</td></tr>'
    for m in key_rows)

page = f'''<title>prog_sim — proof dependency map</title>
<style>
body {{ margin: 0 }}
.viz-root {{
  --page:#f9f9f7; --surface:#fcfcfb; --card:#ffffff; --ink:#0b0b0b; --ink2:#52514e; --muted:#898781;
  --grid:#e1e0d9; --border:rgba(11,11,11,.10); --edge:#8b8a84; --halo:#fcfcfb;
  --c0:#2a78d6; --c1:#1baf7a; --c2:#008300; --c3:#4a3aa7; --c4:#eb6834;
  --c5:#e87ba4; --c6:#e34948; --c7:#eda100; --c8:#0b0b0b;
}}
@media (prefers-color-scheme: dark) {{ .viz-root {{
  --page:#0d0d0d; --surface:#1a1a19; --card:#222221; --ink:#ffffff; --ink2:#c3c2b7; --muted:#898781;
  --grid:#2c2c2a; --border:rgba(255,255,255,.10); --edge:#84837d; --halo:#1a1a19;
  --c0:#3987e5; --c1:#199e70; --c2:#008300; --c3:#9085e9; --c4:#d95926;
  --c5:#d55181; --c6:#e66767; --c7:#c98500; --c8:#ffffff;
}} }}
:root[data-theme="dark"] .viz-root {{
  --page:#0d0d0d; --surface:#1a1a19; --card:#222221; --ink:#ffffff; --ink2:#c3c2b7; --muted:#898781;
  --grid:#2c2c2a; --border:rgba(255,255,255,.10); --edge:#84837d; --halo:#1a1a19;
  --c0:#3987e5; --c1:#199e70; --c2:#008300; --c3:#9085e9; --c4:#d95926;
  --c5:#d55181; --c6:#e66767; --c7:#c98500; --c8:#ffffff;
}}
:root[data-theme="light"] .viz-root {{
  --page:#f9f9f7; --surface:#fcfcfb; --card:#ffffff; --ink:#0b0b0b; --ink2:#52514e; --muted:#898781;
  --grid:#e1e0d9; --border:rgba(11,11,11,.10); --edge:#8b8a84; --halo:#fcfcfb;
  --c0:#2a78d6; --c1:#1baf7a; --c2:#008300; --c3:#4a3aa7; --c4:#eb6834;
  --c5:#e87ba4; --c6:#e34948; --c7:#eda100; --c8:#0b0b0b;
}}
.viz-root {{ background:var(--page); color:var(--ink);
  font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif;
  padding:28px 32px 40px; min-height:100vh; box-sizing:border-box; }}
.viz-root .inner {{ max-width:1280px; margin:0 auto; }}
.viz-root header h1 {{ font-size:22px; font-weight:700; margin:0 0 4px; letter-spacing:-.01em; }}
.viz-root header p {{ margin:0; color:var(--ink2); font-size:13.5px; max-width:78em; }}
.chips {{ display:flex; gap:8px; margin:14px 0 0; flex-wrap:wrap; }}
.chip {{ background:var(--surface); border:1px solid var(--border); border-radius:8px;
  padding:6px 12px; font-size:12.5px; color:var(--ink2); }}
.chip b {{ color:var(--ink); font-weight:650; }}
.legend {{ display:flex; gap:14px; flex-wrap:wrap; margin:16px 0 6px; font-size:12.5px; color:var(--ink2); align-items:center; }}
.lg {{ display:inline-flex; align-items:center; gap:6px; }}
.lg em {{ font-style:normal; color:var(--muted); }}
.sw {{ width:10px; height:10px; border-radius:3px; display:inline-block; flex:none; }}
.sw.g0{{background:var(--c0)}} .sw.g1{{background:var(--c1)}} .sw.g2{{background:var(--c2)}}
.sw.g3{{background:var(--c3)}} .sw.g4{{background:var(--c4)}} .sw.g5{{background:var(--c5)}}
.sw.g6{{background:var(--c6)}} .sw.g7{{background:var(--c7)}} .sw.g8{{background:var(--c8)}}
.howto {{ color:var(--muted); font-size:12.5px; margin:2px 0 8px; }}
.vizwrap {{ overflow-x:auto; background:var(--surface); border:1px solid var(--border);
  border-radius:12px; margin-top:8px; }}
.vizwrap svg {{ display:block; min-width:900px; max-width:1240px; width:100%; height:auto; margin:0 auto; }}
svg .edge {{ fill:none; }}
svg .edge.mm {{ stroke:var(--edge); stroke-opacity:.5; stroke-width:1.4; }}
svg .edge.spine {{ stroke:var(--ink); stroke-opacity:.72; stroke-width:2.8; }}
svg .mbox {{ fill:var(--card); stroke-width:1.4; }}
svg .major.g0 .mbox{{stroke:var(--c0)}} svg .major.g1 .mbox{{stroke:var(--c1)}}
svg .major.g2 .mbox{{stroke:var(--c2)}} svg .major.g3 .mbox{{stroke:var(--c3)}}
svg .major.g4 .mbox{{stroke:var(--c4)}} svg .major.g5 .mbox{{stroke:var(--c5)}}
svg .major.g6 .mbox{{stroke:var(--c6)}} svg .major.g7 .mbox{{stroke:var(--c7)}}
svg .major.g8 .mbox{{stroke:var(--c8); stroke-width:2;}}
svg .major.star .mbox {{ stroke-width:2.2; }}
svg .mtitle {{ font:600 12.5px ui-monospace,Menlo,Consolas,monospace; fill:var(--ink); }}
svg .msub {{ font:10px system-ui,sans-serif; fill:var(--muted); }}
svg .mnum {{ fill:var(--ink); }}
svg .mnumt {{ font:700 10.5px system-ui,sans-serif; fill:var(--halo); text-anchor:middle; }}
svg .dot {{ stroke:var(--card); stroke-width:.8; }}
svg .dot.dg0{{fill:var(--c0)}} svg .dot.dg1{{fill:var(--c1)}} svg .dot.dg2{{fill:var(--c2)}}
svg .dot.dg3{{fill:var(--c3)}} svg .dot.dg4{{fill:var(--c4)}} svg .dot.dg5{{fill:var(--c5)}}
svg .dot.dg6{{fill:var(--c6)}} svg .dot.dg7{{fill:var(--c7)}} svg .dot.dg8{{fill:var(--c8)}}
svg .stab rect {{ fill:var(--surface); stroke:var(--muted); stroke-width:1; stroke-dasharray:4 3.5; }}
svg .stab text {{ font:10px system-ui,sans-serif; fill:var(--ink2); text-anchor:middle; }}
svg.dimmed .edge {{ stroke-opacity:.07; }}
svg.dimmed .major {{ opacity:.18; }}
svg.dimmed .edge.hi {{ stroke:var(--ink); stroke-opacity:.78; stroke-width:1.8; }}
svg.dimmed .major.hi {{ opacity:1; }}
.tip {{ position:fixed; z-index:9; pointer-events:none; background:var(--card);
  border:1px solid var(--border); border-radius:10px; padding:10px 12px; max-width:380px;
  box-shadow:0 6px 24px rgba(0,0,0,.18); display:none; font-size:12.5px; color:var(--ink2); }}
.tip code {{ color:var(--ink); font-weight:650; font-size:13px; font-family:ui-monospace,Menlo,Consolas,monospace; }}
.tip .m {{ color:var(--muted); margin:2px 0 4px; }}
.tip ul {{ margin:6px 0 0; padding-left:16px; }}
.tip li {{ margin:1px 0; }}
.tip li code {{ font-weight:500; font-size:12px; }}
.tip li em {{ font-style:normal; color:var(--muted); }}
.sect {{ font-size:15px; font-weight:700; margin:26px 0 2px; }}
.note {{ color:var(--muted); font-size:12.5px; margin:0 0 8px; }}
.toolbox {{ display:flex; flex-wrap:wrap; gap:6px; margin-top:10px; }}
.chip.tb {{ display:inline-flex; align-items:center; gap:7px; padding:4px 10px; }}
.chip.tb code {{ font-size:12px; font-family:ui-monospace,Menlo,Consolas,monospace; color:var(--ink); }}
.chip.tb em {{ font-style:normal; color:var(--muted); font-size:11px; }}
.cols {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(340px,1fr)); gap:4px 28px;
  margin:14px 0 0; padding:0; list-style:none; }}
.cols li {{ display:flex; gap:10px; padding:7px 0; border-bottom:1px solid var(--grid); }}
.cols .num {{ flex:0 0 22px; height:22px; border-radius:50%; background:var(--ink); color:var(--halo);
  font-size:11.5px; font-weight:700; display:flex; align-items:center; justify-content:center; margin-top:2px; }}
.cols code {{ font-size:13px; font-weight:650; color:var(--ink); font-family:ui-monospace,Menlo,Consolas,monospace; }}
.cols .fl {{ color:var(--muted); font-size:11.5px; margin-left:8px; }}
.cols p {{ margin:2px 0 0; color:var(--ink2); font-size:12.5px; }}
details {{ margin-top:22px; }}
details summary {{ cursor:pointer; color:var(--ink2); font-size:13px; }}
details table {{ border-collapse:collapse; margin-top:10px; font-size:12.5px; }}
details th, details td {{ text-align:left; padding:4px 14px 4px 0; border-bottom:1px solid var(--grid); }}
details th {{ color:var(--muted); font-weight:600; }}
details td.r, details th.r {{ text-align:right; font-variant-numeric:tabular-nums; }}
details code {{ font-family:ui-monospace,Menlo,Consolas,monospace; }}
</style>
<div class="viz-root"><div class="inner">
<header>
  <h1>The proof of <code>prog_sim</code> — the argument, with its support folded in</h1>
  <p>The {stats['majors']} load-bearing lemmas of the LowIR ProgSim campaign, flowing top&nbsp;→&nbsp;down from the summit
     to the leaf facts. The <b>{stats['absorbed']} private support lemmas</b> — used beneath exactly one box — are the dots
     packed <i>inside</i> that box (dot area ≈ proof length, color = source file). A box's <b>“+N shared”</b> tab counts the
     support it shares with other boxes — hover it to see the lemmas and who else uses them. The toolbox strip at the bottom
     holds the {stats['toolbox']} plumbing facts used all over.</p>
  <div class="chips">
    <span class="chip"><b>{stats['nodes']}</b> theorems total</span>
    <span class="chip"><b>{stats['majors']}</b> major</span>
    <span class="chip"><b>{stats['absorbed']}</b> folded into boxes</span>
    <span class="chip"><b>{stats['sharedLemmas']}</b> shared, in the “+N” tabs</span>
    <span class="chip"><b>{stats['toolbox']}</b> in the toolbox</span>
    <span class="chip">axiom-clean: <b>[propext, Quot.sound]</b></span>
  </div>
</header>
<div class="legend">{legend}</div>
<p class="howto">An arrow means the upper lemma (or its private support) uses the lower one; the heavy dark path is the spine.
   Hover any box, dot or “+N shared” tab for details.</p>
<div class="vizwrap"><svg id="g" viewBox="0 0 {W:.0f} {H:.0f}" xmlns="http://www.w3.org/2000/svg">
<g id="edges">{''.join(edge_svg)}</g>
<g id="nodes">{''.join(node_svg)}</g>
</svg></div>
<div class="sect">Shared toolbox</div>
<p class="note">Plumbing facts used beneath 5–14 of the boxes above (register/pc/memory one-liners, step lemmas, encode/decode bridges). Edges omitted to keep the graph readable — hover for counts.</p>
<div class="toolbox">{toolbox_html}</div>
<div class="sect">The spine, in order</div>
<ol class="cols">{spine_list}</ol>
<details><summary>Table view — the {stats['majors']} major lemmas</summary>
<table><tr><th>lemma</th><th>file</th><th class="r">proof lines</th><th class="r">private support</th><th class="r">shared support</th><th class="r">used by</th></tr>{tbl}</table>
</details>
<div class="tip" id="tip"></div>
</div></div>
<script>
const ADJ = {json.dumps(adj)};
const META = {json.dumps(META)};
const DOT = {json.dumps(DOTMETA)};
const svg = document.getElementById('g'), tip = document.getElementById('tip');
const els = {{}};
for (const el of svg.querySelectorAll('[data-n]')) (els[el.dataset.n] ??= []).push(el);
const edgeEls = [...svg.querySelectorAll('.edge')];
function unfocus() {{
  svg.classList.remove('dimmed');
  svg.querySelectorAll('.hi').forEach(e => e.classList.remove('hi'));
  tip.style.display = 'none';
}}
function focus(name) {{
  svg.classList.add('dimmed');
  const nbr = new Set([name, ...(ADJ[name]?.[0]??[]), ...(ADJ[name]?.[1]??[])]);
  for (const n of nbr) (els[n]??[]).forEach(e => e.classList.add('hi'));
  for (const e of edgeEls)
    if (e.dataset.a === name || e.dataset.b === name) e.classList.add('hi');
}}
svg.addEventListener('mouseover', ev => {{
  const box = ev.target.closest('[data-n]');
  if (!box) return;
  unfocus();
  const name = box.dataset.n, m = META[name];
  focus(name);
  const dot = ev.target.closest('.dot');
  const stab = ev.target.closest('.stab');
  if (dot) {{
    const d = DOT[dot.dataset.d];
    tip.innerHTML = `<code>${{d[0]}}</code><div class="m">${{d[1]}} · ${{d[2]}} proof line${{d[2]>1?'s':''}}</div>` +
      `private support of <code>${{m.s}}</code>`;
  }} else if (stab) {{
    const items = m.sh.slice(0, 16).map(x =>
      `<li><code>${{x[0]}}</code> <em>· ${{x[1]}}L · also under ${{x[2].join(', ')}}</em></li>`).join('');
    tip.innerHTML = `<code>${{m.sh.length}} shared support lemma${{m.sh.length>1?'s':''}}</code>` +
      `<div class="m">used by <code>${{m.s}}</code> and the boxes listed per lemma</div><ul>${{items}}</ul>` +
      (m.sh.length > 16 ? `<div class="m">… and ${{m.sh.length-16}} more</div>` : '');
  }} else {{
    tip.innerHTML = `<code>${{m.s}}</code><div class="m">${{m.f}} · ${{m.l}} proof lines</div>` +
      (m.bag ? `holds ${{m.bag}} private support lemma${{m.bag>1?'s':''}}` : 'no private support — leans on shared facts') +
      (m.sh.length ? ` · shares ${{m.sh.length}}` : '') +
      (m.d ? `<div style="margin-top:6px">${{m.d}}</div>` : '');
  }}
  tip.style.display = 'block';
}});
svg.addEventListener('mousemove', ev => {{
  const pad = 14;
  let x = ev.clientX + pad, y = ev.clientY + pad;
  const r = tip.getBoundingClientRect();
  if (x + r.width > innerWidth - 8) x = ev.clientX - r.width - pad;
  if (y + r.height > innerHeight - 8) y = ev.clientY - r.height - pad;
  tip.style.left = x + 'px'; tip.style.top = y + 'px';
}});
svg.addEventListener('mouseout', ev => {{ if (ev.target.closest('[data-n]')) unfocus(); }});
</script>
'''
open('progsim-map.html', 'w').write(page)
print(f'wrote progsim-map.html  svg {W:.0f}x{H:.0f}')
