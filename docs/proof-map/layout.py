#!/usr/bin/env python3
"""Narrow vertical Sugiyama layout for the contracted graph -> layout.json.

Majors only. Ranks from grandalf; ranks wider than MAXW wrap into stacked
sub-rows (safe: layered DAGs have no same-rank edges, so sub-rows keep every
edge flowing strictly downward).
"""
import json, math
from collections import defaultdict
from grandalf.graphs import Vertex, Edge, Graph
from grandalf.layouts import SugiyamaLayout

MAXW = 1210          # target drawable width for the graph body
XGAP = 20            # min horizontal gap between boxes
SUBROW_GAP = 26      # vertical gap between wrapped sub-rows
LAYER_GAP = 64       # vertical gap between ranks

C = json.load(open('contracted.json'))

def short(n):
    for pre in ('LowIR.ProgSim.LowerFacts.', 'LowIR.ProgSim.LayoutFacts.',
                'LowIR.ProgSim.', 'LowIR.Prog.', 'LowIR.', 'Rv64i.'):
        if n.startswith(pre):
            return n[len(pre):]
    return n

# ---- box geometry ----
DOT_PITCH = 10.0
def bag_grid(n):
    if n == 0:
        return 0, 0
    cols = max(4, math.ceil(math.sqrt(n * 2.6)))
    rows = math.ceil(n / cols)
    return cols, rows

SEP_H = 14           # divider zone between private and shared dot grids

boxes = {}
for m in C['majors']:
    name = m['name']
    t = short(name)
    title_w = len(t) * 7.6 + (26 if m['star'] else 0)
    cols, rows = bag_grid(len(m['bag']))
    grid_w = cols * DOT_PITCH
    grid_h = rows * DOT_PITCH
    nsh = len(m['shared'])
    scols, srows = bag_grid(nsh)
    sgrid_w = scols * DOT_PITCH
    sgrid_h = srows * DOT_PITCH
    w = max(title_w, 7 * 5.6 + 60, grid_w, sgrid_w) + 24
    h = (44 + (grid_h + 8 if rows else 0)
         + (SEP_H + sgrid_h + 8 if nsh else 0))
    boxes[name] = {'w': w, 'h': h, 'cols': cols, 'rows': rows,
                   'scols': scols, 'srows': srows}

# ---- grandalf for ranks + initial order ----
class VView:
    def __init__(self, w, h):
        self.w, self.h = w, h
        self.xy = (0, 0)

V = {}
for name, b in boxes.items():
    v = Vertex(name)
    v.view = VView(b['w'] + XGAP, b['h'])
    V[name] = v
E = [Edge(V[e['a']], V[e['b']]) for e in C['edges']]
g = Graph(list(V.values()), E)
sug = SugiyamaLayout(g.C[0])
sug.xspace = XGAP
sug.yspace = LAYER_GAP
sug.init_all(roots=[V['LowIR.ProgSim.prog_sim']], optimize=True)
sug.draw(14)

# ranks from y, order from x
byrank = defaultdict(list)
for name, v in V.items():
    byrank[round(v.view.xy[1])].append(name)
ranks = [sorted(byrank[y], key=lambda n: V[n].view.xy[0]) for y in sorted(byrank)]

# ---- wrap wide ranks into sub-rows, assign final coords ----
succ = defaultdict(list); pred = defaultdict(list)
for e in C['edges']:
    succ[e['a']].append(e['b']); pred[e['b']].append(e['a'])

pos = {}          # name -> (x, y) center
ycur = 0.0
for rank in ranks:
    # split into sub-rows not exceeding MAXW
    rows_, cur, curw = [], [], 0.0
    for n in rank:
        w = boxes[n]['w'] + XGAP
        if cur and curw + w > MAXW:
            rows_.append(cur); cur, curw = [], 0.0
        cur.append(n); curw += w
    rows_.append(cur)
    for row in rows_:
        rowh = max(boxes[n]['h'] for n in row)
        total = sum(boxes[n]['w'] for n in row) + XGAP * (len(row) - 1)
        # center the row near the mean x of the members' already-placed parents
        px = [pos[p][0] for n in row for p in pred[n] if p in pos]
        cx = sum(px) / len(px) if px else 0.0
        cx = max(-MAXW/2 + total/2, min(MAXW/2 - total/2, cx))
        x = cx - total / 2
        for n in row:
            pos[n] = (x + boxes[n]['w'] / 2, ycur + rowh / 2)
            x += boxes[n]['w'] + XGAP
        ycur += rowh + SUBROW_GAP
    ycur += LAYER_GAP - SUBROW_GAP

out_nodes = {}
for name, b in boxes.items():
    out_nodes[name] = dict(b, x=pos[name][0], y=pos[name][1])

out_edges = [dict(e, pts=[list(pos[e['a']]), list(pos[e['b']])]) for e in C['edges']]

json.dump({'boxes': out_nodes, 'edges': out_edges}, open('layout.json', 'w'))
xs = [(b['x'] - b['w']/2, b['x'] + b['w']/2) for b in out_nodes.values()]
ys = [(b['y'] - b['h']/2, b['y'] + b['h']/2) for b in out_nodes.values()]
print(f"extent x {min(a for a,_ in xs):.0f}..{max(b for _,b in xs):.0f}  "
      f"y {min(a for a,_ in ys):.0f}..{max(b for _,b in ys):.0f}  ranks={len(ranks)}")
