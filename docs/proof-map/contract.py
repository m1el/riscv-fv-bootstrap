#!/usr/bin/env python3
"""Contract depgraph.json around major lemmas -> contracted.json

Majors: big boxes. Minors owned by exactly one major: absorbed into its bag.
Minors owned by 2+ majors: grouped per owner-set into shared cluster nodes,
except ubiquitous ones (>= TOOLBOX_MIN owners) which go to the toolbox strip.
"""
import json
from collections import defaultdict, Counter

TOOLBOX_MIN = 5

d = json.load(open('depgraph.json'))
nodes = {n['name']: n for n in d['nodes']}
succ = defaultdict(set)
for a, b in d['edges']:
    succ[a].add(b)
indeg = Counter(b for a, b in d['edges'])

P = 'LowIR.ProgSim.'
STORY = [P+x for x in ['prog_sim', 'entry_run_sim', 'runFuel_eq_stepN', 'prologue_sim',
                       'lower_sim_cf', 'epilogue_sim', 'lower_sim', 'LayoutFacts.fn_hfn',
                       'LowerFacts.lower_resolve', 'two_op_sim', 'NoHalt_chain', 'decode_at']]
MAJORS = STORY + [P+x for x in [
    'single_op_sim', 'run_slotStore', 'run_parkParams', 'run_zeroFrame',
    'run_retStoresFrom', 'run_zeroSlots', 'run_cref', 'run_synth',
    'run_marshalFrom', 'StInv_store_slot', 'StInv_scratch',
    'LowerFacts.lower_totalSymSize', 'LayoutFacts.lower_labels_nodup',
    'LowerFacts.resolve_flatten_append']]
MAJORS = [m for m in MAJORS if m in nodes]
MSET = set(MAJORS)

# ownership: minor m owned by major j iff m reachable from j through minors only
own = defaultdict(set)
reach_minors = {}   # major -> set of minors reachable through minors
for j in MAJORS:
    seen = set()
    stack = list(succ[j])
    while stack:
        n = stack.pop()
        if n in seen or n in MSET:
            continue
        seen.add(n)
        stack += list(succ[n])
    reach_minors[j] = seen
    for m in seen:
        own[m].add(j)

minors = [n for n in nodes if n not in MSET]
absorbed = {m: next(iter(own[m])) for m in minors if len(own[m]) == 1}
toolbox = [m for m in minors if len(own[m]) >= TOOLBOX_MIN]
shared = {m: tuple(sorted(own[m])) for m in minors
          if 2 <= len(own[m]) < TOOLBOX_MIN}

clusters = defaultdict(list)   # owner-set -> [minor]
for m, s in shared.items():
    clusters[s].append(m)
cluster_id = {s: f'C{i}' for i, s in enumerate(sorted(clusters, key=lambda s: (-len(clusters[s]), s)))}

# ---- contracted edges ----
# major -> major: k in succ(j) or succ(m) for m in reach_minors[j]
mm = set()
for j in MAJORS:
    hits = set()
    for src in [j] + list(reach_minors[j]):
        hits |= succ[src] & MSET
    hits.discard(j)
    for k in hits:
        mm.add((j, k))
# major -> cluster: every owner
mc = set()
for s, cid in cluster_id.items():
    for j in s:
        mc.add((j, cid))
# cluster -> major: member minor (or minor reachable from it staying minor... members'
# own succ only — deeper minors already carry ownership) uses major k directly
cm = set()
for s, cid in cluster_id.items():
    for m in clusters[s]:
        for k in succ[m] & MSET:
            cm.add((cid, k))

# ---- transitive reduction over the contracted DAG ----
allnodes = list(MAJORS)
E = list(mm)
sc = defaultdict(set)
for a, b in E:
    sc[a].add(b)
reach = {}
def rset(n, stack=()):
    if n in reach:
        return reach[n]
    r = set()
    for s2 in sc[n]:
        r.add(s2)
        r |= rset(s2)
    reach[n] = r
    return r
for n in allnodes:
    rset(n)
Ered = sorted((a, b) for a, b in E
               if not any(b in reach[s2] for s2 in sc[a] if s2 != b))

def info(m):
    l0, l1 = nodes[m]['lines']
    return {'name': m, 'module': nodes[m]['module'],
            'lines': max(1, l1 - l0 + 1), 'indeg': indeg[m]}

shared_of = defaultdict(list)   # major -> [(info, co-owners)]
for m, s2 in shared.items():
    for j in s2:
        shared_of[j].append(dict(info(m), co=[x for x in s2 if x != j]))
for j in shared_of:
    shared_of[j].sort(key=lambda x: -x['lines'])

out = {
    'majors': [dict(info(j),
                    bag=sorted((info(m) for m, o in absorbed.items() if o == j),
                               key=lambda x: -x['lines']),
                    shared=shared_of.get(j, []),
                    star=(j in STORY), num=(STORY.index(j) + 1 if j in STORY else 0))
               for j in MAJORS],
    'clusters': [{'id': cid, 'owners': list(s),
                  'members': sorted((info(m) for m in clusters[s]), key=lambda x: -x['lines'])}
                 for s, cid in cluster_id.items()],
    'toolbox': sorted((dict(info(m), owners=len(own[m])) for m in toolbox),
                      key=lambda x: -x['owners']),
    'edges': [{'a': a, 'b': b, 'kind': 'mm'} for a, b in Ered],
    'stats': {'nodes': len(nodes), 'deps': len(d['edges']),
              'majors': len(MAJORS), 'absorbed': len(absorbed),
              'sharedClusters': len(clusters), 'sharedLemmas': len(shared),
              'toolbox': len(toolbox)},
}
json.dump(out, open('contracted.json', 'w'))
print(f"majors={len(MAJORS)} absorbed={len(absorbed)} clusters={len(clusters)} "
      f"(covering {len(shared)}) toolbox={len(toolbox)}")
print(f"edges: mm={len(mm)} mc={len(mc)} cm={len(cm)} -> tred {len(Ered)}")
