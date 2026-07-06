# proof-map — the `prog_sim` dependency map

An interactive, self-contained HTML visualization of every theorem beneath the
`prog_sim` summit (`lean/LowIR/ProgSim/Main.lean`), the machine-checked statement
that the compiled RV64I blob computes what the D7/D8 IL says `entry(args)`
computes (see [RESUME-PROGSIM.md](../RESUME-PROGSIM.md)).

**Open [progsim-map.html](progsim-map.html) in a browser.** Light/dark themed,
hover any box, dot or toolbox chip for details including the full theorem
statement. No network access needed.

## How to read it

The 328 reachable project theorems are folded into a 26-node graph so the
argument reads top → down at a glance:

- **Boxes** are the 26 load-bearing lemmas; the numbered ones are the spine
  (`prog_sim → entry_run_sim → prologue/lower_sim_cf/epilogue → lower_sim →
  op atoms → NoHalt/decode_at`). An arrow means the upper lemma — or its
  private support — uses the lower one (transitively reduced).
- **Dots inside a box** are its 186 *private* support lemmas: a minor lemma is
  absorbed by a major iff it is reachable from that major without passing
  through any other major. Dot area ≈ proof length, color = source file.
- **Dots below a box's dashed “shared” divider** are support lemmas reachable
  from 2–4 boxes; they appear in every owning box (hover names the co-owners).
- **The toolbox strip** holds the 37 plumbing facts used beneath 5–14 boxes
  (`pc_setPc`, `mem_rset`, `Emitted_append_*`, `stepN_add`, …); their edges are
  omitted by design.

## Regenerating

The pipeline is deterministic; each step reads/writes files in this directory.

```sh
# 1. extract the raw dependency graph from the compiled Lean environment
cd lean && DEPGRAPH_OUT=../docs/proof-map/depgraph.json \
  lake env lean ../docs/proof-map/DepGraph.lean         # -> depgraph.json

# 2. contract around the major lemmas, lay out, render
cd ../docs/proof-map
python3 contract.py                                     # -> contracted.json
uv run --with grandalf layout.py                        # -> layout.json
python3 render.py                                       # -> progsim-map.html
```

| File | Role |
|---|---|
| [DepGraph.lean](DepGraph.lean) | `CoreM` meta-program: walks proof terms from `prog_sim`, inlines `_proof_`/matcher auxiliaries, emits the theorem-level graph (328 nodes / 821 edges) with each theorem's pretty-printed statement. |
| [contract.py](contract.py) | Ownership partition (major / absorbed / shared / toolbox) + contracted, transitively-reduced edge set. The major-lemma list is curated at the top of this file. |
| [layout.py](layout.py) | Narrow vertical Sugiyama layout (grandalf ranks + width-capped row wrapping). |
| [render.py](render.py) | Emits the final self-contained HTML/SVG page. |
| depgraph.json | Snapshot of the extracted graph (commit `2a473d0` state). |
| [progsim-map.html](progsim-map.html) | The rendered map. |

`contracted.json`/`layout.json` are intermediates and not checked in.
