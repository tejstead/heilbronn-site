"""Friedman-style renderer: filled minimal triangles, non-overlapping per image.

For a saved configuration, finds every triangle attaining the minimum area (within
rtol), partitions them into groups whose members are pairwise interior-disjoint
(greedy coloring of the overlap graph), and renders one PNG per group in the style
of Erich Friedman's packing pages: white background, thin black domain outline,
black point dots, solid-colored triangles.

Usage:
  render.py results/VARIANT/nN.json         -> renders all groups
  render.py all                             -> everything in results/
"""

import glob
import itertools
import json
import os
import sys
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon as MplPolygon
from shapely.geometry import Polygon as ShPolygon

from heil import crosses, triples, hull_cycle

# Friedman's exact GIF palette (sampled from his images)
COLORS = ["#ff0000", "#0000ff", "#00ff00", "#ffff00", "#ff7f00",
          "#00ffff", "#7f007f", "#7f7f7f", "#7f7fff", "#ff00ff"]

RTOL = 1e-7          # triangles within (1+RTOL)*min count as minimal
OVERLAP_EPS = 1e-12  # interiors overlap if intersection area exceeds this


def minimal_triangles(X):
    T = triples(len(X))
    c = np.abs(crosses(X, T))
    mn = c.min()
    return [tuple(t) for t in T[c <= mn * (1 + RTOL)]]


def overlap_groups(X, tris):
    """Greedy-color the interior-overlap graph; returns list of groups."""
    polys = [ShPolygon(X[list(t)]) for t in tris]
    m = len(tris)
    adj = [set() for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            inter = polys[i].intersection(polys[j])
            if inter.area > OVERLAP_EPS:
                adj[i].add(j)
                adj[j].add(i)
    order = sorted(range(m), key=lambda i: -len(adj[i]))  # largest degree first
    color = {}
    for i in order:
        used = {color[j] for j in adj[i] if j in color}
        k = 0
        while k in used:
            k += 1
        color[i] = k
    ngroups = max(color.values()) + 1 if color else 0
    groups = [[] for _ in range(ngroups)]
    for i, k in color.items():
        groups[k].append(tris[i])
    return groups


# display map: reference triangle (0,0),(1,0),(0,1) -> equilateral (Friedman style)
_EQ = np.array([[1.0, 0.5], [0.0, np.sqrt(3) / 2]]).T  # columns: images of e1, e2


def display_coords(X, variant):
    return X @ _EQ if variant == "triangle" else X


def domain_outline(X, variant):
    if variant == "square":
        return np.array([[0, 0], [1, 0], [1, 1], [0, 1], [0, 0]], float)
    if variant == "triangle":
        return np.array([[0, 0], [1, 0], [0, 1], [0, 0]], float) @ _EQ
    cyc = hull_cycle(X)
    return X[np.append(cyc, cyc[0])]


def render_group(X, variant, group, out_png, title=None, px=235):
    """Friedman style: ~235px wide, white bg, thin black outline, flat colored
    triangles with thin black edges, small black dots, no title/axes/margins."""
    outline = domain_outline(X, variant)
    Xd = display_coords(X, variant)
    w = outline[:, 0].max() - outline[:, 0].min()
    h = outline[:, 1].max() - outline[:, 1].min()
    pad = 0.025 * max(w, h)
    figw = px / 100.0
    fig = plt.figure(figsize=(figw, figw * (h + 2 * pad) / (w + 2 * pad)), dpi=100)
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_aspect("equal")
    ax.plot(outline[:, 0], outline[:, 1], "k-", lw=1.0, zorder=1,
            solid_joinstyle="miter")
    for idx, t in enumerate(sorted(group)):
        tri = Xd[list(t)]
        ax.add_patch(MplPolygon(tri, closed=True,
                                facecolor=COLORS[idx % len(COLORS)],
                                edgecolor="black", lw=0.7, zorder=2,
                                joinstyle="miter"))
    ax.plot(Xd[:, 0], Xd[:, 1], "o", color="black", ms=3.6, zorder=3)
    ax.set_axis_off()
    ax.set_xlim(outline[:, 0].min() - pad, outline[:, 0].max() + pad)
    ax.set_ylim(outline[:, 1].min() - pad, outline[:, 1].max() + pad)
    fig.savefig(out_png, dpi=100, facecolor="white")
    plt.close(fig)


def render_config(path, outdir="render"):
    rec = json.load(open(path))
    variant, n = rec["variant"], rec["n"]
    X = np.array(rec["points"])
    tris = minimal_triangles(X)
    groups = overlap_groups(X, tris)
    os.makedirs(outdir, exist_ok=True)
    suffixes = "abcdefghij"
    outs = []
    for gi, g in enumerate(groups):
        sfx = suffixes[gi] if len(groups) > 1 else ""
        out = f"{outdir}/{variant}_n{n}{sfx}.png"
        render_group(X, variant, g, out,
                     title=f"{variant} n={n}   A = {rec['value']:.9f}   "
                           f"({len(g)} of {len(tris)} minimal triangles)")
        outs.append(out)
    print(f"{variant} n={n}: {len(tris)} minimal triangles -> "
          f"{len(groups)} image(s): {', '.join(os.path.basename(o) for o in outs)}")
    return outs


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    arg = sys.argv[1] if len(sys.argv) > 1 else "all"
    paths = sorted(glob.glob("results/*/n*.json")) if arg == "all" else [arg]
    for p in paths:
        render_config(p)
