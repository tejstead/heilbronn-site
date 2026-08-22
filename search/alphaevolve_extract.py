"""Extract AlphaEvolve's Heilbronn coordinates from their results notebook,
save as text files, and render Friedman-style images (credited).

Source: github.com/google-deepmind/alphaevolve_results, mathematical_results.ipynb
(sections B.9 triangle n=11, B.10 convex n=13 and n=14). Published June 2025
with the AlphaEvolve white paper (arXiv:2506.13131, submitted 16 June 2025).

The triangle n=11 coordinates are in DeepMind's equilateral frame
((0,0),(1,0),(1/2,sqrt3/2)); we render in that frame directly. Convex
coordinates are used as-is.
"""

import json
import os
import numpy as np

from heil import value
from render import minimal_triangles, overlap_groups, render_group

os.chdir(os.path.dirname(os.path.abspath(__file__)))

nb = json.load(open("alphaevolve.ipynb"))
src = {i: "".join(c["source"]) for i, c in enumerate(nb["cells"])}

def parse_array(cell_text, name):
    s = cell_text.split(name + " = np.array(")[1]
    depth, end = 0, 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            if depth == 0:
                end = i
                break
            depth -= 1
    return np.array(eval(s[:end]))

t11 = parse_array(src[100], "found_points")
c13 = parse_array(src[106], "construction_1")
c14 = parse_array(src[109], "construction_2")

os.makedirs("alphaevolve", exist_ok=True)

CREDIT = ("# Found by AlphaEvolve (Google DeepMind), published June 2025.\n"
          "# Source: arXiv:2506.13131; coordinates from mathematical_results.ipynb\n"
          "# at github.com/google-deepmind/alphaevolve_results\n")

def save_txt(fname, header, pts):
    with open(f"alphaevolve/{fname}", "w") as f:
        f.write(header + CREDIT)
        for x, y in pts:
            f.write(f"{x:.16f}\t{y:.16f}\n")

save_txt("triangle_n11.txt",
         "# Heilbronn triangle n=11, value 0.0365298898800302\n"
         "# frame: equilateral triangle (0,0),(1,0),(1/2,sqrt(3)/2)\n", t11)
save_txt("convex_n13.txt",
         "# Heilbronn convex n=13, value 0.0309368890 (min area / hull area)\n", c13)
save_txt("convex_n14.txt",
         "# Heilbronn convex n=14, value 0.0278355715 (min area / hull area)\n", c14)

# ---- render. triangle n=11: map equilateral -> reference frame for the
# geometry code, then render (render.py maps back to equilateral for display).
V = np.array([[0.0, 0.0], [1.0, 0.0], [0.5, np.sqrt(3) / 2]])
W = np.array([[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
M = np.linalg.lstsq(np.hstack([V, np.ones((3, 1))]), W, rcond=None)[0]
t11_ref = np.hstack([t11, np.ones((len(t11), 1))]) @ M
t11_ref = np.clip(t11_ref, 0, None)
s = t11_ref.sum(axis=1)
t11_ref[s > 1] /= s[s > 1, None]

for tag, X, variant in (("triangle_n11", t11_ref, "triangle"),
                        ("convex_n13", c13, "convex"),
                        ("convex_n14", c14, "convex")):
    print(f"{tag}: value {value(X, variant):.12f}")
    tris = minimal_triangles(X)
    groups = overlap_groups(X, tris)
    sfx = "abcdefghij"
    for gi, g in enumerate(groups):
        out = f"alphaevolve/{tag}{sfx[gi] if len(groups) > 1 else ''}.png"
        render_group(X, variant, g, out)
    print(f"  {len(tris)} minimal triangles -> {len(groups)} image(s)")
print("ALPHAEVOLVE EXTRACT DONE")
