"""Symbolic/trivial configurations emitted as 30-decimal literals.

Only configurations whose exact description is beyond doubt live here:
the trivial small-n cases and the regular polygons for the convex variant.
Everything else that lacks published coordinates goes through the
reconstruction pipeline instead.
"""

import mpmath

mpmath.mp.dps = 40


def _fmt(x):
    # 30-decimal fixed point, truncated toward zero (the convex value is
    # scale/position invariant, so truncation is harmless).
    f = mpmath.mpf(x)
    scaled = int(mpmath.floor(abs(f) * mpmath.mpf(10) ** 30))
    sign = "-" if f < 0 and scaled != 0 else ""
    return f"{sign}{scaled // 10**30}.{scaled % 10**30:030d}"


def regular_polygon(m):
    pts = []
    for j in range(m):
        th = 2 * mpmath.pi * j / m + mpmath.pi / 2
        pts.append([_fmt(mpmath.cos(th)), _fmt(mpmath.sin(th))])
    return pts


CONSTRUCTIONS = {
    ("triangle", 3): {
        "points": [["0", "0"], ["1", "0"], ["0", "1"]],
        "note": "the container's vertices",
    },
    ("triangle", 4): {
        "points": [["0", "0"], ["1", "0"], ["0", "1"],
                   ["0.333333333333333333333333333333",
                    "0.333333333333333333333333333333"]],
        "note": "vertices plus centroid; one of an infinite family",
    },
    ("convex", 3): {"points": regular_polygon(3), "note": "any triangle"},
    ("convex", 4): {"points": regular_polygon(4), "note": "square (any parallelogram)"},
    ("convex", 5): {"points": regular_polygon(5), "note": "regular pentagon"},
    ("convex", 6): {"points": regular_polygon(6), "note": "regular hexagon"},
}


def get(variant, n):
    c = CONSTRUCTIONS.get((variant, n))
    if c is None:
        return None
    return {"points": c["points"], "note": c["note"],
            "ref": "data/sources/exact/constructions.py"}
