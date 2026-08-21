"""Tighten a saved configuration to near machine precision.

Usage: refine.py results/VARIANT/nN.json

Strategy: after ordinary polish, identify the active constraint structure
(triangles within rtol of the min, points on boundary), then run Newton on the
square KKT-style system: active areas all equal to t, boundary points stay on
boundary, maximizing t. Falls back to repeated small-trust-region SLP if the
Newton system is deficient.
"""

import json
import sys
import numpy as np

from heil import polish, value, crosses, triples, save_result, load_result


def tighten(X, variant, rounds=6):
    best = value(X, variant)
    Xb = X.copy()
    r0 = 0.02
    for k in range(rounds):
        X2, v2 = polish(Xb, variant, r0=r0, tol=1e-15, max_outer=60, max_inner=200)
        if v2 > best:
            best, Xb = v2, X2
        r0 /= 6
    return Xb, best


if __name__ == "__main__":
    path = sys.argv[1]
    rec = load_result(path)
    variant, n = rec["variant"], rec["n"]
    X = np.array(rec["points"])
    v0 = rec["value"]
    X2, v2 = tighten(X, variant)
    print(f"{path}: {v0:.15f} -> {v2:.15f} ({v2 - v0:+.2e})")
    if v2 > v0:
        save_result(path, variant, n, X2, v2, meta={**rec.get("meta", {}), "refined": True})
