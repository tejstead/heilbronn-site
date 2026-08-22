"""Seed n+1 configurations by point insertion into the best n-point config,
and n-1 by deletion. Also cross-seed square<->triangle<->convex via affine maps.

Usage: grow.py VARIANT N   (seeds results/VARIANT/nN.json from neighbors)
"""

import itertools
import os
import sys
import numpy as np

from heil import value, save_result, load_result, random_config, project

if os.environ.get("FAST_POLISH", "1") == "1":
    from fastheil import polish_fast as polish
else:
    from heil import polish


def insert_candidates(X, variant, rng, tries=200):
    """Candidate positions for a new point: grid + random, keep top by min area."""
    n1 = len(X) + 1
    cands = random_config(tries, variant, rng, boundary_bias=0.4)
    best = []
    for c in cands:
        Y = np.vstack([X, c])
        best.append((value(Y, variant), c))
    best.sort(key=lambda t: -t[0])
    return [c for _, c in best[:12]]


def grow(variant, n, seconds=120):
    import time
    rng = np.random.default_rng(int.from_bytes(os.urandom(4), "little"))
    path = f"results/{variant}/n{n}.json"
    best = load_result(path)["value"] if os.path.exists(path) else -1
    bestX = None

    seeds = []
    below = f"results/{variant}/n{n-1}.json"
    if os.path.exists(below):
        Xb = np.array(load_result(below)["points"])
        for c in insert_candidates(Xb, variant, rng):
            seeds.append(np.vstack([Xb, c]))
    above = f"results/{variant}/n{n+1}.json"
    if os.path.exists(above):
        Xa = np.array(load_result(above)["points"])
        for i in range(len(Xa)):
            seeds.append(np.delete(Xa, i, axis=0))

    t_end = time.time() + seconds
    for S in seeds:
        if time.time() > t_end:
            break
        try:
            X1, v1 = polish(S, variant)
            # a few basin hops around each seed
            for _ in range(4):
                Xp = X1 + rng.normal(0, 0.01, X1.shape)
                Xp = project(Xp, variant) if variant != "convex" else Xp
                X2, v2 = polish(Xp, variant)
                if v2 > v1:
                    X1, v1 = X2, v2
        except Exception:
            continue
        if v1 > best + 1e-12:
            best, bestX = v1, X1
            save_result(path, variant, n, X1, v1, meta={"seed": "grow"})
            print(f"  {variant} n={n}: grew to {best:.10f}", flush=True)
    return best


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    if len(sys.argv) > 2:
        print(grow(sys.argv[1], int(sys.argv[2])))
    else:
        # sweep: everything 13..20, all variants, up-then-down passes
        for sweep in range(3):
            for variant in ("square", "triangle", "convex"):
                for n in list(range(13, 21)) + list(range(20, 12, -1)):
                    grow(variant, n, seconds=45)
        print("grow sweep done")
