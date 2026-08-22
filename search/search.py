"""Multistart + basin-hopping driver for Heilbronn variants.

Usage: search.py VARIANT N SECONDS [SEED]
Writes best result to results/VARIANT/nN.json (only if better than existing).
"""

import json
import os
import sys
import time
import numpy as np

from heil import polish, random_config, value, save_result, load_result, canonical

TARGETS = {  # published record values (Friedman pages, truncated => lower bounds)
    "square": {3: .5, 4: .5, 5: 3**.5/9, 6: .125, 7: .08385900858851,
               8: (13**.5 - 1)/36, 9: (9*(65**.5) - 55)/320, 10: .04653741889298,
               11: 1/27, 12: .03259885877426, 13: .02701927223911,
               14: .02430398066856, 15: .02110568045738, 16: 7/341},
    # triangle full-precision values from MathWorld (Cantrell pers. comm. 2007),
    # n=11 AlphaEvolve 2025, n=13 Karpov 2015
    "triangle": {3: 1, 4: 1/3, 5: .171572, 6: .125, 7: 7/72,
                 8: .06778914101959856, 9: 43/784, 10: .04337673349889024,
                 11: .036529889880030156, 12: .03100478174352528,
                 13: .0265013422223496, 14: .02377577301721215,
                 15: .02109025290939601, 16: .01797627598723551},
    # convex n=8,9,10,15,16 known only to 4 truncated digits (.0800+ etc.), so the
    # target is the truncation UPPER bound: exceeding it guarantees a genuine record.
    "convex": {3: 1, 4: .5, 5: .2763932022500210, 6: 1/6, 7: 1/9, 8: .0801,
               9: .0641, 10: .0520, 11: 2/47, 12: 2/51,
               13: .03093688903489563, 14: .02783557145848214,  # AlphaEvolve 2025
               15: .0245, 16: .0223},
}


def perturb(X, rng, scale, variant):
    Xn = X + rng.normal(0, scale, X.shape)
    if variant == "square":
        Xn = np.clip(Xn, 0, 1)
    elif variant == "triangle":
        Xn = np.clip(Xn, 0, None)
        s = Xn.sum(axis=1)
        bad = s > 1
        Xn[bad] /= s[bad, None]
    return Xn


def run(variant, n, seconds, seed=0, verbose=True):
    rng = np.random.default_rng(seed)
    path = f"results/{variant}/n{n}.json"
    best_val, best_X = -1.0, None
    if os.path.exists(path):
        rec = load_result(path)
        best_val = rec["value"]
        best_X = np.array(rec["points"])

    t_end = time.time() + seconds
    n_starts = 0
    while time.time() < t_end:
        n_starts += 1
        bb = rng.choice([0.0, 0.3, 0.6])
        X = random_config(n, variant, rng, boundary_bias=bb)
        try:
            X, v = polish(X, variant)
        except Exception:
            continue
        # basin hop around this local optimum a few times
        hops = 0
        while hops < 6 and time.time() < t_end:
            hops += 1
            sc = rng.choice([0.005, 0.02, 0.06])
            Xp = perturb(X, rng, sc, variant)
            try:
                Xp, vp = polish(Xp, variant)
            except Exception:
                continue
            if vp > v:
                X, v = Xp, vp
                hops = 0
        if v > best_val + 1e-12:
            best_val, best_X = v, X.copy()
            save_result(path, variant, n, best_X, best_val,
                        meta={"seed": seed, "starts": n_starts})
            if verbose:
                tgt = TARGETS.get(variant, {}).get(n)
                mark = ""
                if tgt:
                    mark = f"  (target {tgt:.6f}, {'ABOVE' if best_val > tgt + 1e-9 else 'below'})"
                print(f"[{variant} n={n}] new best {best_val:.9f} after {n_starts} starts{mark}",
                      flush=True)
    if best_X is not None:
        save_result(path, variant, n, best_X, best_val,
                    meta={"seed": seed, "starts": n_starts})
    return best_val


if __name__ == "__main__":
    variant, n, seconds = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else int.from_bytes(os.urandom(4), "little")
    v = run(variant, n, seconds, seed)
    tgt = TARGETS.get(variant, {}).get(n)
    print(f"FINAL {variant} n={n}: {v:.10f}" + (f"  target {tgt:.10f}" if tgt else ""))
