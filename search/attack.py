"""Parallel record attack: seeded basin-hopping + fresh multistart, multiprocessing.

Usage: attack.py VARIANT N SECONDS [WORKERS]
Each worker runs an independent stream; the parent merges results into results/.
"""

import multiprocessing as mp
import os
import sys
import time
import numpy as np

from heil import random_config, value, save_result, load_result, project

if os.environ.get("FAST_POLISH", "1") == "1":
    from fastheil import polish_fast as polish
else:
    from heil import polish

os.chdir(os.path.dirname(os.path.abspath(__file__)))


def mutate(X, rng, variant):
    """One of several move types, returns a new (unpolished) config."""
    X = X.copy()
    n = len(X)
    r = rng.random()
    if r < 0.35:                       # gaussian shake, varied scale
        sc = 10 ** rng.uniform(-3.3, -0.9)
        X += rng.normal(0, sc, X.shape)
    elif r < 0.6:                      # shake a random subset only
        k = rng.integers(1, max(2, n // 3))
        idx = rng.choice(n, size=k, replace=False)
        sc = 10 ** rng.uniform(-2.5, -0.7)
        X[idx] += rng.normal(0, sc, (k, 2))
    elif r < 0.85:                     # teleport one point (topology escape)
        i = rng.integers(n)
        X[i] = random_config(1, variant, rng, boundary_bias=0.5)[0]
    else:                              # swap-ish: teleport 2 points
        idx = rng.choice(n, size=2, replace=False)
        X[idx] = random_config(2, variant, rng, boundary_bias=0.5)
    return project(X, variant) if variant != "convex" else X


def worker(variant, n, seconds, seed, best_val0, best_X0, q):
    rng = np.random.default_rng(seed)
    best_val = best_val0
    best_X = None if best_X0 is None else np.array(best_X0)
    cur_X, cur_val = (best_X.copy(), best_val) if best_X is not None else (None, -1)
    t_end = time.time() + seconds
    fails = 0
    while time.time() < t_end:
        # occasionally restart fresh to explore new topologies
        if cur_X is None or rng.random() < 0.06 or fails > 60:
            X0 = random_config(n, variant, rng, boundary_bias=rng.choice([0.0, 0.3, 0.6]))
            fails = 0
        else:
            X0 = mutate(cur_X, rng, variant)
        try:
            X1, v1 = polish(X0, variant)
        except Exception:
            continue
        if v1 > cur_val + 1e-13:
            cur_X, cur_val = X1, v1
            fails = 0
            if v1 > best_val + 1e-13:
                best_val, best_X = v1, X1.copy()
                q.put((seed, best_val, best_X.tolist(), False))
        else:
            fails += 1
            # occasional downhill acceptance to keep moving
            if rng.random() < 0.02 and v1 > 0.9 * cur_val:
                cur_X, cur_val = X1, v1
    q.put((seed, best_val, None if best_X is None else best_X.tolist(), True))


def main(variant, n, seconds, workers):
    path = f"results/{variant}/n{n}.json"
    best_val, best_X = -1.0, None
    if os.path.exists(path):
        rec = load_result(path)
        best_val, best_X = rec["value"], np.array(rec["points"])
    start_val = best_val
    print(f"attack {variant} n={n}: starting from {best_val:.10f}, "
          f"{workers} workers x {seconds}s", flush=True)

    q = mp.Queue()
    procs = []
    for w in range(workers):
        seed = int.from_bytes(os.urandom(4), "little")
        p = mp.Process(target=worker, args=(variant, n, seconds, seed, best_val,
                                            None if best_X is None else best_X.tolist(), q))
        p.start()
        procs.append(p)

    done = 0
    while done < workers:
        seed, v, Xl, final = q.get()
        if final:
            done += 1
        if Xl is not None and v > best_val + 1e-13:
            best_val = v
            best_X = np.array(Xl)
            save_result(path, variant, n, best_X, best_val, meta={"attack_seed": seed})
            print(f"  IMPROVED to {best_val:.10f} (worker {seed % 1000})", flush=True)
    for p in procs:
        p.join()
    print(f"attack {variant} n={n}: {start_val:.10f} -> {best_val:.10f} "
          f"({'+' if best_val > start_val + 1e-12 else '='}{best_val - start_val:.2e})", flush=True)
    return best_val


if __name__ == "__main__":
    variant, n, seconds = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    workers = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    main(variant, n, seconds, workers)
