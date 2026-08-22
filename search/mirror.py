"""Mirror-symmetric search: k point-pairs (x, ±y) + f points on the axis (y=0).

Parameterization U = [ (x1,y1)...(xk,yk), a1..af ]; config has n = 2k + f points.
Same trust-region SLP as sym.py but with the mirror Jacobian.
"""

import time
import numpy as np
from scipy.optimize import linprog

from heil import (crosses, cross_grad_rows, triples, hull_cycle, poly_area2,
                  value, random_config, polish)


def build(pairs, axis):
    rows = []
    for (x, y) in pairs:
        rows.append([x, y])
        rows.append([x, -y])
    for a in axis:
        rows.append([a, 0.0])
    return np.array(rows)


def jac(k, f):
    n = 2 * k + f
    J = np.zeros((2 * n, 2 * k + f))
    for i in range(k):
        J[2 * (2 * i), 2 * i] = 1        # x of upper point
        J[2 * (2 * i) + 1, 2 * i + 1] = 1  # y of upper point
        J[2 * (2 * i + 1), 2 * i] = 1      # x of lower point
        J[2 * (2 * i + 1) + 1, 2 * i + 1] = -1  # y of lower point
    for j in range(f):
        J[2 * (2 * k + j), 2 * k + j] = 1  # x of axis point (y fixed 0)
    return J


def polish_mirror(pairs, axis, r0=0.04, tol=1e-12, max_outer=30, max_inner=90):
    k, f = len(pairs), len(axis)
    U = np.concatenate([np.asarray(pairs, float).ravel(), np.asarray(axis, float)])
    J = jac(k, f)
    n = 2 * k + f
    T = triples(n)

    def expand(U):
        return build(U[:2 * k].reshape(-1, 2), U[2 * k:])

    def sval(X, s):
        c = (s * crosses(X, T)).min()
        if c <= 0:
            return c
        try:
            cyc = hull_cycle(X)
        except Exception:
            return -1.0
        return (c / 2) / (poly_area2(X, cyc) / 2)

    for outer in range(max_outer):
        X = expand(U)
        s = np.sign(crosses(X, T))
        s[s == 0] = 1.0
        r = r0 if outer == 0 else max(r0 / 4, 1e-4)
        improved = False
        for _ in range(max_inner):
            X = expand(U)
            G = cross_grad_rows(X, T) * s[:, None]
            sc = s * crosses(X, T)
            GJ = G @ J
            m = len(T)
            A_rows = [np.hstack([-GJ, np.ones((m, 1))])]
            b_rows = [sc]
            cyc = hull_cycle(X)
            gh = np.zeros(2 * n)
            L = len(cyc)
            for a_ in range(L):
                p, nxt, prv = cyc[a_], cyc[(a_ + 1) % L], cyc[(a_ - 1) % L]
                gh[2 * p] += X[nxt, 1] - X[prv, 1]
                gh[2 * p + 1] += X[prv, 0] - X[nxt, 0]
            A_rows.append(np.append(gh @ J, 0.0).reshape(1, -1))
            b_rows.append(np.array([0.0]))
            A_ub = np.vstack(A_rows)
            b_ub = np.concatenate(b_rows)
            d = 2 * k + f
            bounds = [(-r, r)] * d + [(None, None)]
            obj = np.zeros(d + 1)
            obj[-1] = -1.0
            res = linprog(obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
            if not res.success:
                r *= 0.5
                if r < tol:
                    break
                continue
            Un = U + res.x[:d]
            if sval(expand(Un), s) > sval(expand(U), s) + 1e-15:
                U = Un
                improved = True
                r = min(r * 1.5, 0.2)
            else:
                r *= 0.5
                if r < tol:
                    break
        if not improved:
            break
    X = expand(U)
    return X, value(X, "convex")


def search_mirror(n, seconds, seed=0, verbose=False):
    """Random restarts over all (k, f) splits with 2k + f = n."""
    rng = np.random.default_rng(seed)
    best_v, best_X = -1.0, None
    splits = [(k, n - 2 * k) for k in range(n // 3, n // 2 + 1) if n - 2 * k >= 0]
    t_end = time.time() + seconds
    while time.time() < t_end:
        k, f = splits[rng.integers(len(splits))]
        ang = rng.random(k) * np.pi  # upper half plane
        rad = 0.3 + 0.7 * np.sqrt(rng.random(k))
        pairs = np.column_stack([rad * np.cos(ang), np.abs(rad * np.sin(ang))])
        axis = np.sort(rng.uniform(-1, 1, f))
        try:
            X, v = polish_mirror(pairs, axis)
            X, v = polish(X, "convex")  # full-space finish
        except Exception:
            continue
        if v > best_v:
            best_v, best_X = v, X.copy()
            if verbose:
                print(f"  mirror n={n} (k={k},f={f}): {v:.10f}", flush=True)
    return best_v, best_X


if __name__ == "__main__":
    import os
    import sys
    from heil import load_result, save_result
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    for n in (17, 19, 20, 18):
        path = f"results/convex/n{n}.json"
        cur = load_result(path)["value"]
        v, X = search_mirror(n, secs, seed=int.from_bytes(os.urandom(4), "little"))
        tag = ""
        if X is not None and v > cur + 1e-12:
            save_result(path, "convex", n, X, v, meta={"sym": "mirror"})
            tag = "  IMPROVED+SAVED"
        print(f"convex n={n} mirror: {v:.10f} (cur {cur:.10f}){tag}", flush=True)
    print("MIRROR DONE", flush=True)
