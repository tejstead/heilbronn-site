"""Heilbronn-type maximin triangle problems: square / triangle / convex-region variants.

Value conventions (all in "normalized area" units, domain area = 1):
  square:   domain [0,1]^2 (area 1).          A = min|cross| / 2
  triangle: domain (0,0),(1,0),(0,1) (area 1/2, affine-invariant). A = min|cross|
  convex:   free points, region = convex hull scaled to area 1.    A = (min|cross|/2)/hullarea
where cross(i,j,k) = 2 * signed area of triangle (p_i, p_j, p_k).
"""

import itertools
import json
import os
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import ConvexHull

# ---------------------------------------------------------------- geometry

_TRIPLES_CACHE = {}


def triples(n):
    if n not in _TRIPLES_CACHE:
        _TRIPLES_CACHE[n] = np.array(list(itertools.combinations(range(n), 3)), dtype=np.int64)
    return _TRIPLES_CACHE[n]


def crosses(X, T=None):
    """Signed 2*area for each triple. X: (n,2)."""
    if T is None:
        T = triples(len(X))
    i, j, k = T[:, 0], T[:, 1], T[:, 2]
    return ((X[j, 0] - X[i, 0]) * (X[k, 1] - X[i, 1])
            - (X[k, 0] - X[i, 0]) * (X[j, 1] - X[i, 1]))


def cross_grad_rows(X, T):
    """Sparse-ish gradient of cross wrt flattened X, returned as dense (m, 2n)."""
    n = len(X)
    m = len(T)
    G = np.zeros((m, 2 * n))
    i, j, k = T[:, 0], T[:, 1], T[:, 2]
    rows = np.arange(m)
    # cross = xi(yj-yk) + xj(yk-yi) + xk(yi-yj)
    G[rows, 2 * i] = X[j, 1] - X[k, 1]
    G[rows, 2 * j] = X[k, 1] - X[i, 1]
    G[rows, 2 * k] = X[i, 1] - X[j, 1]
    G[rows, 2 * i + 1] = X[k, 0] - X[j, 0]
    G[rows, 2 * j + 1] = X[i, 0] - X[k, 0]
    G[rows, 2 * k + 1] = X[j, 0] - X[i, 0]
    return G


def hull_cycle(X):
    """Indices of convex hull vertices in counterclockwise order."""
    return ConvexHull(X).vertices  # scipy returns CCW for 2D


def poly_area2(X, cyc):
    """2 * area of polygon X[cyc] (positive if CCW)."""
    P = X[cyc]
    x, y = P[:, 0], P[:, 1]
    return float(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))


def value(X, variant):
    """Normalized Heilbronn value of configuration X."""
    a = np.abs(crosses(X)).min()
    if variant == "square":
        return a / 2.0
    if variant == "triangle":
        return a
    if variant == "convex":
        cyc = hull_cycle(X)
        return (a / 2.0) / (poly_area2(X, cyc) / 2.0)
    raise ValueError(variant)


# ---------------------------------------------------------------- domains

def random_config(n, variant, rng, boundary_bias=0.0):
    if variant == "square":
        X = rng.random((n, 2))
        if boundary_bias > 0:
            for p in range(n):
                for c in range(2):
                    if rng.random() < boundary_bias:
                        X[p, c] = float(rng.integers(2))
        return X
    if variant == "triangle":
        # uniform in simplex x,y>=0, x+y<=1
        a = rng.random((n, 2))
        flip = a.sum(axis=1) > 1
        a[flip] = 1 - a[flip]
        if boundary_bias > 0:
            for p in range(n):
                r = rng.random()
                if r < boundary_bias:
                    e = rng.integers(3)
                    t = rng.random()
                    if e == 0:
                        a[p] = (t, 0)
                    elif e == 1:
                        a[p] = (0, t)
                    else:
                        a[p] = (t, 1 - t)
        return a
    if variant == "convex":
        # points on/inside a circle; hull normalization happens in objective
        ang = rng.random(n) * 2 * np.pi
        rad = np.sqrt(rng.random(n))
        if boundary_bias > 0:
            rad[rng.random(n) < boundary_bias] = 1.0
        return np.column_stack([rad * np.cos(ang), rad * np.sin(ang)])
    raise ValueError(variant)


def project(X, variant):
    """Exact projection into the domain (no-op for convex)."""
    if variant == "square":
        return np.clip(X, 0.0, 1.0)
    if variant == "triangle":
        X = np.clip(X, 0.0, None)
        s = X.sum(axis=1)
        bad = s > 1.0
        if bad.any():
            X = X.copy()
            X[bad] -= ((s[bad] - 1.0) / 2.0)[:, None]  # orthogonal proj onto x+y=1
            X = np.clip(X, 0.0, None)
        return X
    return X


def domain_lp_constraints(n, variant):
    """(A_dom, b_dom) with A_dom @ x <= b_dom for flattened coords (square/triangle)."""
    if variant == "square":
        A = np.vstack([np.eye(2 * n), -np.eye(2 * n)])
        b = np.concatenate([np.ones(2 * n), np.zeros(2 * n)])
        return A, b
    if variant == "triangle":
        rows = []
        rhs = []
        for p in range(n):
            r = np.zeros(2 * n); r[2 * p] = -1; rows.append(r); rhs.append(0)      # x >= 0
            r = np.zeros(2 * n); r[2 * p + 1] = -1; rows.append(r); rhs.append(0)  # y >= 0
            r = np.zeros(2 * n); r[2 * p] = 1; r[2 * p + 1] = 1; rows.append(r); rhs.append(1)
        return np.array(rows), np.array(rhs, dtype=float)
    return None, None  # convex handled separately


# ---------------------------------------------------------------- SLP local solver

def polish(X, variant, r0=0.05, tol=1e-12, max_outer=40, max_inner=120):
    """Maximize min |triangle area| by successive linear programming with trust region.

    Returns (X_opt, value). Orientations (signs) are re-fixed each outer round.
    """
    X = X.copy().astype(float)
    n = len(X)
    T = triples(n)
    best_val = value(X, variant)

    for outer in range(max_outer):
        s = np.sign(crosses(X, T))
        s[s == 0] = 1.0
        r = r0 if outer == 0 else max(r0 / 4, 1e-4)
        improved = False
        for _ in range(max_inner):
            res = _slp_step(X, T, s, variant, r)
            if res is None:
                r *= 0.5
                if r < tol:
                    break
                continue
            Xn, predicted = res
            vn = _signed_value(Xn, T, s, variant)
            v0 = _signed_value(X, T, s, variant)
            if vn > v0 + 1e-15:
                X = Xn
                improved = True
                if predicted - vn < 0.1 * max(predicted - v0, 1e-18):
                    r = min(r * 1.6, 0.25)
            else:
                r *= 0.5
                if r < tol:
                    break
        cur = value(X, variant)
        if cur > best_val + 1e-13:
            best_val = cur
        elif not improved:
            break
    return X, value(X, variant)


def _signed_value(X, T, s, variant):
    c = s * crosses(X, T)
    a = c.min()
    if variant == "square":
        return a / 2.0
    if variant == "triangle":
        return a
    # convex
    if a <= 0:
        return a  # invalid orientation; treat as bad
    try:
        cyc = hull_cycle(X)
    except Exception:
        return -1.0
    return (a / 2.0) / (poly_area2(X, cyc) / 2.0)


def _slp_step(X, T, s, variant, r):
    """One trust-region LP step. Variables z = (dX flat (2n), t). Maximize t."""
    n = len(X)
    m = len(T)
    c_now = crosses(X, T)
    G = cross_grad_rows(X, T) * s[:, None]  # signed gradients
    sc = s * c_now

    if variant == "convex":
        # normalize current scale: work with hull area fixed via linearized constraint
        cyc = hull_cycle(X)
        hA2 = poly_area2(X, cyc)  # 2*hull area
        # gradient of 2*hullarea wrt coords: shoelace derivative
        gh = np.zeros(2 * n)
        L = len(cyc)
        for a_ in range(L):
            p = cyc[a_]
            nxt = cyc[(a_ + 1) % L]
            prv = cyc[(a_ - 1) % L]
            gh[2 * p] += X[nxt, 1] - X[prv, 1]
            gh[2 * p + 1] += X[prv, 0] - X[nxt, 0]
        # objective units: t approximates min sc; value = t / (2*hA2/2)/2 ... we simply
        # maximize t while keeping hull area (linearized) <= current -> ratio improves if t up
        A_extra = [np.append(gh, 0.0)]
        b_extra = [0.0]  # gh . dX <= 0 : hull area non-increasing (to 1st order)
        scale = hA2
    else:
        A_extra, b_extra = [], []
        scale = 1.0

    # constraints: -(sc + G dX) + 2t*scale_adjust <= 0  =>  -G dX + t_col <= sc
    # we let t be in cross units: sc + G dX >= t  -> -G dX + t <= sc
    A_tri = np.hstack([-G, np.ones((m, 1))])
    b_tri = sc.copy()

    A_dom, b_dom = domain_lp_constraints(n, variant)
    blocks_A = [A_tri]
    blocks_b = [b_tri]
    if A_dom is not None:
        Xf = X.ravel()
        blocks_A.append(np.hstack([A_dom, np.zeros((len(A_dom), 1))]))
        blocks_b.append(b_dom - A_dom @ Xf)
    for a_, b_ in zip(A_extra, b_extra):
        blocks_A.append(a_.reshape(1, -1))
        blocks_b.append(np.array([b_]))

    A_ub = np.vstack(blocks_A)
    b_ub = np.concatenate(blocks_b)

    lb = np.full(2 * n + 1, -r)
    ub = np.full(2 * n + 1, r)
    lb[-1] = -np.inf
    ub[-1] = np.inf
    obj = np.zeros(2 * n + 1)
    obj[-1] = -1.0  # maximize t

    res = linprog(obj, A_ub=A_ub, b_ub=b_ub, bounds=list(zip(lb, ub)), method="highs")
    if not res.success:
        return None
    dX = res.x[:2 * n].reshape(-1, 2)
    t = res.x[-1]
    Xn = project(X + dX, variant)  # LP solver tolerance can leak ~1e-7 outside
    if variant == "square":
        pred = t / 2.0
    elif variant == "triangle":
        pred = t
    else:
        pred = (t / 2.0) / (scale / 2.0)
    return Xn, pred


# ---------------------------------------------------------------- canonicalize / io

def canonical(X, variant):
    """Shift/scale convex configs to hull area 1 centered at origin; others unchanged."""
    X = X.copy()
    if variant == "convex":
        cyc = hull_cycle(X)
        A = poly_area2(X, cyc) / 2.0
        X -= X.mean(axis=0)
        X /= np.sqrt(A)
    return X


def save_result(path, variant, n, X, val, meta=None):
    X = canonical(X, variant)
    rec = {"variant": variant, "n": n, "value": val,
           "points": X.tolist(), "meta": meta or {}}
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(rec, f, indent=1)


def load_result(path):
    with open(path) as f:
        rec = json.load(f)
    return rec
