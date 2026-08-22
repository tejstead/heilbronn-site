"""Symmetry-constrained Heilbronn search: cyclic rotation groups.

A configuration is k orbits of size |G| under a cyclic group G of affine maps,
plus optionally the group's fixed point. Optimization runs in the 2k free
parameters via the same trust-region SLP as heil.polish.
"""

import numpy as np
from scipy.optimize import linprog

from heil import (crosses, cross_grad_rows, triples, hull_cycle, poly_area2,
                  value, project, domain_lp_constraints)


def group(variant, name):
    """List of (A, o) with map p -> A p + o. First element is identity."""
    I = np.eye(2)
    if variant == "triangle" and name == "rot3":
        # cycles reference-triangle vertices (0,0)->(1,0)->(0,1)
        A = np.array([[-1.0, -1.0], [1.0, 0.0]])
        o = np.array([1.0, 0.0])
        A2 = A @ A
        o2 = A @ o + o
        return [(I, np.zeros(2)), (A, o), (A2, o2)], np.array([1 / 3, 1 / 3])
    if variant == "square" and name == "rot2":
        return [(I, np.zeros(2)), (-I, np.array([1.0, 1.0]))], np.array([.5, .5])
    if variant == "square" and name == "rot4":
        A = np.array([[0.0, -1.0], [1.0, 0.0]])
        o = np.array([1.0, 0.0])
        els = [(I, np.zeros(2))]
        M, v = I, np.zeros(2)
        for _ in range(3):
            M, v = A @ M, A @ v + o
            els.append((M, v.copy()))
        return els, np.array([.5, .5])
    if variant == "convex" and name.startswith("rot"):
        m = int(name[3:])
        els = []
        for j in range(m):
            th = 2 * np.pi * j / m
            els.append((np.array([[np.cos(th), -np.sin(th)],
                                  [np.sin(th), np.cos(th)]]), np.zeros(2)))
        return els, np.zeros(2)
    raise ValueError((variant, name))


def build(U, els, center):
    """Expand free points U (k,2) into full config."""
    parts = [np.array([A @ u + o for (A, o) in els]) for u in U]
    X = np.vstack(parts)
    if center is not None:
        X = np.vstack([X, center[None, :]])
    return X


def build_jacobian(k, els, has_center):
    g = len(els)
    n = k * g + (1 if has_center else 0)
    J = np.zeros((2 * n, 2 * k))
    for i in range(k):
        for jg, (A, o) in enumerate(els):
            r = 2 * (i * g + jg)
            J[r:r + 2, 2 * i:2 * i + 2] = A
    return J


def polish_sym(U, variant, els, center, r0=0.04, tol=1e-12, max_outer=30, max_inner=90):
    U = U.copy().astype(float)
    k = len(U)
    has_center = center is not None
    J = build_jacobian(k, els, has_center)
    X = build(U, els, center)
    n = len(X)
    T = triples(n)

    for outer in range(max_outer):
        X = build(U, els, center)
        s = np.sign(crosses(X, T))
        s[s == 0] = 1.0
        r = r0 if outer == 0 else max(r0 / 4, 1e-4)
        improved = False
        for _ in range(max_inner):
            step = _slp_step_sym(U, els, center, J, T, s, variant, r)
            if step is None:
                r *= 0.5
                if r < tol:
                    break
                continue
            Un = step
            Xn = build(Un, els, center)
            vn = _signed_val(Xn, T, s, variant)
            v0 = _signed_val(build(U, els, center), T, s, variant)
            if vn > v0 + 1e-15:
                U = Un
                improved = True
                r = min(r * 1.5, 0.2)
            else:
                r *= 0.5
                if r < tol:
                    break
        if not improved:
            break
    X = build(U, els, center)
    return U, X, value(X, variant)


def _signed_val(X, T, s, variant):
    c = (s * crosses(X, T)).min()
    if variant == "square":
        return c / 2
    if variant == "triangle":
        return c
    if c <= 0:
        return c
    try:
        cyc = hull_cycle(X)
    except Exception:
        return -1.0
    return (c / 2) / (poly_area2(X, cyc) / 2)


def _slp_step_sym(U, els, center, J, T, s, variant, r):
    X = build(U, els, center)
    n = len(X)
    d = 2 * len(U)
    G = cross_grad_rows(X, T) * s[:, None]
    sc = s * crosses(X, T)

    GJ = G @ J
    A_rows = [np.hstack([-GJ, np.ones((len(T), 1))])]
    b_rows = [sc]

    A_dom, b_dom = domain_lp_constraints(n, variant)
    if A_dom is not None:
        A_rows.append(np.hstack([A_dom @ J, np.zeros((len(A_dom), 1))]))
        b_rows.append(b_dom - A_dom @ X.ravel())
    if variant == "convex":
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
    bounds = [(-r, r)] * d + [(None, None)]
    obj = np.zeros(d + 1)
    obj[-1] = -1.0
    res = linprog(obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success:
        return None
    return U + res.x[:d].reshape(-1, 2)


def random_sym_start(k, variant, rng):
    from heil import random_config
    return random_config(k, variant, rng, boundary_bias=rng.choice([0.0, 0.4]))


def search_sym(variant, n, gname, seconds, seed=0, verbose=False):
    """Random-restart symmetric search. Returns (best_val, best_X)."""
    import time
    els, fix = group(variant, gname)
    g = len(els)
    if n % g == 0:
        k, center = n // g, None
    elif n % g == 1:
        k, center = n // g, fix
    else:
        return -1.0, None
    rng = np.random.default_rng(seed)
    best_v, best_X = -1.0, None
    t_end = time.time() + seconds
    while time.time() < t_end:
        U0 = random_sym_start(k, variant, rng)
        try:
            U, X, v = polish_sym(U0, variant, els, center)
            # full-space polish enforces exact feasibility (sym LP can leak ~1e-7)
            from heil import polish, project
            X, v = polish(project(X, variant), variant)
        except Exception:
            continue
        if v > best_v:
            best_v, best_X = v, X.copy()
            if verbose:
                print(f"  sym {variant} n={n} {gname}: {v:.9f}", flush=True)
    return best_v, best_X
