"""Production fast polish for all three variants (port of fastpolish5).

Speedups vs heil.polish (measured, square): 5-7x at n=17..44, equal quality.
Components: constraint filtering (only triangles within CUT x current min
enter the LP; every accepted step re-validated on ALL triples via the C
kernel), direct highspy with a shared solver instance (presolve off), and
column reduction (only points touching pool triangles are LP variables).

Domain handling:
  square   — box [0,1]^2 folded into variable bounds (no extra rows)
  triangle — x,y >= 0 in bounds; x+y <= 1 as one LP row per active point
  convex   — free points; linearized hull-area non-increase row (as heil.py)

The C kernel (ctest/libheil.dylib) evaluates signed mins over all triples;
falls back to numpy if the library is missing.
"""

import os

import numpy as np
import highspy

from heil import crosses, triples, value, hull_cycle, poly_area2, project

CUT = 3.0
GROW_CUT = 2.0
_INF = highspy.kHighsInf

# ---- C kernel (optional; numpy fallback) ----
try:
    import ctypes
    _lib = ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "ctest", "libheil.dylib"))
    _lib.smin_cross.restype = ctypes.c_double
    _lib.smin_cross.argtypes = [ctypes.POINTER(ctypes.c_double), ctypes.c_int,
                                ctypes.POINTER(ctypes.c_char)]
    _lib.pool_fill.restype = ctypes.c_int
    _lib.pool_fill.argtypes = [ctypes.POINTER(ctypes.c_double), ctypes.c_int,
                               ctypes.POINTER(ctypes.c_char), ctypes.c_double,
                               ctypes.POINTER(ctypes.c_int), ctypes.c_int]

    def _smin(X, s, T):
        return _lib.smin_cross(
            X.ctypes.data_as(ctypes.POINTER(ctypes.c_double)), len(X),
            s.ctypes.data_as(ctypes.POINTER(ctypes.c_char)))

    def _pool(X, s, T, thresh, buf):
        cnt = _lib.pool_fill(
            X.ctypes.data_as(ctypes.POINTER(ctypes.c_double)), len(X),
            s.ctypes.data_as(ctypes.POINTER(ctypes.c_char)), thresh,
            buf.ctypes.data_as(ctypes.POINTER(ctypes.c_int)), len(buf))
        return buf[:cnt].copy()
    _HAVE_C = True
except OSError:
    def _smin(X, s, T):
        return float((s.astype(np.float64) * crosses(X, T)).min())

    def _pool(X, s, T, thresh, buf):
        c = s.astype(np.float64) * crosses(X, T)
        return np.where(c <= thresh)[0].astype(np.int32)
    _HAVE_C = False

_H = None


def _highs():
    global _H
    if _H is None:
        _H = highspy.Highs()
        _H.setOptionValue("output_flag", False)
        _H.setOptionValue("presolve", "off")
    return _H


def _pool_lp(X, Tp, sp, sc, r, variant):
    """Filtered, column-reduced trust-region LP. Returns full dX or None."""
    n = len(X)
    pts = np.unique(Tp)
    npts = len(pts)
    col_of = np.full(n, -1, dtype=np.int32)
    col_of[pts] = np.arange(npts, dtype=np.int32)
    m = len(Tp)
    nv = 2 * npts + 1

    i, j, k = Tp[:, 0], Tp[:, 1], Tp[:, 2]
    ci, cj, ck = col_of[i], col_of[j], col_of[k]
    cols = np.empty((m, 7), dtype=np.int32)
    vals = np.empty((m, 7))
    cols[:, 0] = 2 * ci;     vals[:, 0] = -(X[j, 1] - X[k, 1]) * sp
    cols[:, 1] = 2 * ci + 1; vals[:, 1] = -(X[k, 0] - X[j, 0]) * sp
    cols[:, 2] = 2 * cj;     vals[:, 2] = -(X[k, 1] - X[i, 1]) * sp
    cols[:, 3] = 2 * cj + 1; vals[:, 3] = -(X[i, 0] - X[k, 0]) * sp
    cols[:, 4] = 2 * ck;     vals[:, 4] = -(X[i, 1] - X[j, 1]) * sp
    cols[:, 5] = 2 * ck + 1; vals[:, 5] = -(X[j, 0] - X[i, 0]) * sp
    cols[:, 6] = nv - 1;     vals[:, 6] = 1.0

    row_start = [np.arange(0, 7 * m + 1, 7, dtype=np.int32)]
    row_index = [cols.ravel()]
    row_value = [vals.ravel()]
    row_lower = [np.full(m, -_INF)]
    row_upper = [sc]
    nrows = m

    Xp = X[pts]
    if variant == "square":
        lo = np.maximum(-r, -Xp.ravel())
        up = np.minimum(r, 1.0 - Xp.ravel())
    elif variant == "triangle":
        lo = np.maximum(-r, -Xp.ravel())
        up = np.full(2 * npts, r)
        # x+y <= 1 rows for active points: dx + dy <= 1 - (x+y)
        extra_i = []
        extra_v = []
        extra_u = []
        for a, p in enumerate(pts):
            extra_i.append([2 * a, 2 * a + 1])
            extra_v.append([1.0, 1.0])
            extra_u.append(1.0 - (X[p, 0] + X[p, 1]))
        e = len(pts)
        row_start.append(row_start[-1][-1] + np.arange(2, 2 * e + 1, 2,
                                                       dtype=np.int32))
        row_index.append(np.array(extra_i, dtype=np.int32).ravel())
        row_value.append(np.array(extra_v).ravel())
        row_lower.append(np.full(e, -_INF))
        row_upper.append(np.array(extra_u))
        nrows += e
    else:  # convex
        lo = np.full(2 * npts, -r)
        up = np.full(2 * npts, r)
        # linearized hull-area non-increase (gradient over ALL hull points;
        # non-pool hull points don't move, so restrict to active columns)
        cyc = hull_cycle(X)
        gh = np.zeros(2 * n)
        L = len(cyc)
        for a_ in range(L):
            p, nxt, prv = cyc[a_], cyc[(a_ + 1) % L], cyc[(a_ - 1) % L]
            gh[2 * p] += X[nxt, 1] - X[prv, 1]
            gh[2 * p + 1] += X[prv, 0] - X[nxt, 0]
        gh_active = np.concatenate([[gh[2 * p], gh[2 * p + 1]] for p in pts])
        nz = np.nonzero(gh_active)[0].astype(np.int32)
        if len(nz):
            row_start.append(row_start[-1][-1:] + np.int32(len(nz)))
            row_index.append(nz)
            row_value.append(gh_active[nz])
            row_lower.append(np.array([-_INF]))
            row_upper.append(np.array([0.0]))
            nrows += 1

    lp = highspy.HighsLp()
    lp.num_col_ = nv
    lp.num_row_ = nrows
    costs = np.zeros(nv)
    costs[-1] = -1.0
    lp.col_cost_ = costs
    lp.col_lower_ = np.append(lo, -_INF)
    lp.col_upper_ = np.append(up, _INF)
    lp.row_lower_ = np.concatenate(row_lower)
    lp.row_upper_ = np.concatenate(row_upper)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = np.concatenate(row_start)
    lp.a_matrix_.index_ = np.concatenate(row_index)
    lp.a_matrix_.value_ = np.concatenate(row_value)

    h = _highs()
    h.clearModel()
    h.passModel(lp)
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    sol = np.array(h.getSolution().col_value)
    dX = np.zeros((n, 2))
    dX[pts] = sol[:2 * npts].reshape(-1, 2)
    return dX


def _norm_value(X, T, s, variant):
    a = _smin(X, s, T)
    if variant == "square":
        return a / 2.0
    if variant == "triangle":
        return a
    if a <= 0:
        return a
    try:
        cyc = hull_cycle(X)
    except Exception:
        return -1.0
    return (a / 2.0) / (poly_area2(X, cyc) / 2.0)


def polish_fast(X, variant, r0=0.05, tol=1e-12, max_outer=40, max_inner=120):
    """Drop-in fast replacement for heil.polish. Returns (X, value)."""
    X = np.ascontiguousarray(X, dtype=np.float64)
    n = len(X)
    T_all = triples(n)
    m = len(T_all)
    pool_buf = np.empty(m, dtype=np.int32)
    best_val = value(X, variant)

    for outer in range(max_outer):
        s_all = np.sign(crosses(X, T_all)).astype(np.int8)
        s_all[s_all == 0] = 1
        r = r0 if outer == 0 else max(r0 / 4, 1e-4)
        improved = False
        inner = 0
        while inner < max_inner:
            inner += 1
            mn = _smin(X, s_all, T_all)
            if variant == "convex" and mn <= 0:
                break
            pool = _pool(X, s_all, T_all, CUT * max(mn, 1e-15), pool_buf)
            Xn = None
            for _expand in range(4):
                Tp = T_all[pool]
                sp = s_all[pool].astype(np.float64)
                c_pool = sp * crosses(X, Tp)
                dX = _pool_lp(X, Tp, sp, c_pool, r, variant)
                if dX is None:
                    break
                cand = np.ascontiguousarray(project(X + dX, variant))
                mn_new = _smin(cand, s_all, T_all)
                newpool = _pool(cand, s_all, T_all,
                                GROW_CUT * max(mn_new, 1e-15), pool_buf)
                Xn = cand
                if np.isin(newpool, pool, assume_unique=True).all():
                    break
                pool = np.union1d(pool, newpool).astype(np.int32)
            if Xn is None:
                r *= 0.5
                if r < tol:
                    break
                continue
            # acceptance on the variant's normalized value (matters for convex,
            # where hull area changes)
            v_old = _norm_value(X, T_all, s_all, variant)
            v_new = _norm_value(Xn, T_all, s_all, variant)
            if v_new > v_old + 1e-16:
                X = Xn
                improved = True
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


if __name__ == "__main__":
    import time
    from heil import polish, random_config

    rng = np.random.default_rng(42)
    print(f"C kernel: {_HAVE_C}")
    for variant in ("square", "triangle", "convex"):
        for n in (17, 28):
            reps = 6
            Xs = [random_config(n, variant, rng) for _ in range(reps)]
            t0 = time.perf_counter()
            vc = [polish(x, variant)[1] for x in Xs]
            t_old = time.perf_counter() - t0
            t0 = time.perf_counter()
            vf = [polish_fast(x, variant)[1] for x in Xs]
            t_new = time.perf_counter() - t0
            agree = sum(1 for a, b in zip(vc, vf) if abs(a - b) < 1e-9)
            print(f"{variant:9s} n={n}: old {t_old/reps:.3f}s new {t_new/reps:.3f}s "
                  f"speedup {t_old/t_new:.1f}x agree {agree}/{reps} "
                  f"means {np.mean(vc):.8f}/{np.mean(vf):.8f}", flush=True)
