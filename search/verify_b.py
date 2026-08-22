#!/usr/bin/env python3
"""Exact verifier for Heilbronn-type point configurations.

Usage:
    python3 verify.py VARIANT FILE

VARIANT is one of: square, triangle, convex.

All geometry is done in exact arbitrary-precision integer arithmetic:
coordinates are parsed as integer numerators over 10^D, where D is the
maximum number of decimal places seen anywhere in the input file.  The
final value is an exact reduced fraction p/q; the decimal module is used
only to render it as a 30-significant-digit decimal string for display.
"""

import json
import math
import re
import sys
from decimal import Decimal, localcontext
from itertools import combinations

COORD_RE = re.compile(r'^[+-]?\d+(?:\.(\d+))?$')

RELTOL_NUM = 10 ** 9          # ties: (T - Tmin)/Tmin <= 1e-9  <=>
RELTOL_DEN = 10 ** 9 + 1      # T * 1e9 <= Tmin * (1e9 + 1)   (exact ints)


def fail(msg):
    sys.stderr.write("error: %s\n" % msg)
    sys.exit(1)


def parse_file(path):
    """Return (tokens, D) where tokens is a list of (xtok, ytok, lineno)."""
    tokens = []
    try:
        f = open(path, "r")
    except OSError as e:
        fail("cannot open %s: %s" % (path, e))
    with f:
        for lineno, line in enumerate(f, 1):
            s = line.strip()
            if not s or s.startswith('#'):
                continue
            parts = s.split()
            if len(parts) != 2:
                fail("line %d: expected exactly 2 numbers, got %d tokens"
                     % (lineno, len(parts)))
            for t in parts:
                if not COORD_RE.match(t):
                    fail("line %d: cannot parse coordinate %r as a plain "
                         "decimal number" % (lineno, t))
            tokens.append((parts[0], parts[1], lineno))
    if not tokens:
        fail("no points found in %s" % path)
    max_d = 0
    for xt, yt, _ in tokens:
        for t in (xt, yt):
            m = COORD_RE.match(t)
            if m.group(1) is not None:
                max_d = max(max_d, len(m.group(1)))
    return tokens, max_d


def coord_to_int(tok, d):
    """Exact integer numerator of tok over 10^d."""
    neg = tok.startswith('-')
    body = tok.lstrip('+-')
    if '.' in body:
        int_part, frac_part = body.split('.', 1)
    else:
        int_part, frac_part = body, ''
    frac_part = frac_part.ljust(d, '0')
    v = int(int_part) * (10 ** d) + (int(frac_part) if frac_part else 0)
    return -v if neg else v


def twice_area(p, q, r):
    """|2 * area| of triangle (p,q,r) in integer units (exact shoelace)."""
    return abs(p[0] * (q[1] - r[1])
               + q[0] * (r[1] - p[1])
               + r[0] * (p[1] - q[1]))


def cross(o, a, b):
    """Exact integer cross product of vectors OA and OB."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def convex_hull(points):
    """Andrew's monotone chain.  Returns hull vertices in CCW order,
    excluding collinear boundary points.  Exact integer arithmetic."""
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts
    lower = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def hull_twice_area(hull):
    """Exact integer |2 * area| of a polygon via the shoelace sum."""
    n = len(hull)
    if n < 3:
        return 0
    s = 0
    for i in range(n):
        x1, y1 = hull[i]
        x2, y2 = hull[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s)


def check_feasibility(variant, pts, tokens, scale):
    """Exact integer domain tests.  Returns a list of violation strings."""
    violations = []
    for i, ((x, y), (xt, yt, lineno)) in enumerate(zip(pts, tokens)):
        where = "point %d (line %d) = (%s, %s)" % (i, lineno, xt, yt)
        if variant == "square":
            if x < 0:
                violations.append(where + ": x < 0")
            if x > scale:
                violations.append(where + ": x > 1")
            if y < 0:
                violations.append(where + ": y < 0")
            if y > scale:
                violations.append(where + ": y > 1")
        elif variant == "triangle":
            if x < 0:
                violations.append(where + ": x < 0")
            if y < 0:
                violations.append(where + ": y < 0")
            if x + y > scale:
                violations.append(where + ": x + y > 1")
        # convex: no domain constraints
    return violations


def value_to_30sig(p, q):
    """Render exact fraction p/q as a 30-significant-digit decimal string."""
    if p == 0:
        return "0"
    with localcontext() as ctx:
        ctx.prec = 60
        d = Decimal(p) / Decimal(q)
        # round to exactly 30 significant digits
        r = d.quantize(Decimal(1).scaleb(d.adjusted() - 29))
        return format(r, 'f')


def main(argv):
    if len(argv) != 3:
        fail("usage: python3 verify.py VARIANT FILE   "
             "(VARIANT: square | triangle | convex)")
    variant, path = argv[1], argv[2]
    if variant not in ("square", "triangle", "convex"):
        fail("unknown variant %r (expected square, triangle or convex)"
             % variant)

    tokens, D = parse_file(path)
    scale = 10 ** D
    pts = [(coord_to_int(xt, D), coord_to_int(yt, D)) for xt, yt, _ in tokens]
    n = len(pts)
    if n < 3:
        fail("need at least 3 points, got %d" % n)

    violations = check_feasibility(variant, pts, tokens, scale)

    # ---- pass 1: enumerate all C(n,3) triples, find the minimum ----
    min_t = None
    min_triple = None
    count = 0
    for i, j, k in combinations(range(n), 3):
        t = twice_area(pts[i], pts[j], pts[k])
        count += 1
        if min_t is None or t < min_t:
            min_t = t
            min_triple = (i, j, k)
    assert count == math.comb(n, 3), \
        "enumerated %d triples, expected C(%d,3) = %d" % (
            count, n, math.comb(n, 3))

    # ---- pass 2: count ties within relative 1e-9 of the minimum ----
    ties = 0
    for i, j, k in combinations(range(n), 3):
        t = twice_area(pts[i], pts[j], pts[k])
        if t * RELTOL_NUM <= min_t * RELTOL_DEN:
            ties += 1

    # ---- exact value as a fraction of integers ----
    # min_t = 2 * (min triangle area) * 10^(2D)
    hull_vertex_count = None
    if variant == "square":
        # value = min area / 1 = min_t / (2 * 10^(2D))
        num, den = min_t, 2 * scale * scale
    elif variant == "triangle":
        # value = 2 * min area = min_t / 10^(2D)
        num, den = min_t, scale * scale
    else:  # convex
        hull = convex_hull(pts)
        hull_vertex_count = len(hull)
        h2 = hull_twice_area(hull)
        if h2 == 0:
            violations.append(
                "convex hull has zero area (all points are collinear); "
                "value is undefined and reported as 0")
            num, den = 0, 1
        else:
            # value = (min_t / (2*10^(2D))) / (h2 / (2*10^(2D))) = min_t / h2
            num, den = min_t, h2

    if num == 0:
        num, den = 0, 1
    else:
        g = math.gcd(num, den)
        num //= g
        den //= g

    out = {
        "n": n,
        "triples_checked": count,
        "value": value_to_30sig(num, den),
        "value_fraction": "%d/%d" % (num, den),
        "min_triple": list(min_triple),
        "num_min_ties": ties,
        "feasible": len(violations) == 0,
        "violations": violations,
        "hull_vertex_count": hull_vertex_count,
    }
    print(json.dumps(out))


if __name__ == "__main__":
    main(sys.argv)
