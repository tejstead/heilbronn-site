#!/usr/bin/env python3
"""Exact verifier for Heilbronn-type point configurations.

Adapted from the companion search repository's verifiers/verify_a.py
(same arithmetic, same output schema) with the core exposed as a library
function `verify(variant, points)` so the build pipeline can call it per
configuration. The CLI form is kept byte-compatible:

    python3 verify_exact.py VARIANT FILE

All arithmetic is exact. Coordinates are read as rationals
(fractions.Fraction); the triangle scan puts them over one common
denominator and works with Python integers, which is the same arithmetic
without a gcd per operation. The only floating/decimal conversion happens
at the very end, purely for display of the value as a 30-significant-digit
decimal string.
"""

import sys
import json
import math
import itertools
from fractions import Fraction
from decimal import Decimal, Context, ROUND_HALF_EVEN

VARIANTS = ("square", "triangle", "convex")

ZERO = Fraction(0)
ONE = Fraction(1)
# Exact rational representation of the relative tie tolerance 1e-9.
TIE_FACTOR = ONE + Fraction(1, 10 ** 9)


def parse_points_text(text):
    """Parse coordinates.txt content into a list of (Fraction, Fraction).

    Lines starting with '#' are comments; blank lines are ignored. Each
    remaining line must contain exactly two decimal numbers separated by
    whitespace, parsed EXACTLY as rationals via Fraction(string).
    """
    points = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2:
            raise ValueError(
                "line %d: expected 2 numbers, got %d: %r" % (lineno, len(parts), raw)
            )
        points.append((Fraction(parts[0]), Fraction(parts[1])))
    return points


def parse_points(path):
    with open(path, "r") as fh:
        return parse_points_text(fh.read())


def cross(o, a, b):
    """Exact cross product (a - o) x (b - o) as a Fraction."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def triangle_area(p, q, r):
    """Exact area of triangle pqr via the shoelace / cross-product formula."""
    return abs(cross(p, q, r)) / 2


def convex_hull(points):
    """Andrew's monotone chain convex hull using exact cross products.

    Returns hull vertices in counter-clockwise order, excluding collinear
    interior boundary points. Handles degenerate input (all collinear or
    fewer than 3 distinct points) by returning fewer than 3 vertices.
    """
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
    hull = lower[:-1] + upper[:-1]
    if len(hull) < 3:
        # All points collinear: degenerate hull.
        return pts[:2]
    return hull


def polygon_area(vertices):
    """Exact polygon area by the shoelace formula (vertices in order)."""
    n = len(vertices)
    if n < 3:
        return ZERO
    total = ZERO
    for i in range(n):
        x1, y1 = vertices[i]
        x2, y2 = vertices[(i + 1) % n]
        total += x1 * y2 - x2 * y1
    return abs(total) / 2


def scan_triangles(points):
    """Exact minimum triangle area over ALL C(n,3) triples, and the tie set.

    Every coordinate is scaled by L, the lcm of all denominators, to an
    integer; twice the area of a triple is then |cross| / L**2 with cross an
    exact integer. Returns (min_area as a Fraction, the first triple in
    itertools.combinations order attaining it, the list of all triples whose
    area is within relative 1e-9 of the minimum (area <= min * (1 + 1e-9),
    tested exactly as cross * 10**9 <= min_cross * (10**9 + 1)), and the
    number of triples checked)."""
    pts = [(Fraction(x), Fraction(y)) for x, y in points]
    L = 1
    for x, y in pts:
        L = math.lcm(L, x.denominator, y.denominator)
    X = [x.numerator * (L // x.denominator) for x, _ in pts]
    Y = [y.numerator * (L // y.denominator) for _, y in pts]
    n = len(pts)
    crosses = []
    append = crosses.append
    best = None
    best_triple = None
    for i in range(n - 2):
        xi, yi = X[i], Y[i]
        for j in range(i + 1, n - 1):
            dx, dy = X[j] - xi, Y[j] - yi
            for k in range(j + 1, n):
                c = dx * (Y[k] - yi) - dy * (X[k] - xi)
                if c < 0:
                    c = -c
                append(c)
                if best is None or c < best:
                    best = c
                    best_triple = (i, j, k)
    scale = 10 ** 9
    bound = best * (scale + 1)
    ties = [t for t, c in zip(itertools.combinations(range(n), 3), crosses)
            if c * scale <= bound]
    return Fraction(best, 2 * L * L), best_triple, ties, len(crosses)


def check_feasibility(variant, points):
    """Exact domain membership tests. Returns (feasible, violations)."""
    violations = []
    if variant == "square":
        for i, (x, y) in enumerate(points):
            if not (ZERO <= x <= ONE):
                violations.append("point %d: x = %s is outside [0, 1]" % (i, x))
            if not (ZERO <= y <= ONE):
                violations.append("point %d: y = %s is outside [0, 1]" % (i, y))
    elif variant == "triangle":
        for i, (x, y) in enumerate(points):
            if x < ZERO:
                violations.append("point %d: x = %s violates x >= 0" % (i, x))
            if y < ZERO:
                violations.append("point %d: y = %s violates y >= 0" % (i, y))
            if x + y > ONE:
                violations.append(
                    "point %d: x + y = %s violates x + y <= 1" % (i, x + y)
                )
    elif variant == "convex":
        pass  # Points may be anywhere; the domain is their own hull.
    return (len(violations) == 0, violations)


def fraction_to_30sig(fr):
    """Render an exact Fraction as a decimal string with 30 significant
    digits (correctly rounded). Exact terminating decimals shorter than
    30 digits are shown exactly."""
    if fr == 0:
        return "0"
    ctx = Context(prec=30, rounding=ROUND_HALF_EVEN)
    d = ctx.divide(Decimal(fr.numerator), Decimal(fr.denominator))
    return str(d)


def verify(variant, points):
    """Run the full exact verification. Returns the result dict (the same
    schema the upstream verifiers print) plus the exact value under the
    non-serialized key "_value" for callers that need the Fraction."""
    if variant not in VARIANTS:
        raise ValueError("unknown variant %r" % (variant,))
    n = len(points)
    if n < 3:
        raise ValueError("need at least 3 points, got %d" % n)

    feasible, violations = check_feasibility(variant, points)

    min_area, min_triple, ties, triples_checked = scan_triangles(points)
    assert triples_checked == math.comb(n, 3)
    num_min_ties = len(ties)

    # Normalize by the containing region's exact area.
    hull_vertex_count = None
    if variant == "square":
        value = min_area  # region area is exactly 1
    elif variant == "triangle":
        value = 2 * min_area  # region area is exactly 1/2
    else:  # convex
        hull = convex_hull(points)
        hull_vertex_count = len(hull)
        hull_area = polygon_area(hull)
        value = ZERO if hull_area == 0 else min_area / hull_area

    return {
        "n": n,
        "triples_checked": triples_checked,
        "value": fraction_to_30sig(value),
        "value_fraction": "%d/%d" % (value.numerator, value.denominator),
        "min_triple": list(min_triple),
        "num_min_ties": num_min_ties,
        "feasible": feasible,
        "violations": violations,
        "hull_vertex_count": hull_vertex_count,
        "_value": value,
    }


def main(argv):
    if len(argv) != 3 or argv[1] not in VARIANTS:
        sys.stderr.write("usage: python3 verify_exact.py VARIANT FILE\n")
        sys.stderr.write("VARIANT: one of %s\n" % ", ".join(VARIANTS))
        return 2
    result = verify(argv[1], parse_points(argv[2]))
    result.pop("_value")
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
