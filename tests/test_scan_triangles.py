"""scan_triangles (integer arithmetic) against the plain Fraction scan it
replaced: same minimum, same first minimal triple, same tie set."""

import itertools
import pathlib
import random
import sys
from fractions import Fraction

import pytest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from build.vendor.verify_exact import (TIE_FACTOR, parse_points_text,  # noqa: E402
                                       scan_triangles, triangle_area)


def reference(points):
    areas, best, best_t = [], None, None
    for t in itertools.combinations(range(len(points)), 3):
        a = triangle_area(*(points[i] for i in t))
        areas.append((t, a))
        if best is None or a < best:
            best, best_t = a, t
    ties = [t for t, a in areas if a <= best * TIE_FACTOR]
    return best, best_t, ties, len(areas)


def check(points):
    assert scan_triangles(points) == reference(points)


@pytest.mark.parametrize("seed", range(40))
def test_random_rationals(seed):
    rng = random.Random(seed)
    n = rng.randint(3, 14)
    pts = [(Fraction(rng.randint(-50, 50), rng.randint(1, 30)),
            Fraction(rng.randint(-50, 50), rng.randint(1, 30))) for _ in range(n)]
    check(pts)


def test_degenerate_and_ties():
    # collinear points (zero area), repeated points, a lattice full of ties
    check([(Fraction(i), Fraction(2 * i)) for i in range(6)])
    check([(Fraction(1, 3), Fraction(1, 7))] * 3 + [(Fraction(0), Fraction(1))])
    check([(Fraction(i, 3), Fraction(j, 3)) for i in range(4) for j in range(4)])


def test_near_tie_boundary():
    # one triangle exactly at min*(1+1e-9), one just above it
    base = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))]
    eps = Fraction(1, 10 ** 9)
    pts = base + [(Fraction(1) + eps, Fraction(1)), (Fraction(1) + 2 * eps, Fraction(2))]
    check(pts)


@pytest.mark.parametrize("name", ["square-n14", "triangle-n15", "convex-n18"])
def test_real_configurations(name):
    text = (ROOT / "data" / "sources" / "external" / name / "coordinates.txt").read_text()
    check(parse_points_text(text))
