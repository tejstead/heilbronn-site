#!/usr/bin/env python3
"""Import exact configurations published in the arXiv papers into
data/sources/papers/.

Sources:
- arXiv:2603.11107 (Sudermann-Merx) — square: exact coordinates for n=5..9
  (paper §6 / spiralulam exact_coordinates.py) and the appendix's best-known
  exact forms for n=10, 11, 12, 16 (Comellas-Yebra, Goldberg, Beyleveld).
- arXiv:2607.15021 (Sudermann-Merx) — triangle: exact coordinates for
  n=5, 6, 7 (Table 1; unit right triangle = our storage frame).

Coordinates are emitted as 30-decimal literals truncated toward zero, which
preserves feasibility exactly (0 ≤ x floors to ≤ x, and sums for the triangle
constraint only shrink). The exact value implied by the literals then sits
within ~1e-29 of the true optimum — far above any float64-derived source, so
ingest's best-by-exact-value selection adopts these automatically.
"""

import json
import pathlib
import sys

import mpmath
import sympy as sp

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "data" / "sources" / "papers"

mpmath.mp.dps = 60

SQ = "square"
TR = "triangle"

r7 = sp.CRootOf(19 * sp.Symbol("f") ** 3 - 27 * sp.Symbol("f") ** 2 + 11 * sp.Symbol("f") - 1, 1)
s13 = sp.sqrt(13)
s65 = sp.sqrt(65)
s3 = sp.sqrt(3)
s2 = sp.sqrt(2)

c10 = sp.cbrt(63 + 8 * sp.sqrt(62))
z10 = sp.Rational(3, 4) - c10 / 12 - 1 / (12 * c10)
x10 = z10 / 2
y10 = 1 - 3 * z10 + 2 * z10 ** 2

c12 = sp.cbrt(27 + 3 * sp.sqrt(57))
x12 = 1 - (c12 ** 2 + 6) / (6 * c12)
y12 = 2 * x12 ** 2 - 3 * x12 + sp.Rational(1, 2)

R = sp.Rational

CONFIGS = {
    (SQ, 5): {
        "ref": "arXiv:2603.11107",
        "points": [(0, R(1, 3)), (s3 / 3, 0), (1, 1 - s3 / 3), (R(2, 3), 1), (0, 1)],
    },
    (SQ, 6): {
        "ref": "arXiv:2603.11107",
        "note": "one member of the optimal family",
        "points": [(0, R(1005, 5222)), (R(1, 2), 0), (1, R(803, 2611)),
                   (R(1, 2), 1), (0, R(1808, 2611)), (1, R(4217, 5222))],
    },
    (SQ, 7): {
        "ref": "arXiv:2603.11107",
        "note": "in terms of the middle root of 19f^3 - 27f^2 + 11f - 1",
        "points": [
            (0, 3 - 16 * r7 + 19 * r7 ** 2),
            (10 - 27 * r7 + 19 * r7 ** 2, 0),
            (1, R(1, 2) + 5 * r7 - 19 * r7 ** 2 / 2),
            (1, 1), (0, 1),
            (2 + 8 * r7 - 19 * r7 ** 2, 5 - 41 * r7 + 57 * r7 ** 2),
            (10 - 27 * r7 + 19 * r7 ** 2, r7),
        ],
    },
    (SQ, 8): {
        "ref": "arXiv:2603.11107",
        "points": [
            (0, 0), (R(1, 6) + s13 / 6, 0), (1, R(7, 18) - s13 / 18), (1, 1),
            (0, s13 / 18 + R(11, 18)), (R(5, 6) - s13 / 6, 1),
            (R(5, 6) - s13 / 6, R(7, 9) - s13 / 9),
            (R(1, 6) + s13 / 6, R(2, 9) + s13 / 9),
        ],
    },
    (SQ, 9): {
        "ref": "arXiv:2603.11107",
        "points": [
            (0, 1 - s65 / 10), (R(3, 8) - s65 / 40, 0),
            (1, R(9, 16) - 3 * s65 / 80), (R(3, 8) - s65 / 40, 1),
            (0, s65 / 40 + R(5, 8)), (R(1, 4) + s65 / 20, R(3, 4) - s65 / 20),
            (3 * s65 / 80 + R(7, 16), 0), (s65 / 10, 1), (1, s65 / 40 + R(5, 8)),
        ],
    },
    (SQ, 10): {
        "ref": "arXiv:2603.11107",
        "note": "Comellas-Yebra closed form (appendix)",
        "points": [(x10, 0), (1 - y10, 0), (0, x10), (1, y10), (1 - z10, z10),
                   (z10, 1 - z10), (0, 1 - y10), (1, 1 - x10), (y10, 1), (1 - x10, 1)],
    },
    (SQ, 11): {
        "ref": "arXiv:2603.11107",
        "note": "Goldberg's rational configuration, value exactly 1/27",
        "points": [(R(1, 3), 0), (R(2, 3), 0), (0, R(2, 9)), (1, R(2, 9)),
                   (R(1, 3), R(4, 9)), (R(2, 3), R(4, 9)), (0, R(2, 3)),
                   (1, R(2, 3)), (R(1, 2), R(7, 9)), (R(1, 6), 1), (R(5, 6), 1)],
    },
    (SQ, 12): {
        "ref": "arXiv:2603.11107",
        "note": "Comellas-Yebra closed form (appendix)",
        "points": [(x12, 0), (1 - x12, 0), (0, x12), (1, x12), (R(1, 2), y12),
                   (y12, R(1, 2)), (1 - y12, R(1, 2)), (R(1, 2), 1 - y12),
                   (0, 1 - x12), (1, 1 - x12), (x12, 1), (1 - x12, 1)],
    },
    (SQ, 16): {
        "ref": "arXiv:2603.11107",
        "note": "Beyleveld's all-rational configuration, value exactly 7/341",
        "points": [(R(2, 31), 0), (R(29, 31), 1), (R(23, 31), 0), (R(8, 31), 1),
                   (0, R(10, 33)), (1, R(23, 33)), (1, R(2, 33)), (0, R(31, 33)),
                   (R(8, 31), R(4, 11)), (R(23, 31), R(7, 11)),
                   (R(10, 31), R(2, 33)), (R(21, 31), R(31, 33)),
                   (R(21, 31), R(10, 33)), (R(10, 31), R(23, 33)),
                   (R(29, 31), R(4, 11)), (R(2, 31), R(7, 11))],
    },
    (TR, 5): {
        "ref": "arXiv:2607.15021",
        "note": "one member of the optimal family",
        "points": [(0, 0), (2 - s2, 0), (0, 1), (2 - s2, s2 - 1), (3 - 2 * s2, s2 - 1)],
    },
    (TR, 6): {
        "ref": "arXiv:2607.15021",
        "note": "one member of the optimal family",
        "points": [(R(1, 4), 0), (R(3, 4), 0), (0, R(3, 8)), (R(3, 4), R(1, 4)),
                   (0, 1), (R(1, 4), R(1, 2))],
    },
    (TR, 7): {
        "ref": "arXiv:2607.15021",
        "points": [(R(1, 6), 0), (R(3, 4), 0), (0, R(1, 4)), (R(5, 6), R(1, 6)),
                   (0, R(5, 6)), (R(1, 4), R(3, 4)), (R(1, 3), R(1, 3))],
    },
}


def floor30(expr):
    """30-decimal literal truncated toward zero (feasibility-preserving)."""
    v = mpmath.mpf(str(sp.N(expr, 45)))
    scaled = int(mpmath.floor(abs(v) * mpmath.mpf(10) ** 30))
    sign = "-" if v < 0 and scaled else ""
    if scaled == 0:
        return "0"
    ip, fp = divmod(scaled, 10 ** 30)
    s = f"{sign}{ip}.{fp:030d}".rstrip("0").rstrip(".")
    return s or "0"


def main():
    sys.path.insert(0, str(ROOT))
    from build.vendor.verify_exact import verify
    from fractions import Fraction

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "ATTRIBUTION.md").write_text(
        "# Attribution\n\nExact configurations transcribed from the papers\n"
        "arXiv:2603.11107 (square n=5..12, 16) and arXiv:2607.15021\n"
        "(triangle n=5..7) by N. Sudermann-Merx, including the previously\n"
        "unpublished exact forms of Comellas-Yebra (n=10, 12), Goldberg\n"
        "(n=11) and Beyleveld (n=16). Emitted as 30-decimal truncated\n"
        "literals by scripts/import_papers.py and re-verified exactly.\n")

    for (variant, n), cfg in sorted(CONFIGS.items()):
        lits = [(floor30(x), floor30(y)) for x, y in cfg["points"]]
        pts = [(Fraction(a), Fraction(b)) for a, b in lits]
        res = verify(variant, pts)
        assert res["feasible"], (variant, n, res["violations"][:2])
        d = OUT / f"{variant}-n{n:02d}"
        d.mkdir(exist_ok=True)
        lines = [f"# Heilbronn {variant} n={n} — exact configuration from {cfg['ref']}"]
        if cfg.get("note"):
            lines.append(f"# {cfg['note']}")
        lines.append(f"# exact value of these literals: {res['value']}")
        lines += [f"{a}\t{b}" for a, b in lits]
        (d / "coordinates.txt").write_text("\n".join(lines) + "\n")
        (d / "meta.json").write_text(json.dumps({
            "ref": cfg["ref"], "note": cfg.get("note"),
            "value_fraction": res["value_fraction"],
        }, indent=1) + "\n")
        print(f"{variant}/{n}: {res['value'][:20]}…  ok")


if __name__ == "__main__":
    main()
