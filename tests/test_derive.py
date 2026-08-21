"""Symmetry detection and congruence grouping on known configurations."""

import json
import pathlib
import sys

from build.derive import derive, friedman_label

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "data" / "sources" / "exact"))
import constructions  # noqa: E402


def _derive_exact(variant, n):
    c = constructions.get(variant, n)
    return derive(variant, c["points"])


def test_pentagon_is_d5():
    d = _derive_exact("convex", 5)
    assert d["symmetry"]["group"] == "D5"
    assert friedman_label(d["symmetry"], "convex") == "5-fold dihedral symmetry"


def test_hexagon_is_d6():
    d = _derive_exact("convex", 6)
    assert d["symmetry"]["group"] == "D6"


def test_square4_is_d4_single_class():
    doc = json.loads((ROOT / "data" / "canonical" / "square" / "n04.json").read_text())
    d = derive("square", doc["points"])
    assert d["symmetry"]["group"] == "D4"
    assert len(d["classes"]) == 1 and len(d["classes"][0]["triangles"]) == 4


def test_convex18_d6_classes():
    doc = json.loads((ROOT / "data" / "canonical" / "convex" / "n18.json").read_text())
    d = derive("convex", doc["points"])
    assert d["symmetry"]["group"] == "D6"
    # 36 minimal triangles in 3 congruence classes of 12 (the D6 orbits).
    assert sorted(len(c["triangles"]) for c in d["classes"]) == [12, 12, 12]


def test_triangle_frame_c3_detection():
    # The equilateral-frame D3 detection must see 120° symmetry through the
    # right-frame coordinates: use the reconstructed triangle n=7 if present.
    p = ROOT / "data" / "sources" / "reconstructed" / "triangle-n07"
    if not p.exists():
        return  # reconstruction not run yet
    from build.vendor.verify_exact import parse_points_text
    pts = [[str(x), str(y)] for x, y in parse_points_text((p / "coordinates.txt").read_text())]
    d = derive("triangle", pts)
    assert d["symmetry"]["rotation"] and d["symmetry"]["rotation"]["order"] == 3
