"""Ingest invariants: frame conversion and canonical output sanity."""

import json
import pathlib
from fractions import Fraction

from build.ingest import eq_to_right_frame, published_window
from build.vendor.verify_exact import verify, parse_points_text

ROOT = pathlib.Path(__file__).resolve().parent.parent


def test_eq_to_right_frame_preserves_value_and_feasibility():
    src = ROOT / "data" / "sources" / "alphaevolve" / "triangle_n11.txt"
    pts_eq = [[str(x), str(y)] for x, y in parse_points_text(src.read_text())]
    pts_right = eq_to_right_frame(pts_eq)
    pts = [(Fraction(x), Fraction(y)) for x, y in pts_right]
    res = verify("triangle", pts)
    assert res["feasible"], res["violations"]
    # Published AlphaEvolve value: 0.036529889880030156 (normalized).
    assert abs(res["_value"] - Fraction("0.036529889880030156")) < Fraction(1, 10**13)


def test_published_window_accepts_rounded_and_truncated():
    entry = {"decimal": "0.08386", "lower_bound": True}
    low, high = published_window(entry)
    proven = Fraction("0.08385900900751340663796674354476")
    assert low <= proven < high


def test_canonical_docs_exist_and_verify_fields_match():
    count = 0
    for f in (ROOT / "data" / "canonical").glob("*/n*.json"):
        doc = json.loads(f.read_text())
        assert doc["schema_version"] == 1
        if doc["points"] is not None:
            assert doc["verify"]["feasible"] is True
            assert doc["value"]["fraction"] == doc["verify"]["value_fraction"]
            count += 1
    assert count >= 70  # 99 rows minus the gaps
