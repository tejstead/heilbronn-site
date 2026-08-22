"""The five exact families: generation succeeds, every sample verifies
exactly (generate() raises otherwise), and sample 0 is the stored member."""

import json
import pathlib

import pytest

from build.families import FAMILY_BUILDERS, generate

ROOT = pathlib.Path(__file__).resolve().parent.parent


@pytest.mark.parametrize("variant,n", sorted(FAMILY_BUILDERS))
def test_family_generates_and_verifies(variant, n):
    doc = json.loads(
        (ROOT / "data" / "canonical" / variant / f"n{n:02d}.json").read_text())
    fam = generate(variant, n, doc)   # raises if any sample fails exact check
    assert len(fam["samples"]) >= 17
    assert fam["moving"]
    # sample 0 is the stored member (30-decimal literal vs stored literal)
    from fractions import Fraction
    for (sx, sy), (px, py) in zip(fam["samples"][0], doc["points"]):
        assert abs(Fraction(sx) - Fraction(px)) < Fraction(1, 10**20)
        assert abs(Fraction(sy) - Fraction(py)) < Fraction(1, 10**20)
    # only the declared moving points move
    still = [i for i in range(len(doc["points"])) if i not in fam["moving"]]
    for s in fam["samples"][1:]:
        for i in still:
            assert s[i] == fam["samples"][0][i]


def test_no_family_for_other_configs():
    doc = json.loads(
        (ROOT / "data" / "canonical" / "square" / "n07.json").read_text())
    assert generate("square", 7, doc) is None
