"""Directory-name rules of the submission checker (n up to 100, per-variant caps)."""

import pathlib
import sys

import pytest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import check_submission  # noqa: E402

MISSING = "`coordinates.txt` is missing"


def first_problem(name):
    res = check_submission.check_dir(pathlib.Path("/nonexistent") / name)
    return res["problems"][0]


@pytest.mark.parametrize("name", ["square-n03", "square-n37", "square-n99",
                                  "square-n100", "triangle-n37", "triangle-n100",
                                  "convex-n40", "convex-n100"])
def test_names_accepted(name):
    # A good name gets as far as looking for the coordinates.
    assert first_problem(name) == MISSING


@pytest.mark.parametrize("name", ["square-n7", "square-n007", "square-n02",
                                  "square-n101", "triangle-n101", "convex-n101",
                                  "hexagon-n10"])
def test_names_refused(name):
    assert first_problem(name) != MISSING
