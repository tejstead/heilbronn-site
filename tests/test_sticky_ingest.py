"""The committed canonical row competes as a candidate so a source-directory
overwrite (a submission merged after a better one landed in the same
directory) can never lower an entry."""

from build.ingest import sticky_candidate


def test_sticky_candidate_needs_coordinates():
    assert sticky_candidate(None) is None
    assert sticky_candidate({"points": None, "coordinates_source": {"kind": "external"}}) is None
    assert sticky_candidate({"points": [["0", "0"]], "coordinates_source": None}) is None


def test_sticky_candidate_carries_provenance_credit_and_exact_form():
    prev = {
        "points": [["0.1", "0.2"], ["0.3", "0.4"], ["0.5", "0.1"]],
        "coordinates_source": {"kind": "external", "ref": "someone/repo",
                               "note": "a note", "basis": None},
        "credit": {"found": {"name": "Ada Lovelace", "date": "August 2026"}},
        "value": {"exact_poly": {"poly": "2*x - 1", "near": 0.5,
                                 "which": "coordinate-matched", "note": "submitted"}},
    }
    cand = sticky_candidate(prev)
    assert cand["sticky"] is True
    assert cand["points"] == prev["points"]
    assert (cand["kind"], cand["ref"], cand["note"]) == ("external", "someone/repo", "a note")
    assert cand["credit"] == "Ada Lovelace, August 2026"
    assert cand["exact_poly_prev"]["poly"] == "2*x - 1"


def test_sticky_candidate_only_carries_coordinate_matched_polynomials():
    prev = {
        "points": [["0.1", "0.2"]],
        "coordinates_source": {"kind": "reconstructed", "ref": "r", "note": None, "basis": "figure"},
        "credit": {"found": {"name": "X", "date": None}},
        "value": {"exact_poly": {"poly": "x", "near": 0, "which": "unique real"}},
    }
    cand = sticky_candidate(prev)
    assert "credit" not in cand          # only external rows carry a submitter credit
    assert "exact_poly_prev" not in cand  # curated forms come back via overrides
