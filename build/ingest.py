"""Ingest: unify all vendored sources into canonical per-configuration JSONs.

For each (variant, n) the candidates from every source are exactly verified
(vendored verifier, exact rationals) and the best value wins. The result is
written to data/canonical/{variant}/nNN.json and committed, so the rest of
the pipeline — and reviewers — see one schema and reviewable diffs.

Also prints the coverage audit: per row, the chosen source and how our exact
value relates to Friedman's published (truncated) value.
"""

import json
import pathlib
import re
import sys
from fractions import Fraction

from .vendor.verify_exact import parse_points_text, verify, fraction_to_30sig

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCES = ROOT / "data" / "sources"
CURATED = ROOT / "data" / "curated"
CANONICAL = ROOT / "data" / "canonical"

VARIANTS = ("square", "triangle", "convex")
NS = range(3, 36)

FRAMES = {"square": "unit-square", "triangle": "right", "convex": "free"}

MONTHS = ("January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December")
CREDIT_RE = re.compile(
    r"^(Found(?: and proved)? by|Proved(?: optimal)? by)\s+(.+?)"
    r"(?:,\s*| in )((?:%s)\s+\d{4}|\d{4})\.?$" % "|".join(MONTHS))


def latest_snapshot():
    snaps = sorted((SOURCES / "friedman").glob("parsed-*.json"))
    if not snaps:
        sys.exit("no Friedman snapshot — run scripts/friedman_sync.py first")
    return json.loads(snaps[-1].read_text())


def load_curated(name):
    p = CURATED / name
    return json.loads(p.read_text()) if p.exists() else {}


def frac_to_dec(fr):
    """Exact decimal string for a Fraction with 10-smooth denominator (all
    source coordinates are decimal literals, so this always applies)."""
    from decimal import Decimal
    d = Decimal(fr.numerator) / Decimal(fr.denominator)
    s = format(d.normalize(), "f")
    return s


def points_to_strings(points):
    return [[frac_to_dec(x), frac_to_dec(y)] for x, y in points]


def eq_to_right_frame(points_str):
    """Exact-decimal conversion from the equilateral frame (0,0),(1,0),
    (1/2,sqrt(3)/2) to the right frame (0,0),(1,0),(0,1):
    x' = x - y/sqrt(3),  y' = 2y/sqrt(3).

    Computed at 50 dps, rounded to 15 decimals, then nudged (in exact
    rationals) back inside the domain if rounding pushed a boundary point
    out. The normalized value is affine-invariant, so this loses ~1e-15 of
    the value at most.
    """
    import mpmath
    mpmath.mp.dps = 50
    s3 = mpmath.sqrt(3)
    out = []
    for xs, ys in points_str:
        x, y = mpmath.mpf(xs), mpmath.mpf(ys)
        xr = x - y / s3
        yr = 2 * y / s3
        out.append([mpmath.nstr(xr, 17, strip_zeros=False),
                    mpmath.nstr(yr, 17, strip_zeros=False)])
    # Round to 15 decimals and repair feasibility exactly.
    step = Fraction(1, 10 ** 15)
    fixed = []
    for xs, ys in out:
        x = round(Fraction(xs), 15) if "." in xs else Fraction(xs)
        y = round(Fraction(ys), 15) if "." in ys else Fraction(ys)
        x = max(x, Fraction(0))
        y = max(y, Fraction(0))
        while x + y > 1:
            if x >= y:
                x -= step
            else:
                y -= step
        fixed.append([fmt15(x), fmt15(y)])
    return fixed


def fmt15(fr):
    """Format an exact multiple of 1e-15 as a fixed 15-decimal string."""
    scaled = fr * 10 ** 15
    assert scaled.denominator == 1
    sign = "-" if scaled < 0 else ""
    v = abs(int(scaled))
    return f"{sign}{v // 10**15}.{v % 10**15:015d}"


def _external_exact_coeffs(path):
    """Contributor-supplied minimal polynomial (see CONTRIBUTING.md): integer
    coefficients, constant first, in exact.json. Returned as list[int] or
    None. Deliberately data-only — the sympy expression string is built here
    from validated integers, never parsed from contributor text."""
    if not path.exists():
        return None
    data = json.loads(path.read_text())
    raw = data.get("minimal_polynomial")
    if not isinstance(raw, list) or not 2 <= len(raw) <= 65:
        return None
    coeffs = []
    for c in raw:
        if isinstance(c, str) and c.lstrip("-").isdigit():
            c = int(c)
        if not isinstance(c, int) or isinstance(c, bool) or c.bit_length() > 4096:
            return None
        coeffs.append(c)
    return coeffs if coeffs[-1] != 0 else None


def coeffs_to_poly(coeffs):
    terms = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        if i == 0:
            terms.append(str(c))
        elif i == 1:
            terms.append(f"{c}*x")
        else:
            terms.append(f"{c}*x**{i}")
    return " + ".join(terms).replace("+ -", "- ")


def gather_candidates(variant, n):
    """Yield candidate dicts: {points (list of [str,str]), kind, ref, note}."""
    tag = f"{variant}-n{n:02d}"

    d = SOURCES / "tejsteadqc" / tag
    if d.exists():
        meta = json.loads((d / "meta.json").read_text())
        pts = parse_points_text((d / "coordinates.txt").read_text())
        yield {
            "points": points_to_strings(pts),
            "kind": "author",
            "ref": f"TejSteadQC/heilbronn-configurations {meta['origin']}",
            "note": None,
            "verify_upstream": json.loads((d / "verify_output.json").read_text()),
        }

    ae = SOURCES / "alphaevolve" / f"{variant}_n{n}.txt"
    if ae.exists():
        text = ae.read_text()
        pts = points_to_strings(parse_points_text(text))
        if variant == "triangle":  # equilateral frame upstream
            pts = eq_to_right_frame(pts)
        yield {
            "points": pts,
            "kind": "alphaevolve",
            "ref": "google-deepmind/alphaevolve_results (arXiv:2506.13131)",
            "note": "converted from the equilateral frame" if variant == "triangle" else None,
        }

    if variant == "square":
        sp = SOURCES / "spiralulam" / f"config_n{n:02d}.json"
        if sp.exists():
            data = json.loads(sp.read_text())
            yield {
                "points": [[repr(float(x)), repr(float(y))] for x, y in data["points"]],
                "kind": "spiralulam",
                "ref": f"spiralulam/heilbronn config_n{n:02d}.json",
                "note": data.get("source"),
                "delta_exact": data.get("delta_exact"),
            }

    ext = SOURCES / "external" / tag
    if ext.exists():
        meta = json.loads((ext / "meta.json").read_text())
        pts = parse_points_text((ext / "coordinates.txt").read_text())
        yield {
            "points": points_to_strings(pts),
            "kind": "external",
            "ref": meta["ref"],
            "note": meta.get("note"),
            "credit": meta.get("credit"),
            "exact_coeffs": _external_exact_coeffs(ext / "exact.json"),
        }

    pap = SOURCES / "papers" / tag
    if pap.exists():
        meta = json.loads((pap / "meta.json").read_text())
        pts = parse_points_text((pap / "coordinates.txt").read_text())
        yield {
            "points": points_to_strings(pts),
            "kind": "paper",
            "ref": meta["ref"],
            "note": meta.get("note"),
        }

    rec = SOURCES / "reconstructed" / tag
    if rec.exists() and (rec / "provenance.json").exists():
        prov = json.loads((rec / "provenance.json").read_text())
        pts = parse_points_text((rec / "coordinates.txt").read_text())
        yield {
            "points": points_to_strings(pts),
            "kind": "reconstructed",
            "ref": prov.get("ref", "local reconstruction"),
            "note": prov.get("note"),
            "basis": prov.get("basis"),
        }

    exact_mod = SOURCES / "exact" / "constructions.py"
    if exact_mod.exists():
        sys.path.insert(0, str(exact_mod.parent))
        try:
            import constructions
            c = constructions.get(variant, n)
        finally:
            sys.path.pop(0)
        if c is not None:
            yield {
                "points": c["points"],
                "kind": "exact-construction",
                "ref": c.get("ref", "data/sources/exact/constructions.py"),
                "note": c.get("note"),
            }


def parse_credits(entry):
    """Split Friedman's credit sentences into found/proved records."""
    found = proved = None
    trivial = False
    for s in entry["credits"]:
        if s.lower().startswith("trivial"):
            trivial = True
            continue
        m = CREDIT_RE.match(s)
        rec = ({"name": m.group(2), "date": m.group(3)} if m
               else {"name": s, "date": None})
        verb = (m.group(1) if m else s).lower()
        if verb.startswith("found and proved"):
            found = proved = rec
        elif verb.startswith("found"):
            found = rec
        else:
            proved = rec
    return trivial, found, proved


def published_window(entry):
    """Return (low, high) exact bounds implied by the published value, or
    None if unparseable. Friedman's "+" entries are usually truncations
    (value in [d, d+ulp)) but sometimes roundings (e.g. square n=7: proven
    optimum .0838590… shown as ".08386+"), so accept the union of both:
    [d - ulp/2, d + ulp). Values below that are genuinely BEHIND, at or
    above the top genuinely BEATS."""
    d = entry["decimal"]
    if d is None:
        return None
    frac = Fraction(d)
    decimals = len(d.split(".")[1]) if "." in d else 0
    ulp = Fraction(1, 10 ** decimals) if decimals else Fraction(1)
    if entry["lower_bound"]:
        return (frac - ulp / 2, frac + ulp)
    return (frac - ulp / 2, frac + ulp / 2)


def ingest():
    snapshot = latest_snapshot()
    overrides = load_curated("overrides.json")
    changelog = load_curated("changelog.json")
    refdata = load_curated("references.json")
    refs_by_config = refdata.get("by_config", {})
    bib = refdata.get("bib", {})
    proofs = refdata.get("proofs", {})

    def proof_for(key):
        rid = proofs.get(key)
        if not rid:
            return None
        entry = bib.get(rid, {})
        return {"id": rid, "title": entry.get("title"), "url": entry.get("url")}

    audit = []
    for variant in VARIANTS:
        outdir = CANONICAL / variant
        outdir.mkdir(parents=True, exist_ok=True)
        for n in NS:
            key = f"{variant}/{n}"
            entry = snapshot["variants"][variant].get(str(n))
            best = None
            for cand in gather_candidates(variant, n):
                pts = [(Fraction(x), Fraction(y)) for x, y in cand["points"]]
                res = verify(variant, pts)
                if not res["feasible"]:
                    print(f"  WARN {key}: {cand['kind']} candidate infeasible, skipped",
                          file=sys.stderr)
                    continue
                if best is None or res["_value"] > best[1]["_value"]:
                    best = (cand, res)

            window = published_window(entry) if entry else None
            if best is None:
                rel = "GAP"
                audit.append((key, rel, "-", entry["decimal"] if entry else "-"))
                # Still emit a coordinate-less canonical row so pages render.
                doc = canonical_doc(variant, n, entry, None, None, rel,
                                    overrides.get(key), changelog.get(key),
                                    refs_by_config.get(key), proof_for(key))
            else:
                cand, res = best
                value = res["_value"]
                if window is None:
                    rel = "OK"
                elif value < window[0]:
                    rel = "BEHIND"
                elif value >= window[1]:
                    rel = "BEATS"
                else:
                    rel = "OK"
                audit.append((key, rel, cand["kind"],
                              fraction_to_30sig(value)[:12]))
                doc = canonical_doc(variant, n, entry, cand, res, rel,
                                    overrides.get(key), changelog.get(key),
                                    refs_by_config.get(key), proof_for(key))
            path = outdir / f"n{n:02d}.json"
            path.write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")

    print(f"{'row':<14}{'rel':<8}{'source':<16}value")
    for key, rel, kind, val in audit:
        if rel != "OK":
            print(f"{key:<14}{rel:<8}{kind:<16}{val}")
    counts = {}
    for _, rel, _, _ in audit:
        counts[rel] = counts.get(rel, 0) + 1
    print("audit:", ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    return audit


def canonical_doc(variant, n, entry, cand, res, page_relation, override, changelog,
                  refs, proof=None):
    trivial, found, proved = parse_credits(entry) if entry else (False, None, None)
    # Status describes the VALUE only; coordinate provenance (including
    # reconstruction) is a separate fact carried by coordinates_source and
    # surfaced as its own tag, never as a competing status.
    # Trivial cases are proven (the credit keeps the trivial flag, and the
    # page comments "Trivial configuration." instead of a separate badge).
    if trivial or proved:
        status = "proven"
    else:
        status = "record"

    doc = {
        "schema_version": 1,
        "variant": variant,
        "n": n,
        "frame": FRAMES[variant],
        "points": cand["points"] if cand else None,
        "value": {
            "decimal": res["value"] if res else None,
            "fraction": res["value_fraction"] if res else None,
            "published": entry["value_text"] if entry else None,
            "published_decimal": entry["decimal"] if entry else None,
            "published_lower_bound": entry["lower_bound"] if entry else None,
            "exact_text": entry["exact_text"] if entry else None,
            "exact_sympy": None,
            "minimal_polynomial": None,
        },
        "status": status,
        # How our exact value relates to Friedman's published value:
        # OK (within its truncation window), BEATS (exceeds it — a pending
        # or unsubmitted improvement), BEHIND (someone holds a better record
        # without public coordinates), GAP (no coordinates at all).
        "page_relation": page_relation,
        "credit": {
            "found": found,
            "proved": proved,
            "trivial": trivial,
        },
        "proof": proof,
        "coordinates_source": ({
            "kind": cand["kind"],
            "ref": cand["ref"],
            "note": cand["note"],
            "basis": cand.get("basis"),
        } if cand else None),
        "coordinates_reconstructed": bool(cand and cand["kind"] == "reconstructed"),
        "symmetry": {"label": entry["symmetry"] if entry else None},
        "notes": entry["notes"] if entry else [],
        "changelog": changelog or [],
        "references": refs or [],
        "verify": res and {k: v for k, v in res.items() if k != "_value"},
    }
    # When an external submission's value beats the published record, the
    # find belongs to the submitter (meta.json credit), not to the holder of
    # the superseded page entry.
    if (cand and cand.get("kind") == "external" and cand.get("credit")
            and page_relation == "BEATS"):
        m = re.match(r"^(.+?),\s*((?:%s)\s+\d{4}|\d{4})$" % "|".join(MONTHS),
                     cand["credit"].strip())
        if m:
            doc["credit"]["found"] = {"name": m.group(1), "date": m.group(2)}
        else:
            doc["credit"]["found"] = {"name": cand["credit"].strip(), "date": None}

    if cand and cand.get("delta_exact") and not doc["value"]["exact_text"]:
        doc["value"]["exact_text"] = cand["delta_exact"]
    if override:
        deep_update(doc, override)
    # A minimal polynomial submitted alongside external coordinates applies
    # only when the curated overrides carry no exact form of their own —
    # curation always wins. finalize_exact then validates it against the
    # coordinates (45 digits, rel 1e-9) and drops it loudly on mismatch.
    if (cand and cand.get("exact_coeffs") and res is not None
            and not doc["value"].get("exact_sympy")
            and not doc["value"].get("exact_poly")):
        doc["value"]["exact_poly"] = {
            "poly": coeffs_to_poly(cand["exact_coeffs"]),
            "near": float(res["_value"]),
            "which": "root nearest the coordinate value",
            "note": "minimal polynomial submitted with the coordinates",
        }
    finalize_exact(doc, res)
    return doc


def finalize_exact(doc, res):
    """Evaluate a curated exact value (closed form and/or minimal polynomial)
    to 45 digits, and validate it against the exact value implied by the
    coordinates. A curated form that disagrees with the coordinates is a
    data error: it is dropped loudly rather than displayed."""
    val = doc["value"]
    if not (val.get("exact_sympy") or val.get("exact_poly")):
        return
    import mpmath
    import sympy
    mpmath.mp.dps = 60

    decs = {}
    if val.get("exact_sympy"):
        expr = sympy.sympify(val["exact_sympy"])
        decs["sympy"] = mpmath.mpf(str(sympy.N(expr, 55)))
    if val.get("exact_poly"):
        p = val["exact_poly"]
        poly = sympy.sympify(p["poly"])
        x = list(poly.free_symbols)[0]
        roots = sympy.Poly(poly, x).nroots(n=55, maxsteps=500)
        real = [sympy.re(r) for r in roots if abs(sympy.im(r)) < sympy.Float(10) ** -40]
        root = min(real, key=lambda r: abs(float(r) - p["near"]))
        decs["poly"] = mpmath.mpf(str(sympy.N(root, 55))) * p.get("scale", 1)

    vals = list(decs.values())
    if len(vals) == 2 and abs(vals[0] - vals[1]) > abs(vals[0]) * mpmath.mpf(10) ** -40:
        print(f"  WARN {doc['variant']}/{doc['n']}: exact_sympy and exact_poly disagree "
              f"({vals[0]} vs {vals[1]}) — dropping exact value", file=sys.stderr)
        val["exact_sympy"] = val["exact_poly"] = val.pop("exact_display", None) and None
        return
    exact = vals[0]

    if res is not None:
        coord = res["_value"]
        coord_mp = mpmath.mpf(coord.numerator) / mpmath.mpf(coord.denominator)
        rel = abs(coord_mp / exact - 1)
        if rel > mpmath.mpf(10) ** -9:
            print(f"  WARN {doc['variant']}/{doc['n']}: curated exact value "
                  f"{mpmath.nstr(exact, 15)} does not match coordinates "
                  f"({mpmath.nstr(coord_mp, 15)}, rel {mpmath.nstr(rel, 3)}) — dropped",
                  file=sys.stderr)
            for k in ("exact_sympy", "exact_poly", "exact_display"):
                val.pop(k, None)
            return

    val["exact_decimal"] = mpmath.nstr(exact, 45, strip_zeros=False)
    if val.get("exact_poly"):
        val["minimal_polynomial"] = val["exact_poly"]["poly"]

    # Presentation MathML, built from the curated display string so the
    # rendered form is exactly what a human would write — and re-evaluated
    # numerically so the pretty output is provably the same number.
    from .mathml import exact_to_mathml, poly_to_mathml
    if val.get("exact_display"):
        try:
            mml, parsed_value = exact_to_mathml(val["exact_display"])
            if abs(parsed_value / float(exact) - 1) > 1e-12:
                raise ValueError(f"display form evaluates to {parsed_value}, "
                                 f"exact is {mpmath.nstr(exact, 15)}")
            val["exact_mathml"] = mml
        except Exception as exc:
            print(f"  WARN {doc['variant']}/{doc['n']}: exact_display not "
                  f"renderable as MathML ({exc}) — falling back to text",
                  file=sys.stderr)
    if val.get("minimal_polynomial"):
        try:
            val["poly_mathml"] = poly_to_mathml(val["minimal_polynomial"])
        except Exception as exc:
            print(f"  WARN {doc['variant']}/{doc['n']}: polynomial not "
                  f"renderable as MathML ({exc})", file=sys.stderr)


def deep_update(doc, patch):
    for k, v in patch.items():
        if isinstance(v, dict) and isinstance(doc.get(k), dict):
            deep_update(doc[k], v)
        else:
            doc[k] = v


if __name__ == "__main__":
    ingest()
