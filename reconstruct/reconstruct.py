#!/usr/bin/env python3
"""Reconstruct configurations whose coordinates were never published.

For each target (variant, n) with a Friedman entry but no public coordinates,
search numerically — symmetry-restricted first when the page names a symmetry,
plus free multistart — polish, tighten to ~1e-15, truncate to 15 decimals,
repair feasibility exactly, and accept only if the exact value of the
truncated literals falls in the published value's window (or matches a known
exact value). Accepted results are written to data/sources/reconstructed/
and picked up by the next ingest.

A run that *exceeds* the published window found something better than the
published record: that is not a reconstruction — it is reported and NOT
written, so it can go through the normal claims workflow instead.

Usage:
    python3 reconstruct/reconstruct.py [--targets triangle/8 convex/16 ...]
                                       [--budget SECONDS_PER_TARGET]
"""

import argparse
import datetime
import json
import pathlib
import sys
import time
from fractions import Fraction

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "build" / "vendor"))

import heil          # noqa: E402  (vendored search toolkit)
import refine        # noqa: E402
import sym           # noqa: E402

from build.ingest import latest_snapshot, published_window, fmt15  # noqa: E402
from build.derive import detect_symmetry, friedman_label           # noqa: E402
from build.vendor.verify_exact import verify                       # noqa: E402

OUT = ROOT / "data" / "sources" / "reconstructed"

# Values known in closed form: reconstruction must reproduce these.
EXACT = {
    ("triangle", 5): 3 - 2 * 2 ** 0.5,
    ("triangle", 6): 1 / 8,
    ("triangle", 7): 7 / 72,
    ("triangle", 9): 43 / 784,
    ("convex", 7): 1 / 9,
    ("convex", 11): 2 / 47,
    ("convex", 12): 2 / 51,
}

# Symmetry-restricted searches worth trying, from Friedman's labels.
SYM_STRATEGY = {
    "triangle": {"120": "rot3", "Completely": "rot3"},
}


def sym_group_for(variant, n, label):
    if not label:
        return None
    if variant == "triangle" and ("120°" in label or "Completely" in label):
        return "rot3"
    if variant == "square":
        if "180°" in label:
            return "rot2"
        if "4-fold" in label or "Completely" in label:
            return "rot4"
    if variant == "convex":
        for k in range(8, 1, -1):
            if f"{k}-fold" in label:
                return f"rot{k}"
    return None


def truncate_repair(X, variant):
    """15-decimal truncation with exact feasibility repair."""
    pts = []
    step = Fraction(1, 10 ** 15)
    for x, y in X:
        fx = Fraction(round(float(x) * 10 ** 15)) / 10 ** 15
        fy = Fraction(round(float(y) * 10 ** 15)) / 10 ** 15
        if variant in ("square", "triangle"):
            fx = min(max(fx, Fraction(0)), Fraction(1))
            fy = min(max(fy, Fraction(0)), Fraction(1))
        if variant == "triangle":
            while fx + fy > 1:
                if fx >= fy:
                    fx -= step
                else:
                    fy -= step
        pts.append((fx, fy))
    return pts


def png_dots(path, n):
    """Digitizer for the newer anti-aliased record PNGs: dots are filled
    black disks (interior distance ≥ ~2 px), triangle edges are ~1 px black
    ridges, so the distance transform separates them where blob erosion
    can't. Sweeps thresholds until exactly n components appear."""
    from PIL import Image
    from scipy import ndimage
    a = np.array(Image.open(path).convert("RGB")).astype(int)
    s = a.sum(axis=2)
    cands = []  # (score, pts, dark)
    for darkthr in (200, 300, 450):
        dark = s < darkthr
        dist = ndimage.distance_transform_edt(dark)
        for t in (3.0, 2.6, 2.2, 2.0, 1.8, 1.6):
            lab, nlab = ndimage.label(dist >= t)
            comps = []
            for i in range(1, nlab + 1):
                mask = lab == i
                ys, xs = np.where(mask)
                if len(ys) < 2:
                    continue
                comps.append((float(dist[mask].max()), len(ys),
                              xs.mean(), ys.mean()))
            if len(comps) < n:
                continue
            # Dots are the roundest, deepest components; edge junk ranks low.
            comps.sort(key=lambda c: (-c[0], -c[1]))
            kept = comps[:n]
            # Score: how cleanly the cut separates dots from junk (gap between
            # the weakest kept peak and the strongest dropped one).
            gap = kept[-1][0] - (comps[n][0] if len(comps) > n else 0.0)
            exact_bonus = 10.0 if len(comps) == n else 0.0
            pts = np.array([(c[2], c[3]) for c in kept])
            cands.append((exact_bonus + gap, pts, dark))
    if not cands:
        return []
    # Distinct candidates only (different threshold combos often coincide).
    cands.sort(key=lambda c: -c[0])
    out = []
    for score, pts, dark in cands:
        key = np.sort(pts.round(1).view("f8").reshape(-1))
        if any(len(k) == len(key) and np.allclose(k, key, atol=1.5) for k, _ in out):
            continue
        out.append((key, (pts, dark)))
        if len(out) >= 4:
            break
    return [pd for _, pd in out]


def image_seeds(variant, n, image_dir):
    """Digitize Friedman's published figure images into seed configurations
    (vendored gifseed logic; images are used only as optimization seeds and
    never republished)."""
    import glob
    import gifseed
    kind = {"triangle": "ht", "convex": "hc", "square": "hb"}[variant]
    seeds = []
    for path in sorted(glob.glob(str(pathlib.Path(image_dir) / f"{kind}{n}*.*"))):
        name = pathlib.Path(path).name
        try:
            # Gather candidate digitizations: the exact-count GIF-era blob
            # extractors first, then the distance-transform variants.
            cands = []
            if variant == "convex":
                pts = gifseed.convex_pts(path, n)
                if len(pts) == n:
                    cands.append((np.array(pts, float), None))
            else:
                pts, dark = gifseed.blobs(path)
                if len(pts) == n:
                    cands.append((np.array(pts, float), dark))
            cands.extend(png_dots(path, n))
            if not cands:
                print(f"  {name}: digitization failed — skip")
                continue
            for ci, (pts, dark) in enumerate(cands):
                suffix = f"#{ci}" if len(cands) > 1 else ""
                P = np.array(pts, float)
                if variant == "convex":
                    seeds.append((name + suffix, P))
                    continue
                if dark is None:
                    continue
                x0, x1, y0, y1 = gifseed.frame(dark)
                P[:, 0] = (P[:, 0] - x0) / (x1 - x0)
                P[:, 1] = (y1 - P[:, 1]) / (y1 - y0)
                if variant == "triangle":
                    V = np.array([[0.0, 0.0], [1.0, 0.0], [0.5, 1.0]])
                    W = np.array([[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
                    M = np.linalg.lstsq(np.hstack([V, np.ones((3, 1))]), W, rcond=None)[0]
                    P = np.hstack([P, np.ones((len(P), 1))]) @ M
                    P = np.clip(P, 0, None)
                    s = P.sum(axis=1)
                    P[s > 1] /= s[s > 1, None]
                seeds.append((name + suffix, P))
        except Exception as exc:
            print(f"  {name}: digitization failed: {exc}")
    return seeds


def reconstruct_one(variant, n, entry, budget, seed=0, image_dir=None,
                    beat_value=None):
    """beat_value: when set (BEHIND rows — re-polishing someone else's record
    figure), acceptance means beating our current coordinates; exceeding the
    truncated published value is the expected good outcome, not a refusal."""
    label = entry["symmetry"]
    window = published_window(entry)
    exact = EXACT.get((variant, n))

    best_v, best_X = -1.0, None

    if image_dir:
        for name, P in image_seeds(variant, n, image_dir):
            try:
                X, v = heil.polish(P, variant)
            except Exception as exc:
                print(f"  {name}: polish failed: {exc}")
                continue
            print(f"  {name}: polished to {v:.10f}")
            if v > best_v:
                best_v, best_X = v, X.copy()
    else:
        gname = sym_group_for(variant, n, label)
        if gname:
            try:
                v, X = sym.search_sym(variant, n, gname, seconds=budget * 0.5, seed=seed)
                if X is not None and v > best_v:
                    best_v, best_X = v, X
            except Exception as exc:
                print(f"  sym search failed: {exc}")

        rng = np.random.default_rng(seed + 1)
        t_end = time.time() + budget * 0.5
        while time.time() < t_end:
            X0 = heil.random_config(n, variant, rng,
                                    boundary_bias=float(rng.choice([0.0, 0.4])))
            try:
                X, v = heil.polish(X0, variant)
            except Exception:
                continue
            if v > best_v:
                best_v, best_X = v, X.copy()

    if best_X is None:
        return None, "no feasible result"

    best_X, best_v = refine.tighten(best_X, variant)
    pts = truncate_repair(best_X, variant)
    res = verify(variant, pts)
    v = res["_value"]

    if not res["feasible"]:
        return None, f"infeasible after truncation: {res['violations'][:2]}"
    if beat_value is not None:
        if v <= beat_value:
            return None, (f"does not beat current coordinates "
                          f"(got {float(v):.12f}, have {float(beat_value):.12f})")
    elif exact is not None:
        rel = abs(float(v) / exact - 1)
        if rel > 1e-9:
            return None, f"missed exact value {exact:.12f} by rel {rel:.2e} (got {float(v):.12f})"
    elif window is not None:
        lo, hi = window
        if v < lo:
            return None, f"below published window (got {float(v):.10f}, want ≥ {float(lo):.10f})"
        if v >= hi:
            return None, (f"EXCEEDS published window ({float(v):.12f} ≥ {float(hi):.10f}) — "
                          f"potential new record, route through the claims workflow")

    det = detect_symmetry(variant, [(float(a), float(b)) for a, b in pts])
    det_label = friedman_label(det, variant)
    sym_match = _labels_compatible(det_label, label)
    return {
        "points": pts, "verify": res, "value": v,
        "detected_symmetry": det, "detected_label": det_label,
        "sym_match": sym_match,
    }, None


def _labels_compatible(detected, published):
    if not published:
        return True
    d, p = detected.lower().rstrip("."), published.lower().rstrip(".")
    if d == p:
        return True
    pairs = [
        ("mirror", "horizontally"), ("mirror", "vertically"),
        ("mirror", "symmetric about"), ("mirror", "reflect"),
        ("dihedral", "dihedral"), ("120", "120"), ("180", "180"),
        ("dihedral", "completely"), ("2-fold dihedral", "2-fold symmetry"),
        ("3-fold dihedral", "3-fold symmetry"),
        ("not symmetric", "no symmetry"),
    ]
    return any(a in d and b in p for a, b in pairs)


def write_out(variant, n, entry, result, budget_note, behind=False):
    tag = f"{variant}-n{n:02d}"
    d = OUT / tag
    d.mkdir(parents=True, exist_ok=True)
    res = result["verify"]
    if behind:
        blurb = [
            "# Re-polished from the published record figure: the record holder's",
            "# arrangement (see credits above) with re-derived coordinates.",
        ]
    else:
        blurb = [
            "# Reconstructed by numerical optimization seeded from the published",
            "# value and symmetry; matches both, but is not claimed to be the",
            "# original author's exact arrangement.",
        ]
    lines = [
        f"# Heilbronn {variant} n={n} — RECONSTRUCTED configuration",
        f"# exact value of these literals: {res['value']}",
        f"# published entry: {entry['value_text']} ({'; '.join(entry['credits'])})",
        *blurb,
    ]
    for x, y in result["points"]:
        lines.append(f"{fmt15(x)}\t{fmt15(y)}")
    (d / "coordinates.txt").write_text("\n".join(lines) + "\n")
    out = {k: v for k, v in res.items() if k != "_value"}
    (d / "verify_output.json").write_text(json.dumps({"a": out}, indent=1) + "\n")
    (d / "provenance.json").write_text(json.dumps({
        "ref": "heilbronn-site reconstruct/reconstruct.py",
        "note": ((f"re-polished from the published record figure — the record "
                  f"holder's arrangement with re-derived coordinates") if behind else
                 (f"reconstructed by local optimization; matches published value "
                  f"{entry['decimal']}{'+' if entry['lower_bound'] else ''}"
                  + (f" and symmetry ({result['detected_label']})" if result["sym_match"] else ""))),
        "date": datetime.date.today().isoformat(),
        "method": budget_note,
        "detected_symmetry": result["detected_label"],
        "published_symmetry": entry["symmetry"],
        "symmetry_match": result["sym_match"],
    }, indent=1) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets", nargs="*",
                    help="variant/n pairs, e.g. triangle/8; default: all canonical gaps")
    ap.add_argument("--budget", type=float, default=30.0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--images", metavar="DIR",
                    help="seed from Friedman figure images in DIR instead of searching")
    ap.add_argument("--behind", action="store_true",
                    help="target rows where the published record beats our coordinates; "
                         "accept anything that improves on them")
    args = ap.parse_args()

    snap = latest_snapshot()
    beat_values = {}
    if args.targets:
        targets = [tuple(t.split("/")) for t in args.targets]
        targets = [(v, int(n)) for v, n in targets]
    elif args.behind:
        targets = []
        for v in ("square", "triangle", "convex"):
            for n in range(3, 36):
                p = ROOT / "data" / "canonical" / v / f"n{n:02d}.json"
                if not p.exists():
                    continue
                doc = json.loads(p.read_text())
                if doc.get("page_relation") == "BEHIND":
                    targets.append((v, n))
                    beat_values[(v, n)] = Fraction(doc["value"]["fraction"])
    else:
        targets = []
        for v in ("square", "triangle", "convex"):
            for n in range(3, 36):
                p = ROOT / "data" / "canonical" / v / f"n{n:02d}.json"
                if p.exists() and json.loads(p.read_text())["points"] is None:
                    targets.append((v, n))

    print(f"{len(targets)} target(s), budget {args.budget}s each")
    failures = []
    for v, n in targets:
        entry = snap["variants"][v].get(str(n))
        if entry is None:
            print(f"{v}/{n}: no Friedman entry, skipped")
            continue
        t0 = time.time()
        result, err = reconstruct_one(v, n, entry, args.budget, seed=args.seed,
                                      image_dir=args.images,
                                      beat_value=beat_values.get((v, n)))
        dt = time.time() - t0
        if err:
            print(f"{v}/{n}: FAILED in {dt:.0f}s — {err}")
            failures.append((v, n, err))
            continue
        write_out(v, n, entry, result,
                  f"sym+multistart polish/tighten, {args.budget:.0f}s budget, seed {args.seed}",
                  behind=(v, n) in beat_values)
        match = "sym ok" if result["sym_match"] else \
            f"SYM MISMATCH (got {result['detected_label']!r}, page {entry['symmetry']!r})"
        print(f"{v}/{n}: ok in {dt:.0f}s — value {float(result['value']):.12f}, {match}")
    if failures:
        print(f"\n{len(failures)} failure(s):")
        for v, n, err in failures:
            print(f"  {v}/{n}: {err}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
