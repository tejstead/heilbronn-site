#!/usr/bin/env python3
"""Verify coordinate submissions (data/sources/external/<variant>-nNN/).

Used by the submission-verify GitHub workflow and runnable locally:

    python3 scripts/check_submission.py data/sources/external/square-n17
    python3 scripts/check_submission.py --base origin/main          # changed dirs
    make check-submission DIRS=data/sources/external/square-n17

For each submission directory it validates the file format, re-verifies the
configuration in exact rational arithmetic (same verifier the site uses), and
compares the value against the current canonical entry. It emits a Markdown
report (stdout, or --out FILE) and exits nonzero if any submission is invalid.
A submission that verifies but does not beat the current value is VALID — the
original author's coordinates for a reconstructed entry are welcome even when
they score lower — it is simply reported as such.

Stdlib only, so CI needs no installs. All parsing is bounded (file sizes,
digit counts, point counts) because this runs on untrusted pull requests.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from build.vendor.verify_exact import verify, fraction_to_30sig  # noqa: E402
from build.derive import detect_symmetry, friedman_label  # noqa: E402

SUBMISSION_ROOT = "data/sources/external"
DIR_RE = re.compile(r"^(square|triangle|convex)-n(\d{2})$")
NUM_RE = re.compile(r"^-?\d{1,6}(\.\d{1,200})?$")
MAX_COORD_BYTES = 64 * 1024
MAX_META_BYTES = 8 * 1024
MAX_POINTS = 100
META_KEYS = {"ref": (True, 300), "credit": (False, 300), "note": (False, 2000)}


def fail(problems, msg):
    problems.append(msg)


def parse_coordinates(path, problems):
    if path.stat().st_size > MAX_COORD_BYTES:
        fail(problems, f"`coordinates.txt` is larger than {MAX_COORD_BYTES // 1024} KB")
        return None
    points = []
    for lineno, raw in enumerate(path.read_text().splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2:
            fail(problems, f"line {lineno}: expected two whitespace-separated numbers")
            return None
        for p in parts:
            if not NUM_RE.match(p):
                fail(problems, f"line {lineno}: `{p[:40]}` is not a plain decimal "
                               "literal (≤6 integer digits, ≤200 decimals, no exponent)")
                return None
        points.append((Fraction(parts[0]), Fraction(parts[1])))
        if len(points) > MAX_POINTS:
            fail(problems, f"more than {MAX_POINTS} points")
            return None
    return points


def check_meta(path, problems, warnings):
    if not path.exists():
        fail(problems, "`meta.json` is missing")
        return None
    if path.stat().st_size > MAX_META_BYTES:
        fail(problems, f"`meta.json` is larger than {MAX_META_BYTES // 1024} KB")
        return None
    try:
        meta = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        fail(problems, f"`meta.json` is not valid JSON: {exc}")
        return None
    if not isinstance(meta, dict):
        fail(problems, "`meta.json` must be a JSON object")
        return None
    for key, (required, maxlen) in META_KEYS.items():
        if key not in meta:
            if required:
                fail(problems, f"`meta.json` is missing required key `{key}`")
            continue
        if not isinstance(meta[key], str) or not meta[key].strip():
            fail(problems, f"`meta.json` key `{key}` must be a non-empty string")
        elif len(meta[key]) > maxlen:
            fail(problems, f"`meta.json` key `{key}` exceeds {maxlen} characters")
    for key in meta:
        if key not in META_KEYS:
            warnings.append(f"`meta.json` has unknown key `{key}` (ignored by ingest)")
    return meta


def canonical_value(variant, n):
    path = ROOT / "data" / "canonical" / variant / f"n{n:02d}.json"
    if not path.exists():
        return None, None
    doc = json.loads(path.read_text())
    v = doc.get("verify") or {}
    frac = v.get("value_fraction")
    published = (doc.get("value") or {}).get("published")
    return (Fraction(frac) if frac else None), published


def check_dir(dirpath):
    """Returns a result dict for one submission directory."""
    res = {"dir": str(dirpath), "problems": [], "warnings": [], "ok": False}
    problems, warnings = res["problems"], res["warnings"]

    m = DIR_RE.match(dirpath.name)
    if not m:
        fail(problems, "directory name must be `<square|triangle|convex>-nNN`")
        return res
    variant, n = m.group(1), int(m.group(2))
    res["variant"], res["n"] = variant, n

    coord_path = dirpath / "coordinates.txt"
    if not coord_path.exists():
        fail(problems, "`coordinates.txt` is missing")
        return res
    points = parse_coordinates(coord_path, problems)
    check_meta(dirpath / "meta.json", problems, warnings)
    for extra in sorted(p.name for p in dirpath.iterdir()
                        if p.name not in ("coordinates.txt", "meta.json",
                                          "verify_output.json")):
        warnings.append(f"unexpected file `{extra}` (only coordinates.txt and "
                        "meta.json are read)")
    if points is None:
        return res

    if len(points) != n:
        fail(problems, f"directory says n={n} but coordinates.txt has {len(points)} points")
        return res
    if len(set(points)) != len(points):
        fail(problems, "duplicate points")
        return res

    v = verify(variant, points)
    res["verify"] = v
    if not v["feasible"]:
        for viol in v["violations"][:5]:
            fail(problems, f"infeasible: {viol}")
        return res

    value = v["_value"]
    res["value_30sig"] = fraction_to_30sig(value)
    sym = detect_symmetry(variant, [(float(x), float(y)) for x, y in points])
    res["symmetry"] = friedman_label(sym, variant) + f" ({sym['group']})" + \
        (" — approximate" if sym.get("approx") else "")
    cur, published = canonical_value(variant, n)
    res["published"] = published
    if cur is None:
        res["relation"] = "no canonical entry to compare against"
    elif value > cur:
        res["relation"] = f"IMPROVES the current value by {float((value - cur) / cur):.4%}"
    elif value == cur:
        res["relation"] = "exactly equals the current value"
    else:
        res["relation"] = (f"below the current value by {float((cur - value) / cur):.4%} "
                           "(still accepted if these are e.g. an original author's coordinates)")
    res["ok"] = not problems
    return res


def changed_submission_dirs(base):
    proc = subprocess.run(
        ["git", "diff", "--name-only", f"{base}...HEAD"],
        cwd=ROOT, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit(f"git diff against {base!r} failed: {proc.stderr.strip()}")
    out = proc.stdout
    dirs, out_of_scope = set(), []
    for line in out.splitlines():
        if line.startswith(SUBMISSION_ROOT + "/"):
            rel = pathlib.Path(line).parent
            if rel != pathlib.Path(SUBMISSION_ROOT):
                dirs.add(ROOT / pathlib.Path(*rel.parts[:4]))
        elif line:
            out_of_scope.append(line)
    return sorted(dirs), out_of_scope


def render(results, out_of_scope):
    lines = ["<!-- submission-verify -->", "## Coordinate submission check", ""]
    if not results:
        lines.append("No submission directories under "
                     f"`{SUBMISSION_ROOT}/` changed in this PR.")
    for r in results:
        head = f"### `{pathlib.Path(r['dir']).name}`"
        lines.append(head)
        if r["ok"]:
            v = r["verify"]
            lines += [
                "",
                f"| | |",
                f"|---|---|",
                f"| verdict | **valid** — feasible in exact arithmetic |",
                f"| value (exact, 30 digits) | `{r['value_30sig']}` |",
                f"| vs current canonical | {r['relation']} |",
                f"| published page entry | `{r['published'] or '—'}` |",
                f"| detected symmetry | {r['symmetry']} |",
                f"| triples checked | {v['triples_checked']}, "
                f"{v['num_min_ties']} tied at the minimum |",
                "",
            ]
        else:
            lines.append("\n**invalid:**\n")
            lines += [f"- {p}" for p in r["problems"]]
            lines.append("")
        for w in r["warnings"]:
            lines.append(f"- ⚠ {w}")
        lines.append("")
    if out_of_scope:
        lines.append(f"This PR also touches {len(out_of_scope)} file(s) outside "
                     f"`{SUBMISSION_ROOT}/` — fine, but they get a human review, "
                     "not this automated one:")
        lines += [f"- `{p}`" for p in out_of_scope[:20]]
        if len(out_of_scope) > 20:
            lines.append(f"- … and {len(out_of_scope) - 20} more")
    lines += ["", "*Verification: exact rational arithmetic over all point "
              "triples (`build/vendor/verify_exact.py`). A valid submission is "
              "adopted by ingest only if its exact value beats every other "
              "source for that entry.*"]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dirs", nargs="*", help="submission directories to check")
    ap.add_argument("--base", help="git ref: check dirs changed since this ref")
    ap.add_argument("--out", help="also write the Markdown report to this file")
    args = ap.parse_args()

    out_of_scope = []
    if args.base:
        dirs, out_of_scope = changed_submission_dirs(args.base)
    else:
        dirs = [pathlib.Path(d).resolve() for d in args.dirs]
    results = [check_dir(d) for d in dirs]

    report = render(results, out_of_scope)
    print(report)
    if args.out:
        pathlib.Path(args.out).write_text(report + "\n")
    sys.exit(0 if all(r["ok"] for r in results) else 1)


if __name__ == "__main__":
    main()
