#!/usr/bin/env python3
"""Fetch and parse Erich Friedman's Heilbronn pages into a facts snapshot.

The snapshot records facts only (values, credits, symmetry labels) — never
his images or prose beyond the per-entry sentences. It is the input both for
seeding curated provenance and for the automated watcher: run periodically,
diff against the committed snapshot, and review what changed.

Usage:
    python3 scripts/friedman_sync.py                  # fetch + write snapshot
    python3 scripts/friedman_sync.py --local DIR      # parse saved HTML files
    python3 scripts/friedman_sync.py --diff OLD NEW   # compare two snapshots
"""

import argparse
import datetime
import html as htmllib
import json
import pathlib
import re
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
SNAP_DIR = ROOT / "data" / "sources" / "friedman"

PAGES = {
    "square": "https://erich-friedman.github.io/packing/heilbronn/",
    "triangle": "https://erich-friedman.github.io/packing/heiltri/",
    "convex": "https://erich-friedman.github.io/packing/heilconvex/",
}

TAG_RE = re.compile(r"<[^>]+>")


def decode_html(data):
    """The pages are hand-edited and inconsistently encoded (heiltri is
    UTF-16 LE with a BOM as of 2026-08). Sniff the BOM, fall back to UTF-8."""
    if data[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return data.decode("utf-16")
    return data.decode("utf-8", "replace")


def clean(fragment):
    """Strip tags and normalize entities/whitespace in an HTML fragment."""
    fragment = fragment.replace("<sup>o</sup>", "°")
    # Exponents: <sup>1/3</sup> etc. must not flatten into the base text
    # (that turned cube roots into a literal "1/3" once).
    fragment = re.sub(r"<sup>\s*([^<]+?)\s*</sup>", r"^(\1)", fragment)
    fragment = TAG_RE.sub("", fragment)
    fragment = htmllib.unescape(fragment)
    # The pages use en/em dashes as minus signs in exact forms.
    fragment = fragment.replace("–", "-").replace("—", "-")
    return re.sub(r"\s+", " ", fragment).strip()


def parse_page(html):
    """Parse one page into {n: entry}. Entries carry the raw sentences so
    nothing is lost; convenience fields are best-effort extractions."""
    entries = {}
    for chunk in html.split("<HR>"):
        m = re.search(r"<font size=\+3>(\d+)\.", chunk)
        if not m:
            continue
        n = int(m.group(1))
        # The text cell is the one whose content starts with "A =". It is not
        # always the last cell (multi-image entries put more images after it),
        # and cells are often unclosed (hand-edited HTML), so split on opening
        # tags and scan.
        parts = None
        for cell in re.split(r"<TD[^>]*>", chunk, flags=re.I)[1:]:
            cand = [clean(p) for p in re.split(r"<p>", cell, flags=re.I)]
            cand = [p for p in cand if p]
            if cand and re.match(r"A\s*=", cand[0]):
                parts = cand
                break
        if parts is None:
            continue

        value_text = parts[0]
        sentences = parts[1:]

        # "A = <exact form> = <decimal>+" | "A = <decimal>+" | "A = 1"
        rhs = value_text.split("=", 1)[1].strip() if "=" in value_text else ""
        segs = [s.strip() for s in rhs.split("=")] if rhs else []
        decimal_raw = segs[-1] if segs else ""
        exact_text = " = ".join(segs[:-1]) if len(segs) > 1 else None
        lower_bound = decimal_raw.endswith("+")
        decimal = decimal_raw.rstrip("+")
        if decimal.startswith("."):
            decimal = "0" + decimal
        if "/" in decimal or not re.fullmatch(r"[0-9.]+", decimal or ""):
            # Pure exact value with no decimal rendering (e.g. "1", "1/2").
            exact_text = rhs.rstrip("+") if exact_text is None else exact_text
            decimal = None

        symmetry = None
        notes = []
        credits = []
        for s in sentences:
            low = s.lower()
            if low.startswith(("trivial", "found by", "proved")):
                credits.append(s)
            elif re.match(r"A\s*=", s) and decimal is None:
                # Long exact forms push the decimal into its own paragraph
                # (e.g. convex n=18): "A = .018238+".
                d = s.split("=", 1)[1].strip()
                lower_bound = d.endswith("+")
                d = d.rstrip("+")
                decimal = ("0" + d) if d.startswith(".") else d
            elif "symmetr" in low or "dihedral" in low or "rotational" in low:
                symmetry = s.rstrip(".")
            else:
                notes.append(s)

        entries[str(n)] = {
            "value_text": value_text,
            "exact_text": exact_text,
            "decimal": decimal,
            "lower_bound": lower_bound,
            "credits": credits,
            "symmetry": symmetry,
            "notes": notes,
        }
    return entries


def build_snapshot(get_html):
    variants = {}
    for variant, url in PAGES.items():
        entries = parse_page(get_html(variant, url))
        if not entries:
            raise RuntimeError(f"parsed 0 entries for {variant} — page layout changed?")
        variants[variant] = entries
    return {
        "fetched": datetime.date.today().isoformat(),
        "source_urls": PAGES,
        "variants": variants,
    }


def diff_snapshots(old, new):
    """Yield human-readable change lines between two snapshots."""
    for variant in PAGES:
        o = old["variants"].get(variant, {})
        n = new["variants"].get(variant, {})
        for key in sorted(set(o) | set(n), key=int):
            if key not in o:
                yield f"{variant} n={key}: NEW entry: {n[key]['value_text']}"
                continue
            if key not in n:
                yield f"{variant} n={key}: entry REMOVED"
                continue
            for field in ("value_text", "credits", "symmetry", "notes"):
                if o[key][field] != n[key][field]:
                    yield (f"{variant} n={key}: {field} changed: "
                           f"{o[key][field]!r} -> {n[key][field]!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--local", metavar="DIR",
                    help="parse {heilbronn,heiltri,heilconvex}.html from DIR instead of fetching")
    ap.add_argument("--diff", nargs=2, metavar=("OLD", "NEW"),
                    help="diff two snapshot JSON files and exit")
    ap.add_argument("--out", help="output path (default: data/sources/friedman/parsed-<date>.json)")
    args = ap.parse_args()

    if args.diff:
        old = json.loads(pathlib.Path(args.diff[0]).read_text())
        new = json.loads(pathlib.Path(args.diff[1]).read_text())
        changes = list(diff_snapshots(old, new))
        for line in changes:
            print(line)
        print(f"{len(changes)} change(s)")
        return 1 if changes else 0

    slugs = {"square": "heilbronn", "triangle": "heiltri", "convex": "heilconvex"}
    if args.local:
        def get_html(variant, url):
            return decode_html((pathlib.Path(args.local) / f"{slugs[variant]}.html").read_bytes())
    else:
        def get_html(variant, url):
            req = urllib.request.Request(url, headers={"User-Agent": "heilbronn-site-sync"})
            with urllib.request.urlopen(req, timeout=30) as resp:
                return decode_html(resp.read())

    snap = build_snapshot(get_html)
    out = pathlib.Path(args.out) if args.out else SNAP_DIR / f"parsed-{snap['fetched']}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(snap, indent=1, ensure_ascii=False) + "\n")
    total = sum(len(v) for v in snap["variants"].values())
    print(f"wrote {out} ({total} entries)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
