"""Render the whole site into dist/heilbronn/ from the canonical data."""

import hashlib
import html
import json
import pathlib
import re
import shutil

import jinja2

from .derive import derive, friedman_label
from .svggen import figure_svg

ROOT = pathlib.Path(__file__).resolve().parent.parent
CANONICAL = ROOT / "data" / "canonical"
DIST = ROOT / "dist" / "heilbronn"

VARIANTS = ("square", "triangle", "convex")
NS = list(range(3, 36))
BASE = "/heilbronn"

META = {
    "square": {
        "title": "The Heilbronn problem for squares",
        "short": "Square",
        "card_title": "Squares",
        "blurb": "n points in the unit square.",
        "intro": (
            "<p>Place <em>n</em> points in the unit square so that the smallest "
            "triangle determined by any three of them has area A as large as "
            "possible. Optimality is proven for n ≤ 9; every later entry is a "
            "best known configuration.</p>"),
        "friedman": "https://erich-friedman.github.io/packing/heilbronn/",
    },
    "triangle": {
        "title": "The Heilbronn problem for triangles",
        "short": "Triangle",
        "card_title": "Triangles",
        "blurb": "n points in a triangle of unit area.",
        "intro": (
            "<p>Place <em>n</em> points in a triangle of unit area. The problem is "
            "affine-invariant, so the triangle's shape does not matter: "
            "coordinates are stored in the right triangle (0,0),(1,0),(0,1) and "
            "drawn equilateral. Papers that use the unit <em>right</em> triangle "
            "(area ½) quote values half as large as these. Optimality is proven "
            "for n ≤ 8.</p>"),
        "friedman": "https://erich-friedman.github.io/packing/heiltri/",
    },
    "convex": {
        "title": "The Heilbronn problem for convex regions",
        "short": "Convex",
        "card_title": "Convex regions",
        "blurb": "n points in a convex region chosen freely, of unit area.",
        "intro": (
            "<p>Here the container is part of the optimization: the points may "
            "lie in <em>any</em> convex region of unit area. The optimal region is the "
            "convex hull of the points, so every configuration is a polygon and "
            "A is the smallest triangle area divided by the hull area. Settled "
            "for n ≤ 7.</p>"),
        "friedman": "https://erich-friedman.github.io/packing/heilconvex/",
    },
}

INDEX_THUMBS = {"square": 16, "triangle": 18, "convex": 18}


def load_docs():
    docs = {}
    for v in VARIANTS:
        for n in NS:
            p = CANONICAL / v / f"n{n:02d}.json"
            if p.exists():
                docs[(v, n)] = json.loads(p.read_text())
    return docs


def snapshot_date():
    snaps = sorted((ROOT / "data" / "sources" / "friedman").glob("parsed-*.json"))
    return json.loads(snaps[-1].read_text())["fetched"]


def hash_assets():
    """Copy css/js into dist with content-hashed names; return the map."""
    assets = {}
    outdir = DIST / "assets"
    outdir.mkdir(parents=True, exist_ok=True)
    for src in list((ROOT / "assets" / "css").glob("*.css")) + \
               list((ROOT / "assets" / "js").glob("*.js")):
        digest = hashlib.sha256(src.read_bytes()).hexdigest()[:10]
        hashed = f"{src.stem}.{digest}{src.suffix}"
        shutil.copy(src, outdir / hashed)
        assets[src.name] = hashed
    return assets


SUPERSCRIPT = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")


def pretty_poly(p):
    """152*x**3 + 12*x**2 - 14*x + 1  ->  152x³ + 12x² − 14x + 1"""
    if not p:
        return None
    import re
    s = p.replace("**", "^").replace("*", "")
    s = re.sub(r"\^(\d+)", lambda m: m.group(1).translate(SUPERSCRIPT), s)
    return s.replace("-", "−")


def short_value(doc, digits=8):
    d = doc["value"].get("exact_decimal") or doc["value"]["decimal"] \
        or doc["value"]["published_decimal"]
    if d is None:
        return "?"
    if len(d) <= digits + 2:
        return d
    return d[: digits + 2]


def fmt_dec(dec, limit=18):
    """Decimal for display: exact terminating decimals lose their trailing
    zeros ("0.5", not "0.5000000000000000…"); everything else truncates to
    `limit` characters with an ellipsis."""
    if dec is None:
        return None
    stripped = dec.rstrip("0")
    if stripped.endswith("."):
        stripped = stripped[:-1]
    if len(stripped) <= limit and stripped != dec:
        return stripped
    return (dec[:limit] + "…") if len(dec) > limit else dec


def fixed8(doc):
    """Uniform 8-decimal rendering for the values table (truncated, which
    keeps every entry a valid lower bound). Rows known only from Friedman's
    truncated decimal keep his short form + '+' — padding them with zeros
    would fake precision we don't have."""
    d = doc["value"].get("exact_decimal") or doc["value"]["decimal"]
    if d is None:
        p = doc["value"]["published_decimal"]
        return f"{p}+" if p else None
    if "." not in d:
        d += "."
    head, tail = d.split(".", 1)
    return f"{head}.{(tail + '00000000')[:8]}"


def credit_text(doc):
    c = doc["credit"]
    if c["trivial"]:
        return "Trivial"
    parts = []
    if c["found"]:
        parts.append(f"{c['found']['name']}" + (f", {c['found']['date']}" if c["found"]["date"] else ""))
    if c["proved"]:
        parts.append(f"proved {c['proved']['name']}" + (f" {c['proved']['date']}" if c["proved"]["date"] else ""))
    return "; ".join(parts) if parts else "—"


def provenance_lines(doc, derived):
    lines = []
    c = doc["credit"]
    if c["trivial"]:
        lines.append("Trivial configuration.")
    if c["found"]:
        lines.append(f"Found by <strong>{c['found']['name']}</strong>"
                     + (f", {c['found']['date']}" if c["found"]["date"] else "") + ".")
    if c["proved"]:
        line = (f"Proved optimal by <strong>{c['proved']['name']}</strong>"
                + (f", {c['proved']['date']}" if c["proved"]["date"] else ""))
        proof = doc.get("proof")
        if proof and proof.get("url"):
            line += f' (<a href="{html.escape(proof["url"], quote=True)}">proof</a>)'
        lines.append(line + ".")
    for note in doc.get("notes", []):
        lines.append(note)
    src = doc.get("coordinates_source")
    if src:
        kind_text = {
            "author": "from this site's companion repository",
            "spiralulam": "from spiralulam/heilbronn (MIT)",
            "alphaevolve": "as published by AlphaEvolve (Google DeepMind)",
            "exact-construction": "generated from the exact construction",
            "reconstructed": "reconstructed by local optimization",
            "paper": "exact, as published in",
            "external": "by an external contributor, re-verified here",
        }.get(src["kind"], src["kind"])
        # ref and note flow in from source meta.json files — for the
        # "external" kind that is contributor-supplied text, and provenance
        # lines render with |safe, so escape rather than trust it.
        note = f" — {html.escape(src['note'])}" if src.get("note") else ""
        lines.append(f"Coordinates {kind_text}: <code>{html.escape(src['ref'])}</code>{note}.")
    if doc.get("verify"):
        v = doc["verify"]
        lines.append(
            f"Verified in exact arithmetic: all {v['triples_checked']} triples "
            f"enumerated, {v['num_min_ties']} tied at the minimum.")
    if doc["value"].get("published"):
        lines.append(f"Friedman's page lists: <code>{doc['value']['published']}</code>.")
    return lines


def banner_for(doc):
    rel = doc.get("page_relation")
    pub = doc["value"].get("published_decimal")
    holder = credit_text(doc)
    if rel == "BEHIND":
        return {"kind": "behind", "text": (
            f"The published record is <code>{pub}+</code> ({holder}). Neither its "
            f"coordinates nor a current figure are public — the page's figure shows "
            f"an older configuration — so the record cannot be reconstructed from "
            f"published information. Shown here: the best exactly verified "
            f"configuration.")}
    if rel == "BEATS":
        if doc.get("page_note"):
            return {"kind": "beats", "text": doc["page_note"]}
        ref = (doc.get("coordinates_source") or {}).get("ref", "")
        kind = (doc.get("coordinates_source") or {}).get("kind", "")
        m = re.search(r"(claims-\d{4}-\d{2}-\d{2})", ref)
        if m:
            return {"kind": "beats", "text": (
                f"These coordinates exceed the page's <code>{pub}+</code>; they were "
                f"submitted for review (batch <code>{m.group(1)}</code>) and the page "
                f"has not been updated yet.")}
        if kind == "reconstructed":
            return {"kind": "beats", "text": (
                f"Re-deriving the record figure produced coordinates exceeding the "
                f"published <code>{pub}+</code> — an unsubmitted refinement of the "
                f"record holder's arrangement.")}
        return {"kind": "beats", "text": (
            f"These coordinates exceed the published <code>{pub}+</code> "
            f"(improvement pending review).")}
    return None


def symmetry_text(doc, derived):
    label = doc["symmetry"]["label"]
    if derived is None:
        return f"Published symmetry: {label}." if label else "Unknown."
    sym = derived["symmetry"]
    det = friedman_label(sym, doc["variant"])
    if sym.get("approx"):
        txt = (f"Approximately {det[0].lower()}{det[1:]} (group {sym['group']}: the "
               f"configuration sits within ~10⁻⁴ of exact symmetry, but the optimum "
               f"is not exactly symmetric at coordinate precision).")
    else:
        txt = f"{det} (group {sym['group']}, order {sym['order']})."
    if label and doc.get("page_relation") == "BEHIND":
        txt += f" The record configuration is listed as: {label.lower()}."
    elif label and det.rstrip(".").lower() != label.rstrip(".").lower():
        txt += f" (Friedman's page says: {label.lower()}.)"
    return txt


def sym_controls(derived):
    if derived is None:
        return []
    sym = derived["symmetry"]
    if sym["rotation"] or sym["axes"]:
        return [{"key": "axes", "label": "show symmetry elements"}]
    return []


def orbit_text(derived):
    """"18 points in 2 orbits (12 + 6)" — or None when trivial."""
    if derived is None:
        return None
    obs = derived.get("orbits") or []
    if not obs or all(len(o) == 1 for o in obs):
        return None
    sizes = sorted((len(o) for o in obs), reverse=True)
    n = sum(sizes)
    return (f"{n} points in {len(sizes)} orbit{'s' if len(sizes) != 1 else ''} "
            f"({' + '.join(map(str, sizes))}) — hover a point to see its orbit.")


MAX_CC = 6  # keep in sync with svggen.MAX_CC


def single_color(derived):
    classes = derived["classes"]
    return len(classes) > MAX_CC or all(len(c["triangles"]) == 1 for c in classes)


def class_rows(derived):
    if derived is None:
        return []
    single = single_color(derived)
    rows = []
    for i, cls in enumerate(derived["classes"]):
        rows.append({
            "cc": 0 if single else i,
            "swatch": not single,
            "count": len(cls["triangles"]),
            "sides": " · ".join(f"{s:.4f}" for s in cls["sides"]),
            "tris": "  ".join("(" + ",".join(map(str, t)) + ")" for t in cls["triangles"][:12])
                    + ("  …" if len(cls["triangles"]) > 12 else ""),
        })
    return rows


def render_all(env, docs, derived_map, assets):
    common = {
        "base": BASE,
        "assets": assets,
        "snapshot_date": snapshot_date(),
    }

    # Per-config pages.
    for (v, n), doc in docs.items():
        derived = derived_map.get((v, n))
        figure = None
        if doc["points"]:
            figure = figure_svg(v, doc["points"], derived, svg_id="fig")
        avail = [m for m in NS if (v, m) in docs]
        idx = avail.index(n)
        refs = []
        bib = json.loads((ROOT / "data" / "curated" / "references.json").read_text())["bib"]
        for rid in doc.get("references", []):
            if rid in bib:
                refs.append(bib[rid])
        val = doc["value"]
        exact_dec = val.get("exact_decimal")
        coord_dec = val.get("decimal")
        if derived:
            cls = class_rows(derived)
            if single_color(derived):
                fig_caption = (f"{len(derived['ties'])} triangles tie for the minimal area."
                               if len(derived["ties"]) > 1 else "A unique minimal triangle.")
            else:
                fig_caption = (f"{len(derived['ties'])} minimal triangles in "
                               f"{len(cls)} congruence classes, colored by class.")
        else:
            cls, fig_caption = [], ""
        ctx = dict(common,
            section=v, slug=v, n=n,
            variant_title=META[v]["short"],
            status=doc["status"],
            recon=recon_label(doc),
            exact_display=val.get("exact_display"),
            exact_mathml=val.get("exact_mathml"),
            poly_mathml=val.get("poly_mathml"),
            exact_decimal=exact_dec,
            value_head=(coord_dec[:17] + "…") if coord_dec and len(coord_dec) > 17 else coord_dec,
            value_full=coord_dec,
            value_fraction=val.get("fraction"),
            value_short=short_value(doc),
            poly=pretty_poly(val.get("minimal_polynomial")),
            poly_which=(val.get("exact_poly") or {}).get("which"),
            poly_note=(val.get("exact_poly") or {}).get("note"),
            banner=banner_for(doc),
            figure=figure,
            fig_caption=fig_caption,
            classes=cls,
            tie_count=len(derived["ties"]) if derived else 0,
            sym_controls=sym_controls(derived),
            symmetry_text=symmetry_text(doc, derived),
            orbit_line=orbit_text(derived),
            provenance=provenance_lines(doc, derived),
            changelog=[{"date": e.get("date", ""), "text": e.get("text", e.get("note", ""))}
                       for e in doc.get("changelog", [])],
            downloads=([
                {"href": "points.txt", "label": "points.txt", "note": "coordinates, tab-separated"},
                {"href": "points.csv", "label": "points.csv", "note": "coordinates, CSV"},
                {"href": "points.json", "label": "points.json", "note": "full record: value, provenance, verification"},
                {"href": "figure.svg", "label": "figure.svg", "note": "this figure"},
            ] if doc["points"] else []),
            references=refs,
            prev=avail[idx - 1] if idx > 0 else None,
            next=avail[idx + 1] if idx + 1 < len(avail) else None,
            cross=[{"slug": w, "title": META[w]["short"]} for w in VARIANTS if w != v and (w, n) in docs],
            friedman_url=META[v]["friedman"],
        )
        out = DIST / v / str(n) / "index.html"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(env.get_template("config.html").render(ctx))
        if figure:
            (out.parent / "figure.svg").write_text(
                '<?xml version="1.0" encoding="UTF-8"?>\n' + figure)

    # Variant pages: one long page of classic entry rows, one per n.
    for v in VARIANTS:
        entries = []
        for n in NS:
            doc = docs.get((v, n))
            if not doc:
                continue
            derived = derived_map.get((v, n))
            val = doc["value"]
            dec = val.get("exact_decimal") or val.get("decimal")
            credit_lines = []
            c = doc["credit"]
            if c["trivial"]:
                credit_lines.append("Trivial.")
            if c["found"]:
                credit_lines.append(f"Found by {c['found']['name']}"
                                    + (f", {c['found']['date']}" if c["found"]["date"] else "") + ".")
            if c["proved"]:
                credit_lines.append(f"Proved optimal by {c['proved']['name']}"
                                    + (f", {c['proved']['date']}" if c["proved"]["date"] else "") + ".")
            symline = None
            if derived:
                sym = derived["symmetry"]
                det = friedman_label(sym, v)
                if sym.get("approx"):
                    det = "approximately " + det[0].lower() + det[1:]
                ties = len(derived["ties"])
                symline = f"{det} · {ties} minimal triangle{'s' if ties != 1 else ''}"
            entries.append({
                "n": n,
                "status": doc["status"],
                "recon": recon_label(doc),
                "fig": (f'<img loading="lazy" width="260" height="260" alt="" '
                        f'src="{BASE}/{v}/{n}/figure.svg">') if doc["points"] else None,
                "mathml": val.get("exact_mathml"),
                "exact_text": None if val.get("exact_mathml") else val.get("exact_display"),
                "poly_mathml": None if val.get("exact_mathml") else val.get("poly_mathml"),
                "dec": fmt_dec(dec),
                "credit_lines": credit_lines,
                "symline": symline,
                "behind": doc.get("page_relation") == "BEHIND",
            })
        ctx = dict(common, section=v, slug=v,
                   title=META[v]["title"], intro=META[v]["intro"],
                   intro_plain=META[v]["blurb"], entries=entries)
        out = DIST / v / "index.html"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(env.get_template("variant.html").render(ctx))

    # Index.
    variants_ctx = []
    for v in VARIANTS:
        tn = INDEX_THUMBS[v]
        variants_ctx.append({
            "slug": v, "title": META[v]["card_title"], "blurb": META[v]["blurb"],
            "thumb": f'<img width="220" height="220" alt="" src="{BASE}/{v}/{tn}/figure.svg">',
        })
    value_rows = []
    for n in NS:
        cells = []
        for v in VARIANTS:
            doc = docs.get((v, n))
            cells.append({
                "slug": v,
                "display": fixed8(doc),
                "proven": doc["status"] in ("proven", "trivial"),
            } if doc else None)
        value_rows.append({"n": n, "cells": cells})
    ctx = dict(common, section="index", variants=variants_ctx, value_rows=value_rows)
    (DIST / "index.html").write_text(env.get_template("index.html").render(ctx))


RECON_LABELS = {
    "figure": "re-derived from figure",
    "value-and-symmetry": "re-derived (value + symmetry)",
    "tightened-original": "tightened originals",
    "original-this-site": "new configuration (this site)",
}


def recon_label(doc):
    """None when coordinates are originals; otherwise a tag naming exactly
    how much reconstruction was involved."""
    src = doc.get("coordinates_source") or {}
    if src.get("kind") != "reconstructed":
        return None
    return RECON_LABELS.get(src.get("basis"), "reconstructed coords")


METHODS_BODY = """
<p>Everything on this site is generated ahead of time from exact coordinate
data; the pages you're reading are static files. The generator, data and
deployment live in the site repository.</p>

<h2>Where the coordinates come from</h2>
<ul>
<li><a href="https://github.com/TejSteadQC/heilbronn-configurations">TejSteadQC/heilbronn-configurations</a>
— coordinates for n = 17…35 in all three variants (and several records below
that), each verified by two independent exact verifiers; also the search
toolkit used to find and polish them (trust-region successive-LP polishing,
KKT tightening, symmetry-restricted search).</li>
<li><a href="https://github.com/spiralulam/heilbronn">spiralulam/heilbronn</a>
(MIT) — square configurations for n = 3…16, the companion repository to
Nathan Sudermann-Merx's certified-optimality work, including the previously
unpublished configurations of Peter Karpov (n = 13, 15) and Mark Beyleveld
(n = 14, 16).</li>
<li><a href="https://github.com/google-deepmind/alphaevolve_results">google-deepmind/alphaevolve_results</a>
— the AlphaEvolve constructions (triangle n = 11, convex n = 13, 14).</li>
<li>Published exact constructions from the proofs (see the bibliography).</li>
<li>Local reconstruction: for configurations whose coordinates were never
published (mostly David Cantrell's), we re-derive them by numerical
optimization seeded from the published figures, and accept a reconstruction
only if its exact value and symmetry match the published entry. These are
labeled <em>reconstructed</em> and never claim to be the original author's
exact arrangement.</li>
</ul>

<h2>Verification</h2>
<p>Every configuration on this site is checked with exact rational
arithmetic: the coordinates' decimal literals are taken exactly, all C(n,3)
triangle areas are enumerated, and the reported value is the exact minimum,
normalized to a unit-area container. The in-browser
<a href="/heilbronn/verifier/">verifier</a> runs the same computation.</p>

<h2>Normalization conventions</h2>
<p>Values here follow Friedman's pages: the container has <strong>unit
area</strong>. Beware when comparing with papers: work in the unit
<em>right</em> triangle (area ½) quotes triangle values half as large, and the
retired circle variant used a unit-<em>radius</em> disk (area π). The triangle
problem is affine-invariant, so coordinates are stored in the right frame
(0,0),(1,0),(0,1) and displayed equilateral.</p>

<h2>Attribution</h2>
<p>This site is an enhanced presentation of the record tables curated for
decades by <a href="https://erich-friedman.github.io/packing/">Erich
Friedman</a>; values, credits and symmetry labels are recorded from his
pages, and each configuration page links back to its row. His images are not
reproduced — every figure is regenerated from coordinates.</p>
"""


def render_extra(env, assets, values_name):
    """Pages that need the values.json asset name (written by downloads)."""
    common = {"base": BASE, "assets": assets, "snapshot_date": snapshot_date()}
    from .charts import build_charts
    (DIST / "trends").mkdir(parents=True, exist_ok=True)
    (DIST / "trends" / "index.html").write_text(
        env.get_template("trends.html").render(
            dict(common, section="trends", charts=build_charts(load_docs()))))
    bib = json.loads((ROOT / "data" / "curated" / "references.json").read_text())["bib"]
    (DIST / "methods").mkdir(parents=True, exist_ok=True)
    (DIST / "methods" / "index.html").write_text(
        env.get_template("methods.html").render(
            dict(common, section="methods", body=METHODS_BODY, bib=list(bib.values()))))
    (DIST / "verifier").mkdir(parents=True, exist_ok=True)
    (DIST / "verifier" / "index.html").write_text(
        env.get_template("verifier.html").render(
            dict(common, section="verifier", values_name=values_name)))
    write_sitemap_and_404(env, common)


SITE_ORIGIN = "https://math.tejstead.com"


def write_sitemap_and_404(env, common):
    urls = [f"{BASE}/", f"{BASE}/trends/", f"{BASE}/verifier/", f"{BASE}/methods/"]
    for v in VARIANTS:
        urls.append(f"{BASE}/{v}/")
        for n in NS:
            if (DIST / v / str(n) / "index.html").exists():
                urls.append(f"{BASE}/{v}/{n}/")
    body = "\n".join(
        f"  <url><loc>{SITE_ORIGIN}{u}</loc></url>" for u in urls)
    (DIST / "sitemap.xml").write_text(
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        f"{body}\n</urlset>\n")
    (DIST / "404.html").write_text(env.get_template("404.html").render(common))
    (DIST.parent / "robots.txt").write_text(
        f"User-agent: *\nAllow: /\nSitemap: {SITE_ORIGIN}{BASE}/sitemap.xml\n")


def make_env():
    return jinja2.Environment(
        loader=jinja2.FileSystemLoader(ROOT / "templates"),
        autoescape=True, trim_blocks=True, lstrip_blocks=True)


def render(docs=None, derived_map=None):
    docs = docs or load_docs()
    if derived_map is None:
        derived_map = {}
        for key, doc in docs.items():
            if doc["points"]:
                derived_map[key] = derive(key[0], doc["points"])
    env = make_env()
    assets = hash_assets()
    render_all(env, docs, derived_map, assets)
    return docs, derived_map, assets, env
