"""Per-configuration download files and the site-wide bundles."""

import io
import json
import pathlib
import zipfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
DIST = ROOT / "dist" / "heilbronn"

DOMAIN_LINE = {
    "square": "unit square [0,1]^2; value = min triangle area",
    "triangle": "triangle (0,0),(1,0),(0,1); value = min 2*area (normalized to unit-area domain)",
    "convex": "convex hull of the points; value = min triangle area / hull area (scale-invariant)",
}


def points_txt(doc):
    lines = [
        f"# Heilbronn {doc['variant']} n={doc['n']}",
        f"# value (exact area implied by these coordinate literals): {doc['value']['decimal']}",
        f"# domain: {DOMAIN_LINE[doc['variant']]}",
    ]
    c = doc["credit"]
    if c["trivial"]:
        lines.append("# credit: trivial configuration")
    elif c["found"]:
        date = f", {c['found']['date']}" if c["found"]["date"] else ""
        lines.append(f"# credit: found by {c['found']['name']}{date}")
    if c["proved"]:
        date = f", {c['proved']['date']}" if c["proved"]["date"] else ""
        lines.append(f"# proved optimal by {c['proved']['name']}{date}")
    src = doc.get("coordinates_source")
    if src:
        lines.append(f"# coordinates: {src['ref']}" + (f" ({src['note']})" if src.get("note") else ""))
    lines.append(f"# via: https://math.tejstead.com/heilbronn/{doc['variant']}/{doc['n']}/")
    for x, y in doc["points"]:
        lines.append(f"{x}\t{y}")
    return "\n".join(lines) + "\n"


def points_csv(doc):
    return "x,y\n" + "\n".join(f"{x},{y}" for x, y in doc["points"]) + "\n"


def write_downloads(docs):
    values = {}
    bundle = []
    for (v, n), doc in sorted(docs.items()):
        values.setdefault(v, {})[str(n)] = {
            "decimal": doc["value"]["decimal"],
            "fraction": doc["value"]["fraction"],
            "published": doc["value"]["published_decimal"],
            "status": doc["status"],
            "page_relation": doc.get("page_relation"),
        }
        if not doc["points"]:
            continue
        d = DIST / v / str(n)
        d.mkdir(parents=True, exist_ok=True)
        txt = points_txt(doc)
        (d / "points.txt").write_text(txt)
        (d / "points.csv").write_text(points_csv(doc))
        (d / "points.json").write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
        bundle.append((f"{v}/n{n:02d}/points.txt", txt))
        bundle.append((f"{v}/n{n:02d}/points.json",
                       json.dumps(doc, indent=1, ensure_ascii=False) + "\n"))

    (DIST / "assets").mkdir(parents=True, exist_ok=True)
    values_json = json.dumps(values, separators=(",", ":"))
    import hashlib
    digest = hashlib.sha256(values_json.encode()).hexdigest()[:10]
    values_name = f"values.{digest}.json"
    (DIST / "assets" / values_name).write_text(values_json)

    datadir = DIST / "data"
    datadir.mkdir(parents=True, exist_ok=True)
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr("README.txt",
                   "Best known Heilbronn configurations (square, triangle, convex),\n"
                   "collected at https://math.tejstead.com/heilbronn/ .\n"
                   "See ATTRIBUTION in each points.json (coordinates_source) and\n"
                   "https://math.tejstead.com/heilbronn/methods/ for provenance.\n")
        for name, content in bundle:
            z.writestr(name, content)
    (datadir / "heilbronn-all.zip").write_bytes(buf.getvalue())
    return values_name
