"""Build-time SVG charts for the trends page. Self-contained like the
figures: styling and dark-mode variants live inside each SVG, series colors
are the first three validated categorical slots (all-pairs safe for three
series), marks follow the dataviz specs (2px lines, 8px-diameter markers,
recessive grid, direct labels + native <title> tooltips)."""

import math

W, H = 720, 400
ML, MR, MT, MB = 62, 120, 18, 46  # margins: right one leaves room for labels

SERIES = {
    "square": ("#2a78d6", "#3987e5"),
    "triangle": ("#eb6834", "#d95926"),
    "convex": ("#1baf7a", "#199e70"),
}

STYLE = (
    "<style>"
    "text{font-family:ui-sans-serif,system-ui,sans-serif;font-size:12.5px;fill:#55534e}"
    ".title{font-size:13.5px;font-weight:600;fill:#1c1c22}"
    ".grid{stroke:#e4e2dc;stroke-width:1}"
    ".axis{stroke:#a9a49b;stroke-width:1.2}"
    ".series{fill:none;stroke-width:2}"
    ".lbl{font-weight:600}"
    + "".join(f".s-{k}{{stroke:{l}}} .m-{k}{{fill:{l}}} .t-{k}{{fill:{l}}}"
              for k, (l, d) in SERIES.items()) +
    "@media(prefers-color-scheme:dark){"
    "text{fill:#97959e}.title{fill:#e8e6e1}"
    ".grid{stroke:#2c2c33}.axis{stroke:#4b4b54}"
    + "".join(f".s-{k}{{stroke:{d}}} .m-{k}{{fill:{d}}} .t-{k}{{fill:{d}}}"
              for k, (l, d) in SERIES.items()) +
    "}</style>"
)


def _fmt(v):
    return f"{v:.2f}".rstrip("0").rstrip(".")


def chart(series, *, title, ylabel, logy=False, yticks, ytick_fmt=str,
          proven_marker=True, svg_id="chart"):
    """series: {name: [(n, value, proven, tooltip), ...]}"""
    ns = [n for pts in series.values() for n, *_ in pts]
    x0, x1 = min(ns), max(ns)

    def X(n):
        return ML + (n - x0) / (x1 - x0) * (W - ML - MR)

    ty = [math.log10(t) if logy else t for t in yticks]
    ylo, yhi = min(ty), max(ty)

    def Y(v):
        v = math.log10(v) if logy else v
        return MT + (yhi - v) / (yhi - ylo) * (H - MT - MB)

    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
             f'role="img" aria-label="{title}" id="{svg_id}">', STYLE]
    parts.append(f'<text class="title" x="{ML}" y="{MT - 4}">{title}</text>')

    for t in yticks:
        y = Y(t)
        parts.append(f'<line class="grid" x1="{ML}" y1="{_fmt(y)}" x2="{W - MR}" y2="{_fmt(y)}"/>')
        parts.append(f'<text x="{ML - 8}" y="{_fmt(y + 4)}" text-anchor="end">{ytick_fmt(t)}</text>')
    for n in range(5, x1 + 1, 5):
        parts.append(f'<text x="{_fmt(X(n))}" y="{H - MB + 18}" text-anchor="middle">{n}</text>')
    parts.append(f'<line class="axis" x1="{ML}" y1="{H - MB}" x2="{W - MR}" y2="{H - MB}"/>')
    parts.append(f'<text x="{_fmt((ML + W - MR) / 2)}" y="{H - 8}" text-anchor="middle">n</text>')
    parts.append(f'<text transform="rotate(-90 16 {_fmt((MT + H - MB) / 2)})" '
                 f'x="16" y="{_fmt((MT + H - MB) / 2)}" text-anchor="middle">{ylabel}</text>')

    labels = []
    for name, pts in series.items():
        path = " ".join(f"{'M' if i == 0 else 'L'}{_fmt(X(n))},{_fmt(Y(v))}"
                        for i, (n, v, *_ ) in enumerate(pts))
        parts.append(f'<path class="series s-{name}" d="{path}"/>')
        for n, v, proven, tip in pts:
            r = 4 if proven and proven_marker else 2.6
            parts.append(
                f'<circle class="m-{name}" cx="{_fmt(X(n))}" cy="{_fmt(Y(v))}" '
                f'r="{r}"><title>{name}, n={n}: {tip}</title></circle>')
        ln, lv, *_ = pts[-1]
        labels.append([name, X(ln) + 10, Y(lv) + 4])
    # De-collide end labels: nudge apart until 15px separation.
    labels.sort(key=lambda l: l[2])
    for i in range(1, len(labels)):
        if labels[i][2] - labels[i - 1][2] < 15:
            labels[i][2] = labels[i - 1][2] + 15
    for name, lx, ly in labels:
        parts.append(f'<text class="lbl t-{name}" x="{_fmt(lx)}" '
                     f'y="{_fmt(ly)}">{name}</text>')

    parts.append("</svg>")
    return "".join(parts)


def build_charts(docs):
    """docs: {(variant, n): canonical doc}. Returns {chart_id: svg}."""
    def val(d):
        s = d["value"].get("exact_decimal") or d["value"]["decimal"]
        return float(s) if s else None

    a_series, a2_series, tie_series = {}, {}, {}
    for v in ("square", "triangle", "convex"):
        a, a2, t = [], [], []
        for n in range(3, 36):
            d = docs.get((v, n))
            if not d or not d["points"]:
                continue
            x = val(d)
            proven = d["status"] in ("proven", "trivial")
            a.append((n, x, proven, f"A = {x:.6g}" + (" (proven)" if proven else "")))
            a2.append((n, x * n * n, proven, f"n²A = {x * n * n:.4g}"))
            ties = d["verify"]["num_min_ties"]
            t.append((n, ties, proven, f"{ties} tied minimal triangles"))
        a_series[v], a2_series[v], tie_series[v] = a, a2, t

    return {
        "values": chart(a_series, title="Best known A(n), unit-area container",
                        ylabel="A(n), log scale", logy=True,
                        yticks=[1, 0.3, 0.1, 0.03, 0.01, 0.003],
                        ytick_fmt=lambda t: f"{t:g}", svg_id="c-values"),
        "normalized": chart(a2_series, title="n²·A(n) — the asymptotic view",
                            ylabel="n²·A(n)",
                            yticks=[0, 2, 4, 6, 8, 10],
                            ytick_fmt=lambda t: f"{t:g}", svg_id="c-normalized"),
        "ties": chart(tie_series, title="Tied minimal triangles per configuration",
                      ylabel="count of tied minima",
                      yticks=[0, 10, 20, 30, 40, 50, 60, 70],
                      ytick_fmt=lambda t: f"{t:g}", proven_marker=False,
                      svg_id="c-ties"),
    }
