"""Structured SVG figures. One SVG per configuration, used inline on the
per-n page (where viewer.js enhances it) and standalone as figure.svg /
thumbnails — so all styling lives in a <style> block inside the SVG itself,
including the dark-mode variants (prefers-color-scheme applies to SVG loaded
via <img> too). Site CSS never needs to reach inside.

Layer structure the viewer depends on:
    g.domain    — container outline
    g.mintris   — <polygon class="mintri cc-K" data-tri="i,j,k" data-cc="K">
    g.points    — <circle data-idx="i">
    g.sym       — display:none; symmetry axes (line.sym-axis) + rotation marker

Congruence classes are color-coded only when there are at most MAX_CC of
them (validated categorical palette, fixed slot order); beyond that — or
when there is no congruence structure at all — every minimal triangle gets
the single neutral series color, which reads far better than a cycled
rainbow.
"""

import math

from .derive import SQ3
from .vendor.verify_exact import convex_hull

SIZE = 1000
PAD = 40

# Validated categorical palette (dataviz reference instance, fixed order),
# stepped separately for light and dark surfaces.
CC_LIGHT = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300"]
CC_DARK = ["#3987e5", "#d95926", "#199e70", "#c98500", "#d55181", "#008300"]
MAX_CC = len(CC_LIGHT)


def _style(class_count, single):
    ccs = 1 if single else class_count
    light = []
    dark = []
    for i in range(ccs):
        c = CC_LIGHT[0] if single else CC_LIGHT[i]
        d = CC_DARK[0] if single else CC_DARK[i]
        light.append(f".cc-{i}{{fill:{c};stroke:{c}}}")
        dark.append(f".cc-{i}{{fill:{d};stroke:{d}}}")
    return (
        "<style>"
        ".domain{fill:none;stroke:#a9a49b;stroke-width:2.5}"
        ".mintri{fill-opacity:.3;stroke-width:2;stroke-linejoin:round}"
        ".points circle{fill:#23232b;stroke:#fdfcfa;stroke-width:2.5}"
        ".points circle.orbit-hl{stroke:#b33c1a;stroke-width:4}"
        ".points circle.free{fill:#eb6834}"
        ".traces polyline{fill:none;stroke:#eb6834;stroke-width:2.5;"
        "stroke-dasharray:3 8;opacity:.9}"
        ".sym{display:none}"
        ".sym line{stroke:#b33c1a;stroke-width:2;stroke-dasharray:10 8}"
        ".sym circle{fill:none;stroke:#b33c1a;stroke-width:2}"
        + "".join(light) +
        "@media(prefers-color-scheme:dark){"
        ".domain{stroke:#4b4b54}"
        ".points circle{fill:#e8e6e1;stroke:#16161a}"
        ".points circle.orbit-hl{stroke:#ef7d54}"
        ".points circle.free{fill:#d95926}"
        ".traces polyline{stroke:#d95926}"
        ".sym line,.sym circle{stroke:#ef7d54}"
        + "".join(dark) +
        "}"
        "</style>"
    )


def _square_tf():
    s = SIZE - 2 * PAD
    return lambda x, y: (PAD + x * s, SIZE - PAD - y * s)


def _triangle_tf():
    # Right frame -> equilateral display frame -> canvas.
    s = SIZE - 2 * PAD
    h = s * SQ3 / 2
    oy = (SIZE - h) / 2
    def tf(x, y):
        ex = x + y / 2
        ey = y * SQ3 / 2
        return (PAD + ex * s, SIZE - oy - ey * s)
    return tf


def _convex_tf(points):
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    w = max(xs) - min(xs) or 1.0
    h = max(ys) - min(ys) or 1.0
    s = (SIZE - 2 * PAD) / max(w, h)
    ox = (SIZE - w * s) / 2 - min(xs) * s
    oy = (SIZE - h * s) / 2
    ymax = max(ys)
    return lambda x, y: (ox + x * s, oy + (ymax - y) * s)


def transform_for(variant, points):
    if variant == "square":
        return _square_tf()
    if variant == "triangle":
        return _triangle_tf()
    return _convex_tf(points)


def _fmt(v):
    return f"{v:.2f}".rstrip("0").rstrip(".")


def _poly(pts, **attrs):
    p = " ".join(f"{_fmt(x)},{_fmt(y)}" for x, y in pts)
    a = "".join(f' {k.replace("_", "-")}="{v}"' for k, v in attrs.items())
    return f'<polygon points="{p}"{a}/>'


def domain_outline(variant, points, tf):
    if variant == "square":
        corners = [(0, 0), (1, 0), (1, 1), (0, 1)]
    elif variant == "triangle":
        corners = [(0, 0), (1, 0), (0, 1)]  # maps to the equilateral outline
    else:
        corners = convex_hull([(float(x), float(y)) for x, y in points])
    return _poly([tf(x, y) for x, y in corners], **{"class": "outline"})


def family_svg(variant, points_str, derived, fam, svg_id="famfig"):
    """Second figure for entries with a proven family: the stored member plus
    dashed traces of each moving point across the family. Returns
    (svg, payload) where payload carries canvas-space samples for family.js.
    """
    pts = [(float(x), float(y)) for x, y in points_str]
    sample_pts = [[(float(x), float(y)) for x, y in s] for s in fam["samples"]]
    if variant == "convex":
        allpts = [p for s in sample_pts for p in s] + pts
        tf = _convex_tf(allpts)
    else:
        tf = transform_for(variant, pts)

    # 3 decimals: at 1e-2 the coordinate quantization perturbs tie areas by
    # ~1e-4 relative — the same order as the display tie tolerance, making
    # persistent ties flicker while scrubbing.
    canvas_samples = [[[round(c, 3) for c in tf(x, y)] for (x, y) in s]
                      for s in sample_pts]

    hull_order = None
    if variant == "convex":
        hull = convex_hull(pts)
        lookup = {(x, y): i for i, (x, y) in enumerate(pts)}
        hull_order = [lookup[tuple(h)] for h in hull]
        domain = _poly([tf(x, y) for x, y in hull], **{"class": "outline"})
    else:
        domain = domain_outline(variant, points_str, tf)

    mintris = []
    for t in derived["ties"]:
        tri = [tf(*pts[i]) for i in t]
        mintris.append(_poly(tri, **{"class": "mintri cc-0",
                                     "data_tri": ",".join(map(str, t))}))

    traces = []
    for i in fam["moving"]:
        path = " ".join(f"{x:.2f},{y:.2f}"
                        for s in canvas_samples for x, y in [s[i]])
        traces.append(f'<polyline points="{path}"/>')

    circles = []
    for i, (x, y) in enumerate(pts):
        cx, cy = tf(x, y)
        free = " free" if i in fam["moving"] else ""
        circles.append(f'<circle class="pt{free}" data-idx="{i}" '
                       f'cx="{_fmt(cx)}" cy="{_fmt(cy)}" r="7"/>')

    payload = {
        "samples": canvas_samples,
        "moving": fam["moving"],
        "hull": hull_order,
        "param": fam["param"],
        "tieTol": 1e-3,
    }
    svg = (
        f'<svg id="{svg_id}" xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="0 0 {SIZE} {SIZE}" role="img" class="single" '
        f'aria-label="family of optimal configurations, {variant} n = {len(pts)}">'
        + _style(1, True)
        + f'<g class="domain">{domain}</g>'
        f'<g class="mintris">{"".join(mintris)}</g>'
        f'<g class="traces">{"".join(traces)}</g>'
        f'<g class="points">{"".join(circles)}</g>'
        f'</svg>'
    )
    return svg, payload


def _tesseract_cc(ties):
    """For square n=16: color min triangles by parallelogram group.
    cc-0 (blue) = axis-aligned tesseract faces, cc-1 (orange) = diagonal, cc-2 (green) = stray.
    Indices are in the canonical file ordering (matched via coordinate lookup)."""
    AXIS = [{0,2,6,10},{0,4,7,15},{2,9,11,12},{4,8,12,14},
            {3,8,10,13},{1,5,6,14},{5,9,13,15},{1,3,7,11}]
    DIAG = [{0,10,12,14},{4,5,8,9},{6,7,12,13},{7,8,10,15},{6,9,11,14},{1,11,13,15}]
    cc_of = {}
    for t in ties:
        s = set(t)
        if any(s.issubset(f) for f in AXIS):
            cc_of[t] = 0
        elif any(s.issubset(f) for f in DIAG):
            cc_of[t] = 1
        else:
            cc_of[t] = 2
    return cc_of


def figure_svg(variant, points_str, derived, svg_id="fig"):
    pts = [(float(x), float(y)) for x, y in points_str]
    tf = transform_for(variant, pts)

    classes = derived["classes"]
    single = len(classes) > MAX_CC or all(len(c["triangles"]) == 1 for c in classes)

    # Special case: square n=16 gets tesseract-based coloring
    if variant == "square" and len(pts) == 16:
        cc_of = _tesseract_cc(derived["ties"])
        single = False
        class_count = 3
    else:
        cc_of = {}
        class_count = len(classes)
        for ci, cls in enumerate(classes):
            for t in cls["triangles"]:
                cc_of[t] = 0 if single else ci

    mintris = []
    for t in derived["ties"]:
        ci = cc_of[t]
        tri = [tf(*pts[i]) for i in t]
        mintris.append(_poly(tri, **{
            "class": f"mintri cc-{ci}",
            "data_tri": ",".join(map(str, t)),
            "data_cc": str(ci),
        }))

    orbit_of = {}
    for oi, orbit in enumerate(derived.get("orbits", [])):
        for i in orbit:
            orbit_of[i] = oi
    circles = []
    for i, (x, y) in enumerate(pts):
        cx, cy = tf(x, y)
        circles.append(f'<circle data-idx="{i}" data-orbit="{orbit_of.get(i, i)}" '
                       f'cx="{_fmt(cx)}" cy="{_fmt(cy)}" r="7"/>')

    sym_elems = []
    sym = derived["symmetry"]
    if variant == "triangle":
        s = SIZE - 2 * PAD
        oy = (SIZE - s * SQ3 / 2) / 2
        sym_tf = lambda ex, ey: (PAD + ex * s, SIZE - oy - ey * s)
    else:
        sym_tf = tf
    if sym["rotation"]:
        cx, cy = sym_tf(*sym["rotation"]["center"])
        sym_elems.append(
            f'<circle class="sym-center" data-order="{sym["rotation"]["order"]}" '
            f'cx="{_fmt(cx)}" cy="{_fmt(cy)}" r="6"/>')
    half = SIZE * 0.75
    for ai, ax in enumerate(sym["axes"]):
        cx, cy = sym_tf(*ax["center"])
        # Canvas y is flipped, so the displayed axis angle is negated.
        dx, dy = math.cos(-ax["angle"]), math.sin(-ax["angle"])
        sym_elems.append(
            f'<line class="sym-axis" data-axis="{ai}" '
            f'x1="{_fmt(cx - dx * half)}" y1="{_fmt(cy - dy * half)}" '
            f'x2="{_fmt(cx + dx * half)}" y2="{_fmt(cy + dy * half)}"/>')

    return (
        f'<svg id="{svg_id}" xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="0 0 {SIZE} {SIZE}" role="img" '
        f'aria-label="{variant} configuration, n = {len(pts)}"'
        f'{" class=" + chr(34) + "single" + chr(34) if single else ""}>'
        + _style(class_count, single)
        + f'<g class="domain">{domain_outline(variant, points_str, tf)}</g>'
        f'<g class="mintris">{"".join(mintris)}</g>'
        f'<g class="sym">{"".join(sym_elems)}</g>'
        f'<g class="points">{"".join(circles)}</g>'
        f'</svg>'
    )
