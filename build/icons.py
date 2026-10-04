"""Site icons: the proven-optimal square n = 8 with one of its minimal
triangles filled in — the problem in a picture. One geometry, emitted as
favicon.svg (modern browsers), favicon.ico (16/32/48) and the 180px
apple-touch-icon. Copies go to the domain root too, where browsers and
home-screen savers look without reading the page."""

from fractions import Fraction

from PIL import Image, ImageDraw

from .derive import minimal_triangles

N = 8
TRIANGLE = (0, 6, 7)   # the long sliver across the middle
BG = "#1c1c22"
POINT = "#f0eee9"
ACCENT = "#ef7d54"
EDGE = "#50505a"

PAD = 0.17             # container inset, fraction of the icon
RADIUS = 0.06          # point radius
CORNER = 0.2           # tile corner radius


def _geometry(points_str):
    pf = [(Fraction(x), Fraction(y)) for x, y in points_str]
    _, ties = minimal_triangles(pf)
    assert TRIANGLE in ties, f"square n={N}: {TRIANGLE} is no longer a minimal triangle"
    w = 1 - 2 * PAD
    return [(PAD + float(x) * w, PAD + (1 - float(y)) * w) for x, y in pf]


def svg(points_str):
    pts = _geometry(points_str)
    f = lambda v: f"{v * 100:.2f}".rstrip("0").rstrip(".")
    tri = " ".join(f"{f(pts[i][0])},{f(pts[i][1])}" for i in TRIANGLE)
    dots = "".join(f'<circle cx="{f(x)}" cy="{f(y)}" r="{f(RADIUS)}"/>' for x, y in pts)
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">'
        f'<rect width="100" height="100" rx="{f(CORNER)}" fill="{BG}"/>'
        f'<rect x="{f(PAD)}" y="{f(PAD)}" width="{f(1 - 2 * PAD)}" height="{f(1 - 2 * PAD)}"'
        f' fill="none" stroke="{EDGE}" stroke-width="3"/>'
        f'<polygon points="{tri}" fill="{ACCENT}"/>'
        f'<g fill="{POINT}">{dots}</g></svg>\n')


def png(points_str, size, rounded=True, outline=True, ss=8):
    """Supersampled raster. Below 32px the container outline is noise."""
    pts = _geometry(points_str)
    s = size * ss
    img = Image.new("RGBA", (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    if rounded:
        d.rounded_rectangle((0, 0, s - 1, s - 1), radius=s * CORNER, fill=BG)
    else:   # iOS masks the corners itself
        d.rectangle((0, 0, s - 1, s - 1), fill=BG)
    if outline:
        d.rectangle((s * PAD, s * PAD, s * (1 - PAD), s * (1 - PAD)),
                    outline=EDGE, width=round(s * 0.03))
    d.polygon([(pts[i][0] * s, pts[i][1] * s) for i in TRIANGLE], fill=ACCENT)
    r = s * RADIUS
    for x, y in pts:
        d.ellipse((x * s - r, y * s - r, x * s + r, y * s + r), fill=POINT)
    return img.resize((size, size), Image.LANCZOS)


def write_icons(points_str, site_dir, root_dir):
    """favicon.svg/.ico and apple-touch-icon.png into the site directory,
    and the .ico and touch icons again at the domain root."""
    ico = [png(points_str, n, outline=n >= 32) for n in (16, 32, 48)]
    touch = png(points_str, 180, rounded=False)
    (site_dir / "favicon.svg").write_text(svg(points_str))
    for d in (site_dir, root_dir):
        ico[-1].save(d / "favicon.ico", sizes=[(16, 16), (32, 32), (48, 48)],
                     append_images=ico[:-1])
        touch.save(d / "apple-touch-icon.png", optimize=True)
    touch.save(root_dir / "apple-touch-icon-precomposed.png", optimize=True)
