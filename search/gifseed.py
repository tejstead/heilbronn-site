"""Extract approximate point coordinates from Friedman's record GIFs and polish.

The dots are filled black blobs; the domain outline is thin black lines.
Strategy: connected components of near-black pixels; components that are small
and dense (blob-like) are points. Domain frame from outline extremes.

Usage: gifseed.py ht|hc N [suffixes]  e.g.  gifseed.py ht 14 a
"""

import os
import sys
import numpy as np
from PIL import Image
from scipy import ndimage

from heil import polish, value, save_result, load_result


def blobs(path):
    a = np.array(Image.open(path).convert("RGB")).astype(int)
    dark = (a.sum(axis=2) < 200)
    # dots are filled disks ~5-7px wide; outline/triangle edges are 1-2px thin.
    # erosion kills lines but leaves dot cores, even when a dot touches a line.
    core = ndimage.binary_erosion(dark, structure=np.ones((3, 3)), iterations=1)
    lab, nlab = ndimage.label(core)
    pts = []
    for i in range(1, nlab + 1):
        ys, xs = np.where(lab == i)
        h, w = int(ys.max() - ys.min()) + 1, int(xs.max() - xs.min()) + 1
        size = len(ys)
        if 2 <= size <= 60 and max(h, w) <= 10:
            pts.append((xs.mean(), ys.mean()))
    return np.array(pts), dark


def frame(dark):
    """Bounding region of ALL dark pixels (the outline dominates)."""
    ys, xs = np.where(dark)
    return xs.min(), xs.max(), ys.min(), ys.max()


def convex_pts(path, n):
    """Convex GIFs: hull points sit at outline-polygon corners; interior dots
    are separate blobs. Extract corners from the outline component's hull."""
    a = np.array(Image.open(path).convert("RGB")).astype(int)
    for darkthr, cntthr in ((250, 8), (250, 7), (400, 8), (500, 8), (250, 6)):
        dark = (a.sum(axis=2) < darkthr)
        # dot pixels have nearly-full 3x3 dark neighborhoods; outline pixels don't
        cnt = ndimage.uniform_filter(dark.astype(float), 3) * 9
        blobby = (cnt >= cntthr) & dark
        lab, n2 = ndimage.label(blobby, structure=np.ones((3, 3)))
        pts = []
        for i in range(1, n2 + 1):
            yy, xx = np.where(lab == i)
            pts.append((xx.mean(), yy.mean()))
        if len(pts) == n:
            break
    return np.array(pts)


def seed_from_gif(kind, n, suffix):
    path = f"pages/{kind}{n}{suffix}.gif"
    if not os.path.exists(path):
        return None
    if kind == "hc":
        pts = convex_pts(path, n)
        if len(pts) != n:
            print(f"  {path}: found {len(pts)} pts (hull+interior), expected {n} - skip")
            return None
        return pts, "convex"
    pts, dark = blobs(path)
    if len(pts) != n:
        print(f"  {path}: found {len(pts)} blobs, expected {n} - skip")
        return None
    x0, x1, y0, y1 = frame(dark)
    P = pts.copy()
    # normalize; flip y (image y down)
    P[:, 0] = (P[:, 0] - x0) / (x1 - x0)
    P[:, 1] = (y1 - P[:, 1]) / (y1 - y0)
    if kind == "ht":
        # drawn as isoceles-ish triangle with apex top; Friedman's triangle pictures
        # use an equilateral-looking triangle: vertices (0,0),(1,0),(0.5,1) in frame.
        # Map to reference triangle (0,0),(1,0),(0,1): affine from those 3 vertices.
        V = np.array([[0.0, 0.0], [1.0, 0.0], [0.5, 1.0]])
        W = np.array([[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]])
        M = np.linalg.lstsq(np.hstack([V, np.ones((3, 1))]), W, rcond=None)[0]
        P = np.hstack([P, np.ones((len(P), 1))]) @ M
        P = np.clip(P, 0, None)
        s = P.sum(axis=1)
        P[s > 1] /= s[s > 1, None]
        variant = "triangle"
    else:
        variant = "convex"
    return P, variant


def run(kind, n, suffixes="abc"):
    variant = "triangle" if kind == "ht" else "convex"
    best_path = f"results/{variant}/n{n}.json"
    best = load_result(best_path)["value"] if os.path.exists(best_path) else -1
    for sfx in [""] + list(suffixes):
        r = seed_from_gif(kind, n, sfx)
        if r is None:
            continue
        P, variant = r
        try:
            X, v = polish(P, variant)
        except Exception as e:
            print(f"  polish fail {kind}{n}{sfx}: {e}")
            continue
        print(f"  {kind}{n}{sfx}: polished to {v:.10f} (best {best:.10f})")
        if v > best + 1e-12:
            best = v
            save_result(best_path, variant, n, X, v, meta={"seed": f"gif {kind}{n}{sfx}"})
            print("    SAVED")
    return best


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    kind, n = sys.argv[1], int(sys.argv[2])
    run(kind, n, sys.argv[3] if len(sys.argv) > 3 else "abc")
