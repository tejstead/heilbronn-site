"""One-off: symmetric re-polish for reconstructions that lost their published
symmetry in free polish, plus custom digitization for hc16.gif."""
import sys, pathlib, json
import numpy as np
from scipy import ndimage
from PIL import Image

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(ROOT / "build" / "vendor"))
import importlib.util
spec = importlib.util.spec_from_file_location("rec", ROOT / "reconstruct" / "reconstruct.py")
rec = importlib.util.module_from_spec(spec); spec.loader.exec_module(rec)
import heil, sym, refine
from build.ingest import latest_snapshot
from build.vendor.verify_exact import verify, parse_points_text
from build.derive import detect_symmetry, friedman_label

snap = latest_snapshot()

def accept(variant, n, X, tag):
    entry = snap["variants"][variant][str(n)]
    pts = rec.truncate_repair(X, variant)
    res = verify(variant, pts)
    v = res["_value"]
    win = rec.published_window(entry)
    exact = rec.EXACT.get((variant, n))
    if exact is not None and abs(float(v)/exact - 1) > 1e-9:
        print(f"{variant}/{n} [{tag}]: missed exact ({float(v):.12f})", flush=True); return False
    if exact is None and win and not (win[0] <= v < win[1]):
        print(f"{variant}/{n} [{tag}]: outside window ({float(v):.12f})", flush=True); return False
    if not res["feasible"]:
        print(f"{variant}/{n} [{tag}]: infeasible", flush=True); return False
    det = detect_symmetry(variant, [(float(a), float(b)) for a, b in pts])
    lab = friedman_label(det, variant)
    result = {"points": pts, "verify": res, "value": v,
              "detected_symmetry": det, "detected_label": lab,
              "sym_match": rec._labels_compatible(lab, entry["symmetry"])}
    rec.write_out(variant, n, entry, result, tag)
    print(f"{variant}/{n} [{tag}]: ACCEPTED {float(v):.12f}, detected {lab!r} vs page {entry['symmetry']!r}", flush=True)
    return True

def symmetrize(X, variant, gname, stages=(0.02, 0.003, 5e-4, 8e-5, 1.2e-5, 2e-6)):
    els, fix = sym.group(variant, gname)
    g = len(els); n = len(X)
    X = np.array(X, float)
    if variant == "convex":
        X = X - X.mean(0)
    center = None; Xr = X
    if n % g == 1:
        ci = int(np.argmin(((X - fix) ** 2).sum(1)))
        center = fix
        Xr = np.delete(X, ci, axis=0)
    A1, o1 = els[1]
    rem = list(range(len(Xr))); orbits = []
    while rem:
        i = rem.pop(0); orbit = [i]; cur = Xr[i]
        for _ in range(g - 1):
            img = A1 @ cur + o1
            j = min(rem, key=lambda k: ((Xr[k] - img) ** 2).sum())
            orbit.append(j); rem.remove(j); cur = Xr[j]
        orbits.append(orbit)
    U = []
    for orbit in orbits:
        acc = np.zeros(2)
        for k, idx in enumerate(orbit):
            A, o = els[k]
            acc += np.linalg.solve(A, Xr[idx] - o)
        U.append(acc / g)
    U = np.array(U)
    Xs = None; v = -1
    for r0 in stages:
        U, Xs, v = sym.polish_sym(U, variant, els, center, r0=r0)
        print(f"  polish_sym r0={r0}: {v:.12f}", flush=True)
    return Xs, v

def load_rec(tag):
    pts = parse_points_text((ROOT / "data/sources/reconstructed" / tag / "coordinates.txt").read_text())
    return np.array([[float(a), float(b)] for a, b in pts])

if __name__ == "__main__":
    which = sys.argv[1:] or ["t15", "c11", "c16"]
    if "t15" in which:
        Xs, v = symmetrize(load_rec("triangle-n15"), "triangle", "rot3")
        accept("triangle", 15, Xs, "image seed + C3-symmetric polish")
    if "c11" in which:
        Xs, v = symmetrize(load_rec("convex-n11"), "convex", "rot2")
        accept("convex", 11, Xs, "image seed + C2-symmetric polish")
    if "c16" in which:
        p = pathlib.Path(sys.argv[sys.argv.index("--img") + 1]) if "--img" in sys.argv else \
            pathlib.Path("/private/tmp/claude-501/-Users-tej-Documents-GitHub-heilbronn-site/eb17a1d9-cebc-423b-804c-c53490f90dfb/scratchpad/gifseed/pages/hc16.gif")
        a = np.array(Image.open(p).convert("RGB")).astype(int)
        d = (a.sum(axis=2) < 300)
        cnt = ndimage.uniform_filter(d.astype(float), 3) * 9
        blobby = (cnt >= 5) & d
        lab, n2 = ndimage.label(blobby, structure=np.ones((3, 3)))
        P = [(xx.mean(), yy.mean()) for i in range(1, n2 + 1)
             for yy, xx in [np.where(lab == i)] if len(yy) >= 2]
        P = np.array(P); print("hc16 blobs:", len(P), flush=True)
        X, v = heil.polish(P, "convex")
        X, v = refine.tighten(X, "convex")
        print("convex/16 free-polished:", v, flush=True)
        if not accept("convex", 16, X, "image seed (custom digitization), free polish"):
            Xs, v = symmetrize(X, "convex", "rot4")
            accept("convex", 16, Xs, "image seed + C4-symmetric polish")
