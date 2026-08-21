"""Independent search for the four rows whose record figures are stale:
square/18 (D2 label), square/25 (asymmetric), convex/32 (D8 label),
convex/35 (asymmetric). Seeds the search toolkit's results/ from our current
canonical best, runs sym-restricted searches for the symmetric rows and
parallel basin-hopping (attack.py) for the rest, then accepts anything that
beats the current coordinates."""
import json, pathlib, subprocess, sys, os
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
CLONE = pathlib.Path(sys.argv[1])
SEARCH = CLONE / "search"
BUDGET = int(sys.argv[2]) if len(sys.argv) > 2 else 1800
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(SEARCH))

TARGETS = [("square", 18), ("square", 25), ("convex", 32), ("convex", 35)]

# 1. seed results/ from canonical
import heil  # from the clone's search dir
for v, n in TARGETS:
    doc = json.loads((ROOT / "data" / "canonical" / v / f"n{n:02d}.json").read_text())
    X = np.array([[float(a), float(b)] for a, b in doc["points"]])
    path = SEARCH / "results" / v / f"n{n}.json"
    if not path.exists() or heil.load_result(path)["value"] < float(doc["value"]["decimal"][:17]):
        heil.save_result(str(path), v, n, X, float(doc["value"]["decimal"][:17]),
                         meta={"seed": "heilbronn-site canonical"})
        print(f"seeded {v}/{n}", flush=True)

# 2. sym searches for the labeled rows (write into results/ if better)
import sym as symmod
def sym_hunt(variant, n, gname, seconds):
    v, X = symmod.search_sym(variant, n, gname, seconds=seconds, seed=11, verbose=True)
    if X is None:
        return
    path = SEARCH / "results" / variant / f"n{n}.json"
    best = heil.load_result(path)["value"]
    if v > best:
        heil.save_result(str(path), variant, n, X, v, meta={"seed": f"sym {gname}"})
        print(f"sym {variant}/{n} {gname}: improved to {v:.12f}", flush=True)
    else:
        print(f"sym {variant}/{n} {gname}: best {v:.12f} (have {best:.12f})", flush=True)

procs = []
env = dict(os.environ)
for v, n in [("square", 25), ("convex", 35), ("square", 18)]:
    p = subprocess.Popen([sys.executable, "attack.py", v, str(n), str(BUDGET), "2"],
                         cwd=SEARCH, env=env)
    procs.append(p)

sym_hunt("convex", 32, "rot8", BUDGET * 0.4)
sym_hunt("square", 18, "rot2", BUDGET * 0.4)
for p in procs:
    p.wait()

# 3. accept pass
import importlib.util
spec = importlib.util.spec_from_file_location("rec", ROOT / "reconstruct" / "reconstruct.py")
rec = importlib.util.module_from_spec(spec); spec.loader.exec_module(rec)
import refine
from fractions import Fraction
from build.ingest import latest_snapshot
from build.vendor.verify_exact import verify
from build.derive import detect_symmetry, friedman_label
snap = latest_snapshot()
for v, n in TARGETS:
    r = heil.load_result(SEARCH / "results" / v / f"n{n}.json")
    doc = json.loads((ROOT / "data" / "canonical" / v / f"n{n:02d}.json").read_text())
    beat = Fraction(doc["value"]["fraction"])
    X = np.array(r["points"])
    X, val_f = refine.tighten(X, v)
    pts = rec.truncate_repair(X, v)
    res = verify(v, pts)
    val = res["_value"]
    if not res["feasible"] or val <= beat:
        print(f"{v}/{n}: no improvement ({float(val):.12f} vs {float(beat):.12f})", flush=True)
        continue
    entry = snap["variants"][v][str(n)]
    det = detect_symmetry(v, [(float(a), float(b)) for a, b in pts])
    lab = friedman_label(det, v)
    result = {"points": pts, "verify": res, "value": val,
              "detected_symmetry": det, "detected_label": lab,
              "sym_match": rec._labels_compatible(lab, entry["symmetry"])}
    rec.write_out(v, n, entry, result, f"independent search (sym/basin-hopping, {BUDGET}s)", behind=True)
    print(f"{v}/{n}: ACCEPTED {float(val):.12f} (beat {float(beat):.12f}), detected {lab!r} vs page {entry['symmetry']!r}", flush=True)
