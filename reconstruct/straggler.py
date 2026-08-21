"""Heavy round for BEHIND rows that resisted plain figure re-polish:
jittered image seeds + symmetry-restricted search + free multistart."""
import sys, pathlib, json, time
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(ROOT / "build" / "vendor"))
import importlib.util
spec = importlib.util.spec_from_file_location("rec", ROOT / "reconstruct" / "reconstruct.py")
rec = importlib.util.module_from_spec(spec); spec.loader.exec_module(rec)
import heil, sym, refine
from fractions import Fraction
from build.ingest import latest_snapshot

IMGDIR = sys.argv[1]
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 240.0
snap = latest_snapshot()

targets = []
for v in ("square", "triangle", "convex"):
    for n in range(3, 36):
        p = ROOT / "data" / "canonical" / v / f"n{n:02d}.json"
        if not p.exists():
            continue
        doc = json.loads(p.read_text())
        if doc.get("page_relation") == "BEHIND":
            targets.append((v, n, Fraction(doc["value"]["fraction"])))

print(f"{len(targets)} straggler(s)")
rng = np.random.default_rng(123)
for v, n, beat in targets:
    entry = snap["variants"][v][str(n)]
    label = entry["symmetry"] or ""
    t0 = time.time()
    best_v, best_X = -1.0, None

    seeds = rec.image_seeds(v, n, IMGDIR)
    deadline = time.time() + BUDGET * 0.5
    round_i = 0
    while time.time() < deadline and seeds:
        for name, P in seeds:
            Q = P if round_i == 0 else P + rng.normal(0, 0.004, P.shape)
            try:
                X, val = heil.polish(Q, v)
            except Exception:
                continue
            if val > best_v:
                best_v, best_X = val, X.copy()
                print(f"  {v}/{n} seed {name} r{round_i}: {val:.10f}", flush=True)
            if time.time() > deadline:
                break
        round_i += 1

    gname = rec.sym_group_for(v, n, label)
    if gname:
        try:
            val, X = sym.search_sym(v, n, gname, seconds=BUDGET * 0.25, seed=5)
            if X is not None and val > best_v:
                best_v, best_X = val, X
                print(f"  {v}/{n} sym {gname}: {val:.10f}", flush=True)
        except Exception as e:
            print(f"  sym fail: {e}", flush=True)

    t_end = time.time() + BUDGET * 0.25
    while time.time() < t_end:
        X0 = heil.random_config(n, v, rng, boundary_bias=float(rng.choice([0.0, 0.4])))
        try:
            X, val = heil.polish(X0, v)
        except Exception:
            continue
        if val > best_v:
            best_v, best_X = val, X.copy()

    if best_X is None:
        print(f"{v}/{n}: nothing found", flush=True)
        continue
    best_X, best_v = refine.tighten(best_X, v)
    pts = rec.truncate_repair(best_X, v)
    from build.vendor.verify_exact import verify
    res = verify(v, pts)
    val = res["_value"]
    if not res["feasible"] or val <= beat:
        print(f"{v}/{n}: best {float(val):.12f} does not beat {float(beat):.12f} "
              f"in {time.time()-t0:.0f}s", flush=True)
        continue
    from build.derive import detect_symmetry, friedman_label
    det = detect_symmetry(v, [(float(a), float(b)) for a, b in pts])
    lab = friedman_label(det, v)
    result = {"points": pts, "verify": res, "value": val,
              "detected_symmetry": det, "detected_label": lab,
              "sym_match": rec._labels_compatible(lab, label)}
    rec.write_out(v, n, entry, result, "straggler round: jittered image seeds + sym + multistart",
                  behind=True)
    print(f"{v}/{n}: ACCEPTED {float(val):.12f} (beat {float(beat):.12f}) "
          f"in {time.time()-t0:.0f}s, detected {lab!r} vs page {label!r}", flush=True)
