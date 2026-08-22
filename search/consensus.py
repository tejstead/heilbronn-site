"""Consensus ladder: extend n with a robustness-based 3-vote stopping rule.

Two kinds of parallel streams per case:

  DISCOVERY (fresh / boundary / grow): independent multistart + basin-hopping,
  as before. Their job is to find the champion and to look for *different*
  topologies that might beat it.

  CONFIRMATION: start from the current champion hit with a STRONG scramble
  (teleport 3-5 points, shake the rest, scale ~0.05-0.1), then search freely
  for the full stream duration. A confirmation stream VOTES FOR the champion
  if it climbs back to within RTOL of the champion value without finding
  anything better.

Stopping rule (per case): champion has >= CONSENSUS confirmation votes.
Any stream (either kind) that BEATS the champion replaces it and resets the
vote count — votes only ever certify the current champion. No stream cap;
discovery pressure continues in every batch. Batch stream length escalates
30% per batch without consensus.

Ledger (timings.json): compute seconds, streams, votes, consensus status.

Usage: consensus.py NMAX [VARIANTS] [STREAM_SECS_BASE] [NMIN]
"""

import json
import multiprocessing as mp
import os
import sys
import time
import numpy as np

from heil import polish, random_config, value, save_result, load_result, project
from attack import mutate

RTOL = 1e-8
CONSENSUS = 3
BATCH = 12          # streams per parallel batch (= workers)
N_CONFIRM = 6       # confirmation streams per batch (rest = discovery)
ESCALATE = 1.3
FLAVORS = ["fresh", "boundary", "grow"]
LEDGER = "timings.json"


def scramble(X, rng, variant):
    """Strong perturbation: teleport 3-5 points, shake the rest hard."""
    X = X.copy()
    n = len(X)
    k = int(rng.integers(3, 6))
    idx = rng.choice(n, size=k, replace=False)
    X[idx] = random_config(k, variant, rng, boundary_bias=0.5)
    rest = np.setdiff1d(np.arange(n), idx)
    X[rest] += rng.normal(0, rng.uniform(0.05, 0.1), (len(rest), 2))
    return project(X, variant) if variant != "convex" else X


def stream(variant, n, seconds, seed, kind, champion, q):
    """One stream. kind: 'fresh'|'boundary'|'grow' (discovery) or 'confirm'."""
    rng = np.random.default_rng(seed)
    best_v, best_X = -1.0, None
    cur_X, cur_val = None, -1.0
    t_end = time.time() + seconds

    champ_X = None if champion is None else np.array(champion)
    grow_seed = None
    if kind == "grow":
        below = f"results/{variant}/n{n-1}.json"
        if os.path.exists(below):
            grow_seed = np.array(load_result(below)["points"])

    fails = 0
    while time.time() < t_end:
        if cur_X is None or rng.random() < 0.08 or fails > 50:
            if kind == "confirm" and champ_X is not None:
                X0 = scramble(champ_X, rng, variant)
            elif kind == "grow" and grow_seed is not None and rng.random() < 0.7:
                c = random_config(1, variant, rng, boundary_bias=0.5)[0]
                X0 = np.vstack([grow_seed, c])
            else:
                bb = 0.6 if kind == "boundary" else rng.choice([0.0, 0.3, 0.6])
                X0 = random_config(n, variant, rng, boundary_bias=bb)
            fails = 0
        else:
            X0 = mutate(cur_X, rng, variant)
        try:
            X1, v1 = polish(X0, variant)
        except Exception:
            continue
        if v1 > cur_val + 1e-13:
            cur_X, cur_val = X1, v1
            fails = 0
            if v1 > best_v:
                best_v, best_X = v1, X1.copy()
        else:
            fails += 1
    q.put((seed, kind, best_v, None if best_X is None else best_X.tolist()))


def run_case(variant, n, stream_secs, led):
    t0 = time.time()
    streams_run = 0
    secs = stream_secs
    path = f"results/{variant}/n{n}.json"

    champ_v, champ_X = -1.0, None
    if os.path.exists(path):
        rec = load_result(path)
        champ_v, champ_X = rec["value"], np.array(rec["points"])
    votes = 0

    while True:
        q = mp.Queue()
        procs = []
        for w in range(BATCH):
            seed = int.from_bytes(os.urandom(4), "little")
            if w < N_CONFIRM and champ_X is not None:
                kind = "confirm"
            else:
                kind = FLAVORS[w % len(FLAVORS)]
            p = mp.Process(target=stream,
                           args=(variant, n, secs, seed, kind,
                                 None if champ_X is None else champ_X.tolist(), q))
            p.start()
            procs.append(p)
        batch = []
        for _ in procs:
            batch.append(q.get())
        for p in procs:
            p.join()
        streams_run += BATCH

        for seed, kind, v, Xl in batch:
            if Xl is None:
                continue
            if v > champ_v * (1 + RTOL):
                champ_v, champ_X = v, np.array(Xl)
                votes = 0  # new champion: previous votes are void
        # count votes for the (possibly new) champion from this batch
        for seed, kind, v, Xl in batch:
            if kind == "confirm" and Xl is not None and v >= champ_v * (1 - RTOL):
                votes += 1

        print(f"  {variant} n={n}: {streams_run} streams (batch {secs:.0f}s), "
              f"champion {champ_v:.10f}, votes {votes}", flush=True)
        if votes >= CONSENSUS:
            status = f"confirmed-{votes}/{streams_run}"
            break
        secs *= ESCALATE

    champ_X, champ_v = polish(champ_X, variant, r0=0.01)
    old = load_result(path)["value"] if os.path.exists(path) else -1
    if champ_v > old + 1e-12:
        save_result(path, variant, n, champ_X, champ_v,
                    meta={"method": "consensus", "status": status})
    stored = max(champ_v, old)

    dt = time.time() - t0
    key = f"{variant}_n{n}"
    ent = led.setdefault(key, {"compute_seconds": 0.0, "history": []})
    ent["compute_seconds"] += dt
    ent["value"] = stored
    ent["consensus"] = status
    ent["streams"] = ent.get("streams", 0) + streams_run
    ent["history"].append({"added_seconds": round(dt, 1), "value": stored,
                           "streams": streams_run, "status": status})
    json.dump(led, open(LEDGER, "w"), indent=1, sort_keys=True)
    print(f"LEDGER {variant} n={n}: {stored:.10f}  [{status}]  +{dt:.0f}s "
          f"(total {ent['compute_seconds']:.0f}s)", flush=True)


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    variants = sys.argv[2].split(",") if len(sys.argv) > 2 else ["square", "triangle", "convex"]
    base = float(sys.argv[3]) if len(sys.argv) > 3 else 240.0
    nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 21

    led = json.load(open(LEDGER)) if os.path.exists(LEDGER) else {}
    for n in range(nmin, nmax + 1):
        stream_secs = base * (n / 20.0) ** 2.2
        for variant in variants:
            run_case(variant, n, stream_secs, led)
    print("CONSENSUS LADDER DONE", flush=True)
