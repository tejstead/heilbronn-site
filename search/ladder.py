"""Ladder extension campaign: push n upward one rung at a time, recording compute time.

For each (variant, n):
  1. seed from the n-1 best via point insertion (grow-style) — cheap, good topology
  2. parallel fresh-multistart + basin-hopping attack (attack.worker) for the budget
  3. accumulate wall-clock seconds into results meta and timings.json

Budget per case scales with n (polish cost ~ n^2.2). Resumable: re-running adds
time to existing cases; already-good solutions are kept.

Usage: ladder.py NMAX [BASE_BUDGET_SECONDS] [VARIANTS]
"""

import json
import os
import sys
import time
import numpy as np

from attack import main as attack_main
from grow import grow
from heil import load_result

LEDGER = "timings.json"


def load_ledger():
    if os.path.exists(LEDGER):
        return json.load(open(LEDGER))
    return {}


def save_ledger(led):
    json.dump(led, open(LEDGER, "w"), indent=1, sort_keys=True)


def record(led, variant, n, seconds, value):
    key = f"{variant}_n{n}"
    ent = led.setdefault(key, {"compute_seconds": 0.0, "history": []})
    ent["compute_seconds"] += seconds
    ent["value"] = value
    ent["history"].append({"added_seconds": round(seconds, 1),
                           "value": value})
    save_ledger(led)


def run_case(variant, n, budget, led):
    t0 = time.time()
    # step 1: grow seeds from neighbors (bounded slice of the budget)
    try:
        grow(variant, n, seconds=min(60 + 4 * n, budget * 0.25))
    except Exception as e:
        print(f"  grow failed for {variant} n={n}: {e}", flush=True)
    # step 2: parallel attack for the rest
    remaining = budget - (time.time() - t0)
    if remaining > 30:
        attack_main(variant, n, remaining, workers=12)
    dt = time.time() - t0
    val = load_result(f"results/{variant}/n{n}.json")["value"]
    record(led, variant, n, dt, val)
    print(f"LEDGER {variant} n={n}: value {val:.10f}, +{dt:.0f}s "
          f"(total {led[f'{variant}_n{n}']['compute_seconds']:.0f}s)", flush=True)


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    base = float(sys.argv[2]) if len(sys.argv) > 2 else 420.0
    variants = sys.argv[3].split(",") if len(sys.argv) > 3 else ["square", "triangle", "convex"]

    led = load_ledger()
    for n in range(21, nmax + 1):
        # budget scales with polish cost ~ (n/20)^2.2
        budget = base * (n / 20.0) ** 2.2
        for variant in variants:
            run_case(variant, n, budget, led)
    print("LADDER DONE", flush=True)
