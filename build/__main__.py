import argparse

from .build import run

# The guard matters: the per-entry stages use spawned worker processes,
# which import the main module again.
if __name__ == "__main__":
    ap = argparse.ArgumentParser(prog="python -m build")
    ap.add_argument("--stage", action="append",
                    choices=["ingest", "render", "downloads", "compress", "check"],
                    help="run only the given stage(s); default: all")
    args = ap.parse_args()
    run(args.stage)
