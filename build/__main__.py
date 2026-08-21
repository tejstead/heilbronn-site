import argparse

from .build import run

ap = argparse.ArgumentParser(prog="python -m build")
ap.add_argument("--stage", action="append",
                choices=["ingest", "render", "downloads", "compress", "check"],
                help="run only the given stage(s); default: all")
args = ap.parse_args()
run(args.stage)
