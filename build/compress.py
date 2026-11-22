"""Emit .gz and .br siblings for every text asset in dist, so Caddy's
`file_server precompressed` serves compressed bytes with zero CPU."""

import gzip
import pathlib

import brotli

from .parallel import pmap

DIST = pathlib.Path(__file__).resolve().parent.parent / "dist"

TEXT_SUFFIXES = {".html", ".css", ".js", ".svg", ".json", ".txt", ".csv", ".xml"}


def _compress_one(path):
    f = pathlib.Path(path)
    data = f.read_bytes()
    f.with_name(f.name + ".gz").write_bytes(gzip.compress(data, 9))
    f.with_name(f.name + ".br").write_bytes(brotli.compress(data, quality=11))


def compress_all():
    files = sorted(str(f) for f in DIST.rglob("*")
                   if f.is_file() and f.suffix in TEXT_SUFFIXES)
    pmap(_compress_one, files, chunksize=16)
    return len(files)
