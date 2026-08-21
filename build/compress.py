"""Emit .gz and .br siblings for every text asset in dist, so Caddy's
`file_server precompressed` serves compressed bytes with zero CPU."""

import gzip
import pathlib

import brotli

DIST = pathlib.Path(__file__).resolve().parent.parent / "dist"

TEXT_SUFFIXES = {".html", ".css", ".js", ".svg", ".json", ".txt", ".csv", ".xml"}


def compress_all():
    count = 0
    for f in DIST.rglob("*"):
        if not f.is_file() or f.suffix not in TEXT_SUFFIXES:
            continue
        data = f.read_bytes()
        f.with_name(f.name + ".gz").write_bytes(gzip.compress(data, 9))
        f.with_name(f.name + ".br").write_bytes(brotli.compress(data, quality=11))
        count += 1
    return count
