"""Process-pool map for the per-entry build stages. Every job is a pure
function of its input (it may write its own output file), and results come
back in input order, so the build's output does not depend on the number
of workers."""

import os


def jobs():
    """Worker processes: HEILBRONN_JOBS, else the CPU count.
    HEILBRONN_JOBS=1 runs everything in the calling process."""
    try:
        return max(1, int(os.environ.get("HEILBRONN_JOBS", "")))
    except ValueError:
        return os.cpu_count() or 1


def pmap(fn, items, chunksize=1):
    """list(map(fn, items)) across jobs() processes, in input order. fn must
    be a module-level function (spawned workers import it by name)."""
    items = list(items)
    if jobs() == 1 or len(items) < 2:
        return [fn(it) for it in items]
    import concurrent.futures
    import multiprocessing
    ctx = multiprocessing.get_context("spawn")
    with concurrent.futures.ProcessPoolExecutor(min(jobs(), len(items)),
                                                mp_context=ctx) as ex:
        return list(ex.map(fn, items, chunksize=chunksize))
