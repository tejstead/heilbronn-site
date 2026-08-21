"""Leaderboards: current records and optimality proofs, aggregated by person.

Credit strings often name teams ("A. Dress, L. Yang, and Z. B. Zeng"); they
are split into individuals and normalized through ALIASES, because the pages
spell the same person several ways. A shared entry counts fully for each
coauthor. Two weightings: every entry equal, and by the sum of the normalized
record values A — which deliberately weights small n (larger areas) heavily.
Trivial entries carry no credit and are excluded.
"""

import collections
import re

# Formatting variants that appear in the recorded credits, one spelling each.
ALIASES = {
    "l. yang": "Lu Yang",
    "yang lu": "Lu Yang",
    "lu yang": "Lu Yang",
    "z. b. zeng": "Zhenbing Zeng",
    "z. zeng": "Zhenbing Zeng",
    "zeng zhenbing": "Zhenbing Zeng",
    "j. z. zhang": "Jingzhong Zhang",
    "zhang jingzhong": "Jingzhong Zhang",
    "l. chen": "Liangyu Chen",
    "a. dress": "Andreas Dress",
    "f. comellas": "Francesc Comellas",
    "j. yebra": "José Luis Andres Yebra",
}

_SPLIT = re.compile(r",\s*(?:and\s+)?|\s+and\s+")


def split_names(credit):
    raw = [p.strip() for p in _SPLIT.split(credit.strip()) if p.strip()]
    # re-join fragments that were split inside parentheses:
    # "cnemri (AlphaEvolve, Google Cloud)" is one name, not two
    parts, buf = [], ""
    for p in raw:
        buf = f"{buf}, {p}" if buf else p
        if buf.count("(") == buf.count(")"):
            parts.append(buf)
            buf = ""
    if buf:
        parts.append(buf)
    return parts


def canon(name):
    return ALIASES.get(name.lower(), name)


def value_of(doc):
    val = doc["value"]
    for k in ("exact_decimal", "decimal", "published_decimal"):
        if val.get(k):
            try:
                return float(val[k])
            except ValueError:
                pass
    return None


def leaderboards(docs):
    boards = {}
    for kind in ("found", "proved"):
        count = collections.Counter()
        weight = collections.defaultdict(float)
        entries = collections.defaultdict(list)
        for (v, n), doc in sorted(docs.items()):
            credit = doc.get("credit") or {}
            c = credit.get(kind)
            if not c or credit.get("trivial"):
                continue
            val = value_of(doc)
            for name in split_names(c["name"]):
                name = canon(name)
                count[name] += 1
                if val:
                    weight[name] += val
                entries[name].append(f"{v} n={n}")
        rows = [{"name": nm, "count": count[nm], "weight": weight[nm],
                 "entries": ", ".join(entries[nm])} for nm in count]
        boards[kind] = {
            "by_count": sorted(rows, key=lambda r: (-r["count"], -r["weight"], r["name"])),
            "by_weight": sorted(rows, key=lambda r: (-r["weight"], -r["count"], r["name"])),
        }
    return boards
