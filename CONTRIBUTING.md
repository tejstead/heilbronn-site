# Contributing a configuration

Found a better arrangement — or have the original coordinates for an entry
this site only shows as a reconstruction? Submissions are plain pull
requests, verified automatically in exact arithmetic.

## What to add

One directory per configuration:

```
data/sources/external/<variant>-nNN/
├── coordinates.txt
└── meta.json
```

`<variant>` is `square`, `triangle`, or `convex`; `NN` is the zero-padded
point count (e.g. `triangle-n15`).

### coordinates.txt

One point per line, two decimal literals separated by whitespace. Lines
starting with `#` are comments.

```
# any comment you like
0.041156363310095543088824043693	0.917687273379808913822351912614
0.041156363310095543088824043693	0.041156363310095543088824043693
```

- **Plain decimals only** — no exponents, no fractions. Literals are parsed
  as exact rationals, so what you write is exactly what is verified.
- **Frames.** `square`: 0 ≤ x, y ≤ 1. `triangle`: the unit right triangle
  x ≥ 0, y ≥ 0, x + y ≤ 1 (values are reported normalized to a unit-area
  triangle, i.e. doubled). `convex`: any coordinates — the domain is the
  points' own convex hull, and the value is area-normalized.
- **Feasibility is checked exactly.** A point at `0.9999999999…` with 200
  digits is fine; a point at `1.0000000001` is not. When rounding interior
  results for the triangle, truncate toward zero so sums stay ≤ 1.
- More digits are better: sources are ranked by the exact value their
  literals achieve, and a 30-decimal literal of a converged optimum will
  beat a 6-decimal one of the same arrangement.

### meta.json

```json
{
 "ref": "where these coordinates come from (paper, repo, 'found by hand')",
 "credit": "Your Name, August 2026",
 "note": "anything the configuration page should say about them"
}
```

`ref` is required; `credit` and `note` are optional but encouraged. The
`note` is shown on the configuration's page, so write it for readers.

## What happens on the PR

A workflow re-verifies every changed submission with the site's exact
verifier — all C(n,3) triples in rational arithmetic — and comments on the
PR with the exact value, the tie count, and how it compares to the current
canonical entry. Invalid submissions (infeasible, malformed, wrong point
count) fail the check.

Submissions are reviewed by the maintainer before merging. Contributors
listed in `.github/trusted-submitters.txt` skip review: their PRs merge
automatically once verification passes — but only when the PR touches
nothing but submission directories. Any change to code, templates, or
curated data always requires review.

A submission that verifies but scores **below** the current value is still
welcome when it has provenance value — for example an original author's
arrangement for an entry we only have as a reconstruction. Say so in the
`note`.

After merge, `build/ingest.py` picks the best source per entry by exact
value, regenerates `data/canonical/`, and the site rebuilds and deploys
automatically — your configuration is live within about ten minutes.

## Notes, corrections, references

Not everything needs coordinates. Corrections to credits, history, or notes
are PRs against `data/curated/` (`overrides.json`, `changelog.json`,
`references.json`) — see the existing entries for the shape. These are
reviewed by hand rather than by the verifier.

## Local check

```
make check-submission DIRS=data/sources/external/<variant>-nNN
make test
```
