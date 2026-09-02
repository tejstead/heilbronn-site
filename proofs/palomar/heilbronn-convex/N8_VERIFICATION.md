# Historical convex Heilbronn n = 8 verification record

> **Historical checkpoint.** This document records the earlier n = 8-only
> package and the exact hashes used for that run. It does not verify the current
> unified n = 3 through n = 8 package, whose Challenge, Comparator surface, and
> source hashes differ. See `README.md` for the unified package's current
> verification status.

Verification date: 2026-09-02

## Selected result

The n = 8-only Palomar Comparator configuration selected these declarations from
`Solution.N8`:

- `HeilbronnChallenge.P8_root_existsUnique`
- `HeilbronnChallenge.heilbronn_convex_eight`
- `HeilbronnChallenge.heilbronn_convex_eight_attained`
- `HeilbronnChallenge.heilbronn_convex_eight_lower_bound`

The exact-value declaration proves the unconditional theorem
`h_convex 8 = v8`. Each selected declaration depends only on the permitted
axioms `propext`, `Quot.sound`, and `Classical.choice`.

## Local build and source audit

The final optimized source passed the following checks under Lean 4.33.1 and
the pinned Mathlib manifest:

- `lake build Solution.N8`: all 9,039 jobs completed in 931.13 seconds, with a
  maximum resident set size of 7,724,433,408 bytes.
- `lake env lean -t 0 Solution/N8.lean`: completed in 6.19 seconds.
- `scripts/palomar_audit.sh`: all ten local policy and source checks passed.
  Before this record was added, the submitted source tree contained 4,703,900
  bytes outside `.lake` and contained no compiled artifacts outside `.lake`.

The selected proof closure contains no unresolved proof placeholders, extra
assumptions, non-kernel evaluation proof primitives, or unchecked
declarations. Its two explicit `decide +kernel` uses request ordinary kernel
reduction.

## Comparator and independent kernels

The verification used these exact tool revisions:

- Palomar Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494`
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- lean4export: `15f6055e299ad5b89345e533cc2192f4cc00f659`

Comparator was run unpiped with NanoDa forced on. Its final output was:

```text
nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The complete Comparator run took 2,698.84 seconds and reported a maximum
resident set size of 9,996,926,976 bytes and zero swaps.

The local macOS run used a no-op replacement for the Linux-only Landrun
sandbox. This changes local process isolation only. It does not change the
Comparator revision, exported declarations, axiom checks, NanoDa replay, or
Lean default-kernel replay. The Palomar service's Linux run remains the
authoritative sandboxed reproduction.

## Frozen input hashes

The Comparator run used these package inputs:

```text
3d392751c91daf9468cda5c0498a68c0b8bf640237a71597b2aff85dd1f7dd48  HeilbronnChallenge.lean
cf82933fcf026d33b28f77ec5b344415af1ae0a552cf6bd1abb6ce15881da936  Solution/N8.lean
212776274350a97d863992fd3ba618500068e6b435af08ca2a994a1f7eb903d1  comparator.json
3d3c71f240ab6a9420b4225ea10eab5792625e7e4ebd57738260ce65d9bae7a2  lakefile.toml
f6a80d6db39cd4233c4bac00b5289d12b478e9bef3b5b829e6d13fc307e350d6  lake-manifest.json
```
