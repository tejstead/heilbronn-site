# Convex Heilbronn values and optimizers for n = 3 through 8

## Submission layout

This source-only Lean project lives at
`proofs/palomar/heilbronn-convex` inside the public
[`heilbronn-site`](https://github.com/tejstead/heilbronn-site) repository.
A Palomar submission should pin that repository, an exact 40-character commit
SHA, and this project's `comparator.json`. The repository-root MIT license
applies to this nested project.

This directory stages one unified Palomar challenge for the convex-region,
own-hull-normalized Heilbronn problem. It is not the unit-square version of
Heilbronn's problem.

> **Verification status (2026-09-02).** The full `HeilbronnSolution` target
> compiles (9,139 jobs), all 29 compared declarations pass the axiom gate with
> no dependencies beyond `propext`, `Quot.sound`, and `Classical.choice`, and
> the strict nested-source audit passes. A local run of Comparator revision
> `575674928e239f5bc452aab72d1dd7b0f1326494`, using lean4export revision
> `15f6055e299ad5b89345e533cc2192f4cc00f659` and NanoDa revision
> `68d5ca9db226849b41a6fff59d796ff19d0a8840`, completed with NanoDa forced on:
> NanoDa and Lean's default kernel both accepted the solution. The local macOS
> run used an exec-only substitute for Linux `landrun`; the export and both
> kernel checks are genuine, while Palomar's sandboxed Linux rerun remains
> authoritative. The source-only repository is well below the 500 MiB limit.

## Statement and normalization

For an indexed configuration `p : Fin n → ℝ × ℝ`, `minTri p` is the minimum
**doubled** area of a triangle determined by three distinct indices. A score
`r` is admissible when the configuration's own convex hull has Lebesgue area
one and `minTri p = 2 * r`. The value `h_convex n` is the supremum of those
admissible scores.

The challenge compares a pointwise upper bound, attainment, and the exact
supremum for every `n = 3,...,8`. It also compares the indicated optimizer
statement:

| n | exact value | optimizer theorem | provenance |
|---:|:------------|:------------------|:-----------|
| 3 | `1` | pairwise unique | elementary folklore |
| 4 | `1/2` | pairwise unique | elementary folklore |
| 5 | `(5 - sqrt 5)/10` | pairwise unique | candidate recorded by Cantrell; full proof and classification first presented here after a scoped search found no published proof |
| 6 | `1/6` | pairwise unique | published value and sharpness: Dress-Yang-Zeng (1995); independently proved here |
| 7 | `1/9` | exhaustive real family, including a continuum-parameterized inequivalent subfamily | published value and sharpness: Yang-Zeng (1995); independently proved here; family and classification first presented here, with no prior exhaustive classification located in the sources checked |
| 8 | the selected root of `2060x^5 - 2332x^4 + 1064x^3 - 240x^2 + 26x - 1` | pairwise unique | exact value, proof, and classification first presented here; scoped search found no published proof |

Here “pairwise unique” means that any two unit-hull optimizers are related by
an arbitrary relabeling and an arbitrary affine transformation with
**nonzero** determinant. It does not mean equality with a choice-defined
canonical witness.

The n = 5 and n = 8 algebraic values are selected by the compared support
theorems `P5_root_existsUnique` and `P8_root_existsUnique`. The linear values
at n = 3, 4, 6, and 7 need no separate root-support target.

For a mathematician-oriented account of the geometric reductions, sharp
inequalities, equality cases, and the role of finite computation, see
[`PROOF_GUIDE.md`](PROOF_GUIDE.md).

## The n = 7 parameterization

`sevenFamilyAt t` is defined for real `t`.
`heilbronn_convex_seven_family_attains` proves that every parameter in
`[1,4/3]` gives a unit-hull configuration with minimum doubled triangle area
`2/9`. For every unit-hull configuration,
`heilbronn_convex_seven_optimizer_classification` proves the exact equivalence
between attaining `2/9` and being nonsingular-affine-equivalent, up to
relabeling, to one of those family members. Thus the family contains all and
only the normalized optimizers.

The full interval is an exhaustive cover, not an injective parameterization:
the members at `t` and `4/(3*t)` are related by an orientation-reversing affine
map. The selected interval `[6/5,5/4]` avoids these mirror identifications.
The formal exact-parameter argument uses the symmetric sum of squared signed
determinants over all ordered triples. Finally,
`heilbronn_convex_seven_infinite_optimizers` explicitly proves that
`[6/5,5/4]` has cardinality continuum, that every parameter there is a
unit-hull optimizer, and that affine-equivalent members in that interval have
equal parameters. The separate Nat-indexed `sevenFamily` remains in the source
but is not what this selected continuum theorem states. The family and its
classification are not attributed to Yang and Zeng.

## Comparator surface

[`comparator.json`](comparator.json) selects 29 theorems:

- six pointwise unit-hull upper bounds;
- six attainment theorems;
- six exact-value theorems;
- five pairwise optimizer-uniqueness theorems, for n = 3, 4, 5, 6, and 8;
- the n = 7 full-family attainment, real-subinterval inequivalence,
  exhaustive-classification, and continuum-subfamily theorems; and
- the two root-selection support theorems for n = 5 and n = 8.

`definition_names` is intentionally empty because this challenge has theorem
holes, not definition holes. Concrete definitions reached from selected
theorem types—including `minTri`, `h_convex`, the selected values,
`NonsingularAffine`, `NonsingularAffine.map`, `AffineEquivalent`, and
`sevenFamilyAt`—have matching bodies that Comparator checks transitively.
Making them definition targets would instead turn them into Solution-filled
holes. The Nat-indexed family helper definitions are outside the selected
Comparator surface.

[`HeilbronnChallenge.lean`](HeilbronnChallenge.lean) imports only `Mathlib` and
is 274 lines / 10,143 bytes, below the Palomar hard limits and both soft warning
thresholds.

## Provenance and literature limits

<!-- palomar-provenance-route-status: frozen -->

The final imported proof routes have been audited against the cited sources.
The n = 6 determinant/order-type proof and the n = 7 hull-case,
Plücker/Bernstein, and continuant proof are self-contained independent proofs
of the published sharp results, so both 1995 chapters are labeled
`independently-proves`. Neither route imports or adapts a theorem from those
chapters. Gronchi–Longinetti is retained only as relevant background for the
n = 5 affinely regular-polygon context; it is not a dependency of the selected
n = 5, n = 6, or n = 7 proof route.

The published sources are:

- Andreas W. M. Dress, Lu Yang, and Zhenbing Zeng, “Heilbronn Problem for Six
  Points in a Planar Convex Body,” *Minimax and Applications* (1995),
  pp. 173–190, [DOI 10.1007/978-1-4613-3557-3_13](https://doi.org/10.1007/978-1-4613-3557-3_13).
- Lu Yang and Zhenbing Zeng, “Heilbronn Problem for Seven Points in a Planar
  Convex Body,” *Minimax and Applications* (1995), pp. 191–218,
  [DOI 10.1007/978-1-4613-3557-3_14](https://doi.org/10.1007/978-1-4613-3557-3_14).
- Paolo Gronchi and Marco Longinetti, “Affinely Regular Polygons as Extremals
  of Area Functionals,” *Discrete & Computational Geometry* 39 (2008),
  pp. 273–297, [DOI 10.1007/s00454-007-9010-5](https://doi.org/10.1007/s00454-007-9010-5).
- Erich Friedman, [“The Heilbronn Problem for Convex
  Regions”](https://erich-friedman.github.io/packing/heilconvex/), a public
  candidate table crediting the n = 5 and numerical n = 8 configurations to
  David Cantrell in June 2007. It is a record page, not a proof source.

The Dress-Yang-Zeng and Yang-Zeng chapters establish the prior published status
of the selected n = 6 and n = 7 values, respectively; this package does not
formalize their arguments. The accessible Dress-Yang-Zeng abstract is not
treated as evidence for the n = 6 equality classification.
Gronchi-Longinetti proves affine rigidity for maximizers of a polygonal ear
functional, which is related background for the n = 5 convex-position core,
but the selected proof is self-contained and does not invoke that result. The
n = 7 coordinate family is first presented in this development and is not attributed to
Yang-Zeng.

The n = 5 audit found a recorded candidate and relevant polygonal rigidity,
but no published proof covering arbitrary configurations. The n = 8 audit
found numerical candidate records but no exact quintic value, global upper
bound, or optimizer classification. An absence-of-prior-art search cannot
prove absolute novelty, so these are scoped reports of what was checked, not
claims that all mathematical literature has been exhausted.
The detailed n = 8 search record is in
[`LITERATURE_AUDIT.md`](LITERATURE_AUDIT.md).

There is one metadata subtlety. Palomar derives a single `result_origin` from
each Comparator entry. This unified entry selects known results as well as new
ones, so [`formalization.yaml`](formalization.yaml) records the entry as
source-based: the folklore cases and the two 1995 results are
`independently-proves`, while the Gronchi-Longinetti result is `background`. The
new n = 5, n = 7-family/classification, and n = 8 contributions are separately identified by
`type: other` / `relationship: other` entries and by the source notes above.

[`N8_VERIFICATION.md`](N8_VERIFICATION.md) records the earlier n = 8-only
checkpoint. Its Challenge, Comparator surface, and hashes differ, so it does
not verify this unified package.

## Automation and checking

Run the build-free staging audit from the `heilbronn-site` checkout root:

```bash
PALOMAR_REPOSITORY_ROOT="$PWD" \
  ./proofs/palomar/heilbronn-convex/scripts/palomar_audit.sh \
  ./proofs/palomar/heilbronn-convex
```

For the final strict preflight:

```bash
PALOMAR_REPOSITORY_ROOT="$PWD" \
PALOMAR_REQUIRE_COMPLETE_PACKAGE=1 \
PALOMAR_REQUIRE_FROZEN_PROVENANCE=1 \
  ./proofs/palomar/heilbronn-convex/scripts/palomar_audit.sh \
  ./proofs/palomar/heilbronn-convex
```

The audit checks the Challenge caps and import, canonical 29-target surface,
placeholder placement, exact axiom allowlist, forbidden proof mechanisms,
whole-repository hygiene and size, metadata shape, repository-root license,
provenance marker, and transitive local import closure. It is a static audit
and does not replace Comparator or either kernel check.

Claude and OpenAI Codex were used extensively, under human direction, for
proof design, Lean implementation, exact certificate search, literature
search, and review. Finite searches and numerical experiments guided the work,
but every selected theorem terminates in an exact Lean proof. The allowed axiom
set is `propext`, `Quot.sound`, and `Classical.choice`; native evaluation and
custom axioms are excluded.

The staged repository contains no compiled `.olean` or `.ilean` files or Lake
caches; those are build artifacts rather than submission source.
