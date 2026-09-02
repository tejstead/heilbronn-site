# Proof roadmap for the convex Heilbronn problem, $n=3,\ldots,8$

This is a high-level map of the proof, not a line-by-line translation of the
Lean development. Its main purpose is to show the case reductions and the
mathematical tools that close each family.

Write

$$
  [abc]=\det(b-a,c-a),\qquad
  m=\min_{i<j<k}|[p_ip_jp_k]|,\qquad
  D=2\,{\rm area}({\rm conv}\{p_i\}).
$$

Thus $m$ and $D$ are doubled areas, and $m/D$ is the ratio of the
smallest ordinary triangle area to hull area. Nonsingular affine maps scale
both by the same factor. In the challenge $D=2$, so the target inequality is
$m\le2v_n$.

The cases $n=3,4,5$ are comparatively short. For $n=3$, the only triangle
is the hull. For $n=4$, Radon's dichotomy gives either a convex
quadrilateral, where a diagonal proves $2m\le D$, or one point inside a
triangle, where a three-piece fan proves $3m\le D$; equality characterizes
parallelograms. For $n=5$, hull sizes three and four give $5m\le D$ and
$4m\le D$. In the convex-pentagon case, normalize at a least ear and apply
three determinant identities plus $(u-w)^2\ge0$; this gives
$m/D\le(5-\sqrt5)/10$, with equality only for an affinely regular pentagon.
Consequently $v_3=1$, $v_4=1/2$, and
$v_5=(5-\sqrt5)/10$; in each case the optimizer is unique up to relabeling
and a nonsingular affine map.
The formal routes are [Solution/N3.lean](Solution/N3.lean),
[Solution/N4.lean](Solution/N4.lean), and
[Heil5/Pentagon.lean](Heil5/Pentagon.lean); the equality classification is
in [Heil5/Structure.lean](Heil5/Structure.lean) and
[Solution/N5Unique.lean](Solution/N5Unique.lean).

## The common proof pattern

For $n=6,7,8$, the development repeats the same five moves.

1. If $m=0$, the bound is immediate. Otherwise every triple is
   noncollinear.
2. Relabel the extreme points into strict counterclockwise order and split by
   the number $h$ of hull vertices.
3. Express $D$ by a fan triangulation and regard every other triangle as a
   determinant constrained by the floor $|[ijk]|\ge m$.
4. Close each hull-size branch by counting, a determinant identity, or an
   exact scalar inequality.
5. Rerun the routing with equality. Strict branches disappear; the surviving
   bracket table reconstructs the optimizer modulo relabeling and affine
   transformation.

The main closure tools are:

| tool | role in this proof | reference |
|:---|:---|:---|
| Radon's theorem | starts the small hull classifications | [Radon (1921)](https://eudml.org/doc/158861); formal determinant version in [HullBridge.lean](HullBridge.lean) |
| Grassmann–Plücker relations | transfer area floors and constrain realizable sign patterns | standard oriented-matroid context: [Björner et al., *Oriented Matroids*](https://www.cambridge.org/core/books/oriented-matroids/contents/8B04A2CADCD27088D3D6013B87D771C4); identities are reproved directly in Lean |
| fan counting and AM–GM | close most nonsharp packets | elementary; implemented as exact determinant and polynomial lemmas |
| Bernstein-basis positivity | certifies a few bounded polynomial subproblems | background: [Lorentz, *Bernstein Polynomials*](https://bookstore.ams.org/CHEL/323); all coefficients and soundness proofs are embedded in Lean |
| affine-frame reconstruction | two signed areas against a nondegenerate frame locate a point | formalized in [HullBridge.lean](HullBridge.lean) |

These citations give context for the named tools. The Lean proof does not
import any mathematical conclusion from them.

## Six points

The target is

$$
  6m\le D.
$$

[canonicalHullCase6_complete](Heil6/FiniteHullCases.lean) reduces every
nondegenerate configuration to one of four hull packets.

| $h$ | remaining points | closing argument |
|---:|:---|:---|
| 3 | three interior | a subdivision into seven configuration triangles gives $7m\le D$ |
| 4 | two interior | split along a diagonal; if $k$ points lie on one side, the two triangle bounds have coefficients $2k+1$ and $2(2-k)+1$, totaling $6$ |
| 5 | one interior | under $D\le6m$, the radial diagonal signs are, up to rotation, all nonnegative, one negative, or two adjacent negatives; ear floors and five Plücker relations contradict every type |
| 6 | none | three complementary bracket pairs and three cyclic Plücker products imply $P<Q<R_c<P$ if $D<6m$ |

The packet assembly is
[six_mul_floor_le_doubledHullArea](Heil6/HullPacketBounds.lean). The genuinely
sharp scalar endpoint is [cycle_bound](Heil6/HexagonScalar.lean). Its key
elementary sublemma says that if positive $x,y$ satisfy $x+y<4m$ and
$m(x+y)\le K$, then $(x-y)^2\ge0$ gives $xy<K$. Applied cyclically,
this is exactly what produces the impossible chain in the last row.

Equality is strict in the three- and five-hull packets and impossible in the
four-hull packet. In the convex hexagon, the nonstrict cyclic argument forces
all six ears to equal $m$, an alternating triangle to equal $3m$, and the
six intermediate brackets to equal $2m$. Those values reconstruct the
remaining vertices from an affine frame, proving one optimizer class. The
rational witness has hull area one and $m=1/3$, so
$h_{\rm convex}(6)=1/6$. See [N6Upper.lean](Heil6/N6Upper.lean) and
[N6UniqueCore.lean](Heil6/N6UniqueCore.lean).

The value $1/6$ was previously published by Dress, Yang, and Zeng,
[“Heilbronn Problem for Six Points in a Planar Convex
Body”](https://doi.org/10.1007/978-1-4613-3557-3_13) (1995). The route above
is a self-contained independent proof, not a formalization of that chapter.

## Seven points

Here the target is

$$
  9m\le D.
$$

[hullClassified_all](Heil7/CanonicalHullClassification7.lean) gives five
hull-size branches.

| $h$ | remaining points | subcases and closer |
|---:|:---|:---|
| 3 | four interior | the interior-point count $(2\cdot4+1)m\le D$ proves the bound; at equality three of the four points acquire odd fan-area codes, but each code has at most one compatible partner, so the branch is strict |
| 4 | three interior | diagonal occupancies $3+0$ and $2+1$ close using the local three-point coefficient $17/2$ and the two-point coefficient $4+2\sqrt3>7$ |
| 5 | two interior | the points miss a common ear; the complementary quadrilateral contributes at least $8m$ and the ear contributes $m$ |
| 6 | one interior | for $d_i=[R,C_i,C_{i+2}]$, sign reduction leaves all $d_i>0$ (with alternating or block long-chord signs), one negative, two consecutive negatives, or four negatives; product inequalities close the all-positive and two-negative cases, an exact $14\times66=924$ Bernstein table closes the one-negative case, and four negatives gives $10m\le D$ directly |
| 7 | none | repeated Plücker relations form a length-four continuant from the five fan triangles; ear caps and endpoint monotonicity give a strict $9m$ bound |

The five branches are assembled by
[hullCaseBounds_proved](Heil7/N7UpperFinal.lean). Representative closers are
[hullThree_counting](Heil7/Hull3CountingRoute.lean),
[hullFour_of_triangleInputs](Heil7/Hull45Core.lean),
[pentagon_common_complementary_quad](Heil7/Hull5PentagonRoute.lean),
[h6_bracket_core_proved](Heil7/Hull6BracketCoreProof.lean), and
[hullSeven_of_continuant](Heil7/Hull7ContinuantRoute.lean).

For equality, the $h=3,4,5,7$ arguments have strict versions, so only the
six-hull branch survives. Its unique tight sign orbit has every $d_i>0$
and alternating $c_i$. The equality equations leave one parameter
$\lambda\in[3/2,2]$, or equivalently $t=2/\lambda\in[1,4/3]$.
This produces the explicit family `sevenFamilyAt t`.

[heilbronn_convex_seven_family_attains](Heil7/N7OptimizerClassificationFinal.lean)
proves that every member of that interval has unit hull and $m=2/9$;
[heilbronn_convex_seven_optimizer_classification](Heil7/N7OptimizerClassificationFinal.lean)
proves that every optimizer is affinely equivalent, after relabeling, to a
member. Finally,
[sevenFamilyAt_affineEquivalent_iff](Heil7/N7FamilyAffine.lean) shows that
the only repeated parameterization is the reflection
$t\leftrightarrow4/(3t)$. Restriction to $[6/5,5/4]$ removes that
identification, and
[heilbronn_convex_seven_infinite_optimizers](Heil7/N7OptimizerClassificationFinal.lean)
packages the resulting continuum of distinct affine classes. Thus
$h_{\rm convex}(7)=1/9$, but uniqueness fails in a completely classified
way.

The value $1/9$ was previously published by Yang and Zeng,
[“Heilbronn Problem for Seven Points in a Planar Convex
Body”](https://doi.org/10.1007/978-1-4613-3557-3_14) (1995). Again, the
formal route is an independent proof. The exhaustive family and affine
classification are contributions of this development and are not attributed
to that chapter.

## Eight points

Let $v_8\approx0.080000139329466$ be the selected root of

$$
  2060x^5-2332x^4+1064x^3-240x^2+26x-1.
$$

The target is $m\le v_8D$. Before the hull split, choose a maximum-area
triangle and map it to the fixed affine reference frame, then relabel the
other five points into nondecreasing x-order. The six hull-size exclusions
are first proved for strict order; density handles coordinate ties, while
geometric hull custody recovers the genuine cyclic hull used by the dispatch.
The global theorem
[upperBound_of_geometricHullSizes](Heilbronn8/UniversalHullGeometryFinal.lean)
routes a hypothetical counterexample through the following six cases.

| $h$ | first split | final closer |
|---:|:---|:---|
| 3 | five interior points | triangle-hull theorem: $25m\le2D$ |
| 4 | four points assigned to the four diagonal sectors | a $4^4$ census reduces to balanced, orbit I, orbit II, and reflected orbit II packets; all give $m\le(5/63)D$ |
| 5 | three points assigned to eleven pentagon regions | the $11^3$ census reduces to occupancy $111$, $210$, or $300$; common-ear/reanchoring inequalities, including the final CAB/type-717 packet, give $25m\le2D$ |
| 6 | split the six hull vertices by the line through the two interior points | cyclic blocks $1+5$, $2+4$, or $3+3$; a variation bound closes the wide case, while the compact case becomes Ferrers $L/M/R$ tables modulo dihedral symmetry and exact scalar frontiers; all give $25m\le2D$ |
| 7 | classify the radial wheel about the one interior point | eight cutoff types $0,\ldots,7$; types $0,1,2,3,4,6,7$ are strict, while type $5$, the $C24$ chamber, is sharp |
| 8 | all points on the hull | the octagon scalar inequality gives $17m$ from the alternating core and $8m$ from four ears, hence $25m\le2D$ |

Since $2/25<v_8$, every $25m\le2D$ branch is nonsharp; the four-hull
constant $5/63$ is smaller still. The selected Lean endpoints are
[geometricHullThreeExclusion](Heilbronn8/UniversalHullGeometryFinal.lean),
[geometricHullFourExclusion](Heilbronn8/GeometricHullFour.lean),
[geometricHullFiveExclusion_tableFree](Heilbronn8/TriHull/HullFive300CabUniversal.lean),
[geometricHullSixExclusion_of_completedDirectFrontiers](Heilbronn8/Survivors/Join/HullSixThreeThreeSmallPResidualXFrontier.lean),
[geometricHullSevenExclusion](Heilbronn8/HullSevenGeometricExclusion.lean), and
[geometricHullEightExclusion](Heilbronn8/UniversalHullGeometryFinal.lean).

### The sharp endpoint and the general $C24$ closure

The algebraic value is clearest at the tight symmetric endpoint. There are
variables $s,u\ge1$; putting $r=\sqrt{su}$, AM–GM compares its fan area with

$$
  6+r^2+2r+\frac2r.
$$

The last long-chord inequality implies $Q(r)\ge0$, where

$$
  Q(r)=r^5+2r^4-4r^2-4r-2.
$$

Hence $r$ is at least the unique root $\rho\in[1.47,1.5]$. The
one-variable expression is minimized at $\rho$, and exact elimination gives

$$
  v_8=\frac{\rho}{\rho^3+2\rho^2+6\rho+2}.
$$

This is [hullSeven_tight_core_v8](Heilbronn8/TriHull/HullSevenTightCore.lean).
It explains the origin of the quintic, but a general $C24$ packet does not
directly reduce to that two-variable fan. The selected general proof first
uses a chord selector. A cap-meeting surrogate is sent to the broader radial
core in [HullSevenBroadCore.lean](Heilbronn8/TriHull/HullSevenBroadCore.lean);
the complementary all-above-cap packet is closed strictly in
[HullSevenAllAboveCap.lean](Heilbronn8/TriHull/HullSevenAllAboveCap.lean).
Together [HullSevenChordSelector.lean](Heilbronn8/TriHull/HullSevenChordSelector.lean)
shows that every realizable $C24$ packet satisfies the sharp bound.

### Attainment and uniqueness

The witness is a reflection-symmetric seven-gon plus one interior point, with
coordinates in $\mathbb Q(v_8)$. Lean enumerates all $56$ triangle
determinants: symbolic identities are reduced using the quintic, and the
remaining signs are certified from exact rational isolating bounds. Separate
lemmas prove the claimed hull order and area; a final affine scaling gives
hull area one and $m=2v_8$. See
[WitnessCore.lean](Heilbronn8/WitnessCore.lean),
[WitnessMinimum.lean](Heilbronn8/WitnessMinimum.lean),
[WitnessHull.lean](Heilbronn8/WitnessHull.lean), and
[ClaimsAttain.lean](Heilbronn8/ClaimsAttain.lean).

For equality, the strict rational bounds eliminate hull sizes
$3,4,5,6,8$, and the equality-aware wheel router eliminates every
seven-hull type except $C24$. Equality in the sharp scalar inequalities,
together with the Plücker relations, then fixes its normalized chord table.
Two bracket rows locate every hull vertex relative to the interior point and
two consecutive vertices, so affine-frame reconstruction gives a single
optimizer class. See
[HullBoundaryRouterConcrete.lean](Heilbronn8/HullBoundaryRouterConcrete.lean)
and [HullSevenC24GaugeReconstruction.lean](Heilbronn8/TriHull/HullSevenC24GaugeReconstruction.lean).

Numerical $n=8$ candidates were previously recorded on
[Erich Friedman's convex-region table](https://erich-friedman.github.io/packing/heilconvex/).
The scoped search documented in [LITERATURE_AUDIT.md](LITERATURE_AUDIT.md)
found no earlier exact value, global proof, or optimizer classification.
That is a report of the search performed, not a claim that an absence from all
literature can be proved.

## What remains computational

The old Rust/Python searches found promising order types and scalar
inequalities, but their output is not a premise of the submitted theorem.
The selected proof reads no external JSON certificate corpus or Farkas bank.
It does retain exact finite mathematics where the case tree genuinely needs
it: a $2^{10}$ sign census for $n=6$; a 924-entry rational Bernstein table
in one $n=7$ chamber; and the sector, occupancy, Ferrers, wheel, interval,
AM–GM, and Bernstein checks summarized above for $n=8$.

Those objects are represented by Lean data and accompanied by proofs of
coverage and soundness. All are kernel-checked: finite tables and polynomial
certificates use exact Boolean/rational computation, while analytic
inequalities are proved over $\mathbb R$. The transitive source closure still
contains legacy certificate interfaces and two tiny diagnostic evaluations,
but no selected endpoint instantiates the generated Farkas provider or
depends on those evaluations. Floating-point search, native evaluation,
custom axioms, and external certificate files are not trusted.

For build and independent-kernel verification, see [README.md](README.md).
