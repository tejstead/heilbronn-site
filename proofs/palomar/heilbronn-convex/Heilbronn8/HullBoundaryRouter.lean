import Heilbronn8.GeometricHullExclusionCore
import Heilbronn8.HullSevenBoundaryCutoff
import Heilbronn8.Survivors.Join.HullEightOctagon
import Heilbronn8.TriHull.HullSevenC24GaugeReconstruction

/-!
# Equality-aware routing by the actual convex-hull size

Phase-two scratch source.  This file isolates the small interface that the
non-seven hull branches must expose: the closed rational inequality

`25 * minTri v <= 2 * doubledHullArea v`.

At a positive-area `v8` boundary this inequality is impossible because
`2 / 25 < v8`.  The only remaining hull size is seven, where
`StrictHullSevenInterior.c24_of_v8_boundary` returns the concrete C24 packet.

The three imports after `GeometricHullExclusionCore` are intended package
locations for the adjacent phase-two scratch modules.  No frozen package file
is changed by this proposal.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

noncomputable section

/-- Geometry-only closed `2/25` bound for one actual hull size. -/
def GeometricHullSizeTwoTwentyFiveBound (size : Nat) : Prop :=
  ∀ {v : Configuration} (custody : GeometricHullCustody v),
    0 < minTri v → custody.data.cycle.length = size →
      25 * minTri v ≤ 2 * doubledHullArea v

/-- Hull size eight already exports exactly the required closed bound; unlike
sizes three through six, it needs no production refactor. -/
theorem geometricHullEight_twoTwentyFiveBound :
    GeometricHullSizeTwoTwentyFiveBound 8 := by
  intro v custody _hmin h8
  have hinjective : Function.Injective (custody.data.castGet h8) :=
    HullCycleData.castGet_injective custody.data h8 custody.hull.nodup
  have hcyclic : StrictCyclicPos (custody.data.castGet h8) v :=
    HullCycleData.strictCyclicPos_cast custody.data h8
      custody.hull.strictCyclicPos
  exact strictOctagon_twentyFive_minTri_le_two_doubledHullArea
    hinjective hcyclic

private lemma false_of_v8_boundary_and_twoTwentyFiveBound
    {v : Configuration}
    (harea : 0 < doubledHullArea v)
    (hboundary : v8 * doubledHullArea v ≤ minTri v)
    (hcut : 25 * minTri v ≤ 2 * doubledHullArea v) : False := by
  have hq : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hlevel :
      (2 / 25 : ℝ) * doubledHullArea v <
        v8 * doubledHullArea v :=
    mul_lt_mul_of_pos_right hq harea
  have hsmall :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    lt_of_lt_of_le hlevel hboundary
  nlinarith

/-- Every positive-area configuration on the sharp `v8` boundary has actual
hull size seven and lies in the C24/type-5 chamber, provided the five other
hull sizes expose their already-proved closed rational estimates. -/
theorem hullSevenC24PointData_exists_of_v8_boundary
    (h3 : GeometricHullSizeTwoTwentyFiveBound 3)
    (h4 : GeometricHullSizeTwoTwentyFiveBound 4)
    (h5 : GeometricHullSizeTwoTwentyFiveBound 5)
    (h6 : GeometricHullSizeTwoTwentyFiveBound 6)
    (h8 : GeometricHullSizeTwoTwentyFiveBound 8)
    {v : Configuration}
    (harea : 0 < doubledHullArea v)
    (hboundary : v8 * doubledHullArea v ≤ minTri v) :
    Nonempty (TriHull.HullSevenC24PointData v) := by
  have hmin : 0 < minTri v :=
    lt_of_lt_of_le (mul_pos v8_pos harea) hboundary
  obtain ⟨data, hull⟩ := exists_hullCycleOf_of_minTri_pos v hmin
  let custody : GeometricHullCustody v :=
    { signs := StrictSignData.ofAllTripleSignsStrict v
        (allTripleSignsStrict_of_minTri_pos v hmin)
      data := data
      hull := hull }
  have hsizes :
      custody.data.cycle.length = 3 ∨
      custody.data.cycle.length = 4 ∨
      custody.data.cycle.length = 5 ∨
      custody.data.cycle.length = 6 ∨
      custody.data.cycle.length = 7 ∨
      custody.data.cycle.length = 8 := by
    have hlower := custody.data.length_ge_three
    have hupper := custody.data.length_le_eight
    omega
  rcases hsizes with hsize | hsize | hsize | hsize | hsize | hsize
  · exact (false_of_v8_boundary_and_twoTwentyFiveBound harea hboundary
      (h3 custody hmin hsize)).elim
  · exact (false_of_v8_boundary_and_twoTwentyFiveBound harea hboundary
      (h4 custody hmin hsize)).elim
  · exact (false_of_v8_boundary_and_twoTwentyFiveBound harea hboundary
      (h5 custody hmin hsize)).elim
  · exact (false_of_v8_boundary_and_twoTwentyFiveBound harea hboundary
      (h6 custody hmin hsize)).elim
  · obtain ⟨pointLabel, hpointOutside, X⟩ :=
      exists_strictHullSevenInterior_geometric custody.hull hsize hmin
    have hcycleInjective :
        Function.Injective (custody.data.castGet hsize) :=
      HullCycleData.castGet_injective custody.data hsize custody.hull.nodup
    have harea' :
        doubledHullArea v = fanSum v (custody.data.castGet hsize) := by
      calc
        doubledHullArea v = custody.data.fanExpr v :=
          doubledHullArea_eq_of_isHullArea custody.hull.isHullArea
        _ = fanSum v (custody.data.castGet hsize) :=
          (HullCycleData.fanSum_castGet custody.data hsize).symm
    exact X.c24_of_v8_boundary hcycleInjective hpointOutside hmin harea'
      hboundary
  · exact (false_of_v8_boundary_and_twoTwentyFiveBound harea hboundary
      (h8 custody hmin hsize)).elim

/-- Boundary inequalities are exactly the normalized upper hypothesis used by
the chord-selector and rigidity layers. -/
lemma v8_normalized_hullArea_le_one_of_boundary
    {v : Configuration} (hmin : 0 < minTri v)
    (hboundary : v8 * doubledHullArea v ≤ minTri v) :
    v8 * (doubledHullArea v / minTri v) ≤ 1 := by
  have hdiv :
      (v8 * doubledHullArea v) / minTri v ≤ 1 := by
    exact (div_le_iff₀ hmin).2 (by simpa using hboundary)
  calc
    v8 * (doubledHullArea v / minTri v) =
        (v8 * doubledHullArea v) / minTri v := by ring
    _ ≤ 1 := hdiv

/-- The sole remaining selector obligation: all-above is strict at the
boundary, hence a C24 chord input has a capped surrogate. -/
def HullSevenC24BoundaryCapProvider : Prop :=
  ∀ {v : Configuration} (X : TriHull.HullSevenC24PointData v),
    v8 * (doubledHullArea v / minTri v) ≤ 1 →
      Nonempty (TriHull.HullSevenCappedSurrogate X.toChordInput)

/-- The strict all-above cutoff installed by `HullSevenChordSelector` supplies
the cap provider required by the equality router. -/
theorem hullSevenC24BoundaryCapProvider_proved :
    HullSevenC24BoundaryCapProvider := by
  intro v X hupper
  exact TriHull.hullSevenCappedSurrogate_exists_of_v8_upper
    X.toChordInput hupper

/-- Pairwise optimizer classification in the raw geometry interface.  It is
already the desired uniqueness modulo relabeling and a positive-determinant
affine map; the public phase-four `GaugeEquivalent` theorem is a thin wrapper.
-/
theorem pairwise_gauge_unique_of_v8_boundary
    (h3 : GeometricHullSizeTwoTwentyFiveBound 3)
    (h4 : GeometricHullSizeTwoTwentyFiveBound 4)
    (h5 : GeometricHullSizeTwoTwentyFiveBound 5)
    (h6 : GeometricHullSizeTwoTwentyFiveBound 6)
    (h8 : GeometricHullSizeTwoTwentyFiveBound 8)
    (cap : HullSevenC24BoundaryCapProvider)
    {v u : Configuration}
    (hvArea : 0 < doubledHullArea v)
    (huArea : 0 < doubledHullArea u)
    (hvBoundary : v8 * doubledHullArea v ≤ minTri v)
    (huBoundary : v8 * doubledHullArea u ≤ minTri u) :
    ∃ (sigma : Equiv.Perm (Fin 8)) (T : PosAffine),
      u = fun i ↦ T.map (v (sigma i)) := by
  obtain ⟨X⟩ := hullSevenC24PointData_exists_of_v8_boundary
    h3 h4 h5 h6 h8 hvArea hvBoundary
  obtain ⟨Y⟩ := hullSevenC24PointData_exists_of_v8_boundary
    h3 h4 h5 h6 h8 huArea huBoundary
  have hvMin : 0 < minTri v :=
    lt_of_lt_of_le (mul_pos v8_pos hvArea) hvBoundary
  have huMin : 0 < minTri u :=
    lt_of_lt_of_le (mul_pos v8_pos huArea) huBoundary
  have hvUpper := v8_normalized_hullArea_le_one_of_boundary hvMin hvBoundary
  have huUpper := v8_normalized_hullArea_le_one_of_boundary huMin huBoundary
  obtain ⟨SX⟩ := cap X hvUpper
  obtain ⟨SY⟩ := cap Y huUpper
  exact TriHull.hullSevenC24_pairwise_gauge_unique
    X Y SX SY hvUpper huUpper

end

end Heilbronn8
