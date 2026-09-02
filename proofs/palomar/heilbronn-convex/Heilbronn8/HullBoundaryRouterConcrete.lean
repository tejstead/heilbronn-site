import Heilbronn8.HullBoundaryRouter
import Heilbronn8.HullThreeFourRawBounds
import Heilbronn8.TriHull.HullFiveTwoTwentyFiveBound
import Heilbronn8.Survivors.Join.HullSixCompletedRawBound

/-!
# Concrete equality-aware hull router

This module installs the raw rational providers for hull sizes three through
six into `HullBoundaryRouter`.  Its final theorem has no provider, density,
order-type, certificate, or `Beats` hypothesis.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

noncomputable section

theorem geometricHullFive_twoTwentyFiveBound :
    GeometricHullSizeTwoTwentyFiveBound 5 := by
  intro v custody hmin h5
  exact TriHull.geometricHullFive_twoTwentyFiveBound custody hmin h5

theorem geometricHullSix_twoTwentyFiveBound :
    GeometricHullSizeTwoTwentyFiveBound 6 := by
  intro v custody _hmin h6
  exact twentyFive_minTri_le_twice_hullArea_of_hullCycleSix_completed
    custody.hull h6

/-- Any two positive-area configurations on the sharp `v8` boundary differ by
relabeling and a positive-determinant affine map. -/
theorem pairwise_gauge_unique_of_v8_boundary_unconditional
    {v u : Configuration}
    (hvArea : 0 < doubledHullArea v)
    (huArea : 0 < doubledHullArea u)
    (hvBoundary : v8 * doubledHullArea v ≤ minTri v)
    (huBoundary : v8 * doubledHullArea u ≤ minTri u) :
    ∃ (sigma : Equiv.Perm (Fin 8)) (T : PosAffine),
      u = fun i ↦ T.map (v (sigma i)) := by
  exact pairwise_gauge_unique_of_v8_boundary
    geometricHullThree_twoTwentyFiveBound
    geometricHullFour_twoTwentyFiveBound
    geometricHullFive_twoTwentyFiveBound
    geometricHullSix_twoTwentyFiveBound
    geometricHullEight_twoTwentyFiveBound
    hullSevenC24BoundaryCapProvider_proved
    hvArea huArea hvBoundary huBoundary

end

end Heilbronn8
