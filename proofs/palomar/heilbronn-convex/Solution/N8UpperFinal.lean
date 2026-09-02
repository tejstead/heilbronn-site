import Solution.N8

/-!
# Pointwise Palomar upper bound for eight points

The exact-value theorem alone is not used as a substitute for the challenge's
pointwise statement.  This module specializes the already-compiled geometric
hull-size upper-bound functional and translates its internal `minTri` and `v8`
to the challenge namespace.
-/

set_option relaxedAutoImplicit false

namespace HeilbronnChallenge

noncomputable section

theorem heilbronn_convex_eight_upper_bound
    (p : Fin 8 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v8 := by
  have hinternal : Heilbronn8.minTri p ≤ 2 * Heilbronn8.v8 :=
    (Heilbronn8.upperBound_of_geometricHullSizes
      (Heilbronn8.geometricHullFourExclusion Heilbronn8.StrictXOrder)
      Heilbronn8.TriHull.geometricHullFiveExclusion_tableFree
      Heilbronn8.geometricHullSixExclusion_of_completedDirectFrontiers
      Heilbronn8.geometricHullSevenExclusion) p hvol
  calc
    minTri p = Heilbronn8.minTri p := (minTri_eq_eight p).symm
    _ ≤ 2 * Heilbronn8.v8 := hinternal
    _ = 2 * v8 := by rw [v8_eq_eight]

end

end HeilbronnChallenge
