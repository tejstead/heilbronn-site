import Heil6.HullPacketBounds
import Solution.N6

set_option linter.style.header false

/-!
# Pointwise and supremum-form n = 6 upper bounds

The finite hull normal form and four packet bounds first give the pointwise
inequality `6 * minTri v ≤ doubledHullArea v`.  At unit hull area this is
`minTri v ≤ 1/3`, exactly the upper half of `h_convex 6 = 1/6`.
-/

namespace N6Scratch

open HeilbronnChallenge

theorem six_mul_minTri_le_doubledHullArea
    (v : Fin 6 → ℝ × ℝ) :
    6 * minTri v ≤ HullBridge.doubledHullArea v := by
  apply HullPacketBounds.six_mul_floor_le_doubledHullArea
  intro i j k hij hik hjk
  simpa only [FiniteHullCases.DistinctTriangleFloor,
    PlanarDet.sig, HeilbronnChallenge.sig] using
    minTri_le_of_distinct v i j k hij hik hjk

theorem minTri_le_one_third_of_unit_volume
    (v : Fin 6 → ℝ × ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1) :
    minTri v ≤ 1 / 3 := by
  have hbound := six_mul_minTri_le_doubledHullArea v
  have harea := HullBridge.doubledHullArea_of_unit_volume hvolume
  rw [harea] at hbound
  norm_num at hbound ⊢
  linarith

theorem admissibleScore_six_le_v6
    (r : ℝ) (hr : AdmissibleScore 6 r) : r ≤ v6 := by
  rcases hr.2.2 with ⟨v, hvolume, hscore⟩
  have hbound := minTri_le_one_third_of_unit_volume v hvolume
  rw [hscore] at hbound
  rw [v6]
  norm_num at hbound ⊢
  linarith

/-- Pointwise upper bound in the exact form used by the unified challenge. -/
theorem heilbronn_convex_six_upper_bound
    (p : Fin 6 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v6 := by
  calc
    minTri p ≤ 1 / 3 := minTri_le_one_third_of_unit_volume p hvol
    _ = 2 * v6 := by rw [v6]; norm_num

/-- The exact convex Heilbronn value at six points. -/
theorem heilbronn_convex_six : h_convex 6 = v6 :=
  h_convex_eq v6 v6_admissible admissibleScore_six_le_v6

end N6Scratch

namespace HeilbronnChallenge

/-- Challenge-facing wrapper for the pointwise six-point upper bound. -/
theorem heilbronn_convex_six_upper_bound
    (p : Fin 6 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v6 :=
  N6Scratch.heilbronn_convex_six_upper_bound p hvol

/-- Challenge-facing wrapper for the completed six-point upper bound. -/
theorem heilbronn_convex_six : h_convex 6 = v6 :=
  N6Scratch.heilbronn_convex_six

end HeilbronnChallenge
