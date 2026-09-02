import Heil7.CanonicalHullClassification7
import Heil7.Hull3CountingRoute
import Heil7.TriangleInputAdapter
import Heil7.Hull6BracketCoreProof
import Heil7.Hull7ContinuantRoute

/-!
# Unconditional seven-point upper bound

This is the thin assembly layer for the source-complete hull-size proofs.  It
contains no geometric or numerical certificate argument: each field is
provided by its dedicated hull-size module, and the canonical hull classifier
then gives the pointwise doubled-area inequality.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- All five possible convex-hull sizes satisfy the canonical area bound. -/
theorem hullCaseBounds_proved : HullCaseBounds where
  h3 := hullThree_counting
  h4 := hull45_fields_unconditional.1
  h5 := hull45_fields_unconditional.2
  h6 := hullSix_bound_proved
  h7 := hullSeven_of_continuant

/-- Pointwise Yang--Zeng upper bound in the canonical doubled-area language. -/
theorem sevenPointAreaBound_proved : SevenPointAreaBound :=
  fun v => nine_minTri_le_doubledHullArea
    hullCaseBounds_proved hullClassified_all v

/-- Exact convex Heilbronn value for seven points. -/
theorem heilbronn_convex_seven_proved : h_convex 7 = v7 :=
  heilbronn_convex_seven hullCaseBounds_proved hullClassified_all

end HeilbronnChallenge.N7Upper

namespace HeilbronnChallenge

/-- Public pointwise upper bound for every unit-area seven-point
configuration. -/
theorem heilbronn_convex_seven_upper_bound
    (p : Fin 7 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v7 := by
  have hbound := N7Upper.sevenPointAreaBound_proved p
  have harea := HullBridge.doubledHullArea_of_unit_volume hvol
  rw [harea] at hbound
  rw [v7]
  norm_num at hbound ⊢
  linarith

/-- Public exact-value theorem, obtained from the pointwise upper bound and
the rational attaining configuration in `Solution.N7`. -/
theorem heilbronn_convex_seven : h_convex 7 = v7 :=
  N7Upper.heilbronn_convex_seven_proved

end HeilbronnChallenge
