import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadScalar

/-!
# Cleared elimination interface for the broad `3 x 3` chamber

The geometric ear calculation naturally produces two polynomial residuals.
This file checks that they are exactly the cleared forms of the rational
`F ≤ B ≤ G` sandwich consumed by the broad scalar theorem.  Keeping this
step separate makes the remaining geometry adapter division-free.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The two nonnegative cleared residuals imply the sharp shifted central
product bound.  Every geometric hypothesis is displayed explicitly. -/
theorem hullSixThreeThree_broad_product_ge_nine_of_clearedResiduals
    {x y U v L ell B E : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hU : 1 ≤ U) (hv : 1 ≤ v) (hL : 1 ≤ L) (hell : 1 ≤ ell)
    (hBE : B + E = x + y)
    (hUL : y + 2 ≤ U * L) (hvell : x + 2 ≤ v * ell)
    (hDb :
      0 ≤ (B + 1) * (x * y) - (x + 1) * (y + 1) +
        (B - x) * x * U + (B - y) * y * v - (E + 1) * U * v)
    (hDe :
      0 ≤ (E + 1) * (x * y) - (x + 1) * (y + 1) +
        (E - x) * x * L + (E - y) * y * ell - (B + 1) * L * ell) :
    9 ≤ x * y := by
  have hE : E = x + y - B := by linarith
  have hFden : 0 < (U + y) * (v + x) := by positivity
  have hGden : 0 < (L + y) * (ell + x) := by positivity
  have hFid :
      (U + y) * (v + x) *
          (B - hullSixThreeThreeBroadF x y U v) =
        (B + 1) * (x * y) - (x + 1) * (y + 1) +
          (B - x) * x * U + (B - y) * y * v - (E + 1) * U * v := by
    rw [hE]
    simp only [hullSixThreeThreeBroadF]
    field_simp [ne_of_gt hFden]
    ring
  have hGid :
      (L + y) * (ell + x) *
          (hullSixThreeThreeBroadG x y L ell - B) =
        (E + 1) * (x * y) - (x + 1) * (y + 1) +
          (E - x) * x * L + (E - y) * y * ell - (B + 1) * L * ell := by
    rw [hE]
    simp only [hullSixThreeThreeBroadG]
    field_simp [ne_of_gt hGden]
    ring
  have hFB : hullSixThreeThreeBroadF x y U v ≤ B := by
    by_contra hnot
    have hneg : B - hullSixThreeThreeBroadF x y U v < 0 := by linarith
    have hprod :
        (U + y) * (v + x) *
            (B - hullSixThreeThreeBroadF x y U v) < 0 :=
      mul_neg_of_pos_of_neg hFden hneg
    rw [hFid] at hprod
    linarith
  have hBG : B ≤ hullSixThreeThreeBroadG x y L ell := by
    by_contra hnot
    have hneg : hullSixThreeThreeBroadG x y L ell - B < 0 := by linarith
    have hprod :
        (L + y) * (ell + x) *
            (hullSixThreeThreeBroadG x y L ell - B) < 0 :=
      mul_neg_of_pos_of_neg hGden hneg
    rw [hGid] at hprod
    linarith
  exact hullSixThreeThree_broad_product_ge_nine
    hx hy hU hv hL hell hUL hvell hFB hBG

end Heilbronn8
