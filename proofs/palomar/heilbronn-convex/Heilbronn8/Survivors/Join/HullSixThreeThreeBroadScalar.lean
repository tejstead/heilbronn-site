import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadFG
import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadPolynomial

/-!
# Scalar closure of the broad `3 x 3` chamber

This file joins the geometry-free polynomial certificate to the four-case
`F/G` wrapper.  The only bridge is the displayed rational identity below;
in particular, no monotonicity argument is used outside the physical
domain where all four fan variables are at least one.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Positivity of the four-variable polynomial gives the strict comparison
at the two raw product boundaries. -/
theorem hullSixThreeThree_broad_rawBoundary_of_polynomial
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy1 : 1 < x * y) (hxy9 : x * y < 9) :
    HullSixThreeThreeBroadRawBoundary x y := by
  intro U v hU hv
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hpoly :
      0 < hullSixThreeThreeBroadPolynomial x y U v :=
    hullSixThreeThreeBroadPolynomial_pos hx hy hU hv hxy1 hxy9
  have hUy : 0 < U + y := by linarith
  have hvx : 0 < v + x := by linarith
  have hUyy : 0 < U * y + y + 2 := by positivity
  have hvxx : 0 < v * x + x + 2 := by positivity
  have hid :
      hullSixThreeThreeBroadF x y U v -
          hullSixThreeThreeBroadG x y ((y + 2) / U) ((x + 2) / v) =
        (x + 1) * (y + 1) *
            hullSixThreeThreeBroadPolynomial x y U v /
          ((U + y) * (v + x) *
            (U * y + y + 2) * (v * x + x + 2)) := by
    simp only [hullSixThreeThreeBroadF, hullSixThreeThreeBroadG,
      hullSixThreeThreeBroadPolynomial]
    field_simp [ne_of_gt hUpos, ne_of_gt hvpos, ne_of_gt hUy,
      ne_of_gt hvx, ne_of_gt hUyy, ne_of_gt hvxx]
    ring
  have hnum :
      0 < (x + 1) * (y + 1) *
        hullSixThreeThreeBroadPolynomial x y U v := by
    positivity
  have hden :
      0 < (U + y) * (v + x) *
        (U * y + y + 2) * (v * x + x + 2) := by
    positivity
  have hdiff :
      0 < hullSixThreeThreeBroadF x y U v -
        hullSixThreeThreeBroadG x y ((y + 2) / U) ((x + 2) / v) := by
    rw [hid]
    exact div_pos hnum hden
  linarith

/-- Complete geometry-free product conclusion for the broad chamber. -/
theorem hullSixThreeThree_broad_product_ge_nine
    {x y U v L ell B : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hU : 1 ≤ U) (hv : 1 ≤ v) (hL : 1 ≤ L) (hell : 1 ≤ ell)
    (hUL : y + 2 ≤ U * L) (hvell : x + 2 ≤ v * ell)
    (hFB : hullSixThreeThreeBroadF x y U v ≤ B)
    (hBG : B ≤ hullSixThreeThreeBroadG x y L ell) :
    9 ≤ x * y := by
  apply hullSixThreeThree_broad_product_ge_nine_of_rawBoundary
    hx hy hU hv hL hell hUL hvell hFB hBG
  intro hxy1 hxy9
  exact hullSixThreeThree_broad_rawBoundary_of_polynomial hx hy hxy1 hxy9

/-- The shifted product conclusion in the broad chamber implies the central
sum bound used by the geometric hull decomposition. -/
theorem hullSixThreeThree_broad_sum_ge_eight
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : 9 ≤ x * y) :
    8 ≤ (x + 1) + (y + 1) := by
  have hsumPos : 0 < x + y := by linarith
  have hsq : 4 * (x * y) ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have hsumSix : 6 ≤ x + y := by
    by_contra hnot
    have hsumLt : x + y < 6 := lt_of_not_ge hnot
    have hfactor : 0 < (6 - (x + y)) * (6 + (x + y)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  linarith

end Heilbronn8
