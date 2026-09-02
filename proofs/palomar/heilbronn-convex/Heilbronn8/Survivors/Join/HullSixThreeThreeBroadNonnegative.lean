import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadResiduals

/-!
# Boundary extension of the broad scalar theorem

The geometric chamber floors only give nonnegativity of the shifted central
cross areas `x = -X₁₁ / m - 1` and `y = Y₁₁ / m - 1`.  The polynomial
argument is stated on the open quadrant, but either coordinate-zero boundary
is elementary: there `F` is positive and `G` is negative.  This file records
that small closure so the geometric adapter need not assume an unjustified
strict floor.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Nonnegative-coordinate version of the broad product theorem. -/
theorem hullSixThreeThree_broad_product_ge_nine_nonnegative
    {x y U v L ell B : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hU : 1 ≤ U) (hv : 1 ≤ v) (hL : 1 ≤ L) (hell : 1 ≤ ell)
    (hUL : y + 2 ≤ U * L) (hvell : x + 2 ≤ v * ell)
    (hFB : hullSixThreeThreeBroadF x y U v ≤ B)
    (hBG : B ≤ hullSixThreeThreeBroadG x y L ell) :
    9 ≤ x * y := by
  by_cases hxZero : x = 0
  · subst x
    have hFPos : 0 < hullSixThreeThreeBroadF 0 y U v := by
      simp [hullSixThreeThreeBroadF]
      have hnum : 0 < U * v * (y + 1) + v * y ^ 2 + y + 1 := by
        have hUv : 0 < U * v := mul_pos
          (lt_of_lt_of_le zero_lt_one hU) (lt_of_lt_of_le zero_lt_one hv)
        positivity
      have hden : 0 < (U + y) * v := by positivity
      exact div_pos hnum hden
    have hGNeg : hullSixThreeThreeBroadG 0 y L ell < 0 := by
      simp [hullSixThreeThreeBroadG]
      have hnum : -(L * ell) - y - 1 < 0 := by
        have hLE : 0 < L * ell := mul_pos
          (lt_of_lt_of_le zero_lt_one hL)
          (lt_of_lt_of_le zero_lt_one hell)
        linarith
      have hden : 0 < (L + y) * ell := by positivity
      exact div_neg_of_neg_of_pos hnum hden
    linarith
  · by_cases hyZero : y = 0
    · subst y
      have hFPos : 0 < hullSixThreeThreeBroadF x 0 U v := by
        simp [hullSixThreeThreeBroadF]
        have hnum : 0 < U * v * (x + 1) + U * x ^ 2 + x + 1 := by
          have hUv : 0 < U * v := mul_pos
            (lt_of_lt_of_le zero_lt_one hU) (lt_of_lt_of_le zero_lt_one hv)
          positivity
        have hden : 0 < U * (v + x) := by positivity
        exact div_pos hnum hden
      have hGNeg : hullSixThreeThreeBroadG x 0 L ell < 0 := by
        simp [hullSixThreeThreeBroadG]
        have hnum : -(L * ell) - x - 1 < 0 := by
          have hLE : 0 < L * ell := mul_pos
            (lt_of_lt_of_le zero_lt_one hL)
            (lt_of_lt_of_le zero_lt_one hell)
          linarith
        have hden : 0 < L * (ell + x) := by positivity
        exact div_neg_of_neg_of_pos hnum hden
      linarith
    · exact hullSixThreeThree_broad_product_ge_nine
        (lt_of_le_of_ne hx (Ne.symm hxZero))
        (lt_of_le_of_ne hy (Ne.symm hyZero))
        hU hv hL hell hUL hvell hFB hBG

/-- The corresponding nonnegative shifted-sum conclusion. -/
theorem hullSixThreeThree_broad_sum_ge_eight_nonnegative
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 9 ≤ x * y) :
    8 ≤ (x + 1) + (y + 1) := by
  have hxPos : 0 < x := by
    by_contra h
    have hxZero : x = 0 := le_antisymm (le_of_not_gt h) hx
    rw [hxZero, zero_mul] at hxy
    norm_num at hxy
  have hyPos : 0 < y := by
    by_contra h
    have hyZero : y = 0 := le_antisymm (le_of_not_gt h) hy
    rw [hyZero, mul_zero] at hxy
    norm_num at hxy
  exact hullSixThreeThree_broad_sum_ge_eight hxPos hyPos hxy

/-- Cleared-residual form with the closed-quadrant hypotheses supplied by
geometric chamber floors. -/
theorem hullSixThreeThree_broad_product_ge_nine_of_clearedResiduals_nonnegative
    {x y U v L ell B E : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
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
  exact hullSixThreeThree_broad_product_ge_nine_nonnegative
    hx hy hU hv hL hell hUL hvell hFB hBG

/-- Positive ear residuals with merely nonnegative shifted central variables. -/
theorem hullSixThreeThree_broad_product_ge_nine_of_earResiduals_nonnegative
    {x y U v L ell B E TU TL p0 q0 P0 Q0 y0 h0 x0 z0 : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hU : 1 ≤ U) (hv : 1 ≤ v) (hL : 1 ≤ L) (hell : 1 ≤ ell)
    (hBE : B + E = x + y)
    (hUL : y + 2 ≤ U * L) (hvell : x + 2 ≤ v * ell)
    (hTU : 1 ≤ TU) (hTL : 1 ≤ TL)
    (hp0 : 0 ≤ p0) (hq0 : 0 ≤ q0) (hP0 : 0 ≤ P0) (hQ0 : 0 ≤ Q0)
    (hy0 : 1 ≤ y0) (hh0 : 1 ≤ h0) (hx0 : 1 ≤ x0) (hz0 : 1 ≤ z0)
    (hB0 : 0 ≤ B + 1) (hE0 : 0 ≤ E + 1)
    (hDbEq :
      (B + 1) * (x * y) - (x + 1) * (y + 1) +
          (B - x) * x * U + (B - y) * y * v - (E + 1) * U * v =
        (x + 1) * (y + 1) * (TU - 1) +
          (y + 1) * p0 * (h0 - 1) +
          (x + 1) * q0 * (y0 - 1) +
          (B + 1) * (y0 - 1) * (h0 - 1))
    (hDeEq :
      (E + 1) * (x * y) - (x + 1) * (y + 1) +
          (E - x) * x * L + (E - y) * y * ell - (B + 1) * L * ell =
        (x + 1) * (y + 1) * (TL - 1) +
          (y + 1) * P0 * (x0 - 1) +
          (x + 1) * Q0 * (z0 - 1) +
          (E + 1) * (z0 - 1) * (x0 - 1)) :
    9 ≤ x * y := by
  have hDb :
      0 ≤ (B + 1) * (x * y) - (x + 1) * (y + 1) +
        (B - x) * x * U + (B - y) * y * v - (E + 1) * U * v := by
    rw [hDbEq]
    positivity
  have hDe :
      0 ≤ (E + 1) * (x * y) - (x + 1) * (y + 1) +
        (E - x) * x * L + (E - y) * y * ell - (B + 1) * L * ell := by
    rw [hDeEq]
    positivity
  exact hullSixThreeThree_broad_product_ge_nine_of_clearedResiduals_nonnegative
    hx hy hU hv hL hell hBE hUL hvell hDb hDe

end Heilbronn8
