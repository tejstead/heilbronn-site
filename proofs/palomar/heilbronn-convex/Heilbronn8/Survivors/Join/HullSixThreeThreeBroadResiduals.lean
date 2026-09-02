import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadElimination

/-!
# Positive residual form of the broad `3 x 3` ears

After the upper and lower ear identities are substituted, the two cleared
`F/G` residuals are sums of four manifestly nonnegative products.  This file
packages that last positivity step.  A geometric adapter only has to prove
the two exact identities displayed in the hypotheses.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Manifestly positive ear residuals imply the shifted central product
bound.  The variables `p0,q0,P0,Q0` are the four outer adjacent fan areas;
`y0,h0,x0,z0` are the six-staircase cross areas used by the two ears. -/
theorem hullSixThreeThree_broad_product_ge_nine_of_earResiduals
    {x y U v L ell B E TU TL p0 q0 P0 Q0 y0 h0 x0 z0 : ℝ}
    (hx : 0 < x) (hy : 0 < y)
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
  exact hullSixThreeThree_broad_product_ge_nine_of_clearedResiduals
    hx hy hU hv hL hell hBE hUL hvell hDb hDe

end Heilbronn8
