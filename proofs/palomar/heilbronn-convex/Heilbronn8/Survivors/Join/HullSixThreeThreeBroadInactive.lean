import Heilbronn8.Survivors.Join.HullSixFerrersSymmetry

/-!
# The both-inactive boundary certificate for the broad `3 x 3` chamber

In the scalar elimination for the broad table, two product lower bounds are
replaced by `max 1` boundaries.  When both algebraic product boundaries lie
below one, monotonicity reduces the comparison to a single numerator.  This
file proves that numerator strictly positive by two small polynomial
identities.  It is independent of the harder four-variable polynomial used
when at least one product boundary is active.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Positivity of the numerator in the both-inactive product-boundary case.

The expression is symmetric in `p,q`.  For `p+q ≤ 6`, its fourfold is a
sum of two nonnegative products, the first strictly positive.  For
`6 < p+q`, it is `16` plus two nonnegative products. -/
theorem hullSixThreeThree_broad_inactiveNumerator_pos
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p * q ≤ 9) :
    0 <
      4 * (p ^ 2 + q ^ 2) + 11 * (p + q) + 13 -
        2 * (p * q) * (p + q) - 3 * (p * q) := by
  let N : ℝ :=
    4 * (p ^ 2 + q ^ 2) + 11 * (p + q) + 13 -
      2 * (p * q) * (p + q) - 3 * (p * q)
  by_cases hs : p + q ≤ 6
  · have hfirstFactor : 0 < (p + q + 2) ^ 2 := by positivity
    have hsecondFactor : 0 < 13 - 2 * (p + q) := by linarith
    have hfirst :
        0 < (p + q + 2) ^ 2 * (13 - 2 * (p + q)) :=
      mul_pos hfirstFactor hsecondFactor
    have hsquare : 0 ≤ (p + q) ^ 2 - 4 * (p * q) := by
      nlinarith [sq_nonneg (p - q)]
    have hcoefficient : 0 < 2 * (p + q) + 11 := by linarith
    have hsecond :
        0 ≤ ((p + q) ^ 2 - 4 * (p * q)) *
          (2 * (p + q) + 11) :=
      mul_nonneg hsquare (le_of_lt hcoefficient)
    have hid :
        4 * N =
          (p + q + 2) ^ 2 * (13 - 2 * (p + q)) +
            ((p + q) ^ 2 - 4 * (p * q)) *
              (2 * (p + q) + 11) := by
      dsimp [N]
      ring
    nlinarith
  · have hs6 : 0 ≤ p + q - 6 := by linarith
    have hcoef1 : 0 < 4 * (p + q) + 17 := by linarith
    have hterm1 :
        0 ≤ (p + q - 6) * (4 * (p + q) + 17) :=
      mul_nonneg hs6 (le_of_lt hcoef1)
    have h9 : 0 ≤ 9 - p * q := by linarith
    have hcoef2 : 0 < 2 * (p + q) + 11 := by linarith
    have hterm2 :
        0 ≤ (9 - p * q) * (2 * (p + q) + 11) :=
      mul_nonneg h9 (le_of_lt hcoef2)
    have hid :
        N = 16 + (p + q - 6) * (4 * (p + q) + 17) +
          (9 - p * q) * (2 * (p + q) + 11) := by
      dsimp [N]
      ring
    nlinarith

end Heilbronn8
