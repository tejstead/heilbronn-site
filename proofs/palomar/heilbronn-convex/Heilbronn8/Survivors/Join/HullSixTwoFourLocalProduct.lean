import Mathlib

/-!
# A local-product closure for six-hull chambers

In a normalized `2 + 4` frame the hull fan has one upper same-side edge and
three lower same-side edges; in a `3 + 3` frame it has two of each.  In both
cases there are four same-side edges and two cross-block boundary edges.  In either
the `P`-fan or the `Q`-fan, the two cross-block edges contribute at least
`1 + 3`: one has the ordinary triangle floor and the other contains that
floor plus the two opposite line-level floors.  The two lower edges not used
in a chosen adjacent Plucker minor contribute another `1 + 1`.

Consequently, if the upper edge `E` and one lower edge `D` satisfy
`12 <= E * D`, then `E + D > 13/2` and the whole fan is strictly larger than
`25/2`.  This is the common endpoint for the easy separated chamber blocks;
the chamber adapter remains responsible for proving the product bound and
the exact fan identity.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- A product of twelve forces the selected pair of positive fan areas above
`13/2`.  The proof is the rational square identity
`4 E D <= (E + D)^2`; no square-root API is involved. -/
theorem hullSixTwoFour_pair_gt_thirteen_halves
    {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hproduct : 12 ≤ E * D) :
    (13 : ℝ) / 2 < E + D := by
  by_contra hnot
  have hsum : E + D ≤ (13 : ℝ) / 2 := le_of_not_gt hnot
  have hsum0 : 0 ≤ E + D := add_nonneg hE hD
  have hfactor :
      0 ≤ ((13 : ℝ) / 2 - (E + D)) *
        ((13 : ℝ) / 2 + (E + D)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (E - D)]

/-- Scale-aware form of the same rational product argument. -/
theorem hullSixTwoFour_pair_gt_thirteen_halves_mul
    {m E D : ℝ} (hm : 0 < m) (hE : m ≤ E) (hD : m ≤ D)
    (hproduct : 12 * m ^ 2 ≤ E * D) :
    (13 : ℝ) / 2 * m < E + D := by
  by_contra hnot
  have hsum : E + D ≤ (13 : ℝ) / 2 * m := le_of_not_gt hnot
  have hsum0 : 0 ≤ E + D := by linarith
  have hfactor :
      0 ≤ ((13 : ℝ) / 2 * m - (E + D)) *
        ((13 : ℝ) / 2 * m + (E + D)) :=
    mul_nonneg (by linarith) (by linarith)
  have hmSq : 0 < m ^ 2 := sq_pos_of_pos hm
  nlinarith [sq_nonneg (E - D)]

/-- The `P`-Plucker product bound for a local block with rows `RR / LR`.
Here `x00,x01` are the top row and `x10,x11` the bottom row. -/
theorem hullSixTwoFour_product_twelve_of_RR_LR
    {m x00 x01 x10 x11 E D : ℝ} (hm : 0 ≤ m)
    (hx00 : x00 ≤ -3 * m) (hx01 : x01 ≤ -3 * m)
    (hx10 : m ≤ x10) (hx11 : x11 ≤ -3 * m)
    (hplucker : E * D = x00 * x11 - x01 * x10) :
    12 * m ^ 2 ≤ E * D := by
  have hneg00 : 0 ≤ -x00 := by linarith
  have hneg01 : 0 ≤ -x01 := by linarith
  have hneg11 : 0 ≤ -x11 := by linarith
  have hthree : 0 ≤ 3 * m := by positivity
  have hfirst : (3 * m) * (3 * m) ≤ (-x00) * (-x11) :=
    mul_le_mul (by linarith) (by linarith) hthree hneg00
  have hsecond : (3 * m) * m ≤ (-x01) * x10 :=
    mul_le_mul (by linarith) hx10 hm hneg01
  rw [hplucker]
  nlinarith

/-- The `Q`-Plucker product bound for a local block with rows `LR / LL`.
The variables are the `Q`-based cross-chord determinants. -/
theorem hullSixTwoFour_product_twelve_of_LR_LL
    {m y00 y01 y10 y11 E D : ℝ} (hm : 0 ≤ m)
    (hy00 : 3 * m ≤ y00) (hy01 : y01 ≤ -m)
    (hy10 : 3 * m ≤ y10) (hy11 : 3 * m ≤ y11)
    (hplucker : E * D = y00 * y11 - y01 * y10) :
    12 * m ^ 2 ≤ E * D := by
  have hthree : 0 ≤ 3 * m := by positivity
  have hneg01 : 0 ≤ -y01 := by linarith
  have hfirst : (3 * m) * (3 * m) ≤ y00 * y11 :=
    mul_le_mul hy00 hy11 hthree (by linarith)
  have hsecond : m * (3 * m) ≤ (-y01) * y10 :=
    mul_le_mul (by linarith) hy10 hthree (by linarith)
  rw [hplucker]
  nlinarith

/-- Scalar endpoint for every `2 + 4` tableau adapter which supplies an
adjacent Plucker product of at least twelve.  `capStrong` is the cross-block
fan area strengthened by the two line-level floors; the remaining four
named quantities are ordinary boundary fan areas. -/
theorem hullSixTwoFour_finish_of_product_twelve
    {H E D capOrdinary capStrong otherLower0 otherLower1 : ℝ}
    (hE : 1 ≤ E) (hD : 1 ≤ D)
    (hproduct : 12 ≤ E * D)
    (hcapOrdinary : 1 ≤ capOrdinary)
    (hcapStrong : 3 ≤ capStrong)
    (hotherLower0 : 1 ≤ otherLower0)
    (hotherLower1 : 1 ≤ otherLower1)
    (harea :
      H = E + D + capOrdinary + capStrong + otherLower0 + otherLower1) :
    (25 : ℝ) / 2 < H := by
  have hpair : (13 : ℝ) / 2 < E + D :=
    hullSixTwoFour_pair_gt_thirteen_halves
      (le_trans zero_le_one hE) (le_trans zero_le_one hD) hproduct
  rw [harea]
  linarith

/-- Scale-aware local-product endpoint, in the form used directly by a
geometric residual adapter. -/
theorem hullSixTwoFour_finish_of_product_twelve_mul
    {m H E D capOrdinary capStrong otherLower0 otherLower1 : ℝ}
    (hm : 0 < m) (hE : m ≤ E) (hD : m ≤ D)
    (hproduct : 12 * m ^ 2 ≤ E * D)
    (hcapOrdinary : m ≤ capOrdinary)
    (hcapStrong : 3 * m ≤ capStrong)
    (hotherLower0 : m ≤ otherLower0)
    (hotherLower1 : m ≤ otherLower1)
    (harea :
      H = E + D + capOrdinary + capStrong + otherLower0 + otherLower1) :
    25 * m < 2 * H := by
  have hpair : (13 : ℝ) / 2 * m < E + D :=
    hullSixTwoFour_pair_gt_thirteen_halves_mul hm hE hD hproduct
  rw [harea]
  linarith

/-- Dimension-neutral name for the preceding six-fan endpoint.  In the
`3 + 3` application the two `other` arguments are one upper and one lower
same-side edge rather than two lower edges. -/
theorem hullSixSixFan_finish_of_product_twelve_mul
    {m H E D capOrdinary capStrong other0 other1 : ℝ}
    (hm : 0 < m) (hE : m ≤ E) (hD : m ≤ D)
    (hproduct : 12 * m ^ 2 ≤ E * D)
    (hcapOrdinary : m ≤ capOrdinary)
    (hcapStrong : 3 * m ≤ capStrong)
    (hother0 : m ≤ other0) (hother1 : m ≤ other1)
    (harea : H = E + D + capOrdinary + capStrong + other0 + other1) :
    25 * m < 2 * H :=
  hullSixTwoFour_finish_of_product_twelve_mul hm hE hD hproduct
    hcapOrdinary hcapStrong hother0 hother1 harea

end Heilbronn8
