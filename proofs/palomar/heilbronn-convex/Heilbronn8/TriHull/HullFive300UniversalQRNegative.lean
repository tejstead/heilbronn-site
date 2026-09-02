import Heilbronn8.TriHull.HullFive300UniversalNegativeEndpoint

/-!
# The double-negative `QR` subcell of the remaining `--++` orbit

This source-only scalar lemma handles the subcell in which both auxiliary
triangles `XQR` and `DQR` have negative orientation.  It is independent of
the box cover.  The two exact Pluecker product chains force a stronger
normalized bound `H >= 26`.
-/

namespace Heilbronn8.TriHull

/-- A rational AM-GM substitute at product threshold thirty-six. -/
lemma hullFive300_product_thirty_six_sum_ge
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hproduct : 36 ≤ r * s) :
    12 ≤ r + s := by
  by_contra hnot
  have hsum : r + s < 12 := lt_of_not_ge hnot
  have hcapPos : 0 < 12 - (r + s) := sub_pos.mpr hsum
  have hplusPos : 0 < 12 + (r + s) := by linarith
  have hcapProduct := mul_pos hcapPos hplusPos
  have hsquare := sq_nonneg (r - s)
  nlinarith

/-- In the `delta,tau < 0`, `AXR,BQD > 0` outer cell, assume additionally
that `XQR,DQR < 0`.  Here `Delta=PQR`, `N=-CQR`, `j=-XQR`,
`m=-DQR`, `sigma=-delta`, and `rho=-tau`, all in the normalization where
every selected triangle magnitude is at least two.

The `QR` rows give
`Delta * (y+z-2) >= 6*N`; the two central rows give
`N * (a+e-2) >= 6*Delta`.  Their product yields the conclusion without any
division or square roots. -/
theorem hullFive300_ee_qr_negative_scalar
    {a b c d e f g x y z w Delta N j m sigma rho aqr bqr H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hDelta : 2 ≤ Delta) (hN : 2 ≤ N)
    (hj : 2 ≤ j) (hm : 2 ≤ m)
    (hsigma : 2 ≤ sigma) (hrho : 2 ≤ rho)
    (haqr : 2 ≤ aqr) (hbqr : 2 ≤ bqr)
    (hfan : b + d = N + Delta)
    (hcentralQ : a * N = b * bqr + c * Delta)
    (hcentralR : e * N = d * aqr + f * Delta)
    (hXQR : b * j = y * Delta - N * sigma)
    (hDQR : d * m = z * Delta - N * rho)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    26 ≤ H := by
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hDelta0 : 0 ≤ Delta := le_trans (by norm_num) hDelta
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hDeltaPos : 0 < Delta := lt_of_lt_of_le (by norm_num) hDelta

  have hbj := mul_le_mul_of_nonneg_left hj hb0
  have hdm := mul_le_mul_of_nonneg_left hm hd0
  have hNsigma := mul_le_mul_of_nonneg_left hsigma hN0
  have hNrho := mul_le_mul_of_nonneg_left hrho hN0
  have hQR : 6 * N ≤ Delta * (y + z - 2) := by
    nlinarith [hXQR, hDQR, hfan]

  have hbB := mul_le_mul_of_nonneg_left hbqr hb0
  have hdA := mul_le_mul_of_nonneg_left haqr hd0
  have hcDelta := mul_le_mul_of_nonneg_right hc hDelta0
  have hfDelta := mul_le_mul_of_nonneg_right hf hDelta0
  have hcentral : 6 * Delta ≤ N * (a + e - 2) := by
    nlinarith [hcentralQ, hcentralR, hfan]

  have hleftFactor : 0 ≤ a + e - 2 := by linarith
  have hrightFactor : 0 ≤ y + z - 2 := by linarith
  have hmul :
      (6 * Delta) * (6 * N) ≤
        (N * (a + e - 2)) * (Delta * (y + z - 2)) :=
    mul_le_mul hcentral hQR (by positivity) (by positivity)
  have hNDpos : 0 < N * Delta := mul_pos hNpos hDeltaPos
  have hrearranged :
      (N * Delta) * 36 ≤
        (N * Delta) * ((a + e - 2) * (y + z - 2)) := by
    calc
      (N * Delta) * 36 = (6 * Delta) * (6 * N) := by ring
      _ ≤ (N * (a + e - 2)) * (Delta * (y + z - 2)) := hmul
      _ = (N * Delta) * ((a + e - 2) * (y + z - 2)) := by ring
  have hproduct : 36 ≤ (a + e - 2) * (y + z - 2) :=
    le_of_mul_le_mul_left hrearranged hNDpos
  have hsum : 12 ≤ (a + e - 2) + (y + z - 2) :=
    hullFive300_product_thirty_six_sum_ge
      hleftFactor hrightFactor hproduct
  nlinarith [hH]

end Heilbronn8.TriHull
