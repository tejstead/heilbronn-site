import Heilbronn8.TriHull.HullFive300UniversalEELocal

/-!
# A rational partial closure of the `+++- / ++-+` outer orbit

For the `+++-` representative, put `A=AQR`.  The subcell `A <= e` closes by
one corrected endpoint row and the opposite ear identity.  Reflection gives
the corresponding subcell of `++-+`.  No square roots or divisions are used.
-/

namespace Heilbronn8.TriHull

/-- Rational AM-GM at product threshold eight. -/
lemma hullFive300_product_eight_sum_gt
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hproduct : 8 ≤ r * s) :
    28 / 5 < r + s := by
  by_contra hnot
  have hsum : r + s ≤ 28 / 5 := le_of_not_gt hnot
  have hsum0 : 0 ≤ r + s := add_nonneg hr hs
  have hcap0 : 0 ≤ 28 / 5 - (r + s) := sub_nonneg.mpr hsum
  have hplus0 : 0 ≤ 28 / 5 + (r + s) := by linarith
  have hcapProduct := mul_nonneg hcap0 hplus0
  have hsquare := sq_nonneg (r - s)
  nlinarith

/-- The `delta,tau,AXR > 0` subcell with `AQR <= e` already forces the
normalized target.  The fourth outer sign is not used. -/
theorem hullFive300_ppp_aqr_le_e_scalar
    {a b d e f g x y z w A delta tau axr H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hd : 2 ≤ d)
    (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hA : 2 ≤ A) (hdelta : 2 ≤ delta)
    (htau : 2 ≤ tau) (haxr : 2 ≤ axr)
    (hAle : A ≤ e)
    (hAXRrow :
      b * axr = b * A + y * (A - e) - delta * (A + f))
    (hearR : f * tau = d * w - e * z)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    25 ≤ H := by
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have he0 : 0 ≤ e := le_trans (by norm_num) he
  have hf0 : 0 ≤ f := le_trans (by norm_num) hf
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hAplusF : 0 ≤ A + f := by linarith

  have haxrScaled := mul_le_mul_of_nonneg_left haxr hb0
  have hyTerm : y * (A - e) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hy0 (sub_nonpos.mpr hAle)
  have hdeltaScaled :=
    mul_le_mul_of_nonneg_right hdelta hAplusF
  have hBA : 2 * f + 4 ≤ (b - 2) * (A - 2) := by
    nlinarith [hAXRrow, haxrScaled, hyTerm, hdeltaScaled]
  have hbExcess : 0 ≤ b - 2 := sub_nonneg.mpr hb
  have htransfer := mul_le_mul_of_nonneg_left hAle hbExcess
  have hBE : 8 ≤ (b - 2) * (e - 2) := by
    nlinarith [hBA, htransfer]
  have hbe : 28 / 5 < (b - 2) + (e - 2) :=
    hullFive300_product_eight_sum_gt hbExcess (sub_nonneg.mpr he) hBE

  have hftau : 4 ≤ f * tau := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr htau)]
  have hez : 4 ≤ e * z := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hz)]
  have hdw : 8 ≤ d * w := by nlinarith [hearR]
  have hdwSum : 28 / 5 < d + w :=
    hullFive300_product_eight_sum_gt hd0 hw0 hdw
  nlinarith [hH]

end Heilbronn8.TriHull
