import Heilbronn8.TriHull.HullFive300UniversalScalar

/-!
# Negative-endpoint outer closures for hull-five `3 + 0 + 0`

Continue to encode the four outer signs as

`(delta = -[QPX], tau = [RPD], [AXR], [BQD])`.

A local negative sign paired with the negative cross sign on the same end is
already much stronger than the hull target:

* `delta <= -2` and `[AXR] <= -2` force `e + x >= 12`;
* `tau <= -2` and `[BQD] <= -2` force `a + w >= 12`.

Consequently this one reflected pair closes the outer orbits

`----`, `+--- / -+--`, `+-+- / -+-+`, and `--+- / ---+`.

At this stage, together with the independently checked hard `++++` closure,
the exact five remaining reflection orbits are

`+++- / ++-+`, `++--`, `--++`, `+-++ / -+++`, and `+--+ / -++-`.

The former claims that the first two of these were closed used incorrectly
signed cross identities and have been quarantined.  The later independent
`HullFive300UniversalEELocal` QR split closes `--++`, leaving the other four.
-/

namespace Heilbronn8.TriHull

/-- If two nonnegative shifted factors have product at least sixteen, their
unshifted sum is at least twelve. -/
lemma hullFive300_two_shifted_product_sum_ge
    {r s : ℝ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hproduct : 16 ≤ (r - 2) * (s - 2)) :
    12 ≤ r + s := by
  by_contra hnot
  have hsum : r + s < 12 := lt_of_not_ge hnot
  let X := r - 2
  let Y := s - 2
  have hX : 0 ≤ X := by dsimp [X]; linarith
  have hY : 0 ≤ Y := by dsimp [Y]; linarith
  have hXY : 16 ≤ X * Y := by simpa [X, Y] using hproduct
  have hsumXY : X + Y < 8 := by dsimp [X, Y]; linarith
  have hcapPos : 0 < 8 - (X + Y) := sub_pos.mpr hsumXY
  have hplusPos : 0 < 8 + (X + Y) := by linarith
  have hcapProduct := mul_pos hcapPos hplusPos
  have hsquare := sq_nonneg (X - Y)
  nlinarith

/-- Left negative endpoint: `delta <= -2` and `AXR <= -2` force the
normalized hull sum to be at least `26`. -/
theorem hullFive300_negative_left_endpoint_scalar
    {a b d e g x y z w delta u qneg aqr axr H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hu : 2 ≤ u) (hqneg : 2 ≤ qneg) (haqr : 2 ≤ aqr)
    (hdelta : delta ≤ -2) (haxr : axr ≤ -2)
    (huDef : u = a + x + delta)
    (hAXR : a * axr = u * aqr - x * e - delta * (g + qneg + e))
    (hH : H = a + b + d + e + x + y + z + w + g) :
    26 ≤ H := by
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have haxrScaled := mul_le_mul_of_nonneg_left haxr hapos.le
  have huaqrLower := mul_le_mul_of_nonneg_left haqr hu0
  have hnegDelta : 2 ≤ -delta := by linarith
  have hremainder0 : 0 ≤ g + qneg + e - 2 := by linarith
  have hdeltaRemainder :=
    mul_le_mul_of_nonneg_right hnegDelta hremainder0
  have hxe : 4 * a + 2 * x + 2 * g + 2 * e ≤ x * e := by
    nlinarith [hAXR, haxrScaled, huaqrLower, hdeltaRemainder, huDef]
  have hproduct : 16 ≤ (e - 2) * (x - 2) := by nlinarith
  have hex : 12 ≤ e + x :=
    hullFive300_two_shifted_product_sum_ge he hx hproduct
  nlinarith [hH]

/-- Right negative endpoint, the exact reflection of
`hullFive300_negative_left_endpoint_scalar`. -/
theorem hullFive300_negative_right_endpoint_scalar
    {a b d e g x y z w tau l p bqr bqd H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hl : 2 ≤ l) (hp : 2 ≤ p) (hbqr : 2 ≤ bqr)
    (htau : tau ≤ -2) (hbqd : bqd ≤ -2)
    (hlDef : l = e + w + tau)
    (hBQD : e * bqd = l * bqr - w * a - tau * (g + a + p))
    (hH : H = a + b + d + e + x + y + z + w + g) :
    26 ≤ H := by
  have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he
  have hl0 : 0 ≤ l := le_trans (by norm_num) hl
  have hbqdScaled := mul_le_mul_of_nonneg_left hbqd hepos.le
  have hlbqrLower := mul_le_mul_of_nonneg_left hbqr hl0
  have hnegTau : 2 ≤ -tau := by linarith
  have hremainder0 : 0 ≤ g + a + p - 2 := by linarith
  have htauRemainder :=
    mul_le_mul_of_nonneg_right hnegTau hremainder0
  have hwa : 4 * e + 2 * w + 2 * g + 2 * a ≤ w * a := by
    nlinarith [hBQD, hbqdScaled, hlbqrLower, htauRemainder, hlDef]
  have hproduct : 16 ≤ (a - 2) * (w - 2) := by nlinarith
  have haw : 12 ≤ a + w :=
    hullFive300_two_shifted_product_sum_ge ha hw hproduct
  nlinarith [hH]

/-- Combined reflection-pair dispatcher.  Either negative endpoint alone
forces the target; no assumption on the other endpoint's two signs is used. -/
theorem hullFive300_negative_endpoint_scalar
    {a b d e g x y z w delta tau u l p qneg aqr bqr axr bqd H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hu : 2 ≤ u) (hl : 2 ≤ l)
    (hp : 2 ≤ p) (hqneg : 2 ≤ qneg)
    (haqr : 2 ≤ aqr) (hbqr : 2 ≤ bqr)
    (huDef : u = a + x + delta)
    (hlDef : l = e + w + tau)
    (hAXR : a * axr = u * aqr - x * e - delta * (g + qneg + e))
    (hBQD : e * bqd = l * bqr - w * a - tau * (g + a + p))
    (hH : H = a + b + d + e + x + y + z + w + g)
    (hnegative :
      (delta ≤ -2 ∧ axr ≤ -2) ∨ (tau ≤ -2 ∧ bqd ≤ -2)) :
    25 ≤ H := by
  rcases hnegative with hleft | hright
  · have h26 := hullFive300_negative_left_endpoint_scalar
      ha hb hd he hg hx hy hz hw hu hqneg haqr
      hleft.1 hleft.2 huDef hAXR hH
    linarith
  · have h26 := hullFive300_negative_right_endpoint_scalar
      ha hb hd he hg hx hy hz hw hl hp hbqr
      hright.1 hright.2 hlDef hBQD hH
    linarith

end Heilbronn8.TriHull
