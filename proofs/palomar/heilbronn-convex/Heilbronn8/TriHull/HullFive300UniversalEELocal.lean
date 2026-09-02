import Heilbronn8.TriHull.HullFive300UniversalQRMixed
import Heilbronn8.TriHull.HullFive300UniversalQRPositive

set_option maxHeartbeats 0

/-!
# A complete local-negative/local-negative hull-five closure

Assume `delta=-sigma` and `tau=-rho`, with `sigma,rho >= 2`.  The selected
triangles `XQR` and `DQR` each have magnitude at least two, so there are four
auxiliary sign cells.  The negative, mixed, reflected mixed, and positive QR
lemmas close those four cells respectively.

The resulting theorem is stronger than an outer-sign orbit closure: it does
not use either `AXR` or `BQD`.
-/

namespace Heilbronn8.TriHull

/-- If both local ear parameters have negative orientation, the normalized
hull fan has area at least twenty-five, independently of the two outer-cross
orientations. -/
theorem hullFive300_both_local_negative_scalar
    {a b c d e f g x y z w Delta N sigma rho aqr bqr xqr dqr H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hDelta : 2 ≤ Delta) (hN : 2 ≤ N)
    (hsigma : 2 ≤ sigma) (hrho : 2 ≤ rho)
    (haqr : 2 ≤ aqr) (hbqr : 2 ≤ bqr)
    (hfan : b + d = N + Delta)
    (hcentralQ : a * N = b * bqr + c * Delta)
    (hcentralR : e * N = d * aqr + f * Delta)
    (hearQ : c * sigma = a * y - b * x)
    (hearR : f * rho = e * z - d * w)
    (hXQRN : b * xqr = N * sigma - y * Delta)
    (hXQRB : bqr * sigma = a * xqr + x * Delta)
    (hDQRN : d * dqr = N * rho - z * Delta)
    (hDQRA : aqr * rho = e * dqr + w * Delta)
    (hU : 2 ≤ a + x - sigma)
    (hL : 2 ≤ e + w - rho)
    (hXsign : 2 ≤ xqr ∨ xqr ≤ -2)
    (hDsign : 2 ≤ dqr ∨ dqr ≤ -2)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    25 ≤ H := by
  rcases hXsign with hxpos | hxneg
  · rcases hDsign with hdpos | hdneg
    · have hXQRN' : N * sigma = b * xqr + y * Delta := by
        nlinarith [hXQRN]
      have hDQRN' : N * rho = d * dqr + z * Delta := by
        nlinarith [hDQRN]
      exact hullFive300_ee_qr_positive_scalar
        ha hb hc hd he hf hg hx hy hz hw hDelta hN hxpos hdpos
        haqr hbqr hfan hcentralQ hcentralR hXQRN' hXQRB
        hDQRN' hDQRA hH
    · have hj : 2 ≤ -dqr := by linarith
      have hXQR' : d * (-dqr) = z * Delta - N * rho := by
        nlinarith [hDQRN]
      have hDQR' : b * xqr = N * sigma - y * Delta := hXQRN
      have hHreflected :
          H = e + d + b + a + w + z + y + x + g := by
        rw [hH]
        ring
      exact hullFive300_ee_qr_mixed_scalar
        he hd hf hb ha hg hw hz hy hx hDelta hN hj hxpos
        hrho hsigma haqr (by linarith [hfan]) hcentralR hearR
        hXQR' hDQR' hU hHreflected
  · rcases hDsign with hdpos | hdneg
    · have hj : 2 ≤ -xqr := by linarith
      have hXQR' : b * (-xqr) = y * Delta - N * sigma := by
        nlinarith [hXQRN]
      exact hullFive300_ee_qr_mixed_scalar
        ha hb hc hd he hg hx hy hz hw hDelta hN hj hdpos
        hsigma hrho hbqr hfan hcentralQ hearQ hXQR' hDQRN hL hH
    · have hj : 2 ≤ -xqr := by linarith
      have hm : 2 ≤ -dqr := by linarith
      have hXQR' : b * (-xqr) = y * Delta - N * sigma := by
        nlinarith [hXQRN]
      have hDQR' : d * (-dqr) = z * Delta - N * rho := by
        nlinarith [hDQRN]
      have h26 := hullFive300_ee_qr_negative_scalar
        ha hb hc hd he hf hg hx hy hz hw hDelta hN hj hm
        hsigma hrho haqr hbqr hfan hcentralQ hcentralR
        hXQR' hDQR' hH
      linarith

end Heilbronn8.TriHull
