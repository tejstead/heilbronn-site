import Heilbronn8.TriHull.HullFive300UniversalCentralSigns
import Heilbronn8.TriHull.HullFive300UniversalNegativeEndpoint
import Heilbronn8.TriHull.HullFive300UniversalEELocal
import Heilbronn8.TriHull.HullFive300UniversalPM
import Heilbronn8.TriHull.HullFive300UniversalME
import Heilbronn8.TriHull.HullFive300UniversalMM
import Heilbronn8.TriHull.HullFive300UniversalPE
import Heilbronn8.TriHull.HullFive300UniversalPEQLt

set_option maxHeartbeats 0

/-!
# Uniform scalar dispatcher for the adjacent hull-five chart

This module joins the sign-specific scalar closures behind one raw adjacent
chart interface.  The four split signs are `delta`, `tau`, `axr`, and `bqd`.
The central signs are forced internally from the normalized area floors.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private lemma two_le_abs_cases {t : ℝ} (h : 2 ≤ |t|) :
    t ≤ -2 ∨ 2 ≤ t := by
  by_cases ht : 0 ≤ t
  · right
    simpa [abs_of_nonneg ht] using h
  · left
    have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht'] at h
    linarith

/-- Complete the positive-endpoint branch.  A negative auxiliary QR sign is
closed by the mixed-endpoint argument.  For a positive auxiliary QR sign,
`Q < Delta` is impossible and `Delta ≤ Q` is the direct PE closure. -/
theorem hullFive300_pe_complete_scalar
    {beta a b c d e f g x y z w p Q Delta A B N
      delta tau axr V earF eta H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hp : 2 ≤ p) (hQ : 2 ≤ Q) (hDelta : 2 ≤ Delta)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hN : 2 ≤ N)
    (hdelta : 2 ≤ delta) (htau : tau ≤ -2) (haxr : 2 ≤ axr)
    (hV : 2 ≤ V) (hearF : 2 ≤ earF) (hetaAbs : 2 ≤ |eta|)
    (hTlt : a + b + c + d + e + f + g < 21)
    (hBeta : beta = d + e + f)
    (hADef : A = e + Delta - p)
    (hBDef : B = a + Delta - Q)
    (hNDef : N = b + d - Delta)
    (hCentralE : e * N = d * A + f * Delta)
    (hCentralA : a * N = b * B + c * Delta)
    (hCentralG : a * e = p * Q + g * Delta)
    (hVDef : V = b + y - delta)
    (hearFDef : earF = z + w - f)
    (hAXRrow : b * axr = V * A - delta * f - y * e)
    (hfanQ : b * x = a * y + c * delta)
    (hEtaN : d * eta = -N * tau - z * Delta)
    (hEtaF : f * eta = A * z - N * w)
    (hEtaA : -A * tau = e * eta + w * Delta)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    25 ≤ H := by
  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he
  have hbetapos : 0 < beta := by
    rw [hBeta]
    linarith only [hd, he, hf]
  have hbetaLower : e + 4 ≤ beta := by
    rw [hBeta]
    linarith only [hd, hf]

  let t : ℝ := Delta - p
  let C0 : ℝ := e * (b - 2) - 2 * f
  have htA : t = A - e := by
    dsimp [t]
    rw [hADef]
    ring
  have hcentral1 : e * (b - Delta) = d * t + f * Delta := by
    have hCentralEExpanded := hCentralE
    rw [hNDef, hADef] at hCentralEExpanded
    dsimp [t]
    nlinarith only [hCentralEExpanded]
  have hC0id : C0 = d * t + (Delta - 2) * (e + f) := by
    dsimp [C0]
    nlinarith only [hcentral1]
  have hbetat : beta * t = b * e - p * (e + f) := by
    rw [hBeta]
    dsimp [t] at hcentral1 ⊢
    nlinarith only [hcentral1]
  have hrow : b * axr = V * t + b * e - delta * (e + f) := by
    rw [hAXRrow, htA, hVDef]
    ring
  have hrowUpper : b * axr ≤ V * t + C0 := by
    have hdeltaProd : 0 ≤ (delta - 2) * (e + f) :=
      mul_nonneg (sub_nonneg.mpr hdelta) (by
        linarith only [he, hf])
    dsimp [C0]
    nlinarith only [hrow, hdeltaProd]
  have hlocal : 2 * b ≤ V * t + C0 := by
    have hscaled := mul_le_mul_of_nonneg_left haxr hbpos.le
    nlinarith only [hscaled, hrowUpper]
  have hbt : beta * t ≤ C0 := by
    have hpProd : 0 ≤ (p - 2) * (e + f) :=
      mul_nonneg (sub_nonneg.mpr hp) (by
        linarith only [he, hf])
    dsimp [C0]
    nlinarith only [hbetat, hpProd]
  have hV0 : 0 ≤ V := le_trans (by norm_num) hV
  have hlocalScaled := mul_le_mul_of_nonneg_left hlocal hbetapos.le
  have htScaled := mul_le_mul_of_nonneg_left hbt hV0
  have hhard : 2 * b * beta ≤ C0 * (beta + V) := by
    nlinarith only [hlocalScaled, htScaled]
  have hC0pos : 0 < C0 := by
    have hleft : 0 < 2 * b * beta := by positivity
    have hsum : 0 < beta + V := by
      linarith only [hbetapos, hV0]
    have hprod : 0 < C0 * (beta + V) := lt_of_lt_of_le hleft hhard
    exact pos_of_mul_pos_left hprod hsum.le
  have hRupper : beta + V < 19 - a - g := by
    have hid : beta + V = H - (g + (a + x + delta) + earF) := by
      rw [hBeta, hVDef, hearFDef, hH]
      ring
    linarith only [hid, hHlt, hx, hdelta, hearF]
  have hR15 : beta + V < 15 := by
    linarith only [hRupper, ha, hg]
  have hstrict : 2 * b * beta < 15 * C0 := by
    have hmul := mul_lt_mul_of_pos_left hR15 hC0pos
    nlinarith only [hhard, hmul]
  have hP : 60 < 13 * b * e - 8 * b - 30 * e := by
    dsimp [C0] at hstrict
    have hscaled :=
      mul_le_mul_of_nonneg_left hbetaLower (by positivity : 0 ≤ 2 * b)
    nlinarith only [hstrict, hscaled, hf]
  have htCap : t ≤ Delta - 2 := by
    dsimp [t]
    linarith only [hp]
  have hCcap : C0 ≤ beta * (Delta - 2) := by
    rw [hC0id, hBeta]
    have hscaled :=
      mul_le_mul_of_nonneg_left htCap (by
        linarith only [hd] : 0 ≤ d)
    nlinarith only [hscaled]
  have hcommon : 2 * b ≤ (Delta - 2) * (beta + V) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hCcap (by
        linarith only [hbetapos, hV0] : 0 ≤ beta + V)
    have hchain : beta * (2 * b) ≤
        beta * ((Delta - 2) * (beta + V)) := by
      nlinarith only [hhard, hmul]
    exact le_of_mul_le_mul_left hchain hbetapos

  let rho : ℝ := -tau
  have hrho : 2 ≤ rho := by
    dsimp [rho]
    linarith only [htau]
  rcases two_le_abs_cases hetaAbs with hetaNeg | hetaPos
  · let m : ℝ := -eta
    have hm : 2 ≤ m := by
      dsimp [m]
      linarith only [hetaNeg]
    have hzSlope : Delta * z = N * rho + d * m := by
      dsimp [rho, m]
      nlinarith only [hEtaN]
    have hwSlope : Delta * w = A * rho + e * m := by
      dsimp [rho, m]
      nlinarith only [hEtaA]
    exact hnot (hullFive300_me_eta_neg_scalar
      (T := a + b + c + d + e + f + g)
      ha hb hc hd he hf hg hx hy hz hw hp hQ hA hN hDelta hrho hm
      (by linarith only [hNDef])
      (by ring) hTlt hH
      hCentralG hCentralE hzSlope hwSlope)
  · by_cases hQlt : Q < Delta
    · have hcentral : (a + b + c) * Delta = a * d + b * Q := by
        have hfactor : a * (d - Delta) =
            b * (Delta - Q) + c * Delta := by
          have hCentralAExpanded := hCentralA
          rw [hNDef, hBDef] at hCentralAExpanded
          nlinarith only [hCentralAExpanded]
        nlinarith only [hfactor]
      exact False.elim (hullFive300_pe_q_lt_delta_impossible
        ha hb hc hd he hf hg hDelta hTlt hcentral hQlt hP hcommon hRupper)
    · have hQge : Delta ≤ Q := le_of_not_gt hQlt
      exact hnot (hullFive300_pe_qge_eta_pos_scalar
        ha hb hc hd he hf hg hx hy hz hw hp hQge hDelta hA hB hN
        hdelta hetaPos haxr hV hearF hBeta hADef hBDef hNDef
        hCentralE hCentralA hCentralG hVDef hearFDef hAXRrow hfanQ
        (by nlinarith [hEtaF]) hH)

/-- Uniform raw scalar closure of the adjacent `3 + 0 + 0` chart. -/
theorem hullFive300_adjacent_scalar
    {a b c d e f g x y z w alpha beta T p Q Delta A B N W
      delta tau axr bqd u V k l E F ellR ellL xi eta H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hu : 2 ≤ u) (hV : 2 ≤ V) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hE : 2 ≤ E) (hF : 2 ≤ F)
    (hellR : 2 ≤ ellR) (hellL : 2 ≤ ellL)
    (hpAbs : 2 ≤ |p|) (hQAbs : 2 ≤ |Q|)
    (hDeltaAbs : 2 ≤ |Delta|) (hAAbs : 2 ≤ |A|)
    (hBAbs : 2 ≤ |B|) (hNAbs : 2 ≤ |N|)
    (hdeltaAbs : 2 ≤ |delta|) (htauAbs : 2 ≤ |tau|)
    (haxrAbs : 2 ≤ |axr|) (hbqdAbs : 2 ≤ |bqd|)
    (hxiAbs : 2 ≤ |xi|) (hetaAbs : 2 ≤ |eta|)
    (halpha : alpha = a + b + c)
    (hbeta : beta = d + e + f)
    (hT : T = alpha + beta + g)
    (hH : H = a + b + d + e + x + y + z + w + g)
    (huDef : u = a + x + delta)
    (hVDef : V = b + y - delta)
    (hkDef : k = d + z - tau)
    (hlDef : l = e + w + tau)
    (hEDef : E = x + y - c)
    (hFDef : F = z + w - f)
    (hAPQ : alpha * p = a * beta - b * g)
    (hBRP : beta * Q = e * alpha - d * g)
    (hDeltaLeft : alpha * Delta = a * d + b * Q)
    (hDeltaRight : beta * Delta = b * e + d * p)
    (hADef : A = Delta + e - p)
    (hBDef : B = Delta + a - Q)
    (hND : N + Delta = b + d)
    (hWDef : W = g + p + Q - Delta)
    (hTcentral : T = A + B + c + f + N + W)
    (hNW : N * W = A * (B + c) + B * f)
    (hDW : Delta * W = A * a + B * e - A * B)
    (haN : a * N = b * B + c * Delta)
    (heN : e * N = d * A + f * Delta)
    (hae : a * e = p * Q + g * Delta)
    (hfanQ : b * x = a * y + c * delta)
    (hfanR : d * w = e * z + f * tau)
    (hEllR : b * ellR = N * V - d * y)
    (hEllL : d * ellL = N * k - b * z)
    (hAXR : b * axr = V * A - delta * f - y * e)
    (hBQD : d * bqd = k * B - tau * c - z * a)
    (hAXRendpoint :
      a * axr = u * A - x * e - delta * (g + Q + e))
    (hBQDendpoint :
      e * bqd = l * B - w * a - tau * (g + a + p))
    (hXiN : b * xi = -N * delta - y * Delta)
    (hXiC : c * xi = B * y - N * x)
    (hXiB : -B * delta = a * xi + x * Delta)
    (hEtaN : d * eta = -N * tau - z * Delta)
    (hEtaF : f * eta = A * z - N * w)
    (hEtaA : -A * tau = e * eta + w * Delta) :
    25 ≤ H := by
  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have hHTEF : H = T + E + F := by
    rw [hH, hT, halpha, hbeta, hEDef, hFDef]
    ring
  have hTlt : T < 21 := by
    linarith only [hHTEF, hHlt, hE, hF]
  have hTsum : T = a + b + c + d + e + f + g := by
    rw [hT, halpha, hbeta]
    ring

  have hcentralSigns : 2 ≤ p ∧ 2 ≤ Q := by
    have hsigns := hullFive300_adjacent_central_signs (q := -Q)
      ha hb hc hd he hf hg halpha hbeta hT hTlt
      hpAbs (by simpa [abs_neg] using hQAbs) hDeltaAbs
      hAPQ
      (by
        calc
          beta * (-Q) = -(beta * Q) := by ring
          _ = -(e * alpha - d * g) := by rw [hBRP]
          _ = d * g - e * alpha := by ring)
      (by rw [hDeltaLeft]; ring) hDeltaRight
    exact ⟨hsigns.1, by linarith only [hsigns.2]⟩
  have hp : 2 ≤ p := hcentralSigns.1
  have hQ : 2 ≤ Q := hcentralSigns.2
  obtain ⟨hDelta, hA, hB, hN⟩ := hullFive300_adjacent_qr_signs
    ha hb hc hd he hf hg halpha hbeta hT hTlt hp hQ
    hDeltaAbs hAAbs hBAbs hNAbs hAPQ hBRP hDeltaLeft hADef hBDef haN

  have halphaNonneg : 0 ≤ alpha := by
    rw [halpha]
    linarith only [ha, hb, hc]
  have hbetaNonneg : 0 ≤ beta := by
    rw [hbeta]
    linarith only [hd, he, hf]
  have hAPQFloor : 2 * alpha ≤ a * beta - b * g := by
    calc
      2 * alpha = alpha * 2 := by ring
      _ ≤ alpha * p := mul_le_mul_of_nonneg_left hp halphaNonneg
      _ = a * beta - b * g := hAPQ
  have hBRPFloor : 2 * beta ≤ e * alpha - d * g := by
    calc
      2 * beta = beta * 2 := by ring
      _ ≤ beta * Q := mul_le_mul_of_nonneg_left hQ hbetaNonneg
      _ = e * alpha - d * g := hBRP

  have hNDef : N = b + d - Delta := by
    linarith only [hND]
  have hTatomLt : a + b + c + d + e + f + g < 21 := by
    rw [← hTsum]
    exact hTlt

  have hCentralLeft : beta * (A - e) = b * e - p * (e + f) := by
    rw [hADef]
    calc
      beta * (Delta + e - p - e) = beta * Delta - beta * p := by ring
      _ = (b * e + d * p) - beta * p := by rw [hDeltaRight]
      _ = b * e - p * (e + f) := by rw [hbeta]; ring
  have hCentralRight : alpha * (B - a) = d * a - Q * (a + c) := by
    rw [hBDef]
    calc
      alpha * (Delta + a - Q - a) = alpha * Delta - alpha * Q := by ring
      _ = (a * d + b * Q) - alpha * Q := by rw [hDeltaLeft]
      _ = d * a - Q * (a + c) := by rw [halpha]; ring
  have hAXRPM : b * axr = b * A + y * (A - e) - delta * (A + f) := by
    rw [hAXR, hVDef]
    ring
  have hBQDPM : d * bqd = d * B + z * (B - a) - tau * (B + c) := by
    rw [hBQD, hkDef]
    ring

  have hWA : W + A = g + Q + e := by
    rw [hWDef, hADef]
    ring
  have hWB : W + B = g + p + a := by
    rw [hWDef, hBDef]
    ring
  have hWpos : 0 < W := by
    have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
    have hRhsPos : 0 < A * (B + c) + B * f := by positivity
    by_contra hn
    have hWnonpos : W ≤ 0 := le_of_not_gt hn
    have hprod : N * W ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hNpos.le hWnonpos
    rw [hNW] at hprod
    exact (not_lt_of_ge hprod) hRhsPos

  have hAlphaA : alpha * A = b * (Q + e + g) + c * e - a * f := by
    calc
      alpha * A = alpha * (Delta + e - p) := by rw [hADef]
      _ = alpha * Delta + alpha * e - alpha * p := by ring
      _ = (a * d + b * Q) + alpha * e - (a * beta - b * g) := by
        rw [hDeltaLeft, hAPQ]
      _ = b * (Q + e + g) + c * e - a * f := by
        rw [halpha, hbeta]
        ring
  have hBetaB : beta * B = d * (p + a + g) + f * a - e * c := by
    calc
      beta * B = beta * (Delta + a - Q) := by rw [hBDef]
      _ = beta * Delta + beta * a - beta * Q := by ring
      _ = (b * e + d * p) + beta * a - (e * alpha - d * g) := by
        rw [hDeltaRight, hBRP]
      _ = d * (p + a + g) + f * a - e * c := by
        rw [halpha, hbeta]
        ring
  have hLeftBracket :
      alpha * A + f * (a + b) - c * e = b * (W + A + f) := by
    rw [hAlphaA, hWA]
    ring
  have hRightBracket :
      beta * B + c * (e + d) - f * a = d * (W + B + c) := by
    rw [hBetaB, hWB]
    ring

  have hMMShape :
      4 + (A - 2) * (B - 2) ≤
        ((A - 2) + (B - 2)) *
          (W + (A - 2) + (B - 2) - 2) := by
    have hid :
        ((A - 2) + (B - 2)) *
              (W + (A - 2) + (B - 2) - 2) -
            4 - (A - 2) * (B - 2) =
          (Delta - 2) ^ 2 +
            (g - 2) * (Delta - 2) +
            (g - 2) * (B - 2) +
            (g - 2) * (A - 2) +
            (e - 2) * (Delta - 2) +
            (e - 2) * (A - 2) +
            (a - 2) * (Delta - 2) +
            (a - 2) * (B - 2) +
            6 * (Delta - 2) + 2 * (g - 2) := by
      rw [hADef, hBDef, hWDef]
      linear_combination hae
    have hrhs : 0 ≤
          (Delta - 2) ^ 2 +
            (g - 2) * (Delta - 2) +
            (g - 2) * (B - 2) +
            (g - 2) * (A - 2) +
            (e - 2) * (Delta - 2) +
            (e - 2) * (A - 2) +
            (a - 2) * (Delta - 2) +
            (a - 2) * (B - 2) +
            6 * (Delta - 2) + 2 * (g - 2) := by positivity
    nlinarith only [hid, hrhs]

  have hPMLeft (hdelta : 2 ≤ delta) (htau : 2 ≤ tau)
      (haxr : 2 ≤ axr) : 25 ≤ H := by
    exact hullFive300_ppp_scalar
      ha hb hc hd he hf hg hx hy hz hw hp hA hdelta htau haxr hV hF
      halpha hbeta huDef hVDef hFDef hH hAPQFloor hCentralLeft hAXRPM
      hfanQ hfanR
  have hPMRight (hdelta : 2 ≤ delta) (htau : 2 ≤ tau)
      (hbqd : 2 ≤ bqd) : 25 ≤ H := by
    have hHreflected : H = e + d + b + a + w + z + y + x + g := by
      rw [hH]
      ring
    exact hullFive300_ppp_scalar
      he hd hf hb ha hc hg hw hz hy hx hQ hB htau hdelta hbqd hk hE
      (by rw [hbeta]; ring) (by rw [halpha]; ring)
      hlDef hkDef (by rw [hEDef]; ring) hHreflected
      hBRPFloor hCentralRight hBQDPM
      hfanR hfanQ

  have hEE (hdelta : delta ≤ -2) (htau : tau ≤ -2) : 25 ≤ H := by
    let sigma : ℝ := -delta
    let rho : ℝ := -tau
    have hsigma : 2 ≤ sigma := by
      dsimp [sigma]
      linarith only [hdelta]
    have hrho : 2 ≤ rho := by
      dsimp [rho]
      linarith only [htau]
    have hXsign : 2 ≤ xi ∨ xi ≤ -2 := by
      rcases two_le_abs_cases hxiAbs with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
    have hDsign : 2 ≤ eta ∨ eta ≤ -2 := by
      rcases two_le_abs_cases hetaAbs with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
    exact hullFive300_both_local_negative_scalar
      ha hb hc hd he hf hg hx hy hz hw hDelta hN hsigma hrho hA hB
      hND.symm haN heN
      (by dsimp [sigma]; nlinarith only [hfanQ])
      (by dsimp [rho]; nlinarith only [hfanR])
      (by dsimp [sigma]; nlinarith only [hXiN])
      (by dsimp [sigma]; nlinarith only [hXiB])
      (by dsimp [rho]; nlinarith only [hEtaN])
      (by dsimp [rho]; nlinarith only [hEtaA])
      (by dsimp [sigma]; nlinarith only [hu, huDef])
      (by dsimp [rho]; nlinarith only [hl, hlDef])
      hXsign hDsign hH

  have hMELeft (hdelta : 2 ≤ delta) (htau : tau ≤ -2)
      (haxr : axr ≤ -2) : 25 ≤ H := by
    let rho : ℝ := -tau
    let v : ℝ := -axr
    have hrho : 2 ≤ rho := by
      dsimp [rho]
      linarith only [htau]
    have hv : 2 ≤ v := by
      dsimp [v]
      linarith only [haxr]
    exact hullFive300_me_scalar
      ha hb hc hd he hf hg hx hy hz hw hp hQ hA hB hN hDelta
      hdelta hrho hV hv hellR hetaAbs
      hND hTsum hTcentral hTlt hH hNW hDW haN heN hae
      hVDef hEllR
      (by dsimp [v]; nlinarith only [hAXR])
      (by dsimp [rho]; nlinarith only [hEtaN]) hEtaF
      (by dsimp [rho]; nlinarith only [hfanR])
  have hMERight (hdelta : delta ≤ -2) (htau : 2 ≤ tau)
      (hbqd : bqd ≤ -2) : 25 ≤ H := by
    let rho : ℝ := -delta
    let v : ℝ := -bqd
    have hrho : 2 ≤ rho := by
      dsimp [rho]
      linarith only [hdelta]
    have hv : 2 ≤ v := by
      dsimp [v]
      linarith only [hbqd]
    have hHreflected : H = e + d + b + a + w + z + y + x + g := by
      rw [hH]
      ring
    exact hullFive300_me_scalar (W := W)
      he hd hf hb ha hc hg hw hz hy hx hQ hp hB hA hN hDelta
      htau hrho hk hv hellL hxiAbs
      (by simpa [add_comm] using hND)
      (by rw [hTsum]; ring) (by rw [hTcentral]; ring) hTlt hHreflected
      (by rw [hNW]; ring) (by rw [hDW]; ring) heN haN
      (by simpa [mul_comm] using hae) hkDef hEllL
      (by dsimp [v]; nlinarith only [hBQD])
      (by dsimp [rho]; nlinarith only [hXiN]) hXiC
      (by dsimp [rho]; nlinarith only [hfanQ])

  have hPELeft (hdelta : 2 ≤ delta) (htau : tau ≤ -2)
      (haxr : 2 ≤ axr) : 25 ≤ H := by
    exact hullFive300_pe_complete_scalar
      ha hb hc hd he hf hg hx hy hz hw hp hQ hDelta hA hB hN
      hdelta htau haxr hV hF hetaAbs hTatomLt hbeta
      (by rw [hADef]; ring) (by rw [hBDef]; ring) hNDef
      heN haN hae hVDef hFDef hAXR hfanQ hEtaN hEtaF hEtaA hH
  have hPERight (hdelta : delta ≤ -2) (htau : 2 ≤ tau)
      (hbqd : 2 ≤ bqd) : 25 ≤ H := by
    have hHreflected : H = e + d + b + a + w + z + y + x + g := by
      rw [hH]
      ring
    exact hullFive300_pe_complete_scalar
      he hd hf hb ha hc hg hw hz hy hx hQ hp hDelta hB hA hN
      htau hdelta hbqd hk hE hxiAbs
      (by linarith only [hTatomLt])
      (show alpha = b + a + c by rw [halpha]; ring)
      (by rw [hBDef]; ring) (by rw [hADef]; ring)
      (by nlinarith only [hND]) haN heN
      (by simpa [mul_comm] using hae)
      hkDef (by rw [hEDef]; ring) hBQD hfanR hXiN hXiC hXiB hHreflected

  have hNegative (hnegative :
      (delta ≤ -2 ∧ axr ≤ -2) ∨ (tau ≤ -2 ∧ bqd ≤ -2)) : 25 ≤ H := by
    exact hullFive300_negative_endpoint_scalar
      ha hb hd he hg hx hy hz hw hu hl hp hQ hA hB huDef hlDef
      hAXRendpoint hBQDendpoint hH hnegative

  have hMM (hdelta : 2 ≤ delta) (htau : 2 ≤ tau)
      (haxr : axr ≤ -2) (hbqd : bqd ≤ -2) : 25 ≤ H := by
    let r : ℝ := A - 2
    let q : ℝ := B - 2
    let C : ℝ := c - 2
    let F0 : ℝ := f - 2
    let n : ℝ := N - 2
    let X : ℝ := E - 2
    let Y : ℝ := F - 2
    have hr : 0 ≤ r := by
      dsimp [r]
      linarith only [hA]
    have hq : 0 ≤ q := by
      dsimp [q]
      linarith only [hB]
    have hC : 0 ≤ C := by
      dsimp [C]
      linarith only [hc]
    have hF0 : 0 ≤ F0 := by
      dsimp [F0]
      linarith only [hf]
    have hn : 0 ≤ n := by
      dsimp [n]
      linarith only [hN]
    have hX : 0 ≤ X := by
      dsimp [X]
      linarith only [hE]
    have hY : 0 ≤ Y := by
      dsimp [Y]
      linarith only [hF]
    have hWr : 4 ≤ W + r := by
      dsimp [r]
      linarith only [hWA, hg, hQ, he, hA]
    have hWq : 4 ≤ W + q := by
      dsimp [q]
      linarith only [hWB, hg, hp, ha, hB]
    have hNrow : (2 + n) * W =
        (2 + r) * (4 + q + C) + (2 + q) * (2 + F0) := by
      calc
        (2 + n) * W = N * W := by dsimp [n]; ring
        _ = A * (B + c) + B * f := hNW
        _ = (2 + r) * (4 + q + C) + (2 + q) * (2 + F0) := by
          dsimp [r, q, C, F0]
          ring

    have hLeftCore : a * (A + f) + c * (A - e) = b * W := by
      have h := hLeftBracket
      rw [halpha] at h
      linear_combination h
    have hAXRElimFactor :
        b * (x * (A + f) + c * axr - c * A - y * W) = 0 := by
      linear_combination
        (A + f) * hfanQ + c * hAXRPM + y * hLeftCore
    have hAXRElim : x * (A + f) + c * axr - c * A = y * W := by
      rcases mul_eq_zero.mp hAXRElimFactor with hbzero | hzero
      · exfalso
        linarith only [hb, hbzero]
      · linear_combination hzero
    have hLeftEarIdentity :
        (E - 2) * (A + f) - (2 * W - c * (f - 2)) =
          -c * (axr + 2) + (y - 2) * (W + A + f) := by
      rw [hEDef]
      linear_combination hAXRElim
    have hLeftDifference :
        0 ≤ (E - 2) * (A + f) - (2 * W - c * (f - 2)) := by
      have hcross : 0 ≤ -c * (axr + 2) := by
        have hprod : c * (axr + 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (by linarith only [hc]) (by linarith only [haxr])
        simpa only [neg_mul] using neg_nonneg.mpr hprod
      have hsum : 0 ≤ W + A + f := by
        rw [hWA]
        linarith only [hg, hQ, he, hf]
      have htail : 0 ≤ (y - 2) * (W + A + f) :=
        mul_nonneg (by linarith only [hy]) hsum
      rw [hLeftEarIdentity]
      exact add_nonneg hcross htail
    have hEarX : 2 * W - (2 + C) * F0 ≤ X * (4 + r + F0) := by
      dsimp [C, F0, X, r]
      nlinarith only [hLeftDifference]

    have hRightCore : e * (B + c) + f * (B - a) = d * W := by
      have h := hRightBracket
      rw [hbeta] at h
      linear_combination h
    have hBQDElimFactor :
        d * (w * (B + c) + f * bqd - f * B - z * W) = 0 := by
      linear_combination
        (B + c) * hfanR + f * hBQDPM + z * hRightCore
    have hBQDElim : w * (B + c) + f * bqd - f * B = z * W := by
      rcases mul_eq_zero.mp hBQDElimFactor with hdzero | hzero
      · exfalso
        linarith only [hd, hdzero]
      · linear_combination hzero
    have hRightEarIdentity :
        (F - 2) * (B + c) - (2 * W - f * (c - 2)) =
          -f * (bqd + 2) + (z - 2) * (W + B + c) := by
      rw [hFDef]
      linear_combination hBQDElim
    have hRightDifference :
        0 ≤ (F - 2) * (B + c) - (2 * W - f * (c - 2)) := by
      have hcross : 0 ≤ -f * (bqd + 2) := by
        have hprod : f * (bqd + 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (by linarith only [hf]) (by linarith only [hbqd])
        simpa only [neg_mul] using neg_nonneg.mpr hprod
      have hsum : 0 ≤ W + B + c := by
        rw [hWB]
        linarith only [hg, hp, ha, hc]
      have htail : 0 ≤ (z - 2) * (W + B + c) :=
        mul_nonneg (by linarith only [hz]) hsum
      rw [hRightEarIdentity]
      exact add_nonneg hcross htail
    have hEarY : 2 * W - (2 + F0) * C ≤ Y * (4 + q + C) := by
      dsimp [F0, C, Y, q]
      nlinarith only [hRightDifference]

    have h11 := hullFive300_mm_transformed_scalar
      hWpos hr hq hC hF0 hn hX hY hWr hWq
      (by simpa [r, q] using hMMShape) hNrow hEarX hEarY
    have hHshift : H = 14 + (W + r + q + C + F0 + n + X + Y) := by
      rw [hHTEF, hTcentral]
      dsimp [r, q, C, F0, n, X, Y]
      ring
    linarith only [h11, hHshift]

  rcases two_le_abs_cases hdeltaAbs with hdeltaNeg | hdeltaPos
  · rcases two_le_abs_cases htauAbs with htauNeg | htauPos
    · exact hnot (hEE hdeltaNeg htauNeg)
    · rcases two_le_abs_cases haxrAbs with haxrNeg | haxrPos
      · exact hnot (hNegative (Or.inl ⟨hdeltaNeg, haxrNeg⟩))
      · rcases two_le_abs_cases hbqdAbs with hbqdNeg | hbqdPos
        · exact hnot (hMERight hdeltaNeg htauPos hbqdNeg)
        · exact hnot (hPERight hdeltaNeg htauPos hbqdPos)
  · rcases two_le_abs_cases htauAbs with htauNeg | htauPos
    · rcases two_le_abs_cases hbqdAbs with hbqdNeg | hbqdPos
      · exact hnot (hNegative (Or.inr ⟨htauNeg, hbqdNeg⟩))
      · rcases two_le_abs_cases haxrAbs with haxrNeg | haxrPos
        · exact hnot (hMELeft hdeltaPos htauNeg haxrNeg)
        · exact hnot (hPELeft hdeltaPos htauNeg haxrPos)
    · rcases two_le_abs_cases haxrAbs with haxrNeg | haxrPos
      · rcases two_le_abs_cases hbqdAbs with hbqdNeg | hbqdPos
        · exact hnot (hMM hdeltaPos htauPos haxrNeg hbqdNeg)
        · exact hnot (hPMRight hdeltaPos htauPos hbqdPos)
      · exact hnot (hPMLeft hdeltaPos htauPos haxrPos)

end Heilbronn8.TriHull
