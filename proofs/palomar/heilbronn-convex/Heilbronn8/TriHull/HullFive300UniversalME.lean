import Heilbronn8.TriHull.HullFive300UniversalPM

set_option maxHeartbeats 0

/-!
# Rational closure of the mixed-endpoint `+--+ / -++-` orbit

This file is purely scalar.  In the representative used below, `delta > 0`,
`rho = -tau > 0`, and `v = -AXR > 0`.  The remaining auxiliary determinant
`eta = DQR` is split by sign.  Both branches are division-free after the
positive central factors are cleared.

The central change of variables is

* `A = AQR`, `B = BQR`, `D = PQR`, `N = -CQR`;
* `W = g + p + Q - D`, where `Q = -BPR`.

It satisfies

`T = A + B + c + f + N + W`,
`N W = A (B + c) + B f`, and
`D W = A a + B e - A B`.
-/

namespace Heilbronn8.TriHull

/-- The two-atom polynomial certificate used in the positive-`DQR` branch. -/
lemma hullFive300_me_af_certificate
    {A f : ℝ}
    (hA : 2 ≤ A) (hf : 2 ≤ f)
    (hS17 : A + f < 17)
    (hdisc : 16 * A + 8 * f < (17 - (A + f)) ^ 2) :
    81 * A * f ≤ 16 * (A + f) * (A + f + 2) := by
  let x : ℝ := A - 2
  let y : ℝ := f - 2
  let r : ℝ := x + y
  let K : ℝ := r ^ 2 - 34 * r + 121
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr13 : r < 13 := by dsimp [r, x, y]; linarith
  have hKx : 8 * x < K := by
    dsimp [K, r, x, y] at *
    nlinarith
  have hKpos : 0 < K := by nlinarith
  have hrCap : r < 17 / 4 := by
    by_contra hnot
    have hrGe : 17 / 4 ≤ r := le_of_not_gt hnot
    have hsecond : r + 17 / 4 - 34 < 0 := by linarith
    have hprod : (r - 17 / 4) * (r + 17 / 4 - 34) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hrGe) hsecond.le
    have hidentity :
        K = -87 / 16 + (r - 17 / 4) * (r + 17 / 4 - 34) := by
      dsimp [K]
      ring
    nlinarith
  have hrewrite :
      16 * (A + f) * (A + f + 2) - 81 * A * f =
        16 * r ^ 2 - 81 * x * y - 2 * r + 60 := by
    dsimp [r, x, y]
    ring
  rw [show
      81 * A * f ≤ 16 * (A + f) * (A + f + 2) ↔
        0 ≤ 16 * (A + f) * (A + f + 2) - 81 * A * f by
          constructor <;> intro h <;> linarith]
  rw [hrewrite]
  by_cases hrSmall : r ≤ 60 / 17
  · have hxy : 4 * x * y ≤ r ^ 2 := by
      dsimp [r]
      nlinarith [sq_nonneg (x - y)]
    have hfactor : 0 ≤ (60 - 17 * r) * (r + 4) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hrLarge : 60 / 17 < r := lt_of_not_ge hrSmall
    have hsecond : r + 60 / 17 - 38 < 0 := by linarith
    have hprod :
        (r - 60 / 17) * (r + 60 / 17 - 38) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hsecond.le
    have hKfourIdentity :
        K - 4 * r = -191 / 289 +
          (r - 60 / 17) * (r + 60 / 17 - 38) := by
      dsimp [K]
      ring
    have hKfour : K < 4 * r := by nlinarith
    have hxCap : x ≤ K / 8 := by linarith
    have hcapHalf : K / 8 ≤ r / 2 := by linarith
    have hcapMinus : 0 ≤ K / 8 - x := by linarith
    have hother : 0 ≤ r - K / 8 - x := by linarith
    have hxyCap : x * y ≤ (K / 8) * (r - K / 8) := by
      have hproduct := mul_nonneg hcapMinus hother
      dsimp [r] at hproduct
      nlinarith
    let Qpoly : ℝ :=
      64 * (16 * r ^ 2 - 2 * r + 60 -
        81 * (K / 8) * (r - K / 8))
    let u0 : ℝ := 17 * r - 60
    have hu0 : 0 ≤ u0 := by dsimp [u0]; linarith
    have hu17 : u0 < 17 := by dsimp [u0]; linarith
    have hQexpand :
        Qpoly = 81 * r ^ 4 - 6156 * r ^ 3 + 136294 * r ^ 2 -
          745004 * r + 1189761 := by
      dsimp [Qpoly, K]
      ring
    have hQshift :
        17 ^ 4 * Qpoly =
          2954961 + 6213668 * u0 + 22301206 * u0 ^ 2 -
            85212 * u0 ^ 3 + 81 * u0 ^ 4 := by
      rw [hQexpand]
      dsimp [u0]
      ring
    have hcoef : 0 ≤ 22301206 - 85212 * u0 := by linarith
    have hlinear : 0 ≤ 6213668 * u0 :=
      mul_nonneg (by norm_num) hu0
    have hquadratic : 0 ≤ u0 ^ 2 * (22301206 - 85212 * u0) :=
      mul_nonneg (sq_nonneg u0) hcoef
    have hquartic : 0 ≤ 81 * u0 ^ 4 := by positivity
    have hQnonneg : 0 ≤ Qpoly := by
      have h17 : (0 : ℝ) < 17 ^ 4 := by positivity
      nlinarith [hQshift, hlinear, hquadratic, hquartic]
    dsimp [Qpoly] at hQnonneg
    nlinarith

/-- The central rational inequality needed by the positive-`DQR` branch. -/
lemma hullFive300_me_central_ratio
    {A B c f N D a e W T : ℝ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hc : 2 ≤ c) (hf : 2 ≤ f)
    (hN : 2 ≤ N) (hD : 2 ≤ D) (ha : 2 ≤ a) (he : 2 ≤ e)
    (hT : T = A + B + c + f + N + W) (hTlt : T < 21)
    (hNW : N * W = A * (B + c) + B * f)
    (hDW : D * W = A * a + B * e - A * B)
    (haN : 2 * (B + c) ≤ a * N)
    (heN : 2 * (A + f) ≤ e * N) :
    15 ≤ a + e + 2 * (A + N) / f + 2 * (N + f) / A := by
  let S : ℝ := A + f
  let h : ℝ := a + e
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hfpos : 0 < f := lt_of_lt_of_le (by norm_num) hf
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNWpos : 0 < N * W := by
    rw [hNW]
    have hAR : 0 < A * (B + c) :=
      mul_pos hApos (by linarith)
    have hBf : 0 < B * f := mul_pos hBpos hfpos
    linarith
  have hWpos : 0 < W := by
    rcases (mul_pos_iff.mp hNWpos) with hpos | hneg
    · exact hpos.2
    · nlinarith
  have hDWlower : A * B + 2 * W ≤ A * a + B * e := by
    have hscaled := mul_le_mul_of_nonneg_right hD hWpos.le
    rw [hDW] at hscaled
    nlinarith

  have hhCleared : 2 * N + 2 * (S + 2) ≤ N * h := by
    by_cases hAB : B ≤ A
    · have hscaled := mul_le_mul_of_nonneg_left hDWlower hNpos.le
      have hgap : 0 ≤ (A - B) * (e * N - 2 * S) :=
        mul_nonneg (sub_nonneg.mpr hAB) (by simpa [S] using sub_nonneg.mpr heN)
      have hraw :
          A * (B * N + 2 * (S + c)) ≤ A * (N * h) := by
        dsimp [S, h] at *
        nlinarith [hNW]
      have hcancel : B * N + 2 * (S + c) ≤ N * h :=
        le_of_mul_le_mul_left (by simpa [mul_assoc] using hraw) hApos
      dsimp [S, h] at *
      nlinarith
    · have hBA : A ≤ B := le_of_not_ge hAB
      have hscaled := mul_le_mul_of_nonneg_left hDWlower hNpos.le
      have hgap : 0 ≤ (B - A) * (a * N - 2 * (B + c)) :=
        mul_nonneg (sub_nonneg.mpr hBA) (sub_nonneg.mpr haN)
      have hraw :
          B * (A * N + 2 * (B + c + f)) ≤ B * (N * h) := by
        dsimp [h] at *
        nlinarith [hNW]
      have hcancel : A * N + 2 * (B + c + f) ≤ N * h :=
        le_of_mul_le_mul_left (by simpa [mul_assoc] using hraw) hBpos
      dsimp [S, h] at *
      nlinarith

  have hNWlower : 4 * A + 2 * f ≤ N * W := by
    have hR : 4 ≤ B + c := by linarith
    have hAR := mul_le_mul_of_nonneg_left hR hApos.le
    have hBf := mul_le_mul_of_nonneg_right hB (le_trans (by norm_num) hf)
    rw [hNW]
    nlinarith
  have hSNW : S + N + W < 17 := by
    dsimp [S]
    rw [hT] at hTlt
    nlinarith
  have hSNWscaled := mul_lt_mul_of_pos_right hSNW hNpos
  have hq : N ^ 2 + (S - 17) * N + 4 * A + 2 * f < 0 := by
    nlinarith
  have hS17 : S < 17 := by nlinarith
  have hdisc : 16 * A + 8 * f < (17 - S) ^ 2 := by
    nlinarith [sq_nonneg (2 * N + S - 17)]
  have hAF : 81 * A * f ≤ 16 * S * (S + 2) := by
    simpa [S] using hullFive300_me_af_certificate hA hf hS17 hdisc

  have hAfpos : 0 < A * f := mul_pos hApos hfpos
  have hAfNpos : 0 < A * f * N := mul_pos hAfpos hNpos
  have hratio : 4 * A * f ≤ 2 * (A ^ 2 + f ^ 2) := by
    nlinarith [sq_nonneg (A - f)]
  let U : ℝ := 2 * A * f * (S + 2)
  let V : ℝ := 2 * N ^ 2 * S
  have hU : 0 ≤ U := by dsimp [U, S]; positivity
  have hV : 0 ≤ V := by dsimp [V, S]; positivity
  have hAFscaled := mul_le_mul_of_nonneg_left hAF
    (mul_nonneg (sq_nonneg N) hAfpos.le)
  have hUV : (9 * A * f * N) ^ 2 ≤ 4 * U * V := by
    dsimp [U, V]
    nlinarith
  have hsumSquare : (9 * A * f * N) ^ 2 ≤ (U + V) ^ 2 := by
    nlinarith [sq_nonneg (U - V)]
  have hcross : 9 * A * f * N ≤ U + V := by
    by_contra hnot
    have hlt : U + V < 9 * A * f * N := lt_of_not_ge hnot
    have hleft : 0 < 9 * A * f * N - (U + V) := by linarith
    have hright : 0 < 9 * A * f * N + (U + V) := by positivity
    have hprod := mul_pos hleft hright
    nlinarith

  have hhScaled := mul_le_mul_of_nonneg_left hhCleared hAfpos.le
  have hcleared :
      15 * (A * f * N) ≤
        (a + e + 2 * (A + N) / f + 2 * (N + f) / A) *
          (A * f * N) := by
    dsimp [S, h, U, V] at *
    field_simp [ne_of_gt hApos, ne_of_gt hfpos]
    nlinarith
  exact le_of_mul_le_mul_right (by simpa [mul_assoc] using hcleared) hAfNpos

/-- Positive auxiliary determinant in the mixed-endpoint orbit. -/
theorem hullFive300_me_eta_pos_scalar
    {a b c d e f g x y z w A B N D W T delta V v ell eta H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hN : 2 ≤ N) (hD : 2 ≤ D)
    (hdelta : 2 ≤ delta) (hV : 2 ≤ V) (hv : 2 ≤ v)
    (hell : 2 ≤ ell) (heta : 2 ≤ eta)
    (hND : N + D = b + d)
    (hT : T = A + B + c + f + N + W) (hTlt : T < 21)
    (hNW : N * W = A * (B + c) + B * f)
    (hDW : D * W = A * a + B * e - A * B)
    (haN : a * N = b * B + c * D)
    (heN : e * N = d * A + f * D)
    (hVDef : V = b + y - delta)
    (hEll : b * ell = N * V - d * y)
    (hVrow : b * v = delta * f + y * e - V * A)
    (hEta : f * eta = A * z - N * w)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    25 ≤ H := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hfpos : 0 < f := lt_of_lt_of_le (by norm_num) hf
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hRsum : N + D = b + d := hND
  have hRsumF : f * (N + D) = f * (b + d) :=
    congrArg (fun q : ℝ => f * q) hRsum
  have hcentralBracket : N * (e + f) - d * (A + f) = b * f := by
    ring_nf at hRsumF ⊢
    nlinarith [heN]
  have hEllScaled := mul_le_mul_of_nonneg_left hell (le_trans (by norm_num) hb)
  have hVScaled := mul_le_mul_of_nonneg_left hv (le_trans (by norm_num) hb)
  have hVrow' :
      b * v = b * f + y * (e + f) - V * (A + f) := by
    rw [hVrow, hVDef]
    ring
  have hVupper : (A + f) * V ≤ b * f + y * (e + f) - 2 * b := by
    nlinarith [hVrow']
  have hVlower : d * y + 2 * b ≤ N * V := by nlinarith [hEll]
  have hleftProduct := mul_le_mul_of_nonneg_left hVlower (by positivity : 0 ≤ A + f)
  have hrightProduct := mul_le_mul_of_nonneg_left hVupper (le_trans (by norm_num) hN)
  have hcentralY :
      y * (N * (e + f) - d * (A + f)) = y * (b * f) :=
    congrArg (fun q : ℝ => y * q) hcentralBracket
  have hY : 2 * (A + N) ≤ f * (N + y - 2) := by
    nlinarith [hcentralY]
  have hZ : 2 * (N + f) ≤ A * z := by
    have hetaScaled := mul_le_mul_of_nonneg_left heta (le_trans (by norm_num) hf)
    have hNw := mul_le_mul_of_nonneg_left hw (le_trans (by norm_num) hN)
    nlinarith [hEta]
  have haNlower : 2 * (B + c) ≤ a * N := by
    rw [haN]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hB),
      mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hD)]
  have heNlower : 2 * (A + f) ≤ e * N := by
    rw [heN]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hA),
      mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hD)]
  have hcentral := hullFive300_me_central_ratio
    hA hB hc hf hN hD ha he hT hTlt hNW hDW haNlower heNlower
  have hYdiv : 2 * (A + N) / f ≤ N + y - 2 :=
    (div_le_iff₀ hfpos).2 (by simpa [mul_comm] using hY)
  have hZdiv : 2 * (N + f) / A ≤ z :=
    (div_le_iff₀ hApos).2 (by simpa [mul_comm] using hZ)
  rw [hH]
  nlinarith [hcentral, hND]

/-- Negative auxiliary determinant in the mixed-endpoint orbit. -/
theorem hullFive300_me_eta_neg_scalar
    {a b c d e f g x y z w p Q A N D rho m T H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hp : 2 ≤ p) (hQ : 2 ≤ Q) (hA : 2 ≤ A)
    (hN : 2 ≤ N) (hD : 2 ≤ D) (hrho : 2 ≤ rho) (hm : 2 ≤ m)
    (hND : N + D = b + d)
    (hT : T = a + b + c + d + e + f + g) (hTlt : T < 21)
    (hH : H = a + b + d + e + x + y + z + w + g)
    (hae : a * e = p * Q + g * D)
    (heN : e * N = d * A + f * D)
    (hzSlope : D * z = N * rho + d * m)
    (hwSlope : D * w = A * rho + e * m) :
    25 ≤ H := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he
  have hD9 : D < 9 := by
    rw [hT] at hTlt
    nlinarith [hND]
  have hOuter : 2 * (A + N + d + e) ≤ D * (z + w) := by
    have hRhoProd : 2 * (A + N) ≤ rho * (A + N) := by
      have := mul_le_mul_of_nonneg_right hrho (by positivity : 0 ≤ A + N)
      nlinarith
    have hMProd : 2 * (d + e) ≤ m * (d + e) := by
      have := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ d + e)
      nlinarith
    nlinarith [hzSlope, hwSlope]
  let C : ℝ := 2 * D + 4
  have hCae : C ≤ a * e := by
    have hpQ : 4 ≤ p * Q := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hQ)]
    have hgD : 2 * D ≤ g * D := by
      exact mul_le_mul_of_nonneg_right hg (le_trans (by norm_num) hD)
    dsimp [C]
    rw [hae]
    nlinarith
  have hCeN : C ≤ e * N := by
    have hdA : 4 ≤ d * A := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hA)]
    have hfD : 2 * D ≤ f * D :=
      mul_le_mul_of_nonneg_right hf (le_trans (by norm_num) hD)
    dsimp [C]
    rw [heN]
    nlinarith
  have hDH :
      D * (a + N + D + e + 6) + 2 * (N + e + 4) ≤ D * H := by
    have hNDscaled : D * (N + D) = D * (b + d) :=
      congrArg (fun q : ℝ => D * q) hND
    have hxyzSum : 0 ≤ x + y + g - 6 := by linarith
    have hxyz : 0 ≤ D * (x + y + g - 6) :=
      mul_nonneg (le_trans (by norm_num) hD) hxyzSum
    rw [hH]
    nlinarith [hNDscaled, hOuter]
  have heDH := mul_le_mul_of_nonneg_left hDH (le_trans (by norm_num) he)
  have hDC := mul_le_mul_of_nonneg_left hCae (le_trans (by norm_num) hD)
  have hDplusC := mul_le_mul_of_nonneg_left hCeN (by positivity : 0 ≤ D + 2)
  let P : ℝ :=
    (D + 2) * e ^ 2 + (D ^ 2 - 19 * D + 8) * e +
      4 * (D + 2) * (D + 1)
  have hPbound : P ≤ e * D * (H - 25) := by
    dsimp [P, C] at *
    nlinarith
  let t : ℝ := D - 3
  let s : ℝ := e - 4
  let R : ℝ := -t ^ 2 + 42 * t + 135
  have htLow : -1 ≤ t := by dsimp [t]; linarith
  have htHigh : t < 6 := by dsimp [t]; linarith
  have hRidentity : R = (t + 1) * (6 - t) + 37 * (t + 1) + 92 := by
    dsimp [R]
    ring
  have hRpos : 0 < R := by
    rw [hRidentity]
    have hfirst : 0 ≤ (t + 1) * (6 - t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hPshift :
      P = (t + 5) * s ^ 2 + t * (t - 5) * s + 8 * t ^ 2 := by
    dsimp [P, t, s]
    ring
  have hSOS :
      4 * (t + 5) * P =
        (2 * (t + 5) * s + t * (t - 5)) ^ 2 + t ^ 2 * R := by
    rw [hPshift]
    dsimp [R]
    ring
  have hPnonneg : 0 ≤ P := by
    have ht5 : 0 < t + 5 := by linarith
    have hright : 0 ≤ (2 * (t + 5) * s + t * (t - 5)) ^ 2 + t ^ 2 * R :=
      add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg t) hRpos.le)
    by_contra hnot
    have hneg : 4 * (t + 5) * P < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht5) (lt_of_not_ge hnot)
    nlinarith [hSOS]
  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have hneg : e * D * (H - 25) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hepos hDpos) (by linarith)
  nlinarith

/-- Complete scalar dispatcher for the mixed-endpoint orbit. -/
theorem hullFive300_me_scalar
    {a b c d e f g x y z w p Q A B N D W T delta rho V v ell eta H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hp : 2 ≤ p) (hQ : 2 ≤ Q) (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hN : 2 ≤ N) (hD : 2 ≤ D) (hdelta : 2 ≤ delta)
    (hrho : 2 ≤ rho) (hV : 2 ≤ V) (hv : 2 ≤ v) (hell : 2 ≤ ell)
    (hetaAbs : 2 ≤ |eta|)
    (hND : N + D = b + d)
    (hT : T = a + b + c + d + e + f + g)
    (hT' : T = A + B + c + f + N + W) (hTlt : T < 21)
    (hH : H = a + b + d + e + x + y + z + w + g)
    (hNW : N * W = A * (B + c) + B * f)
    (hDW : D * W = A * a + B * e - A * B)
    (haN : a * N = b * B + c * D)
    (heN : e * N = d * A + f * D)
    (hae : a * e = p * Q + g * D)
    (hVDef : V = b + y - delta)
    (hEll : b * ell = N * V - d * y)
    (hVrow : b * v = delta * f + y * e - V * A)
    (hDQRd : d * eta = N * rho - z * D)
    (hDQRf : f * eta = A * z - N * w)
    (hfanR : f * rho = e * z - d * w) :
    25 ≤ H := by
  by_cases heta0 : 0 ≤ eta
  · have heta : 2 ≤ eta := by simpa [abs_of_nonneg heta0] using hetaAbs
    exact hullFive300_me_eta_pos_scalar
      ha hb hc hd he hf hg hx hy hz hw hA hB hN hD hdelta hV hv hell heta
      hND hT' hTlt hNW hDW haN heN hVDef hEll hVrow hDQRf hH
  · have hetaNeg : eta < 0 := lt_of_not_ge heta0
    let m : ℝ := -eta
    have hm : 2 ≤ m := by
      have hm' := hetaAbs
      rw [abs_of_neg hetaNeg] at hm'
      simpa [m] using hm'
    have hzSlope : D * z = N * rho + d * m := by
      dsimp [m]
      nlinarith [hDQRd]
    have hfactor : f * (e * eta - A * rho + D * w) = 0 := by
      calc
        f * (e * eta - A * rho + D * w) =
            e * (f * eta) - A * (f * rho) + f * D * w := by ring
        _ = e * (A * z - N * w) - A * (e * z - d * w) + f * D * w := by
          rw [hDQRf, hfanR]
        _ = w * (d * A + f * D - e * N) := by ring
        _ = 0 := by rw [← heN]; ring
    have hcross : e * eta - A * rho + D * w = 0 := by
      rcases mul_eq_zero.mp hfactor with hfzero | hzero
      · nlinarith
      · exact hzero
    have hwSlope : D * w = A * rho + e * m := by
      dsimp [m]
      nlinarith
    exact hullFive300_me_eta_neg_scalar
      ha hb hc hd he hf hg hx hy hz hw hp hQ hA hN hD hrho hm
      hND hT hTlt hH hae heN hzSlope hwSlope

end Heilbronn8.TriHull
