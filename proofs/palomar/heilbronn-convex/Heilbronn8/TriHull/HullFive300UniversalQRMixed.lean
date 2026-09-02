import Heilbronn8.TriHull.HullFive300UniversalQRNegative

set_option maxHeartbeats 0

/-!
# A mixed `QR` subcell of the remaining `--++` orbit

This source-only scalar lemma handles the subcell with negative `XQR` and
positive `DQR`.  Reflection handles the opposite mixed subcell.  The proof
uses only exact Pluecker rows, minimum-area floors, and rational polynomial
inequalities.  It contains no division or square roots.
-/

namespace Heilbronn8.TriHull

/-- The rational gap used after clearing the two positive denominators.
The proof is split at `S = N + Delta = 8`; every nonlinear step is exposed
as a square or a product of nonnegative factors. -/
private lemma hullFive300_qr_mixed_rational_gap
    {N Delta S : ℝ}
    (hN : 2 ≤ N) (hDelta : 2 ≤ Delta)
    (hS : S = N + Delta) :
    N * Delta * (17 - S) <
      6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8 := by
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hDelta0 : 0 ≤ Delta := le_trans (by norm_num) hDelta
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hDeltaPos : 0 < Delta := lt_of_lt_of_le (by norm_num) hDelta
  have hS4 : 4 ≤ S := by rw [hS]; linarith
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS4
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS4
  have hNDpos : 0 < N * Delta := mul_pos hNpos hDeltaPos

  have hfirst :
      0 < 5 * (6 * Delta ^ 2 + 2 * N ^ 2) - 34 * N * Delta := by
    have hsquare := sq_nonneg (30 * Delta - 17 * N)
    have hNtwo : 0 < N ^ 2 := sq_pos_of_pos hNpos
    nlinarith
  have hsecond :
      0 < 5 * S * (8 * N + 4 * Delta) - 116 * N * Delta := by
    have hsquare := sq_nonneg (10 * N - 7 * Delta)
    have hDeltaTwo : 0 < Delta ^ 2 := sq_pos_of_pos hDeltaPos
    rw [hS]
    nlinarith

  by_cases hSlow : S ≤ 8
  · have hproduct : 4 * N * Delta ≤ S ^ 2 := by
      have hsquare := sq_nonneg (N - Delta)
      rw [hS]
      nlinarith
    have hSsquareCap : S ^ 2 ≤ 8 * S := by
      have hmul := mul_le_mul_of_nonneg_left hSlow hS0
      nlinarith
    have hthird : 0 ≤ 40 * S - 19 * N * Delta := by
      nlinarith [hproduct, hSsquareCap]
    have hfourth : 0 < 5 * S ^ 2 - 51 * S + 135 := by
      have hsquare := sq_nonneg (10 * S - 51)
      nlinarith
    have hfirstScaled :
        0 < S * (5 * (6 * Delta ^ 2 + 2 * N ^ 2) - 34 * N * Delta) :=
      mul_pos hSpos hfirst
    have hfourthScaled :
        0 < N * Delta * (5 * S ^ 2 - 51 * S + 135) :=
      mul_pos hNDpos hfourth
    have hdecomp :
        5 * S *
            ((6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8) -
              N * Delta * (17 - S)) =
          S * (5 * (6 * Delta ^ 2 + 2 * N ^ 2) - 34 * N * Delta) +
          (5 * S * (8 * N + 4 * Delta) - 116 * N * Delta) +
          (40 * S - 19 * N * Delta) +
          N * Delta * (5 * S ^ 2 - 51 * S + 135) := by
      ring
    have hscaled :
        0 < 5 * S *
          ((6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8) -
            N * Delta * (17 - S)) := by
      rw [hdecomp]
      nlinarith
    have hscalePos : 0 < 5 * S := by positivity
    have hgap :
        0 < (6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8) -
          N * Delta * (17 - S) := by
      by_contra hnot
      have hnonpos := le_of_not_gt hnot
      have hmul := mul_nonpos_of_nonneg_of_nonpos hscalePos.le hnonpos
      linarith
    linarith
  · have hS8 : 8 ≤ S := le_of_not_ge hSlow
    have hleft : 0 ≤ S - 8 := sub_nonneg.mpr hS8
    have hright : 0 ≤ 10 * S - 29 := by linarith
    have hfactor := mul_nonneg hleft hright
    have hthird : 0 ≤ 10 * S ^ 2 - 109 * S + 232 := by
      nlinarith
    have hfirstScaled :
        0 < 2 * S *
          (5 * (6 * Delta ^ 2 + 2 * N ^ 2) - 34 * N * Delta) := by
      positivity
    have hthirdScaled :
        0 ≤ N * Delta * (10 * S ^ 2 - 109 * S + 232) :=
      mul_nonneg (le_of_lt hNDpos) hthird
    have hSND : 0 ≤ S * N * Delta := by positivity
    have hdecomp :
        10 * S *
            ((6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8) -
              N * Delta * (17 - S)) =
          2 * S * (5 * (6 * Delta ^ 2 + 2 * N ^ 2) - 34 * N * Delta) +
          2 * (5 * S * (8 * N + 4 * Delta) - 116 * N * Delta) +
          N * Delta * (10 * S ^ 2 - 109 * S + 232) +
          80 * S + 7 * S * N * Delta := by
      ring
    have hscaled :
        0 < 10 * S *
          ((6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8) -
            N * Delta * (17 - S)) := by
      rw [hdecomp]
      nlinarith [hfirstScaled, hsecond, hthirdScaled, hSND]
    have hscalePos : 0 < 10 * S := by positivity
    have hgap :
        0 < (6 * Delta ^ 2 + 2 * N ^ 2 + 8 * N + 4 * Delta + 8) -
          N * Delta * (17 - S) := by
      by_contra hnot
      have hnonpos := le_of_not_gt hnot
      have hmul := mul_nonpos_of_nonneg_of_nonpos hscalePos.le hnonpos
      linarith
    linarith

/-- In the `delta,tau < 0`, `AXR,BQD > 0` outer cell, assume additionally
that `XQR < 0 < DQR`.  Here `sigma=-delta`, `rho=-tau`, `j=-XQR`,
`m=DQR`, `Delta=PQR`, and `N=-CQR`.  All quantities are normalized so every
selected triangle magnitude is at least two.

The conclusion is the target fan-area bound.  The reflected mixed subcell is
obtained by exchanging the two adjacent ears. -/
theorem hullFive300_ee_qr_mixed_scalar
    {a b c d e g x y z w Delta N j m sigma rho bqr H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hg : 2 ≤ g)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hDelta : 2 ≤ Delta) (hN : 2 ≤ N)
    (hj : 2 ≤ j) (hm : 2 ≤ m)
    (hsigma : 2 ≤ sigma) (hrho : 2 ≤ rho)
    (hbqr : 2 ≤ bqr)
    (hfan : b + d = N + Delta)
    (hcentralQ : a * N = b * bqr + c * Delta)
    (hearX : c * sigma = a * y - b * x)
    (hXQR : b * j = y * Delta - N * sigma)
    (hDQR : d * m = N * rho - z * Delta)
    (hleftEar : 2 ≤ e + w - rho)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    25 ≤ H := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg
  have hDelta0 : 0 ≤ Delta := le_trans (by norm_num) hDelta
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hbqr0 : 0 ≤ bqr := le_trans (by norm_num) hbqr
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hDeltaPos : 0 < Delta := lt_of_lt_of_le (by norm_num) hDelta
  have hND0 : 0 ≤ N * Delta := mul_nonneg hN0 hDelta0
  have hNDpos : 0 < N * Delta := mul_pos hNpos hDeltaPos

  have hbj : 2 * b ≤ b * j := by
    have hmul := mul_le_mul_of_nonneg_left hj hb0
    nlinarith
  have hXrow : N * sigma + 2 * b ≤ y * Delta := by
    nlinarith [hXQR, hbj]
  have hNsigma := mul_le_mul_of_nonneg_left hsigma hN0
  have hDy : 2 * (N + b) ≤ Delta * y := by
    nlinarith [hXrow, hNsigma]

  have hXrowA := mul_le_mul_of_nonneg_left hXrow ha0
  have hEarDelta :
      Delta * (c * sigma) = Delta * (a * y - b * x) :=
    congrArg (fun t : ℝ => Delta * t) hearX
  have hCentralSigma :
      sigma * (a * N) = sigma * (b * bqr + c * Delta) :=
    congrArg (fun t : ℝ => sigma * t) hcentralQ
  have hDxRaw :
      b * (sigma * bqr + 2 * a) ≤ b * (Delta * x) := by
    nlinarith [hXrowA, hEarDelta, hCentralSigma]
  have hDx : sigma * bqr + 2 * a ≤ Delta * x := by
    exact le_of_mul_le_mul_left hDxRaw hbpos
  have hsigmaB := mul_le_mul_of_nonneg_right hsigma hbqr0
  have hDxTwo : 2 * (bqr + a) ≤ Delta * x := by
    nlinarith [hDx, hsigmaB]
  have hleft :
      Delta * (a + b) + 2 * (a + bqr + b + N) ≤
        Delta * (a + b + x + y) := by
    nlinarith [hDxTwo, hDy]

  have hdm : 2 * d ≤ d * m := by
    have hmul := mul_le_mul_of_nonneg_left hm hd0
    nlinarith
  have hDrow : z * Delta + 2 * d ≤ N * rho := by
    nlinarith [hDQR, hdm]
  have hDz := mul_le_mul_of_nonneg_right hz hDelta0
  have hRho : 2 * (Delta + d) ≤ N * rho := by
    nlinarith [hDrow, hDz]
  have hEarN := mul_le_mul_of_nonneg_left hleftEar hN0
  have hNz := mul_le_mul_of_nonneg_right hz hN0
  have hright :
      4 * N + 2 * (Delta + d) ≤ N * (e + w + z) := by
    nlinarith [hRho, hEarN, hNz]

  have hbB := mul_le_mul_of_nonneg_left hbqr hb0
  have hcDelta := mul_le_mul_of_nonneg_right hc hDelta0
  have haN : 2 * (b + Delta) ≤ a * N := by
    nlinarith [hcentralQ, hbB, hcDelta]
  have hDeltaPlus : 0 ≤ Delta + 2 := by positivity
  have haNScaled := mul_le_mul_of_nonneg_right haN hDeltaPlus

  have hleftN := mul_le_mul_of_nonneg_left hleft hN0
  have hrightDelta := mul_le_mul_of_nonneg_left hright hDelta0
  have hgND := mul_le_mul_of_nonneg_right hg hND0
  have hHND :
      N * Delta * H =
        N * Delta * (a + b + d + e + x + y + z + w + g) :=
    congrArg (fun t : ℝ => N * Delta * t) hH
  have hraw :
      N * Delta * (a + b + d + 6) +
          2 * N * (a + bqr + b + N) + 2 * Delta * (Delta + d) ≤
        N * Delta * H := by
    nlinarith [hleftN, hrightDelta, hgND, hHND]

  have hfanND :
      N * Delta * (b + d) = N * Delta * (N + Delta) :=
    congrArg (fun t : ℝ => N * Delta * t) hfan
  have hfanDelta :
      Delta * (b + d) = Delta * (N + Delta) :=
    congrArg (fun t : ℝ => Delta * t) hfan
  have hbExcess : 0 ≤ b - 2 := sub_nonneg.mpr hb
  have hNbExcess : 0 ≤ N * (b - 2) := mul_nonneg hN0 hbExcess
  have hNBExcess : 0 ≤ N * (bqr - 2) :=
    mul_nonneg hN0 (sub_nonneg.mpr hbqr)
  have hcore :
      N * Delta * (N + Delta + 8) +
          6 * Delta ^ 2 + 4 * (Delta + 2) + 2 * N * (N + 4) ≤
        N * Delta * H := by
    nlinarith [hraw, haNScaled, hfanND, hfanDelta,
      hbExcess, hNbExcess, hNBExcess]

  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have hupper := mul_lt_mul_of_pos_left hHlt hNDpos
  have hgap := hullFive300_qr_mixed_rational_gap
    hN hDelta (show N + Delta = N + Delta from rfl)
  nlinarith [hcore, hupper, hgap]

end Heilbronn8.TriHull
