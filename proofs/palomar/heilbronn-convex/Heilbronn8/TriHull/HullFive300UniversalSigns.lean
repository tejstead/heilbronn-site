import Heilbronn8.TriHull.HullFive300UniversalScalar

set_option maxHeartbeats 0

/-!
# Forced central signs in the adjacent-fan hull-five `3 + 0 + 0` chart

Assume `Q` lies in `PBC` and `R` lies in `PCA`.  When the normalized central
triangle has doubled area below `21`, the minimum-area floors and the four
standard adjacent-fan identities force

* `[APQ] >= 2`, and
* `[BPR] <= -2`.

Thus these two central signs need not be split in the later outer-ear proof.
The remaining outer signs are deliberately not mentioned here.
-/

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

/-- The asymmetric half of the sign argument: the first adjacent cross-area
cannot be negative.  Applying the same lemma after the exact reflection
`a<->e`, `b<->d`, `c<->f`, `p<->-q` handles the second cross-area. -/
private lemma hullFive300_not_first_negative
    {a b c d e f g alpha beta T p q Delta : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (halpha : alpha = a + b + c)
    (hbeta : beta = d + e + f)
    (hT : T = alpha + beta + g) (hTlt : T < 21)
    (hpabs : 2 ≤ |p|) (hqabs : 2 ≤ |q|)
    (hDeltaAbs : 2 ≤ |Delta|)
    (hp : alpha * p = a * beta - b * g)
    (hq : beta * q = d * g - e * alpha)
    (hDeltaLeft : alpha * Delta = a * d - b * q)
    (hDeltaRight : beta * Delta = b * e + d * p) :
    ¬ p ≤ -2 := by
  intro hpneg
  have halpha6 : 6 ≤ alpha := by rw [halpha]; linarith
  have hbeta6 : 6 ≤ beta := by rw [hbeta]; linarith
  have halphaPos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha6
  have hbetaPos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta6
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he
  have halphaB : b + 4 ≤ alpha := by rw [halpha]; linarith
  have hbetaD : d + 4 ≤ beta := by rw [hbeta]; linarith

  have haBetaProduct : 12 ≤ a * beta := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hbeta6)
    nlinarith
  have hpMultiplied := mul_le_mul_of_nonneg_left hpneg halphaPos.le
  have hbgLower : 2 * b + 20 ≤ b * g := by
    nlinarith [hp, hpMultiplied, haBetaProduct, halphaB]
  have hbgSum : b + g < 11 := by
    nlinarith [hT, hTlt, halphaB, hbeta6]
  have hbSumMultiplied := mul_lt_mul_of_pos_left hbgSum hbpos
  have hbQuadratic : (b - 4) * (b - 5) < 0 := by
    nlinarith [hbgLower, hbSumMultiplied]
  have hb4 : 4 < b := by
    by_contra hnot
    have hb4' : b ≤ 4 := le_of_not_gt hnot
    have hprod := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hb4') (by linarith : b - 5 ≤ 0)
    linarith
  have hb5 : b < 5 := by
    by_contra hnot
    have hb5' : 5 ≤ b := le_of_not_gt hnot
    have hprod := mul_nonneg
      (by linarith : 0 ≤ b - 4) (sub_nonneg.mpr hb5')
    linarith
  have hg6 : 6 < g := by
    by_contra hnot
    have hg6' : g ≤ 6 := le_of_not_gt hnot
    have hbgUpper := mul_le_mul_of_nonneg_left hg6' hbpos.le
    nlinarith [hbgLower, hbgUpper, hb5]

  have hqneg : q ≤ -2 := by
    rcases two_le_abs_cases hqabs with hqneg | hqpos
    · exact hqneg
    · have heAlphaProduct : 12 ≤ e * alpha := by
        have hprod :=
          mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr halpha6)
        nlinarith
      have hqMultiplied :=
        mul_le_mul_of_nonneg_left hqpos hbetaPos.le
      have hdgLower : 2 * d + 20 ≤ d * g := by
        nlinarith [hq, hqMultiplied, heAlphaProduct, hbetaD]
      have hdgSum : d + g < 11 := by
        nlinarith [hT, hTlt, halpha6, hbetaD]
      have hdSumMultiplied := mul_lt_mul_of_pos_left hdgSum hdpos
      have hdQuadratic : (d - 4) * (d - 5) < 0 := by
        nlinarith [hdgLower, hdSumMultiplied]
      have hd4 : 4 < d := by
        by_contra hnot
        have hd4' : d ≤ 4 := le_of_not_gt hnot
        have hprod := mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr hd4') (by linarith : d - 5 ≤ 0)
        linarith
      exfalso
      rw [halpha, hbeta] at hT
      nlinarith

  have hadLower : 4 ≤ a * d := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hd)
    nlinarith
  have hbqUpper := mul_le_mul_of_nonneg_left hqneg hbpos.le
  have hAlphaDeltaPos : 0 < alpha * Delta := by
    rw [hDeltaLeft]
    nlinarith
  have hDeltaPos : 0 < Delta := by
    by_contra hnot
    have hDeltaNonpos : Delta ≤ 0 := le_of_not_gt hnot
    have := mul_nonpos_of_nonneg_of_nonpos halphaPos.le hDeltaNonpos
    linarith
  have hDelta2 : 2 ≤ Delta := by
    simpa [abs_of_pos hDeltaPos] using hDeltaAbs
  have hBetaDeltaLower :=
    mul_le_mul_of_nonneg_left hDelta2 hbetaPos.le
  have hdpUpper := mul_le_mul_of_nonneg_left hpneg hdpos.le
  have heProduct : 4 * d + 2 * f ≤ e * (b - 2) := by
    nlinarith [hDeltaRight, hBetaDeltaLower, hdpUpper, hbeta]
  have heProduct12 : 12 ≤ e * (b - 2) := by nlinarith
  have he4 : 4 < e := by
    by_contra hnot
    have he4' : e ≤ 4 := le_of_not_gt hnot
    have hleft := mul_lt_mul_of_pos_left (by linarith : b - 2 < 3) hepos
    have hright := mul_le_mul_of_nonneg_right he4' (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  rw [halpha, hbeta] at hT
  nlinarith

/-- Under adjacent fan occupancy and `T < 21`, the central signs are forced:
`p = [APQ]` is positive and `q = [BPR]` is negative.  In a normalized
minimum-area configuration their magnitudes are at least two. -/
theorem hullFive300_adjacent_central_signs
    {a b c d e f g alpha beta T p q Delta : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (halpha : alpha = a + b + c)
    (hbeta : beta = d + e + f)
    (hT : T = alpha + beta + g) (hTlt : T < 21)
    (hpabs : 2 ≤ |p|) (hqabs : 2 ≤ |q|)
    (hDeltaAbs : 2 ≤ |Delta|)
    (hp : alpha * p = a * beta - b * g)
    (hq : beta * q = d * g - e * alpha)
    (hDeltaLeft : alpha * Delta = a * d - b * q)
    (hDeltaRight : beta * Delta = b * e + d * p) :
    2 ≤ p ∧ q ≤ -2 := by
  have hpCases := two_le_abs_cases hpabs
  have hpNotNeg := hullFive300_not_first_negative
    ha hb hc hd he hf hg halpha hbeta hT hTlt
    hpabs hqabs hDeltaAbs hp hq hDeltaLeft hDeltaRight
  have hpPos : 2 ≤ p := hpCases.resolve_left hpNotNeg

  have hreflectedAlpha : beta = e + d + f := by rw [hbeta]; ring
  have hreflectedBeta : alpha = b + a + c := by rw [halpha]; ring
  have hreflectedT : T = beta + alpha + g := by rw [hT]; ring
  have hreflectedP : beta * (-q) = e * alpha - d * g := by
    rw [show beta * (-q) = -(beta * q) by ring, hq]
    ring
  have hreflectedQ : alpha * (-p) = b * g - a * beta := by
    rw [show alpha * (-p) = -(alpha * p) by ring, hp]
    ring
  have hreflectedDeltaLeft : beta * Delta = e * b - d * (-p) := by
    rw [hDeltaRight]
    ring
  have hreflectedDeltaRight : alpha * Delta = d * a + b * (-q) := by
    rw [hDeltaLeft]
    ring
  have hqNotPos : ¬ 2 ≤ q := by
    intro hqPos
    have hreflectedNotNeg := hullFive300_not_first_negative
      he hd hf hb ha hc hg hreflectedAlpha hreflectedBeta
      hreflectedT hTlt
      (by simpa [abs_neg] using hqabs)
      (by simpa [abs_neg] using hpabs) hDeltaAbs
      hreflectedP hreflectedQ hreflectedDeltaLeft hreflectedDeltaRight
    exact hreflectedNotNeg (by linarith)
  have hqCases := two_le_abs_cases hqabs
  exact ⟨hpPos, hqCases.resolve_right hqNotPos⟩

end Heilbronn8.TriHull
