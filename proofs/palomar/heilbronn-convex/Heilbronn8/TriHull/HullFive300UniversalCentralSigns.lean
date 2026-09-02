import Heilbronn8.TriHull.HullFive300UniversalSigns

/-!
# The positive central QR chart for hull-five `3 + 0 + 0`

After the adjacent-fan argument has fixed `p = [APQ]` and
`Q = [BRP] = -[BPR]` as positive, the four remaining central QR
determinants are positive as soon as the normalized central triangle has
doubled area below `21`.

The proof uses only the exact adjacent-fan rows and the minimum-area absolute
floors.  In particular, it does not depend on any outer-ear sign.
-/

namespace Heilbronn8.TriHull

/-- Force the positive central QR chart.

The intended variables are

* `Delta = [PQR]`, `A = [AQR]`, `B = [BQR]`;
* `N = -[CQR]`;
* `p = [APQ]` and `Q = -[BPR] = [BRP]`.

All quantities are doubled areas normalized so that every nonzero selected
triangle has magnitude at least two.
-/
theorem hullFive300_adjacent_qr_signs
    {a b c d e f g alpha beta T p Q Delta A B N : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f) (hg : 2 ≤ g)
    (halpha : alpha = a + b + c)
    (hbeta : beta = d + e + f)
    (hT : T = alpha + beta + g) (hTlt : T < 21)
    (hp : 2 ≤ p) (hQ : 2 ≤ Q)
    (hDeltaAbs : 2 ≤ |Delta|)
    (hAAbs : 2 ≤ |A|) (hBAbs : 2 ≤ |B|) (hNAbs : 2 ≤ |N|)
    (hAPQ : alpha * p = a * beta - b * g)
    (hBRP : beta * Q = e * alpha - d * g)
    (hDeltaLeft : alpha * Delta = a * d + b * Q)
    (hAdef : A = Delta + e - p)
    (hBdef : B = Delta + a - Q)
    (hNrow : a * N = b * B + c * Delta) :
    2 ≤ Delta ∧ 2 ≤ A ∧ 2 ≤ B ∧ 2 ≤ N := by
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hbPos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hcPos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hdPos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hePos : 0 < e := lt_of_lt_of_le (by norm_num) he
  have hgPos : 0 < g := lt_of_lt_of_le (by norm_num) hg
  have halphaLower : a + 4 ≤ alpha := by rw [halpha]; linarith
  have hbetaLower : e + 4 ≤ beta := by rw [hbeta]; linarith
  have halphaPos : 0 < alpha := by linarith

  have hDeltaProductPos : 0 < alpha * Delta := by
    rw [hDeltaLeft]
    exact add_pos (mul_pos haPos hdPos) (mul_pos hbPos (by linarith))
  have hDeltaPos : 0 < Delta := by
    by_contra hnot
    have hDeltaNonpos : Delta ≤ 0 := le_of_not_gt hnot
    have hproduct :=
      mul_nonpos_of_nonneg_of_nonpos halphaPos.le hDeltaNonpos
    linarith
  have hDelta : 2 ≤ Delta := by
    simpa [abs_of_pos hDeltaPos] using hDeltaAbs

  have hAPos : 0 < A := by
    by_contra hnot
    have hANonpos : A ≤ 0 := le_of_not_gt hnot
    have hANeg : A ≤ -2 := by
      rw [abs_of_nonpos hANonpos] at hAAbs
      linarith
    rw [hAdef] at hANeg
    have hpSix : 6 ≤ p := by linarith
    have hpAlphaLower1 : 6 * (a + 4) ≤ p * (a + 4) :=
      mul_le_mul_of_nonneg_right hpSix (by linarith)
    have hpAlphaLower2 : p * (a + 4) ≤ p * alpha :=
      mul_le_mul_of_nonneg_left halphaLower (by linarith)
    have hpAlphaLower : 6 * (a + 4) ≤ p * alpha :=
      hpAlphaLower1.trans hpAlphaLower2
    have hpAlphaUpper : p * alpha < a * beta := by
      have hbg : 0 < b * g := mul_pos hbPos hgPos
      nlinarith [hAPQ]
    have hbetaUpper : beta < 15 - a := by
      linarith [hT]
    have haBetaUpper : a * beta < a * (15 - a) :=
      mul_lt_mul_of_pos_left hbetaUpper haPos
    have hquadratic : 6 * (a + 4) < a * (15 - a) :=
      hpAlphaLower.trans_lt (hpAlphaUpper.trans haBetaUpper)
    have hsquare := sq_nonneg (a - 9 / 2)
    nlinarith
  have hA : 2 ≤ A := by
    simpa [abs_of_pos hAPos] using hAAbs

  have hBPos : 0 < B := by
    by_contra hnot
    have hBNonpos : B ≤ 0 := le_of_not_gt hnot
    have hBNeg : B ≤ -2 := by
      rw [abs_of_nonpos hBNonpos] at hBAbs
      linarith
    rw [hBdef] at hBNeg
    have hQSix : 6 ≤ Q := by linarith
    have hQBetaLower1 : 6 * (e + 4) ≤ Q * (e + 4) :=
      mul_le_mul_of_nonneg_right hQSix (by linarith)
    have hQBetaLower2 : Q * (e + 4) ≤ Q * beta :=
      mul_le_mul_of_nonneg_left hbetaLower (by linarith)
    have hQBetaLower : 6 * (e + 4) ≤ Q * beta :=
      hQBetaLower1.trans hQBetaLower2
    have hQBetaUpper : Q * beta < e * alpha := by
      have hdg : 0 < d * g := mul_pos hdPos hgPos
      nlinarith [hBRP]
    have halphaUpper : alpha < 15 - e := by
      linarith [hT]
    have heAlphaUpper : e * alpha < e * (15 - e) :=
      mul_lt_mul_of_pos_left halphaUpper hePos
    have hquadratic : 6 * (e + 4) < e * (15 - e) :=
      hQBetaLower.trans_lt (hQBetaUpper.trans heAlphaUpper)
    have hsquare := sq_nonneg (e - 9 / 2)
    nlinarith
  have hB : 2 ≤ B := by
    simpa [abs_of_pos hBPos] using hBAbs

  have hNProductPos : 0 < a * N := by
    rw [hNrow]
    exact add_pos (mul_pos hbPos hBPos) (mul_pos hcPos hDeltaPos)
  have hNPos : 0 < N := by
    by_contra hnot
    have hNNonpos : N ≤ 0 := le_of_not_gt hnot
    have hproduct := mul_nonpos_of_nonneg_of_nonpos haPos.le hNNonpos
    linarith
  have hN : 2 ≤ N := by
    simpa [abs_of_pos hNPos] using hNAbs

  exact ⟨hDelta, hA, hB, hN⟩

end Heilbronn8.TriHull
