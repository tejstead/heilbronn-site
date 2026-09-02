import Heilbronn8.Survivors.Join.HullSixTwoFourLongSide

/-!
# Scalar closure for the `p = (0,4)` maximal-q frontier

The proof uses only the positive second `P`-row.  The two endpoint sectors
close when the last lower height is large.  When it is at most two, the
three lower recurrences, the two lower ears, and the translated final lower
edge force the four-sector middle block to have size at least `13 / 2`.

No `Q` cross-chord sign occurs in the scalar interface.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

/-- Scalar closure for the positive-row `p = (0,4)` frontier. -/
theorem hullSixTwoFour_p04MaximalQ_scalar
    {a b c d e f A C E0 E1 E2 F X11 X12 X13 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hC1 : 1 ≤ C) (hE01 : 1 ≤ E0)
    (hE11 : 1 ≤ E1) (hE21 : 1 ≤ E2)
    (hQ : 1 ≤ E2 - e + f)
    (hF : a + f + 1 ≤ F)
    (hAF : a + b * F ≤ f * A)
    (hRec1 : b * E1 = e * X11 - d * X12)
    (hRec2 : b * E2 = f * X12 - e * X13)
    (hX13 : 1 ≤ X13)
    (hHull : 1 ≤ C + E0 - X11)
    (hEar0 : d ≤ (d - c) * E1 - (e - d) * E0)
    (hEar1 : e ≤ (e - f) * E1 + (e - d) * E2)
    (hLong : 5 ≤ E0 + E1 + E2) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hE00 : 0 ≤ E0 := le_trans zero_le_one hE01
  have hE10 : 0 ≤ E1 := le_trans zero_le_one hE11
  have hE20 : 0 ≤ E2 := le_trans zero_le_one hE21
  have hF0 : 0 ≤ F := by linarith

  have hbF : F ≤ b * F := by
    simpa using mul_le_mul_of_nonneg_right hb1 hF0
  have hfA : f + 3 ≤ f * A := by
    nlinarith [hAF, hF]
  have hALower : 1 + 3 / f ≤ A := by
    have hdiv : (f + 3) / f ≤ A :=
      (div_le_iff₀ hf).2 (by simpa [mul_comm] using hfA)
    convert hdiv using 1 <;> field_simp [hf.ne'] <;> ring
  have hEndpoint : 3 + f + 3 / f ≤ A + F := by
    nlinarith [hALower, hF]
  have hMiddleSix : 6 ≤ C + E0 + E1 + E2 := by
    linarith

  by_cases hfHigh : 2 < f
  · have hfactor : 0 < (2 * f - 3) * (f - 2) := by
      exact mul_pos (by linarith) (by linarith)
    have hpoly : (7 : ℝ) / 2 * f < f ^ 2 + 3 := by
      nlinarith
    have hratio : (7 : ℝ) / 2 < f + 3 / f := by
      have hdiv : (7 : ℝ) / 2 < (f ^ 2 + 3) / f :=
        (lt_div_iff₀ hf).2 hpoly
      convert hdiv using 1 <;> field_simp [hf.ne'] <;> ring
    nlinarith [hEndpoint, hMiddleSix]
  · have hf2 : f ≤ 2 := le_of_not_gt hfHigh

    have heX13 : e ≤ e * X13 := by
      simpa using mul_le_mul_of_nonneg_left hX13 he.le
    have hfar : b * E2 + e ≤ f * X12 := by
      linarith [hRec2, heX13]
    have hX11Upper : X11 ≤ C + E0 - 1 := by linarith [hHull]
    have heX11 : e * X11 ≤ e * (C + E0 - 1) :=
      mul_le_mul_of_nonneg_left hX11Upper he.le
    have hfarScaled : d * (b * E2 + e) ≤ d * (f * X12) :=
      mul_le_mul_of_nonneg_left hfar hd.le
    have hrecBase : b * E1 + d * X12 = e * X11 := by
      linarith [hRec1]
    have hrecScaled :
        f * (b * E1 + d * X12) = f * (e * X11) := by
      exact congrArg (fun x : ℝ ↦ f * x) hrecBase
    have hcentralRaw :
        f * b * E1 + d * b * E2 + d * e ≤
          f * e * (C + E0 - 1) := by
      nlinarith [hfarScaled, hrecScaled,
        mul_le_mul_of_nonneg_left heX11 hf.le]
    have hcentralDiv :
        (f * b * E1 + d * b * E2 + d * e) / (f * e) ≤
          C + E0 - 1 := by
      apply (div_le_iff₀ (mul_pos hf he)).2
      nlinarith [hcentralRaw]
    have hcentralShape :
        (f * b * E1 + d * b * E2 + d * e) / (f * e) =
          b / e * E1 + d / f + b * d / (e * f) * E2 := by
      field_simp [hf.ne', he.ne'] <;> ring
    rw [hcentralShape] at hcentralDiv
    have hMiddleCore :
        1 + d / f + (1 + b / e) * E1 +
            (1 + b * d / (e * f)) * E2 ≤
          C + E0 + E1 + E2 := by
      nlinarith [hcentralDiv]

    have hMiddleLow : (13 : ℝ) / 2 ≤ C + E0 + E1 + E2 := by
      by_cases hed : e ≤ d
      · let s : ℝ := e - f
        have hsecond : (e - d) * E2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hed) hE20
        have hEarReduced : e ≤ (e - f) * E1 := by
          nlinarith [hEar1, hsecond]
        have hs : 0 < s := by
          dsimp [s]
          by_contra hnot
          have hnonpos : e - f ≤ 0 := le_of_not_gt hnot
          have hmul : (e - f) * E1 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hnonpos hE10
          nlinarith
        have hE1Lower : e / s ≤ E1 :=
          (div_le_iff₀ hs).2 (by simpa [s, mul_comm] using hEarReduced)
        have hE2Lower : 1 + s ≤ E2 := by
          dsimp [s]
          linarith [hQ]
        have hcoef1 : 1 + 1 / e ≤ 1 + b / e := by
          have hdiv : 1 / e ≤ b / e :=
            (div_le_div_iff_of_pos_right he).2 hb1
          linarith
        have hcoef10 : 0 ≤ 1 + 1 / e := by positivity
        have hcoef1b0 : 0 ≤ 1 + b / e := by positivity
        have hterm1a : (1 + 1 / e) * (e / s) ≤
            (1 + 1 / e) * E1 :=
          mul_le_mul_of_nonneg_left hE1Lower hcoef10
        have hterm1b : (1 + 1 / e) * E1 ≤
            (1 + b / e) * E1 :=
          mul_le_mul_of_nonneg_right hcoef1 hE10
        have hterm1 : (e + 1) / s ≤ (1 + b / e) * E1 := by
          calc
            (e + 1) / s = (1 + 1 / e) * (e / s) := by
              field_simp [he.ne', hs.ne'] <;> ring
            _ ≤ (1 + 1 / e) * E1 := hterm1a
            _ ≤ (1 + b / e) * E1 := hterm1b
        have hbd : e ≤ b * d := by
          have hdle : d ≤ b * d := by
            simpa using mul_le_mul_of_nonneg_right hb1 hd.le
          exact hed.trans hdle
        have hfrac : 1 / f ≤ b * d / (e * f) := by
          calc
            1 / f = e / (e * f) := by
              field_simp [he.ne', hf.ne'] <;> ring
            _ ≤ b * d / (e * f) :=
              (div_le_div_iff_of_pos_right (mul_pos he hf)).2 hbd
        have hcoef2 : 1 + 1 / f ≤ 1 + b * d / (e * f) := by
          linarith
        have hcoef20 : 0 ≤ 1 + 1 / f := by positivity
        have hterm2a : (1 + 1 / f) * (1 + s) ≤
            (1 + 1 / f) * E2 :=
          mul_le_mul_of_nonneg_left hE2Lower hcoef20
        have hterm2b : (1 + 1 / f) * E2 ≤
            (1 + b * d / (e * f)) * E2 :=
          mul_le_mul_of_nonneg_right hcoef2 hE20
        have hterm2 : (1 + 1 / f) * (1 + s) ≤
            (1 + b * d / (e * f)) * E2 := hterm2a.trans hterm2b
        have hdf : e / f ≤ d / f :=
          (div_le_div_iff_of_pos_right hf).2 hed
        have hExprBase :
            1 + e / f + (e + 1) / s + (1 + 1 / f) * (1 + s) ≤
              C + E0 + E1 + E2 := by
          nlinarith [hMiddleCore, hterm1, hterm2, hdf]
        have hExprShape :
            1 + e / f + (e + 1) / s + (1 + 1 / f) * (1 + s) =
              4 + s + (f + 1) / s + (2 * s + 1) / f := by
          have heq : e = f + s := by dsimp [s]; ring
          rw [heq]
          field_simp [hf.ne', hs.ne']
          ring
        have hExpr :
            4 + s + (f + 1) / s + (2 * s + 1) / f ≤
              C + E0 + E1 + E2 := by
          rw [← hExprShape]
          exact hExprBase
        have hfirst : s + (1 : ℝ) / 2 ≤ (2 * s + 1) / f := by
          apply (le_div_iff₀ hf).2
          have hnonneg : 0 ≤ s + (1 : ℝ) / 2 := by linarith
          have hmul := mul_le_mul_of_nonneg_right hf2 hnonneg
          nlinarith
        have hsecondFrac : 2 / s ≤ (f + 1) / s :=
          (div_le_div_iff_of_pos_right hs).2 (by linarith [hf1])
        have hamgm : 4 ≤ 2 * s + 2 / s := by
          have hsq : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
          have hdiv : 2 ≤ s + 1 / s := by
            rw [show s + 1 / s = (s ^ 2 + 1) / s by
              field_simp [hs.ne'] <;> ring]
            apply (le_div_iff₀ hs).2
            nlinarith
          calc
            (4 : ℝ) = 2 * 2 := by norm_num
            _ ≤ 2 * (s + 1 / s) :=
              mul_le_mul_of_nonneg_left hdiv (by norm_num)
            _ = 2 * s + 2 / s := by ring
        nlinarith [hExpr, hfirst, hsecondFrac, hamgm]
      · have hde : d < e := lt_of_not_ge hed
        let r : ℝ := d - c
        have hr : 0 < r := by
          dsimp [r]
          by_contra hnot
          have hdc : d - c ≤ 0 := le_of_not_gt hnot
          have hfirst : (d - c) * E1 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hdc hE10
          have hsecond : 0 ≤ (e - d) * E0 :=
            mul_nonneg (sub_nonneg.mpr (le_of_lt hde)) hE00
          nlinarith [hEar0]
        have hEarReduced : e ≤ r * E1 := by
          have hmul : e - d ≤ (e - d) * E0 := by
            simpa using mul_le_mul_of_nonneg_left hE01
              (sub_nonneg.mpr (le_of_lt hde))
          dsimp [r]
          nlinarith [hEar0]
        have hE1Lower : e / r ≤ E1 :=
          (div_le_iff₀ hr).2 (by simpa [mul_comm] using hEarReduced)

        by_cases hef : e ≤ f
        · have hfirstNonpos : (e - f) * E1 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hef) hE10
          have hEarFar : e ≤ (e - d) * E2 := by
            nlinarith [hEar1, hfirstNonpos]
          have hgap : 0 < e - d := sub_pos.mpr hde
          have hE2Lower : e / (e - d) ≤ E2 :=
            (div_le_iff₀ hgap).2 (by simpa [mul_comm] using hEarFar)
          have he2 : e ≤ 2 := le_trans hef hf2
          have hdgt1 : 1 < d := by
            dsimp [r] at hr
            linarith
          have h2r : 2 * r < e := by
            dsimp [r]
            nlinarith [hc1]
          have hE1gt2 : 2 < E1 := by
            have hdiv : 2 < e / r := (lt_div_iff₀ hr).2 h2r
            exact hdiv.trans_le hE1Lower
          have h2gap : 2 * (e - d) ≤ e := by nlinarith [hd1, he2]
          have hE2ge2 : 2 ≤ E2 := by
            have hdiv : 2 ≤ e / (e - d) :=
              (le_div_iff₀ hgap).2 h2gap
            exact hdiv.trans hE2Lower
          have hdf : (1 : ℝ) / 2 < d / f := by
            apply (lt_div_iff₀ hf).2
            nlinarith
          have hbe : (1 : ℝ) / 2 ≤ b / e := by
            apply (le_div_iff₀ he).2
            nlinarith [hb1, he2]
          have hef4 : e * f ≤ 4 := by
            have hprod : 0 ≤ (2 - e) * (2 - f) :=
              mul_nonneg (sub_nonneg.mpr he2) (sub_nonneg.mpr hf2)
            nlinarith
          have hbd1 : 1 ≤ b * d := by
            have hprod : 0 ≤ (b - 1) * (d - 1) :=
              mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hd1)
            nlinarith
          have hquarter : (1 : ℝ) / 4 ≤ b * d / (e * f) := by
            apply (le_div_iff₀ (mul_pos he hf)).2
            nlinarith [hef4, hbd1]
          have hterm1 : 3 < (1 + b / e) * E1 := by
            have hcoef : (3 : ℝ) / 2 ≤ 1 + b / e := by linarith
            have hmul := mul_lt_mul_of_pos_left hE1gt2 (by positivity :
              (0 : ℝ) < 3 / 2)
            have hmul2 := mul_le_mul_of_nonneg_right hcoef hE10
            nlinarith
          have hterm2 : (5 : ℝ) / 2 ≤
              (1 + b * d / (e * f)) * E2 := by
            have hcoef : (5 : ℝ) / 4 ≤
                1 + b * d / (e * f) := by linarith
            have hmul := mul_le_mul_of_nonneg_left hE2ge2
              (by positivity : (0 : ℝ) ≤ 5 / 4)
            have hmul2 := mul_le_mul_of_nonneg_right hcoef hE20
            nlinarith
          nlinarith [hMiddleCore, hdf, hterm1, hterm2]
        · have hfe : f < e := lt_of_not_ge hef
          have hE2Lower : 1 + e - f ≤ E2 := by linarith [hQ]
          have hcoef1 : 1 + 1 / e ≤ 1 + b / e := by
            have hdiv : 1 / e ≤ b / e :=
              (div_le_div_iff_of_pos_right he).2 hb1
            linarith
          have hterm1a : (1 + 1 / e) * (e / r) ≤
              (1 + 1 / e) * E1 :=
            mul_le_mul_of_nonneg_left hE1Lower (by positivity)
          have hterm1b : (1 + 1 / e) * E1 ≤
              (1 + b / e) * E1 :=
            mul_le_mul_of_nonneg_right hcoef1 hE10
          have hterm1 : (e + 1) / r ≤ (1 + b / e) * E1 := by
            calc
              (e + 1) / r = (1 + 1 / e) * (e / r) := by
                field_simp [he.ne', hr.ne'] <;> ring
              _ ≤ (1 + 1 / e) * E1 := hterm1a
              _ ≤ (1 + b / e) * E1 := hterm1b
          have hfrac : d / (e * f) ≤ b * d / (e * f) := by
            apply (div_le_div_iff_of_pos_right (mul_pos he hf)).2
            simpa using mul_le_mul_of_nonneg_right hb1 hd.le
          have hcoef2 : 1 + d / (e * f) ≤
              1 + b * d / (e * f) := by linarith
          have hterm2a : (1 + d / (e * f)) * (1 + e - f) ≤
              (1 + d / (e * f)) * E2 :=
            mul_le_mul_of_nonneg_left hE2Lower (by positivity)
          have hterm2b : (1 + d / (e * f)) * E2 ≤
              (1 + b * d / (e * f)) * E2 :=
            mul_le_mul_of_nonneg_right hcoef2 hE20
          have hterm2 : (1 + d / (e * f)) * (1 + e - f) ≤
              (1 + b * d / (e * f)) * E2 := hterm2a.trans hterm2b
          have hL :
              1 + d / f + (e + 1) / r +
                    (1 + d / (e * f)) * (1 + e - f) ≤
                C + E0 + E1 + E2 := by
            nlinarith [hMiddleCore, hterm1, hterm2]
          have hDiffE :
              0 ≤
                (e - d) / r +
                  (e - d) * (1 + (f - 1) / (e * f)) := by positivity
          have hShapeE :
              1 + d / f + (e + 1) / r +
                    (1 + d / (e * f)) * (1 + e - f) -
                  (1 + d / f + (d + 1) / r +
                    (1 + 1 / f) * (1 + d - f)) =
                (e - d) / r +
                  (e - d) * (1 + (f - 1) / (e * f)) := by
            field_simp [he.ne', hf.ne', hr.ne'] <;> ring
          have hLd :
              1 + d / f + (d + 1) / r +
                    (1 + 1 / f) * (1 + d - f) ≤
                C + E0 + E1 + E2 := by
            nlinarith [hL, hDiffE, hShapeE]
          have hdrc : 1 + r ≤ d := by
            dsimp [r]
            linarith [hc1]
          have hcoefD : 0 ≤ 1 / f + 1 / r + 1 + 1 / f := by positivity
          have hDiffD :
              0 ≤ (d - (1 + r)) *
                (1 / f + 1 / r + 1 + 1 / f) :=
            mul_nonneg (sub_nonneg.mpr hdrc) hcoefD
          have hShapeD :
              1 + d / f + (d + 1) / r +
                    (1 + 1 / f) * (1 + d - f) -
                  (4 + r - f + 2 / r + (2 * r + 3 - f) / f) =
                (d - (1 + r)) *
                  (1 / f + 1 / r + 1 + 1 / f) := by
            field_simp [hf.ne', hr.ne'] <;> ring
          have hG :
              4 + r - f + 2 / r + (2 * r + 3 - f) / f ≤
                C + E0 + E1 + E2 := by
            nlinarith [hLd, hDiffD, hShapeD]
          have hrf : r ≤ 2 * r / f := by
            apply (le_div_iff₀ hf).2
            have hmul : f * r ≤ 2 * r :=
              mul_le_mul_of_nonneg_right hf2 hr.le
            simpa [mul_comm] using hmul
          have hthree : (3 : ℝ) / 2 ≤ 3 / f := by
            apply (le_div_iff₀ hf).2
            nlinarith
          have hratioShape :
              (2 * r + 3 - f) / f = 2 * r / f + 3 / f - 1 := by
            field_simp [hf.ne'] <;> ring
          have hamgm : 4 ≤ 2 * r + 2 / r := by
            have hdiv : 2 ≤ r + 1 / r := by
              rw [show r + 1 / r = (r ^ 2 + 1) / r by
                field_simp [hr.ne'] <;> ring]
              apply (le_div_iff₀ hr).2
              nlinarith [sq_nonneg (r - 1)]
            calc
              (4 : ℝ) = 2 * 2 := by norm_num
              _ ≤ 2 * (r + 1 / r) :=
                mul_le_mul_of_nonneg_left hdiv (by norm_num)
              _ = 2 * r + 2 / r := by ring
          rw [hratioShape] at hG
          nlinarith [hG, hrf, hthree, hamgm]

    have hsq : 0 < (2 * f - 3) ^ 2 + 3 := by positivity
    have hpoly : 3 * f < f ^ 2 + 3 := by nlinarith
    have hratio : 3 < f + 3 / f := by
      have hdiv : 3 < (f ^ 2 + 3) / f := (lt_div_iff₀ hf).2 hpoly
      convert hdiv using 1 <;> field_simp [hf.ne'] <;> ring
    nlinarith [hEndpoint, hMiddleLow]

end Heilbronn8.Survivors.Join
