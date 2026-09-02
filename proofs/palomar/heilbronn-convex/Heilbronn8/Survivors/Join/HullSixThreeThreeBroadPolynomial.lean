import Mathlib

/-!
# The four-variable polynomial in the broad `3 x 3` chamber

This file is deliberately geometry-free.  It proves positivity of the
polynomial left after the two ear inequalities and the two product bounds
in the broad chamber have been eliminated.  The proof follows the rational
fixed-product argument: first isolate a positive quadratic in `U * v`, then
reduce every possibly negative coefficient to one of the two endpoints
`(U,v) = (U*v,1)` and `(1,U*v)`, and finally prove the endpoint by a chord
between `x*y = 1` and `x*y = 9`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The polynomial occurring in the active-boundary part of the broad
`3 x 3` scalar elimination. -/
def hullSixThreeThreeBroadPolynomial (x y U v : ℝ) : ℝ :=
  U ^ 2 * v ^ 2 +
    (x + 2 * y - x * y) * U ^ 2 * v +
    (2 * x + y - x * y) * U * v ^ 2 +
    (2 * x ^ 2 + 2 * y ^ 2 + 8 - x * y * (x + y)) * U * v +
    (x + 2) * (2 * x + y - x * y) * U +
    (y + 2) * (x + 2 * y - x * y) * v +
    (x + 2) * (y + 2)

private theorem broadPolynomial_sqrt_transfer
    {r rm s : ℝ}
    (hs : 2 ≤ s) (hr : r < rm)
    (hR : 9 ≤ r + 2 * s + 4)
    (hend :
      0 ≤ 2 * s ^ 2 - (s + 4) * rm + 8 +
        2 * Real.sqrt (rm + 2 * s + 4)) :
    0 < 2 * s ^ 2 - (s + 4) * r + 8 +
      2 * Real.sqrt (r + 2 * s + 4) := by
  let R : ℝ := r + 2 * s + 4
  let Rm : ℝ := rm + 2 * s + 4
  have hR0 : 0 ≤ R := by
    dsimp [R]
    linarith
  have hRm0 : 0 ≤ Rm := by
    dsimp [Rm]
    linarith
  have hRRm : R ≤ Rm := by
    dsimp [R, Rm]
    linarith
  have hsqrt_le : Real.sqrt R ≤ Real.sqrt Rm :=
    Real.sqrt_le_sqrt hRRm
  have hsqrtR_sq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  have hsqrtRm_sq : (Real.sqrt Rm) ^ 2 = Rm := Real.sq_sqrt hRm0
  have hsqrtR_nonneg : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hsqrtRm_nonneg : 0 ≤ Real.sqrt Rm := Real.sqrt_nonneg Rm
  have hsqrtR_three : 3 ≤ Real.sqrt R := by
    dsimp [R] at hR0 hsqrtR_sq hsqrtR_nonneg ⊢
    nlinarith
  have hsqrtRm_three : 3 ≤ Real.sqrt Rm := by
    have hRmNine : 9 ≤ Rm := le_trans hR hRRm
    nlinarith
  have hproduct :
      (Real.sqrt Rm - Real.sqrt R) *
          (Real.sqrt Rm + Real.sqrt R) = rm - r := by
    dsimp [R, Rm] at hsqrtR_sq hsqrtRm_sq
    nlinarith
  have hdiff_nonneg : 0 ≤ Real.sqrt Rm - Real.sqrt R := by
    linarith
  have hsum_six : 6 ≤ Real.sqrt Rm + Real.sqrt R := by
    linarith
  have haux :
      0 ≤ (Real.sqrt Rm - Real.sqrt R) *
        (Real.sqrt Rm + Real.sqrt R - 6) :=
    mul_nonneg hdiff_nonneg (by linarith)
  have hdiff_bound :
      6 * (Real.sqrt Rm - Real.sqrt R) ≤ rm - r := by
    nlinarith [hproduct]
  have hdelta : 0 < rm - r := by linarith
  have hlarge :
      6 * (rm - r) ≤ (s + 4) * (rm - r) := by
    exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdelta)
  have hgain :
      0 < (s + 4) * (rm - r) -
        2 * (Real.sqrt Rm - Real.sqrt R) := by
    nlinarith
  dsimp [R, Rm] at hend hgain ⊢
  nlinarith

private theorem broadPolynomial_quadratic_pos
    {r s m : ℝ}
    (hr1 : 1 < r) (hr9 : r < 9)
    (hs : 2 ≤ s) (hsquare : 4 * r ≤ s ^ 2)
    (hm : 0 < m) :
    0 < m ^ 2 + (2 * s ^ 2 - (s + 4) * r + 8) * m +
      (r + 2 * s + 4) := by
  let R : ℝ := r + 2 * s + 4
  have hRnine : 9 ≤ R := by
    dsimp [R]
    linarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hRnine
  have hsqrtR_sq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  have hf :
      0 < 2 * s ^ 2 - (s + 4) * r + 8 + 2 * Real.sqrt R := by
    by_cases hsix : s ≤ 6
    · let rm : ℝ := s ^ 2 / 4
      have hrrm : r ≤ rm := by
        dsimp [rm]
        linarith
      have hRm0 : 0 ≤ rm + 2 * s + 4 := by
        dsimp [rm]
        nlinarith [sq_nonneg (s + 4)]
      have hsqrtRm_sq :
          (Real.sqrt (rm + 2 * s + 4)) ^ 2 =
            rm + 2 * s + 4 := Real.sq_sqrt hRm0
      have hsqrtRm_nonneg :
          0 ≤ Real.sqrt (rm + 2 * s + 4) := Real.sqrt_nonneg _
      have hsqrtRm :
          Real.sqrt (rm + 2 * s + 4) = (s + 4) / 2 := by
        dsimp [rm] at hsqrtRm_sq ⊢
        have hcand : 0 ≤ (s + 4) / 2 := by linarith
        nlinarith
      have hfactor : 0 < s ^ 2 + 2 * s + 8 := by
        nlinarith [sq_nonneg (s + 1)]
      have hend_id :
          2 * s ^ 2 - (s + 4) * rm + 8 +
              2 * Real.sqrt (rm + 2 * s + 4) =
            (6 - s) * (s ^ 2 + 2 * s + 8) / 4 := by
        rw [hsqrtRm]
        dsimp [rm]
        ring
      by_cases heq : r = rm
      · have hslt : s < 6 := by
          subst r
          dsimp [rm] at hr9
          nlinarith
        dsimp [R]
        rw [heq, hend_id]
        exact div_pos (mul_pos (by linarith) hfactor) (by norm_num)
      · have hrlt : r < rm := lt_of_le_of_ne hrrm heq
        have hend :
            0 ≤ 2 * s ^ 2 - (s + 4) * rm + 8 +
              2 * Real.sqrt (rm + 2 * s + 4) := by
          rw [hend_id]
          positivity
        dsimp [R]
        exact broadPolynomial_sqrt_transfer hs hrlt hRnine hend
    · have hsix' : 6 < s := lt_of_not_ge hsix
      let rm : ℝ := 9
      have hRm0 : 0 ≤ rm + 2 * s + 4 := by
        dsimp [rm]
        linarith
      have hsqrtRm_sq :
          (Real.sqrt (rm + 2 * s + 4)) ^ 2 =
            rm + 2 * s + 4 := Real.sq_sqrt hRm0
      have hsqrtRm_nonneg :
          0 ≤ Real.sqrt (rm + 2 * s + 4) := Real.sqrt_nonneg _
      have hsqrtRm_five :
          5 ≤ Real.sqrt (rm + 2 * s + 4) := by
        dsimp [rm] at hsqrtRm_sq ⊢
        nlinarith
      have hend_id :
          2 * s ^ 2 - (s + 4) * rm + 8 +
              2 * Real.sqrt (rm + 2 * s + 4) =
            (s - 6) * (2 * s + 3) +
              2 * (Real.sqrt (2 * s + 13) - 5) := by
        dsimp [rm]
        have hsqrtArg : (9 : ℝ) + 2 * s + 4 = 2 * s + 13 := by ring
        rw [hsqrtArg]
        ring
      have hend :
          0 ≤ 2 * s ^ 2 - (s + 4) * rm + 8 +
            2 * Real.sqrt (rm + 2 * s + 4) := by
        rw [hend_id]
        have hfirst : 0 ≤ (s - 6) * (2 * s + 3) := by positivity
        have hsecond : 0 ≤ Real.sqrt (2 * s + 13) - 5 := by
          dsimp [rm] at hsqrtRm_five
          have hsqrtArg : (9 : ℝ) + 2 * s + 4 = 2 * s + 13 := by ring
          rw [hsqrtArg] at hsqrtRm_five
          exact sub_nonneg.mpr hsqrtRm_five
        positivity
      dsimp [R]
      exact broadPolynomial_sqrt_transfer hs hr9 hRnine hend
  have hdecomp :
      m ^ 2 + (2 * s ^ 2 - (s + 4) * r + 8) * m +
          (r + 2 * s + 4) =
        (m - Real.sqrt R) ^ 2 +
          (2 * s ^ 2 - (s + 4) * r + 8 + 2 * Real.sqrt R) * m := by
    nlinarith
  rw [hdecomp]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hf hm)

set_option maxHeartbeats 2000000 in
private theorem broadPolynomial_endpoint_right_pos
    {x y m : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hm : 0 < m) (hm1 : 1 ≤ m)
    (hxy1 : 1 < x * y) (hxy9 : x * y < 9)
    (halpha :
      m * (x + 2 * y - x * y) +
          (x + 2) * (2 * x + y - x * y) < 0) :
    0 < hullSixThreeThreeBroadPolynomial x y m 1 := by
  let A : ℝ := x + 2 * y - x * y
  let B : ℝ := 2 * x + y - x * y
  have halphaAB : m * A + (x + 2) * B < 0 := by
    simpa [A, B] using halpha
  have hx2 : 2 < x := by
    by_contra hnot
    have hxle : x ≤ 2 := le_of_not_gt hnot
    have hA : 0 < A := by
      have hnonneg : 0 ≤ y * (2 - x) :=
        mul_nonneg (le_of_lt hy) (sub_nonneg.mpr hxle)
      dsimp [A]
      nlinarith
    have hBneg : B < 0 := by
      by_contra hBn
      have hB : 0 ≤ B := le_of_not_gt hBn
      have hxplus : 0 < x + 2 := by linarith
      have hfirst : 0 < m * A := mul_pos hm hA
      have hsecond : 0 ≤ (x + 2) * B :=
        mul_nonneg (le_of_lt hxplus) hB
      linarith
    have hx1 : 1 < x := by
      by_contra hnot1
      have hxle1 : x ≤ 1 := le_of_not_gt hnot1
      have hnonneg : 0 ≤ y * (1 - x) :=
        mul_nonneg (le_of_lt hy) (sub_nonneg.mpr hxle1)
      dsimp [B] at hBneg
      nlinarith
    have hmul1 : 2 * x ^ 2 < (x * y) * (x - 1) := by
      have hbase : 2 * x < y * (x - 1) := by
        dsimp [B] at hBneg
        nlinarith
      have := mul_lt_mul_of_pos_left hbase hx
      nlinarith
    have hmul2 : (x * y) * (x - 1) < 9 * (x - 1) :=
      mul_lt_mul_of_pos_right hxy9 (by linarith)
    have hxthreehalves : (3 : ℝ) / 2 < x := by
      by_contra hnot15
      have hxle15 : x ≤ (3 : ℝ) / 2 := le_of_not_gt hnot15
      nlinarith [sq_nonneg (x - (3 : ℝ) / 2)]
    have hcoef : 4 - 2 * x - x ^ 2 < 0 := by
      nlinarith [sq_nonneg (x - (3 : ℝ) / 2)]
    have hxycoef :
        9 * (4 - 2 * x - x ^ 2) <
          (x * y) * (4 - 2 * x - x ^ 2) :=
      mul_lt_mul_of_neg_right hxy9 hcoef
    have hfactor :
        0 ≤ 2 * (x - 3) * (x - 2) * (x + 3) := by
      have h1 : x - 3 < 0 := by linarith
      have h2 : x - 2 ≤ 0 := by linarith
      have h3 : 0 < x + 3 := by linarith
      have hp : 0 ≤ (x - 3) * (x - 2) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt h1) h2
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      have htwoP : 0 ≤ 2 * ((x - 3) * (x - 2)) :=
        mul_nonneg htwo hp
      simpa only [mul_assoc] using mul_nonneg htwoP (le_of_lt h3)
    have hxE :
        0 < x * (A + (x + 2) * B) := by
      have hid :
          x * (A + (x + 2) * B) =
            2 * x ^ 3 + 5 * x ^ 2 +
              (x * y) * (4 - 2 * x - x ^ 2) := by
        dsimp [A, B]
        ring
      have hendpoint :
          2 * x ^ 3 + 5 * x ^ 2 +
              9 * (4 - 2 * x - x ^ 2) =
            2 * (x - 3) * (x - 2) * (x + 3) := by
        ring
      rw [hid]
      nlinarith
    have hE : 0 < A + (x + 2) * B := by
      exact pos_of_mul_pos_right hxE (le_of_lt hx)
    have hmA : 0 ≤ (m - 1) * A :=
      mul_nonneg (sub_nonneg.mpr hm1) (le_of_lt hA)
    have hrewrite :
        m * A + (x + 2) * B =
          (m - 1) * A + (A + (x + 2) * B) := by ring
    rw [hrewrite] at halphaAB
    linarith

  let r : ℝ := x * y
  let P1 : ℝ := hullSixThreeThreeBroadPolynomial x (1 / x) m 1
  let P9 : ℝ := hullSixThreeThreeBroadPolynomial x (9 / x) m 1
  have hr1 : 1 < r := by simpa [r] using hxy1
  have hr9 : r < 9 := by simpa [r] using hxy9
  have hxne : x ≠ 0 := ne_of_gt hx
  have hx2pos : 0 < x ^ 2 := sq_pos_of_pos hx

  have hP1_id :
      P1 =
        (m * x + 1) *
            (m * x ^ 2 + 2 * m + 4 * x ^ 3 + 4 * x ^ 2 + 5 * x + 2) /
          x ^ 2 := by
    dsimp [P1, hullSixThreeThreeBroadPolynomial]
    field_simp [hxne]
    ring
  have hP1_second :
      0 < m * x ^ 2 + 2 * m + 4 * x ^ 3 + 4 * x ^ 2 + 5 * x + 2 := by
    have hx3 : 0 < x ^ 3 := by positivity
    positivity
  have hP1 : 0 < P1 := by
    rw [hP1_id]
    exact div_pos (mul_pos (by positivity) hP1_second) hx2pos

  let alpha9 : ℝ :=
    m * (x + 2 * (9 / x) - x * (9 / x)) +
      (x + 2) * (2 * x + 9 / x - x * (9 / x))
  have hDpos :
      0 < (x - 2) * m + (x + 2) * (x - 1) := by
    have hfirst : 0 < (x - 2) * m := mul_pos (by linarith) hm
    have hsecond : 0 < (x + 2) * (x - 1) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have halpha9_diff :
      alpha9 - (m * A + (x + 2) * B) =
        -(9 - r) * ((x - 2) * m + (x + 2) * (x - 1)) / x := by
    dsimp [alpha9, A, B, r]
    field_simp [hxne]
    ring
  have halpha9 : alpha9 < 0 := by
    have hdiff :
        alpha9 - (m * A + (x + 2) * B) < 0 := by
      rw [halpha9_diff]
      have hnum : -(9 - r) *
          ((x - 2) * m + (x + 2) * (x - 1)) < 0 := by
        have hprod :
            0 < (9 - r) *
              ((x - 2) * m + (x + 2) * (x - 1)) :=
          mul_pos (by linarith) hDpos
        linarith
      exact div_neg_of_neg_of_pos hnum hx
    linarith

  have hP9 : 0 < P9 := by
    by_cases hx3case : x < 3
    · let aa : ℝ := x * (x ^ 2 - 8 * x + 18)
      let bb : ℝ := 4 * x ^ 4 - 12 * x ^ 3 - 10 * x ^ 2 - 54 * x + 162
      let cc : ℝ := 4 * x ^ 3 + 4 * x ^ 2 - 27 * x + 162
      let H : ℝ :=
        4 * x ^ 6 - 24 * x ^ 4 - 164 * x ^ 3 -
          108 * x ^ 2 - 324 * x + 729
      have haa : 0 < aa := by
        have hinner : 0 < x ^ 2 - 8 * x + 18 := by
          have hid : x ^ 2 - 8 * x + 18 = (x - 4) ^ 2 + 2 := by ring
          rw [hid]
          positivity
        exact mul_pos hx hinner
      have hx_sq_le : x ^ 2 ≤ 9 := by nlinarith
      have hx4nonneg : 0 ≤ 4 * x ^ 4 := by positivity
      have hpow6 : 4 * x ^ 6 ≤ 36 * x ^ 4 := by
        have ht := mul_le_mul_of_nonneg_left hx_sq_le hx4nonneg
        nlinarith
      have hx3pos : 0 < x ^ 3 := by positivity
      have hpow4 : 12 * x ^ 4 ≤ 36 * x ^ 3 := by
        have ht := mul_le_mul_of_nonneg_left (le_of_lt hx3case) (by positivity : 0 ≤ 12 * x ^ 3)
        nlinarith
      have hx_cube : 8 < x ^ 3 := by
        have hfac :
            0 < (x - 2) * (x ^ 2 + 2 * x + 4) := by
          exact mul_pos (by linarith) (by nlinarith [sq_nonneg (x + 1)])
        nlinarith
      have hH : H < 0 := by
        dsimp [H]
        nlinarith
      have hdisc_id :
          bb ^ 2 - 4 * aa * cc = 4 * (x - 3) ^ 2 * H := by
        dsimp [aa, bb, cc, H]
        ring
      have hdisc : bb ^ 2 - 4 * aa * cc < 0 := by
        rw [hdisc_id]
        have hsquarepos : 0 < (x - 3) ^ 2 := by
          exact sq_pos_of_ne_zero (by linarith)
        exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hsquarepos) hH
      have hnum_id :
          x ^ 2 * P9 = aa * m ^ 2 + bb * m + cc := by
        dsimp [P9, aa, bb, cc, hullSixThreeThreeBroadPolynomial]
        field_simp [hxne]
        ring
      have hquad_id :
          4 * aa * (aa * m ^ 2 + bb * m + cc) =
            (2 * aa * m + bb) ^ 2 - (bb ^ 2 - 4 * aa * cc) := by ring
      have hnum : 0 < aa * m ^ 2 + bb * m + cc := by
        have hrhs :
            0 < (2 * aa * m + bb) ^ 2 - (bb ^ 2 - 4 * aa * cc) := by
          nlinarith [sq_nonneg (2 * aa * m + bb)]
        have hfouraa : 0 < 4 * aa := by positivity
        nlinarith
      rw [← hnum_id] at hnum
      exact pos_of_mul_pos_right hnum (le_of_lt hx2pos)
    · have hx3le : 3 ≤ x := le_of_not_gt hx3case
      have hxne3 : x ≠ 3 := by
        intro heq
        subst x
        norm_num [alpha9] at halpha9
      by_cases hx6case : x < 6
      · have hx3 : 3 < x := lt_of_le_of_ne hx3le (Ne.symm hxne3)
        have h6mx : 0 < 6 - x := by linarith
        let n : ℝ := m - (x + 2) * (2 * x - 3) / (6 - x)
        have halpha9_factor :
            x * alpha9 =
              (x - 3) *
                (m * (x - 6) + (x + 2) * (2 * x - 3)) := by
          dsimp [alpha9]
          field_simp [hxne]
          ring
        have hbracket :
            m * (x - 6) + (x + 2) * (2 * x - 3) < 0 := by
          have hleft : x * alpha9 < 0 := mul_neg_of_pos_of_neg hx halpha9
          rw [halpha9_factor] at hleft
          rcases mul_neg_iff.mp hleft with hcase | hcase
          · exact hcase.2
          · linarith
        have hn : 0 < n := by
          dsimp [n]
          apply sub_pos.mpr
          apply (div_lt_iff₀ h6mx).2
          nlinarith
        let c2 : ℝ := x * (6 - x) ^ 2 * ((x - 4) ^ 2 + 2)
        let c1 : ℝ :=
          6 * (6 - x) * (x - 3) * (x ^ 3 + 21 * x - 54)
        let c0 : ℝ :=
          -x * (x - 3) ^ 2 *
            (4 * x ^ 4 - 16 * x ^ 3 - 89 * x ^ 2 - 300 * x - 180)
        have hc2 : 0 < c2 := by
          dsimp [c2]
          positivity
        have hcubic : 0 < x ^ 3 + 21 * x - 54 := by
          have hx_cube : 27 < x ^ 3 := by
            have hfac :
                0 < (x - 3) * (x ^ 2 + 3 * x + 9) := by
              exact mul_pos (by linarith) (by nlinarith [sq_nonneg (x + (3 : ℝ) / 2)])
            nlinarith
          linarith
        have hc1 : 0 < c1 := by
          dsimp [c1]
          positivity
        have hbracket0 :
            4 * x ^ 4 - 16 * x ^ 3 - 89 * x ^ 2 - 300 * x - 180 < 0 := by
          have hpow : 4 * x ^ 4 < 24 * x ^ 3 := by
            have ht := mul_lt_mul_of_pos_left hx6case (by positivity : 0 < 4 * x ^ 3)
            nlinarith
          have hxlin : 8 * x < 89 := by linarith
          have hrest : 8 * x ^ 3 < 89 * x ^ 2 := by
            have ht := mul_lt_mul_of_pos_right hxlin (sq_pos_of_pos hx)
            nlinarith
          nlinarith
        have hc0 : 0 < c0 := by
          dsimp [c0]
          have hfront : 0 < x * (x - 3) ^ 2 := by positivity
          nlinarith [mul_neg_of_pos_of_neg hfront hbracket0]
        have hshift :
            x ^ 2 * (6 - x) ^ 2 * P9 =
              c2 * n ^ 2 + c1 * n + c0 := by
          dsimp [P9, c2, c1, c0, n, hullSixThreeThreeBroadPolynomial]
          field_simp [hxne, ne_of_gt h6mx]
          ring
        have hrhs : 0 < c2 * n ^ 2 + c1 * n + c0 := by positivity
        have hden : 0 < x ^ 2 * (6 - x) ^ 2 := by positivity
        have hprod : 0 < x ^ 2 * (6 - x) ^ 2 * P9 := by
          rw [hshift]
          exact hrhs
        exact pos_of_mul_pos_right hprod (le_of_lt hden)
      · have hx6 : 6 ≤ x := le_of_not_gt hx6case
        have hA9 :
            0 ≤ x + 2 * (9 / x) - x * (9 / x) := by
          have hid :
              x + 2 * (9 / x) - x * (9 / x) =
                (x - 3) * (x - 6) / x := by
            field_simp [hxne]
            ring
          have hright : 0 ≤ (x - 3) * (x - 6) := by positivity
          rw [hid]
          exact div_nonneg hright (le_of_lt hx)
        have hB9 :
            0 < 2 * x + 9 / x - x * (9 / x) := by
          have hid :
              2 * x + 9 / x - x * (9 / x) =
                (x - 3) * (2 * x - 3) / x := by
            field_simp [hxne]
            ring
          have hx3pos : 0 < x - 3 := by linarith
          have h2x3pos : 0 < 2 * x - 3 := by linarith
          have hright : 0 < (x - 3) * (2 * x - 3) :=
            mul_pos hx3pos h2x3pos
          rw [hid]
          exact div_pos hright hx
        have hxplus : 0 < x + 2 := by positivity
        dsimp [alpha9] at halpha9
        have hfirst : 0 ≤ m * (x + 2 * (9 / x) - x * (9 / x)) :=
          mul_nonneg (le_of_lt hm) hA9
        have hsecond :
            0 < (x + 2) * (2 * x + 9 / x - x * (9 / x)) :=
          mul_pos hxplus hB9
        linarith

  have hactual :
      hullSixThreeThreeBroadPolynomial x y m 1 =
        hullSixThreeThreeBroadPolynomial x (r / x) m 1 := by
    have hry : r / x = y := by
      dsimp [r]
      field_simp [hxne] <;> ring
    rw [hry]
  have hchord :
      hullSixThreeThreeBroadPolynomial x (r / x) m 1 -
          ((9 - r) * P1 + (r - 1) * P9) / 8 =
        -(m + 1) * (r - 9) * (r - 1) * (x - 2) / x ^ 2 := by
    dsimp [P1, P9, hullSixThreeThreeBroadPolynomial]
    field_simp [hxne]
    ring
  have hweighted : 0 < ((9 - r) * P1 + (r - 1) * P9) / 8 := by
    apply div_pos
    · exact add_pos (mul_pos (by linarith) hP1) (mul_pos (by linarith) hP9)
    · norm_num
  have hcorrection :
      0 < -(m + 1) * (r - 9) * (r - 1) * (x - 2) / x ^ 2 := by
    apply div_pos
    · have h1 : 0 < m + 1 := by linarith
      have h2 : r - 9 < 0 := by linarith
      have h3 : 0 < r - 1 := by linarith
      have h4 : 0 < x - 2 := by linarith
      have hfirst : 0 < -(m + 1) * (r - 9) := by
        have hneg : (m + 1) * (r - 9) < 0 := mul_neg_of_pos_of_neg h1 h2
        linarith
      exact mul_pos (mul_pos hfirst h3) h4
    · exact hx2pos
  rw [hactual]
  linarith [hchord]

set_option maxHeartbeats 1000000

/-- Positivity of the broad active-boundary polynomial below the sharp
central product `x*y = 9`.

The inequalities `1 ≤ U,v` are the four surviving adjacent-fan floors after
the two product constraints have been substituted.  Strictness at the upper
endpoint is useful to the scalar wrapper: a hypothetical `x*y < 9` produces
an immediate contradiction with its cleared `F ≤ G` inequality. -/
theorem hullSixThreeThreeBroadPolynomial_pos
    {x y U v : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hU : 1 ≤ U) (hv : 1 ≤ v)
    (hxy1 : 1 < x * y) (hxy9 : x * y < 9) :
    0 < hullSixThreeThreeBroadPolynomial x y U v := by
  let r : ℝ := x * y
  let s : ℝ := x + y
  let m : ℝ := U * v
  let A : ℝ := x + 2 * y - x * y
  let B : ℝ := 2 * x + y - x * y
  let C : ℝ := 2 * x ^ 2 + 2 * y ^ 2 + 8 - x * y * (x + y)
  let R : ℝ := (x + 2) * (y + 2)
  let Q : ℝ := m ^ 2 + C * m + R
  let alpha : ℝ := m * A + (x + 2) * B
  let beta : ℝ := m * (m * B + (y + 2) * A)

  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hm1 : 1 ≤ m := by
    dsimp [m]
    nlinarith [mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hv)]
  have hUm : U ≤ m := by
    dsimp [m]
    have := mul_le_mul_of_nonneg_left hv (le_of_lt hUpos)
    simpa using this
  have hr1 : 1 < r := by simpa [r] using hxy1
  have hr9 : r < 9 := by simpa [r] using hxy9
  have hspos : 0 < s := by
    dsimp [s]
    linarith
  have hsquare : 4 * r ≤ s ^ 2 := by
    dsimp [r, s]
    nlinarith [sq_nonneg (x - y)]
  have hs2 : 2 < s := by
    nlinarith
  have hC : C = 2 * s ^ 2 - (s + 4) * r + 8 := by
    dsimp [C, s, r]
    ring
  have hR : R = r + 2 * s + 4 := by
    dsimp [R, r, s]
    ring
  have hQ : 0 < Q := by
    have hcore := broadPolynomial_quadratic_pos
      hr1 hr9 (le_of_lt hs2) hsquare hm
    dsimp [Q]
    rw [hC, hR]
    exact hcore
  have hdecomp :
      hullSixThreeThreeBroadPolynomial x y U v =
        Q + alpha * U + beta / U := by
    dsimp [Q, alpha, beta, A, B, C, R, m,
      hullSixThreeThreeBroadPolynomial]
    field_simp [ne_of_gt hUpos]
    ring

  have hsymm :
      hullSixThreeThreeBroadPolynomial x y 1 m =
        hullSixThreeThreeBroadPolynomial y x m 1 := by
    dsimp [hullSixThreeThreeBroadPolynomial]
    ring

  by_cases ha : 0 ≤ alpha
  · by_cases hb : 0 ≤ beta
    · have hbetaU : 0 ≤ beta / U := div_nonneg hb (le_of_lt hUpos)
      rw [hdecomp]
      have halphaU : 0 ≤ alpha * U :=
        mul_nonneg ha (le_of_lt hUpos)
      linarith
    · have hbneg : beta < 0 := lt_of_not_ge hb
      have hinner : m * B + (y + 2) * A < 0 := by
        have hbeta_id : beta = m * (m * B + (y + 2) * A) := rfl
        rw [hbeta_id] at hbneg
        rcases mul_neg_iff.mp hbneg with hcase | hcase
        · exact hcase.2
        · linarith
      have hleftSwap :
          0 < hullSixThreeThreeBroadPolynomial y x m 1 := by
        apply broadPolynomial_endpoint_right_pos hy hx hm hm1
        · nlinarith
        · nlinarith
        · dsimp [A, B] at hinner ⊢
          nlinarith
      have hleft :
          0 < hullSixThreeThreeBroadPolynomial x y 1 m := by
        rw [hsymm]
        exact hleftSwap
      have hleft_decomp :
          hullSixThreeThreeBroadPolynomial x y 1 m =
            Q + alpha + beta := by
        dsimp [Q, alpha, beta, A, B, C, R, m,
          hullSixThreeThreeBroadPolynomial]
        ring
      have hdiff_id :
          hullSixThreeThreeBroadPolynomial x y U v -
              hullSixThreeThreeBroadPolynomial x y 1 m =
            (U - 1) * (alpha - beta / U) := by
        rw [hdecomp, hleft_decomp]
        field_simp [ne_of_gt hUpos]
        ring
      have hfactor : 0 < alpha - beta / U := by
        have hdivneg : beta / U < 0 := div_neg_of_neg_of_pos hbneg hUpos
        linarith
      have hdiff :
          0 ≤ hullSixThreeThreeBroadPolynomial x y U v -
            hullSixThreeThreeBroadPolynomial x y 1 m := by
        rw [hdiff_id]
        exact mul_nonneg (sub_nonneg.mpr hU) (le_of_lt hfactor)
      linarith
  · have haneg : alpha < 0 := lt_of_not_ge ha
    have hright :
        0 < hullSixThreeThreeBroadPolynomial x y m 1 := by
      apply broadPolynomial_endpoint_right_pos hx hy hm hm1 hxy1 hxy9
      simpa [alpha, A, B, m] using haneg
    have hright_decomp :
        hullSixThreeThreeBroadPolynomial x y m 1 =
          Q + alpha * m + beta / m := by
      dsimp [Q, alpha, beta, A, B, C, R, m,
        hullSixThreeThreeBroadPolynomial]
      field_simp [ne_of_gt hUpos, ne_of_gt hvpos]
      ring
    by_cases hb : 0 ≤ beta
    · have hdiff_id :
          hullSixThreeThreeBroadPolynomial x y U v -
              hullSixThreeThreeBroadPolynomial x y m 1 =
            alpha * (U - m) + beta * (m - U) / (U * m) := by
        rw [hdecomp, hright_decomp]
        field_simp [ne_of_gt hUpos, ne_of_gt hm]
        ring
      have hfirst : 0 ≤ alpha * (U - m) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt haneg) (by linarith)
      have hsecond : 0 ≤ beta * (m - U) / (U * m) := by positivity
      have hdiff :
          0 ≤ hullSixThreeThreeBroadPolynomial x y U v -
            hullSixThreeThreeBroadPolynomial x y m 1 := by
        rw [hdiff_id]
        exact add_nonneg hfirst hsecond
      linarith
    · have hbneg : beta < 0 := lt_of_not_ge hb
      have hinner : m * B + (y + 2) * A < 0 := by
        have hbeta_id : beta = m * (m * B + (y + 2) * A) := rfl
        rw [hbeta_id] at hbneg
        rcases mul_neg_iff.mp hbneg with hcase | hcase
        · exact hcase.2
        · linarith
      have hleftSwap :
          0 < hullSixThreeThreeBroadPolynomial y x m 1 := by
        apply broadPolynomial_endpoint_right_pos hy hx hm hm1
        · nlinarith
        · nlinarith
        · dsimp [A, B] at hinner ⊢
          nlinarith
      have hleft :
          0 < hullSixThreeThreeBroadPolynomial x y 1 m := by
        rw [hsymm]
        exact hleftSwap
      have hleft_decomp :
          hullSixThreeThreeBroadPolynomial x y 1 m =
            Q + alpha + beta := by
        dsimp [Q, alpha, beta, A, B, C, R, m,
          hullSixThreeThreeBroadPolynomial]
        ring
      by_cases hendpoints :
          alpha + beta ≤ alpha * m + beta / m
      · by_cases hmEq : m = 1
        · have hUEq : U = 1 := by linarith
          have hsame :
              hullSixThreeThreeBroadPolynomial x y U v =
                hullSixThreeThreeBroadPolynomial x y 1 m := by
            rw [hdecomp, hleft_decomp, hUEq]
            norm_num
          rw [hsame]
          exact hleft
        · have hmgt : 1 < m := lt_of_le_of_ne hm1 (Ne.symm hmEq)
          have hendpoint_factor : 0 ≤ alpha - beta / m := by
            have hid :
                alpha * m + beta / m - (alpha + beta) =
                  (m - 1) * (alpha - beta / m) := by
              field_simp [ne_of_gt hm]
              ring
            have hprod : 0 ≤ (m - 1) * (alpha - beta / m) := by
              rw [← hid]
              linarith
            by_contra hfactorNeg
            have hfactorNeg' : alpha - beta / m < 0 := lt_of_not_ge hfactorNeg
            have := mul_neg_of_pos_of_neg (by linarith : 0 < m - 1) hfactorNeg'
            linarith
          have hbeta_compare : beta / U ≤ beta / m := by
            have hid :
                beta / m - beta / U = beta * (U - m) / (U * m) := by
              field_simp [ne_of_gt hUpos, ne_of_gt hm] <;> ring
            have hnum : 0 ≤ beta * (U - m) :=
              mul_nonneg_of_nonpos_of_nonpos (le_of_lt hbneg) (by linarith)
            have hden : 0 < U * m := mul_pos hUpos hm
            rw [← sub_nonneg]
            rw [hid]
            exact div_nonneg hnum (le_of_lt hden)
          have hfactor : 0 ≤ alpha - beta / U := by linarith
          have hdiff_id :
              hullSixThreeThreeBroadPolynomial x y U v -
                  hullSixThreeThreeBroadPolynomial x y 1 m =
                (U - 1) * (alpha - beta / U) := by
            rw [hdecomp, hleft_decomp]
            field_simp [ne_of_gt hUpos]
            ring
          have hdiff :
              0 ≤ hullSixThreeThreeBroadPolynomial x y U v -
                hullSixThreeThreeBroadPolynomial x y 1 m := by
            rw [hdiff_id]
            exact mul_nonneg (sub_nonneg.mpr hU) hfactor
          linarith
      · have hendpoints' : alpha * m + beta / m < alpha + beta :=
          lt_of_not_ge hendpoints
        by_cases hmEq : m = 1
        · rw [hmEq] at hendpoints'
          norm_num at hendpoints'
        · have hmgt : 1 < m := lt_of_le_of_ne hm1 (Ne.symm hmEq)
          have hendpoint_factor : alpha - beta / m ≤ 0 := by
            have hid :
                alpha * m + beta / m - (alpha + beta) =
                  (m - 1) * (alpha - beta / m) := by
              field_simp [ne_of_gt hm]
              ring
            have hprod : (m - 1) * (alpha - beta / m) < 0 := by
              rw [← hid]
              linarith
            rcases mul_neg_iff.mp hprod with hcase | hcase
            · exact le_of_lt hcase.2
            · linarith
          have hbeta_compare : beta / m ≤ beta / (U * m) := by
            have hid :
                beta / (U * m) - beta / m =
                  beta * (1 - U) / (U * m) := by
              field_simp [ne_of_gt hUpos, ne_of_gt hm] <;> ring
            have hnum : 0 ≤ beta * (1 - U) :=
              mul_nonneg_of_nonpos_of_nonpos (le_of_lt hbneg) (by linarith)
            have hden : 0 < U * m := mul_pos hUpos hm
            rw [← sub_nonneg]
            rw [hid]
            exact div_nonneg hnum (le_of_lt hden)
          have hfactor : 0 ≤ -alpha + beta / (U * m) := by
            linarith
          have hdiff_id :
              hullSixThreeThreeBroadPolynomial x y U v -
                  hullSixThreeThreeBroadPolynomial x y m 1 =
                (m - U) * (-alpha + beta / (U * m)) := by
            rw [hdecomp, hright_decomp]
            field_simp [ne_of_gt hUpos, ne_of_gt hm]
            ring
          have hdiff :
              0 ≤ hullSixThreeThreeBroadPolynomial x y U v -
                hullSixThreeThreeBroadPolynomial x y m 1 := by
            rw [hdiff_id]
            exact mul_nonneg (sub_nonneg.mpr hUm) hfactor
          linarith

end Heilbronn8
