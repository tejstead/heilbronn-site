import Mathlib

/-!
# Scalar core for the `p = (1,1)`, negative-`Y13` frontier packet

This order-resolved core is the common endpoint of the four choices
`u = max a b` and `v = min d e`.  Geometry supplies the appropriate mixed
fan expansion and the appropriate `P`- or `Q`-ear.  No sign of `Y02` is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- Order-resolved scalar closure for the negative-`Y13` half of the
`p = (1,1)` partial frontier. -/
theorem hullSixTwoFourP11Y13Neg_orderedCore
    {a b u v C E0 Ec Fp H : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 1 < v)
    (hau : a ≤ u) (hbu : b ≤ u)
    (hC : b + 1 ≤ a * C)
    (hE0 : v * C + 1 ≤ b * E0)
    (hFp : a + 1 ≤ b * Fp)
    (hEc : v / (v - 1) ≤ Ec)
    (hH : u + v + 2 + C + E0 + Ec + Fp ≤ H) :
    (25 : ℝ) / 2 < H := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hv0 : 0 ≤ v := le_trans (by norm_num) (le_of_lt hv)
  have hvSub : 0 < v - 1 := sub_pos.mpr hv

  have hCLower : (b + 1) / a ≤ C := by
    exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hC)
  have hE0Lower : (v * C + 1) / b ≤ E0 := by
    exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hE0)
  have hFpLower : (a + 1) / b ≤ Fp := by
    exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hFp)
  have hvCLower :
      v * ((b + 1) / a) + 1 ≤ v * C + 1 := by
    have hmul := mul_le_mul_of_nonneg_left hCLower hv0
    linarith
  have hE0Fine :
      (v * ((b + 1) / a) + 1) / b ≤ E0 := by
    exact le_trans ((div_le_div_iff_of_pos_right hb).2 hvCLower) hE0Lower

  have hRaw :
      u + v + 2 + (b + 1) / a +
          (v * ((b + 1) / a) + 1) / b +
            v / (v - 1) + (a + 1) / b ≤ H := by
    linarith [hH, hCLower, hE0Fine, hEc, hFpLower]
  have hRawExpanded :
      u + v + 2 + v / (v - 1) + a / b + b / a +
          (v + 1) / a + 2 / b + v / (a * b) ≤ H := by
    have hid :
        u + v + 2 + (b + 1) / a +
              (v * ((b + 1) / a) + 1) / b +
                v / (v - 1) + (a + 1) / b =
          u + v + 2 + v / (v - 1) + a / b + b / a +
              (v + 1) / a + 2 / b + v / (a * b) := by
      field_simp [ha.ne', hb.ne'] <;> ring
    rw [← hid]
    exact hRaw

  have hRatio : 2 ≤ a / b + b / a := by
    rw [← sub_nonneg]
    have hid :
        a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by
      field_simp [ha.ne', hb.ne'] <;> ring
    rw [hid]
    exact div_nonneg (sq_nonneg _) (mul_pos ha hb).le
  have hInvA : 1 / u ≤ 1 / a :=
    one_div_le_one_div_of_le ha hau
  have hInvB : 1 / u ≤ 1 / b :=
    one_div_le_one_div_of_le hb hbu
  have hRecip :
      (v + 3) / u ≤ (v + 1) / a + 2 / b := by
    have hv1 : 0 ≤ v + 1 := by linarith
    have hleft := mul_le_mul_of_nonneg_left hInvA hv1
    have hright := mul_le_mul_of_nonneg_left hInvB (by norm_num : (0 : ℝ) ≤ 2)
    have hshapeLeft : (v + 1) * (1 / u) = (v + 1) / u := by ring
    have hshapeRight : (v + 1) * (1 / a) = (v + 1) / a := by ring
    have hshapeTwoU : 2 * (1 / u) = 2 / u := by ring
    have hshapeTwoB : 2 * (1 / b) = 2 / b := by ring
    rw [hshapeLeft, hshapeRight] at hleft
    rw [hshapeTwoU, hshapeTwoB] at hright
    have hsplit : (v + 3) / u = (v + 1) / u + 2 / u := by
      field_simp [hu.ne'] <;> ring
    rw [hsplit]
    linarith
  have habUpper : a * b ≤ u * u := by
    exact mul_le_mul hau hbu (le_of_lt hb) (le_of_lt hu)
  have hInvProd : 1 / (u * u) ≤ 1 / (a * b) :=
    one_div_le_one_div_of_le (mul_pos ha hb) habUpper
  have hProd : v / u ^ 2 ≤ v / (a * b) := by
    have hmul := mul_le_mul_of_nonneg_left hInvProd hv0
    have huShape : v * (1 / (u * u)) = v / u ^ 2 := by ring
    have habShape : v * (1 / (a * b)) = v / (a * b) := by ring
    rwa [huShape, habShape] at hmul
  have hReplace :
      2 + (v + 3) / u + v / u ^ 2 ≤
        a / b + b / a + (v + 1) / a + 2 / b + v / (a * b) := by
    linarith [hRatio, hRecip, hProd]
  have hG :
      u + v + 4 + v / (v - 1) + (v + 3) / u + v / u ^ 2 ≤ H := by
    linarith [hRawExpanded, hReplace]

  let w : ℝ := v - 1
  have hw : 0 < w := by simpa [w] using hvSub
  have hPair :
      2 + 1 / u < w * (1 + 1 / u + 1 / u ^ 2) + 1 / w := by
    rw [← sub_pos]
    have hid :
        w * (1 + 1 / u + 1 / u ^ 2) + 1 / w -
              (2 + 1 / u) =
          (w * (1 + 1 / (2 * u)) - 1) ^ 2 / w +
            3 * w / (4 * u ^ 2) := by
      field_simp [hu.ne', hw.ne'] <;> ring
    rw [hid]
    have hfirst :
        0 ≤ (w * (1 + 1 / (2 * u)) - 1) ^ 2 / w :=
      div_nonneg (sq_nonneg _) hw.le
    have hsecond : 0 < 3 * w / (4 * u ^ 2) := by positivity
    linarith
  have hGShape :
      u + v + 4 + v / (v - 1) + (v + 3) / u + v / u ^ 2 =
        u + 6 + 4 / u + 1 / u ^ 2 +
          (w * (1 + 1 / u + 1 / u ^ 2) + 1 / w) := by
    dsimp [w]
    field_simp [hu.ne', hvSub.ne'] <;> ring
  have hMiddle :
      u + 8 + 5 / u + 1 / u ^ 2 <
        u + v + 4 + v / (v - 1) + (v + 3) / u + v / u ^ 2 := by
    rw [hGShape]
    rw [← show 4 / u + 1 / u = 5 / u by ring]
    linarith [hPair]

  have hPoly : 0 < 2 * u ^ 3 - 9 * u ^ 2 + 10 * u + 2 := by
    have hcoef : 0 < 2 * u + (1 : ℝ) / 3 := by positivity
    have hfirst :
        0 ≤ (2 * u + (1 : ℝ) / 3) * (u - (7 : ℝ) / 3) ^ 2 :=
      mul_nonneg hcoef.le (sq_nonneg _)
    have hsecond : 0 < (2 : ℝ) / 3 * u + 5 / 27 := by positivity
    have hid :
        2 * u ^ 3 - 9 * u ^ 2 + 10 * u + 2 =
          (2 * u + (1 : ℝ) / 3) * (u - (7 : ℝ) / 3) ^ 2 +
            (2 : ℝ) / 3 * u + 5 / 27 := by ring
    rw [hid]
    linarith
  have hEndpoint :
      (25 : ℝ) / 2 < u + 8 + 5 / u + 1 / u ^ 2 := by
    rw [← sub_pos]
    have hid :
        u + 8 + 5 / u + 1 / u ^ 2 - (25 : ℝ) / 2 =
          (2 * u ^ 3 - 9 * u ^ 2 + 10 * u + 2) / (2 * u ^ 2) := by
      field_simp [hu.ne'] <;> ring
    rw [hid]
    exact div_pos hPoly (by positivity)
  exact lt_of_lt_of_le (lt_trans hEndpoint hMiddle) hG

end Heilbronn8
