import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Q223Q233ScalarAMGM

/-!
# Raw scalar reduction for the `p = 111`, `q = 233` chamber

This file is the small algebraic seam between the determinant/fan packet and
the frozen two-height AM--GM certificate.  Geometry supplies the displayed
fan lower bounds.  The proof first averages the two upper-chain estimates,
then eliminates the intermediate height `b` and finishes with one reciprocal
AM--GM in the positive variable `D = f * (A + a) - a`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- The raw q233 fan packet implies the sharp two-height reduction, hence the
`25 / 2` hull bound.  Here `A` is the first upper fan, `F` is the wrap fan,
`E` is the `U0 U2` diagonal, and `U,L` are the upper and lower fan sums. -/
theorem hullSixThreeThreeP111Q233_raw_scalar
    {H a b c f A F E U L : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A)
    (hAsign : b - a + (a + b) / f ≤ A)
    (hE : (c * A + a) / b ≤ E)
    (hUdiag : 1 + c / a + (1 + 1 / a) * E ≤ U)
    (hUfan : A + 2 ≤ U)
    (hL : 1 + (F + f) / a ≤ L)
    (hF : a + f + 1 ≤ F)
    (hH : H = U + L + F) :
    (25 : ℝ) / 2 < H := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1

  have hcA : A ≤ c * A := by
    have hprod := mul_nonneg (sub_nonneg.mpr hc1) hA0
    nlinarith
  have hEweak : (A + a) / b ≤ E := by
    apply le_trans ?_ hE
    exact (div_le_div_iff_of_pos_right hb).2 (by linarith)
  have hca : 1 / a ≤ c / a :=
    (div_le_div_iff_of_pos_right ha).2 hc1
  have hfactor : 0 ≤ 1 + 1 / a := by positivity
  have hEmul := mul_le_mul_of_nonneg_left hEweak hfactor
  have hUdiagWeak :
      1 + 1 / a + (A + a) * (a + 1) / (a * b) ≤ U := by
    have hid :
        (1 + 1 / a) * ((A + a) / b) =
          (A + a) * (a + 1) / (a * b) := by
      field_simp [ha.ne', hb.ne']
      <;> ring
    rw [← hid]
    nlinarith [hUdiag, hca, hEmul]
  have hUavg :
      (3 : ℝ) / 2 + A / 2 + 1 / (2 * a) +
          (A + a) * (a + 1) / (2 * a * b) ≤ U := by
    have hshape :
        (3 : ℝ) / 2 + A / 2 + 1 / (2 * a) +
            (A + a) * (a + 1) / (2 * a * b) =
          ((1 + 1 / a + (A + a) * (a + 1) / (a * b)) +
            (A + 2)) / 2 := by
      field_simp [ha.ne', hb.ne'] <;> ring
    rw [hshape]
    linarith

  have hFdiv : (a + 2 * f + 1) / a ≤ (F + f) / a := by
    apply (div_le_div_iff_of_pos_right ha).2
    linarith
  have hLweak : 2 + (2 * f + 1) / a ≤ L := by
    have hid :
        2 + (2 * f + 1) / a = 1 + (a + 2 * f + 1) / a := by
      field_simp [ha.ne']
      <;> ring
    rw [hid]
    nlinarith [hL, hFdiv]

  have hFanReduction :
      (9 : ℝ) / 2 +
          (a + f + (2 * f + (3 : ℝ) / 2) / a + A / 2 +
            (A + a) * (a + 1) / (2 * a * b)) ≤ H := by
    rw [hH]
    calc
      _ = ((3 : ℝ) / 2 + A / 2 + 1 / (2 * a) +
            (A + a) * (a + 1) / (2 * a * b)) +
          (2 + (2 * f + 1) / a) + (a + f + 1) := by
        field_simp [ha.ne', hb.ne'] <;> ring
      _ ≤ U + L + F := add_le_add (add_le_add hUavg hLweak) hF

  let D : ℝ := f * (A + a) - a
  have hDb : b * (f + 1) ≤ D := by
    have hmul := mul_le_mul_of_nonneg_left hAsign (le_of_lt hf)
    have hid :
        f * (b - a + (a + b) / f) =
          b * (f + 1) - f * a + a := by
      field_simp [hf.ne']
      <;> ring
    rw [hid] at hmul
    dsimp [D]
    nlinarith
  have hbfp : 0 < b * (f + 1) := by positivity
  have hD : 0 < D := lt_of_lt_of_le hbfp hDb
  have hDplus : D + a = f * (A + a) := by
    dsimp [D]
    ring
  have hrecip : (f + 1) / D ≤ 1 / b := by
    apply (div_le_div_iff₀ hD hb).2
    nlinarith

  let C : ℝ := (A + a) * (a + 1) / (2 * a)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hrecip hC0
  have hBElim :
      (D + a) * (a + 1) * (f + 1) / (2 * a * f * D) ≤
        (A + a) * (a + 1) / (2 * a * b) := by
    calc
      (D + a) * (a + 1) * (f + 1) / (2 * a * f * D) =
          C * ((f + 1) / D) := by
            dsimp [C]
            rw [hDplus]
            field_simp [ha.ne', hf.ne', hD.ne']
            <;> ring
      _ ≤ C * (1 / b) := hscaled
      _ = (A + a) * (a + 1) / (2 * a * b) := by
            dsimp [C]
            field_simp [ha.ne', hb.ne']
            <;> ring
  have hBElimSplit :
      (D + a) * (a + 1) * (f + 1) / (2 * a * f * D) =
        (a + 1) * (f + 1) / (2 * a * f) +
          (a + 1) * (f + 1) / (2 * f * D) := by
    field_simp [ha.ne', hf.ne', hD.ne']
    <;> ring
  have hASplit :
      a + A / 2 = a * (f + 1) / (2 * f) + D / (2 * f) := by
    dsimp [D]
    field_simp [hf.ne']
    <;> ring

  let K : ℝ := (a + 1) * (f + 1)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hsquare : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK0
  have hdiff :
      D / (2 * f) + K / (2 * f * D) - Real.sqrt K / f =
        (D - Real.sqrt K) ^ 2 / (2 * f * D) := by
    field_simp [hf.ne', hD.ne']
    nlinarith [hsquare]
  have hdiff0 : 0 ≤ (D - Real.sqrt K) ^ 2 / (2 * f * D) := by
    positivity
  have hreciprocal :
      Real.sqrt K / f ≤ D / (2 * f) + K / (2 * f * D) := by
    nlinarith [hdiff, hdiff0]

  have hEndpoint :
      a * (f + 1) / (2 * f) +
          (a + 1) * (f + 1) / (2 * a * f) +
          Real.sqrt ((a + 1) * (f + 1)) / f ≤
        a + A / 2 + (A + a) * (a + 1) / (2 * a * b) := by
    change
      a * (f + 1) / (2 * f) +
          (a + 1) * (f + 1) / (2 * a * f) + Real.sqrt K / f ≤
        a + A / 2 + (A + a) * (a + 1) / (2 * a * b)
    nlinarith [hBElim, hBElimSplit, hASplit, hreciprocal]

  have hReduced :
      (9 : ℝ) / 2 + hullSixThreeThreeP111Q233Reduced a f ≤ H := by
    unfold hullSixThreeThreeP111Q233Reduced
    nlinarith [hFanReduction, hEndpoint]
  exact hullSixThreeThreeP111Q233_reduced_finish ha1 hf1 hReduced

end Heilbronn8
