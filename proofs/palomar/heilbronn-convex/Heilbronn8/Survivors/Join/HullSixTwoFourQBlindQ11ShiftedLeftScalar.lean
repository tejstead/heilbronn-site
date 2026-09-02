import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCoincidentAMGM

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

theorem hullSixTwoFourQBlindQ11ShiftedLeft_scalar
    {a b c d e f A C x y z Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hC1 : 1 ≤ C) (hFp1 : 1 ≤ Fp)
    (hAtransition : a + b ≤ c * A)
    (hxTransition : d * (b + c + 1) + c ≤ b * x)
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hy : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hA : (a + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAtransition)
  have hASplit : a / c + b / c ≤ A := by
    simpa [add_div] using hA
  have hxLower :
      d + (d * (c + 1) + c) / b ≤ x := by
    have hdiv : (d * (b + c + 1) + c) / b ≤ x := by
      exact (div_le_iff₀ hb).2
        (by simpa [mul_comm] using hxTransition)
    calc
      d + (d * (c + 1) + c) / b =
          (d * (b + c + 1) + c) / b := by
            field_simp [hb.ne'] <;> ring
      _ ≤ x := hdiv

  have hPair (hdgt : 1 < d) :
      (5 : ℝ) / 2 < b / c + (d * (c + 1) + c) / b := by
    let U : ℝ := b / c
    let V : ℝ := (d * (c + 1) + c) / b
    have hU : 0 < U := by
      dsimp [U]
      positivity
    have hK : 0 < d * (c + 1) + c := by positivity
    have hV : 0 < V := by
      dsimp [V]
      positivity
    have hdc : 0 < c * (d - 1) :=
      mul_pos hc (sub_pos.mpr hdgt)
    have hquot : 2 < (d * (c + 1) + c) / c := by
      apply (lt_div_iff₀ hc).2
      nlinarith
    have hprod : 2 < U * V := by
      calc
        2 < (d * (c + 1) + c) / c := hquot
        _ = U * V := by
          dsimp [U, V]
          field_simp [hb.ne', hc.ne'] <;> ring
    by_contra hnot
    have hle : U + V ≤ (5 : ℝ) / 2 := le_of_not_gt hnot
    have hleft : 0 ≤ (5 : ℝ) / 2 - (U + V) := sub_nonneg.mpr hle
    have hright : 0 ≤ (5 : ℝ) / 2 + (U + V) := by positivity
    have hfactor :
        0 ≤ ((5 : ℝ) / 2 - (U + V)) *
          ((5 : ℝ) / 2 + (U + V)) :=
      mul_nonneg hleft hright
    nlinarith [sq_nonneg (U - V)]

  have haReciprocal : 1 + 1 / c ≤ a + a / c := by
    have hfac : 0 ≤ (a - 1) * (1 + 1 / c) :=
      mul_nonneg (sub_nonneg.mpr ha1) (by positivity)
    have hid :
        a + a / c - (1 + 1 / c) = (a - 1) * (1 + 1 / c) := by
      ring
    nlinarith [hfac, hid]

  by_cases hde : d ≤ e
  · have hq : 0 ≤ e - d := sub_nonneg.mpr hde
    have hdrop : d ≤ (d - c) * y := by
      have hnonneg : 0 ≤ (e - d) * x :=
        mul_nonneg hq (le_of_lt hx)
      nlinarith
    have hcd : c < d := by
      by_contra hnot
      have hgap : d - c ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hmul : (d - c) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hgap (le_of_lt hy)
      nlinarith
    have ht : 0 < d - c := sub_pos.mpr hcd
    have hdgt : 1 < d := lt_of_le_of_lt hc1 hcd
    have hyLower : d / (d - c) ≤ y := by
      exact (div_le_iff₀ ht).2 (by simpa [mul_comm] using hdrop)
    have htPair : 2 ≤ (d - c) + c / (d - c) := by
      have hfrac : 2 - (d - c) ≤ c / (d - c) := by
        apply (le_div_iff₀ ht).2
        nlinarith [sq_nonneg ((d - c) - 1)]
      linarith
    have hHeightGroup :
        2 * c + 3 ≤ c + d + d / (d - c) := by
      have hid :
          c + d + d / (d - c) =
            2 * c + 1 + (d - c) + c / (d - c) := by
        field_simp [ht.ne'] <;> ring
      rw [hid]
      linarith
    have hcFactor : 0 ≤ (2 * c - 1) * (c - 1) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hc1)
    have hcReciprocal : 3 ≤ 2 * c + 1 / c := by
      have hfrac : 3 - 2 * c ≤ 1 / c := by
        apply (le_div_iff₀ hc).2
        nlinarith
      linarith
    have hLower :
        3 + (a + a / c) +
              (b / c + (d * (c + 1) + c) / b) +
              (c + d + d / (d - c)) ≤
          A + C + x + y + z + Fp + a + c := by
      linarith [hASplit, hxLower, hyLower, hC1, hz1, hFp1]
    have hThreshold :
        (25 : ℝ) / 2 <
          3 + (a + a / c) +
            (b / c + (d * (c + 1) + c) / b) +
            (c + d + d / (d - c)) := by
      nlinarith [hPair hdgt]
    exact hThreshold.trans_le hLower
  · have hed : e < d := lt_of_not_ge hde
    have hdz : d - e ≤ (d - e) * z := by
      simpa using mul_le_mul_of_nonneg_left hz1
        (sub_nonneg.mpr (le_of_lt hed))
    have hey : d ≤ (e - f) * y := by
      nlinarith
    have hef : f < e := by
      by_contra hnot
      have hgap : e - f ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hmul : (e - f) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hgap (le_of_lt hy)
      nlinarith
    have hdgt : 1 < d := lt_of_le_of_lt hf1 (hef.trans hed)
    have hcoef : e - f < d - 1 := by linarith
    have hmulStrict : (e - f) * y < (d - 1) * y :=
      mul_lt_mul_of_pos_right hcoef hy
    have hdyStrict : d < (d - 1) * y := hey.trans_lt hmulStrict
    have hdt : 0 < d - 1 := sub_pos.mpr hdgt
    have hyLower : d / (d - 1) ≤ y := by
      exact le_of_lt ((div_lt_iff₀ hdt).2
        (by simpa [mul_comm] using hdyStrict))
    have hcPair : 2 ≤ c + 1 / c := by
      have hfrac : 2 - c ≤ 1 / c := by
        apply (le_div_iff₀ hc).2
        nlinarith [sq_nonneg (c - 1)]
      linarith
    have haHeightGroup : 3 ≤ a + a / c + c := by
      nlinarith
    have hdtPair : 2 ≤ (d - 1) + 1 / (d - 1) := by
      have hfrac : 2 - (d - 1) ≤ 1 / (d - 1) := by
        apply (le_div_iff₀ hdt).2
        nlinarith [sq_nonneg ((d - 1) - 1)]
      linarith
    have hdHeightGroup : 4 ≤ d + d / (d - 1) := by
      have hid :
          d + d / (d - 1) =
            2 + (d - 1) + 1 / (d - 1) := by
        field_simp [hdt.ne'] <;> ring
      rw [hid]
      linarith
    have hLower :
        3 + (a + a / c + c) +
              (b / c + (d * (c + 1) + c) / b) +
              (d + d / (d - 1)) ≤
          A + C + x + y + z + Fp + a + c := by
      linarith [hASplit, hxLower, hyLower, hC1, hz1, hFp1]
    have hThreshold :
        (25 : ℝ) / 2 <
          3 + (a + a / c + c) +
            (b / c + (d * (c + 1) + c) / b) +
            (d + d / (d - 1)) := by
      nlinarith [hPair hdgt]
    exact hThreshold.trans_le hLower

end Heilbronn8
