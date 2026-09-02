import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Compact AM--GM closure for coincident `2 + 4` transitions

This file isolates the normalized scalar argument used by the q-blind
coincident-transition chambers `q = 11, 22, 33`.  After one lower-ear
elimination, the remaining expression is an eight-term Laurent sum.  The
multiplicities `1, 3, 4, 3, 1, 2, 1, 3` make an exact eighteen-copy
weighted AM--GM certificate.

The final theorem records the raw one-sided packet needed by the geometric
adapter.  Its hypothesis `d <= e` is supplied after applying the
rotation-complement symmetry when necessary.  The primed fan floor
`1 <= E0 + d - c` is retained explicitly: it is what forces `c < d` from
the lower-ear inequality.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The Laurent remainder in the coincident-transition scalar reduction. -/
noncomputable def hullSixTwoFourCoincidentLaurent
    (r s u : ℝ) : ℝ :=
  u + r + s + 2 / s + u / s + 1 / r + u / r + 1 / (2 * u)

/-- The eight distinct terms of the eighteen-copy certificate. -/
noncomputable def hullSixTwoFourCoincidentAMGMTerm
    (r s u : ℝ) : Fin 8 → ℝ :=
  ![u, r, s, 2 / s, u / s, 1 / r, u / r, 1 / (2 * u)]

/-- Multiplicities of total mass eighteen. -/
def hullSixTwoFourCoincidentAMGMWeight : Fin 8 → ℕ :=
  ![1, 3, 4, 3, 1, 2, 1, 3]

/-- The variable-free product after the three ratio exponents cancel. -/
noncomputable def hullSixTwoFourCoincidentAMGMConstant : ℝ :=
  1 / 20155392

theorem hullSixTwoFourCoincident_amgmWeight_pos
    (i : Fin 8) : 0 < hullSixTwoFourCoincidentAMGMWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourCoincidentAMGMWeight]

theorem hullSixTwoFourCoincident_amgmWeight_sum :
    ∑ i, hullSixTwoFourCoincidentAMGMWeight i = 18 := by
  norm_num [hullSixTwoFourCoincidentAMGMWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourCoincident_amgmTerm_nonneg
    {r s u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (i : Fin 8) :
    0 ≤ hullSixTwoFourCoincidentAMGMTerm r s u i := by
  fin_cases i <;>
    simp [hullSixTwoFourCoincidentAMGMTerm] <;>
    positivity

theorem hullSixTwoFourCoincident_amgmTerm_sum
    (r s u : ℝ) :
    ∑ i, hullSixTwoFourCoincidentAMGMTerm r s u i =
      hullSixTwoFourCoincidentLaurent r s u := by
  simp [hullSixTwoFourCoincidentAMGMTerm,
    hullSixTwoFourCoincidentLaurent, Fin.sum_univ_succ] <;>
    ring

/-- The eighteen scaled terms have exact product `1 / 20155392`. -/
theorem hullSixTwoFourCoincident_amgmTerm_product
    {r s u : ℝ} (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) :
    (∏ i,
        (hullSixTwoFourCoincidentAMGMTerm r s u i /
          (hullSixTwoFourCoincidentAMGMWeight i : ℝ)) ^
            hullSixTwoFourCoincidentAMGMWeight i) =
      hullSixTwoFourCoincidentAMGMConstant := by
  simp [hullSixTwoFourCoincidentAMGMTerm,
    hullSixTwoFourCoincidentAMGMWeight, Fin.prod_univ_succ,
    hullSixTwoFourCoincidentAMGMConstant]
  field_simp [hr.ne', hs.ne', hu.ne'] <;> ring

theorem hullSixTwoFourCoincident_amgmConstant_pos :
    0 < hullSixTwoFourCoincidentAMGMConstant := by
  norm_num [hullSixTwoFourCoincidentAMGMConstant]

/-- Exact integer endpoint for the eighteen-copy certificate. -/
theorem hullSixTwoFourCoincident_amgm_integer_gap :
    (7 : ℕ) ^ 18 * 20155392 < 18 ^ 18 := by
  norm_num

/-- The certified AM--GM root is strictly larger than seven. -/
theorem hullSixTwoFourCoincident_amgm_root_gap :
    (7 : ℝ) <
      18 * hullSixTwoFourCoincidentAMGMConstant ^ ((18 : ℝ)⁻¹) := by
  have hpow :
      ((7 : ℝ) / 18) ^ 18 <
        hullSixTwoFourCoincidentAMGMConstant := by
    norm_num [hullSixTwoFourCoincidentAMGMConstant]
  have hpowRpow :
      ((7 : ℝ) / 18) ^ (18 : ℝ) <
        hullSixTwoFourCoincidentAMGMConstant := by
    change ((7 : ℝ) / 18) ^ ((18 : ℕ) : ℝ) <
      hullSixTwoFourCoincidentAMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (7 : ℝ) / 18 <
        hullSixTwoFourCoincidentAMGMConstant ^ ((18 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourCoincident_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- The exact eight-term Laurent inequality used by the raw scalar wrapper. -/
theorem hullSixTwoFourCoincident_laurent_gt
    {r s u : ℝ} (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) :
    (7 : ℝ) < hullSixTwoFourCoincidentLaurent r s u := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourCoincidentAMGMWeight
    (hullSixTwoFourCoincidentAMGMTerm r s u)
    hullSixTwoFourCoincident_amgmWeight_pos
    (hullSixTwoFourCoincident_amgmTerm_nonneg
      (le_of_lt hr) (le_of_lt hs) (le_of_lt hu))
  rw [hullSixTwoFourCoincident_amgmWeight_sum,
    hullSixTwoFourCoincident_amgmTerm_product hr hs hu] at hamgm
  rw [← hullSixTwoFourCoincident_amgmTerm_sum r s u]
  exact hullSixTwoFourCoincident_amgm_root_gap.trans_le hamgm

/--
The reduced normalized max-expression theorem.  Here `d - c` is the positive
lower-height jump forced by the raw ear packet.
-/
theorem hullSixTwoFourCoincident_reduced
    {a b c d : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hcd : c < d) :
    (25 : ℝ) / 2 <
      3 + a + d + (a + b) / c + (c + d) / b +
        max (2 * d / a) (d / (d - c)) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have ht : 0 < d - c := sub_pos.mpr hcd
  have hr : 0 < a / c := div_pos ha hc
  have hs : 0 < b / c := div_pos hb hc
  have hu : 0 < (d - c) / c := div_pos ht hc
  have hLaurent := hullSixTwoFourCoincident_laurent_gt hr hs hu

  have hLaurentExpand :
      hullSixTwoFourCoincidentLaurent
          (a / c) (b / c) ((d - c) / c) =
        (d - c) / c + a / c + b / c + 2 * c / b +
          (d - c) / b + c / a + (d - c) / a +
            c / (2 * (d - c)) := by
    unfold hullSixTwoFourCoincidentLaurent
    field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

  have hmaxAverage :
      (2 * d / a + d / (d - c)) / 2 ≤
        max (2 * d / a) (d / (d - c)) := by
    have hleft := le_max_left (2 * d / a) (d / (d - c))
    have hright := le_max_right (2 * d / a) (d / (d - c))
    linarith

  have htRatio : (d - c) / c ≤ d - c := by
    rw [div_le_iff₀ hc]
    have hmul := mul_le_mul_of_nonneg_left hc1 (le_of_lt ht)
    nlinarith
  have hac : (2 : ℝ) ≤ a + c := by
    linarith

  have hCore :
      (11 : ℝ) / 2 +
          hullSixTwoFourCoincidentLaurent
            (a / c) (b / c) ((d - c) / c) ≤
        3 + a + c + (d - c) + a / c + b / c +
          2 * c / b + (d - c) / b + c / a +
            (d - c) / a + c / (2 * (d - c)) + 1 / 2 := by
    rw [hLaurentExpand]
    linarith

  have hRaw :
      3 + a + c + (d - c) + a / c + b / c +
          2 * c / b + (d - c) / b + c / a +
            (d - c) / a + c / (2 * (d - c)) + 1 / 2 ≤
        3 + a + d + (a + b) / c + (c + d) / b +
          max (2 * d / a) (d / (d - c)) := by
    have hIdentity :
        3 + a + c + (d - c) + a / c + b / c +
            2 * c / b + (d - c) / b + c / a +
              (d - c) / a + c / (2 * (d - c)) + 1 / 2 =
          3 + a + d + (a + b) / c + (c + d) / b +
            (2 * d / a + d / (d - c)) / 2 := by
      field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring
    rw [hIdentity]
    simpa [add_comm] using add_le_add_left hmaxAverage
      (3 + a + d + (a + b) / c + (c + d) / b)

  have hThreshold :
      (25 : ℝ) / 2 <
        (11 : ℝ) / 2 +
          hullSixTwoFourCoincidentLaurent
            (a / c) (b / c) ((d - c) / c) := by
    linarith
  exact hThreshold.trans_le (hCore.trans hRaw)

/--
Raw normalized coincident-transition closure in mixed-fan variables.

`E1p` is the coincident primed transition edge and `E0 + d - c` is
the preceding primed fan edge.  The three unit floors account for the other
mixed fan edges in the displayed conclusion.
-/
theorem hullSixTwoFourCoincident_scalar
    {a b c d e A C E0 E1p E2p Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (hde : d ≤ e)
    (hE1p1 : 1 ≤ E1p) (hE0p1 : 1 ≤ E0 + d - c)
    (hC1 : 1 ≤ C) (hE2p1 : 1 ≤ E2p) (hFp1 : 1 ≤ Fp)
    (hAtransition : a + b ≤ c * A)
    (hE0transition : c + d ≤ b * E0)
    (hE1transition : d + e ≤ a * E1p)
    (hEar0 :
      d ≤ (E1p + d - e) * (d - c) - E0 * (e - d)) :
    (25 : ℝ) / 2 < A + C + E0 + E1p + E2p + Fp + a + d := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hq : 0 ≤ e - d := sub_nonneg.mpr hde
  have hE1p0 : 0 ≤ E1p := le_trans (by norm_num) hE1p1
  have hE0p0 : 0 ≤ E0 + d - c := le_trans (by norm_num) hE0p1
  have hEarRewrite :
      (E1p + d - e) * (d - c) - E0 * (e - d) =
        (d - c) * E1p - (e - d) * (E0 + d - c) := by
    ring
  rw [hEarRewrite] at hEar0

  have hcd : c < d := by
    by_contra hnot
    have hgap : d - c ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have hfirst : (d - c) * E1p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hgap hE1p0
    have hsecond : 0 ≤ (e - d) * (E0 + d - c) :=
      mul_nonneg hq hE0p0
    nlinarith
  have ht : 0 < d - c := sub_pos.mpr hcd
  have hsecond : 0 ≤ (e - d) * (E0 + d - c) :=
    mul_nonneg hq hE0p0
  have hEarUpper : d ≤ (d - c) * E1p := by
    nlinarith
  have hReciprocal : d / (d - c) ≤ E1p := by
    rw [div_le_iff₀ ht]
    simpa [mul_comm] using hEarUpper
  have hTransition : 2 * d / a ≤ E1p := by
    rw [div_le_iff₀ ha]
    nlinarith
  have hMax : max (2 * d / a) (d / (d - c)) ≤ E1p :=
    max_le hTransition hReciprocal
  have hALower : (a + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2
      (by simpa [mul_comm] using hAtransition)
  have hE0Lower : (c + d) / b ≤ E0 := by
    exact (div_le_iff₀ hb).2
      (by simpa [mul_comm] using hE0transition)
  have hReduced := hullSixTwoFourCoincident_reduced ha1 hb1 hc1 hcd
  have hLower :
      3 + a + d + (a + b) / c + (c + d) / b +
          max (2 * d / a) (d / (d - c)) ≤
        A + C + E0 + E1p + E2p + Fp + a + d := by
    linarith
  exact hReduced.trans_le hLower

end Heilbronn8
