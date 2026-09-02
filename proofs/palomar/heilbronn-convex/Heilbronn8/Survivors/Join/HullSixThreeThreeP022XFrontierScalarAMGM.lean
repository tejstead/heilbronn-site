import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar certificate for the maximal-q `p = 022` X-frontier

The exact geometry leaves the sign of the single `Q`-cell `Y01`
unspecified.  Its absolute area floor gives two branches.

* If `Y01 >= 1`, base change couples the wrap fan and the lower `P` fan.
  A 12-copy Laurent AM--GM certificate closes the branch.
* If `Y01 <= -1`, the same cell strengthens the first `P` fan while the
  consecutive hull triangle `U2 L0 L1` strengthens the two following fan
  sectors.  A 23-copy Laurent AM--GM certificate closes this branch.

Both theorems below are deliberately chamber-free scalar interfaces.  The
geometric adapter supplies only cleared-denominator inequalities.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## The `Y01 >= 1` branch -/

noncomputable def hullSixThreeThreeP022YPosLaurent
    (a b c d e f : ℝ) : ℝ :=
  a + d + d / a + e / a + c / b + a * c / (b * d) +
    a / d + f / d + f * b / (c * d) + b / c

noncomputable def hullSixThreeThreeP022YPosTerm
    (a b c d e f : ℝ) : Fin 10 → ℝ :=
  ![a, d, d / a, e / a, c / b, a * c / (b * d),
    a / d, f / d, f * b / (c * d), b / c]

def hullSixThreeThreeP022YPosWeight : Fin 10 → ℕ :=
  ![1, 2, 2, 1, 1, 1, 1, 1, 1, 1]

noncomputable def hullSixThreeThreeP022YPosConstant : ℝ :=
  1 / 16

theorem hullSixThreeThreeP022YPos_weight_pos
    (i : Fin 10) : 0 < hullSixThreeThreeP022YPosWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP022YPosWeight]

theorem hullSixThreeThreeP022YPos_weight_sum :
    ∑ i, hullSixThreeThreeP022YPosWeight i = 12 := by
  norm_num [hullSixThreeThreeP022YPosWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP022YPos_term_nonneg
    {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (i : Fin 10) :
    0 ≤ hullSixThreeThreeP022YPosTerm a b c d e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP022YPosTerm] <;>
    positivity

theorem hullSixThreeThreeP022YPos_term_sum
    (a b c d e f : ℝ) :
    ∑ i, hullSixThreeThreeP022YPosTerm a b c d e f i =
      hullSixThreeThreeP022YPosLaurent a b c d e f := by
  simp [hullSixThreeThreeP022YPosTerm,
    hullSixThreeThreeP022YPosLaurent, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP022YPos_term_product
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeP022YPosTerm a b c d e f i /
          (hullSixThreeThreeP022YPosWeight i : ℝ)) ^
            hullSixThreeThreeP022YPosWeight i) =
      hullSixThreeThreeP022YPosConstant * e * f ^ 2 := by
  simp [hullSixThreeThreeP022YPosTerm,
    hullSixThreeThreeP022YPosWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP022YPosConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeP022YPos_constant_pos :
    0 < hullSixThreeThreeP022YPosConstant := by
  norm_num [hullSixThreeThreeP022YPosConstant]

theorem hullSixThreeThreeP022YPos_integer_gap :
    (19 : ℕ) ^ 12 * 16 < 24 ^ 12 := by
  norm_num

theorem hullSixThreeThreeP022YPos_root_gap :
    (19 : ℝ) / 2 <
      12 * hullSixThreeThreeP022YPosConstant ^ ((12 : ℝ)⁻¹) := by
  have hpow :
      ((19 : ℝ) / 24) ^ 12 < hullSixThreeThreeP022YPosConstant := by
    norm_num [hullSixThreeThreeP022YPosConstant]
  have hpowRpow :
      ((19 : ℝ) / 24) ^ (12 : ℝ) <
        hullSixThreeThreeP022YPosConstant := by
    change ((19 : ℝ) / 24) ^ ((12 : ℕ) : ℝ) <
      hullSixThreeThreeP022YPosConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (19 : ℝ) / 24 <
        hullSixThreeThreeP022YPosConstant ^ ((12 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP022YPos_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP022YPos_laurent_gt
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f) :
    (19 : ℝ) / 2 < hullSixThreeThreeP022YPosLaurent a b c d e f := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP022YPosWeight
    (hullSixThreeThreeP022YPosTerm a b c d e f)
    hullSixThreeThreeP022YPos_weight_pos
    (hullSixThreeThreeP022YPos_term_nonneg
      ha.le hb.le hc.le hd.le he.le hf.le)
  rw [hullSixThreeThreeP022YPos_weight_sum,
    hullSixThreeThreeP022YPos_term_product ha hb hc hd he hf] at hamgm
  have hResidual : (1 : ℝ) ≤ e * f ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ e * f ^ 2 :=
        mul_le_mul he1 (one_le_pow₀ hf1) (by norm_num) (by positivity)
  have hProductFloor :
      hullSixThreeThreeP022YPosConstant ≤
        hullSixThreeThreeP022YPosConstant * e * f ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hResidual
      (le_of_lt hullSixThreeThreeP022YPos_constant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixThreeThreeP022YPosConstant ^ ((12 : ℝ)⁻¹) ≤
        (hullSixThreeThreeP022YPosConstant * e * f ^ 2) ^
          ((12 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixThreeThreeP022YPos_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixThreeThreeP022YPos_term_sum a b c d e f]
  exact hullSixThreeThreeP022YPos_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-- Cleared-denominator six-fan wrapper for the `Y01 >= 1` branch. -/
theorem hullSixThreeThreeP022YPos_scalar
    {a b c d e f A B C D E F : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hA : c * d + a * c + a * b ≤ b * d * A)
    (hB : 1 ≤ B)
    (hC : c * f + b * f + b * d ≤ c * d * C)
    (hD : 1 ≤ D)
    (hE : a * (d - e) + d + e ≤ a * E)
    (hF : a + e + 1 ≤ F) :
    (25 : ℝ) / 2 < A + B + C + D + E + F := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hf0 : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have hbd0 : 0 < b * d := mul_pos hb0 hd0
  have hcd0 : 0 < c * d := mul_pos hc0 hd0
  have hAlower : c / b + a * c / (b * d) + a / d ≤ A := by
    calc
      c / b + a * c / (b * d) + a / d =
          (c * d + a * c + a * b) / (b * d) := by
        field_simp [hb0.ne', hd0.ne'] <;> ring
      _ ≤ A := (div_le_iff₀ hbd0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hA)
  have hClower : f / d + f * b / (c * d) + b / c ≤ C := by
    calc
      f / d + f * b / (c * d) + b / c =
          (c * f + b * f + b * d) / (c * d) := by
        field_simp [hc0.ne', hd0.ne'] <;> ring
      _ ≤ C := (div_le_iff₀ hcd0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hC)
  have hElower : d - e + d / a + e / a ≤ E := by
    calc
      d - e + d / a + e / a =
          (a * (d - e) + d + e) / a := by
        field_simp [ha0.ne'] <;> ring
      _ ≤ E := (div_le_iff₀ ha0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hE)
  have hL := hullSixThreeThreeP022YPos_laurent_gt ha hb hc hd he hf
  dsimp [hullSixThreeThreeP022YPosLaurent] at hL
  linarith

/-! ## The `Y01 <= -1` branch -/

noncomputable def hullSixThreeThreeP022YNegLaurent
    (a b c d e f : ℝ) : ℝ :=
  a + e + c + a * c / d + c / d + a / d + f / c + d / c +
    e / c + d * e / (c * f) + d / f

noncomputable def hullSixThreeThreeP022YNegTerm
    (a b c d e f : ℝ) : Fin 11 → ℝ :=
  ![a, e, c, a * c / d, c / d, a / d, f / c, d / c,
    e / c, d * e / (c * f), d / f]

def hullSixThreeThreeP022YNegWeight : Fin 11 → ℕ :=
  ![1, 2, 5, 1, 2, 2, 3, 2, 2, 1, 2]

noncomputable def hullSixThreeThreeP022YNegConstant : ℝ :=
  1 / ((2 : ℝ) ^ 12 * 3 ^ 3 * 5 ^ 5)

theorem hullSixThreeThreeP022YNeg_weight_pos
    (i : Fin 11) : 0 < hullSixThreeThreeP022YNegWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP022YNegWeight]

theorem hullSixThreeThreeP022YNeg_weight_sum :
    ∑ i, hullSixThreeThreeP022YNegWeight i = 23 := by
  norm_num [hullSixThreeThreeP022YNegWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP022YNeg_term_nonneg
    {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (i : Fin 11) :
    0 ≤ hullSixThreeThreeP022YNegTerm a b c d e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP022YNegTerm] <;>
    positivity

theorem hullSixThreeThreeP022YNeg_term_sum
    (a b c d e f : ℝ) :
    ∑ i, hullSixThreeThreeP022YNegTerm a b c d e f i =
      hullSixThreeThreeP022YNegLaurent a b c d e f := by
  simp [hullSixThreeThreeP022YNegTerm,
    hullSixThreeThreeP022YNegLaurent, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP022YNeg_term_product
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeP022YNegTerm a b c d e f i /
          (hullSixThreeThreeP022YNegWeight i : ℝ)) ^
            hullSixThreeThreeP022YNegWeight i) =
      hullSixThreeThreeP022YNegConstant * a ^ 4 * e ^ 5 := by
  simp [hullSixThreeThreeP022YNegTerm,
    hullSixThreeThreeP022YNegWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP022YNegConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeP022YNeg_constant_pos :
    0 < hullSixThreeThreeP022YNegConstant := by
  unfold hullSixThreeThreeP022YNegConstant
  positivity

theorem hullSixThreeThreeP022YNeg_integer_gap :
    (19 : ℕ) ^ 23 * 345600000 < 46 ^ 23 := by
  norm_num

theorem hullSixThreeThreeP022YNeg_root_gap :
    (19 : ℝ) / 2 <
      23 * hullSixThreeThreeP022YNegConstant ^ ((23 : ℝ)⁻¹) := by
  have hpow :
      ((19 : ℝ) / 46) ^ 23 < hullSixThreeThreeP022YNegConstant := by
    norm_num [hullSixThreeThreeP022YNegConstant]
  have hpowRpow :
      ((19 : ℝ) / 46) ^ (23 : ℝ) <
        hullSixThreeThreeP022YNegConstant := by
    change ((19 : ℝ) / 46) ^ ((23 : ℕ) : ℝ) <
      hullSixThreeThreeP022YNegConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (19 : ℝ) / 46 <
        hullSixThreeThreeP022YNegConstant ^ ((23 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP022YNeg_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP022YNeg_laurent_gt
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f) :
    (19 : ℝ) / 2 < hullSixThreeThreeP022YNegLaurent a b c d e f := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP022YNegWeight
    (hullSixThreeThreeP022YNegTerm a b c d e f)
    hullSixThreeThreeP022YNeg_weight_pos
    (hullSixThreeThreeP022YNeg_term_nonneg
      ha.le hb.le hc.le hd.le he.le hf.le)
  rw [hullSixThreeThreeP022YNeg_weight_sum,
    hullSixThreeThreeP022YNeg_term_product ha hb hc hd he hf] at hamgm
  have hResidual : (1 : ℝ) ≤ a ^ 4 * e ^ 5 := by
    simpa using (mul_le_mul (one_le_pow₀ ha1) (one_le_pow₀ he1)
      (by norm_num) (by positivity))
  have hProductFloor :
      hullSixThreeThreeP022YNegConstant ≤
        hullSixThreeThreeP022YNegConstant * a ^ 4 * e ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hResidual
      (le_of_lt hullSixThreeThreeP022YNeg_constant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixThreeThreeP022YNegConstant ^ ((23 : ℝ)⁻¹) ≤
        (hullSixThreeThreeP022YNegConstant * a ^ 4 * e ^ 5) ^
          ((23 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixThreeThreeP022YNeg_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixThreeThreeP022YNeg_term_sum a b c d e f]
  exact hullSixThreeThreeP022YNeg_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-- Cleared-denominator six-fan wrapper for the `Y01 <= -1` branch. -/
theorem hullSixThreeThreeP022YNeg_scalar
    {a b c d e f A B C D E F : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hA : c * d + a * c + c + a ≤ d * A)
    (hB : 1 ≤ B)
    (hCD : c + f + d ≤ c * (C + D))
    (hE : e * f + d * e + c * d ≤ c * f * E)
    (hF : a + e + 1 ≤ F) :
    (25 : ℝ) / 2 < A + B + C + D + E + F := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hf0 : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have hcf0 : 0 < c * f := mul_pos hc0 hf0
  have hAlower : c + a * c / d + c / d + a / d ≤ A := by
    calc
      c + a * c / d + c / d + a / d =
          (c * d + a * c + c + a) / d := by
        field_simp [hd0.ne'] <;> ring
      _ ≤ A := (div_le_iff₀ hd0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hA)
  have hCDlower : 1 + f / c + d / c ≤ C + D := by
    calc
      1 + f / c + d / c = (c + f + d) / c := by
        field_simp [hc0.ne'] <;> ring
      _ ≤ C + D := (div_le_iff₀ hc0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hCD)
  have hElower : e / c + d * e / (c * f) + d / f ≤ E := by
    calc
      e / c + d * e / (c * f) + d / f =
          (e * f + d * e + c * d) / (c * f) := by
        field_simp [hc0.ne', hf0.ne'] <;> ring
      _ ≤ E := (div_le_iff₀ hcf0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hE)
  have hL := hullSixThreeThreeP022YNeg_laurent_gt ha hb hc hd he hf
  dsimp [hullSixThreeThreeP022YNegLaurent] at hL
  linarith

end Heilbronn8
