import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ14AscendingAMGM

/-!
# Direct mixed-fan closure for the q-blind `q = 13` chamber

The exact `MRRR / LMMR` table has a terminal recurrence which is stronger
than the terminal inequality used by the old plateau route.  In the
descending-height branch, averaging the two bounds on `A` and the two bounds
on `x` reduces the normalized fan directly to one of two Laurent sums,
according as `d - f <= f` or `f < d - f`.  Their weighted AM--GM
certificates have total masses fifty and one hundred.

In the ascending-height branch the mixed q14 proof applies verbatim away
from its unique equality locus.  At that locus the exact q13 terminal
recurrence supplies the missing strict inequality.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

open scoped BigOperators

/-! ## The descending mixed-fan core -/

noncomputable def hullSixTwoFourQ13DescendingCore
    (a b c f t : ℝ) : ℝ :=
  3 + a / 2 + b / 2 + c / 2 + t / 2 + f / t + a / b +
    a / (2 * c) + b / (2 * c) + c / (2 * a) + c / (2 * b) +
    f / (2 * a) + f / (2 * b) + f / (2 * c) +
    t / (2 * a) + t / (2 * b) +
    a * f / (2 * b) + a * f / (2 * b * c) +
    (a + b + f + a * f / b) / (2 * (f + t))

noncomputable def hullSixTwoFourQ13DescendingLeftLaurent
    (a b c f t : ℝ) : ℝ :=
  13 / 4 + a / 2 + b / 2 + c / 2 + t / 2 + f / t +
    5 * a / (4 * b) + a / (2 * c) + b / (2 * c) +
    c / (2 * a) + c / (2 * b) + f / (2 * a) +
    f / (2 * b) + f / (2 * c) + t / (2 * a) +
    t / (2 * b) + a * f / (2 * b) + a * f / (2 * b * c) +
    a / (4 * f) + b / (4 * f)

noncomputable def hullSixTwoFourQ13DescendingLeftTerm
    (a b c f t : ℝ) : Fin 20 → ℝ :=
  ![13 / 4, a / 2, b / 2, c / 2, t / 2, f / t,
    5 * a / (4 * b), a / (2 * c), b / (2 * c),
    c / (2 * a), c / (2 * b), f / (2 * a),
    f / (2 * b), f / (2 * c), t / (2 * a),
    t / (2 * b), a * f / (2 * b), a * f / (2 * b * c),
    a / (4 * f), b / (4 * f)]

def hullSixTwoFourQ13DescendingLeftWeight : Fin 20 → ℕ :=
  ![13, 2, 3, 3, 2, 5, 3, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2]

noncomputable def hullSixTwoFourQ13DescendingLeftConstant : ℝ :=
  1 / ((2 : ℝ) ^ 76 * (3 : ℝ) ^ 12 * (5 : ℝ) ^ 2)

theorem hullSixTwoFourQ13DescendingLeft_weight_pos
    (i : Fin 20) : 0 < hullSixTwoFourQ13DescendingLeftWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ13DescendingLeftWeight]

theorem hullSixTwoFourQ13DescendingLeft_weight_sum :
    ∑ i, hullSixTwoFourQ13DescendingLeftWeight i = 50 := by
  norm_num [hullSixTwoFourQ13DescendingLeftWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ13DescendingLeft_term_nonneg
    {a b c f t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hf : 0 ≤ f) (ht : 0 ≤ t) (i : Fin 20) :
    0 ≤ hullSixTwoFourQ13DescendingLeftTerm a b c f t i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ13DescendingLeftTerm] <;>
    positivity

theorem hullSixTwoFourQ13DescendingLeft_term_sum
    (a b c f t : ℝ) :
    ∑ i, hullSixTwoFourQ13DescendingLeftTerm a b c f t i =
      hullSixTwoFourQ13DescendingLeftLaurent a b c f t := by
  simp [hullSixTwoFourQ13DescendingLeftTerm,
    hullSixTwoFourQ13DescendingLeftLaurent, Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFourQ13DescendingLeft_term_product
    {a b c f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourQ13DescendingLeftTerm a b c f t i /
          (hullSixTwoFourQ13DescendingLeftWeight i : ℝ)) ^
            hullSixTwoFourQ13DescendingLeftWeight i) =
      hullSixTwoFourQ13DescendingLeftConstant * (a ^ 3 * f ^ 8) := by
  simp [hullSixTwoFourQ13DescendingLeftTerm,
    hullSixTwoFourQ13DescendingLeftWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ13DescendingLeftConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hf.ne', ht.ne'] <;> ring

theorem hullSixTwoFourQ13DescendingLeft_constant_pos :
    0 < hullSixTwoFourQ13DescendingLeftConstant := by
  norm_num [hullSixTwoFourQ13DescendingLeftConstant]

theorem hullSixTwoFourQ13DescendingLeft_factor_gap :
    (3 : ℕ) ^ 12 * 5 ^ 2 < 2 ^ 24 := by
  norm_num

theorem hullSixTwoFourQ13DescendingLeft_root_gap :
    (25 : ℝ) / 2 <
      50 * hullSixTwoFourQ13DescendingLeftConstant ^ ((50 : ℝ)⁻¹) := by
  have hpow :
      ((1 : ℝ) / 4) ^ 50 < hullSixTwoFourQ13DescendingLeftConstant := by
    norm_num [hullSixTwoFourQ13DescendingLeftConstant]
  have hpowRpow :
      ((1 : ℝ) / 4) ^ (50 : ℝ) <
        hullSixTwoFourQ13DescendingLeftConstant := by
    change ((1 : ℝ) / 4) ^ ((50 : ℕ) : ℝ) <
      hullSixTwoFourQ13DescendingLeftConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (1 : ℝ) / 4 <
        hullSixTwoFourQ13DescendingLeftConstant ^ ((50 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourQ13DescendingLeft_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourQ13DescendingLeft_laurent_gt
    {a b c f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (ht : 0 < t)
    (ha1 : 1 ≤ a) (hf1 : 1 ≤ f) :
    (25 : ℝ) / 2 <
      hullSixTwoFourQ13DescendingLeftLaurent a b c f t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ13DescendingLeftWeight
    (hullSixTwoFourQ13DescendingLeftTerm a b c f t)
    hullSixTwoFourQ13DescendingLeft_weight_pos
    (hullSixTwoFourQ13DescendingLeft_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hf) (le_of_lt ht))
  rw [hullSixTwoFourQ13DescendingLeft_weight_sum,
    hullSixTwoFourQ13DescendingLeft_term_product ha hb hc hf ht] at hamgm
  have ha3 : (1 : ℝ) ≤ a ^ 3 := one_le_pow₀ ha1
  have hf8 : (1 : ℝ) ≤ f ^ 8 := one_le_pow₀ hf1
  have hmonomial : (1 : ℝ) ≤ a ^ 3 * f ^ 8 := by
    simpa using mul_le_mul ha3 hf8 (by norm_num) (by positivity)
  have hProductFloor :
      hullSixTwoFourQ13DescendingLeftConstant ≤
        hullSixTwoFourQ13DescendingLeftConstant * (a ^ 3 * f ^ 8) := by
    have := mul_le_mul_of_nonneg_left hmonomial
      (le_of_lt hullSixTwoFourQ13DescendingLeft_constant_pos)
    simpa using this
  have hRootFloor :
      hullSixTwoFourQ13DescendingLeftConstant ^ ((50 : ℝ)⁻¹) ≤
        (hullSixTwoFourQ13DescendingLeftConstant * (a ^ 3 * f ^ 8)) ^
          ((50 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixTwoFourQ13DescendingLeft_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourQ13DescendingLeft_term_sum a b c f t]
  exact hullSixTwoFourQ13DescendingLeft_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

noncomputable def hullSixTwoFourQ13DescendingRightLaurent
    (a b c f t : ℝ) : ℝ :=
  3 + a / 2 + b / 2 + c / 2 + t / 2 + 5 * f / (4 * t) +
    a / b + a / (2 * c) + b / (2 * c) + c / (2 * a) +
    c / (2 * b) + f / (2 * a) + f / (2 * b) + f / (2 * c) +
    t / (2 * a) + t / (2 * b) + a * f / (2 * b) +
    a * f / (2 * b * c) + a / (4 * t) + b / (4 * t) +
    a * f / (4 * b * t)

noncomputable def hullSixTwoFourQ13DescendingRightTerm
    (a b c f t : ℝ) : Fin 21 → ℝ :=
  ![3, a / 2, b / 2, c / 2, t / 2, 5 * f / (4 * t),
    a / b, a / (2 * c), b / (2 * c), c / (2 * a),
    c / (2 * b), f / (2 * a), f / (2 * b), f / (2 * c),
    t / (2 * a), t / (2 * b), a * f / (2 * b),
    a * f / (2 * b * c), a / (4 * t), b / (4 * t),
    a * f / (4 * b * t)]

def hullSixTwoFourQ13DescendingRightWeight : Fin 21 → ℕ :=
  ![24, 4, 8, 5, 5, 8, 4, 3, 6, 5, 3, 4, 2, 3, 5, 3, 2, 1, 2, 2, 1]

noncomputable def hullSixTwoFourQ13DescendingRightConstant : ℝ :=
  1 / ((2 : ℝ) ^ 243 * (3 : ℝ) ^ 18 * (5 : ℝ) ^ 12)

theorem hullSixTwoFourQ13DescendingRight_weight_pos
    (i : Fin 21) : 0 < hullSixTwoFourQ13DescendingRightWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ13DescendingRightWeight]

theorem hullSixTwoFourQ13DescendingRight_weight_sum :
    ∑ i, hullSixTwoFourQ13DescendingRightWeight i = 100 := by
  norm_num [hullSixTwoFourQ13DescendingRightWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ13DescendingRight_term_nonneg
    {a b c f t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hf : 0 ≤ f) (ht : 0 ≤ t) (i : Fin 21) :
    0 ≤ hullSixTwoFourQ13DescendingRightTerm a b c f t i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ13DescendingRightTerm] <;>
    positivity

theorem hullSixTwoFourQ13DescendingRight_term_sum
    (a b c f t : ℝ) :
    ∑ i, hullSixTwoFourQ13DescendingRightTerm a b c f t i =
      hullSixTwoFourQ13DescendingRightLaurent a b c f t := by
  simp [hullSixTwoFourQ13DescendingRightTerm,
    hullSixTwoFourQ13DescendingRightLaurent, Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFourQ13DescendingRight_term_product
    {a b c f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourQ13DescendingRightTerm a b c f t i /
          (hullSixTwoFourQ13DescendingRightWeight i : ℝ)) ^
            hullSixTwoFourQ13DescendingRightWeight i) =
      hullSixTwoFourQ13DescendingRightConstant * (a ^ 3 * f ^ 21) := by
  simp [hullSixTwoFourQ13DescendingRightTerm,
    hullSixTwoFourQ13DescendingRightWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ13DescendingRightConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hf.ne', ht.ne'] <;> ring

theorem hullSixTwoFourQ13DescendingRight_constant_pos :
    0 < hullSixTwoFourQ13DescendingRightConstant := by
  norm_num [hullSixTwoFourQ13DescendingRightConstant]

theorem hullSixTwoFourQ13DescendingRight_factor_gap :
    (3 : ℕ) ^ 18 * 5 ^ 12 < 2 ^ 57 := by
  norm_num

theorem hullSixTwoFourQ13DescendingRight_root_gap :
    (25 : ℝ) / 2 <
      100 * hullSixTwoFourQ13DescendingRightConstant ^ ((100 : ℝ)⁻¹) := by
  have hpow :
      ((1 : ℝ) / 8) ^ 100 < hullSixTwoFourQ13DescendingRightConstant := by
    norm_num [hullSixTwoFourQ13DescendingRightConstant]
  have hpowRpow :
      ((1 : ℝ) / 8) ^ (100 : ℝ) <
        hullSixTwoFourQ13DescendingRightConstant := by
    change ((1 : ℝ) / 8) ^ ((100 : ℕ) : ℝ) <
      hullSixTwoFourQ13DescendingRightConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (1 : ℝ) / 8 <
        hullSixTwoFourQ13DescendingRightConstant ^ ((100 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourQ13DescendingRight_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourQ13DescendingRight_laurent_gt
    {a b c f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (ht : 0 < t)
    (ha1 : 1 ≤ a) (hf1 : 1 ≤ f) :
    (25 : ℝ) / 2 <
      hullSixTwoFourQ13DescendingRightLaurent a b c f t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ13DescendingRightWeight
    (hullSixTwoFourQ13DescendingRightTerm a b c f t)
    hullSixTwoFourQ13DescendingRight_weight_pos
    (hullSixTwoFourQ13DescendingRight_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hf) (le_of_lt ht))
  rw [hullSixTwoFourQ13DescendingRight_weight_sum,
    hullSixTwoFourQ13DescendingRight_term_product ha hb hc hf ht] at hamgm
  have ha3 : (1 : ℝ) ≤ a ^ 3 := one_le_pow₀ ha1
  have hf21 : (1 : ℝ) ≤ f ^ 21 := one_le_pow₀ hf1
  have hmonomial : (1 : ℝ) ≤ a ^ 3 * f ^ 21 := by
    simpa using mul_le_mul ha3 hf21 (by norm_num) (by positivity)
  have hProductFloor :
      hullSixTwoFourQ13DescendingRightConstant ≤
        hullSixTwoFourQ13DescendingRightConstant * (a ^ 3 * f ^ 21) := by
    have := mul_le_mul_of_nonneg_left hmonomial
      (le_of_lt hullSixTwoFourQ13DescendingRight_constant_pos)
    simpa using this
  have hRootFloor :
      hullSixTwoFourQ13DescendingRightConstant ^ ((100 : ℝ)⁻¹) ≤
        (hullSixTwoFourQ13DescendingRightConstant * (a ^ 3 * f ^ 21)) ^
          ((100 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixTwoFourQ13DescendingRight_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourQ13DescendingRight_term_sum a b c f t]
  exact hullSixTwoFourQ13DescendingRight_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

theorem hullSixTwoFourQ13Descending_left_le_core
    {a b c f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (ht : 0 < t) (htf : t ≤ f) :
    hullSixTwoFourQ13DescendingLeftLaurent a b c f t ≤
      hullSixTwoFourQ13DescendingCore a b c f t := by
  have hsum : 0 < f + t := add_pos hf ht
  have hfactor : 0 ≤ a + b + f + a * f / b := by positivity
  have hgap : 0 ≤ f - t := sub_nonneg.mpr htf
  have hden : 0 < 4 * f * (f + t) := by positivity
  have hquotient :
      0 ≤ (a + b + f + a * f / b) * (f - t) /
        (4 * f * (f + t)) := by
    exact div_nonneg (mul_nonneg hfactor hgap) (le_of_lt hden)
  have hid :
      hullSixTwoFourQ13DescendingCore a b c f t -
          hullSixTwoFourQ13DescendingLeftLaurent a b c f t =
        (a + b + f + a * f / b) * (f - t) /
          (4 * f * (f + t)) := by
    dsimp [hullSixTwoFourQ13DescendingCore,
      hullSixTwoFourQ13DescendingLeftLaurent]
    field_simp [ha.ne', hb.ne', hc.ne', hf.ne', ht.ne', hsum.ne'] <;> ring
  linarith

theorem hullSixTwoFourQ13Descending_right_le_core
    {a b c f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (ht : 0 < t) (hft : f ≤ t) :
    hullSixTwoFourQ13DescendingRightLaurent a b c f t ≤
      hullSixTwoFourQ13DescendingCore a b c f t := by
  have hsum : 0 < f + t := add_pos hf ht
  have hfactor : 0 ≤ a + b + f + a * f / b := by positivity
  have hgap : 0 ≤ t - f := sub_nonneg.mpr hft
  have hden : 0 < 4 * t * (f + t) := by positivity
  have hquotient :
      0 ≤ (a + b + f + a * f / b) * (t - f) /
        (4 * t * (f + t)) := by
    exact div_nonneg (mul_nonneg hfactor hgap) (le_of_lt hden)
  have hid :
      hullSixTwoFourQ13DescendingCore a b c f t -
          hullSixTwoFourQ13DescendingRightLaurent a b c f t =
        (a + b + f + a * f / b) * (t - f) /
          (4 * t * (f + t)) := by
    dsimp [hullSixTwoFourQ13DescendingCore,
      hullSixTwoFourQ13DescendingRightLaurent]
    field_simp [ha.ne', hb.ne', hc.ne', hf.ne', ht.ne', hsum.ne'] <;> ring
  linarith

/-! ## Public scalar closures -/

/-- Direct q13 closure in the branch `e < d`. -/
theorem hullSixTwoFourQ13DescendingDirect_scalar
    {a b c d e f A C x y z Fp K : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hC1 : 1 ≤ C) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z) (hK1 : 1 ≤ K)
    (hed : e < d)
    (hAtransition : a + b ≤ c * A)
    (hVerticalTransition : a + b ≤ e * (A + a - b))
    (hTopTransition : c + d ≤ a * x)
    (hBottomTransition : c + d ≤ b * (x + c - d))
    (hTerminal : b * Fp = f * (A + a - b) + a * K)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hy : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hfe : f < e := by
    by_contra hnot
    have hef : e ≤ f := le_of_not_gt hnot
    have hfirst : (e - d) * z < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hed) hz
    have hsecond : (f - e) * y ≥ 0 :=
      mul_nonneg (sub_nonneg.mpr hef) (le_of_lt hy)
    linarith
  let t : ℝ := d - f
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hefPos : 0 < e - f := sub_pos.mpr hfe
  have hEarReduced : d ≤ (e - f) * y := by
    have hzScaled : d - e ≤ (d - e) * z := by
      have := mul_le_mul_of_nonneg_left hz1 (sub_nonneg.mpr (le_of_lt hed))
      simpa using this
    nlinarith [hEar1]
  have hyAtE : d / (e - f) ≤ y := by
    exact (div_le_iff₀ hefPos).2 (by simpa [mul_comm] using hEarReduced)
  have hdenStrict : e - f < d - f := by linarith
  have hyAtD : d / (d - f) < y := by
    have hfrac : d / (d - f) < d / (e - f) := by
      rw [div_lt_div_iff₀ ht hefPos]
      nlinarith
    exact hfrac.trans_le hyAtE

  have hAAtC : (a + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAtransition)
  have hAAtE : (a + b) / e - a + b ≤ A := by
    have hdiv : (a + b) / e ≤ A + a - b := by
      exact (div_le_iff₀ he).2 (by simpa [mul_comm] using hVerticalTransition)
    linarith
  have hfracDE : (a + b) / d ≤ (a + b) / e := by
    rw [div_le_div_iff₀ hd he]
    nlinarith
  have hAAtD : (a + b) / d - a + b ≤ A := by
    linarith
  have hAAverage :
      ((a + b) / c + ((a + b) / d - a + b)) / 2 ≤ A := by
    nlinarith [hAAtC, hAAtD]

  have hxTop : (c + d) / a ≤ x := by
    exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hTopTransition)
  have hxBottom : d - c + (c + d) / b ≤ x := by
    have hdiv : (c + d) / b ≤ x + c - d := by
      exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hBottomTransition)
    linarith
  have hxAverage :
      ((c + d) / a + (d - c + (c + d) / b)) / 2 ≤ x := by
    nlinarith [hxTop, hxBottom]

  have haK : a ≤ a * K := by
    simpa using mul_le_mul_of_nonneg_left hK1 (le_of_lt ha)
  have hTerminalNumerator :
      f * (A + a - b) + a ≤ b * Fp := by
    rw [hTerminal]
    linarith
  have hTerminalDiv :
      (f * (A + a - b) + a) / b ≤ Fp := by
    exact (div_le_iff₀ hb).2 (by
      simpa [mul_comm] using hTerminalNumerator)
  have hTerminalLower :
      (1 + f / b) * A + f * (a - b) / b + a / b ≤ A + Fp := by
    have hid :
        (1 + f / b) * A + f * (a - b) / b + a / b =
          A + (f * (A + a - b) + a) / b := by
      field_simp [hb.ne'] <;> ring
    rw [hid]
    linarith
  have hCoefficient : 0 ≤ 1 + f / b := by positivity
  have hAWeighted := mul_le_mul_of_nonneg_left hAAverage hCoefficient
  have hAFpLower :
      (1 + f / b) *
            (((a + b) / c + ((a + b) / d - a + b)) / 2) +
          f * (a - b) / b + a / b ≤ A + Fp := by
    nlinarith [hAWeighted, hTerminalLower]

  have hsum : 0 < f + t := by
    dsimp [t]
    linarith
  have hdf : d - f ≠ 0 := by
    exact ne_of_gt (by simpa [t] using ht)
  have hCoreIdentity :
      hullSixTwoFourQ13DescendingCore a b c f t =
        a + c + 2 +
          ((1 + f / b) *
              (((a + b) / c + ((a + b) / d - a + b)) / 2) +
            f * (a - b) / b + a / b) +
          ((c + d) / a + (d - c + (c + d) / b)) / 2 +
          d / (d - f) := by
    dsimp [hullSixTwoFourQ13DescendingCore, t]
    field_simp [ha.ne', hb.ne', hc.ne', hd.ne', hdf, hsum.ne'] <;> ring
  have hCoreBelow :
      hullSixTwoFourQ13DescendingCore a b c f t <
        A + C + x + y + z + Fp + a + c := by
    rw [hCoreIdentity]
    nlinarith [hAFpLower, hxAverage, hyAtD, hC1, hz1]

  by_cases htf : t ≤ f
  · have hLaurent := hullSixTwoFourQ13DescendingLeft_laurent_gt
      ha hb hc hf ht ha1 hf1
    have hCompare := hullSixTwoFourQ13Descending_left_le_core
      ha hb hc hf ht htf
    linarith
  · have hft : f ≤ t := (lt_of_not_ge htf).le
    have hLaurent := hullSixTwoFourQ13DescendingRight_laurent_gt
      ha hb hc hf ht ha1 hf1
    have hCompare := hullSixTwoFourQ13Descending_right_le_core
      ha hb hc hf ht hft
    linarith

/-- Direct q13 closure in the branch `d <= e`. -/
theorem hullSixTwoFourQ13AscendingDirect_scalar
    {a b c d e f A C x y z Fp K : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hf1 : 1 ≤ f)
    (hcd : c < d) (hde : d ≤ e)
    (hC1 : 1 ≤ C) (hz1 : 1 ≤ z) (hFp1 : 1 ≤ Fp) (hK1 : 1 ≤ K)
    (hAtransition : a + b ≤ c * A)
    (hTopTransition : c + d ≤ a * x)
    (hBottomTransition : c + d ≤ b * (x + c - d))
    (hYUpper : b * y ≤ e * (b + d - 1) - d)
    (hTerminal : b * Fp = f * (A + a - b) + a * K)
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - f) * y - (d - e) * z) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  refine hullSixTwoFourAscendingMixed_scalar_of_exceptional
    ha1 hb1 hc1 hf1 hcd hde hC1 hz1 hFp1
    hAtransition hTopTransition hBottomTransition hYUpper hEar0 hEar1 ?_
  intro haEq hcEq hdEq _heEq hyEq hfEq
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hALowerExceptional : 1 + b ≤ A := by
    rw [haEq, hcEq] at hAtransition
    nlinarith
  have hTerminalExceptional : 3 ≤ b * Fp := by
    rw [haEq, hfEq] at hTerminal
    have hAK : 1 ≤ K := hK1
    nlinarith [hALowerExceptional]
  have hFpLowerExceptional : 3 / b ≤ Fp := by
    exact (div_le_iff₀ hb).2 (by
      simpa [mul_comm] using hTerminalExceptional)
  have hxLowerExceptional : 1 + 3 / b ≤ x := by
    rw [hcEq, hdEq] at hBottomTransition
    have hdiv : 3 / b ≤ x - 1 := (div_le_iff₀ hb).2 (by
      calc
        (3 : ℝ) = 1 + 2 := by norm_num
        _ ≤ b * (x + 1 - 2) := hBottomTransition
        _ = (x - 1) * b := by ring)
    linarith
  have hpositive : 0 < (4 * b - 9) ^ 2 + 15 := by
    nlinarith [sq_nonneg (4 * b - 9)]
  have hgap : (9 : ℝ) / 2 < b + 6 / b := by
    have hid :
        (b + 6 / b) - (9 : ℝ) / 2 =
          ((4 * b - 9) ^ 2 + 15) / (16 * b) := by
      field_simp [hb.ne'] <;> ring
    have hfrac : 0 < ((4 * b - 9) ^ 2 + 15) / (16 * b) := by
      positivity
    nlinarith
  rw [haEq, hcEq, hyEq]
  nlinarith [hALowerExceptional, hxLowerExceptional,
    hFpLowerExceptional, hC1, hz1, hgap]

end Heilbronn8
