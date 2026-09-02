import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the `p = (1,3)` maximal-q frontier

Only four `P`-cross-chord signs are used: `X00 >= 1`, `X01 <= -1`,
`X12 >= 1`, and `X13 <= -1`.  Eliminating the two internal chords from
the first two lower recurrences gives

```text
d * e * A >= a * b * E1 + a * d + b * e.
```

The two lower ears then leave four small Laurent sums.  Each is closed by
an exact weighted AM--GM certificate.  No `Q` cross-chord sign occurs in
this file.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

/-! ## The branch `d <= e`, with `t = d - c` -/

noncomputable def hullSixTwoFourP13AscNearLaurent
    (a b c e t : ℝ) : ℝ :=
  3 + a + 1 / b + 3 * b / (2 * a) + 2 * c / a + t / a +
    e / b + a / e + c / e + c / t + b / (2 * c) +
      a * b / (e * t) + b * c / (e * t)

noncomputable def hullSixTwoFourP13AscNearTerm
    (a b c e t : ℝ) : Fin 13 → ℝ :=
  ![3, a, 1 / b, 3 * b / (2 * a), 2 * c / a, t / a,
    e / b, a / e, c / e, c / t, b / (2 * c),
    a * b / (e * t), b * c / (e * t)]

def hullSixTwoFourP13AscNearWeight : Fin 13 → ℕ :=
  ![7, 3, 3, 2, 1, 3, 5, 2, 1, 1, 4, 1, 1]

noncomputable def hullSixTwoFourP13AscNearConstant : ℝ :=
  1 / ((2 : ℝ) ^ 17 * 5 ^ 5 * 7 ^ 7)

theorem hullSixTwoFourP13AscNearWeight_pos
    (i : Fin 13) : 0 < hullSixTwoFourP13AscNearWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP13AscNearWeight]

theorem hullSixTwoFourP13AscNearWeight_sum :
    ∑ i, hullSixTwoFourP13AscNearWeight i = 34 := by
  norm_num [hullSixTwoFourP13AscNearWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourP13AscNearTerm_nonneg
    {a b c e t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (ht : 0 ≤ t) (i : Fin 13) :
    0 ≤ hullSixTwoFourP13AscNearTerm a b c e t i := by
  fin_cases i <;>
    simp [hullSixTwoFourP13AscNearTerm] <;> positivity

theorem hullSixTwoFourP13AscNearTerm_sum
    (a b c e t : ℝ) :
    ∑ i, hullSixTwoFourP13AscNearTerm a b c e t i =
      hullSixTwoFourP13AscNearLaurent a b c e t := by
  simp [hullSixTwoFourP13AscNearTerm,
    hullSixTwoFourP13AscNearLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFourP13AscNearTerm_product
    {a b c e t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourP13AscNearTerm a b c e t i /
          (hullSixTwoFourP13AscNearWeight i : ℝ)) ^
            hullSixTwoFourP13AscNearWeight i) =
      hullSixTwoFourP13AscNearConstant := by
  simp [hullSixTwoFourP13AscNearTerm,
    hullSixTwoFourP13AscNearWeight, Fin.prod_univ_succ,
    hullSixTwoFourP13AscNearConstant]
  field_simp [ha.ne', hb.ne', hc.ne', he.ne', ht.ne'] <;> ring

theorem hullSixTwoFourP13AscNearConstant_pos :
    0 < hullSixTwoFourP13AscNearConstant := by
  norm_num [hullSixTwoFourP13AscNearConstant]

theorem hullSixTwoFourP13AscNear_root_gap :
    (25 : ℝ) / 2 <
      34 * hullSixTwoFourP13AscNearConstant ^ ((34 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 68) ^ 34 < hullSixTwoFourP13AscNearConstant := by
    norm_num [hullSixTwoFourP13AscNearConstant]
  have hpowRpow :
      ((25 : ℝ) / 68) ^ (34 : ℝ) <
        hullSixTwoFourP13AscNearConstant := by
    change ((25 : ℝ) / 68) ^ ((34 : ℕ) : ℝ) <
      hullSixTwoFourP13AscNearConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 68 <
        hullSixTwoFourP13AscNearConstant ^ ((34 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourP13AscNearConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP13AscNear_laurent_gt
    {a b c e t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (ht : 0 < t) :
    (25 : ℝ) / 2 < hullSixTwoFourP13AscNearLaurent a b c e t := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFourP13AscNearWeight
    (hullSixTwoFourP13AscNearTerm a b c e t)
    hullSixTwoFourP13AscNearWeight_pos
    (hullSixTwoFourP13AscNearTerm_nonneg
      ha.le hb.le hc.le he.le ht.le)
  rw [hullSixTwoFourP13AscNearWeight_sum,
    hullSixTwoFourP13AscNearTerm_product ha hb hc he ht,
    hullSixTwoFourP13AscNearTerm_sum a b c e t] at hamgm
  exact hullSixTwoFourP13AscNear_root_gap.trans_le hamgm

noncomputable def hullSixTwoFourP13AscFarLaurent
    (a b c e t : ℝ) : ℝ :=
  3 + a + 1 / b + b / a + 2 * c / a + t / a + e / b +
    a / e + c / e + c / t + b / (2 * t) +
      b * c / (2 * a * t) + a * b / (e * t) + b * c / (e * t)

noncomputable def hullSixTwoFourP13AscFarTerm
    (a b c e t : ℝ) : Fin 14 → ℝ :=
  ![3, a, 1 / b, b / a, 2 * c / a, t / a, e / b,
    a / e, c / e, c / t, b / (2 * t), b * c / (2 * a * t),
    a * b / (e * t), b * c / (e * t)]

def hullSixTwoFourP13AscFarWeight : Fin 14 → ℕ :=
  ![10, 8, 2, 3, 2, 5, 5, 2, 1, 1, 1, 1, 1, 1]

noncomputable def hullSixTwoFourP13AscFarConstant : ℝ :=
  3 ^ 7 / ((2 : ℝ) ^ 40 * 5 ^ 20)

theorem hullSixTwoFourP13AscFarWeight_pos
    (i : Fin 14) : 0 < hullSixTwoFourP13AscFarWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP13AscFarWeight]

theorem hullSixTwoFourP13AscFarWeight_sum :
    ∑ i, hullSixTwoFourP13AscFarWeight i = 43 := by
  norm_num [hullSixTwoFourP13AscFarWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourP13AscFarTerm_nonneg
    {a b c e t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (ht : 0 ≤ t) (i : Fin 14) :
    0 ≤ hullSixTwoFourP13AscFarTerm a b c e t i := by
  fin_cases i <;>
    simp [hullSixTwoFourP13AscFarTerm] <;> positivity

theorem hullSixTwoFourP13AscFarTerm_sum
    (a b c e t : ℝ) :
    ∑ i, hullSixTwoFourP13AscFarTerm a b c e t i =
      hullSixTwoFourP13AscFarLaurent a b c e t := by
  simp [hullSixTwoFourP13AscFarTerm,
    hullSixTwoFourP13AscFarLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFourP13AscFarTerm_product
    {a b c e t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourP13AscFarTerm a b c e t i /
          (hullSixTwoFourP13AscFarWeight i : ℝ)) ^
            hullSixTwoFourP13AscFarWeight i) =
      hullSixTwoFourP13AscFarConstant * c ^ 6 := by
  simp [hullSixTwoFourP13AscFarTerm,
    hullSixTwoFourP13AscFarWeight, Fin.prod_univ_succ,
    hullSixTwoFourP13AscFarConstant]
  field_simp [ha.ne', hb.ne', hc.ne', he.ne', ht.ne'] <;> ring

theorem hullSixTwoFourP13AscFarConstant_pos :
    0 < hullSixTwoFourP13AscFarConstant := by
  norm_num [hullSixTwoFourP13AscFarConstant]

theorem hullSixTwoFourP13AscFar_root_gap :
    (25 : ℝ) / 2 <
      43 * hullSixTwoFourP13AscFarConstant ^ ((43 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 86) ^ 43 < hullSixTwoFourP13AscFarConstant := by
    norm_num [hullSixTwoFourP13AscFarConstant]
  have hpowRpow :
      ((25 : ℝ) / 86) ^ (43 : ℝ) <
        hullSixTwoFourP13AscFarConstant := by
    change ((25 : ℝ) / 86) ^ ((43 : ℕ) : ℝ) <
      hullSixTwoFourP13AscFarConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 86 <
        hullSixTwoFourP13AscFarConstant ^ ((43 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourP13AscFarConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP13AscFar_laurent_gt
    {a b c e t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (ht : 0 < t) (hc1 : 1 ≤ c) :
    (25 : ℝ) / 2 < hullSixTwoFourP13AscFarLaurent a b c e t := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFourP13AscFarWeight
    (hullSixTwoFourP13AscFarTerm a b c e t)
    hullSixTwoFourP13AscFarWeight_pos
    (hullSixTwoFourP13AscFarTerm_nonneg
      ha.le hb.le hc.le he.le ht.le)
  rw [hullSixTwoFourP13AscFarWeight_sum,
    hullSixTwoFourP13AscFarTerm_product ha hb hc he ht] at hamgm
  have hc6 : (1 : ℝ) ≤ c ^ 6 := one_le_pow₀ hc1
  have hProductFloor : hullSixTwoFourP13AscFarConstant ≤
      hullSixTwoFourP13AscFarConstant * c ^ 6 := by
    have h := mul_le_mul_of_nonneg_left hc6
      (le_of_lt hullSixTwoFourP13AscFarConstant_pos)
    simpa using h
  have hRootFloor :
      hullSixTwoFourP13AscFarConstant ^ ((43 : ℝ)⁻¹) ≤
        (hullSixTwoFourP13AscFarConstant * c ^ 6) ^ ((43 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (le_of_lt hullSixTwoFourP13AscFarConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourP13AscFarTerm_sum a b c e t]
  exact hullSixTwoFourP13AscFar_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## The branch `e < d`, with `t = e - f` -/

noncomputable def hullSixTwoFourP13DescNearLaurent
    (a b c d f t : ℝ) : ℝ :=
  2 + a + f + b / a + c / a + d / a + 2 * f / b + t / b +
    a / (2 * f) + c / (2 * f) + b / d + b * c / (a * d) +
      f / t + a * b / (d * t) + b * c / (d * t)

noncomputable def hullSixTwoFourP13DescNearTerm
    (a b c d f t : ℝ) : Fin 15 → ℝ :=
  ![2, a, f, b / a, c / a, d / a, 2 * f / b, t / b,
    a / (2 * f), c / (2 * f), b / d, b * c / (a * d),
    f / t, a * b / (d * t), b * c / (d * t)]

def hullSixTwoFourP13DescNearWeight : Fin 15 → ℕ :=
  ![2, 4, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 1]

noncomputable def hullSixTwoFourP13DescNearConstant : ℝ :=
  1 / ((2 : ℝ) ^ 21 * 3 ^ 3)

theorem hullSixTwoFourP13DescNearWeight_pos
    (i : Fin 15) : 0 < hullSixTwoFourP13DescNearWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP13DescNearWeight]

theorem hullSixTwoFourP13DescNearWeight_sum :
    ∑ i, hullSixTwoFourP13DescNearWeight i = 26 := by
  norm_num [hullSixTwoFourP13DescNearWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourP13DescNearTerm_nonneg
    {a b c d f t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (ht : 0 ≤ t)
    (i : Fin 15) :
    0 ≤ hullSixTwoFourP13DescNearTerm a b c d f t i := by
  fin_cases i <;>
    simp [hullSixTwoFourP13DescNearTerm] <;> positivity

theorem hullSixTwoFourP13DescNearTerm_sum
    (a b c d f t : ℝ) :
    ∑ i, hullSixTwoFourP13DescNearTerm a b c d f t i =
      hullSixTwoFourP13DescNearLaurent a b c d f t := by
  simp [hullSixTwoFourP13DescNearTerm,
    hullSixTwoFourP13DescNearLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFourP13DescNearTerm_product
    {a b c d f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hf : 0 < f) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourP13DescNearTerm a b c d f t i /
          (hullSixTwoFourP13DescNearWeight i : ℝ)) ^
            hullSixTwoFourP13DescNearWeight i) =
      hullSixTwoFourP13DescNearConstant * c ^ 4 * f := by
  simp [hullSixTwoFourP13DescNearTerm,
    hullSixTwoFourP13DescNearWeight, Fin.prod_univ_succ,
    hullSixTwoFourP13DescNearConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', hf.ne', ht.ne'] <;> ring

theorem hullSixTwoFourP13DescNearConstant_pos :
    0 < hullSixTwoFourP13DescNearConstant := by
  norm_num [hullSixTwoFourP13DescNearConstant]

theorem hullSixTwoFourP13DescNear_root_gap :
    (25 : ℝ) / 2 <
      26 * hullSixTwoFourP13DescNearConstant ^ ((26 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 52) ^ 26 < hullSixTwoFourP13DescNearConstant := by
    norm_num [hullSixTwoFourP13DescNearConstant]
  have hpowRpow :
      ((25 : ℝ) / 52) ^ (26 : ℝ) <
        hullSixTwoFourP13DescNearConstant := by
    change ((25 : ℝ) / 52) ^ ((26 : ℕ) : ℝ) <
      hullSixTwoFourP13DescNearConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 52 <
        hullSixTwoFourP13DescNearConstant ^ ((26 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourP13DescNearConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP13DescNear_laurent_gt
    {a b c d f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hf : 0 < f) (ht : 0 < t)
    (hc1 : 1 ≤ c) (hf1 : 1 ≤ f) :
    (25 : ℝ) / 2 < hullSixTwoFourP13DescNearLaurent a b c d f t := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFourP13DescNearWeight
    (hullSixTwoFourP13DescNearTerm a b c d f t)
    hullSixTwoFourP13DescNearWeight_pos
    (hullSixTwoFourP13DescNearTerm_nonneg
      ha.le hb.le hc.le hd.le hf.le ht.le)
  rw [hullSixTwoFourP13DescNearWeight_sum,
    hullSixTwoFourP13DescNearTerm_product ha hb hc hd hf ht] at hamgm
  have hfactor : (1 : ℝ) ≤ c ^ 4 * f := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c ^ 4 * f :=
        mul_le_mul (one_le_pow₀ hc1) hf1 (by norm_num) (by positivity)
  have hProductFloor : hullSixTwoFourP13DescNearConstant ≤
      hullSixTwoFourP13DescNearConstant * c ^ 4 * f := by
    have h := mul_le_mul_of_nonneg_left hfactor
      (le_of_lt hullSixTwoFourP13DescNearConstant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixTwoFourP13DescNearConstant ^ ((26 : ℝ)⁻¹) ≤
        (hullSixTwoFourP13DescNearConstant * c ^ 4 * f) ^
          ((26 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (le_of_lt hullSixTwoFourP13DescNearConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourP13DescNearTerm_sum a b c d f t]
  exact hullSixTwoFourP13DescNear_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

noncomputable def hullSixTwoFourP13DescFarLaurent
    (a b c d f t : ℝ) : ℝ :=
  2 + a + f + b / a + c / a + d / a + 2 * f / b + t / b +
    a / (2 * t) + c / (2 * t) + b / d + b * c / (a * d) +
      f / t + a * b / (d * t) + b * c / (d * t)

noncomputable def hullSixTwoFourP13DescFarTerm
    (a b c d f t : ℝ) : Fin 15 → ℝ :=
  ![2, a, f, b / a, c / a, d / a, 2 * f / b, t / b,
    a / (2 * t), c / (2 * t), b / d, b * c / (a * d),
    f / t, a * b / (d * t), b * c / (d * t)]

def hullSixTwoFourP13DescFarWeight : Fin 15 → ℕ :=
  ![6, 8, 3, 3, 1, 5, 3, 5, 1, 1, 2, 1, 1, 1, 1]

noncomputable def hullSixTwoFourP13DescFarConstant : ℝ :=
  1 / ((2 : ℝ) ^ 25 * 3 ^ 15 * 5 ^ 10)

theorem hullSixTwoFourP13DescFarWeight_pos
    (i : Fin 15) : 0 < hullSixTwoFourP13DescFarWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP13DescFarWeight]

theorem hullSixTwoFourP13DescFarWeight_sum :
    ∑ i, hullSixTwoFourP13DescFarWeight i = 42 := by
  norm_num [hullSixTwoFourP13DescFarWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourP13DescFarTerm_nonneg
    {a b c d f t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (ht : 0 ≤ t)
    (i : Fin 15) :
    0 ≤ hullSixTwoFourP13DescFarTerm a b c d f t i := by
  fin_cases i <;>
    simp [hullSixTwoFourP13DescFarTerm] <;> positivity

theorem hullSixTwoFourP13DescFarTerm_sum
    (a b c d f t : ℝ) :
    ∑ i, hullSixTwoFourP13DescFarTerm a b c d f t i =
      hullSixTwoFourP13DescFarLaurent a b c d f t := by
  simp [hullSixTwoFourP13DescFarTerm,
    hullSixTwoFourP13DescFarLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFourP13DescFarTerm_product
    {a b c d f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hf : 0 < f) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourP13DescFarTerm a b c d f t i /
          (hullSixTwoFourP13DescFarWeight i : ℝ)) ^
            hullSixTwoFourP13DescFarWeight i) =
      hullSixTwoFourP13DescFarConstant * c ^ 4 * f ^ 7 := by
  simp [hullSixTwoFourP13DescFarTerm,
    hullSixTwoFourP13DescFarWeight, Fin.prod_univ_succ,
    hullSixTwoFourP13DescFarConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', hf.ne', ht.ne'] <;> ring

theorem hullSixTwoFourP13DescFarConstant_pos :
    0 < hullSixTwoFourP13DescFarConstant := by
  norm_num [hullSixTwoFourP13DescFarConstant]

theorem hullSixTwoFourP13DescFar_root_gap :
    (25 : ℝ) / 2 <
      42 * hullSixTwoFourP13DescFarConstant ^ ((42 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 84) ^ 42 < hullSixTwoFourP13DescFarConstant := by
    norm_num [hullSixTwoFourP13DescFarConstant]
  have hpowRpow :
      ((25 : ℝ) / 84) ^ (42 : ℝ) <
        hullSixTwoFourP13DescFarConstant := by
    change ((25 : ℝ) / 84) ^ ((42 : ℕ) : ℝ) <
      hullSixTwoFourP13DescFarConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 84 <
        hullSixTwoFourP13DescFarConstant ^ ((42 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourP13DescFarConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP13DescFar_laurent_gt
    {a b c d f t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hf : 0 < f) (ht : 0 < t)
    (hc1 : 1 ≤ c) (hf1 : 1 ≤ f) :
    (25 : ℝ) / 2 < hullSixTwoFourP13DescFarLaurent a b c d f t := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFourP13DescFarWeight
    (hullSixTwoFourP13DescFarTerm a b c d f t)
    hullSixTwoFourP13DescFarWeight_pos
    (hullSixTwoFourP13DescFarTerm_nonneg
      ha.le hb.le hc.le hd.le hf.le ht.le)
  rw [hullSixTwoFourP13DescFarWeight_sum,
    hullSixTwoFourP13DescFarTerm_product ha hb hc hd hf ht] at hamgm
  have hfactor : (1 : ℝ) ≤ c ^ 4 * f ^ 7 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c ^ 4 * f ^ 7 :=
        mul_le_mul (one_le_pow₀ hc1) (one_le_pow₀ hf1)
          (by norm_num) (by positivity)
  have hProductFloor : hullSixTwoFourP13DescFarConstant ≤
      hullSixTwoFourP13DescFarConstant * c ^ 4 * f ^ 7 := by
    have h := mul_le_mul_of_nonneg_left hfactor
      (le_of_lt hullSixTwoFourP13DescFarConstant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixTwoFourP13DescFarConstant ^ ((42 : ℝ)⁻¹) ≤
        (hullSixTwoFourP13DescFarConstant * c ^ 4 * f ^ 7) ^
          ((42 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (le_of_lt hullSixTwoFourP13DescFarConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourP13DescFarTerm_sum a b c d f t]
  exact hullSixTwoFourP13DescFar_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## The frontier scalar theorem -/

/-- Scalar closure for the partial `p = (1,3)` `X` frontier. -/
theorem hullSixTwoFour_p13MaximalQ_scalar
    {a b c d e f A C E0 E1 E2 F X00 X01 X11 X12 X13 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hE01 : 1 ≤ E0) (hE11 : 1 ≤ E1) (hE21 : 1 ≤ E2)
    (hCIdentity : a * C = c * A + b * X00)
    (hE0TopIdentity : a * E0 = d * X00 - c * X01)
    (hE0BottomIdentity : b * E0 = d * C - c * X11)
    (hE1BottomIdentity : b * E1 = e * X11 - d * X12)
    (hE2BottomIdentity : b * E2 = f * X12 - e * X13)
    (hX00 : 1 ≤ X00) (hX01 : X01 ≤ -1)
    (hX12 : 1 ≤ X12) (hX13 : X13 ≤ -1)
    (hF : a + f + 1 ≤ F)
    (hEar0 : d ≤ (d - c) * E1 - (e - d) * E0)
    (hEar1 : e ≤ (e - f) * E1 + (e - d) * E2) :
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

  have hdX00 : d ≤ d * X00 := by
    simpa using mul_le_mul_of_nonneg_left hX00 hd.le
  have hcX01 : c * X01 ≤ -c := by
    simpa using mul_le_mul_of_nonneg_left hX01 hc.le
  have hE0Top : d * X00 + c ≤ a * E0 := by
    nlinarith [hE0TopIdentity, hdX00, hcX01]
  have hE0TopScaled : b * (d * X00 + c) ≤ b * (a * E0) :=
    mul_le_mul_of_nonneg_left hE0Top hb.le
  have hKey : a * c * X11 + b * c ≤ c * d * A := by
    have hE0Scaled : a * (b * E0) = a * (d * C - c * X11) :=
      congrArg (fun x : ℝ ↦ a * x) hE0BottomIdentity
    have hCScaled : d * (a * C) = d * (c * A + b * X00) :=
      congrArg (fun x : ℝ ↦ d * x) hCIdentity
    nlinarith [hE0TopScaled, hE0Scaled, hCScaled]
  have hdA : a * X11 + b ≤ d * A := by
    have hscaled : c * (a * X11 + b) ≤ c * (d * A) := by
      nlinarith [hKey]
    exact le_of_mul_le_mul_left hscaled hc

  have hdX12 : d ≤ d * X12 := by
    simpa using mul_le_mul_of_nonneg_left hX12 hd.le
  have hE1Chord : b * E1 + d ≤ e * X11 := by
    nlinarith [hE1BottomIdentity, hdX12]
  have hAKey : a * b * E1 + a * d + b * e ≤ d * e * A := by
    calc
      a * b * E1 + a * d + b * e = a * (b * E1 + d) + b * e := by ring
      _ ≤ a * (e * X11) + b * e := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hE1Chord ha.le) le_rfl
      _ = e * (a * X11 + b) := by ring
      _ ≤ e * (d * A) := mul_le_mul_of_nonneg_left hdA he.le
      _ = d * e * A := by ring
  have hALower :
      a / e + b / d + a * b * E1 / (d * e) ≤ A := by
    have hdiv :
        (a * b * E1 + a * d + b * e) / (d * e) ≤ A :=
      (div_le_iff₀ (mul_pos hd he)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hAKey)
    calc
      a / e + b / d + a * b * E1 / (d * e) =
          (a * b * E1 + a * d + b * e) / (d * e) := by
        field_simp [hd.ne', he.ne'] <;> ring
      _ ≤ A := hdiv

  have hbX00 : b ≤ b * X00 := by
    simpa using mul_le_mul_of_nonneg_left hX00 hb.le
  have hCTransition : c * A + b ≤ a * C := by
    nlinarith [hCIdentity, hbX00]
  have hCDiv : (c * A + b) / a ≤ C :=
    (div_le_iff₀ ha).2 (by simpa [mul_comm] using hCTransition)
  have hAMul : c / a *
      (a / e + b / d + a * b * E1 / (d * e)) ≤ c / a * A :=
    mul_le_mul_of_nonneg_left hALower (by positivity)
  have hCLower :
      b / a + c / e + b * c / (a * d) +
          b * c * E1 / (d * e) ≤ C := by
    have hleftShape :
        b / a + c / e + b * c / (a * d) +
            b * c * E1 / (d * e) =
          b / a + c / a *
            (a / e + b / d + a * b * E1 / (d * e)) := by
      field_simp [ha.ne', hd.ne', he.ne'] <;> ring
    rw [hleftShape]
    calc
      b / a + c / a *
            (a / e + b / d + a * b * E1 / (d * e))
          ≤ b / a + c / a * A := add_le_add le_rfl hAMul
      _ = (c * A + b) / a := by
        field_simp [ha.ne'] <;> ring
      _ ≤ C := hCDiv

  have hE0Lower : (c + d) / a ≤ E0 := by
    apply (div_le_iff₀ ha).2
    nlinarith [hE0Top, hdX00]
  have hfX12 : f ≤ f * X12 := by
    simpa using mul_le_mul_of_nonneg_left hX12 hf.le
  have heX13 : e * X13 ≤ -e := by
    simpa using mul_le_mul_of_nonneg_left hX13 he.le
  have hE2Transition : e + f ≤ b * E2 := by
    nlinarith [hE2BottomIdentity, hfX12, heX13]
  have hE2Lower : (e + f) / b ≤ E2 :=
    (div_le_iff₀ hb).2 (by simpa [mul_comm] using hE2Transition)

  have hRaw :
      1 + a + f + (b + c + d) / a + (e + f) / b +
          a / e + b / d + c / e + b * c / (a * d) +
          (1 + b * (a + c) / (d * e)) * E1 ≤
        A + C + E0 + E1 + E2 + F := by
    have hshape :
        E1 + a * b * E1 / (d * e) + b * c * E1 / (d * e) =
          (1 + b * (a + c) / (d * e)) * E1 := by
      field_simp [hd.ne', he.ne'] <;> ring
    rw [← hshape]
    rw [show (b + c + d) / a = b / a + (c + d) / a by ring]
    nlinarith [hALower, hCLower, hE0Lower, hE2Lower, hF]

  by_cases hde : d ≤ e
  · let t : ℝ := d - c
    have hsecond : 0 ≤ (e - d) * E0 :=
      mul_nonneg (sub_nonneg.mpr hde) hE00
    have hEarReduced : d ≤ (d - c) * E1 := by
      nlinarith [hEar0, hsecond]
    have ht : 0 < t := by
      dsimp [t]
      by_contra hnot
      have hdc : d - c ≤ 0 := le_of_not_gt hnot
      have hmul : (d - c) * E1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hdc hE10
      nlinarith
    have hE1Lower : d / t ≤ E1 :=
      (div_le_iff₀ ht).2 (by simpa [t, mul_comm] using hEarReduced)
    have hcoef : 0 ≤ 1 + b * (a + c) / (d * e) := by positivity
    have hE1Term :
        (1 + b * (a + c) / (d * e)) * (d / t) ≤
          (1 + b * (a + c) / (d * e)) * E1 :=
      mul_le_mul_of_nonneg_left hE1Lower hcoef
    have hfDiv : 1 / b ≤ f / b :=
      (div_le_div_iff_of_pos_right hb).2 hf1
    have hAscRaw :
        2 + a + 1 / b + (b + c + d) / a + e / b +
            a / e + b / d + c / e + b * c / (a * d) +
            (1 + b * (a + c) / (d * e)) * (d / t) ≤
          A + C + E0 + E1 + E2 + F := by
      calc
        _ ≤ 1 + a + f + (b + c + d) / a + (e + f) / b +
              a / e + b / d + c / e + b * c / (a * d) +
              (1 + b * (a + c) / (d * e)) * E1 := by
          rw [show (e + f) / b = e / b + f / b by ring]
          linarith [hE1Term, hf1, hfDiv]
        _ ≤ _ := hRaw
    have hAscShape :
        2 + a + 1 / b + (b + c + d) / a + e / b +
            a / e + b / d + c / e + b * c / (a * d) +
            (1 + b * (a + c) / (d * e)) * (d / t) =
          3 + a + 1 / b + b / a + 2 * c / a + t / a + e / b +
            a / e + b / d + c / e + b * c / (a * d) + c / t +
            a * b / (e * t) + b * c / (e * t) := by
      have hdt : d = t + c := by
        dsimp [t]
        ring
      rw [hdt]
      field_simp [ha.ne', hb.ne', he.ne', ht.ne',
        (add_pos ht hc).ne'] <;> ring
    rw [hAscShape] at hAscRaw
    by_cases htc : t ≤ c
    · have hdUpper : d ≤ 2 * c := by
        dsimp [t] at htc
        linarith
      have hBD : b / (2 * c) ≤ b / d := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) hc) hd).2
        have hmul := mul_le_mul_of_nonneg_left hdUpper hb.le
        nlinarith
      have hBCD : b / (2 * a) ≤ b * c / (a * d) := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) ha)
          (mul_pos ha hd)).2
        have hmul := mul_le_mul_of_nonneg_left hdUpper
          (mul_nonneg ha.le hb.le)
        nlinarith
      have hLaurentLower :
          hullSixTwoFourP13AscNearLaurent a b c e t ≤
            A + C + E0 + E1 + E2 + F := by
        dsimp [hullSixTwoFourP13AscNearLaurent]
        have hThreeB : 3 * b / (2 * a) = b / a + b / (2 * a) := by
          field_simp [ha.ne'] <;> ring
        rw [hThreeB]
        linarith [hAscRaw, hBD, hBCD]
      exact (hullSixTwoFourP13AscNear_laurent_gt ha hb hc he ht).trans_le
        hLaurentLower
    · have hct : c ≤ t := le_of_lt (lt_of_not_ge htc)
      have hdUpper : d ≤ 2 * t := by
        dsimp [t] at hct ⊢
        linarith
      have hBD : b / (2 * t) ≤ b / d := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) ht) hd).2
        have hmul := mul_le_mul_of_nonneg_left hdUpper hb.le
        nlinarith
      have hBCD : b * c / (2 * a * t) ≤ b * c / (a * d) := by
        apply (div_le_div_iff₀
          (mul_pos (mul_pos (by norm_num) ha) ht)
          (mul_pos ha hd)).2
        have hmul := mul_le_mul_of_nonneg_left hdUpper
          (mul_nonneg (mul_nonneg ha.le hb.le) hc.le)
        nlinarith
      have hLaurentLower :
          hullSixTwoFourP13AscFarLaurent a b c e t ≤
            A + C + E0 + E1 + E2 + F := by
        dsimp [hullSixTwoFourP13AscFarLaurent]
        nlinarith [hAscRaw, hBD, hBCD]
      exact (hullSixTwoFourP13AscFar_laurent_gt
        ha hb hc he ht hc1).trans_le hLaurentLower
  · have hed : e < d := lt_of_not_ge hde
    let t : ℝ := e - f
    have hsecond : (e - d) * E2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_lt hed)) hE20
    have hEarReduced : e ≤ (e - f) * E1 := by
      nlinarith [hEar1, hsecond]
    have ht : 0 < t := by
      dsimp [t]
      by_contra hnot
      have hef : e - f ≤ 0 := le_of_not_gt hnot
      have hmul : (e - f) * E1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hef hE10
      nlinarith
    have hE1Lower : e / t ≤ E1 :=
      (div_le_iff₀ ht).2 (by simpa [t, mul_comm] using hEarReduced)
    have hcoef : 0 ≤ 1 + b * (a + c) / (d * e) := by positivity
    have hE1Term :
        (1 + b * (a + c) / (d * e)) * (e / t) ≤
          (1 + b * (a + c) / (d * e)) * E1 :=
      mul_le_mul_of_nonneg_left hE1Lower hcoef
    have hDescRaw :
        1 + a + f + (b + c + d) / a + (e + f) / b +
            a / e + b / d + c / e + b * c / (a * d) +
            (1 + b * (a + c) / (d * e)) * (e / t) ≤
          A + C + E0 + E1 + E2 + F := by
      nlinarith [hRaw, hE1Term]
    have hDescShape :
        1 + a + f + (b + c + d) / a + (e + f) / b +
            a / e + b / d + c / e + b * c / (a * d) +
            (1 + b * (a + c) / (d * e)) * (e / t) =
          2 + a + f + b / a + c / a + d / a + 2 * f / b + t / b +
            a / e + b / d + c / e + b * c / (a * d) + f / t +
            a * b / (d * t) + b * c / (d * t) := by
      have het : e = t + f := by
        dsimp [t]
        ring
      have hBcd :
          (b + c + d) / a = b / a + c / a + d / a := by
        ring
      have hEf :
          (e + f) / b = 2 * f / b + t / b := by
        rw [het]
        ring
      have hEt : e / t = 1 + f / t := by
        rw [het, add_div, div_self ht.ne']
      have hMixed :
          b * (a + c) / (d * e) * (e / t) =
            a * b / (d * t) + b * c / (d * t) := by
        field_simp [hd.ne', he.ne', ht.ne'] <;> ring
      have hLast :
          (1 + b * (a + c) / (d * e)) * (e / t) =
            1 + f / t + a * b / (d * t) + b * c / (d * t) := by
        calc
          _ = e / t + b * (a + c) / (d * e) * (e / t) := by ring
          _ = (1 + f / t) +
                (a * b / (d * t) + b * c / (d * t)) := by
            rw [hMixed, hEt]
          _ = _ := by ring
      rw [hBcd, hEf, hLast]
      ring
    rw [hDescShape] at hDescRaw
    by_cases htf : t ≤ f
    · have heUpper : e ≤ 2 * f := by
        dsimp [t] at htf
        linarith
      have hAE : a / (2 * f) ≤ a / e := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) hf) he).2
        have hmul := mul_le_mul_of_nonneg_left heUpper ha.le
        nlinarith
      have hCE : c / (2 * f) ≤ c / e := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) hf) he).2
        have hmul := mul_le_mul_of_nonneg_left heUpper hc.le
        nlinarith
      have hLaurentLower :
          hullSixTwoFourP13DescNearLaurent a b c d f t ≤
            A + C + E0 + E1 + E2 + F := by
        dsimp [hullSixTwoFourP13DescNearLaurent]
        nlinarith [hDescRaw, hAE, hCE]
      exact (hullSixTwoFourP13DescNear_laurent_gt
        ha hb hc hd hf ht hc1 hf1).trans_le hLaurentLower
    · have hft : f ≤ t := le_of_lt (lt_of_not_ge htf)
      have heUpper : e ≤ 2 * t := by
        dsimp [t] at hft ⊢
        linarith
      have hAE : a / (2 * t) ≤ a / e := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) ht) he).2
        have hmul := mul_le_mul_of_nonneg_left heUpper ha.le
        nlinarith
      have hCE : c / (2 * t) ≤ c / e := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) ht) he).2
        have hmul := mul_le_mul_of_nonneg_left heUpper hc.le
        nlinarith
      have hLaurentLower :
          hullSixTwoFourP13DescFarLaurent a b c d f t ≤
            A + C + E0 + E1 + E2 + F := by
        dsimp [hullSixTwoFourP13DescFarLaurent]
        nlinarith [hDescRaw, hAE, hCE]
      exact (hullSixTwoFourP13DescFar_laurent_gt
        ha hb hc hd hf ht hc1 hf1).trans_le hLaurentLower

end Heilbronn8.Survivors.Join
