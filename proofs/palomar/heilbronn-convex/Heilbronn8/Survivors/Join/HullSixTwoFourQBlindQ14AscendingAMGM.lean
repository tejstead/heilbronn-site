import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Ascending lower-height closure for the q-blind `q = 14` chamber

This file records the AM--GM audit for `c < d <= e` in the end-open q-blind
chamber.  The original total-fan draft missed the factor `f / e` in the
`E1` coefficient.  Consequently the standalone `f = 1` Laurent certificate
below is mathematically true but is **not** reachable from the corrected raw
geometry; it is retained only so that the failed route stays documented.  The
`f = e` certificate remains valid.  When `e < f`, the second lower-ear
inequality supplies `f / (e - d)` and the corrected rising scalar theorem
still closes because lowering `f` to `e` restores the old coefficient.

The geometric adapter is intentionally not imported here.  Its only input is
one of the two scalar lower bounds displayed in the public theorems below.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## Audited but unreachable old `f = 1` Laurent sum -/

noncomputable def hullSixTwoFourQ14AscendingLeftLaurent
    (b c t : ℝ) : ℝ :=
  3 + c + t + 2 / c + b / c + 2 * c / b +
    t / b + 1 / (b * c) + c / t + 1 / t

noncomputable def hullSixTwoFourQ14AscendingLeftTerm
    (b c t : ℝ) : Fin 10 → ℝ :=
  ![3, c, t, 2 / c, b / c, 2 * c / b,
    t / b, 1 / (b * c), c / t, 1 / t]

def hullSixTwoFourQ14AscendingLeftWeight : Fin 10 → ℕ :=
  ![6, 4, 3, 3, 4, 2, 1, 1, 2, 2]

noncomputable def hullSixTwoFourQ14AscendingLeftConstant : ℝ :=
  1 / 6115295232

theorem hullSixTwoFourQ14AscendingLeft_weight_pos
    (i : Fin 10) : 0 < hullSixTwoFourQ14AscendingLeftWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ14AscendingLeftWeight]

theorem hullSixTwoFourQ14AscendingLeft_weight_sum :
    ∑ i, hullSixTwoFourQ14AscendingLeftWeight i = 28 := by
  norm_num [hullSixTwoFourQ14AscendingLeftWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ14AscendingLeft_term_nonneg
    {b c t : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (i : Fin 10) :
    0 ≤ hullSixTwoFourQ14AscendingLeftTerm b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ14AscendingLeftTerm] <;>
    positivity

theorem hullSixTwoFourQ14AscendingLeft_term_sum
    (b c t : ℝ) :
    ∑ i, hullSixTwoFourQ14AscendingLeftTerm b c t i =
      hullSixTwoFourQ14AscendingLeftLaurent b c t := by
  simp [hullSixTwoFourQ14AscendingLeftTerm,
    hullSixTwoFourQ14AscendingLeftLaurent, Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFourQ14AscendingLeft_term_product
    {b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourQ14AscendingLeftTerm b c t i /
          (hullSixTwoFourQ14AscendingLeftWeight i : ℝ)) ^
            hullSixTwoFourQ14AscendingLeftWeight i) =
      hullSixTwoFourQ14AscendingLeftConstant := by
  simp [hullSixTwoFourQ14AscendingLeftTerm,
    hullSixTwoFourQ14AscendingLeftWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ14AscendingLeftConstant]
  field_simp [hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFourQ14AscendingLeft_constant_pos :
    0 < hullSixTwoFourQ14AscendingLeftConstant := by
  norm_num [hullSixTwoFourQ14AscendingLeftConstant]

theorem hullSixTwoFourQ14AscendingLeft_integer_gap :
    6115295232 * (25 : ℕ) ^ 28 < 56 ^ 28 := by
  norm_num

theorem hullSixTwoFourQ14AscendingLeft_root_gap :
    (25 : ℝ) / 2 <
      28 * hullSixTwoFourQ14AscendingLeftConstant ^ ((28 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 56) ^ 28 <
        hullSixTwoFourQ14AscendingLeftConstant := by
    norm_num [hullSixTwoFourQ14AscendingLeftConstant]
  have hpowRpow :
      ((25 : ℝ) / 56) ^ (28 : ℝ) <
        hullSixTwoFourQ14AscendingLeftConstant := by
    change ((25 : ℝ) / 56) ^ ((28 : ℕ) : ℝ) <
      hullSixTwoFourQ14AscendingLeftConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 56 <
        hullSixTwoFourQ14AscendingLeftConstant ^ ((28 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ14AscendingLeft_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourQ14AscendingLeft_laurent_gt
    {b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    (25 : ℝ) / 2 <
      hullSixTwoFourQ14AscendingLeftLaurent b c t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ14AscendingLeftWeight
    (hullSixTwoFourQ14AscendingLeftTerm b c t)
    hullSixTwoFourQ14AscendingLeft_weight_pos
    (hullSixTwoFourQ14AscendingLeft_term_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFourQ14AscendingLeft_weight_sum,
    hullSixTwoFourQ14AscendingLeft_term_product hb hc ht] at hamgm
  rw [← hullSixTwoFourQ14AscendingLeft_term_sum b c t]
  exact hullSixTwoFourQ14AscendingLeft_root_gap.trans_le hamgm

/-! ## The `f = e` endpoint -/

noncomputable def hullSixTwoFourQ14AscendingEqualLaurent
    (b c t : ℝ) : ℝ :=
  9 / 7 + 1 / c + b / c + 2 * c / b + t / b + 2 / b +
    t / (b * c) + c / t + 1 / t + t / c +
    (2 / 3) * b + (2 / 3) * c + (2 / 3) * t

noncomputable def hullSixTwoFourQ14AscendingEqualTerm
    (b c t : ℝ) : Fin 13 → ℝ :=
  ![9 / 7, 1 / c, b / c, 2 * c / b, t / b, 2 / b,
    t / (b * c), c / t, 1 / t, t / c,
    (2 / 3) * b, (2 / 3) * c, (2 / 3) * t]

def hullSixTwoFourQ14AscendingEqualWeight : Fin 13 → ℕ :=
  ![3, 2, 5, 3, 2, 2, 1, 4, 3, 2, 3, 3, 2]

noncomputable def hullSixTwoFourQ14AscendingEqualConstant : ℝ :=
  1 / 4429507590900000

theorem hullSixTwoFourQ14AscendingEqual_weight_pos
    (i : Fin 13) : 0 < hullSixTwoFourQ14AscendingEqualWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ14AscendingEqualWeight]

theorem hullSixTwoFourQ14AscendingEqual_weight_sum :
    ∑ i, hullSixTwoFourQ14AscendingEqualWeight i = 35 := by
  norm_num [hullSixTwoFourQ14AscendingEqualWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ14AscendingEqual_term_nonneg
    {b c t : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (i : Fin 13) :
    0 ≤ hullSixTwoFourQ14AscendingEqualTerm b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ14AscendingEqualTerm] <;>
    positivity

theorem hullSixTwoFourQ14AscendingEqual_term_sum
    (b c t : ℝ) :
    ∑ i, hullSixTwoFourQ14AscendingEqualTerm b c t i =
      hullSixTwoFourQ14AscendingEqualLaurent b c t := by
  simp [hullSixTwoFourQ14AscendingEqualTerm,
    hullSixTwoFourQ14AscendingEqualLaurent, Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFourQ14AscendingEqual_term_product
    {b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourQ14AscendingEqualTerm b c t i /
          (hullSixTwoFourQ14AscendingEqualWeight i : ℝ)) ^
            hullSixTwoFourQ14AscendingEqualWeight i) =
      hullSixTwoFourQ14AscendingEqualConstant := by
  simp [hullSixTwoFourQ14AscendingEqualTerm,
    hullSixTwoFourQ14AscendingEqualWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ14AscendingEqualConstant]
  field_simp [hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFourQ14AscendingEqual_constant_pos :
    0 < hullSixTwoFourQ14AscendingEqualConstant := by
  norm_num [hullSixTwoFourQ14AscendingEqualConstant]

theorem hullSixTwoFourQ14AscendingEqual_root_gap :
    (25 : ℝ) / 2 <
      35 * hullSixTwoFourQ14AscendingEqualConstant ^ ((35 : ℝ)⁻¹) := by
  have hpow :
      ((5 : ℝ) / 14) ^ 35 <
        hullSixTwoFourQ14AscendingEqualConstant := by
    norm_num [hullSixTwoFourQ14AscendingEqualConstant]
  have hpowRpow :
      ((5 : ℝ) / 14) ^ (35 : ℝ) <
        hullSixTwoFourQ14AscendingEqualConstant := by
    change ((5 : ℝ) / 14) ^ ((35 : ℕ) : ℝ) <
      hullSixTwoFourQ14AscendingEqualConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (5 : ℝ) / 14 <
        hullSixTwoFourQ14AscendingEqualConstant ^ ((35 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ14AscendingEqual_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourQ14AscendingEqual_laurent_gt
    {b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    (25 : ℝ) / 2 <
      hullSixTwoFourQ14AscendingEqualLaurent b c t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ14AscendingEqualWeight
    (hullSixTwoFourQ14AscendingEqualTerm b c t)
    hullSixTwoFourQ14AscendingEqual_weight_pos
    (hullSixTwoFourQ14AscendingEqual_term_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFourQ14AscendingEqual_weight_sum,
    hullSixTwoFourQ14AscendingEqual_term_product hb hc ht] at hamgm
  rw [← hullSixTwoFourQ14AscendingEqual_term_sum b c t]
  exact hullSixTwoFourQ14AscendingEqual_root_gap.trans_le hamgm

/-! ## The `e < f` branch -/

noncomputable def hullSixTwoFourQ14AscendingRisingLaurent
    (b c d u : ℝ) : ℝ :=
  1 / 16 + 1 / c + b / c + 2 * c / b + 2 / b +
    u / (b * d) + u / (b * c) + 1 / d + d / u + 1 / u +
    u / c + (7 / 8) * b + (7 / 8) * c + (7 / 8) * u

noncomputable def hullSixTwoFourQ14AscendingRisingTerm
    (b c d u : ℝ) : Fin 14 → ℝ :=
  ![1 / 16, 1 / c, b / c, 2 * c / b, 2 / b,
    u / (b * d), u / (b * c), 1 / d, d / u, 1 / u,
    u / c, (7 / 8) * b, (7 / 8) * c, (7 / 8) * u]

def hullSixTwoFourQ14AscendingRisingWeight : Fin 14 → ℕ :=
  ![1, 2, 3, 4, 2, 1, 1, 3, 4, 3, 2, 5, 4, 3]

noncomputable def hullSixTwoFourQ14AscendingRisingConstant : ℝ :=
  13841287201 / 30635487866488368188620800000

theorem hullSixTwoFourQ14AscendingRising_weight_pos
    (i : Fin 14) : 0 < hullSixTwoFourQ14AscendingRisingWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ14AscendingRisingWeight]

theorem hullSixTwoFourQ14AscendingRising_weight_sum :
    ∑ i, hullSixTwoFourQ14AscendingRisingWeight i = 38 := by
  norm_num [hullSixTwoFourQ14AscendingRisingWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ14AscendingRising_term_nonneg
    {b c d u : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hu : 0 ≤ u) (i : Fin 14) :
    0 ≤ hullSixTwoFourQ14AscendingRisingTerm b c d u i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ14AscendingRisingTerm] <;>
    positivity

theorem hullSixTwoFourQ14AscendingRising_term_sum
    (b c d u : ℝ) :
    ∑ i, hullSixTwoFourQ14AscendingRisingTerm b c d u i =
      hullSixTwoFourQ14AscendingRisingLaurent b c d u := by
  simp [hullSixTwoFourQ14AscendingRisingTerm,
    hullSixTwoFourQ14AscendingRisingLaurent, Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFourQ14AscendingRising_term_product
    {b c d u : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hu : 0 < u) :
    (∏ i,
        (hullSixTwoFourQ14AscendingRisingTerm b c d u i /
          (hullSixTwoFourQ14AscendingRisingWeight i : ℝ)) ^
            hullSixTwoFourQ14AscendingRisingWeight i) =
      hullSixTwoFourQ14AscendingRisingConstant := by
  simp [hullSixTwoFourQ14AscendingRisingTerm,
    hullSixTwoFourQ14AscendingRisingWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ14AscendingRisingConstant]
  field_simp [hb.ne', hc.ne', hd.ne', hu.ne'] <;> ring

theorem hullSixTwoFourQ14AscendingRising_constant_pos :
    0 < hullSixTwoFourQ14AscendingRisingConstant := by
  norm_num [hullSixTwoFourQ14AscendingRisingConstant]

theorem hullSixTwoFourQ14AscendingRising_root_gap :
    (25 : ℝ) / 2 <
      38 * hullSixTwoFourQ14AscendingRisingConstant ^ ((38 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 76) ^ 38 <
        hullSixTwoFourQ14AscendingRisingConstant := by
    norm_num [hullSixTwoFourQ14AscendingRisingConstant]
  have hpowRpow :
      ((25 : ℝ) / 76) ^ (38 : ℝ) <
        hullSixTwoFourQ14AscendingRisingConstant := by
    change ((25 : ℝ) / 76) ^ ((38 : ℕ) : ℝ) <
      hullSixTwoFourQ14AscendingRisingConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 76 <
        hullSixTwoFourQ14AscendingRisingConstant ^ ((38 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ14AscendingRising_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourQ14AscendingRising_laurent_gt
    {b c d u : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hu : 0 < u) :
    (25 : ℝ) / 2 <
      hullSixTwoFourQ14AscendingRisingLaurent b c d u := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ14AscendingRisingWeight
    (hullSixTwoFourQ14AscendingRisingTerm b c d u)
    hullSixTwoFourQ14AscendingRising_weight_pos
    (hullSixTwoFourQ14AscendingRising_term_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt hd) (le_of_lt hu))
  rw [hullSixTwoFourQ14AscendingRising_weight_sum,
    hullSixTwoFourQ14AscendingRising_term_product hb hc hd hu] at hamgm
  rw [← hullSixTwoFourQ14AscendingRising_term_sum b c d u]
  exact hullSixTwoFourQ14AscendingRising_root_gap.trans_le hamgm

/-! ## Scalar wrappers

The formerly proposed peak wrapper is retained below only as an audit record
inside a block comment.  It used the incorrect coefficient `1 + a / d` on
`E1`; the correct coefficient is `1 + a * f / (d * e)`.  With the corrected
coefficient its `f = 1` raw relaxation is false (for example
`a=f=1`, `b=43/20`, `c=5/4`, and `d=e=47/20` give
`27650127/2223100 < 25/2`).
-/

/- The exact affine-in-`f` closer when `c < d <= e` and `f <= e`. -/
/-
theorem hullSixTwoFourQ14AscendingPeak_scalar
    {a b c d e f H : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hcd : c < d) (hde : d ≤ e) (hfe : f ≤ e)
    (hcompact : max a b + e ≤ (9 : ℝ) / 2)
    (hLower :
      1 + (a + b) / c + (c + d) / b +
          a * f * (c + d) / (b * c * d) +
          (d + a) / (d - c) +
          (1 + e - f) * (1 + a / e) + f / c ≤ H) :
    (25 : ℝ) / 2 < H := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  let t : ℝ := d - c
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hdc0 : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcd)
  let kappa : ℝ :=
    a * (c + d) / (b * c * d) - (1 + a / e) + 1 / c
  have hRawOneIdentity :
      1 + (a + b) / c + (c + d) / b +
            a * f * (c + d) / (b * c * d) +
            (d + a) / (d - c) +
            (1 + e - f) * (1 + a / e) + f / c =
        (1 + (a + b) / c + (c + d) / b +
            a * (c + d) / (b * c * d) +
            (d + a) / (d - c) + e + a + 1 / c) +
          (f - 1) * kappa := by
    dsimp [kappa]
    field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hdc0] <;> ring
  have hRawEqualIdentity :
      1 + (a + b) / c + (c + d) / b +
            a * f * (c + d) / (b * c * d) +
            (d + a) / (d - c) +
            (1 + e - f) * (1 + a / e) + f / c =
        (2 + (a + b) / c + (c + d) / b +
            a * e * (c + d) / (b * c * d) +
            (d + a) / (d - c) + a / e + e / c) +
          (f - e) * kappa := by
    dsimp [kappa]
    field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hdc0] <;> ring
  by_cases hkappa : 0 ≤ kappa
  · have hAffine : 0 ≤ (f - 1) * kappa :=
      mul_nonneg (sub_nonneg.mpr hf1) hkappa
    have hRawOne :
        1 + (a + b) / c + (c + d) / b +
            a * (c + d) / (b * c * d) +
            (d + a) / (d - c) + e + a + 1 / c ≤ H := by
      rw [hRawOneIdentity] at hLower
      linarith
    have hMonotoneA :
        0 ≤ (a - 1) *
          (1 / c + (c + d) / (b * c * d) + 1 / (d - c) + 1) := by
      exact mul_nonneg (sub_nonneg.mpr ha1) (by positivity)
    have hMonotoneE : 0 ≤ e - d := sub_nonneg.mpr hde
    have hBaseLower :
        1 + (1 + b) / c + (c + d) / b +
            (c + d) / (b * c * d) +
            (d + 1) / (d - c) + d + 1 + 1 / c ≤ H := by
      have hIdentity :
          1 + (a + b) / c + (c + d) / b +
                a * (c + d) / (b * c * d) +
                (d + a) / (d - c) + e + a + 1 / c =
            1 + (1 + b) / c + (c + d) / b +
                (c + d) / (b * c * d) +
                (d + 1) / (d - c) + d + 1 + 1 / c +
              (a - 1) *
                (1 / c + (c + d) / (b * c * d) +
                  1 / (d - c) + 1) + (e - d) := by
        field_simp [ha.ne', hb.ne', hc.ne', hd.ne', hdc0] <;> ring
      rw [hIdentity] at hRawOne
      linarith
    have hBaseIdentity :
        1 + (1 + b) / c + (c + d) / b +
              (c + d) / (b * c * d) +
              (d + 1) / (d - c) + d + 1 + 1 / c =
          hullSixTwoFourQ14AscendingLeftLaurent b c t + 1 / (b * d) := by
      dsimp [t, hullSixTwoFourQ14AscendingLeftLaurent]
      field_simp [hb.ne', hc.ne', hd.ne', hdc0] <;> ring
    have hExtra : 0 < 1 / (b * d) := by positivity
    have hLaurent :=
      hullSixTwoFourQ14AscendingLeft_laurent_gt hb hc ht
    rw [hBaseIdentity] at hBaseLower
    nlinarith
  · have hkappaNeg : kappa < 0 := lt_of_not_ge hkappa
    have hAffine : 0 ≤ (f - e) * kappa :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfe)
        (le_of_lt hkappaNeg)
    have hRawEqual :
        2 + (a + b) / c + (c + d) / b +
            a * e * (c + d) / (b * c * d) +
            (d + a) / (d - c) + a / e + e / c ≤ H := by
      rw [hRawEqualIdentity] at hLower
      linarith
    have hMonotoneA :
        0 ≤ (a - 1) *
          (1 / c + e * (c + d) / (b * c * d) +
            1 / (d - c) + 1 / e) := by
      exact mul_nonneg (sub_nonneg.mpr ha1) (by positivity)
    have hAtOne :
        2 + (1 + b) / c + (c + d) / b +
            e * (c + d) / (b * c * d) +
            (d + 1) / (d - c) + 1 / e + e / c ≤ H := by
      have hIdentity :
          2 + (a + b) / c + (c + d) / b +
                a * e * (c + d) / (b * c * d) +
                (d + a) / (d - c) + a / e + e / c =
            2 + (1 + b) / c + (c + d) / b +
                e * (c + d) / (b * c * d) +
                (d + 1) / (d - c) + 1 / e + e / c +
              (a - 1) *
                (1 / c + e * (c + d) / (b * c * d) +
                  1 / (d - c) + 1 / e) := by
        field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hdc0] <;> ring
      rw [hIdentity] at hRawEqual
      linarith
    have hProductDrop :
        (c + d) / (b * c) ≤ e * (c + d) / (b * c * d) := by
      have hDiff :
          e * (c + d) / (b * c * d) - (c + d) / (b * c) =
            (e - d) * (c + d) / (b * c * d) := by
        field_simp [hb.ne', hc.ne', hd.ne'] <;> ring
      have hGapNonneg : 0 ≤ e - d := sub_nonneg.mpr hde
      have hNonneg :
          0 ≤ (e - d) * (c + d) / (b * c * d) := by
        positivity
      linarith
    have hPairDrop : d / c + 1 / d ≤ e / c + 1 / e := by
      have hDiff :
          e / c + 1 / e - (d / c + 1 / d) =
            (e - d) * (e * d - c) / (c * d * e) := by
        field_simp [hc.ne', hd.ne', he.ne'] <;> ring
      have hedMul : d ≤ e * d := by
        have := mul_le_mul_of_nonneg_right he1 (le_of_lt hd)
        simpa using this
      have hedMinus : 0 ≤ e * d - c := by nlinarith
      have hGapNonneg : 0 ≤ e - d := sub_nonneg.mpr hde
      have hNonneg :
          0 ≤ (e - d) * (e * d - c) / (c * d * e) := by
        positivity
      linarith
    have hAtD :
        2 + (1 + b) / c + (c + d) / b +
            (c + d) / (b * c) +
            (d + 1) / (d - c) + 1 / d + d / c ≤ H := by
      linarith
    have haMax : a ≤ max a b := le_max_left a b
    have hbMax : b ≤ max a b := le_max_right a b
    have hbdCompact : b + d ≤ (9 : ℝ) / 2 := by linarith
    have hdUpper : d ≤ (7 : ℝ) / 2 := by linarith
    have hInvD : (2 : ℝ) / 7 ≤ 1 / d := by
      have hDiff :
          1 / d - (2 : ℝ) / 7 = (7 - 2 * d) / (7 * d) := by
        field_simp [hd.ne'] <;> ring
      have hNumerator : 0 ≤ 7 - 2 * d := by nlinarith
      have hNonneg : 0 ≤ (7 - 2 * d) / (7 * d) := by positivity
      linarith
    have hGap : 0 ≤ (9 : ℝ) / 2 - (b + c + t) := by
      dsimp [t]
      linarith
    have hSupport : 0 ≤ (2 / 3 : ℝ) *
        ((9 : ℝ) / 2 - (b + c + t)) :=
      mul_nonneg (by norm_num) hGap
    have hAtDIdentity :
        2 + (1 + b) / c + (c + d) / b +
              (c + d) / (b * c) +
              (d + 1) / (d - c) + 1 / d + d / c =
          hullSixTwoFourQ14AscendingEqualLaurent b c t +
            (1 / d - 2 / 7) +
            (2 / 3) * ((9 : ℝ) / 2 - (b + c + t)) := by
      dsimp [t, hullSixTwoFourQ14AscendingEqualLaurent]
      field_simp [hb.ne', hc.ne', hd.ne', ht.ne'] <;> ring
    have hLaurent :=
      hullSixTwoFourQ14AscendingEqual_laurent_gt hb hc ht
    rw [hAtDIdentity] at hAtD
    nlinarith
-/

/-- The reciprocal-ear closer when `c < d < e < f`. -/
theorem hullSixTwoFourQ14AscendingRising_scalar
    {a b c d e f H : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hcd : c < d) (hde : d < e) (hef : e < f)
    (hcompact : max a b + f ≤ (9 : ℝ) / 2)
    (hLower :
      1 + (a + b) / c + (c + d) / b +
          a * f * (c + d) / (b * c * d) +
          (1 + a * f / (d * e)) +
          (1 + a / e) * (f / (e - d)) +
          f / c ≤ H) :
    (25 : ℝ) / 2 < H := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  let u : ℝ := e - d
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hed0 : e - d ≠ 0 := sub_ne_zero.mpr (ne_of_gt hde)
  have hMonotoneA :
      0 ≤ (a - 1) *
        (1 / c + f * (c + d) / (b * c * d) +
          f / (d * e) + f / (e * (e - d))) := by
    exact mul_nonneg (sub_nonneg.mpr ha1) (by positivity)
  have hAtOne :
      1 + (1 + b) / c + (c + d) / b +
          f * (c + d) / (b * c * d) +
          (1 + f / (d * e)) +
          (1 + 1 / e) * (f / (e - d)) +
          f / c ≤ H := by
    have hIdentity :
        1 + (a + b) / c + (c + d) / b +
              a * f * (c + d) / (b * c * d) +
              (1 + a * f / (d * e)) +
              (1 + a / e) * (f / (e - d)) +
              f / c =
          1 + (1 + b) / c + (c + d) / b +
              f * (c + d) / (b * c * d) +
              (1 + f / (d * e)) +
              (1 + 1 / e) * (f / (e - d)) +
              f / c +
            (a - 1) *
              (1 / c + f * (c + d) / (b * c * d) +
                f / (d * e) + f / (e * (e - d))) := by
      field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hed0] <;> ring
    rw [hIdentity] at hLower
    linarith
  have hFMonotone :
      0 ≤ (f - e) *
        ((c + d) / (b * c * d) + 1 / (d * e) +
          (1 + 1 / e) / (e - d) + 1 / c) := by
    exact mul_nonneg (sub_nonneg.mpr (le_of_lt hef)) (by positivity)
  have hAtE :
      2 + (1 + b) / c + (c + d) / b +
          e * (c + d) / (b * c * d) + 1 / d +
          (e + 1) / (e - d) + e / c ≤ H := by
    have hIdentity :
        1 + (1 + b) / c + (c + d) / b +
              f * (c + d) / (b * c * d) +
              (1 + f / (d * e)) +
              (1 + 1 / e) * (f / (e - d)) +
              f / c =
          2 + (1 + b) / c + (c + d) / b +
              e * (c + d) / (b * c * d) + 1 / d +
              (e + 1) / (e - d) + e / c +
            (f - e) *
              ((c + d) / (b * c * d) +
                1 / (d * e) +
                (1 + 1 / e) / (e - d) + 1 / c) := by
      field_simp [hb.ne', hc.ne', hd.ne', he.ne', hed0] <;> ring
    rw [hIdentity] at hAtOne
    linarith
  have hdc : c ≤ d := le_of_lt hcd
  have hRisingCore :
      4 + 1 / c + b / c + 2 * c / b + 2 / b +
          u / (b * d) + u / (b * c) + 1 / d + d / u +
          1 / u + u / c ≤ H := by
    have hdb : c / b ≤ d / b := by
      have hDiff : d / b - c / b = (d - c) / b := by ring
      have hNonneg : 0 ≤ (d - c) / b := by positivity
      linarith
    have hdbc : 1 / b ≤ d / (b * c) := by
      have hDiff : d / (b * c) - 1 / b = (d - c) / (b * c) := by
        field_simp [hb.ne', hc.ne'] <;> ring
      have hNonneg : 0 ≤ (d - c) / (b * c) := by positivity
      linarith
    have hdcRatio : 1 ≤ d / c := by
      exact (le_div_iff₀ hc).2 (by simpa using hdc)
    have hIdentity :
        2 + (1 + b) / c + (c + d) / b +
              e * (c + d) / (b * c * d) + 1 / d +
              (e + 1) / (e - d) + e / c =
          3 + 1 / c + b / c + c / b + d / b +
              1 / b + d / (b * c) + u / (b * d) +
              u / (b * c) + 1 / d + d / u + 1 / u +
              d / c + u / c := by
      dsimp [u]
      field_simp [hb.ne', hc.ne', hd.ne', he.ne', hed0] <;> ring
    rw [hIdentity] at hAtE
    have hGap :
        0 ≤ (d / b - c / b) + (d / (b * c) - 1 / b) +
          (d / c - 1) := by
      linarith [hdb, hdbc, hdcRatio]
    have hCoreSplit :
        3 + 1 / c + b / c + c / b + d / b + 1 / b +
              d / (b * c) + u / (b * d) + u / (b * c) +
              1 / d + d / u + 1 / u + d / c + u / c =
          (4 + 1 / c + b / c + 2 * c / b + 2 / b +
              u / (b * d) + u / (b * c) + 1 / d + d / u +
              1 / u + u / c) +
            ((d / b - c / b) + (d / (b * c) - 1 / b) +
              (d / c - 1)) := by
      ring
    rw [hCoreSplit] at hAtE
    linarith
  have hbMax : b ≤ max a b := le_max_right a b
  have hbeCompact : b + e ≤ (9 : ℝ) / 2 := by linarith
  have hbcGap : 0 ≤ (9 : ℝ) / 2 - (b + c + u) := by
    dsimp [u]
    linarith
  have hSupport :
      0 ≤ (7 / 8 : ℝ) * ((9 : ℝ) / 2 - (b + c + u)) :=
    mul_nonneg (by norm_num) hbcGap
  have hCoreIdentity :
      4 + 1 / c + b / c + 2 * c / b + 2 / b +
            u / (b * d) + u / (b * c) + 1 / d + d / u +
            1 / u + u / c =
        hullSixTwoFourQ14AscendingRisingLaurent b c d u +
          (7 / 8) * ((9 : ℝ) / 2 - (b + c + u)) := by
    dsimp [hullSixTwoFourQ14AscendingRisingLaurent]
    ring
  have hLaurent :=
    hullSixTwoFourQ14AscendingRising_laurent_gt hb hc hd hu
  rw [hCoreIdentity] at hRisingCore
  nlinarith

/-! ## Correct mixed-fan closure for every ascending q14 height order

The total-`F` route above is unnecessary in the q14 chamber.  Keeping the
upper bound on the first bottom `M` cell gives a short mixed-fan proof which
works for every `d <= e`, with no order assumption on `f` and no compactness
bound.  This also avoids the missing-`f/e` pitfall in the old total-`F`
coefficient completely.
-/

/-- The ten-term Laurent sum obtained by averaging the two exact bounds on
the first mixed fan edge with coefficients `1/4` and `3/4`. -/
noncomputable def hullSixTwoFourQ14AscendingMixedLaurent
    (a b c t : ℝ) : ℝ :=
  a + c + a / c + b / c + c / t + c / (2 * a) +
    t / (4 * a) + 3 * t / 4 + 3 * c / (2 * b) + 3 * t / (4 * b)

noncomputable def hullSixTwoFourQ14AscendingMixedTerm
    (a b c t : ℝ) : Fin 10 → ℝ :=
  ![a, c, a / c, b / c, c / t, c / (2 * a),
    t / (4 * a), 3 * t / 4, 3 * c / (2 * b), 3 * t / (4 * b)]

def hullSixTwoFourQ14AscendingMixedWeight : Fin 10 → ℕ :=
  ![4, 4, 4, 6, 4, 2, 1, 3, 4, 2]

noncomputable def hullSixTwoFourQ14AscendingMixedConstant : ℝ :=
  ((1 : ℝ) / 4) ^ 34

theorem hullSixTwoFourQ14AscendingMixed_weight_pos
    (i : Fin 10) : 0 < hullSixTwoFourQ14AscendingMixedWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ14AscendingMixedWeight]

theorem hullSixTwoFourQ14AscendingMixed_weight_sum :
    ∑ i, hullSixTwoFourQ14AscendingMixedWeight i = 34 := by
  norm_num [hullSixTwoFourQ14AscendingMixedWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ14AscendingMixed_term_nonneg
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin 10) :
    0 ≤ hullSixTwoFourQ14AscendingMixedTerm a b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ14AscendingMixedTerm] <;>
    positivity

theorem hullSixTwoFourQ14AscendingMixed_term_sum
    (a b c t : ℝ) :
    ∑ i, hullSixTwoFourQ14AscendingMixedTerm a b c t i =
      hullSixTwoFourQ14AscendingMixedLaurent a b c t := by
  simp [hullSixTwoFourQ14AscendingMixedTerm,
    hullSixTwoFourQ14AscendingMixedLaurent, Fin.sum_univ_succ] <;>
    ring

/-- The scaled product is `4^-34` times the residual height monomial. -/
theorem hullSixTwoFourQ14AscendingMixed_term_product
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourQ14AscendingMixedTerm a b c t i /
          (hullSixTwoFourQ14AscendingMixedWeight i : ℝ)) ^
            hullSixTwoFourQ14AscendingMixedWeight i) =
      hullSixTwoFourQ14AscendingMixedConstant *
        (a ^ 5 * c ^ 4 * t ^ 2) := by
  simp [hullSixTwoFourQ14AscendingMixedTerm,
    hullSixTwoFourQ14AscendingMixedWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ14AscendingMixedConstant]
  field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFourQ14AscendingMixed_constant_pos :
    0 < hullSixTwoFourQ14AscendingMixedConstant := by
  norm_num [hullSixTwoFourQ14AscendingMixedConstant]

/-- Strict AM--GM away from the unique residual equality locus. -/
theorem hullSixTwoFourQ14AscendingMixed_laurent_gt
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t)
    (hresidual : 1 < a ^ 5 * c ^ 4 * t ^ 2) :
    (17 : ℝ) / 2 < hullSixTwoFourQ14AscendingMixedLaurent a b c t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ14AscendingMixedWeight
    (hullSixTwoFourQ14AscendingMixedTerm a b c t)
    hullSixTwoFourQ14AscendingMixed_weight_pos
    (hullSixTwoFourQ14AscendingMixed_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFourQ14AscendingMixed_weight_sum,
    hullSixTwoFourQ14AscendingMixed_term_product ha hb hc ht] at hamgm
  have hProductStrict :
      ((1 : ℝ) / 4) ^ 34 <
        hullSixTwoFourQ14AscendingMixedConstant *
          (a ^ 5 * c ^ 4 * t ^ 2) := by
    have h := mul_lt_mul_of_pos_left hresidual
      hullSixTwoFourQ14AscendingMixed_constant_pos
    simpa [hullSixTwoFourQ14AscendingMixedConstant] using h
  have hProductStrictRpow :
      ((1 : ℝ) / 4) ^ (34 : ℝ) <
        hullSixTwoFourQ14AscendingMixedConstant *
          (a ^ 5 * c ^ 4 * t ^ 2) := by
    change ((1 : ℝ) / 4) ^ ((34 : ℕ) : ℝ) <
      hullSixTwoFourQ14AscendingMixedConstant *
        (a ^ 5 * c ^ 4 * t ^ 2)
    rw [Real.rpow_natCast]
    exact hProductStrict
  have hroot :
      (1 : ℝ) / 4 <
        (hullSixTwoFourQ14AscendingMixedConstant *
          (a ^ 5 * c ^ 4 * t ^ 2)) ^ ((34 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (by positivity) (by norm_num)]
    exact hProductStrictRpow
  rw [← hullSixTwoFourQ14AscendingMixed_term_sum a b c t]
  nlinarith

/--
Raw normalized closure for every q-blind `q = 14` branch with `d <= e`.

`x,y,z` are the first three primed lower fan edges.  `hYUpper` is the
compressed form of the exact first bottom-row recurrence together with
`J1 <= b+d-1` and `J2 >= 1`.  The two transitions on `x` must both be kept:
their `1/4 : 3/4` average is exactly the AM--GM certificate above.  The
terminal recurrence is used only at the unique AM--GM equality locus.
-/
theorem hullSixTwoFourAscendingMixed_scalar_of_exceptional
    {a b c d e f A C x y z Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hf1 : 1 ≤ f)
    (hcd : c < d) (hde : d ≤ e)
    (hC1 : 1 ≤ C) (hz1 : 1 ≤ z) (hFp1 : 1 ≤ Fp)
    (hAtransition : a + b ≤ c * A)
    (hTopTransition : c + d ≤ a * x)
    (hBottomTransition : c + d ≤ b * (x + c - d))
    (hYUpper : b * y ≤ e * (b + d - 1) - d)
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - f) * y - (d - e) * z)
    (hExceptional :
      a = 1 → c = 1 → d = 2 → e = 2 → y = 2 → f = 1 →
        (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hd : 0 < d := hc.trans hcd
  let t : ℝ := d - c
  let u : ℝ := e - d
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith

  have hALower : (a + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAtransition)
  have hxTop : (2 * c + t) / a ≤ x := by
    rw [div_le_iff₀ ha]
    dsimp [t]
    nlinarith
  have hxBottom : t + (2 * c + t) / b ≤ x := by
    have hdiv : (c + d) / b ≤ x + c - d :=
      (div_le_iff₀ hb).2 (by
        simpa [mul_comm] using hBottomTransition)
    have hid :
        t + (2 * c + t) / b = d - c + (c + d) / b := by
      dsimp [t]
      ring
    rw [hid]
    linarith
  have hxAverage :
      c / (2 * a) + t / (4 * a) + 3 * t / 4 +
          3 * c / (2 * b) + 3 * t / (4 * b) ≤ x := by
    have havg :
        (1 / 4 : ℝ) * ((2 * c + t) / a) +
            (3 / 4 : ℝ) * (t + (2 * c + t) / b) ≤ x := by
      nlinarith [hxTop, hxBottom]
    have hid :
        (1 / 4 : ℝ) * ((2 * c + t) / a) +
              (3 / 4 : ℝ) * (t + (2 * c + t) / b) =
          c / (2 * a) + t / (4 * a) + 3 * t / 4 +
            3 * c / (2 * b) + 3 * t / (4 * b) := by
      field_simp [ha.ne', hb.ne'] <;> ring
    rwa [hid] at havg

  have hEarRearranged : d + u * x ≤ t * y := by
    dsimp [t, u]
    nlinarith [hEar0]
  have hyBase : 1 + c / t ≤ y := by
    have hdLower : d ≤ t * y := by
      have hux0 : 0 ≤ u * x := by
        have hx : 0 < x := by
          have hcdPos : 0 < c + d := add_pos hc hd
          have hax : 0 < a * x := hcdPos.trans_le hTopTransition
          by_contra hnot
          have hx0 : x ≤ 0 := le_of_not_gt hnot
          have hax0 : a * x ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hx0
          linarith
        exact mul_nonneg hu (le_of_lt hx)
      nlinarith [hEarRearranged]
    have hdiv : d / t ≤ y := (div_le_iff₀ ht).2 (by
      simpa [mul_comm] using hdLower)
    have hid : d / t = 1 + c / t := by
      dsimp [t]
      field_simp [sub_ne_zero.mpr (ne_of_gt hcd)] <;> ring
    rwa [hid] at hdiv

  have hRaw :
      4 + hullSixTwoFourQ14AscendingMixedLaurent a b c t ≤
        A + C + x + y + z + Fp + a + c := by
    have hAsplit : a / c + b / c ≤ A := by
      have hid : (a + b) / c = a / c + b / c := by ring
      rwa [hid] at hALower
    dsimp [hullSixTwoFourQ14AscendingMixedLaurent]
    nlinarith [hAsplit, hxAverage, hyBase, hC1, hz1, hFp1]

  have ha5 : (1 : ℝ) ≤ a ^ 5 := one_le_pow₀ ha1
  have hc2 : (1 : ℝ) ≤ c ^ 2 := one_le_pow₀ hc1
  have hc4 : (1 : ℝ) ≤ c ^ 4 := one_le_pow₀ hc1

  by_cases htLt : t < 1
  · have hSlopeGap : 0 < (2 - t) * d :=
      mul_pos (by linarith) hd
    have hSlopeScaled : t * (b + d - 1) ≤ b * x := by
      nlinarith [hBottomTransition, hSlopeGap]
    have hUSlope : u * (t * (b + d - 1)) ≤ u * (b * x) :=
      mul_le_mul_of_nonneg_left hSlopeScaled hu
    have hEarScaled : b * (d + u * x) ≤ b * (t * y) :=
      mul_le_mul_of_nonneg_left hEarRearranged (le_of_lt hb)
    have hYScaled :
        t * (b * y) ≤ t * (e * (b + d - 1) - d) :=
      mul_le_mul_of_nonneg_left hYUpper (le_of_lt ht)
    have heExpand : e = d + u := by
      dsimp [u]
      ring
    have hCompatScaled : b * d ≤ t * (d * (b + d - 1) - d) := by
      rw [heExpand] at hYScaled
      nlinarith [hEarScaled, hYScaled, hUSlope]
    have hCompat : b ≤ t * (b + d - 2) := by
      have hmul : d * b ≤ d * (t * (b + d - 2)) := by
        nlinarith [hCompatScaled]
      exact le_of_mul_le_mul_left hmul hd
    have hOneMinus : 1 - t ≤ b * (1 - t) := by
      have := mul_le_mul_of_nonneg_right hb1 (by linarith : 0 ≤ 1 - t)
      simpa using this
    have hBonus : 0 < t * (1 - t) :=
      mul_pos ht (sub_pos.mpr htLt)
    have hdExpand : d = c + t := by
      dsimp [t]
      ring
    rw [hdExpand] at hCompat
    have hct : 1 < c * t := by
      nlinarith [hCompat, hOneMinus, hBonus]
    have hctSq : 1 < (c * t) ^ 2 := by
      nlinarith [sq_nonneg (c * t - 1)]
    have hprefix : (1 : ℝ) ≤ a ^ 5 * c ^ 2 := by
      simpa using mul_le_mul ha5 hc2 (by norm_num) (by positivity)
    have hscale :
        (c * t) ^ 2 ≤ (a ^ 5 * c ^ 2) * (c * t) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hprefix (sq_nonneg (c * t))
      simpa using this
    have hresidual : 1 < a ^ 5 * c ^ 4 * t ^ 2 := by
      have hid :
          (a ^ 5 * c ^ 2) * (c * t) ^ 2 = a ^ 5 * c ^ 4 * t ^ 2 := by
        ring
      rw [← hid]
      exact hctSq.trans_le hscale
    have hLaurent := hullSixTwoFourQ14AscendingMixed_laurent_gt
      ha hb hc ht hresidual
    linarith
  · have htGe : 1 ≤ t := le_of_not_gt htLt
    by_cases htEq : t = 1
    · by_cases haEq : a = 1
      · by_cases hcEq : c = 1
        · have hdEq : d = 2 := by
            dsimp [t] at htEq
            nlinarith
          have heExpand : e = 2 + u := by
            dsimp [u]
            nlinarith
          have hx3 : 3 ≤ x := by
            nlinarith [hTopTransition]
          have hux3 : 3 * u ≤ u * x :=
            by
              simpa [mul_comm] using
                mul_le_mul_of_nonneg_left hx3 hu
          have hyLowerExceptional : 2 + 3 * u ≤ y := by
            nlinarith [hEarRearranged, hux3]
          have hub : u ≤ b * u := by
            have := mul_le_mul_of_nonneg_right hb1 hu
            simpa using this
          have hbyUpper : b * y ≤ b * (2 + 2 * u) := by
            rw [hdEq, heExpand] at hYUpper
            nlinarith [hYUpper, hub]
          have hyUpperExceptional : y ≤ 2 + 2 * u :=
            by exact le_of_mul_le_mul_left hbyUpper hb
          have huEq : u = 0 := by
            nlinarith [hyLowerExceptional, hyUpperExceptional, hu]
          have heEq : e = 2 := by
            rw [heExpand, huEq]
            ring
          have hyEq : y = 2 := by
            rw [huEq] at hyLowerExceptional hyUpperExceptional
            nlinarith
          have hfEq : f = 1 := by
            rw [hdEq, heEq, hyEq] at hEar1
            nlinarith
          exact hExceptional haEq hcEq hdEq heEq hyEq hfEq
        · have hcGt : 1 < c := lt_of_le_of_ne hc1 (Ne.symm hcEq)
          have hc4Strict : 1 < c ^ 4 := by
            have hpoly :
                0 < (c - 1) * (c ^ 3 + c ^ 2 + c + 1) :=
              mul_pos (sub_pos.mpr hcGt) (by positivity)
            nlinarith [hpoly]
          have hscale : c ^ 4 ≤ a ^ 5 * c ^ 4 := by
            have := mul_le_mul_of_nonneg_right ha5 (by positivity : 0 ≤ c ^ 4)
            simpa [mul_comm] using this
          have hresidual : 1 < a ^ 5 * c ^ 4 * t ^ 2 := by
            rw [htEq]
            norm_num
            exact hc4Strict.trans_le hscale
          have hLaurent := hullSixTwoFourQ14AscendingMixed_laurent_gt
            ha hb hc ht hresidual
          linarith
      · have haGt : 1 < a := lt_of_le_of_ne ha1 (Ne.symm haEq)
        have ha5Strict : 1 < a ^ 5 := by
          have hpoly :
              0 < (a - 1) * (a ^ 4 + a ^ 3 + a ^ 2 + a + 1) :=
            mul_pos (sub_pos.mpr haGt) (by positivity)
          nlinarith [hpoly]
        have hscale : a ^ 5 ≤ a ^ 5 * c ^ 4 := by
          have := mul_le_mul_of_nonneg_left hc4 (by positivity : 0 ≤ a ^ 5)
          simpa using this
        have hresidual : 1 < a ^ 5 * c ^ 4 * t ^ 2 := by
          rw [htEq]
          norm_num
          exact ha5Strict.trans_le hscale
        have hLaurent := hullSixTwoFourQ14AscendingMixed_laurent_gt
          ha hb hc ht hresidual
        linarith
    · have htGt : 1 < t := lt_of_le_of_ne htGe (Ne.symm htEq)
      have ht2Strict : 1 < t ^ 2 := by
        nlinarith [sq_nonneg (t - 1)]
      have hprefix : (1 : ℝ) ≤ a ^ 5 * c ^ 4 := by
        simpa using mul_le_mul ha5 hc4 (by norm_num) (by positivity)
      have hscale : t ^ 2 ≤ (a ^ 5 * c ^ 4) * t ^ 2 := by
        have := mul_le_mul_of_nonneg_right hprefix (sq_nonneg t)
        simpa using this
      have hresidual : 1 < a ^ 5 * c ^ 4 * t ^ 2 := by
        exact ht2Strict.trans_le hscale
      have hLaurent := hullSixTwoFourQ14AscendingMixed_laurent_gt
        ha hb hc ht hresidual
      linarith

/--
Raw normalized closure for every q-blind `q = 14` branch with `d <= e`.

This preserves the original public API.  Its terminal transition supplies the
only exceptional equality-locus closure required by
`hullSixTwoFourAscendingMixed_scalar_of_exceptional`.
-/
theorem hullSixTwoFourQ14AscendingMixed_scalar
    {a b c d e f A C x y z Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hf1 : 1 ≤ f)
    (hcd : c < d) (hde : d ≤ e)
    (hC1 : 1 ≤ C) (hz1 : 1 ≤ z) (hFp1 : 1 ≤ Fp)
    (hAtransition : a + b ≤ c * A)
    (hTopTransition : c + d ≤ a * x)
    (hBottomTransition : c + d ≤ b * (x + c - d))
    (hYUpper : b * y ≤ e * (b + d - 1) - d)
    (hTerminal : a + b ≤ f * (A + a - b))
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - f) * y - (d - e) * z) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  refine hullSixTwoFourAscendingMixed_scalar_of_exceptional
    ha1 hb1 hc1 hf1 hcd hde hC1 hz1 hFp1
    hAtransition hTopTransition hBottomTransition hYUpper hEar0 hEar1 ?_
  intro haEq hcEq hdEq _heEq hyEq hfEq
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hALowerExceptional : 2 * b ≤ A := by
    rw [haEq, hfEq] at hTerminal
    nlinarith
  have hxLowerExceptional : 1 + 3 / b ≤ x := by
    rw [hcEq, hdEq] at hBottomTransition
    have hdiv : 3 / b ≤ x - 1 := (div_le_iff₀ hb).2 (by
      calc
        (3 : ℝ) = 1 + 2 := by norm_num
        _ ≤ b * (x + 1 - 2) := hBottomTransition
        _ = (x - 1) * b := by ring)
    linarith
  have hquad : 0 < 4 * b ^ 2 - 9 * b + 6 := by
    have hsquare : 0 ≤ (8 * b - 9) ^ 2 := sq_nonneg (8 * b - 9)
    nlinarith
  have hbStrict : (11 : ℝ) / 2 < 2 * b + 1 + 3 / b := by
    have hid :
        (2 * b + 1 + 3 / b) - (11 : ℝ) / 2 =
          (4 * b ^ 2 - 9 * b + 6) / (2 * b) := by
      field_simp [hb.ne'] <;> ring
    have hfrac : 0 < (4 * b ^ 2 - 9 * b + 6) / (2 * b) :=
      div_pos hquad (by positivity)
    nlinarith [hid, hfrac]
  rw [haEq, hcEq, hyEq]
  nlinarith [hALowerExceptional, hxLowerExceptional,
    hC1, hz1, hFp1, hbStrict]

end Heilbronn8
