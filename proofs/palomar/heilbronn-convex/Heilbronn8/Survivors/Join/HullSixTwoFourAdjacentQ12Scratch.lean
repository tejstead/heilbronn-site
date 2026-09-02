import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scratch scalar certificate for the adjacent `q = 12` two-plus-four chamber

This source-only module records three small Laurent AM--GM certificates and a
single raw scalar wrapper.  It deliberately contains no geometric adapter.
The three branches are `d ≤ e`, `e < d ∧ c ≤ e`, and
`e < d ∧ e < c`; their AM--GM masses are respectively 29, 42, and 21.

The raw wrapper retains the two shared-cell variables `J` and `K`.  Their exact
identities are essential: the packet obtained by discarding them has a boundary
point with total area exactly `25 / 2`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

/-! ## The branch `d ≤ e`: a 29-copy certificate -/

noncomputable def hullSixTwoFour_q12_leLaurent
    (a b c t : ℝ) : ℝ :=
  a + 3 * c / 2 + a / c + b / c + t / 2 + c / a +
    t / (2 * a) + c ^ 2 / (2 * b) + c * t / (2 * b) +
      c / b + 3 * t / (2 * b) + c / (2 * t)

noncomputable def hullSixTwoFour_q12_leTerm
    (a b c t : ℝ) : Fin 12 → ℝ :=
  ![a, 3 * c / 2, a / c, b / c, t / 2, c / a,
    t / (2 * a), c ^ 2 / (2 * b), c * t / (2 * b),
    c / b, 3 * t / (2 * b), c / (2 * t)]

def hullSixTwoFour_q12_leWeight : Fin 12 → ℕ :=
  ![3, 4, 3, 5, 1, 3, 1, 1, 1, 2, 1, 4]

noncomputable def hullSixTwoFour_q12_leConstant : ℝ :=
  1 / (2 ^ 31 * 3 ^ 4 * 5 ^ 5)

theorem hullSixTwoFour_q12_leWeight_pos
    (i : Fin 12) : 0 < hullSixTwoFour_q12_leWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_q12_leWeight]

theorem hullSixTwoFour_q12_leWeight_sum :
    ∑ i, hullSixTwoFour_q12_leWeight i = 29 := by
  norm_num [hullSixTwoFour_q12_leWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_q12_leTerm_nonneg
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin 12) :
    0 ≤ hullSixTwoFour_q12_leTerm a b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFour_q12_leTerm] <;>
    positivity

theorem hullSixTwoFour_q12_leTerm_sum
    (a b c t : ℝ) :
    ∑ i, hullSixTwoFour_q12_leTerm a b c t i =
      hullSixTwoFour_q12_leLaurent a b c t := by
  simp [hullSixTwoFour_q12_leTerm, hullSixTwoFour_q12_leLaurent,
    Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFour_q12_leTerm_product
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFour_q12_leTerm a b c t i /
          (hullSixTwoFour_q12_leWeight i : ℝ)) ^
            hullSixTwoFour_q12_leWeight i) =
      hullSixTwoFour_q12_leConstant * a ^ 2 * c ^ 8 := by
  simp [hullSixTwoFour_q12_leTerm, hullSixTwoFour_q12_leWeight,
    Fin.prod_univ_succ, hullSixTwoFour_q12_leConstant]
  field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFour_q12_leConstant_pos :
    0 < hullSixTwoFour_q12_leConstant := by
  norm_num [hullSixTwoFour_q12_leConstant]

theorem hullSixTwoFour_q12_le_integer_gap :
    (9 : ℕ) ^ 29 * 2 ^ 31 * 3 ^ 4 * 5 ^ 5 < 29 ^ 29 := by
  norm_num

theorem hullSixTwoFour_q12_le_root_gap :
    (9 : ℝ) <
      29 * hullSixTwoFour_q12_leConstant ^ ((29 : ℝ)⁻¹) := by
  have hpow :
      ((9 : ℝ) / 29) ^ 29 < hullSixTwoFour_q12_leConstant := by
    norm_num [hullSixTwoFour_q12_leConstant]
  have hpowRpow :
      ((9 : ℝ) / 29) ^ (29 : ℝ) <
        hullSixTwoFour_q12_leConstant := by
    change ((9 : ℝ) / 29) ^ ((29 : ℕ) : ℝ) <
      hullSixTwoFour_q12_leConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (9 : ℝ) / 29 <
        hullSixTwoFour_q12_leConstant ^ ((29 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_q12_leConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_q12_le_laurent_gt
    {a b c t : ℝ} (ha1 : 1 ≤ a) (hb : 0 < b)
    (hc1 : 1 ≤ c) (ht : 0 < t) :
    (9 : ℝ) < hullSixTwoFour_q12_leLaurent a b c t := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_q12_leWeight
    (hullSixTwoFour_q12_leTerm a b c t)
    hullSixTwoFour_q12_leWeight_pos
    (hullSixTwoFour_q12_leTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFour_q12_leWeight_sum,
    hullSixTwoFour_q12_leTerm_product ha hb hc ht] at hamgm
  have hResidual : (1 : ℝ) ≤ a ^ 2 * c ^ 8 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ a ^ 2 * c ^ 8 :=
        mul_le_mul (one_le_pow₀ ha1) (one_le_pow₀ hc1)
          (by norm_num) (by positivity)
  have hProductFloor :
      hullSixTwoFour_q12_leConstant ≤
        hullSixTwoFour_q12_leConstant * a ^ 2 * c ^ 8 := by
    have h := mul_le_mul_of_nonneg_left hResidual
      (le_of_lt hullSixTwoFour_q12_leConstant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixTwoFour_q12_leConstant ^ ((29 : ℝ)⁻¹) ≤
        (hullSixTwoFour_q12_leConstant * a ^ 2 * c ^ 8) ^
          ((29 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixTwoFour_q12_leConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFour_q12_leTerm_sum a b c t]
  exact hullSixTwoFour_q12_le_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## The branch `e < d` and `c ≤ e`: a 42-copy certificate -/

noncomputable def hullSixTwoFour_q12_downLaurent
    (a b c t : ℝ) : ℝ :=
  a + c + a / c + b / c + t / 2 + c / (2 * a) +
    1 / (2 * a) + t / (2 * a) + c * t / (2 * b) +
      3 / (2 * b) + 3 * t / (2 * b) + 1 / (2 * t)

noncomputable def hullSixTwoFour_q12_downTerm
    (a b c t : ℝ) : Fin 12 → ℝ :=
  ![a, c, a / c, b / c, t / 2, c / (2 * a),
    1 / (2 * a), t / (2 * a), c * t / (2 * b),
    3 / (2 * b), 3 * t / (2 * b), 1 / (2 * t)]

def hullSixTwoFour_q12_downWeight : Fin 12 → ℕ :=
  ![5, 7, 4, 7, 1, 3, 2, 1, 1, 4, 2, 5]

noncomputable def hullSixTwoFour_q12_downConstant : ℝ :=
  27 / (2 ^ 39 * 5 ^ 10 * 7 ^ 14)

theorem hullSixTwoFour_q12_downWeight_pos
    (i : Fin 12) : 0 < hullSixTwoFour_q12_downWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_q12_downWeight]

theorem hullSixTwoFour_q12_downWeight_sum :
    ∑ i, hullSixTwoFour_q12_downWeight i = 42 := by
  norm_num [hullSixTwoFour_q12_downWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_q12_downTerm_nonneg
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin 12) :
    0 ≤ hullSixTwoFour_q12_downTerm a b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFour_q12_downTerm] <;>
    positivity

theorem hullSixTwoFour_q12_downTerm_sum
    (a b c t : ℝ) :
    ∑ i, hullSixTwoFour_q12_downTerm a b c t i =
      hullSixTwoFour_q12_downLaurent a b c t := by
  simp [hullSixTwoFour_q12_downTerm, hullSixTwoFour_q12_downLaurent,
    Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFour_q12_downTerm_product
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFour_q12_downTerm a b c t i /
          (hullSixTwoFour_q12_downWeight i : ℝ)) ^
            hullSixTwoFour_q12_downWeight i) =
      hullSixTwoFour_q12_downConstant * a ^ 3 := by
  simp [hullSixTwoFour_q12_downTerm, hullSixTwoFour_q12_downWeight,
    Fin.prod_univ_succ, hullSixTwoFour_q12_downConstant]
  field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFour_q12_downConstant_pos :
    0 < hullSixTwoFour_q12_downConstant := by
  norm_num [hullSixTwoFour_q12_downConstant]

theorem hullSixTwoFour_q12_down_integer_gap :
    (17 : ℕ) ^ 42 * 2 ^ 39 * 5 ^ 10 * 7 ^ 14 <
      27 * 84 ^ 42 := by
  norm_num

theorem hullSixTwoFour_q12_down_root_gap :
    (17 : ℝ) / 2 <
      42 * hullSixTwoFour_q12_downConstant ^ ((42 : ℝ)⁻¹) := by
  have hpow :
      ((17 : ℝ) / 84) ^ 42 < hullSixTwoFour_q12_downConstant := by
    norm_num [hullSixTwoFour_q12_downConstant]
  have hpowRpow :
      ((17 : ℝ) / 84) ^ (42 : ℝ) <
        hullSixTwoFour_q12_downConstant := by
    change ((17 : ℝ) / 84) ^ ((42 : ℕ) : ℝ) <
      hullSixTwoFour_q12_downConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (17 : ℝ) / 84 <
        hullSixTwoFour_q12_downConstant ^ ((42 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_q12_downConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_q12_down_laurent_gt
    {a b c t : ℝ} (ha1 : 1 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (17 : ℝ) / 2 < hullSixTwoFour_q12_downLaurent a b c t := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_q12_downWeight
    (hullSixTwoFour_q12_downTerm a b c t)
    hullSixTwoFour_q12_downWeight_pos
    (hullSixTwoFour_q12_downTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFour_q12_downWeight_sum,
    hullSixTwoFour_q12_downTerm_product ha hb hc ht] at hamgm
  have hProductFloor :
      hullSixTwoFour_q12_downConstant ≤
        hullSixTwoFour_q12_downConstant * a ^ 3 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ ha1 : (1 : ℝ) ≤ a ^ 3)
      (le_of_lt hullSixTwoFour_q12_downConstant_pos)
    simpa using h
  have hRootFloor :
      hullSixTwoFour_q12_downConstant ^ ((42 : ℝ)⁻¹) ≤
        (hullSixTwoFour_q12_downConstant * a ^ 3) ^ ((42 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixTwoFour_q12_downConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFour_q12_downTerm_sum a b c t]
  exact hullSixTwoFour_q12_down_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## The branch `e < d` and `e < c`: a 21-copy certificate -/

noncomputable def hullSixTwoFour_q12_riseLaurent
    (a b c t : ℝ) : ℝ :=
  a + 3 * c / 10 + a / c + b / c + c / a + 1 / a +
    t / a + 3 / (5 * b) + 3 * t / (5 * b) +
      7 / (10 * t) + 7 * t / 10

noncomputable def hullSixTwoFour_q12_riseTerm
    (a b c t : ℝ) : Fin 11 → ℝ :=
  ![a, 3 * c / 10, a / c, b / c, c / a, 1 / a,
    t / a, 3 / (5 * b), 3 * t / (5 * b),
    7 / (10 * t), 7 * t / 10]

def hullSixTwoFour_q12_riseWeight : Fin 11 → ℕ :=
  ![4, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1]

noncomputable def hullSixTwoFour_q12_riseConstant : ℝ :=
  2401 / 1105920000000

theorem hullSixTwoFour_q12_riseWeight_pos
    (i : Fin 11) : 0 < hullSixTwoFour_q12_riseWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_q12_riseWeight]

theorem hullSixTwoFour_q12_riseWeight_sum :
    ∑ i, hullSixTwoFour_q12_riseWeight i = 21 := by
  norm_num [hullSixTwoFour_q12_riseWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_q12_riseTerm_nonneg
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin 11) :
    0 ≤ hullSixTwoFour_q12_riseTerm a b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFour_q12_riseTerm] <;>
    positivity

theorem hullSixTwoFour_q12_riseTerm_sum
    (a b c t : ℝ) :
    ∑ i, hullSixTwoFour_q12_riseTerm a b c t i =
      hullSixTwoFour_q12_riseLaurent a b c t := by
  simp [hullSixTwoFour_q12_riseTerm, hullSixTwoFour_q12_riseLaurent,
    Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFour_q12_riseTerm_product
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFour_q12_riseTerm a b c t i /
          (hullSixTwoFour_q12_riseWeight i : ℝ)) ^
            hullSixTwoFour_q12_riseWeight i) =
      hullSixTwoFour_q12_riseConstant := by
  simp [hullSixTwoFour_q12_riseTerm, hullSixTwoFour_q12_riseWeight,
    Fin.prod_univ_succ, hullSixTwoFour_q12_riseConstant]
  field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFour_q12_riseConstant_pos :
    0 < hullSixTwoFour_q12_riseConstant := by
  norm_num [hullSixTwoFour_q12_riseConstant]

theorem hullSixTwoFour_q12_rise_integer_gap :
    (81 : ℕ) ^ 21 * 1105920000000 <
      2401 * 210 ^ 21 := by
  norm_num

theorem hullSixTwoFour_q12_rise_root_gap :
    (81 : ℝ) / 10 <
      21 * hullSixTwoFour_q12_riseConstant ^ ((21 : ℝ)⁻¹) := by
  have hpow :
      ((27 : ℝ) / 70) ^ 21 < hullSixTwoFour_q12_riseConstant := by
    norm_num [hullSixTwoFour_q12_riseConstant]
  have hpowRpow :
      ((27 : ℝ) / 70) ^ (21 : ℝ) <
        hullSixTwoFour_q12_riseConstant := by
    change ((27 : ℝ) / 70) ^ ((21 : ℕ) : ℝ) <
      hullSixTwoFour_q12_riseConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (27 : ℝ) / 70 <
        hullSixTwoFour_q12_riseConstant ^ ((21 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_q12_riseConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_q12_rise_laurent_gt
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (81 : ℝ) / 10 < hullSixTwoFour_q12_riseLaurent a b c t := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_q12_riseWeight
    (hullSixTwoFour_q12_riseTerm a b c t)
    hullSixTwoFour_q12_riseWeight_pos
    (hullSixTwoFour_q12_riseTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFour_q12_riseWeight_sum,
    hullSixTwoFour_q12_riseTerm_product ha hb hc ht] at hamgm
  rw [← hullSixTwoFour_q12_riseTerm_sum a b c t]
  exact hullSixTwoFour_q12_rise_root_gap.trans_le hamgm

/-! ## Raw adjacent-q12 scalar packet -/

/--
Raw q12 closure in normalized height/fan variables.  `J` and `K` are the two
shared bottom-cell determinants; the two displayed identities are the coupling
that is lost in the false independent-transition relaxation.
-/
theorem hullSixTwoFour_q12_scalar
    {a b c d e f A C x y z Fp J K : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A) (hC1 : 1 ≤ C)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hFp1 : 1 ≤ Fp) (hJ1 : 1 ≤ J) (hK1 : 1 ≤ K)
    (hAtransition : a + b ≤ c * A)
    (hxtransition : c + d ≤ a * x)
    (hJidentity : b * x + c * J = d * (b + c + C))
    (hKidentity : d * K = b * y - e * J)
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hy0 : 0 ≤ y := le_trans zero_le_one hy1
  have hz0 : 0 ≤ z := le_trans zero_le_one hz1
  have hJ0 : 0 ≤ J := le_trans zero_le_one hJ1
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have hALower : (a + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAtransition)
  have hxLower : (c + d) / a ≤ x := by
    exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hxtransition)
  have hXYidentity :
      b * (x + y) = d * (b + c + C + K) + (e - c) * J := by
    nlinarith [hJidentity, hKidentity]

  by_cases hde : d ≤ e
  · have hq : 0 ≤ e - d := sub_nonneg.mpr hde
    have hcd : c < d := by
      by_contra hnot
      have hdc : d - c ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hfirst : (d - c) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hdc hy0
      have hsecond : 0 ≤ (e - d) * x := mul_nonneg hq hx0
      nlinarith
    let t : ℝ := d - c
    have ht : 0 < t := by
      dsimp [t]
      exact sub_pos.mpr hcd
    have hEarYmul : d ≤ t * y := by
      dsimp [t]
      nlinarith [mul_nonneg hq hx0]
    have hEarY : d / t ≤ y :=
      (div_le_iff₀ ht).2 (by simpa [mul_comm] using hEarYmul)
    have hxHalf : c / a + t / (2 * a) ≤ x / 2 := by
      have hshape : c / a + t / (2 * a) = (c + d) / (2 * a) := by
        dsimp [t]
        field_simp [ha.ne'] <;> ring
      rw [hshape]
      have hscaled : (c + d) / (2 * a) = ((c + d) / a) / 2 := by
        field_simp [ha.ne'] <;> ring
      rw [hscaled]
      linarith
    have hyHalf : (1 : ℝ) / 2 + c / (2 * t) ≤ y / 2 := by
      have hshape : (1 : ℝ) / 2 + c / (2 * t) = (d / t) / 2 := by
        rw [div_div, mul_comm t 2]
        have h2t : (2 : ℝ) * t ≠ 0 :=
          mul_ne_zero (by norm_num) ht.ne'
        apply (eq_div_iff h2t).2
        rw [add_mul, div_mul_cancel₀ c h2t]
        dsimp [t]
        ring
      rw [hshape]
      linarith
    have hec : t ≤ e - c := by
      dsimp [t]
      linarith
    have hKextra : 0 ≤ d * (K - 1) :=
      mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hK1)
    have hJextra : 0 ≤ (e - c) * (J - 1) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hJ1)
    have hBXY :
        d * (b + c + C + 1) + t ≤ b * (x + y) := by
      rw [hXYidentity]
      nlinarith
    have hCextra : 0 ≤ (2 * b + d) * (C - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hC1)
    have hSharedNum :
        2 * b + b * d + c * d + 2 * c + 3 * t ≤
          2 * b * C + b * (x + y) := by
      dsimp [t] at hBXY ⊢
      nlinarith
    have hShared :
        1 + d / 2 + c * d / (2 * b) + (2 * c + 3 * t) / (2 * b) ≤
          C + (x + y) / 2 := by
      calc
        1 + d / 2 + c * d / (2 * b) + (2 * c + 3 * t) / (2 * b) =
            (2 * b + b * d + c * d + 2 * c + 3 * t) / (2 * b) := by
              field_simp [hb.ne'] <;> ring
        _ ≤ (2 * b * C + b * (x + y)) / (2 * b) :=
          div_le_div_of_nonneg_right hSharedNum (by positivity)
        _ = C + (x + y) / 2 := by
          field_simp [hb.ne'] <;> ring
    have hLower :
        (7 : ℝ) / 2 + hullSixTwoFour_q12_leLaurent a b c t ≤
          A + C + x + y + z + Fp + a + c := by
      have hdecomp :
          (7 : ℝ) / 2 + hullSixTwoFour_q12_leLaurent a b c t =
            2 + a + c + (a / c + b / c) +
              (c / a + t / (2 * a)) +
              ((1 : ℝ) / 2 + c / (2 * t)) +
              (1 + d / 2 + c * d / (2 * b) +
                (2 * c + 3 * t) / (2 * b)) := by
        dsimp [hullSixTwoFour_q12_leLaurent, t]
        field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring
      rw [hdecomp]
      have hASplit : a / c + b / c ≤ A := by
        simpa [add_div] using hALower
      linarith
    have hLaurent := hullSixTwoFour_q12_le_laurent_gt ha1 hb hc1 ht
    exact (by linarith : (25 : ℝ) / 2 <
      (7 : ℝ) / 2 + hullSixTwoFour_q12_leLaurent a b c t).trans_le hLower

  · have hed : e < d := lt_of_not_ge hde
    have hfd : f < e := by
      by_contra hnot
      have hef : e ≤ f := le_of_not_gt hnot
      have hfirst : (e - d) * z < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr hed) (lt_of_lt_of_le zero_lt_one hz1)
      have hsecond : 0 ≤ (f - e) * y :=
        mul_nonneg (sub_nonneg.mpr hef) hy0
      nlinarith
    let k : ℝ := e - f
    let t : ℝ := e - 1
    have hk : 0 < k := by
      dsimp [k]
      exact sub_pos.mpr hfd
    have ht : 0 < t := by
      dsimp [t]
      linarith
    have hkt : k ≤ t := by
      dsimp [k, t]
      linarith
    have hEarYmul : d ≤ k * y := by
      dsimp [k]
      have hdz : 0 ≤ (d - e) * (z - 1) :=
        mul_nonneg (sub_nonneg.mpr (le_of_lt hed))
          (sub_nonneg.mpr hz1)
      nlinarith
    have hty : d ≤ t * y := by
      have hextra : 0 ≤ (t - k) * y :=
        mul_nonneg (sub_nonneg.mpr hkt) hy0
      nlinarith
    have hEarY : e / t < y := by
      apply (div_lt_iff₀ ht).2
      nlinarith
    have hxE : (c + e) / a < x := by
      apply lt_of_lt_of_le _ hxLower
      apply (div_lt_div_iff_of_pos_right ha).2
      linarith
    by_cases hce : c ≤ e
    · have hec0 : 0 ≤ e - c := sub_nonneg.mpr hce
      have hKextra : 0 ≤ d * (K - 1) :=
        mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hK1)
      have hJextra : 0 ≤ (e - c) * (J - 1) :=
        mul_nonneg hec0 (sub_nonneg.mpr hJ1)
      have hCextra : 0 ≤ e * (C - 1) :=
        mul_nonneg (le_of_lt he) (sub_nonneg.mpr hC1)
      have hBXY :
          e * (b + c + 2) + (e - c) ≤ b * (x + y) := by
        rw [hXYidentity]
        have hcoeff : 0 ≤ b + c + C + 1 := by positivity
        have hdextra : 0 ≤ (d - e) * (b + c + C + 1) :=
          mul_nonneg (sub_nonneg.mpr (le_of_lt hed)) hcoeff
        nlinarith
      have hSharedNum :
          2 * b + b * e + c * t + 3 + 3 * t ≤
            2 * b * C + b * (x + y) := by
        dsimp [t] at hBXY ⊢
        have hbCextra : 0 ≤ 2 * b * (C - 1) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr hC1)
        nlinarith
      have hShared :
          (3 : ℝ) / 2 + t / 2 + c * t / (2 * b) +
                3 / (2 * b) + 3 * t / (2 * b) ≤
            C + (x + y) / 2 := by
        calc
          (3 : ℝ) / 2 + t / 2 + c * t / (2 * b) +
                3 / (2 * b) + 3 * t / (2 * b) =
              (2 * b + b * e + c * t + 3 + 3 * t) / (2 * b) := by
                dsimp [t]
                field_simp [hb.ne'] <;> ring
          _ ≤ (2 * b * C + b * (x + y)) / (2 * b) :=
            div_le_div_of_nonneg_right hSharedNum (by positivity)
          _ = C + (x + y) / 2 := by
            field_simp [hb.ne'] <;> ring
      have hxHalf : c / (2 * a) + 1 / (2 * a) + t / (2 * a) < x / 2 := by
        have hshape :
            c / (2 * a) + 1 / (2 * a) + t / (2 * a) =
              ((c + e) / a) / 2 := by
          dsimp [t]
          field_simp [ha.ne'] <;> ring
        rw [hshape]
        linarith
      have hyHalf : (1 : ℝ) / 2 + 1 / (2 * t) < y / 2 := by
        have hshape : (1 : ℝ) / 2 + 1 / (2 * t) = (e / t) / 2 := by
          have h2t : (2 * t : ℝ) ≠ 0 :=
            mul_ne_zero (by norm_num) ht.ne'
          rw [div_div, mul_comm t 2]
          apply (eq_div_iff h2t).2
          calc
            ((1 : ℝ) / 2 + 1 / (2 * t)) * (2 * t) =
                (1 : ℝ) / 2 * (2 * t) + 1 := by
              rw [add_mul, div_mul_cancel₀ _ h2t]
            _ = e := by
              dsimp [t]
              ring
        rw [hshape]
        linarith
      have hLower :
          4 + hullSixTwoFour_q12_downLaurent a b c t <
            A + C + x + y + z + Fp + a + c := by
        have hdecomp :
            4 + hullSixTwoFour_q12_downLaurent a b c t =
              2 + a + c + (a / c + b / c) +
                (c / (2 * a) + 1 / (2 * a) + t / (2 * a)) +
                ((1 : ℝ) / 2 + 1 / (2 * t)) +
                ((3 : ℝ) / 2 + t / 2 + c * t / (2 * b) +
                  3 / (2 * b) + 3 * t / (2 * b)) := by
          dsimp [hullSixTwoFour_q12_downLaurent]
          ring
        rw [hdecomp]
        have hASplit : a / c + b / c ≤ A := by
          simpa [add_div] using hALower
        linarith
      have hLaurent := hullSixTwoFour_q12_down_laurent_gt ha1 hb hc ht
      linarith

    · have hec : e < c := lt_of_not_ge hce
      have hBYidentity : b * y = d * K + e * J := by
        nlinarith [hKidentity]
      have hYBmul : d + e ≤ b * y := by
        rw [hBYidentity]
        have hdK : d ≤ d * K := by
          have := mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hK1)
          nlinarith
        have heJ : e ≤ e * J := by
          have := mul_nonneg (le_of_lt he) (sub_nonneg.mpr hJ1)
          nlinarith
        nlinarith
      have hYB : 2 * e / b < y := by
        apply (div_lt_iff₀ hb).2
        nlinarith
      have hYconvex :
          (3 : ℝ) / 10 * (2 * e / b) + 7 / 10 * (e / t) < y := by
        nlinarith [hYB, hEarY]
      have hCSplit : 3 * c / 10 + 7 * e / 10 < c := by
        linarith
      have hLower :
          (22 : ℝ) / 5 + hullSixTwoFour_q12_riseLaurent a b c t <
            A + C + x + y + z + Fp + a + c := by
        have hdecomp :
            (22 : ℝ) / 5 + hullSixTwoFour_q12_riseLaurent a b c t =
              3 + a + (3 * c / 10 + 7 * e / 10) +
                (a / c + b / c) + (c + e) / a +
                ((3 : ℝ) / 10 * (2 * e / b) + 7 / 10 * (e / t)) := by
          have het : e = t + 1 := by
            dsimp [t]
            ring
          have hA :
              c / a + 1 / a + t / a = (c + e) / a := by
            rw [het]
            ring
          have hB :
              3 / (5 * b) + 3 * t / (5 * b) =
                (3 : ℝ) / 10 * (2 * e / b) := by
            rw [← div_div, ← div_div, ← add_div, ← mul_div_assoc, het]
            ring
          have hT :
              (7 : ℝ) / (10 * t) = 7 / 10 * (1 / t) := by
            rw [← div_div]
            simp only [div_eq_mul_inv, one_mul]
          have hEt : e / t = 1 + 1 / t := by
            rw [het, add_div, div_self ht.ne']
          have hScalar :
              (22 : ℝ) / 5 + 7 / (10 * t) + 7 * t / 10 =
                3 + 7 * e / 10 + 7 / 10 * (e / t) := by
            rw [hT, hEt, het]
            ring
          unfold hullSixTwoFour_q12_riseLaurent
          linear_combination hA + hB + hScalar
        rw [hdecomp]
        have hASplit : a / c + b / c ≤ A := by
          simpa [add_div] using hALower
        linarith
      have hLaurent := hullSixTwoFour_q12_rise_laurent_gt ha hb hc ht
      linarith

end Heilbronn8.Survivors.Join
