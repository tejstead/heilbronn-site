import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the maximal-q `p = (1,2)` frontier

Four retained `X` transitions reduce the normalized hull area to two small
Laurent sums.  The lower-ear height order decides which sum occurs.  Both
orders are closed by exact weighted AM--GM certificates.

No `Q` cross-chord sign occurs in this file.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

/-! ## The `d <= e` Laurent certificate -/

noncomputable def hullSixTwoFour_p12HighLaurent
    (a b d : ℝ) : ℝ :=
  a + a / d + b / d + 1 / d + b / (a * d) +
    b / a + d / a + 1 / a + d / b

noncomputable def hullSixTwoFour_p12HighTerm
    (a b d : ℝ) : Fin 9 → ℝ :=
  ![a, a / d, b / d, 1 / d, b / (a * d),
    b / a, d / a, 1 / a, d / b]

def hullSixTwoFour_p12HighWeight : Fin 9 → ℕ :=
  ![3, 2, 1, 1, 1, 1, 2, 1, 3]

noncomputable def hullSixTwoFour_p12HighConstant : ℝ :=
  1 / 11664

theorem hullSixTwoFour_p12HighWeight_pos
    (i : Fin 9) : 0 < hullSixTwoFour_p12HighWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_p12HighWeight]

theorem hullSixTwoFour_p12HighWeight_sum :
    ∑ i, hullSixTwoFour_p12HighWeight i = 15 := by
  norm_num [hullSixTwoFour_p12HighWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_p12HighTerm_nonneg
    {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (i : Fin 9) :
    0 ≤ hullSixTwoFour_p12HighTerm a b d i := by
  fin_cases i <;> simp [hullSixTwoFour_p12HighTerm] <;> positivity

theorem hullSixTwoFour_p12HighTerm_sum
    (a b d : ℝ) :
    ∑ i, hullSixTwoFour_p12HighTerm a b d i =
      hullSixTwoFour_p12HighLaurent a b d := by
  simp [hullSixTwoFour_p12HighTerm,
    hullSixTwoFour_p12HighLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_p12HighTerm_product
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (∏ i,
        (hullSixTwoFour_p12HighTerm a b d i /
          (hullSixTwoFour_p12HighWeight i : ℝ)) ^
            hullSixTwoFour_p12HighWeight i) =
      hullSixTwoFour_p12HighConstant := by
  simp [hullSixTwoFour_p12HighTerm,
    hullSixTwoFour_p12HighWeight, Fin.prod_univ_succ,
    hullSixTwoFour_p12HighConstant]
  field_simp [ha.ne', hb.ne', hd.ne'] <;> ring

theorem hullSixTwoFour_p12HighConstant_pos :
    0 < hullSixTwoFour_p12HighConstant := by
  norm_num [hullSixTwoFour_p12HighConstant]

theorem hullSixTwoFour_p12High_integer_gap :
    (8 : ℕ) ^ 15 * 11664 < 15 ^ 15 := by
  norm_num

theorem hullSixTwoFour_p12High_root_gap :
    (8 : ℝ) <
      15 * hullSixTwoFour_p12HighConstant ^ ((15 : ℝ)⁻¹) := by
  have hpow : ((8 : ℝ) / 15) ^ 15 <
      hullSixTwoFour_p12HighConstant := by
    norm_num [hullSixTwoFour_p12HighConstant]
  have hpowRpow : ((8 : ℝ) / 15) ^ (15 : ℝ) <
      hullSixTwoFour_p12HighConstant := by
    change ((8 : ℝ) / 15) ^ ((15 : ℕ) : ℝ) <
      hullSixTwoFour_p12HighConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (8 : ℝ) / 15 <
      hullSixTwoFour_p12HighConstant ^ ((15 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_p12HighConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_p12High_laurent_gt
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (8 : ℝ) < hullSixTwoFour_p12HighLaurent a b d := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_p12HighWeight
    (hullSixTwoFour_p12HighTerm a b d)
    hullSixTwoFour_p12HighWeight_pos
    (hullSixTwoFour_p12HighTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hd))
  rw [hullSixTwoFour_p12HighWeight_sum,
    hullSixTwoFour_p12HighTerm_product ha hb hd,
    hullSixTwoFour_p12HighTerm_sum a b d] at hamgm
  exact hullSixTwoFour_p12High_root_gap.trans_le hamgm

/-! ## The `e < d` Laurent certificate -/

noncomputable def hullSixTwoFour_p12LowLaurent
    (a b d r : ℝ) : ℝ :=
  a + r + a / d + b / d + 1 / d + b / (a * d) +
    b / a + d / a + 1 / a + d / (2 * b) +
      1 / (2 * b) + r / (2 * b) + d / (2 * r)

noncomputable def hullSixTwoFour_p12LowTerm
    (a b d r : ℝ) : Fin 13 → ℝ :=
  ![a, r, a / d, b / d, 1 / d, b / (a * d),
    b / a, d / a, 1 / a, d / (2 * b),
    1 / (2 * b), r / (2 * b), d / (2 * r)]

def hullSixTwoFour_p12LowWeight : Fin 13 → ℕ :=
  ![5, 2, 3, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3]

noncomputable def hullSixTwoFour_p12LowConstant : ℝ :=
  1 / 257989017600000

theorem hullSixTwoFour_p12LowWeight_pos
    (i : Fin 13) : 0 < hullSixTwoFour_p12LowWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_p12LowWeight]

theorem hullSixTwoFour_p12LowWeight_sum :
    ∑ i, hullSixTwoFour_p12LowWeight i = 30 := by
  norm_num [hullSixTwoFour_p12LowWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_p12LowTerm_nonneg
    {a b d r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (hr : 0 ≤ r) (i : Fin 13) :
    0 ≤ hullSixTwoFour_p12LowTerm a b d r i := by
  fin_cases i <;> simp [hullSixTwoFour_p12LowTerm] <;> positivity

theorem hullSixTwoFour_p12LowTerm_sum
    (a b d r : ℝ) :
    ∑ i, hullSixTwoFour_p12LowTerm a b d r i =
      hullSixTwoFour_p12LowLaurent a b d r := by
  simp [hullSixTwoFour_p12LowTerm,
    hullSixTwoFour_p12LowLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_p12LowTerm_product
    {a b d r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (hr : 0 < r) :
    (∏ i,
        (hullSixTwoFour_p12LowTerm a b d r i /
          (hullSixTwoFour_p12LowWeight i : ℝ)) ^
            hullSixTwoFour_p12LowWeight i) =
      hullSixTwoFour_p12LowConstant := by
  simp [hullSixTwoFour_p12LowTerm,
    hullSixTwoFour_p12LowWeight, Fin.prod_univ_succ,
    hullSixTwoFour_p12LowConstant]
  field_simp [ha.ne', hb.ne', hd.ne', hr.ne'] <;> ring

theorem hullSixTwoFour_p12LowConstant_pos :
    0 < hullSixTwoFour_p12LowConstant := by
  norm_num [hullSixTwoFour_p12LowConstant]

theorem hullSixTwoFour_p12Low_integer_gap :
    (19 : ℕ) ^ 30 * 257989017600000 < 60 ^ 30 := by
  norm_num

theorem hullSixTwoFour_p12Low_root_gap :
    (19 : ℝ) / 2 <
      30 * hullSixTwoFour_p12LowConstant ^ ((30 : ℝ)⁻¹) := by
  have hpow : ((19 : ℝ) / 60) ^ 30 <
      hullSixTwoFour_p12LowConstant := by
    norm_num [hullSixTwoFour_p12LowConstant]
  have hpowRpow : ((19 : ℝ) / 60) ^ (30 : ℝ) <
      hullSixTwoFour_p12LowConstant := by
    change ((19 : ℝ) / 60) ^ ((30 : ℕ) : ℝ) <
      hullSixTwoFour_p12LowConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (19 : ℝ) / 60 <
      hullSixTwoFour_p12LowConstant ^ ((30 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_p12LowConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_p12Low_laurent_gt
    {a b d r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (hr : 0 < r) :
    (19 : ℝ) / 2 < hullSixTwoFour_p12LowLaurent a b d r := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_p12LowWeight
    (hullSixTwoFour_p12LowTerm a b d r)
    hullSixTwoFour_p12LowWeight_pos
    (hullSixTwoFour_p12LowTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hd) (le_of_lt hr))
  rw [hullSixTwoFour_p12LowWeight_sum,
    hullSixTwoFour_p12LowTerm_product ha hb hd hr,
    hullSixTwoFour_p12LowTerm_sum a b d r] at hamgm
  exact hullSixTwoFour_p12Low_root_gap.trans_le hamgm

/-! ## The scalar frontier closer -/

/-- Scalar closure for the maximal-q `p = (1,2)` `X` frontier. -/
theorem hullSixTwoFour_p12MaximalQ_scalar
    {a b c d e f A C E0 E1 E2 F : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A) (hE01 : 1 ≤ E0)
    (hE11 : 1 ≤ E1) (hE21 : 1 ≤ E2)
    (hQ : 1 ≤ E2 - e + f)
    (hF : a + f + 1 ≤ F)
    (hE0Transition : c + d ≤ a * E0)
    (hE1Transition : d + e ≤ b * E1)
    (hATransition : a + b ≤ d * A)
    (hCTransition : c * A + b ≤ a * C)
    (hEar0 : d ≤ (d - c) * E1 - (e - d) * E0)
    (hEar1 : e ≤ (e - f) * E1 + (e - d) * E2) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hE00 : 0 ≤ E0 := le_trans zero_le_one hE01
  have hE10 : 0 ≤ E1 := le_trans zero_le_one hE11
  have hE20 : 0 ≤ E2 := le_trans zero_le_one hE21

  have hEF : a + e + 2 ≤ E2 + F := by
    nlinarith [hQ, hF]
  have hALower : (a + b) / d ≤ A := by
    exact (div_le_iff₀ hd).2 (by simpa [mul_comm] using hATransition)
  have hAc : A ≤ c * A := by
    simpa using mul_le_mul_of_nonneg_right hc1 hA0
  have hCWeak : A + b ≤ a * C := by
    linarith [hAc, hCTransition]
  have hCLower : (A + b) / a ≤ C := by
    exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hCWeak)
  have hCLower' : A / a + b / a ≤ C := by
    calc
      A / a + b / a = (A + b) / a := by ring
      _ ≤ C := hCLower
  have hE0Weak : 1 + d ≤ a * E0 := by
    linarith [hc1, hE0Transition]
  have hE0Lower : (1 + d) / a ≤ E0 := by
    exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hE0Weak)
  have hE0Lower' : 1 / a + d / a ≤ E0 := by
    calc
      1 / a + d / a = (1 + d) / a := by ring
      _ ≤ E0 := hE0Lower
  have hAOver : ((a + b) / d) / a ≤ A / a := by
    exact (div_le_div_iff_of_pos_right ha).2 hALower
  have hCoreShape :
      hullSixTwoFour_p12HighLaurent a b d - a - d / b =
        (a + b) / d + ((a + b) / d) / a + (b + d + 1) / a := by
    dsimp [hullSixTwoFour_p12HighLaurent]
    field_simp [ha.ne', hb.ne', hd.ne'] <;> ring
  have hCore :
      hullSixTwoFour_p12HighLaurent a b d - a - d / b ≤
        A + C + E0 := by
    rw [hCoreShape]
    rw [show (b + d + 1) / a = b / a + d / a + 1 / a by ring]
    nlinarith [hALower, hAOver, hCLower', hE0Lower']
  have hBase :
      2 + a + e +
          (hullSixTwoFour_p12HighLaurent a b d - a - d / b) + E1 ≤
        A + C + E0 + E1 + E2 + F := by
    nlinarith [hCore, hEF]

  by_cases hde : d ≤ e
  · have hdc : (d - c) * E1 ≤ (d - 1) * E1 := by
      have hcoef : d - c ≤ d - 1 := by linarith
      exact mul_le_mul_of_nonneg_right hcoef hE10
    have hgap : e - d ≤ (e - d) * E0 := by
      simpa using mul_le_mul_of_nonneg_left hE01 (sub_nonneg.mpr hde)
    have hEarReduced : e ≤ (d - 1) * E1 := by
      nlinarith [hEar0, hdc, hgap]
    have hdr : 0 < d - 1 := by
      by_contra hnot
      have hnonpos : d - 1 ≤ 0 := le_of_not_gt hnot
      have hmul : (d - 1) * E1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnonpos hE10
      nlinarith
    have hEarLower : e / (d - 1) ≤ E1 := by
      exact (div_le_iff₀ hdr).2
        (by simpa [mul_comm] using hEarReduced)
    have hTransitionLower : (d + e) / b ≤ E1 := by
      exact (div_le_iff₀ hb).2
        (by simpa [mul_comm] using hE1Transition)
    have hAverage :
        (1 / 2 : ℝ) * ((d + e) / b) +
            (1 / 2 : ℝ) * (e / (d - 1)) ≤ E1 := by
      nlinarith [hTransitionLower, hEarLower]
    have hdHalf : d / b ≤ (1 / 2 : ℝ) * ((d + e) / b) := by
      have hnum : d ≤ (d + e) / 2 := by nlinarith
      have hdiv : d / b ≤ ((d + e) / 2) / b :=
        (div_le_div_iff_of_pos_right hb).2 hnum
      calc
        d / b ≤ ((d + e) / 2) / b := hdiv
        _ = (1 / 2 : ℝ) * ((d + e) / b) := by
          field_simp [hb.ne'] <;> ring
    have hdEarHalf : d / (2 * (d - 1)) ≤
        (1 / 2 : ℝ) * (e / (d - 1)) := by
      have hdiv : d / (d - 1) ≤ e / (d - 1) :=
        (div_le_div_iff_of_pos_right hdr).2 hde
      have hshape : d / (2 * (d - 1)) =
          (1 / 2 : ℝ) * (d / (d - 1)) := by
        field_simp [hdr.ne'] <;> ring
      rw [hshape]
      exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    have hEdge : d / b + d / (2 * (d - 1)) ≤ E1 := by
      nlinarith [hAverage, hdHalf, hdEarHalf]
    have hLower :
        2 + hullSixTwoFour_p12HighLaurent a b d +
            d + d / (2 * (d - 1)) ≤
          A + C + E0 + E1 + E2 + F := by
      nlinarith [hBase, hEdge, hde]
    have hLaurent := hullSixTwoFour_p12High_laurent_gt ha hb hd
    have hpair : (5 : ℝ) / 2 < d + d / (2 * (d - 1)) := by
      let r : ℝ := d - 1
      have hr : 0 < r := by simpa [r] using hdr
      have hpos : 0 < 2 * (r - 1 / 2) ^ 2 + 1 / 2 := by positivity
      have hnum : 0 < 2 * r ^ 2 - 2 * r + 1 := by nlinarith
      have hratio : 1 < r + 1 / (2 * r) := by
        have hshape :
            r + 1 / (2 * r) - 1 =
              (2 * r ^ 2 - 2 * r + 1) / (2 * r) := by
          field_simp [hr.ne'] <;> ring
        have hfrac :
            0 < (2 * r ^ 2 - 2 * r + 1) / (2 * r) :=
          div_pos hnum (by positivity)
        nlinarith [hshape, hfrac]
      dsimp [r] at hratio ⊢
      have hshape : d / (2 * (d - 1)) =
          (1 : ℝ) / 2 + 1 / (2 * (d - 1)) := by
        field_simp [hdr.ne'] <;> ring
      rw [hshape]
      nlinarith
    nlinarith [hLower, hLaurent, hpair]
  · have hed : e < d := lt_of_not_ge hde
    have hef : (e - f) * E1 ≤ (e - 1) * E1 := by
      have hcoef : e - f ≤ e - 1 := by linarith
      exact mul_le_mul_of_nonneg_right hcoef hE10
    have hgap : (e - d) * E2 ≤ e - d := by
      have hcoef : e - d ≤ 0 := sub_nonpos.mpr (le_of_lt hed)
      simpa using mul_le_mul_of_nonpos_left hE21 hcoef
    have hEarReduced : d ≤ (e - 1) * E1 := by
      nlinarith [hEar1, hef, hgap]
    let r : ℝ := e - 1
    have hr : 0 < r := by
      dsimp [r]
      by_contra hnot
      have hnonpos : e - 1 ≤ 0 := le_of_not_gt hnot
      have hmul : (e - 1) * E1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnonpos hE10
      nlinarith
    have hEarLower : d / r ≤ E1 := by
      exact (div_le_iff₀ hr).2
        (by simpa [r, mul_comm] using hEarReduced)
    have hTransitionLower : (d + e) / b ≤ E1 := by
      exact (div_le_iff₀ hb).2
        (by simpa [mul_comm] using hE1Transition)
    have hAverage :
        (1 / 2 : ℝ) * ((d + e) / b) +
            (1 / 2 : ℝ) * (d / r) ≤ E1 := by
      nlinarith [hTransitionLower, hEarLower]
    have hLowShape :
        3 + hullSixTwoFour_p12LowLaurent a b d r =
          2 + a + e +
            (hullSixTwoFour_p12HighLaurent a b d - a - d / b) +
              (1 / 2 : ℝ) * ((d + e) / b) +
                (1 / 2 : ℝ) * (d / r) := by
      dsimp [r, hullSixTwoFour_p12LowLaurent,
        hullSixTwoFour_p12HighLaurent]
      field_simp [ha.ne', hb.ne', hd.ne', hr.ne'] <;> ring
    have hLower :
        3 + hullSixTwoFour_p12LowLaurent a b d r ≤
          A + C + E0 + E1 + E2 + F := by
      rw [hLowShape]
      nlinarith [hBase, hAverage]
    have hLaurent := hullSixTwoFour_p12Low_laurent_gt ha hb hd hr
    nlinarith [hLower, hLaurent]

end Heilbronn8.Survivors.Join
