import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Ordered scalar closure for the `p22/q22` packet

The polynomial recurrence bound gives a three-term lower bound for `C`.
The middle transition and the appropriate lower ear are averaged.  After
splitting on `d <= e` and on `1 + b / d <= b^2`, two high-product branches
are closed by exact weighted AM--GM certificates.  Both low-product branches
reduce to the same elementary two-variable inequality.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## High-product AM--GM certificates -/

noncomputable def hullSixTwoFourP22Q22MinusHighLaurent
    (r b d : ℝ) : ℝ :=
  r + b + 3 / (2 * b) + 1 / d + b / d + r / (2 * b) +
    3 * d / (2 * b) + 1 / (2 * r)

noncomputable def hullSixTwoFourP22Q22MinusHighTerm
    (r b d : ℝ) : Fin 8 → ℝ :=
  ![r, b, 3 / (2 * b), 1 / d, b / d, r / (2 * b),
    3 * d / (2 * b), 1 / (2 * r)]

def hullSixTwoFourP22Q22MinusHighWeight : Fin 8 → ℕ :=
  ![1, 4, 2, 1, 2, 1, 3, 2]

noncomputable def hullSixTwoFourP22Q22MinusHighConstant : ℝ :=
  9 / 4194304

theorem hullSixTwoFourP22Q22MinusHighWeight_pos
    (i : Fin 8) : 0 < hullSixTwoFourP22Q22MinusHighWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP22Q22MinusHighWeight]

theorem hullSixTwoFourP22Q22MinusHighWeight_sum :
    ∑ i, hullSixTwoFourP22Q22MinusHighWeight i = 16 := by
  norm_num [hullSixTwoFourP22Q22MinusHighWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourP22Q22MinusHighTerm_nonneg
    {r b d : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (i : Fin 8) :
    0 ≤ hullSixTwoFourP22Q22MinusHighTerm r b d i := by
  fin_cases i <;>
    simp [hullSixTwoFourP22Q22MinusHighTerm] <;> positivity

theorem hullSixTwoFourP22Q22MinusHighTerm_sum
    (r b d : ℝ) :
    ∑ i, hullSixTwoFourP22Q22MinusHighTerm r b d i =
      hullSixTwoFourP22Q22MinusHighLaurent r b d := by
  simp [hullSixTwoFourP22Q22MinusHighTerm,
    hullSixTwoFourP22Q22MinusHighLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFourP22Q22MinusHighTerm_product
    {r b d : ℝ} (hr : 0 < r) (hb : 0 < b) (hd : 0 < d) :
    (∏ i,
        (hullSixTwoFourP22Q22MinusHighTerm r b d i /
          (hullSixTwoFourP22Q22MinusHighWeight i : ℝ)) ^
            hullSixTwoFourP22Q22MinusHighWeight i) =
      hullSixTwoFourP22Q22MinusHighConstant := by
  simp [hullSixTwoFourP22Q22MinusHighTerm,
    hullSixTwoFourP22Q22MinusHighWeight, Fin.prod_univ_succ,
    hullSixTwoFourP22Q22MinusHighConstant]
  field_simp [hr.ne', hb.ne', hd.ne'] <;> ring

theorem hullSixTwoFourP22Q22MinusHighConstant_pos :
    0 < hullSixTwoFourP22Q22MinusHighConstant := by
  norm_num [hullSixTwoFourP22Q22MinusHighConstant]

theorem hullSixTwoFourP22Q22MinusHigh_root_gap :
    (7 : ℝ) <
      16 * hullSixTwoFourP22Q22MinusHighConstant ^ ((16 : ℝ)⁻¹) := by
  have hpow :
      ((7 : ℝ) / 16) ^ 16 < hullSixTwoFourP22Q22MinusHighConstant := by
    norm_num [hullSixTwoFourP22Q22MinusHighConstant]
  have hpowRpow :
      ((7 : ℝ) / 16) ^ (16 : ℝ) <
        hullSixTwoFourP22Q22MinusHighConstant := by
    change ((7 : ℝ) / 16) ^ ((16 : ℕ) : ℝ) <
      hullSixTwoFourP22Q22MinusHighConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (7 : ℝ) / 16 <
        hullSixTwoFourP22Q22MinusHighConstant ^ ((16 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourP22Q22MinusHighConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP22Q22MinusHigh_laurent_gt
    {r b d : ℝ} (hr : 0 < r) (hb : 0 < b) (hd : 0 < d) :
    (7 : ℝ) < hullSixTwoFourP22Q22MinusHighLaurent r b d := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourP22Q22MinusHighWeight
    (hullSixTwoFourP22Q22MinusHighTerm r b d)
    hullSixTwoFourP22Q22MinusHighWeight_pos
    (hullSixTwoFourP22Q22MinusHighTerm_nonneg hr.le hb.le hd.le)
  rw [hullSixTwoFourP22Q22MinusHighWeight_sum,
    hullSixTwoFourP22Q22MinusHighTerm_product hr hb hd,
    hullSixTwoFourP22Q22MinusHighTerm_sum r b d] at hamgm
  exact hullSixTwoFourP22Q22MinusHigh_root_gap.trans_le hamgm

noncomputable def hullSixTwoFourP22Q22PlusHighLaurent
    (r b d : ℝ) : ℝ :=
  r + b + 1 / b + 1 / d + b / d + 2 * d / b + 1 / (2 * r)

noncomputable def hullSixTwoFourP22Q22PlusHighTerm
    (r b d : ℝ) : Fin 7 → ℝ :=
  ![r, b, 1 / b, 1 / d, b / d, 2 * d / b, 1 / (2 * r)]

def hullSixTwoFourP22Q22PlusHighWeight : Fin 7 → ℕ :=
  ![1, 2, 1, 1, 1, 2, 1]

noncomputable def hullSixTwoFourP22Q22PlusHighConstant : ℝ := 1 / 8

theorem hullSixTwoFourP22Q22PlusHighWeight_pos
    (i : Fin 7) : 0 < hullSixTwoFourP22Q22PlusHighWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP22Q22PlusHighWeight]

theorem hullSixTwoFourP22Q22PlusHighWeight_sum :
    ∑ i, hullSixTwoFourP22Q22PlusHighWeight i = 9 := by
  norm_num [hullSixTwoFourP22Q22PlusHighWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourP22Q22PlusHighTerm_nonneg
    {r b d : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (i : Fin 7) :
    0 ≤ hullSixTwoFourP22Q22PlusHighTerm r b d i := by
  fin_cases i <;>
    simp [hullSixTwoFourP22Q22PlusHighTerm] <;> positivity

theorem hullSixTwoFourP22Q22PlusHighTerm_sum
    (r b d : ℝ) :
    ∑ i, hullSixTwoFourP22Q22PlusHighTerm r b d i =
      hullSixTwoFourP22Q22PlusHighLaurent r b d := by
  simp [hullSixTwoFourP22Q22PlusHighTerm,
    hullSixTwoFourP22Q22PlusHighLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFourP22Q22PlusHighTerm_product
    {r b d : ℝ} (hr : 0 < r) (hb : 0 < b) (hd : 0 < d) :
    (∏ i,
        (hullSixTwoFourP22Q22PlusHighTerm r b d i /
          (hullSixTwoFourP22Q22PlusHighWeight i : ℝ)) ^
            hullSixTwoFourP22Q22PlusHighWeight i) =
      hullSixTwoFourP22Q22PlusHighConstant := by
  simp [hullSixTwoFourP22Q22PlusHighTerm,
    hullSixTwoFourP22Q22PlusHighWeight, Fin.prod_univ_succ,
    hullSixTwoFourP22Q22PlusHighConstant]
  field_simp [hr.ne', hb.ne', hd.ne'] <;> ring

theorem hullSixTwoFourP22Q22PlusHighConstant_pos :
    0 < hullSixTwoFourP22Q22PlusHighConstant := by
  norm_num [hullSixTwoFourP22Q22PlusHighConstant]

theorem hullSixTwoFourP22Q22PlusHigh_root_gap :
    (7 : ℝ) <
      9 * hullSixTwoFourP22Q22PlusHighConstant ^ ((9 : ℝ)⁻¹) := by
  have hpow :
      ((7 : ℝ) / 9) ^ 9 < hullSixTwoFourP22Q22PlusHighConstant := by
    norm_num [hullSixTwoFourP22Q22PlusHighConstant]
  have hpowRpow :
      ((7 : ℝ) / 9) ^ (9 : ℝ) <
        hullSixTwoFourP22Q22PlusHighConstant := by
    change ((7 : ℝ) / 9) ^ ((9 : ℕ) : ℝ) <
      hullSixTwoFourP22Q22PlusHighConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (7 : ℝ) / 9 <
        hullSixTwoFourP22Q22PlusHighConstant ^ ((9 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num)
      (le_of_lt hullSixTwoFourP22Q22PlusHighConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP22Q22PlusHigh_laurent_gt
    {r b d : ℝ} (hr : 0 < r) (hb : 0 < b) (hd : 0 < d) :
    (7 : ℝ) < hullSixTwoFourP22Q22PlusHighLaurent r b d := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourP22Q22PlusHighWeight
    (hullSixTwoFourP22Q22PlusHighTerm r b d)
    hullSixTwoFourP22Q22PlusHighWeight_pos
    (hullSixTwoFourP22Q22PlusHighTerm_nonneg hr.le hb.le hd.le)
  rw [hullSixTwoFourP22Q22PlusHighWeight_sum,
    hullSixTwoFourP22Q22PlusHighTerm_product hr hb hd,
    hullSixTwoFourP22Q22PlusHighTerm_sum r b d] at hamgm
  exact hullSixTwoFourP22Q22PlusHigh_root_gap.trans_le hamgm

/-! ## Shared elementary comparisons -/

private theorem hullSixTwoFourP22Q22_ratio_sum_two
    {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (2 : ℝ) ≤ b / d + d / b := by
  have hshape :
      b / d + d / b - 2 = (b - d) ^ 2 / (b * d) := by
    field_simp [hb.ne', hd.ne'] <;> ring
  apply sub_nonneg.mp
  rw [hshape]
  positivity

private theorem hullSixTwoFourP22Q22_high_compare
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hba : b ≤ a) (hsq : 1 + b / d ≤ b ^ 2) :
    b + 1 / b + 1 / d ≤ a + 1 / a + b / (a * d) := by
  have hbd : d + b ≤ b ^ 2 * d := by
    calc
      d + b = (1 + b / d) * d := by
        field_simp [hd.ne'] <;> ring
      _ ≤ b ^ 2 * d := mul_le_mul_of_nonneg_right hsq hd.le
  have hb2ad : b ^ 2 * d ≤ a * b * d := by
    have h := mul_le_mul_of_nonneg_right hba (mul_nonneg hb.le hd.le)
    nlinarith
  have hfactor : 0 ≤ a * b * d - d - b := by nlinarith
  have hshape :
      a + 1 / a + b / (a * d) - (b + 1 / b + 1 / d) =
        (a - b) * (a * b * d - d - b) / (a * b * d) := by
    field_simp [ha.ne', hb.ne', hd.ne'] <;> ring
  apply sub_nonneg.mp
  rw [hshape]
  positivity

private theorem hullSixTwoFourP22Q22_low_compare
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hba : b ≤ a) (hsq : b ^ 2 < 1 + b / d) :
    2 * b < a + 1 / a + b / (a * d) := by
  have hnum : 0 < (a - b) ^ 2 + (1 + b / d - b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have hshape :
      a + 1 / a + b / (a * d) - 2 * b =
        ((a - b) ^ 2 + (1 + b / d - b ^ 2)) / a := by
    field_simp [ha.ne', hd.ne'] <;> ring
  apply sub_pos.mp
  rw [hshape]
  positivity

private theorem hullSixTwoFourP22Q22_base_seven
    {b r : ℝ} (hb1 : 1 ≤ b) (hr : 0 < r) :
    (7 : ℝ) ≤ r + 2 * b + 2 + (1 + r) / b + 1 / (2 * r) := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  by_cases hsmall : r ≤ 2 * b - 1
  · have hshape :
        r + 2 * b + 2 + (1 + r) / b + 1 / (2 * r) - 7 =
          (2 * r - 1) ^ 2 / (2 * r) +
            (b - 1) * (2 * b - 1 - r) / b := by
      field_simp [hb.ne', hr.ne'] <;> ring
    apply sub_nonneg.mp
    rw [hshape]
    have hfirst : 0 ≤ (2 * r - 1) ^ 2 / (2 * r) := by positivity
    have hsecond : 0 ≤ (b - 1) * (2 * b - 1 - r) / b := by
      exact div_nonneg
        (mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hsmall)) hb.le
    positivity
  · have hlarge : 2 * b - 1 < r := lt_of_not_ge hsmall
    have hr1 : 1 < r := by nlinarith
    have h2b : (2 : ℝ) ≤ 2 * b := by nlinarith
    have hquot : (2 : ℝ) < (1 + r) / b := by
      exact (lt_div_iff₀ hb).2 (by nlinarith)
    have hhalf : 0 < 1 / (2 * r) := by positivity
    nlinarith

/-! ## The ordered scalar endpoint -/

/-- Ordered scalar closure for the exact `p22/q22` packet. -/
theorem hullSixTwoFour_p22q22_ordered_scalar
    {a b d e C E1 H : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hd1 : 1 ≤ d) (he1 : 1 ≤ e)
    (hba : b ≤ a)
    (hCRec : d + a * b + b ≤ a * d * C)
    (hE1Rec : e + 3 * d ≤ b * E1)
    (hEar0 : d ≤ e → d ≤ (d - 1) * E1)
    (hEar1 : e < d → e ≤ (e - 1) * E1)
    (hH : a + e + C + E1 + 4 ≤ H) :
    (25 : ℝ) / 2 < H := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1

  have hCLower : 1 / a + b / d + b / (a * d) ≤ C := by
    have hdiv : (d + a * b + b) / (a * d) ≤ C :=
      (div_le_iff₀ (mul_pos ha hd)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hCRec)
    calc
      1 / a + b / d + b / (a * d) =
          (d + a * b + b) / (a * d) := by
        field_simp [ha.ne', hd.ne'] <;> ring
      _ ≤ C := hdiv
  have hE1Lower : (e + 3 * d) / b ≤ E1 :=
    (div_le_iff₀ hb).2 (by simpa [mul_comm] using hE1Rec)
  have hE1pos : 0 < E1 := by
    have hnum : 0 < e + 3 * d := by positivity
    have hquot : 0 < (e + 3 * d) / b := div_pos hnum hb
    exact lt_of_lt_of_le hquot hE1Lower

  by_cases hde : d ≤ e
  · let r : ℝ := d - 1
    have hear := hEar0 hde
    have hr : 0 < r := by
      dsimp [r]
      by_contra hnot
      have hrnonpos : d - 1 ≤ 0 := le_of_not_gt hnot
      have hmul : (d - 1) * E1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hrnonpos hE1pos.le
      nlinarith
    have hEarDiv : d / r ≤ E1 :=
      (div_le_iff₀ hr).2 (by simpa [r, mul_comm] using hear)
    have hAvg0 : ((e + 3 * d) / b + d / r) / 2 ≤ E1 := by
      nlinarith [hE1Lower, hEarDiv]
    have hEAvg : (e + 3 * d) / (2 * b) + d / (2 * r) ≤ E1 := by
      calc
        (e + 3 * d) / (2 * b) + d / (2 * r) =
            ((e + 3 * d) / b + d / r) / 2 := by
          field_simp [hb.ne', hr.ne'] <;> ring
        _ ≤ E1 := hAvg0
    have heLower : d ≤ e := hde
    have hEAvgD : (d + 3 * d) / (2 * b) + d / (2 * r) ≤ E1 := by
      calc
        (d + 3 * d) / (2 * b) + d / (2 * r) ≤
            (e + 3 * d) / (2 * b) + d / (2 * r) := by
          exact add_le_add
            ((div_le_div_iff_of_pos_right
              (mul_pos (by norm_num) hb)).2 (by linarith))
            (le_refl _)
        _ ≤ E1 := hEAvg
    have hRaw :
        (11 : ℝ) / 2 +
            (r + a + 1 / a + b / d + b / (a * d) +
              2 * d / b + 1 / (2 * r)) ≤ H := by
      have hshape :
          (11 : ℝ) / 2 +
              (r + a + 1 / a + b / d + b / (a * d) +
                2 * d / b + 1 / (2 * r)) =
            a + d + (1 / a + b / d + b / (a * d)) +
              ((d + 3 * d) / (2 * b) + d / (2 * r)) + 4 := by
        have hdr : d = r + 1 := by
          dsimp [r]
          ring
        rw [hdr]
        field_simp [ha.ne', hb.ne', hr.ne',
          (add_pos hr zero_lt_one).ne'] <;> ring
      rw [hshape]
      nlinarith [hH, hCLower, hEAvgD]
    by_cases hsq : 1 + b / d ≤ b ^ 2
    · have hcompare := hullSixTwoFourP22Q22_high_compare ha hb hd hba hsq
      have hLower :
          hullSixTwoFourP22Q22PlusHighLaurent r b d ≤
            r + a + 1 / a + b / d + b / (a * d) +
              2 * d / b + 1 / (2 * r) := by
        dsimp [hullSixTwoFourP22Q22PlusHighLaurent]
        nlinarith
      have hseven := hullSixTwoFourP22Q22PlusHigh_laurent_gt hr hb hd
      nlinarith
    · have hsqLow : b ^ 2 < 1 + b / d := lt_of_not_ge hsq
      have hcompare :=
        hullSixTwoFourP22Q22_low_compare ha hb hd hba hsqLow
      have hratio := hullSixTwoFourP22Q22_ratio_sum_two hb hd
      have hdr : d / b = (1 + r) / b := by
        dsimp [r]
        ring
      have hBStrict :
          r + 2 * b + 2 + (1 + r) / b + 1 / (2 * r) <
            r + a + 1 / a + b / d + b / (a * d) +
              2 * d / b + 1 / (2 * r) := by
        rw [← hdr]
        have hsum :
            2 * b + 2 <
              (a + 1 / a + b / (a * d)) + (b / d + d / b) :=
          add_lt_add_of_lt_of_le hcompare hratio
        have hsum' :=
          add_lt_add_right
            (add_lt_add_left (add_lt_add_right hsum (d / b)) r)
            (1 / (2 * r))
        convert hsum' using 1 <;> ring
      have hB := hullSixTwoFourP22Q22_base_seven hb1 hr
      nlinarith
  · have hed : e < d := lt_of_not_ge hde
    let r : ℝ := e - 1
    have hear := hEar1 hed
    have hr : 0 < r := by
      dsimp [r]
      by_contra hnot
      have hrnonpos : e - 1 ≤ 0 := le_of_not_gt hnot
      have hmul : (e - 1) * E1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hrnonpos hE1pos.le
      nlinarith
    have hEarDiv : e / r ≤ E1 :=
      (div_le_iff₀ hr).2 (by simpa [r, mul_comm] using hear)
    have hAvg0 : ((e + 3 * d) / b + e / r) / 2 ≤ E1 := by
      nlinarith [hE1Lower, hEarDiv]
    have hEAvg : (e + 3 * d) / (2 * b) + e / (2 * r) ≤ E1 := by
      calc
        (e + 3 * d) / (2 * b) + e / (2 * r) =
            ((e + 3 * d) / b + e / r) / 2 := by
          field_simp [hb.ne', hr.ne'] <;> ring
        _ ≤ E1 := hAvg0
    have hRaw :
        (11 : ℝ) / 2 +
            (r + a + 1 / a + b / d + b / (a * d) + 1 / (2 * b) +
              r / (2 * b) + 3 * d / (2 * b) + 1 / (2 * r)) ≤ H := by
      have hshape :
          (11 : ℝ) / 2 +
              (r + a + 1 / a + b / d + b / (a * d) + 1 / (2 * b) +
                r / (2 * b) + 3 * d / (2 * b) + 1 / (2 * r)) =
            a + e + (1 / a + b / d + b / (a * d)) +
              ((e + 3 * d) / (2 * b) + e / (2 * r)) + 4 := by
        have her : e = 1 + r := by
          dsimp [r]
          ring
        rw [her]
        field_simp [ha.ne', hb.ne', hd.ne', hr.ne'] <;> ring
      rw [hshape]
      nlinarith [hH, hCLower, hEAvg]
    by_cases hsq : 1 + b / d ≤ b ^ 2
    · have hcompare := hullSixTwoFourP22Q22_high_compare ha hb hd hba hsq
      have hLower :
          hullSixTwoFourP22Q22MinusHighLaurent r b d ≤
            r + a + 1 / a + b / d + b / (a * d) + 1 / (2 * b) +
              r / (2 * b) + 3 * d / (2 * b) + 1 / (2 * r) := by
        dsimp [hullSixTwoFourP22Q22MinusHighLaurent]
        have hcompare' :
            b + 3 / (2 * b) + 1 / d ≤
              a + 1 / a + b / (a * d) + 1 / (2 * b) := by
          calc
            b + 3 / (2 * b) + 1 / d =
                (b + 1 / b + 1 / d) + 1 / (2 * b) := by
              field_simp [hb.ne', hd.ne'] <;> ring
            _ ≤ (a + 1 / a + b / (a * d)) + 1 / (2 * b) :=
              add_le_add hcompare le_rfl
            _ = a + 1 / a + b / (a * d) + 1 / (2 * b) := by ring
        nlinarith [hcompare']
      have hseven := hullSixTwoFourP22Q22MinusHigh_laurent_gt hr hb hd
      nlinarith
    · have hsqLow : b ^ 2 < 1 + b / d := lt_of_not_ge hsq
      have hcompare :=
        hullSixTwoFourP22Q22_low_compare ha hb hd hba hsqLow
      have hratio := hullSixTwoFourP22Q22_ratio_sum_two hb hd
      have hrd : 1 + r ≤ d := by
        dsimp [r]
        linarith
      have hrest :
          (1 + r) / b ≤ 1 / (2 * b) + r / (2 * b) + d / (2 * b) := by
        calc
          (1 + r) / b = (2 * (1 + r)) / (2 * b) := by
            field_simp [hb.ne'] <;> ring
          _ ≤ (1 + r + d) / (2 * b) :=
            (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hb)).2
              (by nlinarith [hrd])
          _ = 1 / (2 * b) + r / (2 * b) + d / (2 * b) := by
            field_simp [hb.ne'] <;> ring
      have hBStrict :
          r + 2 * b + 2 + (1 + r) / b + 1 / (2 * r) <
            r + a + 1 / a + b / d + b / (a * d) + 1 / (2 * b) +
              r / (2 * b) + 3 * d / (2 * b) + 1 / (2 * r) := by
        have htail :
            2 + (1 + r) / b ≤
              b / d + 1 / (2 * b) + r / (2 * b) +
                3 * d / (2 * b) := by
          calc
            2 + (1 + r) / b ≤
                (b / d + d / b) +
                  (1 / (2 * b) + r / (2 * b) + d / (2 * b)) :=
              add_le_add hratio hrest
            _ = b / d + 1 / (2 * b) + r / (2 * b) +
                  3 * d / (2 * b) := by
              field_simp [hb.ne', hd.ne'] <;> ring
        have hcore :
            2 * b + (2 + (1 + r) / b) <
              (a + 1 / a + b / (a * d)) +
                (b / d + 1 / (2 * b) + r / (2 * b) +
                  3 * d / (2 * b)) :=
          add_lt_add_of_lt_of_le hcompare htail
        calc
          r + 2 * b + 2 + (1 + r) / b + 1 / (2 * r) =
              r + (2 * b + (2 + (1 + r) / b)) + 1 / (2 * r) := by ring
          _ < r + ((a + 1 / a + b / (a * d)) +
                (b / d + 1 / (2 * b) + r / (2 * b) +
                  3 * d / (2 * b))) + 1 / (2 * r) :=
            add_lt_add_of_lt_of_le
              (add_lt_add_of_le_of_lt (le_refl r) hcore)
              (le_refl _)
          _ = r + a + 1 / a + b / d + b / (a * d) + 1 / (2 * b) +
                r / (2 * b) + 3 * d / (2 * b) + 1 / (2 * r) := by ring
      have hB := hullSixTwoFourP22Q22_base_seven hb1 hr
      nlinarith

end Heilbronn8
