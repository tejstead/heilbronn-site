import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM--GM closure for the adjacent q-blind `q = 23` chamber

This file isolates the normalized scalar argument for the adjacent signed
cell pair `q = 23` in the `2 + 4` hull-six family.  The two possible orders
of the middle lower heights have independent exact AM--GM certificates.

When `d <= e`, the first lower ear and the shared-cell cap reduce the chamber
to an eleven-term, twenty-six-copy Laurent sum.  When `e <= d`, the second
lower ear reduces it to a fourteen-term, twenty-eight-copy Laurent sum whose
scaled product contains the harmless factor `f^7 >= 1`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## The `d <= e` certificate -/

/-- The Laurent remainder in the nondecreasing middle-height branch. -/
noncomputable def hullSixTwoFourQ23IncreasingLaurent
    (a b c t : ℝ) : ℝ :=
  a + c + a / c + b / c + 1 / b + 1 / b ^ 2 +
    8 * c / (5 * a) + 8 * t / (5 * a) + c / (5 * t) +
      4 / (5 * a * b) + 3 / (5 * b * t)

/-- The eleven terms in the twenty-six-copy certificate. -/
noncomputable def hullSixTwoFourQ23IncreasingTerm
    (a b c t : ℝ) : Fin 11 → ℝ :=
  ![a, c, a / c, b / c, 1 / b, 1 / b ^ 2,
    8 * c / (5 * a), 8 * t / (5 * a), c / (5 * t),
    4 / (5 * a * b), 3 / (5 * b * t)]

/-- Multiplicities of total mass twenty-six. -/
def hullSixTwoFourQ23IncreasingWeight : Fin 11 → ℕ :=
  ![4, 3, 3, 5, 1, 1, 4, 2, 1, 1, 1]

/-- The variable-free scaled product in the increasing branch. -/
noncomputable def hullSixTwoFourQ23IncreasingConstant : ℝ :=
  4 / 1483154296875

theorem hullSixTwoFourQ23Increasing_weight_pos
    (i : Fin 11) : 0 < hullSixTwoFourQ23IncreasingWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ23IncreasingWeight]

theorem hullSixTwoFourQ23Increasing_weight_sum :
    ∑ i, hullSixTwoFourQ23IncreasingWeight i = 26 := by
  norm_num [hullSixTwoFourQ23IncreasingWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ23Increasing_term_nonneg
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin 11) :
    0 ≤ hullSixTwoFourQ23IncreasingTerm a b c t i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ23IncreasingTerm] <;>
    positivity

theorem hullSixTwoFourQ23Increasing_term_sum
    (a b c t : ℝ) :
    ∑ i, hullSixTwoFourQ23IncreasingTerm a b c t i =
      hullSixTwoFourQ23IncreasingLaurent a b c t := by
  simp [hullSixTwoFourQ23IncreasingTerm,
    hullSixTwoFourQ23IncreasingLaurent, Fin.sum_univ_succ] <;>
    ring

/-- The twenty-six scaled terms have exact product `4 / 1483154296875`. -/
theorem hullSixTwoFourQ23Increasing_term_product
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourQ23IncreasingTerm a b c t i /
          (hullSixTwoFourQ23IncreasingWeight i : ℝ)) ^
            hullSixTwoFourQ23IncreasingWeight i) =
      hullSixTwoFourQ23IncreasingConstant := by
  simp [hullSixTwoFourQ23IncreasingTerm,
    hullSixTwoFourQ23IncreasingWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ23IncreasingConstant]
  field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFourQ23Increasing_constant_pos :
    0 < hullSixTwoFourQ23IncreasingConstant := by
  norm_num [hullSixTwoFourQ23IncreasingConstant]

/-- Exact integer endpoint for the twenty-six-copy certificate. -/
theorem hullSixTwoFourQ23Increasing_integer_gap :
    (93 : ℕ) ^ 26 * 1483154296875 < 4 * 260 ^ 26 := by
  norm_num

/-- Its AM--GM root is strictly larger than `93 / 10`. -/
theorem hullSixTwoFourQ23Increasing_root_gap :
    (93 : ℝ) / 10 <
      26 * hullSixTwoFourQ23IncreasingConstant ^ ((26 : ℝ)⁻¹) := by
  have hpow :
      ((93 : ℝ) / 260) ^ 26 <
        hullSixTwoFourQ23IncreasingConstant := by
    norm_num [hullSixTwoFourQ23IncreasingConstant]
  have hpowRpow :
      ((93 : ℝ) / 260) ^ (26 : ℝ) <
        hullSixTwoFourQ23IncreasingConstant := by
    change ((93 : ℝ) / 260) ^ ((26 : ℕ) : ℝ) <
      hullSixTwoFourQ23IncreasingConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (93 : ℝ) / 260 <
        hullSixTwoFourQ23IncreasingConstant ^ ((26 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ23Increasing_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- Exact Laurent inequality for the nondecreasing branch. -/
theorem hullSixTwoFourQ23Increasing_laurent_gt
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (93 : ℝ) / 10 < hullSixTwoFourQ23IncreasingLaurent a b c t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ23IncreasingWeight
    (hullSixTwoFourQ23IncreasingTerm a b c t)
    hullSixTwoFourQ23Increasing_weight_pos
    (hullSixTwoFourQ23Increasing_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFourQ23Increasing_weight_sum,
    hullSixTwoFourQ23Increasing_term_product ha hb hc ht] at hamgm
  rw [← hullSixTwoFourQ23Increasing_term_sum a b c t]
  exact hullSixTwoFourQ23Increasing_root_gap.trans_le hamgm

/-- The reduced endpoint inequality used after eliminating the q23 cells. -/
theorem hullSixTwoFourQ23Increasing_reduced
    {a b c d : ℝ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hc1 : 1 ≤ c) (hcd : c < d) :
    (25 : ℝ) / 2 <
      (16 : ℝ) / 5 +
        hullSixTwoFourQ23IncreasingLaurent a b c (d - c) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have ht : 0 < d - c := sub_pos.mpr hcd
  have hLaurent :=
    hullSixTwoFourQ23Increasing_laurent_gt ha hb hc ht
  linarith

/-! ## The `e <= d` certificate -/

/-- The Laurent sum left after writing `e = f + k` in the decreasing branch. -/
noncomputable def hullSixTwoFourQ23DecreasingLaurent
    (a b c e f k : ℝ) : ℝ :=
  13 / 5 + 2 * a / 9 + 7 * a / (9 * e) + 2 * a / (9 * c) +
    7 * b / 9 + 7 * b / (9 * e) + 2 * b / (9 * c) + e +
      3 * f / (5 * k) + c / b + 3 * f / b + 2 * k / b +
        4 * f / (5 * a) + 4 * k / (5 * a)

/-- The fourteen terms in the twenty-eight-copy certificate. -/
noncomputable def hullSixTwoFourQ23DecreasingTerm
    (a b c e f k : ℝ) : Fin 14 → ℝ :=
  ![13 / 5, 2 * a / 9, 7 * a / (9 * e), 2 * a / (9 * c),
    7 * b / 9, 7 * b / (9 * e), 2 * b / (9 * c), e,
    3 * f / (5 * k), c / b, 3 * f / b, 2 * k / b,
    4 * f / (5 * a), 4 * k / (5 * a)]

/-- Multiplicities of total mass twenty-eight. -/
def hullSixTwoFourQ23DecreasingWeight : Fin 14 → ℕ :=
  ![5, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 1]

/-- The variable-free part of the scaled product. -/
noncomputable def hullSixTwoFourQ23DecreasingConstant : ℝ :=
  ((2 : ℝ) ^ 2 * 7 ^ 6 * 13 ^ 5) / (3 ^ 22 * 5 ^ 15)

theorem hullSixTwoFourQ23Decreasing_weight_pos
    (i : Fin 14) : 0 < hullSixTwoFourQ23DecreasingWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ23DecreasingWeight]

theorem hullSixTwoFourQ23Decreasing_weight_sum :
    ∑ i, hullSixTwoFourQ23DecreasingWeight i = 28 := by
  norm_num [hullSixTwoFourQ23DecreasingWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ23Decreasing_term_nonneg
    {a b c e f k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hk : 0 ≤ k) (i : Fin 14) :
    0 ≤ hullSixTwoFourQ23DecreasingTerm a b c e f k i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ23DecreasingTerm] <;>
    positivity

theorem hullSixTwoFourQ23Decreasing_term_sum
    (a b c e f k : ℝ) :
    ∑ i, hullSixTwoFourQ23DecreasingTerm a b c e f k i =
      hullSixTwoFourQ23DecreasingLaurent a b c e f k := by
  simp [hullSixTwoFourQ23DecreasingTerm,
    hullSixTwoFourQ23DecreasingLaurent, Fin.sum_univ_succ] <;>
    ring

/-- The twenty-eight scaled terms have product `constant * f^7`. -/
theorem hullSixTwoFourQ23Decreasing_term_product
    {a b c e f k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hk : 0 < k) :
    (∏ i,
        (hullSixTwoFourQ23DecreasingTerm a b c e f k i /
          (hullSixTwoFourQ23DecreasingWeight i : ℝ)) ^
            hullSixTwoFourQ23DecreasingWeight i) =
      hullSixTwoFourQ23DecreasingConstant * f ^ 7 := by
  simp [hullSixTwoFourQ23DecreasingTerm,
    hullSixTwoFourQ23DecreasingWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ23DecreasingConstant]
  field_simp [ha.ne', hb.ne', hc.ne', he.ne', hf.ne', hk.ne'] <;> ring

theorem hullSixTwoFourQ23Decreasing_constant_pos :
    0 < hullSixTwoFourQ23DecreasingConstant := by
  norm_num [hullSixTwoFourQ23DecreasingConstant]

/-- Exact integer endpoint for the twenty-eight-copy certificate. -/
theorem hullSixTwoFourQ23Decreasing_integer_gap :
    3 ^ 22 * 5 ^ 15 * (25 : ℕ) ^ 28 <
      2 ^ 2 * 7 ^ 6 * 13 ^ 5 * 56 ^ 28 := by
  norm_num

/-- The variable-free AM--GM root is strictly larger than `25 / 2`. -/
theorem hullSixTwoFourQ23Decreasing_root_gap :
    (25 : ℝ) / 2 <
      28 * hullSixTwoFourQ23DecreasingConstant ^ ((28 : ℝ)⁻¹) := by
  have hpow :
      ((25 : ℝ) / 56) ^ 28 <
        hullSixTwoFourQ23DecreasingConstant := by
    norm_num [hullSixTwoFourQ23DecreasingConstant]
  have hpowRpow :
      ((25 : ℝ) / 56) ^ (28 : ℝ) <
        hullSixTwoFourQ23DecreasingConstant := by
    change ((25 : ℝ) / 56) ^ ((28 : ℕ) : ℝ) <
      hullSixTwoFourQ23DecreasingConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (25 : ℝ) / 56 <
        hullSixTwoFourQ23DecreasingConstant ^ ((28 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ23Decreasing_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- Exact Laurent inequality for the decreasing branch. -/
theorem hullSixTwoFourQ23Decreasing_laurent_gt
    {a b c e f k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hk : 0 < k)
    (hf1 : 1 ≤ f) :
    (25 : ℝ) / 2 <
      hullSixTwoFourQ23DecreasingLaurent a b c e f k := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ23DecreasingWeight
    (hullSixTwoFourQ23DecreasingTerm a b c e f k)
    hullSixTwoFourQ23Decreasing_weight_pos
    (hullSixTwoFourQ23Decreasing_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt he) (le_of_lt hf) (le_of_lt hk))
  rw [hullSixTwoFourQ23Decreasing_weight_sum,
    hullSixTwoFourQ23Decreasing_term_product ha hb hc he hf hk] at hamgm
  have hfPow : (1 : ℝ) ≤ f ^ 7 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hf1 7)
  have hProductFloor :
      hullSixTwoFourQ23DecreasingConstant ≤
        hullSixTwoFourQ23DecreasingConstant * f ^ 7 := by
    have h := mul_le_mul_of_nonneg_left hfPow
      (le_of_lt hullSixTwoFourQ23Decreasing_constant_pos)
    simpa using h
  have hRootFloor :
      hullSixTwoFourQ23DecreasingConstant ^ ((28 : ℝ)⁻¹) ≤
        (hullSixTwoFourQ23DecreasingConstant * f ^ 7) ^ ((28 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixTwoFourQ23Decreasing_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourQ23Decreasing_term_sum a b c e f k]
  exact hullSixTwoFourQ23Decreasing_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## Raw q23 packet -/

/--
Complete scalar closure for the adjacent q-blind `q = 23` packet.

The variables `w,x,y` are the three consecutive primed lower-fan edges,
and `T,J,K` are the shared signed cell magnitudes.  All hypotheses are raw
area-floor, transition, cell-identity, cap, or lower-ear inequalities.
-/
theorem hullSixTwoFourQ23_scalar
    {a b c d e f A C w x y Fp T J K : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A) (hC1 : 1 ≤ C)
    (hw1 : 1 ≤ w) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y)
    (hFp1 : 1 ≤ Fp) (hT1 : 1 ≤ T)
    (hJ1 : 1 ≤ J) (hK1 : 1 ≤ K)
    (hAtransition : a + b ≤ c * A)
    (hwTransition : c + d ≤ b * (w + c - d))
    (hVerticalTransition : a + b ≤ e * (A + a - b))
    (hxTransition : d + e ≤ a * x)
    (hCellW : b * w + c * T = d * (b + c + C))
    (hCellX : b * x + d * J = e * T)
    (hCellY : b * y = f * J + e * K)
    (hTcap : T ≤ b + d - 1)
    (hEar0 : d ≤ (d - c) * x - (e - d) * w)
    (hEar2 : e ≤ (e - d) * y - (f - e) * x) :
    (25 : ℝ) / 2 < A + C + w + x + y + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw1
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy1

  by_cases hde : d ≤ e
  · have hq : 0 ≤ e - d := sub_nonneg.mpr hde
    have hcd : c < d := by
      by_contra hnot
      have hgap : d - c ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hfirst : (d - c) * x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hgap hx0
      have hsecond : 0 ≤ (e - d) * w := mul_nonneg hq hw0
      nlinarith
    let t : ℝ := d - c
    have ht : 0 < t := by
      dsimp [t]
      exact sub_pos.mpr hcd
    have hEarDrop : d ≤ t * x := by
      dsimp [t]
      have hsecond : 0 ≤ (e - d) * w := mul_nonneg hq hw0
      nlinarith
    have hxReciprocal : d / t ≤ x := by
      rw [div_le_iff₀ ht]
      simpa [mul_comm] using hEarDrop
    have hxTransition' : 2 * d / a ≤ x := by
      rw [div_le_iff₀ ha]
      nlinarith

    have hTbd : T ≤ b * d := by
      have hprod : 0 ≤ (b - 1) * (d - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hJscaled : d ≤ d * J := by
      simpa using mul_le_mul_of_nonneg_left hJ1 (le_of_lt hd)
    have hCellXLower : b * x + d ≤ e * T := by
      rw [← hCellX]
      linarith
    have hCellXUpper : e * T ≤ e * (b * d) :=
      mul_le_mul_of_nonneg_left hTbd (le_of_lt he)
    have heLowerRaw : b * x + d ≤ e * (b * d) :=
      hCellXLower.trans hCellXUpper
    have heLower : x / d + 1 / b ≤ e := by
      have hdiv : (b * x + d) / (b * d) ≤ e := by
        rw [div_le_iff₀ (mul_pos hb hd)]
        simpa [mul_assoc, mul_left_comm, mul_comm] using heLowerRaw
      calc
        x / d + 1 / b = (b * x + d) / (b * d) := by
          field_simp [hb.ne', hd.ne'] <;> ring
        _ ≤ e := hdiv

    have hfJ : 1 ≤ f * J := by
      have := mul_le_mul hf1 hJ1 (by norm_num)
        (le_trans (by norm_num) hf1)
      simpa using this
    have heK : e ≤ e * K := by
      simpa using mul_le_mul_of_nonneg_left hK1 (le_of_lt he)
    have hyScaled : e + 1 ≤ b * y := by
      rw [hCellY]
      linarith
    have hyLower0 : (e + 1) / b ≤ y := by
      rw [div_le_iff₀ hb]
      simpa [mul_comm] using hyScaled
    have hyLower :
        x / (b * d) + 1 / b ^ 2 + 1 / b ≤ y := by
      have heLowerPlus : x / d + 1 / b + 1 ≤ e + 1 := by
        linarith
      have hdiv := div_le_div_of_nonneg_right heLowerPlus (le_of_lt hb)
      have hid :
          (x / d + 1 / b + 1) / b =
            x / (b * d) + 1 / b ^ 2 + 1 / b := by
        field_simp [hb.ne', hd.ne'] <;> ring
      rw [← hid]
      exact hdiv.trans hyLower0

    have hALower : (a + b) / c ≤ A := by
      exact (div_le_iff₀ hc).2
        (by simpa [mul_comm] using hAtransition)
    have hxMix1 :
        8 * d / (5 * a) + d / (5 * t) ≤ x := by
      calc
        8 * d / (5 * a) + d / (5 * t) =
            (4 : ℝ) / 5 * (2 * d / a) + (1 : ℝ) / 5 * (d / t) := by
          field_simp [ha.ne', ht.ne'] <;> ring
        _ ≤ (4 : ℝ) / 5 * x + (1 : ℝ) / 5 * x :=
          add_le_add
            (mul_le_mul_of_nonneg_left hxTransition' (by norm_num))
            (mul_le_mul_of_nonneg_left hxReciprocal (by norm_num))
        _ = x := by ring
    have hxMix1Expand :
        8 * c / (5 * a) + 8 * t / (5 * a) +
            c / (5 * t) + 1 / 5 ≤ x := by
      have hdc : d = c + t := by dsimp [t]; ring
      rw [hdc] at hxMix1
      convert hxMix1 using 1 <;>
        field_simp [ha.ne', ht.ne'] <;> ring
    have hxMix2Raw :
        4 * d / (5 * a) + 3 * d / (5 * t) ≤ x := by
      calc
        4 * d / (5 * a) + 3 * d / (5 * t) =
            (2 : ℝ) / 5 * (2 * d / a) + (3 : ℝ) / 5 * (d / t) := by
          field_simp [ha.ne', ht.ne'] <;> ring
        _ ≤ (2 : ℝ) / 5 * x + (3 : ℝ) / 5 * x :=
          add_le_add
            (mul_le_mul_of_nonneg_left hxTransition' (by norm_num))
            (mul_le_mul_of_nonneg_left hxReciprocal (by norm_num))
        _ = x := by ring
    have hxMix2 :
        4 / (5 * a * b) + 3 / (5 * b * t) ≤ x / (b * d) := by
      have hbd : 0 < b * d := mul_pos hb hd
      have hdiv := (div_le_div_iff_of_pos_right hbd).2 hxMix2Raw
      calc
        4 / (5 * a * b) + 3 / (5 * b * t) =
            (4 * d / (5 * a) + 3 * d / (5 * t)) / (b * d) := by
          field_simp [ha.ne', hb.ne', hd.ne', ht.ne'] <;> ring
        _ ≤ x / (b * d) := hdiv
    have hReduced :=
      hullSixTwoFourQ23Increasing_reduced ha1 hb1 hc1 hcd
    have hLower :
        (16 : ℝ) / 5 +
            hullSixTwoFourQ23IncreasingLaurent a b c t ≤
          A + C + w + x + y + Fp + a + c := by
      unfold hullSixTwoFourQ23IncreasingLaurent
      have hFloors : (3 : ℝ) ≤ C + w + Fp := by linarith
      have hALower' : a / c + b / c ≤ A := by
        calc
          a / c + b / c = (a + b) / c := by ring
          _ ≤ A := hALower
      linarith
    exact hReduced.trans_le hLower
  · have hed : e < d := lt_of_not_ge hde
    have hde' : e ≤ d := le_of_lt hed
    have hp : 0 ≤ d - e := sub_nonneg.mpr hde'
    have hfed : f < e := by
      by_contra hnot
      have hef : e ≤ f := le_of_not_gt hnot
      have hfirst : (e - d) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hde') hy0
      have hsecond : 0 ≤ (f - e) * x :=
        mul_nonneg (sub_nonneg.mpr hef) hx0
      nlinarith
    let k : ℝ := e - f
    have hk : 0 < k := by
      dsimp [k]
      exact sub_pos.mpr hfed

    have hALowerC : (a + b) / c ≤ A := by
      exact (div_le_iff₀ hc).2
        (by simpa [mul_comm] using hAtransition)
    have hALowerE : (a + b) / e - a + b ≤ A := by
      have hdiv : (a + b) / e ≤ A + a - b := by
        exact (div_le_iff₀ he).2
          (by simpa [mul_comm] using hVerticalTransition)
      linarith
    have hALower :
        (2 / 9 : ℝ) * ((a + b) / c) +
            (7 / 9 : ℝ) * ((a + b) / e - a + b) ≤ A := by
      nlinarith [hALowerC, hALowerE]

    have hwLower : (c + d) / b - c + d ≤ w := by
      have hdiv : (c + d) / b ≤ w + c - d := by
        exact (div_le_iff₀ hb).2
          (by simpa [mul_comm] using hwTransition)
      linarith
    have hxTop : (d + e) / a ≤ x := by
      exact (div_le_iff₀ ha).2
        (by simpa [mul_comm] using hxTransition)
    have hEarRewrite :
        (e - d) * y - (f - e) * x =
          k * x - (d - e) * y := by
      dsimp [k]
      ring
    rw [hEarRewrite] at hEar2
    have hpY : d - e ≤ (d - e) * y := by
      simpa using mul_le_mul_of_nonneg_left hy1 hp
    have hEarDrop : d ≤ k * x := by
      nlinarith
    have hxEar : d / k ≤ x := by
      rw [div_le_iff₀ hk]
      simpa [mul_comm] using hEarDrop
    have hxLower :
        (2 / 5 : ℝ) * ((d + e) / a) +
            (3 / 5 : ℝ) * (d / k) ≤ x := by
      nlinarith [hxTop, hxEar]

    have hfJ : f ≤ f * J := by
      simpa using mul_le_mul_of_nonneg_left hJ1 (le_of_lt hf)
    have heK : e ≤ e * K := by
      simpa using mul_le_mul_of_nonneg_left hK1 (le_of_lt he)
    have hyScaled : e + f ≤ b * y := by
      rw [hCellY]
      linarith
    have hyLower : (e + f) / b ≤ y := by
      rw [div_le_iff₀ hb]
      simpa [mul_comm] using hyScaled

    have hRawLower :
        2 + a + c +
            ((2 / 9 : ℝ) * ((a + b) / c) +
              (7 / 9 : ℝ) * ((a + b) / e - a + b)) +
            ((c + d) / b - c + d) +
            ((2 / 5 : ℝ) * ((d + e) / a) +
              (3 / 5 : ℝ) * (d / k)) +
            (e + f) / b ≤
          A + C + w + x + y + Fp + a + c := by
      linarith
    have hSlack :
        0 ≤ (d - e) *
          (1 + 3 / (5 * k) + 1 / b + 2 / (5 * a)) := by
      have hcoef :
          0 ≤ 1 + 3 / (5 * k) + 1 / b + 2 / (5 * a) := by
        positivity
      exact mul_nonneg hp hcoef
    have hIdentity :
        2 + a + c +
            ((2 / 9 : ℝ) * ((a + b) / c) +
              (7 / 9 : ℝ) * ((a + b) / e - a + b)) +
            ((c + d) / b - c + d) +
            ((2 / 5 : ℝ) * ((d + e) / a) +
              (3 / 5 : ℝ) * (d / k)) +
            (e + f) / b =
          hullSixTwoFourQ23DecreasingLaurent a b c e f k +
            (d - e) *
              (1 + 3 / (5 * k) + 1 / b + 2 / (5 * a)) := by
      have hek : e = f + k := by dsimp [k]; ring
      unfold hullSixTwoFourQ23DecreasingLaurent
      rw [hek]
      field_simp [ha.ne', hb.ne', hc.ne', he.ne', hk.ne',
        (add_pos hf hk).ne'] <;> ring
    have hLaurentLower :
        hullSixTwoFourQ23DecreasingLaurent a b c e f k ≤
          A + C + w + x + y + Fp + a + c := by
      rw [hIdentity] at hRawLower
      linarith
    have hLaurent := hullSixTwoFourQ23Decreasing_laurent_gt
      ha hb hc he hf hk hf1
    exact hLaurent.trans_le hLaurentLower

end Heilbronn8
