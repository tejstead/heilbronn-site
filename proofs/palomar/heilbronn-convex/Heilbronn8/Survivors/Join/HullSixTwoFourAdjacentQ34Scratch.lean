import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM--GM closure for the adjacent q-blind `q = 34` chamber

This file isolates the normalized scalar argument for the last adjacent
transition in the `2 + 4` hull-six family.  The proof splits only on the
order of the two middle lower heights.  If `d < e`, the first lower ear
gives a nineteen-copy Laurent certificate.  If `e <= d`, the second lower
ear first forces `f < e`, and a sixteen-copy certificate closes the branch.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## The `d < e` certificate -/

/-- The eleven-term Laurent remainder in the increasing middle branch. -/
noncomputable def hullSixTwoFourQ34IncreasingLaurent
    (a b c p : ℝ) : ℝ :=
  a + c + a / c + b / c + p + 2 * c / b + p / b + c / p +
    c / a + p / a + 1 / a

/-- The eleven distinct terms of the nineteen-copy certificate. -/
noncomputable def hullSixTwoFourQ34IncreasingTerm
    (a b c p : ℝ) : Fin 11 → ℝ :=
  ![a, c, a / c, b / c, p, 2 * c / b, p / b, c / p,
    c / a, p / a, 1 / a]

/-- Multiplicities of total mass nineteen. -/
def hullSixTwoFourQ34IncreasingWeight : Fin 11 → ℕ :=
  ![1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3]

/-- The variable-free scaled product in the increasing branch. -/
noncomputable def hullSixTwoFourQ34IncreasingConstant : ℝ :=
  1 / ((2 : ℝ) ^ 9 * 3 ^ 6)

theorem hullSixTwoFourQ34Increasing_weight_pos
    (i : Fin 11) : 0 < hullSixTwoFourQ34IncreasingWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ34IncreasingWeight]

theorem hullSixTwoFourQ34Increasing_weight_sum :
    ∑ i, hullSixTwoFourQ34IncreasingWeight i = 19 := by
  norm_num [hullSixTwoFourQ34IncreasingWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ34Increasing_term_nonneg
    {a b c p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (i : Fin 11) :
    0 ≤ hullSixTwoFourQ34IncreasingTerm a b c p i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ34IncreasingTerm] <;>
    positivity

theorem hullSixTwoFourQ34Increasing_term_sum
    (a b c p : ℝ) :
    ∑ i, hullSixTwoFourQ34IncreasingTerm a b c p i =
      hullSixTwoFourQ34IncreasingLaurent a b c p := by
  simp [hullSixTwoFourQ34IncreasingTerm,
    hullSixTwoFourQ34IncreasingLaurent, Fin.sum_univ_succ] <;>
    ring

/-- The nineteen scaled terms have exact product `1 / (2^9 * 3^6)`. -/
theorem hullSixTwoFourQ34Increasing_term_product
    {a b c p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hp : 0 < p) :
    (∏ i,
        (hullSixTwoFourQ34IncreasingTerm a b c p i /
          (hullSixTwoFourQ34IncreasingWeight i : ℝ)) ^
            hullSixTwoFourQ34IncreasingWeight i) =
      hullSixTwoFourQ34IncreasingConstant := by
  simp [hullSixTwoFourQ34IncreasingTerm,
    hullSixTwoFourQ34IncreasingWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ34IncreasingConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hp.ne'] <;> ring

theorem hullSixTwoFourQ34Increasing_constant_pos :
    0 < hullSixTwoFourQ34IncreasingConstant := by
  norm_num [hullSixTwoFourQ34IncreasingConstant]

/-- The exact endpoint comparison is just `3^6 < 2^10`. -/
theorem hullSixTwoFourQ34Increasing_integer_gap :
    (3 : ℕ) ^ 6 < 2 ^ 10 := by
  norm_num

/-- The nineteen-copy AM--GM root is strictly larger than `19 / 2`. -/
theorem hullSixTwoFourQ34Increasing_root_gap :
    (19 : ℝ) / 2 <
      19 * hullSixTwoFourQ34IncreasingConstant ^ ((19 : ℝ)⁻¹) := by
  have hpow :
      ((1 : ℝ) / 2) ^ 19 <
        hullSixTwoFourQ34IncreasingConstant := by
    norm_num [hullSixTwoFourQ34IncreasingConstant]
  have hpowRpow :
      ((1 : ℝ) / 2) ^ (19 : ℝ) <
        hullSixTwoFourQ34IncreasingConstant := by
    change ((1 : ℝ) / 2) ^ ((19 : ℕ) : ℝ) <
      hullSixTwoFourQ34IncreasingConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (1 : ℝ) / 2 <
        hullSixTwoFourQ34IncreasingConstant ^ ((19 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ34Increasing_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- Exact Laurent inequality in the `d < e` branch. -/
theorem hullSixTwoFourQ34Increasing_laurent_gt
    {a b c p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hp : 0 < p) :
    (19 : ℝ) / 2 < hullSixTwoFourQ34IncreasingLaurent a b c p := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ34IncreasingWeight
    (hullSixTwoFourQ34IncreasingTerm a b c p)
    hullSixTwoFourQ34Increasing_weight_pos
    (hullSixTwoFourQ34Increasing_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt hp))
  rw [hullSixTwoFourQ34Increasing_weight_sum,
    hullSixTwoFourQ34Increasing_term_product ha hb hc hp] at hamgm
  rw [← hullSixTwoFourQ34Increasing_term_sum a b c p]
  exact hullSixTwoFourQ34Increasing_root_gap.trans_le hamgm

/-! ## The `e <= d` certificate -/

/-- The full reduced Laurent sum after writing `e = f + k`. -/
noncomputable def hullSixTwoFourQ34DecreasingLaurent
    (a b c f k : ℝ) : ℝ :=
  a / 3 + f + k + a / (3 * c) + b / (3 * c) +
    2 * a / (3 * f) + 2 * b / (3 * f) + 2 * b / 3 +
      c / b + f / b + k / b + f / k + 2 * f / a + k / a

/-- The twelve selected terms of the sixteen-copy certificate. -/
noncomputable def hullSixTwoFourQ34DecreasingTerm
    (a b c f k : ℝ) : Fin 12 → ℝ :=
  ![a / 3, f, k, b / (3 * c), 2 * a / (3 * f),
    2 * b / (3 * f), 2 * b / 3, c / b, f / b, k / b,
    f / k, 2 * f / a]

/-- Multiplicities of total mass sixteen. -/
def hullSixTwoFourQ34DecreasingWeight : Fin 12 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2]

/-- The variable-free part of the scaled product. -/
noncomputable def hullSixTwoFourQ34DecreasingConstant : ℝ :=
  1 / 2916

theorem hullSixTwoFourQ34Decreasing_weight_pos
    (i : Fin 12) : 0 < hullSixTwoFourQ34DecreasingWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ34DecreasingWeight]

theorem hullSixTwoFourQ34Decreasing_weight_sum :
    ∑ i, hullSixTwoFourQ34DecreasingWeight i = 16 := by
  norm_num [hullSixTwoFourQ34DecreasingWeight, Fin.sum_univ_succ]

theorem hullSixTwoFourQ34Decreasing_term_nonneg
    {a b c f k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hf : 0 ≤ f) (hk : 0 ≤ k)
    (i : Fin 12) :
    0 ≤ hullSixTwoFourQ34DecreasingTerm a b c f k i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ34DecreasingTerm] <;>
    positivity

theorem hullSixTwoFourQ34Decreasing_term_sum
    (a b c f k : ℝ) :
    ∑ i, hullSixTwoFourQ34DecreasingTerm a b c f k i =
      a / 3 + f + k + b / (3 * c) + 2 * a / (3 * f) +
        2 * b / (3 * f) + 2 * b / 3 + c / b + f / b +
          k / b + f / k + 2 * f / a := by
  simp [hullSixTwoFourQ34DecreasingTerm, Fin.sum_univ_succ] <;>
    ring

/-- The sixteen scaled terms have product `(1 / 2916) * f^5`. -/
theorem hullSixTwoFourQ34Decreasing_term_product
    {a b c f k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (hk : 0 < k) :
    (∏ i,
        (hullSixTwoFourQ34DecreasingTerm a b c f k i /
          (hullSixTwoFourQ34DecreasingWeight i : ℝ)) ^
            hullSixTwoFourQ34DecreasingWeight i) =
      hullSixTwoFourQ34DecreasingConstant * f ^ 5 := by
  simp [hullSixTwoFourQ34DecreasingTerm,
    hullSixTwoFourQ34DecreasingWeight, Fin.prod_univ_succ,
    hullSixTwoFourQ34DecreasingConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hf.ne', hk.ne'] <;> ring

theorem hullSixTwoFourQ34Decreasing_constant_pos :
    0 < hullSixTwoFourQ34DecreasingConstant := by
  norm_num [hullSixTwoFourQ34DecreasingConstant]

/-- Exact integer endpoint for the sixteen-copy certificate. -/
theorem hullSixTwoFourQ34Decreasing_integer_gap :
    3 ^ 6 * (19 : ℕ) ^ 16 < 2 ^ 78 := by
  norm_num

/-- The variable-free AM--GM root is strictly larger than `19 / 2`. -/
theorem hullSixTwoFourQ34Decreasing_root_gap :
    (19 : ℝ) / 2 <
      16 * hullSixTwoFourQ34DecreasingConstant ^ ((16 : ℝ)⁻¹) := by
  have hpow :
      ((19 : ℝ) / 32) ^ 16 <
        hullSixTwoFourQ34DecreasingConstant := by
    norm_num [hullSixTwoFourQ34DecreasingConstant]
  have hpowRpow :
      ((19 : ℝ) / 32) ^ (16 : ℝ) <
        hullSixTwoFourQ34DecreasingConstant := by
    change ((19 : ℝ) / 32) ^ ((16 : ℕ) : ℝ) <
      hullSixTwoFourQ34DecreasingConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (19 : ℝ) / 32 <
        hullSixTwoFourQ34DecreasingConstant ^ ((16 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourQ34Decreasing_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- Exact Laurent inequality in the `e <= d` branch. -/
theorem hullSixTwoFourQ34Decreasing_laurent_gt
    {a b c f k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (hk : 0 < k) (hf1 : 1 ≤ f) :
    (19 : ℝ) / 2 < hullSixTwoFourQ34DecreasingLaurent a b c f k := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ34DecreasingWeight
    (hullSixTwoFourQ34DecreasingTerm a b c f k)
    hullSixTwoFourQ34Decreasing_weight_pos
    (hullSixTwoFourQ34Decreasing_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hf) (le_of_lt hk))
  rw [hullSixTwoFourQ34Decreasing_weight_sum,
    hullSixTwoFourQ34Decreasing_term_product ha hb hc hf hk] at hamgm
  have hfPow : (1 : ℝ) ≤ f ^ 5 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hf1 5)
  have hProductFloor :
      hullSixTwoFourQ34DecreasingConstant ≤
        hullSixTwoFourQ34DecreasingConstant * f ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hfPow
      (le_of_lt hullSixTwoFourQ34Decreasing_constant_pos)
    simpa using h
  have hRootFloor :
      hullSixTwoFourQ34DecreasingConstant ^ ((16 : ℝ)⁻¹) ≤
        (hullSixTwoFourQ34DecreasingConstant * f ^ 5) ^ ((16 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixTwoFourQ34Decreasing_constant_pos)
      hProductFloor (by norm_num)
  have hSelected :
      (19 : ℝ) / 2 <
        ∑ i, hullSixTwoFourQ34DecreasingTerm a b c f k i :=
    hullSixTwoFourQ34Decreasing_root_gap.trans_le
      ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)
  rw [hullSixTwoFourQ34Decreasing_term_sum] at hSelected
  have homit1 : 0 ≤ a / (3 * c) := by positivity
  have homit2 : 0 ≤ k / a := by positivity
  unfold hullSixTwoFourQ34DecreasingLaurent
  linarith

/-! ## Raw q34 packet -/

/--
Complete scalar closure for the adjacent q-blind `q = 34` packet.

The variables `w,x,y` are the three consecutive primed lower-fan edges.
The two displayed ear recurrences and the top-cell lower bound are the only
cell information used by this scalar theorem.
-/
theorem hullSixTwoFourQ34_scalar
    {a b c d e f A C w x y Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A) (hC1 : 1 ≤ C)
    (hw1 : 1 ≤ w) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y)
    (hFp1 : 1 ≤ Fp)
    (hAtransition : a + b ≤ c * A)
    (hwTransition : c + d ≤ b * (w + c - d))
    (hVerticalTransition : a + b ≤ f * (A + a - b))
    (hTop : e + f ≤ a * y)
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

  by_cases hde : d < e
  · let p : ℝ := d - c
    have hq : 0 < e - d := sub_pos.mpr hde
    have hp : 0 < p := by
      by_contra hnot
      have hp0 : p ≤ 0 := le_of_not_gt hnot
      have hfirst : p * x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hp0 hx0
      have hsecond : 0 ≤ (e - d) * w :=
        mul_nonneg (le_of_lt hq) hw0
      dsimp [p] at hfirst
      nlinarith
    have hcd : c < d := by
      exact sub_pos.mp (by simpa [p] using hp)
    have hALower : a / c + b / c ≤ A := by
      have h : (a + b) / c ≤ A :=
        (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAtransition)
      calc
        a / c + b / c = (a + b) / c := by ring
        _ ≤ A := h
    have hWBase : (2 * c + p) / b ≤ w - p := by
      rw [div_le_iff₀ hb]
      dsimp [p]
      nlinarith
    have hWLower : p + 2 * c / b + p / b ≤ w := by
      have hsplit : (2 * c + p) / b = 2 * c / b + p / b := by ring
      rw [hsplit] at hWBase
      linarith
    have hXBase : d ≤ p * x := by
      have hsecond : 0 ≤ (e - d) * w :=
        mul_nonneg (le_of_lt hq) hw0
      dsimp [p]
      nlinarith
    have hXLower : 1 + c / p ≤ x := by
      have hdiv : d / p ≤ x := by
        rw [div_le_iff₀ hp]
        simpa [mul_comm] using hXBase
      have hid : d / p = 1 + c / p := by
        apply (div_eq_iff hp.ne').2
        rw [add_mul, one_mul, div_mul_cancel₀ c hp.ne']
        dsimp [p]
        ring
      rwa [hid] at hdiv
    have hYBase : (e + f) / a ≤ y := by
      exact (div_le_iff₀ ha).2
        (by simpa [mul_comm] using hTop)
    have hYLower : (c + p + 1) / a < y := by
      have hnum : c + p + 1 < e + f := by
        dsimp [p]
        linarith
      have hdiv : (c + p + 1) / a < (e + f) / a := by
        exact (div_lt_div_iff_of_pos_right ha).2 hnum
      exact hdiv.trans_le hYBase
    have hYTerms : c / a + p / a + 1 / a < y := by
      calc
        c / a + p / a + 1 / a = (c + p + 1) / a := by ring
        _ < y := hYLower
    have hAC :
        a / c + b / c + 1 ≤ A + C :=
      add_le_add hALower hC1
    have hACW :
        a / c + b / c + 1 + (p + 2 * c / b + p / b) ≤
          A + C + w :=
      add_le_add hAC hWLower
    have hACWX :
        a / c + b / c + 1 + (p + 2 * c / b + p / b) +
            (1 + c / p) ≤
          A + C + w + x :=
      add_le_add hACW hXLower
    have hACWXY :
        a / c + b / c + 1 + (p + 2 * c / b + p / b) +
              (1 + c / p) + (c / a + p / a + 1 / a) <
          A + C + w + x + y :=
      add_lt_add_of_le_of_lt hACWX hYTerms
    have hACWXYF :
        a / c + b / c + 1 + (p + 2 * c / b + p / b) +
                (1 + c / p) + (c / a + p / a + 1 / a) + 1 <
          A + C + w + x + y + Fp :=
      add_lt_add_of_lt_of_le hACWXY hFp1
    have hAll :
        a / c + b / c + 1 + (p + 2 * c / b + p / b) +
                  (1 + c / p) + (c / a + p / a + 1 / a) + 1 + a + c <
          A + C + w + x + y + Fp + a + c :=
      by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_lt_add_right (add_lt_add_right hACWXYF a) c
    have hLaurent :=
      hullSixTwoFourQ34Increasing_laurent_gt ha hb hc hp
    have hLower :
        3 + hullSixTwoFourQ34IncreasingLaurent a b c p <
          A + C + w + x + y + Fp + a + c := by
      calc
        3 + hullSixTwoFourQ34IncreasingLaurent a b c p =
            a / c + b / c + 1 + (p + 2 * c / b + p / b) +
                (1 + c / p) + (c / a + p / a + 1 / a) + 1 + a + c := by
              unfold hullSixTwoFourQ34IncreasingLaurent
              ring
        _ < A + C + w + x + y + Fp + a + c := hAll
    calc
      (25 : ℝ) / 2 = 3 + (19 : ℝ) / 2 := by norm_num
      _ < 3 + hullSixTwoFourQ34IncreasingLaurent a b c p :=
        by simpa [add_comm] using add_lt_add_left hLaurent 3
      _ < A + C + w + x + y + Fp + a + c := hLower
  · have hed : e ≤ d := le_of_not_gt hde
    have hef : f < e := by
      by_contra hnot
      have hef0 : e ≤ f := le_of_not_gt hnot
      have hfirst : (e - d) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hed) hy0
      have hsecond : 0 ≤ (f - e) * x :=
        mul_nonneg (sub_nonneg.mpr hef0) hx0
      nlinarith
    let k : ℝ := e - f
    have hk : 0 < k := by
      dsimp [k]
      exact sub_pos.mpr hef
    have hXBase : d ≤ k * x := by
      have hgap : 0 ≤ d - e := sub_nonneg.mpr hed
      have hyShift : d - e ≤ (d - e) * y := by
        have := mul_le_mul_of_nonneg_left hy1 hgap
        simpa using this
      dsimp [k]
      nlinarith
    have hXLower : d / k ≤ x := by
      rw [div_le_iff₀ hk]
      simpa [mul_comm] using hXBase
    have hWBase : (c + d) / b ≤ w + c - d := by
      rw [div_le_iff₀ hb]
      simpa [mul_comm] using hwTransition
    have hCWLower : d + (c + d) / b ≤ c + w := by
      linarith
    have hYLower : (e + f) / a ≤ y := by
      exact (div_le_iff₀ ha).2
        (by simpa [mul_comm] using hTop)
    have hALowerC : (a + b) / c ≤ A := by
      exact (div_le_iff₀ hc).2
        (by simpa [mul_comm] using hAtransition)
    have hALowerF : (a + b) / f - a + b ≤ A := by
      have hbase : (a + b) / f ≤ A + a - b := by
        exact (div_le_iff₀ hf).2
          (by simpa [mul_comm] using hVerticalTransition)
      linarith
    have hAConvex :
        ((a + b) / c) / 3 +
            2 * ((a + b) / f - a + b) / 3 ≤ A := by
      linarith
    have hDdiv : e / k ≤ d / k := by
      exact (div_le_div_iff_of_pos_right hk).2 hed
    have hDBdiv : (c + e) / b ≤ (c + d) / b := by
      exact (div_le_div_iff_of_pos_right hb).2 (by linarith)
    have hRawLower :
        2 + a + e + ((a + b) / c) / 3 +
            2 * ((a + b) / f - a + b) / 3 +
              (c + e) / b + e / k + (e + f) / a ≤
          A + C + w + x + y + Fp + a + c := by
      linarith
    have hLaurent :=
      hullSixTwoFourQ34Decreasing_laurent_gt ha hb hc hf hk hf1
    have hRewrite :
        2 + a + e + ((a + b) / c) / 3 +
              2 * ((a + b) / f - a + b) / 3 +
                (c + e) / b + e / k + (e + f) / a =
          3 + hullSixTwoFourQ34DecreasingLaurent a b c f k := by
      have he : e = k + f := by
        dsimp [k]
        ring
      have hek : e / k = 1 + f / k := by
        rw [he, add_div, div_self hk.ne']
      have hdiv3 (u v : ℝ) :
          u / (3 * v) = (u / v) / 3 := by
        rw [div_div, mul_comm v 3]
      rw [hek, he]
      unfold hullSixTwoFourQ34DecreasingLaurent
      rw [hdiv3 a c, hdiv3 b c, hdiv3 (2 * a) f,
        hdiv3 (2 * b) f]
      ring
    rw [hRewrite] at hRawLower
    linarith

end Heilbronn8
