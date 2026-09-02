import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Compact AM--GM closure for the q-blind `q = 04` chamber

The q04 table is `RRRR / LMMM`.  Its genuine first lower-fan transition is
`c + d <= b * (x + c - d)`, where `x` is the first `Q`-fan lower edge.
The tempting q12 transition `c + d <= a*x` is false here.  For example,
heights `(1,20,1,10,10,7)` and gaps `(3,1/20,1/20,1/30,2/35)` satisfy the
q04 floors and ears, but `a*x=10 < 11=c+d`; the true transition has value 20.

Keeping the q04-specific cell inequality
`b*(a+c+1) <= c*A-a*C` leaves two small Laurent sums.  Their eleven-copy
and sixteen-copy certificates need no three-cell recurrence, vertical
transition, or compact height cap.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

/-! ## The orientation `d <= e` -/

noncomputable def hullSixTwoFour_q04_geLaurent
    (a b c t : ℝ) : ℝ :=
  a + c + a / c + a * b / c + b + b / c + t +
    2 * c / b + t / b + c / t

noncomputable def hullSixTwoFour_q04_geTerm
    (a b c t : ℝ) : Fin 10 → ℝ :=
  ![a, c, a / c, a * b / c, b, b / c, t,
    2 * c / b, t / b, c / t]

def hullSixTwoFour_q04_geWeight : Fin 10 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2]

noncomputable def hullSixTwoFour_q04_geConstant : ℝ := 1 / 2

theorem hullSixTwoFour_q04_geWeight_pos
    (i : Fin 10) : 0 < hullSixTwoFour_q04_geWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_q04_geWeight]

theorem hullSixTwoFour_q04_geWeight_sum :
    ∑ i, hullSixTwoFour_q04_geWeight i = 11 := by
  norm_num [hullSixTwoFour_q04_geWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_q04_geTerm_nonneg
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin 10) :
    0 ≤ hullSixTwoFour_q04_geTerm a b c t i := by
  fin_cases i <;> simp [hullSixTwoFour_q04_geTerm] <;> positivity

theorem hullSixTwoFour_q04_geTerm_sum
    (a b c t : ℝ) :
    ∑ i, hullSixTwoFour_q04_geTerm a b c t i =
      hullSixTwoFour_q04_geLaurent a b c t := by
  simp [hullSixTwoFour_q04_geTerm, hullSixTwoFour_q04_geLaurent,
    Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_q04_geTerm_product
    {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFour_q04_geTerm a b c t i /
          (hullSixTwoFour_q04_geWeight i : ℝ)) ^
            hullSixTwoFour_q04_geWeight i) =
      hullSixTwoFour_q04_geConstant * a ^ 3 * b * c := by
  simp [hullSixTwoFour_q04_geTerm, hullSixTwoFour_q04_geWeight,
    Fin.prod_univ_succ, hullSixTwoFour_q04_geConstant]
  field_simp [ha.ne', hb.ne', hc.ne', ht.ne'] <;> ring

theorem hullSixTwoFour_q04_geConstant_pos :
    0 < hullSixTwoFour_q04_geConstant := by
  norm_num [hullSixTwoFour_q04_geConstant]

theorem hullSixTwoFour_q04_ge_integer_gap :
    2 * (17 : ℕ) ^ 11 < 22 ^ 11 := by norm_num

theorem hullSixTwoFour_q04_ge_root_gap :
    (17 : ℝ) / 2 <
      11 * hullSixTwoFour_q04_geConstant ^ ((11 : ℝ)⁻¹) := by
  have hpow : ((17 : ℝ) / 22) ^ 11 <
      hullSixTwoFour_q04_geConstant := by
    norm_num [hullSixTwoFour_q04_geConstant]
  have hpowRpow : ((17 : ℝ) / 22) ^ (11 : ℝ) <
      hullSixTwoFour_q04_geConstant := by
    change ((17 : ℝ) / 22) ^ ((11 : ℕ) : ℝ) <
      hullSixTwoFour_q04_geConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (17 : ℝ) / 22 <
      hullSixTwoFour_q04_geConstant ^ ((11 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_q04_geConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_q04_ge_laurent_gt
    {a b c t : ℝ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hc1 : 1 ≤ c) (ht : 0 < t) :
    (17 : ℝ) / 2 < hullSixTwoFour_q04_geLaurent a b c t := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_q04_geWeight (hullSixTwoFour_q04_geTerm a b c t)
    hullSixTwoFour_q04_geWeight_pos
    (hullSixTwoFour_q04_geTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt ht))
  rw [hullSixTwoFour_q04_geWeight_sum,
    hullSixTwoFour_q04_geTerm_product ha hb hc ht] at hamgm
  have haPow : (1 : ℝ) ≤ a ^ 3 := one_le_pow₀ ha1
  have hab : (1 : ℝ) ≤ a ^ 3 * b := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ a ^ 3 * b :=
        mul_le_mul haPow hb1 (by norm_num) (by positivity)
  have hfactor : (1 : ℝ) ≤ a ^ 3 * b * c := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (a ^ 3 * b) * c :=
        mul_le_mul hab hc1 (by norm_num) (by positivity)
  have hProductFloor : hullSixTwoFour_q04_geConstant ≤
      hullSixTwoFour_q04_geConstant * a ^ 3 * b * c := by
    have h := mul_le_mul_of_nonneg_left hfactor
      (le_of_lt hullSixTwoFour_q04_geConstant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixTwoFour_q04_geConstant ^ ((11 : ℝ)⁻¹) ≤
        (hullSixTwoFour_q04_geConstant * a ^ 3 * b * c) ^ ((11 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (le_of_lt hullSixTwoFour_q04_geConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFour_q04_geTerm_sum a b c t]
  exact hullSixTwoFour_q04_ge_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## The orientation `e < d` -/

noncomputable def hullSixTwoFour_q04_ltLaurent
    (a b c f k : ℝ) : ℝ :=
  a + f + k + a / c + a * b / c + b + b / c + c / b +
    f / b + k / b + f / k

noncomputable def hullSixTwoFour_q04_ltTerm
    (a b c f k : ℝ) : Fin 11 → ℝ :=
  ![a, f, k, a / c, a * b / c, b, b / c, c / b,
    f / b, k / b, f / k]

def hullSixTwoFour_q04_ltWeight : Fin 11 → ℕ :=
  ![1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2]

noncomputable def hullSixTwoFour_q04_ltConstant : ℝ := 1 / 2916

theorem hullSixTwoFour_q04_ltWeight_pos
    (i : Fin 11) : 0 < hullSixTwoFour_q04_ltWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_q04_ltWeight]

theorem hullSixTwoFour_q04_ltWeight_sum :
    ∑ i, hullSixTwoFour_q04_ltWeight i = 16 := by
  norm_num [hullSixTwoFour_q04_ltWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_q04_ltTerm_nonneg
    {a b c f k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hf : 0 ≤ f) (hk : 0 ≤ k)
    (i : Fin 11) :
    0 ≤ hullSixTwoFour_q04_ltTerm a b c f k i := by
  fin_cases i <;> simp [hullSixTwoFour_q04_ltTerm] <;> positivity

theorem hullSixTwoFour_q04_ltTerm_sum
    (a b c f k : ℝ) :
    ∑ i, hullSixTwoFour_q04_ltTerm a b c f k i =
      hullSixTwoFour_q04_ltLaurent a b c f k := by
  simp [hullSixTwoFour_q04_ltTerm, hullSixTwoFour_q04_ltLaurent,
    Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_q04_ltTerm_product
    {a b c f k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hf : 0 < f) (hk : 0 < k) :
    (∏ i,
        (hullSixTwoFour_q04_ltTerm a b c f k i /
          (hullSixTwoFour_q04_ltWeight i : ℝ)) ^
            hullSixTwoFour_q04_ltWeight i) =
      hullSixTwoFour_q04_ltConstant * a ^ 3 * f ^ 4 := by
  simp [hullSixTwoFour_q04_ltTerm, hullSixTwoFour_q04_ltWeight,
    Fin.prod_univ_succ, hullSixTwoFour_q04_ltConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hf.ne', hk.ne'] <;> ring

theorem hullSixTwoFour_q04_ltConstant_pos :
    0 < hullSixTwoFour_q04_ltConstant := by
  norm_num [hullSixTwoFour_q04_ltConstant]

theorem hullSixTwoFour_q04_lt_integer_gap :
    2916 * (17 : ℕ) ^ 16 < 32 ^ 16 := by norm_num

theorem hullSixTwoFour_q04_lt_root_gap :
    (17 : ℝ) / 2 <
      16 * hullSixTwoFour_q04_ltConstant ^ ((16 : ℝ)⁻¹) := by
  have hpow : ((17 : ℝ) / 32) ^ 16 <
      hullSixTwoFour_q04_ltConstant := by
    norm_num [hullSixTwoFour_q04_ltConstant]
  have hpowRpow : ((17 : ℝ) / 32) ^ (16 : ℝ) <
      hullSixTwoFour_q04_ltConstant := by
    change ((17 : ℝ) / 32) ^ ((16 : ℕ) : ℝ) <
      hullSixTwoFour_q04_ltConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (17 : ℝ) / 32 <
      hullSixTwoFour_q04_ltConstant ^ ((16 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_q04_ltConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_q04_lt_laurent_gt
    {a b c f k : ℝ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hc : 0 < c) (hf1 : 1 ≤ f) (hk : 0 < k) :
    (17 : ℝ) / 2 < hullSixTwoFour_q04_ltLaurent a b c f k := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_q04_ltWeight (hullSixTwoFour_q04_ltTerm a b c f k)
    hullSixTwoFour_q04_ltWeight_pos
    (hullSixTwoFour_q04_ltTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hf) (le_of_lt hk))
  rw [hullSixTwoFour_q04_ltWeight_sum,
    hullSixTwoFour_q04_ltTerm_product ha hb hc hf hk] at hamgm
  have hfactor : (1 : ℝ) ≤ a ^ 3 * f ^ 4 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ a ^ 3 * f ^ 4 :=
        mul_le_mul (one_le_pow₀ ha1) (one_le_pow₀ hf1)
          (by norm_num) (by positivity)
  have hProductFloor : hullSixTwoFour_q04_ltConstant ≤
      hullSixTwoFour_q04_ltConstant * a ^ 3 * f ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hfactor
      (le_of_lt hullSixTwoFour_q04_ltConstant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixTwoFour_q04_ltConstant ^ ((16 : ℝ)⁻¹) ≤
        (hullSixTwoFour_q04_ltConstant * a ^ 3 * f ^ 4) ^ ((16 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (le_of_lt hullSixTwoFour_q04_ltConstant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFour_q04_ltTerm_sum a b c f k]
  exact hullSixTwoFour_q04_lt_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-! ## Raw corrected q04 packet -/

/-- Raw normalized q04 closure using the genuine bottom-row transition. -/
theorem hullSixTwoFour_q04_scalar
    {a b c d e f A C x y z Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hC1 : 1 ≤ C) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y)
    (hz1 : 1 ≤ z) (hFp1 : 1 ≤ Fp)
    (hExtra : b * (a + c + 1) ≤ c * A - a * C)
    (hxTransition : c + d ≤ b * (x + c - d))
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    (25 : ℝ) / 2 < A + C + x + y + z + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hy0 : 0 ≤ y := le_trans zero_le_one hy1
  have hAraw : a + b * (a + c + 1) ≤ c * A := by
    have hAC : a ≤ a * C := by
      simpa using mul_le_mul_of_nonneg_left hC1 (le_of_lt ha)
    nlinarith
  have hALower : a / c + a * b / c + b + b / c ≤ A := by
    have hdiv : (a + b * (a + c + 1)) / c ≤ A :=
      (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAraw)
    calc
      a / c + a * b / c + b + b / c =
          (a + b * (a + c + 1)) / c := by
        field_simp [hc.ne'] <;> ring
      _ ≤ A := hdiv
  have hXLower : d - c + (c + d) / b ≤ x := by
    have hdiv : (c + d) / b ≤ x + c - d :=
      (div_le_iff₀ hb).2 (by simpa [mul_comm] using hxTransition)
    linarith

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
    have ht : 0 < t := by dsimp [t]; exact sub_pos.mpr hcd
    have hYmul : d ≤ t * y := by
      dsimp [t]
      nlinarith [mul_nonneg hq hx0]
    have hY : d / t ≤ y :=
      (div_le_iff₀ ht).2 (by simpa [mul_comm] using hYmul)
    have hYSplit : 1 + c / t ≤ y := by
      have hshape : 1 + c / t = d / t := by
        field_simp [ht.ne']
        dsimp [t]
        ring
      rw [hshape]
      exact hY
    have hXSplit : t + 2 * c / b + t / b ≤ x := by
      have hshape : t + 2 * c / b + t / b =
          d - c + (c + d) / b := by
        dsimp [t]
        field_simp [hb.ne'] <;> ring
      rw [hshape]
      exact hXLower
    have hLower : 4 + hullSixTwoFour_q04_geLaurent a b c t ≤
        A + C + x + y + z + Fp + a + c := by
      have hdecomp : 4 + hullSixTwoFour_q04_geLaurent a b c t =
          3 + a + c + (a / c + a * b / c + b + b / c) +
            (t + 2 * c / b + t / b) + (1 + c / t) := by
        dsimp [hullSixTwoFour_q04_geLaurent]
        ring
      rw [hdecomp]
      linarith
    have hLaurent := hullSixTwoFour_q04_ge_laurent_gt ha1 hb1 hc1 ht
    linarith

  · have hed : e < d := lt_of_not_ge hde
    have hfd : f < e := by
      by_contra hnot
      have hef : e ≤ f := le_of_not_gt hnot
      have hfirst : (e - d) * z < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr hed)
          (lt_of_lt_of_le zero_lt_one hz1)
      have hsecond : 0 ≤ (f - e) * y :=
        mul_nonneg (sub_nonneg.mpr hef) hy0
      nlinarith
    let k : ℝ := e - f
    have hk : 0 < k := by dsimp [k]; exact sub_pos.mpr hfd
    have hYmul : d ≤ k * y := by
      dsimp [k]
      have hdz : 0 ≤ (d - e) * (z - 1) :=
        mul_nonneg (sub_nonneg.mpr (le_of_lt hed))
          (sub_nonneg.mpr hz1)
      nlinarith
    have hY : e / k < y := by
      have hdiv : e / k < d / k :=
        (div_lt_div_iff_of_pos_right hk).2 hed
      have hdy : d / k ≤ y :=
        (div_le_iff₀ hk).2 (by simpa [mul_comm] using hYmul)
      exact hdiv.trans_le hdy
    have hYSplit : 1 + f / k < y := by
      have hshape : 1 + f / k = e / k := by
        field_simp [hk.ne']
        dsimp [k]
        ring
      rw [hshape]
      exact hY
    have hXAtE : e - c + (c + e) / b ≤ x := by
      have hmono : e - c + (c + e) / b ≤
          d - c + (c + d) / b := by
        have hdiv : (c + e) / b ≤ (c + d) / b :=
          (div_le_div_iff_of_pos_right hb).2 (by linarith)
        linarith
      exact hmono.trans hXLower
    have hXSplit : f + k - c + (c + f + k) / b ≤ x := by
      have hshape : f + k - c + (c + f + k) / b =
          e - c + (c + e) / b := by
        dsimp [k]
        ring
      rw [hshape]
      exact hXAtE
    have hLower : 4 + hullSixTwoFour_q04_ltLaurent a b c f k <
        A + C + x + y + z + Fp + a + c := by
      have hdecomp : 4 + hullSixTwoFour_q04_ltLaurent a b c f k =
          3 + a + c + (a / c + a * b / c + b + b / c) +
            (f + k - c + (c + f + k) / b) + (1 + f / k) := by
        dsimp [hullSixTwoFour_q04_ltLaurent]
        ring
      rw [hdecomp]
      linarith
    have hLaurent := hullSixTwoFour_q04_lt_laurent_gt
      ha1 hb1 hc hf1 hk
    linarith

end Heilbronn8.Survivors.Join
