import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the positive-`Y13`, `e <= d` half of the `p = (0,3)` frontier

This helper is deliberately q-blind.  Geometry supplies two transitions from
the retained `X` frontier and the honest split `Y13 >= 1`; no other
cross-chord sign occurs in the statement or proof.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

noncomputable def hullSixTwoFour_p03Y13PosLeLaurent
    (b f s : ℝ) : ℝ :=
  2 * b / f + 2 * f / b + b / s + f / s + s / b

noncomputable def hullSixTwoFour_p03Y13PosLeTerm
    (b f s : ℝ) : Fin 5 → ℝ :=
  ![2 * b / f, 2 * f / b, b / s, f / s, s / b]

def hullSixTwoFour_p03Y13PosLeWeight : Fin 5 → ℕ :=
  ![3, 2, 1, 1, 2]

noncomputable def hullSixTwoFour_p03Y13PosLeConstant : ℝ :=
  2 / 27

theorem hullSixTwoFour_p03Y13PosLeWeight_pos
    (i : Fin 5) : 0 < hullSixTwoFour_p03Y13PosLeWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_p03Y13PosLeWeight]

theorem hullSixTwoFour_p03Y13PosLeWeight_sum :
    ∑ i, hullSixTwoFour_p03Y13PosLeWeight i = 9 := by
  norm_num [hullSixTwoFour_p03Y13PosLeWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_p03Y13PosLeTerm_nonneg
    {b f s : ℝ} (hb : 0 ≤ b) (hf : 0 ≤ f) (hs : 0 ≤ s)
    (i : Fin 5) :
    0 ≤ hullSixTwoFour_p03Y13PosLeTerm b f s i := by
  fin_cases i <;> simp [hullSixTwoFour_p03Y13PosLeTerm] <;> positivity

theorem hullSixTwoFour_p03Y13PosLeTerm_sum
    (b f s : ℝ) :
    ∑ i, hullSixTwoFour_p03Y13PosLeTerm b f s i =
      hullSixTwoFour_p03Y13PosLeLaurent b f s := by
  simp [hullSixTwoFour_p03Y13PosLeTerm,
    hullSixTwoFour_p03Y13PosLeLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_p03Y13PosLeTerm_product
    {b f s : ℝ} (hb : 0 < b) (hf : 0 < f) (hs : 0 < s) :
    (∏ i,
        (hullSixTwoFour_p03Y13PosLeTerm b f s i /
          (hullSixTwoFour_p03Y13PosLeWeight i : ℝ)) ^
            hullSixTwoFour_p03Y13PosLeWeight i) =
      hullSixTwoFour_p03Y13PosLeConstant := by
  simp [hullSixTwoFour_p03Y13PosLeTerm,
    hullSixTwoFour_p03Y13PosLeWeight, Fin.prod_univ_succ,
    hullSixTwoFour_p03Y13PosLeConstant]
  field_simp [hb.ne', hf.ne', hs.ne'] <;> ring

theorem hullSixTwoFour_p03Y13PosLeConstant_pos :
    0 < hullSixTwoFour_p03Y13PosLeConstant := by
  norm_num [hullSixTwoFour_p03Y13PosLeConstant]

theorem hullSixTwoFour_p03Y13PosLe_root_gap :
    (13 : ℝ) / 2 <
      9 * hullSixTwoFour_p03Y13PosLeConstant ^ ((9 : ℝ)⁻¹) := by
  have hpow : ((13 : ℝ) / 18) ^ 9 <
      hullSixTwoFour_p03Y13PosLeConstant := by
    norm_num [hullSixTwoFour_p03Y13PosLeConstant]
  have hpowRpow : ((13 : ℝ) / 18) ^ (9 : ℝ) <
      hullSixTwoFour_p03Y13PosLeConstant := by
    change ((13 : ℝ) / 18) ^ ((9 : ℕ) : ℝ) <
      hullSixTwoFour_p03Y13PosLeConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (13 : ℝ) / 18 <
      hullSixTwoFour_p03Y13PosLeConstant ^ ((9 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_p03Y13PosLeConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_p03Y13PosLe_laurent_gt
    {b f s : ℝ} (hb : 0 < b) (hf : 0 < f) (hs : 0 < s) :
    (13 : ℝ) / 2 < hullSixTwoFour_p03Y13PosLeLaurent b f s := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_p03Y13PosLeWeight
    (hullSixTwoFour_p03Y13PosLeTerm b f s)
    hullSixTwoFour_p03Y13PosLeWeight_pos
    (hullSixTwoFour_p03Y13PosLeTerm_nonneg
      (le_of_lt hb) (le_of_lt hf) (le_of_lt hs))
  rw [hullSixTwoFour_p03Y13PosLeWeight_sum,
    hullSixTwoFour_p03Y13PosLeTerm_product hb hf hs,
    hullSixTwoFour_p03Y13PosLeTerm_sum b f s] at hamgm
  exact hullSixTwoFour_p03Y13PosLe_root_gap.trans_le hamgm

/-- Honest scalar closure for the `Y13 >= 1`, `e <= d` half of the
`p = (0,3)` maximal-`q` frontier.  The geometric adapter should derive
`hfAp` from `Y13 >= 1` and the `Q` wrap, and `hbE2` from the retained
`X12 >= 1`, `X13 <= -1` signs. -/
theorem hullSixTwoFour_p03Y13Pos_e_le_d_scalar
    {a b d e f A Ap C E0 E1 E2 F X11 X12 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hd1 : 1 ≤ d)
    (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hE11 : 1 ≤ E1) (hE21 : 1 ≤ E2)
    (hed : e ≤ d) (hAp : Ap = A + a - b)
    (hfAp : a + b ≤ f * Ap) (hbE2 : e + f ≤ b * E2)
    (hF : a + f + 1 ≤ F)
    (hEar : e ≤ (e - f) * E1 + (e - d) * E2)
    (hRec : b * E1 = e * X11 - d * X12)
    (hX12 : 1 ≤ X12) (hHull : 1 ≤ C + E0 - X11) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hE10 : 0 ≤ E1 := le_trans zero_le_one hE11
  have hE20 : 0 ≤ E2 := le_trans zero_le_one hE21
  let s : ℝ := e - f
  have hs : 0 < s := by
    dsimp [s]
    by_contra hnot
    have hef : e - f ≤ 0 := le_of_not_gt hnot
    have hfirst : (e - f) * E1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hef hE10
    have hsecond : (e - d) * E2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hed) hE20
    nlinarith
  have hEarReduced : e ≤ s * E1 := by
    have hsecond : (e - d) * E2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hed) hE20
    dsimp [s]
    nlinarith [hEar]
  have hE1Lower : e / s ≤ E1 := by
    exact (div_le_iff₀ hs).2 (by simpa [mul_comm] using hEarReduced)

  have hdX12 : d ≤ d * X12 := by
    simpa using mul_le_mul_of_nonneg_left hX12 (le_of_lt hd)
  have hX11Upper : X11 ≤ C + E0 - 1 := by linarith [hHull]
  have heX11 : e * X11 ≤ e * (C + E0 - 1) :=
    mul_le_mul_of_nonneg_left hX11Upper (le_of_lt he)
  have hCentral0 : b * E1 + 2 * e ≤ e * (C + E0) := by
    nlinarith [hRec, hdX12, heX11, hed]
  have hbe : b * e ≤ b * (s * E1) :=
    mul_le_mul_of_nonneg_left hEarReduced (le_of_lt hb)
  have hCentralScaled : e * (b + 2 * s) ≤ e * (s * (C + E0)) := by
    calc
      e * (b + 2 * s) = b * e + 2 * s * e := by ring
      _ ≤ b * (s * E1) + 2 * s * e := by linarith
      _ = s * (b * E1 + 2 * e) := by ring
      _ ≤ s * (e * (C + E0)) :=
        mul_le_mul_of_nonneg_left hCentral0 (le_of_lt hs)
      _ = e * (s * (C + E0)) := by ring
  have hCentralScaled' : b + 2 * s ≤ s * (C + E0) :=
    le_of_mul_le_mul_left hCentralScaled he
  have hCentral : 2 + b / s ≤ C + E0 := by
    have hdiv : (2 * s + b) / s ≤ C + E0 := by
      exact (div_le_iff₀ hs).2 (by
        simpa [add_comm, mul_comm] using hCentralScaled')
    convert hdiv using 1 <;> field_simp [hs.ne'] <;> ring

  have hApLower : (a + b) / f ≤ Ap :=
    (div_le_iff₀ hf).2 (by simpa [mul_comm] using hfAp)
  have hTopTransition : b + (a + b) / f ≤ A + a := by
    rw [hAp] at hApLower
    linarith
  have hTopElementary :
      2 + 2 * b / f ≤ b + (a + b) / f + f := by
    apply le_of_mul_le_mul_right (a := f) _ hf
    field_simp [hf.ne']
    have hbf : 0 ≤ b * (f - 1) :=
      mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hf1)
    nlinarith [sq_nonneg (f - 1)]
  have hTop : 6 + 2 * b / f ≤ A + a + f + 4 := by
    linarith [hTopTransition, hTopElementary]

  have hE2Lower : (e + f) / b ≤ E2 :=
    (div_le_iff₀ hb).2 (by simpa [mul_comm] using hbE2)
  have heS : e / s = f / s + 1 := by
    rw [show e = f + s by dsimp [s]; ring, add_div, div_self hs.ne']
  have heB : (e + f) / b = 2 * f / b + s / b := by
    dsimp [s]
    field_simp [hb.ne'] <;> ring
  have hFanLower :
      A + a + f + 4 + b / s + f / s + 2 * f / b + s / b ≤
        A + C + E0 + E1 + E2 + F := by
    nlinarith [hCentral, hE1Lower, hE2Lower, hF, heS, heB]
  have hLaurent := hullSixTwoFour_p03Y13PosLe_laurent_gt hb hf hs
  dsimp [hullSixTwoFour_p03Y13PosLeLaurent] at hLaurent
  nlinarith [hTop, hFanLower]

end Heilbronn8.Survivors.Join
