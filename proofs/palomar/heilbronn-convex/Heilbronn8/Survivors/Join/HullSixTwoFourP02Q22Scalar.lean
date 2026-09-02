import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the exact `p = 02`, `q = 22` packet

The negative `Y12` cell strengthens the middle unprimed recurrence.  Together
with the first two `P`-based recurrences and the closing `Q`-fan floor this
leaves a nine-term Laurent sum.  A thirteen-copy weighted AM--GM certificate
has scaled product `a^3 / 108`, so the height floor `a >= 1` is enough to
close the packet.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

noncomputable def hullSixTwoFourP02Q22Laurent
    (a b c d : ℝ) : ℝ :=
  a + d + 2 * d / b + 1 / b + b / d + c / d +
    a * b / (c * d) + a / d + b / c

noncomputable def hullSixTwoFourP02Q22Term
    (a b c d : ℝ) : Fin 9 → ℝ :=
  ![a, d, 2 * d / b, 1 / b, b / d, c / d,
    a * b / (c * d), a / d, b / c]

def hullSixTwoFourP02Q22Weight : Fin 9 → ℕ :=
  ![1, 3, 2, 1, 1, 2, 1, 1, 1]

noncomputable def hullSixTwoFourP02Q22Constant : ℝ := 1 / 108

theorem hullSixTwoFourP02Q22_weight_pos
    (i : Fin 9) : 0 < hullSixTwoFourP02Q22Weight i := by
  fin_cases i <;> norm_num [hullSixTwoFourP02Q22Weight]

theorem hullSixTwoFourP02Q22_weight_sum :
    ∑ i, hullSixTwoFourP02Q22Weight i = 13 := by
  norm_num [hullSixTwoFourP02Q22Weight, Fin.sum_univ_succ]

theorem hullSixTwoFourP02Q22_term_nonneg
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (i : Fin 9) :
    0 ≤ hullSixTwoFourP02Q22Term a b c d i := by
  fin_cases i <;>
    simp [hullSixTwoFourP02Q22Term] <;>
    positivity

theorem hullSixTwoFourP02Q22_term_sum
    (a b c d : ℝ) :
    ∑ i, hullSixTwoFourP02Q22Term a b c d i =
      hullSixTwoFourP02Q22Laurent a b c d := by
  simp [hullSixTwoFourP02Q22Term, hullSixTwoFourP02Q22Laurent,
    Fin.sum_univ_succ] <;>
    ring

theorem hullSixTwoFourP02Q22_term_product
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (∏ i,
        (hullSixTwoFourP02Q22Term a b c d i /
          (hullSixTwoFourP02Q22Weight i : ℝ)) ^
            hullSixTwoFourP02Q22Weight i) =
      hullSixTwoFourP02Q22Constant * a ^ 3 := by
  simp [hullSixTwoFourP02Q22Term, hullSixTwoFourP02Q22Weight,
    Fin.prod_univ_succ, hullSixTwoFourP02Q22Constant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne'] <;> ring

theorem hullSixTwoFourP02Q22_constant_pos :
    0 < hullSixTwoFourP02Q22Constant := by
  norm_num [hullSixTwoFourP02Q22Constant]

theorem hullSixTwoFourP02Q22_integer_gap :
    108 * (17 : ℕ) ^ 13 < 26 ^ 13 := by
  norm_num

theorem hullSixTwoFourP02Q22_root_gap :
    (17 : ℝ) / 2 <
      13 * hullSixTwoFourP02Q22Constant ^ ((13 : ℝ)⁻¹) := by
  have hpow :
      ((17 : ℝ) / 26) ^ 13 < hullSixTwoFourP02Q22Constant := by
    norm_num [hullSixTwoFourP02Q22Constant]
  have hpowRpow :
      ((17 : ℝ) / 26) ^ (13 : ℝ) <
        hullSixTwoFourP02Q22Constant := by
    change ((17 : ℝ) / 26) ^ ((13 : ℕ) : ℝ) <
      hullSixTwoFourP02Q22Constant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (17 : ℝ) / 26 <
        hullSixTwoFourP02Q22Constant ^ ((13 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourP02Q22_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourP02Q22_laurent_gt
    {a b c d : ℝ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hc1 : 1 ≤ c) (hd1 : 1 ≤ d) :
    (17 : ℝ) / 2 < hullSixTwoFourP02Q22Laurent a b c d := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourP02Q22Weight
    (hullSixTwoFourP02Q22Term a b c d)
    hullSixTwoFourP02Q22_weight_pos
    (hullSixTwoFourP02Q22_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt hd))
  rw [hullSixTwoFourP02Q22_weight_sum,
    hullSixTwoFourP02Q22_term_product ha hb hc hd] at hamgm
  have haPow : (1 : ℝ) ≤ a ^ 3 := one_le_pow₀ ha1
  have hProductFloor :
      hullSixTwoFourP02Q22Constant ≤
        hullSixTwoFourP02Q22Constant * a ^ 3 := by
    simpa using
      (mul_le_mul_of_nonneg_left haPow
        (le_of_lt hullSixTwoFourP02Q22_constant_pos))
  have hRootFloor :
      hullSixTwoFourP02Q22Constant ^ ((13 : ℝ)⁻¹) ≤
        (hullSixTwoFourP02Q22Constant * a ^ 3) ^ ((13 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (le_of_lt hullSixTwoFourP02Q22_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixTwoFourP02Q22_term_sum a b c d]
  exact hullSixTwoFourP02Q22_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-- Compact normalized scalar endpoint for the exact `p02/q22` packet.

The three recurrence premises are the direct consequences of `X00 <= -1`,
`X11 >= 1`, and `Y12 <= -1`, respectively. -/
theorem hullSixTwoFour_p02q22_scalar
    {a b c d f A C E0 E1 E2 F : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (hf1 : 1 ≤ f)
    (hE01 : 1 ≤ E0) (hE21 : 1 ≤ E2)
    (hARec : a * C + b ≤ c * A)
    (hCRec : b * E0 + c ≤ d * C)
    (hE1Rec : b * d + 2 * d + 1 ≤ b * E1)
    (hFcap : a + f + 1 ≤ F) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1

  have hCLower : (b + c) / d ≤ C := by
    apply (div_le_iff₀ hd).2
    have hbE0 : b ≤ b * E0 := by
      simpa using mul_le_mul_of_nonneg_left hE01 (le_of_lt hb)
    nlinarith
  have hALower : (a * C + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hARec)
  have hcoef : 0 ≤ 1 + a / c := by positivity
  have hCScaled :
      (1 + a / c) * ((b + c) / d) ≤ (1 + a / c) * C :=
    mul_le_mul_of_nonneg_left hCLower hcoef
  have hACLower :
      (1 + a / c) * ((b + c) / d) + b / c ≤ A + C := by
    calc
      (1 + a / c) * ((b + c) / d) + b / c
          ≤ (1 + a / c) * C + b / c := by linarith
      _ = C + (a * C + b) / c := by
        field_simp [hc.ne'] <;> ring
      _ ≤ C + A := add_le_add le_rfl hALower
      _ = A + C := by ring
  have hE1Lower : d + 2 * d / b + 1 / b ≤ E1 := by
    have hshape :
        d + 2 * d / b + 1 / b = (b * d + 2 * d + 1) / b := by
      field_simp [hb.ne'] <;> ring
    rw [hshape]
    exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hE1Rec)
  have hFLower : a + 2 ≤ F := by linarith
  have hLower :
      4 + hullSixTwoFourP02Q22Laurent a b c d ≤
        A + C + E0 + E1 + E2 + F := by
    have hExpand :
        4 + hullSixTwoFourP02Q22Laurent a b c d =
          ((1 + a / c) * ((b + c) / d) + b / c) +
            (d + 2 * d / b + 1 / b) + a + 4 := by
      unfold hullSixTwoFourP02Q22Laurent
      field_simp [hb.ne', hc.ne', hd.ne'] <;> ring
    rw [hExpand]
    linarith
  have hLaurent := hullSixTwoFourP02Q22_laurent_gt ha1 hb1 hc1 hd1
  linarith

end Heilbronn8
