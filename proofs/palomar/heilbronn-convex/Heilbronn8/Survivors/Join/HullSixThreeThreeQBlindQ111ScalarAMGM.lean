import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM--GM certificate for the `q = 111` hull-six branch

This is the analytic end of the `p = 011` chamber when `Y01` and `Y21`
are both negative.  It eliminates the five successive slope gaps to a
ten-term Laurent sum and closes that sum by an exact seventeen-copy
weighted AM--GM certificate.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The ten-term Laurent sum left by the signed-gap elimination. -/
noncomputable def hullSixThreeThreeQ111Laurent
    (b c d e : ℝ) : ℝ :=
  e + 2 / e + 1 / d + b / d + d + d * e / c + d / c +
    c / b + d / b + e / b

/-- The ten distinct terms in the seventeen-copy AM--GM certificate. -/
noncomputable def hullSixThreeThreeQ111AMGMTerm
    (b c d e : ℝ) : Fin 10 → ℝ :=
  ![e, 2 / e, 1 / d, b / d, d, d * e / c, d / c,
    c / b, d / b, e / b]

/-- Multiplicities `1,3,1,4,2,1,1,2,1,1`, of total mass seventeen. -/
def hullSixThreeThreeQ111AMGMWeight : Fin 10 → ℕ :=
  ![1, 3, 1, 4, 2, 1, 1, 2, 1, 1]

/-- The variable-free product after all four height exponents cancel. -/
noncomputable def hullSixThreeThreeQ111AMGMConstant : ℝ :=
  1 / 13824

theorem hullSixThreeThreeQ111_amgmWeight_pos
    (i : Fin 10) : 0 < hullSixThreeThreeQ111AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ111AMGMWeight]

theorem hullSixThreeThreeQ111_amgmWeight_sum :
    ∑ i, hullSixThreeThreeQ111AMGMWeight i = 17 := by
  norm_num [hullSixThreeThreeQ111AMGMWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ111_amgmTerm_nonneg
    {b c d e : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (i : Fin 10) :
    0 ≤ hullSixThreeThreeQ111AMGMTerm b c d e i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ111AMGMTerm] <;>
    positivity

theorem hullSixThreeThreeQ111_amgmTerm_sum
    (b c d e : ℝ) :
    ∑ i, hullSixThreeThreeQ111AMGMTerm b c d e i =
      hullSixThreeThreeQ111Laurent b c d e := by
  simp [hullSixThreeThreeQ111AMGMTerm, hullSixThreeThreeQ111Laurent,
    Fin.sum_univ_succ] <;> ring

/-- The seventeen scaled terms have exact product `1 / 13824`. -/
theorem hullSixThreeThreeQ111_amgmTerm_product
    {b c d e : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    (∏ i,
        (hullSixThreeThreeQ111AMGMTerm b c d e i /
          (hullSixThreeThreeQ111AMGMWeight i : ℝ)) ^
            hullSixThreeThreeQ111AMGMWeight i) =
      hullSixThreeThreeQ111AMGMConstant := by
  simp [hullSixThreeThreeQ111AMGMTerm,
    hullSixThreeThreeQ111AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ111AMGMConstant]
  field_simp [hb.ne', hc.ne', hd.ne', he.ne'] <;> ring

theorem hullSixThreeThreeQ111_amgmConstant_pos :
    0 < hullSixThreeThreeQ111AMGMConstant := by
  unfold hullSixThreeThreeQ111AMGMConstant
  positivity

/-- Exact integer endpoint for the seventeen-copy certificate. -/
theorem hullSixThreeThreeQ111_amgm_integer_gap :
    13824 * (19 : ℕ) ^ 17 < 34 ^ 17 := by
  norm_num

/-- The certified AM--GM root is strictly larger than `19 / 2`. -/
theorem hullSixThreeThreeQ111_amgm_root_gap :
    (19 : ℝ) / 2 <
      17 * hullSixThreeThreeQ111AMGMConstant ^ ((17 : ℝ)⁻¹) := by
  have hpow :
      ((19 : ℝ) / 34) ^ 17 < hullSixThreeThreeQ111AMGMConstant := by
    norm_num [hullSixThreeThreeQ111AMGMConstant]
  have hpowRpow :
      ((19 : ℝ) / 34) ^ (17 : ℝ) <
        hullSixThreeThreeQ111AMGMConstant := by
    change ((19 : ℝ) / 34) ^ ((17 : ℕ) : ℝ) <
      hullSixThreeThreeQ111AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (19 : ℝ) / 34 <
        hullSixThreeThreeQ111AMGMConstant ^ ((17 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ111_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- The exact ten-term Laurent inequality used by the chamber proof. -/
theorem hullSixThreeThreeQ111_laurent_gt
    {b c d e : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    (19 : ℝ) / 2 < hullSixThreeThreeQ111Laurent b c d e := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ111AMGMWeight
    (hullSixThreeThreeQ111AMGMTerm b c d e)
    hullSixThreeThreeQ111_amgmWeight_pos
    (hullSixThreeThreeQ111_amgmTerm_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt hd) (le_of_lt he))
  rw [hullSixThreeThreeQ111_amgmWeight_sum,
    hullSixThreeThreeQ111_amgmTerm_product hb hc hd he] at hamgm
  rw [← hullSixThreeThreeQ111_amgmTerm_sum b c d e]
  exact hullSixThreeThreeQ111_amgm_root_gap.trans_le hamgm

/--
Complete scalar closure for the signed branch `-Y01 >= 1`, `-Y21 >= 1`.

The conclusion is the six consecutive-area sum.  No ear inequality, mixed
hull triple, generated certificate, or monotonicity assertion is used.
-/
theorem hullSixThreeThreeQ111_scalar
    {a b c d e f r s t w z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (ha1 : 1 ≤ a) (hf1 : 1 ≤ f)
    (hr : 1 ≤ a * d * r)
    (hs : 1 ≤ b * d * s)
    (ht : 1 ≤ b * c * t)
    (hl1q : 1 ≤ e * f * z + f - e)
    (hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e)
    (hY21neg : 1 ≤ c * e * w - c - e) :
    (25 : ℝ) / 2 <
      a * b * (r + s) + b * c * t + c * d * (s + t) +
        d * e * (s + t + w) + e * f * z +
          a * f * (r + s + t + w + z) := by
  have hl1base : e - f + 1 ≤ e * f * z := by
    linarith
  have hY01base :
      a + e + 1 ≤ a * e * (r + s + t + w) := by
    linarith
  have hY21base : c + e + 1 ≤ c * e * w := by
    linarith

  have hrP : b / d ≤ a * b * r := by
    have h := mul_le_mul_of_nonneg_left hr
      (le_of_lt (div_pos hb hd))
    calc
      b / d ≤ (b / d) * (a * d * r) := by simpa using h
      _ = a * b * r := by field_simp [hd.ne'] <;> ring
  have hsP : a / d ≤ a * b * s := by
    have h := mul_le_mul_of_nonneg_left hs
      (le_of_lt (div_pos ha hd))
    calc
      a / d ≤ (a / d) * (b * d * s) := by simpa using h
      _ = a * b * s := by field_simp [hd.ne'] <;> ring
  have hsE : c / b ≤ c * d * s := by
    have h := mul_le_mul_of_nonneg_left hs
      (le_of_lt (div_pos hc hb))
    calc
      c / b ≤ (c / b) * (b * d * s) := by simpa using h
      _ = c * d * s := by field_simp [hb.ne'] <;> ring
  have htE : d / b ≤ c * d * t := by
    have h := mul_le_mul_of_nonneg_left ht
      (le_of_lt (div_pos hd hb))
    calc
      d / b ≤ (d / b) * (b * c * t) := by simpa using h
      _ = c * d * t := by field_simp [hb.ne'] <;> ring

  let P :=
    a * b * (r + s) + b * c * t + c * d * (s + t) - 2
  let A := (a + b) / d + (c + d) / b - 1
  have hPA : A ≤ P := by
    dsimp [A, P]
    have hid :
        (a + b) / d + (c + d) / b - 1 =
          b / d + a / d + 1 + c / b + d / b - 2 := by ring
    rw [hid]
    nlinarith [hrP, hsP, ht, hsE, htE]

  have hsL : e / b ≤ d * e * s := by
    have h := mul_le_mul_of_nonneg_left hs
      (le_of_lt (div_pos he hb))
    calc
      e / b ≤ (e / b) * (b * d * s) := by simpa using h
      _ = d * e * s := by field_simp [hb.ne'] <;> ring
  have htL : d * e / (b * c) ≤ d * e * t := by
    have h := mul_le_mul_of_nonneg_left ht
      (div_nonneg (mul_nonneg (le_of_lt hd) (le_of_lt he))
        (mul_nonneg (le_of_lt hb) (le_of_lt hc)))
    calc
      d * e / (b * c) ≤
          (d * e / (b * c)) * (b * c * t) := by simpa using h
      _ = d * e * t := by field_simp [hb.ne', hc.ne'] <;> ring
  have hwL : d + d * e / c + d / c ≤ d * e * w := by
    have h := mul_le_mul_of_nonneg_left hY21base
      (le_of_lt (div_pos hd hc))
    calc
      d + d * e / c + d / c = (d / c) * (c + e + 1) := by
        field_simp [hc.ne'] <;> ring
      _ ≤ (d / c) * (c * e * w) := h
      _ = d * e * w := by field_simp [hc.ne'] <;> ring
  have hL0 :
      e / b + d * e / (b * c) + d + d * e / c + d / c ≤
        d * e * (s + t + w) := by
    nlinarith [hsL, htL, hwL]

  have hY01ForF :
      (f / e) * (a + e + 1) ≤
        a * f * (r + s + t + w) := by
    have h := mul_le_mul_of_nonneg_left hY01base
      (le_of_lt (div_pos hf he))
    calc
      (f / e) * (a + e + 1) ≤
          (f / e) * (a * e * (r + s + t + w)) := h
      _ = a * f * (r + s + t + w) := by
        field_simp [he.ne'] <;> ring
  have hzForF :
      (a / e) * (e - f + 1) ≤ a * f * z := by
    have h := mul_le_mul_of_nonneg_left hl1base
      (le_of_lt (div_pos ha he))
    calc
      (a / e) * (e - f + 1) ≤ (a / e) * (e * f * z) := h
      _ = a * f * z := by field_simp [he.ne'] <;> ring
  have hF :
      a + f + (a + f) / e ≤
        a * f * (r + s + t + w + z) := by
    have hid :
        a + f + (a + f) / e =
          (f / e) * (a + e + 1) +
            (a / e) * (e - f + 1) := by
      field_simp [he.ne'] <;> ring
    rw [hid]
    nlinarith [hY01ForF, hzForF]

  let Q :=
    d * e * (s + t + w) + e * f * z +
      a * f * (r + s + t + w + z) - 4
  let B :=
    a + e - 3 + (a + f) / e + e / b + d * e / (b * c) +
      d + d * e / c + d / c
  have hBQ : B ≤ Q := by
    dsimp [B, Q]
    nlinarith [hL0, hl1base, hF]

  let T := hullSixThreeThreeQ111Laurent b c d e
  let excess :=
    (a - 1) * (1 + 1 / e + 1 / d) + (f - 1) / e +
      d * e / (b * c)
  have haSub : 0 ≤ a - 1 := by linarith
  have hfSub : 0 ≤ f - 1 := by linarith
  have hexcess : 0 ≤ excess := by
    dsimp [excess]
    positivity
  have hlowerIdentity : A + B = T - 3 + excess := by
    dsimp [A, B, T, excess, hullSixThreeThreeQ111Laurent]
    field_simp [hb.ne', hc.ne', hd.ne', he.ne'] <;> ring
  have hPQ : T - 3 ≤ P + Q := by
    nlinarith [hPA, hBQ, hlowerIdentity, hexcess]
  have hT : (19 : ℝ) / 2 < T := by
    exact hullSixThreeThreeQ111_laurent_gt hb hc hd he
  have hraw :
      a * b * (r + s) + b * c * t + c * d * (s + t) +
          d * e * (s + t + w) + e * f * z +
            a * f * (r + s + t + w + z) = P + Q + 6 := by
    dsimp [P, Q]
    ring
  rw [hraw]
  linarith

end Heilbronn8
