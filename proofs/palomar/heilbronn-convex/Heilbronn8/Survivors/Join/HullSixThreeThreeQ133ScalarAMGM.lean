import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM--GM certificate for the `(-Y01,+Y12)` hull-six branch

This file isolates the analytic part of one signed `3 x 3` cross-chord
chamber.  The variables `a,b,c` and `d,e,f` are the positive heights of the
three upper and three lower hull vertices, while `r,s,t,w,z` are the five
successive slope gaps.  The assumptions below are exactly four elementary
area floors, one primed lower-fan floor, and the two signed `Y` floors
`-Y01 >= 1` and `Y12 >= 1`.

The proof first eliminates the gaps to a twelve-term Laurent sum.  An exact
eighteen-copy AM--GM certificate then proves that this sum is greater than
`21 / 2`, which closes the normalized hull target `25 / 2`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The Laurent sum left by the signed-gap elimination. -/
noncomputable def hullSixThreeThreeQ133Laurent
    (b c e f : ℝ) : ℝ :=
  b + e + 1 / e + b / e + f / e + b / (e * f) + 1 / f +
    c / b + 1 / b + e / b + e / (b * c) + 1 / c

/-- The twelve distinct AM--GM terms. -/
noncomputable def hullSixThreeThreeQ133AMGMTerm
    (b c e f : ℝ) : Fin 12 → ℝ :=
  ![b, e, 1 / e, b / e, f / e, b / (e * f), 1 / f,
    c / b, 1 / b, e / b, e / (b * c), 1 / c]

/-- Multiplicities `3,3,1,1,2,1,1,2,1,1,1,1`, of total mass eighteen. -/
def hullSixThreeThreeQ133AMGMWeight : Fin 12 → ℕ :=
  ![3, 3, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1]

/-- The variable-free product after all four height exponents cancel. -/
noncomputable def hullSixThreeThreeQ133AMGMConstant : ℝ :=
  1 / ((3 : ℝ) ^ 6 * (2 : ℝ) ^ 4)

theorem hullSixThreeThreeQ133_amgmWeight_pos
    (i : Fin 12) : 0 < hullSixThreeThreeQ133AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ133AMGMWeight]

theorem hullSixThreeThreeQ133_amgmWeight_sum :
    ∑ i, hullSixThreeThreeQ133AMGMWeight i = 18 := by
  norm_num [hullSixThreeThreeQ133AMGMWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ133_amgmTerm_nonneg
    {b c e f : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hf : 0 ≤ f) (i : Fin 12) :
    0 ≤ hullSixThreeThreeQ133AMGMTerm b c e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ133AMGMTerm] <;>
    positivity

theorem hullSixThreeThreeQ133_amgmTerm_sum
    (b c e f : ℝ) :
    ∑ i, hullSixThreeThreeQ133AMGMTerm b c e f i =
      hullSixThreeThreeQ133Laurent b c e f := by
  simp [hullSixThreeThreeQ133AMGMTerm, hullSixThreeThreeQ133Laurent,
    Fin.sum_univ_succ] <;> ring

/-- The eighteen scaled terms have the exact product `1 / (3^6 * 2^4)`. -/
theorem hullSixThreeThreeQ133_amgmTerm_product
    {b c e f : ℝ} (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeQ133AMGMTerm b c e f i /
          (hullSixThreeThreeQ133AMGMWeight i : ℝ)) ^
            hullSixThreeThreeQ133AMGMWeight i) =
      hullSixThreeThreeQ133AMGMConstant := by
  simp [hullSixThreeThreeQ133AMGMTerm,
    hullSixThreeThreeQ133AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ133AMGMConstant]
  field_simp [hb.ne', hc.ne', he.ne', hf.ne'] <;> ring

theorem hullSixThreeThreeQ133_amgmConstant_pos :
    0 < hullSixThreeThreeQ133AMGMConstant := by
  unfold hullSixThreeThreeQ133AMGMConstant
  positivity

/-- Exact integer endpoint for the eighteen-copy AM--GM certificate. -/
theorem hullSixThreeThreeQ133_amgm_integer_gap :
    (7 : ℕ) ^ 18 < 2 ^ 32 * 3 ^ 12 := by
  norm_num

/-- The certified AM--GM root is strictly larger than `21 / 2`. -/
theorem hullSixThreeThreeQ133_amgm_root_gap :
    (21 : ℝ) / 2 <
      18 * hullSixThreeThreeQ133AMGMConstant ^ ((18 : ℝ)⁻¹) := by
  have hpow :
      ((7 : ℝ) / 12) ^ 18 < hullSixThreeThreeQ133AMGMConstant := by
    norm_num [hullSixThreeThreeQ133AMGMConstant]
  have hpowRpow :
      ((7 : ℝ) / 12) ^ (18 : ℝ) <
        hullSixThreeThreeQ133AMGMConstant := by
    change ((7 : ℝ) / 12) ^ ((18 : ℕ) : ℝ) <
      hullSixThreeThreeQ133AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (7 : ℝ) / 12 <
        hullSixThreeThreeQ133AMGMConstant ^ ((18 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ133_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- The exact twelve-term Laurent inequality used by the chamber proof. -/
theorem hullSixThreeThreeQ133_laurent_gt
    {b c e f : ℝ} (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) :
    (21 : ℝ) / 2 < hullSixThreeThreeQ133Laurent b c e f := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ133AMGMWeight
    (hullSixThreeThreeQ133AMGMTerm b c e f)
    hullSixThreeThreeQ133_amgmWeight_pos
    (hullSixThreeThreeQ133_amgmTerm_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt he) (le_of_lt hf))
  rw [hullSixThreeThreeQ133_amgmWeight_sum,
    hullSixThreeThreeQ133_amgmTerm_product hb hc he hf] at hamgm
  rw [← hullSixThreeThreeQ133_amgmTerm_sum b c e f]
  exact hullSixThreeThreeQ133_amgm_root_gap.trans_le hamgm

/--
Complete scalar closure for the signed branch `-Y01 >= 1`, `Y12 >= 1`.

The conclusion is the six consecutive-area sum.  No ear inequality, mixed
hull triple, generated certificate, or unproved monotonicity assertion is used.
-/
theorem hullSixThreeThreeQ133_scalar
    {a b c d e f r s t w z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (ha1 : 1 ≤ a) (hd1 : 1 ≤ d)
    (hs : 1 ≤ b * d * s)
    (ht : 1 ≤ b * c * t)
    (hw : 1 ≤ c * e * w)
    (hl1q : 1 ≤ e * f * z + f - e)
    (hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e)
    (hY12pos : 1 ≤ b + f - b * f * (t + w + z)) :
    (25 : ℝ) / 2 <
      a * b * (r + s) + b * c * t + c * d * (s + t) +
        d * e * (s + t + w) + e * f * z +
          a * f * (r + s + t + w + z) := by
  have hl1base : e - f + 1 ≤ e * f * z := by
    linarith
  have hY01base :
      a + e + 1 ≤ a * e * (r + s + t + w) := by
    linarith
  have hY12base :
      b * f * (t + w + z) ≤ b + f - 1 := by
    linarith

  have hzScaled :
      (b / e) * (e - f + 1) ≤ b * f * z := by
    have h := mul_le_mul_of_nonneg_left hl1base
      (le_of_lt (div_pos hb he))
    calc
      (b / e) * (e - f + 1) ≤ (b / e) * (e * f * z) := h
      _ = b * f * z := by field_simp [he.ne'] <;> ring
  have htwSum :
      b * f * (t + w) + b * f * z ≤ b + f - 1 := by
    calc
      b * f * (t + w) + b * f * z =
          b * f * (t + w + z) := by ring
      _ ≤ b + f - 1 := hY12base
  have htw :
      b * f * (t + w) ≤ (b + e) * (f - 1) / e := by
    calc
      b * f * (t + w) ≤ b + f - 1 - b * f * z := by linarith
      _ ≤ b + f - 1 - (b / e) * (e - f + 1) := by
        exact sub_le_sub_left hzScaled (b + f - 1)
      _ = (b + e) * (f - 1) / e := by
        field_simp [he.ne'] <;> ring

  have hY01Scaled :
      (b / e) * (a + e + 1) ≤
        a * b * (r + s) + a * b * (t + w) := by
    have h := mul_le_mul_of_nonneg_left hY01base
      (le_of_lt (div_pos hb he))
    calc
      (b / e) * (a + e + 1) ≤
          (b / e) * (a * e * (r + s + t + w)) := h
      _ = a * b * (r + s) + a * b * (t + w) := by
        field_simp [he.ne'] <;> ring
  have htwScaled :
      a * b * (t + w) ≤
        (a / f) * ((b + e) * (f - 1) / e) := by
    have h := mul_le_mul_of_nonneg_left htw
      (le_of_lt (div_pos ha hf))
    calc
      a * b * (t + w) = (a / f) * (b * f * (t + w)) := by
        field_simp [hf.ne'] <;> ring
      _ ≤ (a / f) * ((b + e) * (f - 1) / e) := h
  have hu0 :
      b - a + b / e + a * (b + e) / (e * f) ≤
        a * b * (r + s) := by
    have hid :
        b - a + b / e + a * (b + e) / (e * f) =
          (b / e) * (a + e + 1) -
            (a / f) * ((b + e) * (f - 1) / e) := by
      field_simp [he.ne', hf.ne'] <;> ring
    rw [hid]
    linarith

  have hsScaled : c / b ≤ c * d * s := by
    have h := mul_le_mul_of_nonneg_left hs
      (le_of_lt (div_pos hc hb))
    calc
      c / b ≤ (c / b) * (b * d * s) := by simpa using h
      _ = c * d * s := by field_simp [hb.ne'] <;> ring
  have htScaled : d / b ≤ c * d * t := by
    have h := mul_le_mul_of_nonneg_left ht
      (le_of_lt (div_pos hd hb))
    calc
      d / b ≤ (d / b) * (b * c * t) := by simpa using h
      _ = c * d * t := by field_simp [hb.ne'] <;> ring
  have hE : (c + d) / b ≤ c * d * (s + t) := by
    rw [add_div]
    nlinarith [hsScaled, htScaled]

  have hsLower : e / b ≤ d * e * s := by
    have h := mul_le_mul_of_nonneg_left hs
      (le_of_lt (div_pos he hb))
    calc
      e / b ≤ (e / b) * (b * d * s) := by simpa using h
      _ = d * e * s := by field_simp [hb.ne'] <;> ring
  have htLower : d * e / (b * c) ≤ d * e * t := by
    have h := mul_le_mul_of_nonneg_left ht
      (div_nonneg (mul_nonneg (le_of_lt hd) (le_of_lt he))
        (mul_nonneg (le_of_lt hb) (le_of_lt hc)))
    calc
      d * e / (b * c) ≤
          (d * e / (b * c)) * (b * c * t) := by simpa using h
      _ = d * e * t := by field_simp [hb.ne', hc.ne'] <;> ring
  have hwLower : d / c ≤ d * e * w := by
    have h := mul_le_mul_of_nonneg_left hw
      (le_of_lt (div_pos hd hc))
    calc
      d / c ≤ (d / c) * (c * e * w) := by simpa using h
      _ = d * e * w := by field_simp [hc.ne'] <;> ring
  have hL0 :
      e / b + d * e / (b * c) + d / c ≤
        d * e * (s + t + w) := by
    nlinarith [hsLower, htLower, hwLower]

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

  let T := hullSixThreeThreeQ133Laurent b c e f
  let excess :=
    (a - 1) / e + (a - 1) * (b + e) / (e * f) +
      (d - 1) / b + (d - 1) * e / (b * c) + (d - 1) / c
  have haSub : 0 ≤ a - 1 := by linarith
  have hdSub : 0 ≤ d - 1 := by linarith
  have hexcess : 0 ≤ excess := by
    dsimp [excess]
    positivity
  have hlowerIdentity :
      b - a + b / e + a * (b + e) / (e * f) + 1 +
          (c + d) / b +
          (e / b + d * e / (b * c) + d / c) +
          (e - f + 1) + (a + f + (a + f) / e) =
        T + 2 + excess := by
    dsimp [T, excess, hullSixThreeThreeQ133Laurent]
    field_simp [hb.ne', hc.ne', he.ne', hf.ne'] <;> ring
  have hHullLower :
      T + 2 ≤
        a * b * (r + s) + b * c * t + c * d * (s + t) +
          d * e * (s + t + w) + e * f * z +
            a * f * (r + s + t + w + z) := by
    nlinarith [hu0, ht, hE, hL0, hl1base, hF, hexcess]
  have hT : (21 : ℝ) / 2 < T := by
    exact hullSixThreeThreeQ133_laurent_gt hb hc he hf
  linarith

end Heilbronn8
