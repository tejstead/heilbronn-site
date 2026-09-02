import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar certificates for three maximal-q merged-path frontiers

This file closes the analytic part of the partial-`X` frontiers

```text
p = 023, 112, 122,   q = 233.
```

After ordering the six hull vertices by slope from the interior chord, every
successive pair has determinant at least one.  Telescoping those five path
edges through the six `P`-fan areas leaves a fourteen-term Laurent lower
bound.  The three exact weighted AM--GM certificates below have masses
`34`, `35`, and `34`.  Their scaled products are respectively

```text
a^5 c^4 / (2^24 3^18),
d^5 f^5 / (2^22 3^9 7^7),
d^4 f^5 / (2^24 3^18).
```

The line-height floors make the residual monomials at least one.  No `Y`
sign, lower-ear inequality, finite chamber census, or generated certificate
is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## The frontier `p = 023` -/

noncomputable def hullSixThreeThreeP023MergedLaurent
    (a b c d e f : ℝ) : ℝ :=
  a + f + b / d + a * b / (d * e) + a / e + c / f + b / f +
    c / e + c * d / (b * e) + c * d / (b * f) + d / f + 1 +
      f / b + e / b

noncomputable def hullSixThreeThreeP023MergedTerm
    (a b c d e f : ℝ) : Fin 14 → ℝ :=
  ![a, f, b / d, a * b / (d * e), a / e, c / f, b / f,
    c / e, c * d / (b * e), c * d / (b * f), d / f, 1,
    f / b, e / b]

def hullSixThreeThreeP023MergedWeight : Fin 14 → ℕ :=
  ![3, 6, 4, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4]

noncomputable def hullSixThreeThreeP023MergedConstant : ℝ :=
  1 / ((2 : ℝ) ^ 24 * (3 : ℝ) ^ 18)

theorem hullSixThreeThreeP023Merged_weight_pos
    (i : Fin 14) : 0 < hullSixThreeThreeP023MergedWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP023MergedWeight]

theorem hullSixThreeThreeP023Merged_weight_sum :
    ∑ i, hullSixThreeThreeP023MergedWeight i = 34 := by
  norm_num [hullSixThreeThreeP023MergedWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP023Merged_term_nonneg
    {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (i : Fin 14) :
    0 ≤ hullSixThreeThreeP023MergedTerm a b c d e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP023MergedTerm] <;>
    positivity

theorem hullSixThreeThreeP023Merged_term_sum
    (a b c d e f : ℝ) :
    ∑ i, hullSixThreeThreeP023MergedTerm a b c d e f i =
      hullSixThreeThreeP023MergedLaurent a b c d e f := by
  simp [hullSixThreeThreeP023MergedTerm,
    hullSixThreeThreeP023MergedLaurent, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP023Merged_term_product
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeP023MergedTerm a b c d e f i /
          (hullSixThreeThreeP023MergedWeight i : ℝ)) ^
            hullSixThreeThreeP023MergedWeight i) =
      hullSixThreeThreeP023MergedConstant * a ^ 5 * c ^ 4 := by
  simp [hullSixThreeThreeP023MergedTerm,
    hullSixThreeThreeP023MergedWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP023MergedConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeP023Merged_constant_pos :
    0 < hullSixThreeThreeP023MergedConstant := by
  unfold hullSixThreeThreeP023MergedConstant
  positivity

theorem hullSixThreeThreeP023Merged_integer_gap :
    (23 : ℕ) ^ 34 * (2 ^ 24 * 3 ^ 18) < 68 ^ 34 := by
  norm_num

theorem hullSixThreeThreeP023Merged_root_gap :
    (23 : ℝ) / 2 <
      34 * hullSixThreeThreeP023MergedConstant ^ ((34 : ℝ)⁻¹) := by
  have hpow :
      ((23 : ℝ) / 68) ^ 34 < hullSixThreeThreeP023MergedConstant := by
    norm_num [hullSixThreeThreeP023MergedConstant]
  have hpowRpow :
      ((23 : ℝ) / 68) ^ (34 : ℝ) <
        hullSixThreeThreeP023MergedConstant := by
    change ((23 : ℝ) / 68) ^ ((34 : ℕ) : ℝ) <
      hullSixThreeThreeP023MergedConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (23 : ℝ) / 68 <
        hullSixThreeThreeP023MergedConstant ^ ((34 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP023Merged_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP023Merged_laurent_gt
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f) :
    (23 : ℝ) / 2 < hullSixThreeThreeP023MergedLaurent a b c d e f := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP023MergedWeight
    (hullSixThreeThreeP023MergedTerm a b c d e f)
    hullSixThreeThreeP023Merged_weight_pos
    (hullSixThreeThreeP023Merged_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hd) (le_of_lt he) (le_of_lt hf))
  rw [hullSixThreeThreeP023Merged_weight_sum,
    hullSixThreeThreeP023Merged_term_product ha hb hc hd he hf] at hamgm
  have hResidual : (1 : ℝ) ≤ a ^ 5 * c ^ 4 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ a ^ 5 * c ^ 4 :=
        mul_le_mul (one_le_pow₀ ha1) (one_le_pow₀ hc1)
          (by norm_num) (by positivity)
  have hProductFloor :
      hullSixThreeThreeP023MergedConstant ≤
        hullSixThreeThreeP023MergedConstant * a ^ 5 * c ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hResidual
      (le_of_lt hullSixThreeThreeP023Merged_constant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixThreeThreeP023MergedConstant ^ ((34 : ℝ)⁻¹) ≤
        (hullSixThreeThreeP023MergedConstant * a ^ 5 * c ^ 4) ^
          ((34 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixThreeThreeP023Merged_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixThreeThreeP023Merged_term_sum a b c d e f]
  exact hullSixThreeThreeP023Merged_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-- Raw six-fan wrapper for the `p = 023` merged path. -/
theorem hullSixThreeThreeP023Merged_scalar
    {a b c d e f A B C D E F : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hA : b * e + a * b + a * d ≤ d * e * A)
    (hB : c + b ≤ f * B)
    (hC : b * c * f + c * d * f + c * d * e + b * d * e ≤
      b * e * f * C)
    (hD : 1 ≤ D)
    (hE : f + e ≤ b * E)
    (hF : a + f + 1 ≤ F) :
    (25 : ℝ) / 2 < A + B + C + D + E + F := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hf0 : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have hde0 : 0 < d * e := mul_pos hd0 he0
  have hbef0 : 0 < b * e * f := mul_pos (mul_pos hb0 he0) hf0
  have hAlower : b / d + a * b / (d * e) + a / e ≤ A := by
    calc
      b / d + a * b / (d * e) + a / e =
          (b * e + a * b + a * d) / (d * e) := by
        field_simp [hd0.ne', he0.ne'] <;> ring
      _ ≤ A := (div_le_iff₀ hde0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hA)
  have hBlower : c / f + b / f ≤ B := by
    rw [← add_div]
    exact (div_le_iff₀ hf0).2 (by simpa [mul_comm] using hB)
  have hClower :
      c / e + c * d / (b * e) + c * d / (b * f) + d / f ≤ C := by
    calc
      c / e + c * d / (b * e) + c * d / (b * f) + d / f =
          (b * c * f + c * d * f + c * d * e + b * d * e) /
            (b * e * f) := by
        field_simp [hb0.ne', he0.ne', hf0.ne'] <;> ring
      _ ≤ C := (div_le_iff₀ hbef0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hC)
  have hElower : f / b + e / b ≤ E := by
    rw [← add_div]
    exact (div_le_iff₀ hb0).2 (by simpa [mul_comm] using hE)
  have hL := hullSixThreeThreeP023Merged_laurent_gt ha hb hc hd he hf
  dsimp [hullSixThreeThreeP023MergedLaurent] at hL
  linarith

/-! ## The frontier `p = 112` -/

noncomputable def hullSixThreeThreeP112MergedLaurent
    (a b c d e f : ℝ) : ℝ :=
  a + f + 1 + c / e + b / e + c / a + c * d / (a * b) +
    c * d / (b * e) + d / e + e / a + d * e / (a * b) +
      d / b + f / c + e / c

noncomputable def hullSixThreeThreeP112MergedTerm
    (a b c d e f : ℝ) : Fin 14 → ℝ :=
  ![a, f, 1, c / e, b / e, c / a, c * d / (a * b),
    c * d / (b * e), d / e, e / a, d * e / (a * b), d / b,
    f / c, e / c]

def hullSixThreeThreeP112MergedWeight : Fin 14 → ℕ :=
  ![7, 3, 3, 2, 4, 2, 1, 1, 1, 3, 1, 1, 2, 4]

noncomputable def hullSixThreeThreeP112MergedConstant : ℝ :=
  1 / ((2 : ℝ) ^ 22 * (3 : ℝ) ^ 9 * (7 : ℝ) ^ 7)

theorem hullSixThreeThreeP112Merged_weight_pos
    (i : Fin 14) : 0 < hullSixThreeThreeP112MergedWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP112MergedWeight]

theorem hullSixThreeThreeP112Merged_weight_sum :
    ∑ i, hullSixThreeThreeP112MergedWeight i = 35 := by
  norm_num [hullSixThreeThreeP112MergedWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP112Merged_term_nonneg
    {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (i : Fin 14) :
    0 ≤ hullSixThreeThreeP112MergedTerm a b c d e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP112MergedTerm] <;>
    positivity

theorem hullSixThreeThreeP112Merged_term_sum
    (a b c d e f : ℝ) :
    ∑ i, hullSixThreeThreeP112MergedTerm a b c d e f i =
      hullSixThreeThreeP112MergedLaurent a b c d e f := by
  simp [hullSixThreeThreeP112MergedTerm,
    hullSixThreeThreeP112MergedLaurent, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP112Merged_term_product
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeP112MergedTerm a b c d e f i /
          (hullSixThreeThreeP112MergedWeight i : ℝ)) ^
            hullSixThreeThreeP112MergedWeight i) =
      hullSixThreeThreeP112MergedConstant * d ^ 5 * f ^ 5 := by
  simp [hullSixThreeThreeP112MergedTerm,
    hullSixThreeThreeP112MergedWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP112MergedConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeP112Merged_constant_pos :
    0 < hullSixThreeThreeP112MergedConstant := by
  unfold hullSixThreeThreeP112MergedConstant
  positivity

theorem hullSixThreeThreeP112Merged_integer_gap :
    (23 : ℕ) ^ 35 * (2 ^ 22 * 3 ^ 9 * 7 ^ 7) < 70 ^ 35 := by
  norm_num

theorem hullSixThreeThreeP112Merged_root_gap :
    (23 : ℝ) / 2 <
      35 * hullSixThreeThreeP112MergedConstant ^ ((35 : ℝ)⁻¹) := by
  have hpow :
      ((23 : ℝ) / 70) ^ 35 < hullSixThreeThreeP112MergedConstant := by
    norm_num [hullSixThreeThreeP112MergedConstant]
  have hpowRpow :
      ((23 : ℝ) / 70) ^ (35 : ℝ) <
        hullSixThreeThreeP112MergedConstant := by
    change ((23 : ℝ) / 70) ^ ((35 : ℕ) : ℝ) <
      hullSixThreeThreeP112MergedConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (23 : ℝ) / 70 <
        hullSixThreeThreeP112MergedConstant ^ ((35 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP112Merged_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP112Merged_laurent_gt
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f) :
    (23 : ℝ) / 2 < hullSixThreeThreeP112MergedLaurent a b c d e f := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP112MergedWeight
    (hullSixThreeThreeP112MergedTerm a b c d e f)
    hullSixThreeThreeP112Merged_weight_pos
    (hullSixThreeThreeP112Merged_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hd) (le_of_lt he) (le_of_lt hf))
  rw [hullSixThreeThreeP112Merged_weight_sum,
    hullSixThreeThreeP112Merged_term_product ha hb hc hd he hf] at hamgm
  have hResidual : (1 : ℝ) ≤ d ^ 5 * f ^ 5 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ d ^ 5 * f ^ 5 :=
        mul_le_mul (one_le_pow₀ hd1) (one_le_pow₀ hf1)
          (by norm_num) (by positivity)
  have hProductFloor :
      hullSixThreeThreeP112MergedConstant ≤
        hullSixThreeThreeP112MergedConstant * d ^ 5 * f ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hResidual
      (le_of_lt hullSixThreeThreeP112Merged_constant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixThreeThreeP112MergedConstant ^ ((35 : ℝ)⁻¹) ≤
        (hullSixThreeThreeP112MergedConstant * d ^ 5 * f ^ 5) ^
          ((35 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixThreeThreeP112Merged_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixThreeThreeP112Merged_term_sum a b c d e f]
  exact hullSixThreeThreeP112Merged_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-- Raw six-fan wrapper for the `p = 112` merged path. -/
theorem hullSixThreeThreeP112Merged_scalar
    {a b c d e f A B C D E F : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hA : 1 ≤ A)
    (hB : c + b ≤ e * B)
    (hC : b * c * e + c * d * e + a * c * d + a * b * d ≤
      a * b * e * C)
    (hD : b * e + d * e + a * d ≤ a * b * D)
    (hE : f + e ≤ c * E)
    (hF : a + f + 1 ≤ F) :
    (25 : ℝ) / 2 < A + B + C + D + E + F := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hf0 : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have habe0 : 0 < a * b * e := mul_pos (mul_pos ha0 hb0) he0
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  have hBlower : c / e + b / e ≤ B := by
    rw [← add_div]
    exact (div_le_iff₀ he0).2 (by simpa [mul_comm] using hB)
  have hClower :
      c / a + c * d / (a * b) + c * d / (b * e) + d / e ≤ C := by
    calc
      c / a + c * d / (a * b) + c * d / (b * e) + d / e =
          (b * c * e + c * d * e + a * c * d + a * b * d) /
            (a * b * e) := by
        field_simp [ha0.ne', hb0.ne', he0.ne'] <;> ring
      _ ≤ C := (div_le_iff₀ habe0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hC)
  have hDlower : e / a + d * e / (a * b) + d / b ≤ D := by
    calc
      e / a + d * e / (a * b) + d / b =
          (b * e + d * e + a * d) / (a * b) := by
        field_simp [ha0.ne', hb0.ne'] <;> ring
      _ ≤ D := (div_le_iff₀ hab0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hD)
  have hElower : f / c + e / c ≤ E := by
    rw [← add_div]
    exact (div_le_iff₀ hc0).2 (by simpa [mul_comm] using hE)
  have hL := hullSixThreeThreeP112Merged_laurent_gt ha hb hc hd he hf
  dsimp [hullSixThreeThreeP112MergedLaurent] at hL
  linarith

/-! ## The frontier `p = 122` -/

noncomputable def hullSixThreeThreeP122MergedLaurent
    (a b c d e f : ℝ) : ℝ :=
  a + f + b / e + a / e + 1 + c / a + c * d / (a * e) +
    c * d / (b * e) + d / b + e / a + d / a + f / b +
      e * f / (b * c) + e / c

noncomputable def hullSixThreeThreeP122MergedTerm
    (a b c d e f : ℝ) : Fin 14 → ℝ :=
  ![a, f, b / e, a / e, 1, c / a, c * d / (a * e),
    c * d / (b * e), d / b, e / a, d / a, f / b,
    e * f / (b * c), e / c]

def hullSixThreeThreeP122MergedWeight : Fin 14 → ℕ :=
  ![6, 3, 4, 2, 3, 3, 1, 1, 1, 3, 1, 1, 1, 4]

noncomputable def hullSixThreeThreeP122MergedConstant : ℝ :=
  1 / ((2 : ℝ) ^ 24 * (3 : ℝ) ^ 18)

theorem hullSixThreeThreeP122Merged_weight_pos
    (i : Fin 14) : 0 < hullSixThreeThreeP122MergedWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP122MergedWeight]

theorem hullSixThreeThreeP122Merged_weight_sum :
    ∑ i, hullSixThreeThreeP122MergedWeight i = 34 := by
  norm_num [hullSixThreeThreeP122MergedWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP122Merged_term_nonneg
    {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (i : Fin 14) :
    0 ≤ hullSixThreeThreeP122MergedTerm a b c d e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP122MergedTerm] <;>
    positivity

theorem hullSixThreeThreeP122Merged_term_sum
    (a b c d e f : ℝ) :
    ∑ i, hullSixThreeThreeP122MergedTerm a b c d e f i =
      hullSixThreeThreeP122MergedLaurent a b c d e f := by
  simp [hullSixThreeThreeP122MergedTerm,
    hullSixThreeThreeP122MergedLaurent, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP122Merged_term_product
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeP122MergedTerm a b c d e f i /
          (hullSixThreeThreeP122MergedWeight i : ℝ)) ^
            hullSixThreeThreeP122MergedWeight i) =
      hullSixThreeThreeP122MergedConstant * d ^ 4 * f ^ 5 := by
  simp [hullSixThreeThreeP122MergedTerm,
    hullSixThreeThreeP122MergedWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP122MergedConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeP122Merged_constant_pos :
    0 < hullSixThreeThreeP122MergedConstant := by
  unfold hullSixThreeThreeP122MergedConstant
  positivity

theorem hullSixThreeThreeP122Merged_integer_gap :
    (23 : ℕ) ^ 34 * (2 ^ 24 * 3 ^ 18) < 68 ^ 34 := by
  norm_num

theorem hullSixThreeThreeP122Merged_root_gap :
    (23 : ℝ) / 2 <
      34 * hullSixThreeThreeP122MergedConstant ^ ((34 : ℝ)⁻¹) := by
  have hpow :
      ((23 : ℝ) / 68) ^ 34 < hullSixThreeThreeP122MergedConstant := by
    norm_num [hullSixThreeThreeP122MergedConstant]
  have hpowRpow :
      ((23 : ℝ) / 68) ^ (34 : ℝ) <
        hullSixThreeThreeP122MergedConstant := by
    change ((23 : ℝ) / 68) ^ ((34 : ℕ) : ℝ) <
      hullSixThreeThreeP122MergedConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (23 : ℝ) / 68 <
        hullSixThreeThreeP122MergedConstant ^ ((34 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP122Merged_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP122Merged_laurent_gt
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f) :
    (23 : ℝ) / 2 < hullSixThreeThreeP122MergedLaurent a b c d e f := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP122MergedWeight
    (hullSixThreeThreeP122MergedTerm a b c d e f)
    hullSixThreeThreeP122Merged_weight_pos
    (hullSixThreeThreeP122Merged_term_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (le_of_lt hd) (le_of_lt he) (le_of_lt hf))
  rw [hullSixThreeThreeP122Merged_weight_sum,
    hullSixThreeThreeP122Merged_term_product ha hb hc hd he hf] at hamgm
  have hResidual : (1 : ℝ) ≤ d ^ 4 * f ^ 5 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ d ^ 4 * f ^ 5 :=
        mul_le_mul (one_le_pow₀ hd1) (one_le_pow₀ hf1)
          (by norm_num) (by positivity)
  have hProductFloor :
      hullSixThreeThreeP122MergedConstant ≤
        hullSixThreeThreeP122MergedConstant * d ^ 4 * f ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hResidual
      (le_of_lt hullSixThreeThreeP122Merged_constant_pos)
    simpa [mul_assoc] using h
  have hRootFloor :
      hullSixThreeThreeP122MergedConstant ^ ((34 : ℝ)⁻¹) ≤
        (hullSixThreeThreeP122MergedConstant * d ^ 4 * f ^ 5) ^
          ((34 : ℝ)⁻¹) :=
    Real.rpow_le_rpow
      (le_of_lt hullSixThreeThreeP122Merged_constant_pos)
      hProductFloor (by norm_num)
  rw [← hullSixThreeThreeP122Merged_term_sum a b c d e f]
  exact hullSixThreeThreeP122Merged_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hRootFloor (by norm_num)).trans hamgm)

/-- Raw six-fan wrapper for the `p = 122` merged path. -/
theorem hullSixThreeThreeP122Merged_scalar
    {a b c d e f A B C D E F : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hA : b + a ≤ e * A)
    (hB : 1 ≤ B)
    (hC : b * c * e + b * c * d + a * c * d + a * d * e ≤
      a * b * e * C)
    (hD : e + d ≤ a * D)
    (hE : c * f + e * f + b * e ≤ b * c * E)
    (hF : a + f + 1 ≤ F) :
    (25 : ℝ) / 2 < A + B + C + D + E + F := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hf0 : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have habe0 : 0 < a * b * e := mul_pos (mul_pos ha0 hb0) he0
  have hbc0 : 0 < b * c := mul_pos hb0 hc0
  have hAlower : b / e + a / e ≤ A := by
    rw [← add_div]
    exact (div_le_iff₀ he0).2 (by simpa [mul_comm] using hA)
  have hClower :
      c / a + c * d / (a * e) + c * d / (b * e) + d / b ≤ C := by
    calc
      c / a + c * d / (a * e) + c * d / (b * e) + d / b =
          (b * c * e + b * c * d + a * c * d + a * d * e) /
            (a * b * e) := by
        field_simp [ha0.ne', hb0.ne', he0.ne'] <;> ring
      _ ≤ C := (div_le_iff₀ habe0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hC)
  have hDlower : e / a + d / a ≤ D := by
    rw [← add_div]
    exact (div_le_iff₀ ha0).2 (by simpa [mul_comm] using hD)
  have hElower : f / b + e * f / (b * c) + e / c ≤ E := by
    calc
      f / b + e * f / (b * c) + e / c =
          (c * f + e * f + b * e) / (b * c) := by
        field_simp [hb0.ne', hc0.ne'] <;> ring
      _ ≤ E := (div_le_iff₀ hbc0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hE)
  have hL := hullSixThreeThreeP122Merged_laurent_gt ha hb hc hd he hf
  dsimp [hullSixThreeThreeP122MergedLaurent] at hL
  linarith

end Heilbronn8
