import Mathlib

/-!
# A rational lower bound for the four-side telescoping expression

This file proves the purely algebraic inequality used in the compact-height
hexagon chamber.  The proof is a single supporting plane, certified by the
three-term AM-GM inequality.  In particular, it does not use a subdivision or
a generated certificate bank.
-/

namespace Heilbronn8

set_option maxHeartbeats 400000

/-- The three-term AM-GM inequality in the exact ratio form needed below.
The four sign cases give polynomial nonnegativity certificates, so no roots
or analytic convexity machinery enter the kernel proof. -/
private lemma amgm3_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    3 * p * q ≤ 1 + p ^ 2 * q + p * q ^ 2 := by
  suffices 0 ≤ 1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q by linarith
  by_cases hp1 : 1 ≤ p
  · by_cases hq1 : 1 ≤ q
    · rw [show 1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q =
          (p - 1) ^ 2 + (p - 1) * (q - 1) + (q - 1) ^ 2 +
            (p - 1) ^ 2 * (q - 1) + (p - 1) * (q - 1) ^ 2 by ring]
      positivity
    · have hq1' : q ≤ 1 := le_of_not_ge hq1
      have hid : 4 * (1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q) =
          q * (2 * p + q - 3) ^ 2 + (1 - q) ^ 2 * (4 - q) := by ring
      have hfour : 0 ≤ 4 - q := by linarith
      have hrhs : 0 ≤ q * (2 * p + q - 3) ^ 2 + (1 - q) ^ 2 * (4 - q) := by
        positivity
      nlinarith
  · have hp1' : p ≤ 1 := le_of_not_ge hp1
    by_cases hq1 : 1 ≤ q
    · have hid : 4 * (1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q) =
          p * (p + 2 * q - 3) ^ 2 + (1 - p) ^ 2 * (4 - p) := by ring
      have hfour : 0 ≤ 4 - p := by linarith
      have hrhs : 0 ≤ p * (p + 2 * q - 3) ^ 2 + (1 - p) ^ 2 * (4 - p) := by
        positivity
      nlinarith
    · have hq1' : q ≤ 1 := le_of_not_ge hq1
      rw [show 1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q =
          (1 - p) ^ 2 * q + (1 - q) ^ 2 * p + (1 - p) * (1 - q) by ring]
      positivity

/-- A division-free supporting-plane certificate for `(u,v) ↦ 1/(u*v)`.
After clearing the positive denominator, its numerator is the Motzkin
polynomial, equivalently the AM-GM inequality for three terms whose product is
a cube. -/
private lemma invMul_tangent
    {u v u₀ v₀ : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hu₀ : 0 < u₀) (hv₀ : 0 < v₀) :
    3 / (u₀ * v₀) - u / (u₀ ^ 2 * v₀) - v / (u₀ * v₀ ^ 2)
      ≤ 1 / (u * v) := by
  have hp : 0 < u / u₀ := div_pos hu hu₀
  have hq : 0 < v / v₀ := div_pos hv hv₀
  have hamgm := amgm3_ratio hp hq
  field_simp at hamgm ⊢
  nlinarith

/-- The adjacent-pair summand in the four-side expression. -/
noncomputable def hullSixPairTerm (x y : ℝ) : ℝ :=
  (x + y) / (x * y * (x + y - 1))

private lemma hullSixPairTerm_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hc : 0 < x + y - 1) :
    hullSixPairTerm x y = 1 / (x * (x + y - 1)) + 1 / (y * (x + y - 1)) := by
  simp only [hullSixPairTerm]
  field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hc]
  all_goals ring

/-- Exact rational lower bound for the telescoping expression.  The stronger
conclusion leaves a margin of `1/132` over `9/4`. -/
theorem hullSix_L14_ge_149_div_66
    (a₁ a₂ a₃ a₄ : ℝ)
    (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (ha₃ : 1 ≤ a₃) (ha₄ : 1 ≤ a₄)
    (hsum : a₁ + a₂ + a₃ + a₄ ≤ 17 / 2)
    (ha₄cap : a₄ ≤ 13 / 8) :
    149 / 66 ≤
      2 / a₁ + hullSixPairTerm a₁ a₂ + hullSixPairTerm a₂ a₃ +
        hullSixPairTerm a₃ a₄ + 1 / a₄ := by
  have ha₁pos : 0 < a₁ := lt_of_lt_of_le (by norm_num) ha₁
  have ha₂pos : 0 < a₂ := lt_of_lt_of_le (by norm_num) ha₂
  have ha₃pos : 0 < a₃ := lt_of_lt_of_le (by norm_num) ha₃
  have ha₄pos : 0 < a₄ := lt_of_lt_of_le (by norm_num) ha₄
  have hc₁₂ : 0 < a₁ + a₂ - 1 := by linarith
  have hc₂₃ : 0 < a₂ + a₃ - 1 := by linarith
  have hc₃₄ : 0 < a₃ + a₄ - 1 := by linarith

  have he₁base := invMul_tangent ha₁pos (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 14 / 5) (by norm_num : (0 : ℝ) < 1)
  have he₁ : (10 / 7 : ℝ) - (25 / 98) * a₁ ≤ 2 / a₁ := by
    norm_num [div_eq_mul_inv] at he₁base ⊢
    linarith [he₁base]

  have h₁₂a := invMul_tangent ha₁pos hc₁₂
    (by norm_num : (0 : ℝ) < 14 / 5) (by norm_num : (0 : ℝ) < 18 / 5)
  have h₁₂b := invMul_tangent ha₂pos hc₁₂
    (by norm_num : (0 : ℝ) < 9 / 5) (by norm_num : (0 : ℝ) < 18 / 5)
  have hp₁₂ :
      (33925 / 40824 : ℝ) - (15125 / 142884) * a₁ - (2125 / 13608) * a₂
        ≤ hullSixPairTerm a₁ a₂ := by
    rw [hullSixPairTerm_eq a₁ a₂ ha₁pos ha₂pos hc₁₂]
    norm_num [div_eq_mul_inv] at h₁₂a h₁₂b ⊢
    linarith [h₁₂a, h₁₂b]

  have h₂₃a := invMul_tangent ha₂pos hc₂₃
    (by norm_num : (0 : ℝ) < 9 / 5) (by norm_num : (0 : ℝ) < 123 / 40)
  have h₂₃b := invMul_tangent ha₃pos hc₂₃
    (by norm_num : (0 : ℝ) < 91 / 40) (by norm_num : (0 : ℝ) < 123 / 40)
  have hp₂₃ :
      (13333400 / 12390651 : ℝ) - (7643000 / 37171953) * a₂ -
          (189512000 / 1127549241) * a₃
        ≤ hullSixPairTerm a₂ a₃ := by
    rw [hullSixPairTerm_eq a₂ a₃ ha₂pos ha₃pos hc₂₃]
    norm_num [div_eq_mul_inv] at h₂₃a h₂₃b ⊢
    linarith [h₂₃a, h₂₃b]

  have h₃₄a := invMul_tangent ha₃pos hc₃₄
    (by norm_num : (0 : ℝ) < 91 / 40) (by norm_num : (0 : ℝ) < 29 / 10)
  have h₃₄b := invMul_tangent ha₄pos hc₃₄
    (by norm_num : (0 : ℝ) < 13 / 8) (by norm_num : (0 : ℝ) < 29 / 10)
  have hp₃₄ :
      (93120 / 76531 : ℝ) - (1337600 / 6964321) * a₃ -
          (254720 / 994903) * a₄
        ≤ hullSixPairTerm a₃ a₄ := by
    rw [hullSixPairTerm_eq a₃ a₄ ha₃pos ha₄pos hc₃₄]
    norm_num [div_eq_mul_inv] at h₃₄a h₃₄b ⊢
    linarith [h₃₄a, h₃₄b]

  have he₄base := invMul_tangent ha₄pos (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 13 / 8) (by norm_num : (0 : ℝ) < 1)
  have he₄ : (16 / 13 : ℝ) - (64 / 169) * a₄ ≤ 1 / a₄ := by
    norm_num [div_eq_mul_inv] at he₄base ⊢
    linarith [he₄base]

  have hsupport :
      (139 / 24 : ℝ) - (4 / 11) * (a₁ + a₂ + a₃) - (7 / 11) * a₄ ≤
        2 / a₁ + hullSixPairTerm a₁ a₂ + hullSixPairTerm a₂ a₃ +
          hullSixPairTerm a₃ a₄ + 1 / a₄ := by
    linarith [he₁, hp₁₂, hp₂₃, hp₃₄, he₄]
  linarith [hsupport]

/-- The requested `9/4` form. -/
theorem hullSix_L14_ge_nine_fourths
    (a₁ a₂ a₃ a₄ : ℝ)
    (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (ha₃ : 1 ≤ a₃) (ha₄ : 1 ≤ a₄)
    (hsum : a₁ + a₂ + a₃ + a₄ ≤ 17 / 2)
    (ha₄cap : a₄ ≤ 13 / 8) :
    9 / 4 ≤
      2 / a₁ + hullSixPairTerm a₁ a₂ + hullSixPairTerm a₂ a₃ +
        hullSixPairTerm a₃ a₄ + 1 / a₄ := by
  have h := hullSix_L14_ge_149_div_66 a₁ a₂ a₃ a₄
    ha₁ ha₂ ha₃ ha₄ hsum ha₄cap
  norm_num at h ⊢
  linarith

end Heilbronn8
