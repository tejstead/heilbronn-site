/-
Value layer for the convex Heilbronn n = 8 theorem.

`v8` is the unique real root in [79/1000, 81/1000] of
  P(v) = 2060 v^5 - 2332 v^4 + 1064 v^3 - 240 v^2 + 26 v - 1.

Existence: exact rational sign change at the endpoints plus the
intermediate value theorem. Uniqueness: P is strictly monotone on the
bracket, shown division-free by factoring P(y) - P(x) through the slope
polynomial and bounding it below termwise. No `Polynomial.roots`, no
Sturm sequences; `v8` enters all later files only through `v8_root`
(the defining equation) and rational bracket lemmas.
-/
import Mathlib

namespace Heilbronn8

/-- The defining quintic of the n = 8 optimal ratio. -/
def P (x : ℝ) : ℝ :=
  2060 * x ^ 5 - 2332 * x ^ 4 + 1064 * x ^ 3 - 240 * x ^ 2 + 26 * x - 1

lemma P_left_neg : P (79 / 1000) < 0 := by unfold P; norm_num

lemma P_right_pos : 0 < P (81 / 1000) := by unfold P; norm_num

/-- Termwise lower bound for the slope polynomial of `P` on the bracket:
degree-4 monomials are at least `(79/1000)^4`, degree-3 monomials at most
`(81/1000)^3`, and so on; the alternating coefficient signs leave the
rational value `24851761863/10^10 > 0`. -/
lemma slope_pos {x y : ℝ} (hx1 : 79 / 1000 ≤ x) (hx2 : x ≤ 81 / 1000)
    (hy1 : 79 / 1000 ≤ y) (hy2 : y ≤ 81 / 1000) :
    0 < 2060 * (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4)
      - 2332 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
      + 1064 * (y ^ 2 + y * x + x ^ 2) - 240 * (y + x) + 26 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hx2l : (79 / 1000 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
  have hx2u : x ^ 2 ≤ (81 / 1000 : ℝ) ^ 2 := by nlinarith
  have hx3l : (79 / 1000 : ℝ) ^ 3 ≤ x ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2l) (sub_nonneg.mpr hx1)]
  have hx3u : x ^ 3 ≤ (81 / 1000 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2u) (sub_nonneg.mpr hx2)]
  have hx4l : (79 / 1000 : ℝ) ^ 4 ≤ x ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx3l) (sub_nonneg.mpr hx1)]
  have hy2l : (79 / 1000 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
  have hy2u : y ^ 2 ≤ (81 / 1000 : ℝ) ^ 2 := by nlinarith
  have hy3l : (79 / 1000 : ℝ) ^ 3 ≤ y ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2l) (sub_nonneg.mpr hy1)]
  have hy3u : y ^ 3 ≤ (81 / 1000 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2u) (sub_nonneg.mpr hy2)]
  have hy4l : (79 / 1000 : ℝ) ^ 4 ≤ y ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy3l) (sub_nonneg.mpr hy1)]
  have hm31 : (79 / 1000 : ℝ) ^ 4 ≤ y ^ 3 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy3l) (sub_nonneg.mpr hx1)]
  have hm22 : (79 / 1000 : ℝ) ^ 4 ≤ y ^ 2 * x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2l) (sub_nonneg.mpr hx2l)]
  have hm13 : (79 / 1000 : ℝ) ^ 4 ≤ y * x ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hx3l)]
  have hn21 : y ^ 2 * x ≤ (81 / 1000 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2u) (sub_nonneg.mpr hx2),
      mul_nonneg hy0 hy0]
  have hn12 : y * x ^ 2 ≤ (81 / 1000 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2) (sub_nonneg.mpr hx2u),
      mul_nonneg hx0 hx0]
  have hp11 : (79 / 1000 : ℝ) ^ 2 ≤ y * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hx1)]
  linarith

lemma P_strictMonoOn :
    StrictMonoOn P (Set.Icc (79 / 1000 : ℝ) (81 / 1000)) := by
  intro x hx y hy hxy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hS := slope_pos hx1 hx2 hy1 hy2
  have key : P y - P x
      = (y - x) * (2060 * (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4)
        - 2332 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
        + 1064 * (y ^ 2 + y * x + x ^ 2) - 240 * (y + x) + 26) := by
    unfold P; ring
  nlinarith [mul_pos (sub_pos.mpr hxy) hS]

lemma exists_root :
    ∃ x ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000), P x = 0 := by
  have hcont : ContinuousOn P (Set.Icc (79 / 1000 : ℝ) (81 / 1000)) := by
    apply Continuous.continuousOn
    unfold P
    fun_prop
  have hsub := intermediate_value_Icc
    (by norm_num : (79 / 1000 : ℝ) ≤ 81 / 1000) hcont
  have h0 : (0 : ℝ) ∈ Set.Icc (P (79 / 1000)) (P (81 / 1000)) :=
    ⟨P_left_neg.le, P_right_pos.le⟩
  obtain ⟨x, hx, hPx⟩ := hsub h0
  exact ⟨x, hx, hPx⟩

theorem v8_existsUnique :
    ∃! x : ℝ, x ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000) ∧ P x = 0 := by
  obtain ⟨x, hx, hPx⟩ := exists_root
  refine ⟨x, ⟨hx, hPx⟩, ?_⟩
  rintro y ⟨hy, hPy⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := P_strictMonoOn hy hx h
    rw [hPx, hPy] at this
    exact lt_irrefl 0 this
  · have := P_strictMonoOn hx hy h
    rw [hPx, hPy] at this
    exact lt_irrefl 0 this

/-- The n = 8 optimal ratio: the unique root of `P` in the bracket. -/
noncomputable def v8 : ℝ := Classical.choose v8_existsUnique.exists

lemma v8_spec : v8 ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000) ∧ P v8 = 0 :=
  Classical.choose_spec v8_existsUnique.exists

theorem v8_root : P v8 = 0 := v8_spec.2

theorem v8_mem : v8 ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000) := v8_spec.1

theorem v8_unique {x : ℝ} (hx : x ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000))
    (hPx : P x = 0) : x = v8 :=
  v8_existsUnique.unique ⟨hx, hPx⟩ v8_spec

/-- Any bracket point with `P < 0` lies strictly below `v8`. -/
lemma lt_v8_of_P_neg {q : ℝ}
    (hq : q ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000)) (hPq : P q < 0) :
    q < v8 := by
  rcases lt_trichotomy q v8 with h | h | h
  · exact h
  · rw [h, v8_root] at hPq
    exact absurd hPq (lt_irrefl 0)
  · have := P_strictMonoOn v8_mem hq h
    rw [v8_root] at this
    linarith

/-- Any bracket point with `P > 0` lies strictly above `v8`. -/
lemma v8_lt_of_P_pos {q : ℝ}
    (hq : q ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000)) (hPq : 0 < P q) :
    v8 < q := by
  rcases lt_trichotomy v8 q with h | h | h
  · exact h
  · rw [← h, v8_root] at hPq
    exact absurd hPq (lt_irrefl 0)
  · have := P_strictMonoOn hq v8_mem h
    rw [v8_root] at this
    linarith

theorem v8_gt : (79 / 1000 : ℝ) < v8 :=
  lt_v8_of_P_neg ⟨le_rfl, by norm_num⟩ P_left_neg

theorem v8_lt : v8 < (81 / 1000 : ℝ) :=
  v8_lt_of_P_pos ⟨by norm_num, le_rfl⟩ P_right_pos

theorem v8_pos : 0 < v8 := lt_trans (by norm_num) v8_gt

/-- Sharp working bracket, width `10^-15`:
`v8 = 0.080000139329466438...`. -/
theorem v8_lb : (80000139329466 : ℝ) / 10 ^ 15 < v8 :=
  lt_v8_of_P_neg (by constructor <;> norm_num) (by unfold P; norm_num)

theorem v8_ub : v8 < (80000139329467 : ℝ) / 10 ^ 15 :=
  v8_lt_of_P_pos (by constructor <;> norm_num) (by unfold P; norm_num)

/-- Reduction relation for `Q(v8)` arithmetic: all generated certificate
coefficients are degree-`< 5` polynomials in `v8` reduced through this. -/
theorem v8_pow_five :
    2060 * v8 ^ 5 = 2332 * v8 ^ 4 - 1064 * v8 ^ 3 + 240 * v8 ^ 2 - 26 * v8 + 1 := by
  have h := v8_root
  unfold P at h
  linarith

end Heilbronn8
