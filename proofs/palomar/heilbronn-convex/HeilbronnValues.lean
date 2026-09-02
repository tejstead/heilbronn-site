import Mathlib

namespace HeilbronnValues

/-- The quintic defining the n = 8 value. -/
def P8 (x : ℝ) : ℝ :=
  2060 * x ^ 5 - 2332 * x ^ 4 + 1064 * x ^ 3 - 240 * x ^ 2 + 26 * x - 1
#print axioms P8

lemma P8_left_neg : P8 (79 / 1000) < 0 := by
  unfold P8
  norm_num
#print axioms P8_left_neg

lemma P8_right_pos : 0 < P8 (81 / 1000) := by
  unfold P8
  norm_num
#print axioms P8_right_pos

/-- A positive lower bound for the slope polynomial of `P8` on its bracket. -/
lemma P8_slope_pos {x y : ℝ} (hx1 : 79 / 1000 ≤ x) (hx2 : x ≤ 81 / 1000)
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
#print axioms P8_slope_pos

lemma P8_strictMonoOn :
    StrictMonoOn P8 (Set.Icc (79 / 1000 : ℝ) (81 / 1000)) := by
  intro x hx y hy hxy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hS := P8_slope_pos hx1 hx2 hy1 hy2
  have key : P8 y - P8 x
      = (y - x) * (2060 * (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4)
        - 2332 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
        + 1064 * (y ^ 2 + y * x + x ^ 2) - 240 * (y + x) + 26) := by
    unfold P8
    ring
  nlinarith [mul_pos (sub_pos.mpr hxy) hS]
#print axioms P8_strictMonoOn

lemma P8_exists_root :
    ∃ x ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000), P8 x = 0 := by
  have hcont : ContinuousOn P8 (Set.Icc (79 / 1000 : ℝ) (81 / 1000)) := by
    apply Continuous.continuousOn
    unfold P8
    fun_prop
  have hsub := intermediate_value_Icc
    (by norm_num : (79 / 1000 : ℝ) ≤ 81 / 1000) hcont
  have h0 : (0 : ℝ) ∈ Set.Icc (P8 (79 / 1000)) (P8 (81 / 1000)) :=
    ⟨P8_left_neg.le, P8_right_pos.le⟩
  obtain ⟨x, hx, hPx⟩ := hsub h0
  exact ⟨x, hx, hPx⟩
#print axioms P8_exists_root

theorem v8_existsUnique :
    ExistsUnique (fun x : ℝ => 79 / 1000 < x ∧ x < 81 / 1000 ∧ P8 x = 0) := by
  obtain ⟨x, hx, hPx⟩ := P8_exists_root
  have hxgt : (79 / 1000 : ℝ) < x := by
    rcases lt_or_eq_of_le hx.1 with h | h
    · exact h
    · subst x
      nlinarith [P8_left_neg]
  have hxlt : x < (81 / 1000 : ℝ) := by
    rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · subst x
      nlinarith [P8_right_pos]
  refine ⟨x, ⟨hxgt, hxlt, hPx⟩, ?_⟩
  rintro y ⟨hygt, hylt, hPy⟩
  have hxc : x ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000) :=
    ⟨hxgt.le, hxlt.le⟩
  have hyc : y ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000) :=
    ⟨hygt.le, hylt.le⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmono := P8_strictMonoOn hyc hxc h
    rw [hPx, hPy] at hmono
    exact lt_irrefl 0 hmono
  · have hmono := P8_strictMonoOn hxc hyc h
    rw [hPx, hPy] at hmono
    exact lt_irrefl 0 hmono
#print axioms v8_existsUnique

/-- The unique root of `P8` in the strict rational bracket. -/
noncomputable def v8 : ℝ := Classical.choose v8_existsUnique.exists
#print axioms v8

theorem v8_root : P8 v8 = 0 :=
  (Classical.choose_spec v8_existsUnique.exists).2.2
#print axioms v8_root

theorem v8_gt : (79 / 1000 : ℝ) < v8 :=
  (Classical.choose_spec v8_existsUnique.exists).1
#print axioms v8_gt

theorem v8_lt : v8 < (81 / 1000 : ℝ) :=
  (Classical.choose_spec v8_existsUnique.exists).2.1
#print axioms v8_lt

/-- The quadratic defining the n = 5 value. -/
def P5 (x : ℝ) : ℝ := 5 * x ^ 2 - 5 * x + 1
#print axioms P5

lemma P5_strictAntiOn :
    StrictAntiOn P5 (Set.Ioo (276 / 1000 : ℝ) (277 / 1000)) := by
  intro x hx y hy hxy
  have hS : 5 * (y + x) - 5 < 0 := by
    nlinarith [hx.2, hy.2]
  have key : P5 y - P5 x = (y - x) * (5 * (y + x) - 5) := by
    unfold P5
    ring
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hS]
#print axioms P5_strictAntiOn

theorem v5_existsUnique :
    ExistsUnique (fun x : ℝ => 276 / 1000 < x ∧ x < 277 / 1000 ∧ P5 x = 0) := by
  let r : ℝ := (5 - Real.sqrt 5) / 10
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hrgt : (276 / 1000 : ℝ) < r := by
    dsimp [r]
    nlinarith
  have hrlt : r < (277 / 1000 : ℝ) := by
    dsimp [r]
    nlinarith
  have hrroot : P5 r = 0 := by
    dsimp [r]
    unfold P5
    nlinarith
  refine ⟨r, ⟨hrgt, hrlt, hrroot⟩, ?_⟩
  rintro y ⟨hygt, hylt, hPy⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hanti := P5_strictAntiOn ⟨hygt, hylt⟩ ⟨hrgt, hrlt⟩ h
    rw [hrroot, hPy] at hanti
    exact lt_irrefl 0 hanti
  · have hanti := P5_strictAntiOn ⟨hrgt, hrlt⟩ ⟨hygt, hylt⟩ h
    rw [hrroot, hPy] at hanti
    exact lt_irrefl 0 hanti
#print axioms v5_existsUnique

/-- The unique root of `P5` in the strict rational bracket. -/
noncomputable def v5 : ℝ := Classical.choose v5_existsUnique.exists
#print axioms v5

theorem v5_root : P5 v5 = 0 :=
  (Classical.choose_spec v5_existsUnique.exists).2.2
#print axioms v5_root

theorem v5_gt : (276 / 1000 : ℝ) < v5 :=
  (Classical.choose_spec v5_existsUnique.exists).1
#print axioms v5_gt

theorem v5_lt : v5 < (277 / 1000 : ℝ) :=
  (Classical.choose_spec v5_existsUnique.exists).2.1
#print axioms v5_lt

theorem v5_eq : v5 = (5 - Real.sqrt 5) / 10 := by
  apply v5_existsUnique.unique
  · exact Classical.choose_spec v5_existsUnique.exists
  · have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hs2 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    constructor
    · nlinarith
    constructor
    · nlinarith
    · unfold P5
      nlinarith
#print axioms v5_eq

end HeilbronnValues
