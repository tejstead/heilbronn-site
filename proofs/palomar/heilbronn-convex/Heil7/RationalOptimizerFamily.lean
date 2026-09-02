import Heil7.CanonicalUpper

/-!
# A rational one-parameter family of seven-point optimizers

For `1 ≤ t ≤ 8/7`, the configuration

`[(2,0), (2t,t), (0,2), (-t,t), (-2,-2), (-t,-2t), (0,0)]`

has doubled hull area `18t` and minimum doubled triangle area `2t`.
Thus every member has ratio `1/9`.  Scaling only the first coordinate by
`1/(9t)` gives a rational unit-area representative whenever `t` is rational.

The last section separates the gauge classes.  The invariant used there is
the sum of the squares of all 35 doubled triangle areas, divided by the square
of the doubled hull area.  It is written as an ordered sum divided by six so
that invariance under arbitrary relabeling is immediate.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

open MeasureTheory

/-! ## The family and its hexagonal hull -/

/-- The rational optimizer family, with its interior point in slot six. -/
def rationalOptimizerFamily (t : ℝ) : Configuration7 :=
  ![((2 : ℝ), 0), (2 * t, t), (0, 2), (-t, t),
    (-2, -2), (-t, -2 * t), (0, 0)]

/-- The first six entries of `rationalOptimizerFamily`, in cyclic hull order. -/
def rationalOptimizerHex (t : ℝ) : Fin 6 → ℝ × ℝ :=
  ![((2 : ℝ), 0), (2 * t, t), (0, 2), (-t, t),
    (-2, -2), (-t, -2 * t)]

@[simp] lemma rationalOptimizerFamily_zero (t : ℝ) :
    rationalOptimizerFamily t 0 = ((2 : ℝ), 0) := rfl
@[simp] lemma rationalOptimizerFamily_one (t : ℝ) :
    rationalOptimizerFamily t 1 = (2 * t, t) := rfl
@[simp] lemma rationalOptimizerFamily_two (t : ℝ) :
    rationalOptimizerFamily t 2 = (0, 2) := rfl
@[simp] lemma rationalOptimizerFamily_three (t : ℝ) :
    rationalOptimizerFamily t 3 = (-t, t) := rfl
@[simp] lemma rationalOptimizerFamily_four (t : ℝ) :
    rationalOptimizerFamily t 4 = (-2, -2) := rfl
@[simp] lemma rationalOptimizerFamily_five (t : ℝ) :
    rationalOptimizerFamily t 5 = (-t, -2 * t) := rfl
@[simp] lemma rationalOptimizerFamily_six (t : ℝ) :
    rationalOptimizerFamily t 6 = (0, 0) := rfl

@[simp] lemma rationalOptimizerHex_zero (t : ℝ) :
    rationalOptimizerHex t 0 = ((2 : ℝ), 0) := rfl
@[simp] lemma rationalOptimizerHex_one (t : ℝ) :
    rationalOptimizerHex t 1 = (2 * t, t) := rfl
@[simp] lemma rationalOptimizerHex_two (t : ℝ) :
    rationalOptimizerHex t 2 = (0, 2) := rfl
@[simp] lemma rationalOptimizerHex_three (t : ℝ) :
    rationalOptimizerHex t 3 = (-t, t) := rfl
@[simp] lemma rationalOptimizerHex_four (t : ℝ) :
    rationalOptimizerHex t 4 = (-2, -2) := rfl
@[simp] lemma rationalOptimizerHex_five (t : ℝ) :
    rationalOptimizerHex t 5 = (-t, -2 * t) := rfl

/-- On the stated interval the first six points are a strict CCW hexagon. -/
theorem rationalOptimizerHex_strict (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    ∀ i j k : Fin 6, i < j → j < k →
      0 < HullBridge.sig (rationalOptimizerHex t i)
        (rationalOptimizerHex t j) (rationalOptimizerHex t k) := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have htlt : t < 2 := lt_of_le_of_lt ht.2 (by norm_num)
  have hA : 0 < 6 * t - 4 := by
    linarith only [ht.1]
  have hB : 0 < 3 * t * t := by
    exact mul_pos (mul_pos (by norm_num) htpos) htpos
  have hC : 0 < (4 : ℝ) := by
    norm_num
  have hD : 0 < 3 * t * (2 - t) := by
    exact mul_pos (mul_pos (by norm_num) htpos) (sub_pos.mpr htlt)
  have hE : 0 < (12 : ℝ) := by
    norm_num
  have hF : 0 < 6 * t + 4 := by
    exact add_pos (mul_pos (by norm_num) htpos) (by norm_num)
  have hG : 0 < 3 * t * (t + 2) := by
    exact mul_pos (mul_pos (by norm_num) htpos)
      (add_pos htpos (by norm_num))
  have hH : 0 < 9 * t * t := by
    exact mul_pos (mul_pos (by norm_num) htpos) htpos
  intro i j k hij hjk
  rcases triple_cases6 i j k hij hjk with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    simp only [HullBridge.sig, rationalOptimizerHex_zero,
      rationalOptimizerHex_one, rationalOptimizerHex_two,
      rationalOptimizerHex_three, rationalOptimizerHex_four,
      rationalOptimizerHex_five]
  · convert hA using 1 <;> ring
  · convert hB using 1 <;> ring
  · convert hC using 1 <;> ring
  · convert hD using 1 <;> ring
  · convert hC using 1 <;> ring
  · convert hE using 1 <;> ring
  · convert hF using 1 <;> ring
  · convert hF using 1 <;> ring
  · convert hG using 1 <;> ring
  · convert hA using 1 <;> ring
  · convert hD using 1 <;> ring
  · convert hF using 1 <;> ring
  · convert hG using 1 <;> ring
  · convert hG using 1 <;> ring
  · convert hH using 1 <;> ring
  · convert hB using 1 <;> ring
  · convert hA using 1 <;> ring
  · convert hB using 1 <;> ring
  · convert hC using 1 <;> ring
  · convert hD using 1 <;> ring

/-- The origin is the average of hull vertices zero, two, and four. -/
theorem rationalOptimizerOrigin_mem (t : ℝ) :
    ((0 : ℝ), (0 : ℝ)) ∈
      convexHull ℝ (Set.range (rationalOptimizerHex t)) := by
  have hconv := convex_convexHull ℝ (Set.range (rationalOptimizerHex t))
  have h0 : rationalOptimizerHex t 0 ∈
      convexHull ℝ (Set.range (rationalOptimizerHex t)) :=
    subset_convexHull ℝ _ ⟨0, rfl⟩
  have h2 : rationalOptimizerHex t 2 ∈
      convexHull ℝ (Set.range (rationalOptimizerHex t)) :=
    subset_convexHull ℝ _ ⟨2, rfl⟩
  have h4 : rationalOptimizerHex t 4 ∈
      convexHull ℝ (Set.range (rationalOptimizerHex t)) :=
    subset_convexHull ℝ _ ⟨4, rfl⟩
  have hm := hconv h0 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  have hf := hconv hm h4 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (2 : ℝ) / 3 + 1 / 3 = 1)
  have hval :
      ((2 : ℝ) / 3) • (((1 : ℝ) / 2) • rationalOptimizerHex t 0 +
          ((1 : ℝ) / 2) • rationalOptimizerHex t 2) +
        ((1 : ℝ) / 3) • rationalOptimizerHex t 4 =
          ((0 : ℝ), (0 : ℝ)) := by
    rw [Prod.ext_iff]
    simp only [rationalOptimizerHex_zero, rationalOptimizerHex_two,
      rationalOptimizerHex_four, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul]
    norm_num
  rwa [hval] at hf

lemma range_rationalOptimizerFamily (t : ℝ) :
    Set.range (rationalOptimizerFamily t) =
      insert ((0 : ℝ), (0 : ℝ)) (Set.range (rationalOptimizerHex t)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Set.mem_insert_of_mem _ ⟨0, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨1, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨2, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨3, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨4, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨5, rfl⟩
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_range] at hx
    rcases hx with rfl | ⟨j, rfl⟩
    · exact ⟨6, rfl⟩
    · rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩

/-- Adding the interior origin does not change the convex hull. -/
theorem rationalOptimizerFamily_hull_eq (t : ℝ) :
    convexHull ℝ (Set.range (rationalOptimizerFamily t)) =
      convexHull ℝ (Set.range (rationalOptimizerHex t)) := by
  rw [range_rationalOptimizerFamily]
  apply Set.Subset.antisymm
  · exact convexHull_min
      (Set.insert_subset_iff.mpr
        ⟨rationalOptimizerOrigin_mem t, subset_convexHull ℝ _⟩)
      (convex_convexHull ℝ _)
  · exact convexHull_mono (Set.subset_insert _ _)

/-! ## Exact area and minimum -/

theorem rationalOptimizerHex_volume (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    volume (convexHull ℝ (Set.range (rationalOptimizerHex t))) =
      ENNReal.ofReal (9 * t) := by
  rw [HullBridge.volume_convexHull_strictCCW6 _
    (rationalOptimizerHex_strict t ht)]
  congr 1
  simp only [HullBridge.sig, rationalOptimizerHex_zero,
    rationalOptimizerHex_one, rationalOptimizerHex_two,
    rationalOptimizerHex_three, rationalOptimizerHex_four,
    rationalOptimizerHex_five]
  ring

theorem rationalOptimizerFamily_volume (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    volume (convexHull ℝ (Set.range (rationalOptimizerFamily t))) =
      ENNReal.ofReal (9 * t) := by
  rw [rationalOptimizerFamily_hull_eq,
    rationalOptimizerHex_volume t ht]

/-- The exact doubled hull area is `18t`. -/
theorem rationalOptimizerFamily_doubledHullArea (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    HullBridge.doubledHullArea (rationalOptimizerFamily t) = 18 * t := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  rw [HullBridge.doubledHullArea, rationalOptimizerFamily_volume t ht,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) ht0)]
  ring

/-- The exact minimum doubled triangle area is `2t`. -/
theorem rationalOptimizerFamily_minTri (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    minTri (rationalOptimizerFamily t) = 2 * t := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have ht2 : 0 ≤ 2 * t := mul_nonneg (by norm_num) ht0
  have h2lower : 2 ≤ 3 * t := by
    linarith only [ht.1]
  have h4upper : 3 * t ≤ 4 := by
    linarith only [ht.2]
  have hhigh : 0 ≤ t * (4 - 3 * t) :=
    mul_nonneg ht0 (sub_nonneg.mpr h4upper)
  have hA : 2 * t ≤ 6 * t - 4 := by
    linarith only [ht.1]
  have hB : 2 * t ≤ 3 * t * t := by
    exact mul_le_mul_of_nonneg_right h2lower ht0
  have hC : 2 * t ≤ 4 := by
    linarith only [ht.2]
  have hD : 2 * t ≤ 3 * t * (2 - t) := by
    calc
      2 * t ≤ 2 * t + t * (4 - 3 * t) :=
        le_add_of_nonneg_right hhigh
      _ = 3 * t * (2 - t) := by ring
  have hE : 2 * t ≤ 12 := hC.trans (by norm_num)
  have hF : 2 * t ≤ 6 * t + 4 := by
    linarith only [ht0]
  have hG : 2 * t ≤ 3 * t * (t + 2) := by
    have hcoef : 2 ≤ 3 * (t + 2) := by
      linarith only [ht.1]
    have hmul := mul_le_mul_of_nonneg_left hcoef ht0
    calc
      2 * t = t * 2 := by ring
      _ ≤ t * (3 * (t + 2)) := hmul
      _ = 3 * t * (t + 2) := by ring
  have hH : 2 * t ≤ 9 * t * t := by
    have hcoef : 2 ≤ 9 * t := by
      linarith only [ht.1]
    have hmul := mul_le_mul_of_nonneg_left hcoef ht0
    calc
      2 * t = t * 2 := by ring
      _ ≤ t * (9 * t) := hmul
      _ = 9 * t * t := by ring
  have hI : 2 * t ≤ 2 * t := le_rfl
  have hJ : 2 * t ≤ 4 * t := by
    exact mul_le_mul_of_nonneg_right (by norm_num) ht0
  have habs_of_eq {z w : ℝ} (hzw : z = w) (hw : 2 * t ≤ w) :
      2 * t ≤ |z| := by
    rw [hzw]
    exact hw.trans (le_abs_self w)
  have habs_of_eq_neg {z w : ℝ} (hzw : z = -w) (hw : 2 * t ≤ w) :
      2 * t ≤ |z| := by
    rw [hzw, abs_neg]
    exact hw.trans (le_abs_self w)
  apply le_antisymm
  · calc
      minTri (rationalOptimizerFamily t) ≤
          |sig (rationalOptimizerFamily t 0)
            (rationalOptimizerFamily t 1)
            (rationalOptimizerFamily t 6)| :=
        minTri_le (rationalOptimizerFamily t) 0 1 6
          (by decide) (by decide)
      _ = 2 * t := by
        rw [show sig (rationalOptimizerFamily t 0)
              (rationalOptimizerFamily t 1)
              (rationalOptimizerFamily t 6) = 2 * t by
          simp only [sig, rationalOptimizerFamily_zero,
            rationalOptimizerFamily_one, rationalOptimizerFamily_six]
          ring]
        exact abs_of_nonneg ht2
  · apply le_minTri
    intro q hq
    have hmem : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    rcases triple_cases7 q.1 q.2.1 q.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩
    all_goals
      rw [q0, q1, q2]
      simp only [sig, rationalOptimizerFamily_zero,
        rationalOptimizerFamily_one, rationalOptimizerFamily_two,
        rationalOptimizerFamily_three, rationalOptimizerFamily_four,
        rationalOptimizerFamily_five, rationalOptimizerFamily_six]
    · refine habs_of_eq ?_ hA
      ring
    · refine habs_of_eq ?_ hB
      ring
    · refine habs_of_eq ?_ hC
      ring
    · refine habs_of_eq ?_ hD
      ring
    · refine habs_of_eq ?_ hI
      ring
    · refine habs_of_eq ?_ hC
      ring
    · refine habs_of_eq ?_ hE
      ring
    · refine habs_of_eq ?_ hF
      ring
    · refine habs_of_eq ?_ hC
      ring
    · refine habs_of_eq ?_ hF
      ring
    · refine habs_of_eq ?_ hG
      ring
    · refine habs_of_eq ?_ hI
      ring
    · refine habs_of_eq ?_ hA
      ring
    · refine habs_of_eq_neg ?_ hC
      ring
    · refine habs_of_eq_neg ?_ hJ
      ring
    · refine habs_of_eq ?_ hD
      ring
    · refine habs_of_eq ?_ hF
      ring
    · refine habs_of_eq ?_ hG
      ring
    · refine habs_of_eq ?_ hJ
      ring
    · refine habs_of_eq ?_ hG
      ring
    · refine habs_of_eq ?_ hH
      ring
    · refine habs_of_eq ?_ hB
      ring
    · refine habs_of_eq ?_ hB
      ring
    · refine habs_of_eq_neg ?_ hI
      ring
    · refine habs_of_eq_neg ?_ hB
      ring
    · refine habs_of_eq ?_ hA
      ring
    · refine habs_of_eq ?_ hB
      ring
    · refine habs_of_eq ?_ hI
      ring
    · refine habs_of_eq ?_ hC
      ring
    · refine habs_of_eq ?_ hC
      ring
    · refine habs_of_eq ?_ hI
      ring
    · refine habs_of_eq ?_ hD
      ring
    · refine habs_of_eq ?_ hJ
      ring
    · refine habs_of_eq ?_ hB
      ring
    · refine habs_of_eq ?_ hI
      ring

/-- Every member has the sharp scale-free ratio `1/9`. -/
theorem rationalOptimizerFamily_ratio (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    minTri (rationalOptimizerFamily t) /
      HullBridge.doubledHullArea (rationalOptimizerFamily t) = 1 / 9 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  rw [rationalOptimizerFamily_minTri t ht,
    rationalOptimizerFamily_doubledHullArea t ht]
  field_simp [htpos.ne'] <;> ring

/-! ## A rational unit-area representative and attainment -/

/-- Scale the first coordinate by `1/(9t)`.  Its determinant is `1/(9t)`,
so this sends hull area `9t` to one without introducing square roots. -/
noncomputable def rationalOptimizerUnit (t : ℝ) : Configuration7 :=
  fun i => HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0
    (rationalOptimizerFamily t i)

lemma range_rationalOptimizerUnit (t : ℝ) :
    Set.range (rationalOptimizerUnit t) =
      HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0 ''
        Set.range (rationalOptimizerFamily t) := by
  change Set.range (fun i : Fin 7 =>
      HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0
        (rationalOptimizerFamily t i)) =
    HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0 ''
      Set.range (rationalOptimizerFamily t)
  exact HullBridge.range_affMap (1 / (9 * t)) 0 0 1 0 0
    (rationalOptimizerFamily t)

theorem rationalOptimizerUnit_volume (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    volume (convexHull ℝ (Set.range (rationalOptimizerUnit t))) = 1 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hscale : 0 < (1 : ℝ) / (9 * t) :=
    div_pos (by norm_num) (mul_pos (by norm_num) htpos)
  rw [range_rationalOptimizerUnit]
  rw [HullBridge.volume_convexHull_image_affMap _ _ _ _ _ _
    (by simpa only [mul_one, zero_mul, sub_zero] using hscale)]
  simp only [mul_one, zero_mul, sub_zero]
  rw [rationalOptimizerFamily_volume t ht,
    ← ENNReal.ofReal_mul hscale.le]
  rw [show ((1 : ℝ) / (9 * t)) * (9 * t) = 1 by
    field_simp [htpos.ne'] <;> ring]
  exact ENNReal.ofReal_one

lemma rationalOptimizerUnit_abs_sig (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) (i j k : Fin 7) :
    |sig (rationalOptimizerUnit t i) (rationalOptimizerUnit t j)
        (rationalOptimizerUnit t k)| =
      (1 / (9 * t)) *
        |sig (rationalOptimizerFamily t i) (rationalOptimizerFamily t j)
          (rationalOptimizerFamily t k)| := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hscale : 0 < (1 : ℝ) / (9 * t) :=
    div_pos (by norm_num) (mul_pos (by norm_num) htpos)
  unfold rationalOptimizerUnit
  change |HullBridge.sig
      (HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0
        (rationalOptimizerFamily t i))
      (HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0
        (rationalOptimizerFamily t j))
      (HullBridge.affMap (1 / (9 * t)) 0 0 1 0 0
        (rationalOptimizerFamily t k))| =
    (1 / (9 * t)) *
      |HullBridge.sig (rationalOptimizerFamily t i)
        (rationalOptimizerFamily t j) (rationalOptimizerFamily t k)|
  rw [HullBridge.sig_affMap]
  simp only [mul_one, zero_mul, sub_zero, abs_mul, abs_of_pos hscale]

theorem rationalOptimizerUnit_minTri (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    minTri (rationalOptimizerUnit t) = 2 / 9 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hscale : 0 ≤ (1 : ℝ) / (9 * t) :=
    (div_pos (by norm_num) (mul_pos (by norm_num) htpos)).le
  apply le_antisymm
  · have h := minTri_le (rationalOptimizerUnit t) 0 1 6
      (by decide) (by decide)
    refine h.trans (le_of_eq ?_)
    rw [rationalOptimizerUnit_abs_sig t ht]
    simp only [sig, rationalOptimizerFamily_zero,
      rationalOptimizerFamily_one, rationalOptimizerFamily_six]
    rw [abs_of_nonneg (by nlinarith)]
    field_simp [htpos.ne'] <;> ring
  · apply le_minTri
    intro q hq
    have hmem : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    have hbase := minTri_le (rationalOptimizerFamily t)
      q.1 q.2.1 q.2.2 hmem.1 hmem.2
    rw [rationalOptimizerFamily_minTri t ht] at hbase
    rw [rationalOptimizerUnit_abs_sig t ht]
    calc
      (2 : ℝ) / 9 = (1 / (9 * t)) * (2 * t) := by
        field_simp [htpos.ne'] <;> ring
      _ ≤ (1 / (9 * t)) *
          |sig (rationalOptimizerFamily t q.1)
            (rationalOptimizerFamily t q.2.1)
            (rationalOptimizerFamily t q.2.2)| :=
        mul_le_mul_of_nonneg_left hbase hscale

/-- Every parameter in the interval supplies a unit-area witness attaining
the seven-point score `v7 = 1/9`. -/
theorem rationalOptimizerFamily_attained (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    ∃ p : Fin 7 → ℝ × ℝ,
      volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v7 := by
  refine ⟨rationalOptimizerUnit t, rationalOptimizerUnit_volume t ht, ?_⟩
  rw [rationalOptimizerUnit_minTri t ht, v7]
  norm_num

/-! ## A symmetric affine-gauge invariant -/

/-- Sum of squared signed determinants over all ordered triples.  Repeated
indices contribute zero and each unordered triangle contributes six times. -/
def orderedTriangleSquareSum (v : Configuration7) : ℝ :=
  ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
    (sig (v i) (v j) (v k)) ^ 2

/-- The normalized second moment of the 35 doubled triangle areas. -/
noncomputable def triangleSecondMoment (v : Configuration7) : ℝ :=
  orderedTriangleSquareSum v /
    (6 * HullBridge.doubledHullArea v ^ 2)

lemma sig_posAffine (T : PosAffine) (p q r : ℝ × ℝ) :
    sig (T.map p) (T.map q) (T.map r) =
      (T.a * T.d - T.b * T.c) * sig p q r := by
  simp only [sig, PosAffine.map]
  ring

private lemma sum3_comp_perm_fin7
    (sigma : Equiv.Perm (Fin 7))
    (f : Fin 7 → Fin 7 → Fin 7 → ℝ) :
    (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
        f (sigma i) (sigma j) (sigma k)) =
      ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, f i j k := by
  calc
    (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
        f (sigma i) (sigma j) (sigma k)) =
        ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
          f (sigma i) (sigma j) k := by
      apply Fintype.sum_congr
      intro i
      apply Fintype.sum_congr
      intro j
      exact Equiv.sum_comp sigma
        (fun k : Fin 7 => f (sigma i) (sigma j) k)
    _ = ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
          f (sigma i) j k := by
      apply Fintype.sum_congr
      intro i
      exact Equiv.sum_comp sigma
        (fun j : Fin 7 => ∑ k : Fin 7, f (sigma i) j k)
    _ = ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, f i j k :=
      Equiv.sum_comp sigma
        (fun i : Fin 7 => ∑ j : Fin 7, ∑ k : Fin 7, f i j k)

private lemma sum3_const_mul_fin7 (c : ℝ)
    (f : Fin 7 → Fin 7 → Fin 7 → ℝ) :
    (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
        c * f i j k) =
      c * (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, f i j k) := by
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]

lemma orderedTriangleSquareSum_relabel (v : Configuration7)
    (sigma : Equiv.Perm (Fin 7)) :
    orderedTriangleSquareSum (v ∘ sigma) = orderedTriangleSquareSum v := by
  simpa only [orderedTriangleSquareSum, Function.comp_apply] using
    (sum3_comp_perm_fin7 sigma
      (fun i j k : Fin 7 => (sig (v i) (v j) (v k)) ^ 2))

lemma orderedTriangleSquareSum_posAffine (T : PosAffine)
    (v : Configuration7) :
    orderedTriangleSquareSum (fun i => T.map (v i)) =
      (T.a * T.d - T.b * T.c) ^ 2 * orderedTriangleSquareSum v := by
  unfold orderedTriangleSquareSum
  calc
    (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
        (sig (T.map (v i)) (T.map (v j)) (T.map (v k))) ^ 2) =
        ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
          (T.a * T.d - T.b * T.c) ^ 2 *
            (sig (v i) (v j) (v k)) ^ 2 := by
      apply Fintype.sum_congr
      intro i
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_congr
      intro k
      rw [sig_posAffine T (v i) (v j) (v k), mul_pow]
    _ = (T.a * T.d - T.b * T.c) ^ 2 *
        (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
          (sig (v i) (v j) (v k)) ^ 2) :=
      sum3_const_mul_fin7
        ((T.a * T.d - T.b * T.c) ^ 2)
        (fun i j k : Fin 7 => (sig (v i) (v j) (v k)) ^ 2)

lemma doubledHullArea_posAffine (T : PosAffine) (v : Configuration7) :
    HullBridge.doubledHullArea (fun i => T.map (v i)) =
      (T.a * T.d - T.b * T.c) * HullBridge.doubledHullArea v := by
  have hrange : Set.range (fun i : Fin 7 => T.map (v i)) =
      HullBridge.affMap T.a T.b T.c T.d T.tx T.ty '' Set.range v := by
    simpa only [PosAffine.map, HullBridge.affMap] using
      (HullBridge.range_affMap (n := 7)
        T.a T.b T.c T.d T.tx T.ty v)
  have hvolume :
      MeasureTheory.volume (convexHull ℝ
          (HullBridge.affMap T.a T.b T.c T.d T.tx T.ty '' Set.range v)) =
        ENNReal.ofReal (T.a * T.d - T.b * T.c) *
          MeasureTheory.volume (convexHull ℝ (Set.range v)) :=
    HullBridge.volume_convexHull_image_affMap
      T.a T.b T.c T.d T.tx T.ty T.det_pos (Set.range v)
  change
    2 * (MeasureTheory.volume (convexHull ℝ
      (Set.range (fun i : Fin 7 => T.map (v i))))).toReal =
      (T.a * T.d - T.b * T.c) *
        (2 * (MeasureTheory.volume
          (convexHull ℝ (Set.range v))).toReal)
  rw [hrange, hvolume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal T.det_pos.le]
  ring

lemma triangleSecondMoment_relabel (v : Configuration7)
    (sigma : Equiv.Perm (Fin 7)) :
    triangleSecondMoment (v ∘ sigma) = triangleSecondMoment v := by
  unfold triangleSecondMoment
  rw [orderedTriangleSquareSum_relabel v sigma,
    doubledHullArea_relabel v sigma]

lemma triangleSecondMoment_posAffine (T : PosAffine) (v : Configuration7) :
    triangleSecondMoment (fun i => T.map (v i)) = triangleSecondMoment v := by
  unfold triangleSecondMoment
  rw [orderedTriangleSquareSum_posAffine T v,
    doubledHullArea_posAffine T v]
  have hdet2 : (T.a * T.d - T.b * T.c) ^ 2 ≠ 0 :=
    pow_ne_zero 2 T.det_pos.ne'
  rw [show
    6 * ((T.a * T.d - T.b * T.c) *
          HullBridge.doubledHullArea v) ^ 2 =
      (T.a * T.d - T.b * T.c) ^ 2 *
        (6 * HullBridge.doubledHullArea v ^ 2) by ring]
  exact mul_div_mul_left
    (orderedTriangleSquareSum v)
    (6 * HullBridge.doubledHullArea v ^ 2) hdet2

/-- `triangleSecondMoment` is invariant under the challenge's gauge relation:
an arbitrary relabeling followed by a positive-determinant affine map. -/
theorem triangleSecondMoment_eq_of_gaugeEquivalent
    {v u : Configuration7} (h : GaugeEquivalent v u) :
    triangleSecondMoment u = triangleSecondMoment v := by
  rcases h with ⟨sigma, T, rfl⟩
  simpa only [Function.comp_apply] using
    (triangleSecondMoment_posAffine T (v ∘ sigma)).trans
      (triangleSecondMoment_relabel v sigma)

private lemma sum3_separable {ι : Type*} [Fintype ι]
    (r : ℝ) (a b c : ι → ℝ) :
    (∑ i : ι, ∑ j : ι, ∑ k : ι,
      r * (a i * b j * c k)) =
      r * ((∑ i, a i) * (∑ j, b j) * (∑ k, c k)) := by
  calc
    (∑ i : ι, ∑ j : ι, ∑ k : ι,
        r * (a i * b j * c k)) =
        ∑ i : ι, ∑ j : ι,
          (r * (a i * b j)) * (∑ k : ι, c k) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ i : ι,
          ((r * a i) * (∑ j : ι, b j)) *
            (∑ k : ι, c k) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j : ι, (r * (a i * b j)) * (∑ k : ι, c k)) =
            ∑ j : ι,
              (r * a i * (∑ k : ι, c k)) * b j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (r * a i * (∑ k : ι, c k)) *
              (∑ j : ι, b j) := by
          symm
          rw [Finset.mul_sum]
        _ = ((r * a i) * (∑ j : ι, b j)) *
              (∑ k : ι, c k) := by
          ring
    _ = ∑ i : ι,
          (r * (∑ j : ι, b j) * (∑ k : ι, c k)) * a i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (r * (∑ j : ι, b j) * (∑ k : ι, c k)) *
          (∑ i : ι, a i) := by
      symm
      rw [Finset.mul_sum]
    _ = r * ((∑ i, a i) * (∑ j, b j) * (∑ k, c k)) := by
      ring

private lemma alternatingDetSquareSum {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    (∑ i : ι, ∑ j : ι, ∑ k : ι,
      (x i * y j + x j * y k + x k * y i -
        (x i * y k + x j * y i + x k * y j)) ^ 2) =
      6 * (
        (∑ _ : ι, (1 : ℝ)) *
          (∑ i, x i ^ 2) * (∑ i, y i ^ 2) +
        2 * (∑ i, x i) * (∑ i, y i) *
          (∑ i, x i * y i) -
        (∑ _ : ι, (1 : ℝ)) * (∑ i, x i * y i) ^ 2 -
        (∑ i, x i) ^ 2 * (∑ i, y i ^ 2) -
        (∑ i, y i) ^ 2 * (∑ i, x i ^ 2)) := by
  have hexpand (i j k : ι) :
      (x i * y j + x j * y k + x k * y i -
        (x i * y k + x j * y i + x k * y j)) ^ 2 =
        1 * (x i ^ 2 * y j ^ 2 * 1) +
        1 * (1 * x j ^ 2 * y k ^ 2) +
        1 * (y i ^ 2 * 1 * x k ^ 2) +
        1 * (x i ^ 2 * 1 * y k ^ 2) +
        1 * (y i ^ 2 * x j ^ 2 * 1) +
        1 * (1 * y j ^ 2 * x k ^ 2) +
        2 * (x i * (x j * y j) * y k) +
        2 * ((x i * y i) * y j * x k) +
        2 * (y i * x j * (x k * y k)) +
        2 * ((x i * y i) * x j * y k) +
        2 * (x i * y j * (x k * y k)) +
        2 * (y i * (x j * y j) * x k) +
        (-2) * (x i ^ 2 * y j * y k) +
        (-2) * ((x i * y i) * (x j * y j) * 1) +
        (-2) * (x i * y j ^ 2 * x k) +
        (-2) * (x i * x j * y k ^ 2) +
        (-2) * (y i * x j ^ 2 * y k) +
        (-2) * (1 * (x j * y j) * (x k * y k)) +
        (-2) * ((x i * y i) * 1 * (x k * y k)) +
        (-2) * (y i ^ 2 * x j * x k) +
        (-2) * (y i * y j * x k ^ 2) := by
    ring
  simp_rw [hexpand]
  simp only [Finset.sum_add_distrib, sum3_separable]
  ring

lemma orderedTriangleSquareSum_eq_moments (v : Configuration7) :
    orderedTriangleSquareSum v =
      6 * (
        7 * (∑ i : Fin 7, (v i).1 ^ 2) *
          (∑ i : Fin 7, (v i).2 ^ 2) +
        2 * (∑ i : Fin 7, (v i).1) *
          (∑ i : Fin 7, (v i).2) *
          (∑ i : Fin 7, (v i).1 * (v i).2) -
        7 * (∑ i : Fin 7, (v i).1 * (v i).2) ^ 2 -
        (∑ i : Fin 7, (v i).1) ^ 2 *
          (∑ i : Fin 7, (v i).2 ^ 2) -
        (∑ i : Fin 7, (v i).2) ^ 2 *
          (∑ i : Fin 7, (v i).1 ^ 2)) := by
  unfold orderedTriangleSquareSum
  calc
    (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
        (sig (v i) (v j) (v k)) ^ 2) =
        ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
          ((v i).1 * (v j).2 +
              (v j).1 * (v k).2 +
              (v k).1 * (v i).2 -
            ((v i).1 * (v k).2 +
              (v j).1 * (v i).2 +
              (v k).1 * (v j).2)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      simp only [sig]
      ring
    _ = _ := by
      simpa using
        (alternatingDetSquareSum
          (fun i : Fin 7 => (v i).1)
          (fun i : Fin 7 => (v i).2))

/-- The ordered numerator is six times
`336 + 504 t² + 189 t⁴`, the sum over the 35 unordered triangles. -/
theorem orderedTriangleSquareSum_rationalOptimizerFamily (t : ℝ) :
    orderedTriangleSquareSum (rationalOptimizerFamily t) =
      2016 + 3024 * t ^ 2 + 1134 * t ^ 4 := by
  rw [orderedTriangleSquareSum_eq_moments]
  have hx :
      (∑ i : Fin 7, (rationalOptimizerFamily t i).1) = 0 := by
    simp [Fin.sum_univ_succ, rationalOptimizerFamily]
    ring
  have hy :
      (∑ i : Fin 7, (rationalOptimizerFamily t i).2) = 0 := by
    simp [Fin.sum_univ_succ, rationalOptimizerFamily]
    ring
  have hxx :
      (∑ i : Fin 7, (rationalOptimizerFamily t i).1 ^ 2) =
        8 + 6 * t ^ 2 := by
    simp [Fin.sum_univ_succ, rationalOptimizerFamily]
    ring
  have hyy :
      (∑ i : Fin 7, (rationalOptimizerFamily t i).2 ^ 2) =
        8 + 6 * t ^ 2 := by
    simp [Fin.sum_univ_succ, rationalOptimizerFamily]
    ring
  have hxy :
      (∑ i : Fin 7,
        (rationalOptimizerFamily t i).1 *
          (rationalOptimizerFamily t i).2) = 4 + 3 * t ^ 2 := by
    simp [Fin.sum_univ_succ, rationalOptimizerFamily]
    ring
  rw [hx, hy, hxx, hyy, hxy]
  ring

/-- Closed form of the normalized second moment on the family. -/
noncomputable def rationalOptimizerInvariant (t : ℝ) : ℝ :=
  28 / (27 * t ^ 2) + 14 / 9 + 7 * t ^ 2 / 12

theorem triangleSecondMoment_rationalOptimizerFamily (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) :
    triangleSecondMoment (rationalOptimizerFamily t) =
      rationalOptimizerInvariant t := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  rw [triangleSecondMoment,
    orderedTriangleSquareSum_rationalOptimizerFamily,
    rationalOptimizerFamily_doubledHullArea t ht]
  dsimp [rationalOptimizerInvariant]
  field_simp [htpos.ne'] <;> ring

/-- Exact factor controlling injectivity of the invariant. -/
theorem rationalOptimizerInvariant_sub_factor (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) :
    rationalOptimizerInvariant s - rationalOptimizerInvariant t =
      7 * (s - t) * (s + t) * (3 * s * t - 4) * (3 * s * t + 4) /
        (108 * s ^ 2 * t ^ 2) := by
  dsimp [rationalOptimizerInvariant]
  field_simp [hs.ne', ht.ne'] <;> ring

/-- On `[1,8/7]`, `3st < 4`; the exact factor therefore makes the invariant
strictly decreasing. -/
lemma rationalOptimizerInvariant_strictAntiOn
    {s t : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (8 / 7))
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) (hst : s < t) :
    rationalOptimizerInvariant t < rationalOptimizerInvariant s := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hprod : s * t ≤ ((8 : ℝ) / 7) * (8 / 7) :=
    mul_le_mul hs.2 ht.2 (by linarith [ht.1]) (by norm_num)
  have hneg : 3 * s * t - 4 < 0 := by nlinarith [hprod]
  have hsum : 0 < s + t := add_pos hspos htpos
  have hlast : 0 < 3 * s * t + 4 := by positivity
  have h1 : 7 * (s - t) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hst)
  have h2 : 7 * (s - t) * (s + t) < 0 :=
    mul_neg_of_neg_of_pos h1 hsum
  have h3 : 0 < 7 * (s - t) * (s + t) * (3 * s * t - 4) :=
    mul_pos_of_neg_of_neg h2 hneg
  have hnum :
      0 < 7 * (s - t) * (s + t) * (3 * s * t - 4) *
        (3 * s * t + 4) := mul_pos h3 hlast
  have hden : 0 < 108 * s ^ 2 * t ^ 2 := by positivity
  apply sub_pos.mp
  rw [rationalOptimizerInvariant_sub_factor s t hspos htpos]
  exact div_pos hnum hden

theorem rationalOptimizerInvariant_injectiveOn
    {s t : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (8 / 7))
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7))
    (hI : rationalOptimizerInvariant s = rationalOptimizerInvariant t) :
    s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have h := rationalOptimizerInvariant_strictAntiOn hs ht hst
    linarith
  · have h := rationalOptimizerInvariant_strictAntiOn ht hs hts
    linarith

/-- Distinct parameters in the stated rational interval determine distinct
gauge classes, even though every member attains the same ratio `1/9`. -/
theorem rationalOptimizerFamily_pairwise_gaugeInequivalent
    {s t : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (8 / 7))
    (ht : t ∈ Set.Icc (1 : ℝ) (8 / 7)) (hst : s ≠ t) :
    ¬ GaugeEquivalent (rationalOptimizerFamily s)
      (rationalOptimizerFamily t) := by
  intro hgauge
  have hmoment := triangleSecondMoment_eq_of_gaugeEquivalent hgauge
  rw [triangleSecondMoment_rationalOptimizerFamily t ht,
    triangleSecondMoment_rationalOptimizerFamily s hs] at hmoment
  exact hst (rationalOptimizerInvariant_injectiveOn hs ht hmoment.symm)

end HeilbronnChallenge.N7Upper
