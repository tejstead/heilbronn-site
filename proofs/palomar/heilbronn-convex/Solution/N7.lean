/-
n = 7, the attainment half: `h_convex 7 = 1/9` is attained, which gives the
unconditional bound `v7 ≤ h_convex 7`. The matching upper bound is not in this
file.

The optimum is not in strictly convex position: the best convex-position
configuration is the regular heptagon, whose ratio is below 1/9. Here six points
carry the hull and a seventh sits inside it.

The witness needs no algebraic numbers. The unimodular map `M (x, y) = (-y, x - y)`
has order three, so the origin together with the `M`-orbits of `(-2, -2)` and
`(-1, -2)` is a seven-point integer configuration; its doubled hull area is 18 and
its smallest doubled triangle is 2, ratio exactly 1/9. Scaling both coordinates by
1/3 divides every area by 9, so the hull area becomes 1 and the smallest doubled
triangle becomes 2/9, which is `2 * (1/9)`. Every coordinate stays rational.

Nine of the thirty-five triples attain the minimum; the others are 1/3, 4/9, 1,
10/9 and 4/3.
-/
import Solution.Common

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- The six hull vertices, counter-clockwise. -/
noncomputable def hex7 : Fin 6 → ℝ × ℝ :=
  ![(-2/3, -2/3), (-1/3, -2/3), (2/3, 0), (2/3, 1/3), (0, 2/3), (-1/3, 1/3)]

/-- All seven points: the six hull vertices, then the interior point. -/
noncomputable def cfg7 : Fin 7 → ℝ × ℝ :=
  ![(-2/3, -2/3), (-1/3, -2/3), (2/3, 0), (2/3, 1/3), (0, 2/3), (-1/3, 1/3), (0, 0)]

-- `Matrix.cons_val_*` stops at index 4, so the values are named here.
@[simp] lemma hex7_zero : hex7 0 = (-2/3, -2/3) := rfl
@[simp] lemma hex7_one : hex7 1 = (-1/3, -2/3) := rfl
@[simp] lemma hex7_two : hex7 2 = (2/3, 0) := rfl
@[simp] lemma hex7_three : hex7 3 = (2/3, 1/3) := rfl
@[simp] lemma hex7_four : hex7 4 = (0, 2/3) := rfl
@[simp] lemma hex7_five : hex7 5 = (-1/3, 1/3) := rfl

@[simp] lemma cfg7_zero : cfg7 0 = (-2/3, -2/3) := rfl
@[simp] lemma cfg7_one : cfg7 1 = (-1/3, -2/3) := rfl
@[simp] lemma cfg7_two : cfg7 2 = (2/3, 0) := rfl
@[simp] lemma cfg7_three : cfg7 3 = (2/3, 1/3) := rfl
@[simp] lemma cfg7_four : cfg7 4 = (0, 2/3) := rfl
@[simp] lemma cfg7_five : cfg7 5 = (-1/3, 1/3) := rfl
@[simp] lemma cfg7_six : cfg7 6 = (0, 0) := rfl

/-! ## The hull is the hexagon -/

/-- The six hull vertices are in strictly convex position, counter-clockwise. -/
theorem hex7_strict :
    ∀ i j k : Fin 6, i < j → j < k → 0 < sig (hex7 i) (hex7 j) (hex7 k) := by
  intro i j k hij hjk
  rcases triple_cases6 i j k hij hjk with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [sig, hex7_zero, hex7_one, hex7_two, hex7_three, hex7_four, hex7_five]
    norm_num

theorem volume_convexHull_hex7 :
    volume (convexHull ℝ (Set.range hex7)) = 1 := by
  rw [HullBridge.volume_convexHull_strictCCW6 hex7 hex7_strict]
  simp only [HullBridge.sig, hex7_zero, hex7_one, hex7_two, hex7_three, hex7_four, hex7_five]
  norm_num

/-- The seventh point is the average of hull vertices 0, 2 and 4, so it lies in
the hexagon. -/
theorem interior_mem7 :
    ((0 : ℝ), (0 : ℝ)) ∈ convexHull ℝ (Set.range hex7) := by
  have hconv := convex_convexHull ℝ (Set.range hex7)
  have h0 : hex7 0 ∈ convexHull ℝ (Set.range hex7) :=
    subset_convexHull ℝ _ ⟨0, rfl⟩
  have h2 : hex7 2 ∈ convexHull ℝ (Set.range hex7) :=
    subset_convexHull ℝ _ ⟨2, rfl⟩
  have h4 : hex7 4 ∈ convexHull ℝ (Set.range hex7) :=
    subset_convexHull ℝ _ ⟨4, rfl⟩
  have hm := hconv h0 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  have hf := hconv hm h4 (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (2:ℝ)/3 + 1/3 = 1)
  have hval : ((2:ℝ)/3) • (((1:ℝ)/2) • hex7 0 + ((1:ℝ)/2) • hex7 2)
      + ((1:ℝ)/3) • hex7 4 = ((0 : ℝ), (0 : ℝ)) := by
    rw [Prod.ext_iff]
    simp only [hex7_zero, hex7_two, hex7_four, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul]
    norm_num
  rwa [hval] at hf

theorem range_cfg7 :
    Set.range cfg7 = insert ((0 : ℝ), (0 : ℝ)) (Set.range hex7) := by
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

/-- Adding a point already inside the hexagon does not change the hull. -/
theorem hull_eq7 :
    convexHull ℝ (Set.range cfg7) = convexHull ℝ (Set.range hex7) := by
  rw [range_cfg7]
  apply Set.Subset.antisymm
  · exact convexHull_min
      (Set.insert_subset_iff.mpr ⟨interior_mem7, subset_convexHull ℝ _⟩)
      (convex_convexHull ℝ _)
  · exact convexHull_mono (Set.subset_insert _ _)

theorem volume_convexHull_cfg7 :
    volume (convexHull ℝ (Set.range cfg7)) = 1 := by
  rw [hull_eq7, volume_convexHull_hex7]

/-! ## The smallest triangle -/

theorem minTri_cfg7 : minTri cfg7 = 2/9 := by
  apply le_antisymm
  · have h := minTri_le cfg7 0 1 2 (by decide) (by decide)
    refine h.trans (le_of_eq ?_)
    simp only [sig, cfg7_zero, cfg7_one, cfg7_two]
    norm_num [abs_of_nonneg]
  · apply le_minTri
    intro t ht
    have hmem : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    rcases triple_cases7 t.1 t.2.1 t.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ <;>
    · rw [q0, q1, q2]
      simp only [sig, cfg7_zero, cfg7_one, cfg7_two, cfg7_three, cfg7_four, cfg7_five, cfg7_six]
      rw [le_abs]
      norm_num

/-! ## Challenge theorems -/

theorem heilbronn_convex_seven_attained :
    ∃ p : Fin 7 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v7 := by
  refine ⟨cfg7, volume_convexHull_cfg7, ?_⟩
  rw [minTri_cfg7, v7]
  norm_num

theorem v7_admissible : AdmissibleScore 7 v7 := by
  refine ⟨?_, ?_, heilbronn_convex_seven_attained⟩
  · rw [v7]; norm_num
  · rw [v7]; norm_num

/-- Unconditional lower bound. The upper bound is a separate development. -/
theorem heilbronn_convex_seven_lower_bound : v7 ≤ h_convex 7 :=
  le_csSup ⟨1, fun _ hr => hr.2.1⟩ v7_admissible

end HeilbronnChallenge
