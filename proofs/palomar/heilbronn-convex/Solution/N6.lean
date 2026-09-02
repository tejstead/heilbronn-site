/-
n = 6, the attainment half: `h_convex 6 = 1/6` is attained by the affinely
regular hexagon, and that gives the unconditional bound `v6 ≤ h_convex 6`.
The matching upper bound is not in this file.

The witness needs no algebraic numbers. The regular hexagon has an affine copy
with vertices at the six lattice points `(±1, 0)`, `(0, ±1)`, `(1, -1)`,
`(-1, 1)`, whose doubled hull area is 6 and whose smallest doubled triangle is
1, ratio exactly 1/6. Dividing the first coordinate by 3 rescales both by 1/3,
so the hull area becomes 1 and the smallest doubled triangle becomes 1/3, which
is `2 * (1/6)`. Every coordinate stays rational, so every area below is an exact
rational and `norm_num` closes it.

Six of the twenty triples attain the minimum, namely the six triples of
consecutive vertices; the other fourteen are 2/3 or 1.
-/
import Solution.Common

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- The affinely regular hexagon with its first coordinate divided by 3, so
that the hull area is exactly 1. -/
noncomputable def hex6 : Fin 6 → ℝ × ℝ :=
  ![(1/3, 0), (0, 1), (-1/3, 1), (-1/3, 0), (0, -1), (1/3, -1)]

-- `Matrix.cons_val_*` stops at index 4, so the six values are named here and
-- used as the rewrite set below.
@[simp] lemma hex6_zero : hex6 0 = (1/3, 0) := rfl
@[simp] lemma hex6_one : hex6 1 = (0, 1) := rfl
@[simp] lemma hex6_two : hex6 2 = (-1/3, 1) := rfl
@[simp] lemma hex6_three : hex6 3 = (-1/3, 0) := rfl
@[simp] lemma hex6_four : hex6 4 = (0, -1) := rfl
@[simp] lemma hex6_five : hex6 5 = (1/3, -1) := rfl

/-- Every increasing triple is positively oriented: the six vertices are in
strictly convex position, listed counter-clockwise. -/
theorem hex6_strict :
    ∀ i j k : Fin 6, i < j → j < k → 0 < sig (hex6 i) (hex6 j) (hex6 k) := by
  intro i j k hij hjk
  rcases triple_cases6 i j k hij hjk with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [sig, hex6_zero, hex6_one, hex6_two, hex6_three, hex6_four,
      hex6_five]
    norm_num

/-- The hull is the hexagon itself and has Lebesgue area exactly 1. -/
theorem volume_convexHull_hex6 :
    volume (convexHull ℝ (Set.range hex6)) = 1 := by
  rw [HullBridge.volume_convexHull_strictCCW6 hex6 hex6_strict]
  simp only [HullBridge.sig, hex6_zero, hex6_one, hex6_two, hex6_three,
    hex6_four, hex6_five]
  norm_num

/-- The smallest of the twenty doubled triangle areas is 1/3. -/
theorem minTri_hex6 : minTri hex6 = 1/3 := by
  apply le_antisymm
  · have h := minTri_le hex6 0 1 2 (by decide) (by decide)
    refine h.trans (le_of_eq ?_)
    simp only [sig, hex6_zero, hex6_one, hex6_two]
    norm_num [abs_of_nonneg]
  · apply le_minTri
    intro t ht
    have hmem : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    rcases triple_cases6 t.1 t.2.1 t.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ <;>
    · rw [q0, q1, q2]
      simp only [sig, hex6_zero, hex6_one, hex6_two, hex6_three, hex6_four,
        hex6_five]
      rw [abs_of_nonneg (by norm_num)]
      norm_num

/-! ## Challenge theorems -/

theorem heilbronn_convex_six_attained :
    ∃ p : Fin 6 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v6 := by
  refine ⟨hex6, volume_convexHull_hex6, ?_⟩
  rw [minTri_hex6, v6]
  norm_num

theorem v6_admissible : AdmissibleScore 6 v6 := by
  refine ⟨?_, ?_, heilbronn_convex_six_attained⟩
  · rw [v6]; norm_num
  · rw [v6]; norm_num

/-- Unconditional lower bound. The upper bound is a separate development. -/
theorem heilbronn_convex_six_lower_bound : v6 ≤ h_convex 6 :=
  le_csSup ⟨1, fun _ hr => hr.2.1⟩ v6_admissible

noncomputable def witness6 : Fin 6 → ℝ × ℝ :=
  heilbronn_convex_six_attained.choose

theorem witness6_spec :
    MeasureTheory.volume (convexHull ℝ (Set.range witness6)) = 1 ∧
      minTri witness6 = 2 * v6 :=
  heilbronn_convex_six_attained.choose_spec

end HeilbronnChallenge
