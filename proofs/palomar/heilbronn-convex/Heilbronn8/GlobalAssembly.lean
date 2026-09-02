import Heilbronn8.ClaimsAttain

/-!
# Final constant and theorem assembly

This module isolates the analytic supremum argument from the finite corpus.
The production tree ultimately supplies `UpperBoundStatement`; the explicit
witness already supplies the opposite inequality.

The interval `0 <= r <= 1` in `AdmissibleScore` makes conditional
completeness explicit at the `sSup` boundary.  The theorems below prove that
it is redundant, identify `h_convex` with an independently stated
unrestricted Friedman supremum, and record why the final proof does not need
a separate compactness/attainment development: the explicit witness attains
the supremum as soon as the composed tree supplies the upper bound.
-/

namespace Heilbronn8

def AdmissibleScore (n : Nat) (r : ℝ) : Prop :=
  n = 8 ∧ 0 ≤ r ∧ r ≤ 1 ∧
    ∃ p : Fin 8 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * r

noncomputable def h_convex (n : Nat) : ℝ :=
  sSup {r : ℝ | AdmissibleScore n r}

/-- The intended Friedman score predicate, with no artificial bounds on the
score variable.  This development is fixed at eight points, hence the
explicit `n = 8` guard. -/
def FriedmanAdmissibleScore (n : Nat) (r : ℝ) : Prop :=
  n = 8 ∧
    ∃ p : Fin 8 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * r

/-- Friedman's unrestricted supremum for the eight-point formulation. -/
noncomputable def friedman_h_convex (n : Nat) : ℝ :=
  sSup {r : ℝ | FriedmanAdmissibleScore n r}

/-- The bounds in the local score predicate follow from geometry: minimum
triangle area is nonnegative, and every triangle is contained in the unit
area convex hull. -/
lemma unitHull_score_mem_Icc (p : Fin 8 → ℝ × ℝ) (r : ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hscore : minTri p = 2 * r) :
    0 ≤ r ∧ r ≤ 1 := by
  have hnonneg := minTri_nonneg p
  have hupper := minTri_le_doubledHullArea p
  rw [doubledHullArea_eq_two_of_volume_one hvolume] at hupper
  constructor <;> linarith

/-- The local interval restrictions do not remove any geometric score. -/
theorem admissibleScore_iff_friedmanAdmissibleScore (n : Nat) (r : ℝ) :
    AdmissibleScore n r ↔ FriedmanAdmissibleScore n r := by
  constructor
  · rintro ⟨hn, _hr0, _hr1, p, hvolume, hscore⟩
    exact ⟨hn, p, hvolume, hscore⟩
  · rintro ⟨hn, p, hvolume, hscore⟩
    obtain ⟨hr0, hr1⟩ := unitHull_score_mem_Icc p r hvolume hscore
    exact ⟨hn, hr0, hr1, p, hvolume, hscore⟩

theorem admissibleScore_set_eq_friedman (n : Nat) :
    {r : ℝ | AdmissibleScore n r} =
      {r : ℝ | FriedmanAdmissibleScore n r} := by
  ext r
  exact admissibleScore_iff_friedmanAdmissibleScore n r

/-- The tree-facing `h_convex` is exactly the unrestricted Friedman
supremum. -/
theorem h_convex_eq_friedman_h_convex (n : Nat) :
    h_convex n = friedman_h_convex n := by
  rw [h_convex, friedman_h_convex,
    admissibleScore_set_eq_friedman n]

def UpperBoundStatement : Prop :=
  ∀ p : Fin 8 → ℝ × ℝ,
    MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 →
    minTri p ≤ 2 * v8

lemma v8_admissible : AdmissibleScore 8 v8 := by
  refine ⟨rfl, v8_pos.le, ?_, wN, volume_convexHull_wN, minTri_wN⟩
  linarith [v8_ub]

lemma score_set_bddAbove (n : Nat) :
    BddAbove {r : ℝ | AdmissibleScore n r} := by
  refine ⟨1, ?_⟩
  intro r hr
  exact hr.2.2.1

lemma friedman_score_set_bddAbove (n : Nat) :
    BddAbove {r : ℝ | FriedmanAdmissibleScore n r} := by
  rw [← admissibleScore_set_eq_friedman n]
  exact score_set_bddAbove n

theorem attainment_lower_bound : v8 ≤ h_convex 8 := by
  exact le_csSup (score_set_bddAbove 8) v8_admissible

theorem upper_bound_of_composed_tree (upper : UpperBoundStatement) :
    h_convex 8 ≤ v8 := by
  apply csSup_le
  · exact ⟨v8, v8_admissible⟩
  · intro r hr
    rcases hr with ⟨_hn, _hr0, _hr1, p, hpvolume, hpscore⟩
    have hpupper := upper p hpvolume
    linarith

theorem h_convex_eight_eq_v8_of_upper_bound
    (upper : UpperBoundStatement) : h_convex 8 = v8 := by
  exact le_antisymm (upper_bound_of_composed_tree upper)
    attainment_lower_bound

/-- Unrestricted-supremum form of the Phase-3 assembly theorem. -/
theorem friedman_h_convex_eight_eq_v8_of_upper_bound
    (upper : UpperBoundStatement) : friedman_h_convex 8 = v8 := by
  rw [← h_convex_eq_friedman_h_convex]
  exact h_convex_eight_eq_v8_of_upper_bound upper

/-- No general compactness theorem is needed by the final statement.  Once
the tree supplies the global upper bound, the already checked configuration
`wN` is an actual maximizer of the unrestricted supremum. -/
theorem friedman_supremum_attained_of_upper_bound
    (upper : UpperBoundStatement) :
    ∃ p : Fin 8 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p / 2 = friedman_h_convex 8 := by
  refine ⟨wN, volume_convexHull_wN, ?_⟩
  rw [friedman_h_convex_eight_eq_v8_of_upper_bound upper, minTri_wN]
  ring

#print axioms attainment_lower_bound
#print axioms upper_bound_of_composed_tree
#print axioms h_convex_eight_eq_v8_of_upper_bound
#print axioms h_convex_eq_friedman_h_convex
#print axioms friedman_h_convex_eight_eq_v8_of_upper_bound
#print axioms friedman_supremum_attained_of_upper_bound

end Heilbronn8
