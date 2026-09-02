/-
n = 5: h_convex 5 = v5 = (5 - sqrt 5) / 10.

The mathematics is in `Heil5` (upper bound over the three hull topologies,
attainment by the affinely regular pentagon) and its measure bridge
`Heil5.Bridge`. This file is bookkeeping: `Heilbronn5.minTri` is an explicit
min-chain over the ten triples and `HeilbronnChallenge.minTri` is a
`Finset.inf'` over the same ten triples, so they agree; and `Heilbronn5.tau`
is the same real number as the challenge's `v5`.
-/
import Solution.Common
import Heil5.Bridge

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- `Heilbronn5.sig` and the challenge `sig` have the same body. -/
lemma sig_eq_five (p q r : ℝ × ℝ) : Heilbronn5.sig p q r = sig p q r := rfl

/-- The min-chain and the `Finset.inf'` compute the same minimum. -/
theorem minTri_eq_five (v : Fin 5 → ℝ × ℝ) :
    Heilbronn5.minTri v = minTri v := by
  apply le_antisymm
  · apply le_minTri
    intro t ht
    have hmem : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    rcases triple_cases5 t.1 t.2.1 t.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_012 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_013 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_014 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_023 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_024 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_034 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_123 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_124 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_134 v
    · rw [q0, q1, q2]; exact Heilbronn5.minTri_le_234 v
  · simp only [Heilbronn5.minTri]
    refine le_min (le_min (le_min ?_ ?_) (le_min ?_ ?_))
      (le_min (le_min (le_min ?_ ?_) (le_min ?_ ?_)) (le_min ?_ ?_))
    · exact minTri_le v 0 1 2 (by decide) (by decide)
    · exact minTri_le v 0 1 3 (by decide) (by decide)
    · exact minTri_le v 0 1 4 (by decide) (by decide)
    · exact minTri_le v 0 2 3 (by decide) (by decide)
    · exact minTri_le v 0 2 4 (by decide) (by decide)
    · exact minTri_le v 0 3 4 (by decide) (by decide)
    · exact minTri_le v 1 2 3 (by decide) (by decide)
    · exact minTri_le v 1 2 4 (by decide) (by decide)
    · exact minTri_le v 1 3 4 (by decide) (by decide)
    · exact minTri_le v 2 3 4 (by decide) (by decide)

/-- `tau` and `v5` are the same real number. -/
theorem tau_eq_v5 : Heilbronn5.tau = v5 := by
  show (5 - Real.sqrt 5) / 10 = v5
  rw [v5_eq]

/-! ## Challenge theorems -/

theorem heilbronn_convex_five_attained :
    ∃ p : Fin 5 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v5 := by
  refine ⟨Heilbronn5.goldenNorm, Heilbronn5.volume_goldenNorm, ?_⟩
  rw [← minTri_eq_five, Heilbronn5.minTri_goldenNorm, tau_eq_v5]

theorem heilbronn_convex_five : h_convex 5 = v5 := by
  apply h_convex_eq
  · refine ⟨by linarith [v5_spec.1], by linarith [v5_spec.2.1],
      heilbronn_convex_five_attained⟩
  · rintro r ⟨_, _, p, hvol, hmin⟩
    have hb := Heilbronn5.upper_bound_volume p hvol
    rw [minTri_eq_five, hmin] at hb
    rw [← tau_eq_v5]
    linarith

noncomputable def witness5 : Fin 5 → ℝ × ℝ :=
  heilbronn_convex_five_attained.choose

theorem witness5_spec :
    MeasureTheory.volume (convexHull ℝ (Set.range witness5)) = 1 ∧
      minTri witness5 = 2 * v5 :=
  heilbronn_convex_five_attained.choose_spec

end HeilbronnChallenge
