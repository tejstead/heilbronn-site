/-
n = 8: exact value and attainment.

The `Heilbronn8` development supplies an exact algebraic witness and the
unconditional geometric upper bound. This module transports its minimum, score
predicate, supremum, and selected quintic root to the challenge namespace,
proving `heilbronn_convex_eight`, `_attained`, and `_lower_bound`.
-/
import Solution.Common
import Heilbronn8.UniversalHullGeometryFinalComplete

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- `Heilbronn8.sig` and the challenge `sig` have the same body. -/
lemma sig_eq_eight (p q r : ℝ × ℝ) : Heilbronn8.sig p q r = sig p q r := rfl

/-- The two minima agree. Neither side is unfolded: each is bounded by the
other through its own `Finset.inf'` universal property, so the 56 triples never
have to be enumerated. -/
theorem minTri_eq_eight (v : Fin 8 → ℝ × ℝ) :
    Heilbronn8.minTri v = minTri v := by
  apply le_antisymm
  · apply le_minTri
    intro t ht
    have hmem : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    exact Heilbronn8.minTri_le v hmem.1 hmem.2
  · exact Heilbronn8.le_minTri v fun i j k hij hjk => minTri_le v i j k hij hjk

/-- At eight points, the challenge score predicate and the internal score
predicate describe exactly the same normalized configurations.  The internal
predicate carries an explicit `8 = 8` guard because that development is fixed
at eight points. -/
theorem admissibleScore_eight_iff (r : ℝ) :
    AdmissibleScore 8 r ↔ Heilbronn8.AdmissibleScore 8 r := by
  constructor
  · rintro ⟨hr0, hr1, p, hvol, hmin⟩
    refine ⟨rfl, hr0, hr1, p, hvol, ?_⟩
    rw [minTri_eq_eight]
    exact hmin
  · rintro ⟨_h8, hr0, hr1, p, hvol, hmin⟩
    refine ⟨hr0, hr1, p, hvol, ?_⟩
    rw [← minTri_eq_eight]
    exact hmin

/-- The general challenge supremum specialized to eight points agrees with
the fixed-arity supremum used by the n=8 development. -/
theorem h_convex_eight_eq_internal :
    h_convex 8 = Heilbronn8.h_convex 8 := by
  unfold h_convex Heilbronn8.h_convex
  apply congrArg sSup
  ext r
  exact admissibleScore_eight_iff r

/-! ## The three spellings of `v8` -/

theorem v8_spec : 79 / 1000 < v8 ∧ v8 < 81 / 1000 ∧ P8 v8 = 0 :=
  Classical.choose_spec P8_root_existsUnique.exists

/-- The challenge's `v8` is the value layer's root. -/
theorem v8_eq_values : v8 = HeilbronnValues.v8 :=
  P8_root_existsUnique.unique v8_spec
    ⟨HeilbronnValues.v8_gt, HeilbronnValues.v8_lt, HeilbronnValues.v8_root⟩

/-- The attainment layer's root is that same real number. Its bracket is the
closed interval, the challenge's is the open one, so the two statements are
matched by widening. -/
theorem v8_eq_eight : Heilbronn8.v8 = v8 := by
  refine (Heilbronn8.v8_unique (x := v8) ⟨?_, ?_⟩ ?_).symm
  · exact v8_spec.1.le
  · exact v8_spec.2.1.le
  · exact v8_spec.2.2

theorem v8_pos : 0 < v8 := lt_trans (by norm_num) v8_spec.1

theorem v8_le_one : v8 ≤ 1 := le_of_lt (lt_trans v8_spec.2.1 (by norm_num))

/-! ## Challenge theorems -/

/-- The exact eight-point value, transported from the unconditional geometric
hull-size proof to the challenge's general-arity definitions. -/
theorem heilbronn_convex_eight : h_convex 8 = v8 := by
  calc
    h_convex 8 = Heilbronn8.h_convex 8 := h_convex_eight_eq_internal
    _ = Heilbronn8.v8 := Heilbronn8.heilbronn_eight_final_unconditional
    _ = v8 := v8_eq_eight

theorem heilbronn_convex_eight_attained :
    ∃ p : Fin 8 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v8 := by
  refine ⟨Heilbronn8.wN, Heilbronn8.volume_convexHull_wN, ?_⟩
  rw [← minTri_eq_eight, Heilbronn8.minTri_wN, v8_eq_eight]

/-- The score `v8` is admissible, so it is a member of the set `h_convex 8`
takes the supremum of. -/
theorem v8_admissible : AdmissibleScore 8 v8 :=
  ⟨v8_pos.le, v8_le_one, heilbronn_convex_eight_attained⟩

/-- The witness gives this lower bound independently of the matching
upper-bound proof. -/
theorem heilbronn_convex_eight_lower_bound : v8 ≤ h_convex 8 :=
  le_csSup ⟨1, fun _ hr => hr.2.1⟩ v8_admissible

end HeilbronnChallenge
