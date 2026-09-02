import Heil7.CanonicalUpper

/-!
# The canonical hull-three counting route

If the convex hull of seven points is the positively oriented triangle
`v 0, v 1, v 2`, the four remaining points lie in that triangle.  The generic
interior-point counting theorem in `HullBridge` then partitions the hull into
`2 * 4 + 1 = 9` triangles.  Since every one of those triangles has doubled
area at least the canonical `minTri`, this is exactly the hull-three field of
`HullCaseBounds`.

This proof uses only the canonical Palomar definitions.  It introduces no
certificate or additional geometric hypothesis.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Four points inside the triangular hull give the sharp counting coefficient
`9`.  This has exactly the type required by `HullCaseBounds.h3`. -/
theorem hullThree_counting :
    ∀ (v : Configuration7), HullCCW v 3 →
      (∀ p : Fin 7, 3 ≤ (p : ℕ) → InHullN v 3 p) →
      9 * minTri v ≤ fanArea v 3 := by
  intro v hccw hinHull
  have h012 : 0 < sig (v 0) (v 1) (v 2) :=
    hccw 0 1 2 (by decide) (by decide) (by norm_num)
  by_cases hmzero : minTri v = 0
  · rw [hmzero]
    simp only [fanArea]
    linarith
  · have hmpos : 0 < minTri v :=
      lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hmzero)
    have hmin : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        minTri v ≤ |HullBridge.sig (v i) (v j) (v k)| := by
      intro i j k hij hik hjk
      exact minTri_le_of_distinct v i j k hij hik hjk
    have hrotate : ∀ a b c : ℝ × ℝ, sig a b c = sig b c a := by
      intro a b c
      simp only [sig]
      ring
    have hinside : ∀ p ∈ ({3, 4, 5, 6} : Finset (Fin 7)),
        HullBridge.InTri (v p) (v 0) (v 1) (v 2) := by
      intro p hp
      have hp_ge : 3 ≤ (p : ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      obtain ⟨hsides, hclose⟩ := hinHull p hp_ge
      have h01 : 0 < sig (v 0) (v 1) (v p) := by
        simpa using hsides 0 (by norm_num)
      have h12 : 0 < sig (v 1) (v 2) (v p) := by
        simpa using hsides 1 (by norm_num)
      have h20 : 0 < sig (v 2) (v 0) (v p) := by
        simpa using hclose 2 (by norm_num)
      apply HullBridge.inTri_of_sig (v p) (v 0) (v 1) (v 2) h012
      · rw [← HeilbronnChallenge.sig_eq, hrotate]
        exact h12.le
      · rw [← HeilbronnChallenge.sig_eq, hrotate, hrotate]
        exact h20.le
      · exact h01.le
    have hcount := HullBridge.interior_count_bound v (minTri v) hmpos hmin
      ({3, 4, 5, 6} : Finset (Fin 7)) 0 1 2
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h012 hinside
    have hcard : ({3, 4, 5, 6} : Finset (Fin 7)).card = 4 := by decide
    rw [hcard] at hcount
    norm_num at hcount
    simpa only [fanArea, ← HeilbronnChallenge.sig_eq] using hcount

end HeilbronnChallenge.N7Upper
