/-
The two n = 6 hull cases that need no argument beyond counting interior points.
-/
import HullBridge

set_option linter.style.header false

/-!
# n = 6 hull cases that close by counting alone

`h_convex 6 = 1/6` unfolds to `6 * m ≤ D`, where `m` bounds every doubled
triangle area from below and `D` is the doubled hull area. A triangulation of six
points with `h` of them on the hull has `2 * 6 - h - 2 = 10 - h` triangles, each
of doubled area at least `m`, so counting alone delivers `(10 - h) * m` and the
deficit against the required `6` is `h - 4`.

The two cases with no deficit are settled here, both from
`HullBridge.interior_count_bound`:

* `h = 3` has surplus one. The hull triangle holds the other three points, so a
  single application gives `7 * m`.
* `h = 4` is exactly tight at `6 * m`. Note where the zero margin bites: the two
  interior points are split by a diagonal of the hull quadrilateral, and that
  split is only well defined because `0 < m` forbids a point from lying *on* the
  diagonal. With `m = 0` allowed, a point on the diagonal would belong to both
  closed triangles and the count could be inflated.
-/

namespace Heil6

open HullBridge

/-- `h = 3`: the hull triangle contains the remaining three points, so counting
gives `7 * m`, one unit more than the target needs. -/
theorem hull3_bound (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |sig (v i) (v j) (v k)|)
    (hpos : 0 < sig (v 0) (v 1) (v 2))
    (h3 : InTri (v 3) (v 0) (v 1) (v 2))
    (h4 : InTri (v 4) (v 0) (v 1) (v 2))
    (h5 : InTri (v 5) (v 0) (v 1) (v 2)) :
    7 * m ≤ sig (v 0) (v 1) (v 2) := by
  have hin : ∀ p ∈ ({3, 4, 5} : Finset (Fin 6)),
      InTri (v p) (v 0) (v 1) (v 2) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact h3
    · exact h4
    · exact h5
  have h := interior_count_bound v m hm hmin {3, 4, 5} 0 1 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hpos hin
  have hcard : ({3, 4, 5} : Finset (Fin 6)).card = 3 := by decide
  rw [hcard] at h
  norm_num at h
  linarith

/-- `h = 4`: the hull quadrilateral splits on the diagonal `v 0 v 2`, the two
interior points distribute between the halves, and every distribution gives
exactly `6 * m`. -/
theorem hull4_bound (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |sig (v i) (v j) (v k)|)
    (h012 : 0 < sig (v 0) (v 1) (v 2))
    (h023 : 0 < sig (v 0) (v 2) (v 3))
    (hp4 : InTri (v 4) (v 0) (v 1) (v 2) ∨ InTri (v 4) (v 0) (v 2) (v 3))
    (hp5 : InTri (v 5) (v 0) (v 1) (v 2) ∨ InTri (v 5) (v 0) (v 2) (v 3)) :
    6 * m ≤ sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) := by
  have empty012 : ∀ p ∈ (∅ : Finset (Fin 6)),
      InTri (v p) (v 0) (v 1) (v 2) := by
    intro p hp
    exact absurd hp (Finset.notMem_empty p)
  have empty023 : ∀ p ∈ (∅ : Finset (Fin 6)),
      InTri (v p) (v 0) (v 2) (v 3) := by
    intro p hp
    exact absurd hp (Finset.notMem_empty p)
  have single : ∀ (q : Fin 6) (a b c : Fin 6),
      InTri (v q) (v a) (v b) (v c) →
      ∀ p ∈ ({q} : Finset (Fin 6)), InTri (v p) (v a) (v b) (v c) := by
    intro q a b c hq p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact hq
  have pair : ∀ (a b c : Fin 6),
      InTri (v 4) (v a) (v b) (v c) → InTri (v 5) (v a) (v b) (v c) →
      ∀ p ∈ ({4, 5} : Finset (Fin 6)), InTri (v p) (v a) (v b) (v c) := by
    intro a b c q4 q5 p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact q4
    · exact q5
  rcases hp4 with a4 | a4 <;> rcases hp5 with a5 | a5
  · -- both interior points on the `v 0 v 1 v 2` side: 5m + 1m
    have b1 := interior_count_bound v m hm hmin {4, 5} 0 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h012 (pair 0 1 2 a4 a5)
    have b2 := interior_count_bound v m hm hmin ∅ 0 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h023 empty023
    have c1 : ({4, 5} : Finset (Fin 6)).card = 2 := by decide
    rw [c1] at b1
    simp only [Finset.card_empty] at b2
    norm_num at b1 b2
    linarith
  · -- split one each: 3m + 3m
    have b1 := interior_count_bound v m hm hmin {4} 0 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h012 (single 4 0 1 2 a4)
    have b2 := interior_count_bound v m hm hmin {5} 0 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h023 (single 5 0 2 3 a5)
    simp only [Finset.card_singleton] at b1 b2
    norm_num at b1 b2
    linarith
  · -- the other one-each split: 3m + 3m
    have b1 := interior_count_bound v m hm hmin {5} 0 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h012 (single 5 0 1 2 a5)
    have b2 := interior_count_bound v m hm hmin {4} 0 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h023 (single 4 0 2 3 a4)
    simp only [Finset.card_singleton] at b1 b2
    norm_num at b1 b2
    linarith
  · -- both on the `v 0 v 2 v 3` side: 1m + 5m
    have b1 := interior_count_bound v m hm hmin ∅ 0 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h012 empty012
    have b2 := interior_count_bound v m hm hmin {4, 5} 0 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h023 (pair 0 2 3 a4 a5)
    have c2 : ({4, 5} : Finset (Fin 6)).card = 2 := by decide
    rw [c2] at b2
    simp only [Finset.card_empty] at b1
    norm_num at b1 b2
    linarith

end Heil6
