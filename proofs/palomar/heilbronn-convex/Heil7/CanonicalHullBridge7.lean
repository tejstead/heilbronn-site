import HullBridge

/-!
# Seven-point strict-cycle hull bridge

This source-only scratch extension continues `HullBridge`'s strict-CCW fan
formulas from `Fin 3`--`Fin 6` to `Fin 7`.  Its statement mentions only the
public doubled-area determinant and Lebesgue volume; the finite fan helpers are
kept private.
-/

set_option linter.style.header false

namespace HullBridge

open MeasureTheory

private def fanLeft7 (pts : Fin 7 → ℝ × ℝ) : Fin 5 → ℝ × ℝ :=
  ![pts 1, pts 2, pts 3, pts 4, pts 5]

private def fanRight7 (pts : Fin 7 → ℝ × ℝ) : Fin 5 → ℝ × ℝ :=
  ![pts 2, pts 3, pts 4, pts 5, pts 6]

private lemma strictCCW7_fan_decomposition (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 5, convexHull ℝ {pts 0, fanLeft7 pts i, fanRight7 pts i} := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 := strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 := strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 := strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 := strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h45 := strictCCW_consecutive_halfplane pts hpos 4 5 (by decide)
    have h56 := strictCCW_consecutive_halfplane pts hpos 5 6 (by decide)
    have h60 := strictCCW_closing_halfplane pts hpos 0 6 (by decide)
      (by decide) (by decide)
    have h01x := sig_nonneg_on_convexHull (pts 0) (pts 1) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := sig_nonneg_on_convexHull (pts 1) (pts 2) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := sig_nonneg_on_convexHull (pts 2) (pts 3) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h34x := sig_nonneg_on_convexHull (pts 3) (pts 4) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h34 k) x hx
    have h45x := sig_nonneg_on_convexHull (pts 4) (pts 5) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h45 k) x hx
    have h56x := sig_nonneg_on_convexHull (pts 5) (pts 6) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h56 k) x hx
    have h60x := sig_nonneg_on_convexHull (pts 6) (pts 0) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h60 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
    have hp045 := hpos 0 4 5 (by decide) (by decide)
    have hp056 := hpos 0 5 6 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    by_cases h03 : sig (pts 0) (pts 3) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      apply (mem_triangle_iff_orientations x _ _ _ hp023).2
      rw [sig_reverse (pts 0) (pts 3) x]
      exact ⟨le_of_not_ge h02, h23x, neg_nonneg.mpr h03⟩
    by_cases h04 : sig (pts 0) (pts 4) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨2, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 3, pts 4}
      apply (mem_triangle_iff_orientations x _ _ _ hp034).2
      rw [sig_reverse (pts 0) (pts 4) x]
      exact ⟨le_of_not_ge h03, h34x, neg_nonneg.mpr h04⟩
    by_cases h05 : sig (pts 0) (pts 5) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨3, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 4, pts 5}
      apply (mem_triangle_iff_orientations x _ _ _ hp045).2
      rw [sig_reverse (pts 0) (pts 5) x]
      exact ⟨le_of_not_ge h04, h45x, neg_nonneg.mpr h05⟩
    · refine Set.mem_iUnion.2 ⟨4, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 5, pts 6}
      exact (mem_triangle_iff_orientations x _ _ _ hp056).2
        ⟨le_of_not_ge h05, h56x, h60x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    apply (convexHull_mono
      (s := {pts 0, fanLeft7 pts i, fanRight7 pts i})
      (t := Set.range pts) ?_) hi
    fin_cases i
    all_goals
      rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    · exact ⟨⟨0, rfl⟩, ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨3, rfl⟩, ⟨4, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨4, rfl⟩, ⟨5, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨5, rfl⟩, ⟨6, rfl⟩⟩⟩

private lemma strictCCW7_fan_pairwise (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    ∀ ⦃i j : Fin 5⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft7 pts i, fanRight7 pts i})
        (convexHull ℝ {pts 0, fanLeft7 pts j, fanRight7 pts j}) := by
  have haux : ∀ {i j : Fin 5}, i < j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft7 pts i, fanRight7 pts i})
        (convexHull ℝ {pts 0, fanLeft7 pts j, fanRight7 pts j}) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp only [Fin.mk_lt_mk] at hij
    all_goals try omega
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 1) (pts 2) (pts 3)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 3 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 1) (pts 2) (pts 3) (pts 4)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 2 4 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 1) (pts 2) (pts 4) (pts 5)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 4 (by decide) (by decide))
        (hpos 0 2 5 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 1) (pts 2) (pts 5) (pts 6)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 5 (by decide) (by decide))
        (hpos 0 2 6 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 2) (pts 3) (pts 4)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 2) (pts 3) (pts 4) (pts 5)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 3 5 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 2) (pts 3) (pts 5) (pts 6)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 5 (by decide) (by decide))
        (hpos 0 3 6 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 3) (pts 4) (pts 5)
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 4 5 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 3) (pts 4) (pts 5) (pts 6)
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 4 5 (by decide) (by decide))
        (hpos 0 4 6 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 4) (pts 5) (pts 6)
        (hpos 0 4 5 (by decide) (by decide))
        (hpos 0 5 6 (by decide) (by decide))
  intro i j hij
  by_cases hlt : i < j
  · exact haux hlt
  · exact (haux (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm

/-- Five-triangle fan formula for a strictly convex seven-cycle. -/
theorem volume_convexHull_strictCCW7 (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal
        ((sig (pts 0) (pts 1) (pts 2) + sig (pts 0) (pts 2) (pts 3)
          + sig (pts 0) (pts 3) (pts 4) + sig (pts 0) (pts 4) (pts 5)
          + sig (pts 0) (pts 5) (pts 6)) / 2) := by
  have h012 := hpos 0 1 2 (by decide) (by decide)
  have h023 := hpos 0 2 3 (by decide) (by decide)
  have h034 := hpos 0 3 4 (by decide) (by decide)
  have h045 := hpos 0 4 5 (by decide) (by decide)
  have h056 := hpos 0 5 6 (by decide) (by decide)
  rw [volume_convexHull_eq_sum_fan (Set.range pts) (pts 0)
    (fanLeft7 pts) (fanRight7 pts)
    (strictCCW7_fan_decomposition pts hpos) (strictCCW7_fan_pairwise pts hpos)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Fin.sum_univ_five]
  change |sig (pts 0) (pts 1) (pts 2)| / 2 + |sig (pts 0) (pts 2) (pts 3)| / 2
    + |sig (pts 0) (pts 3) (pts 4)| / 2 + |sig (pts 0) (pts 4) (pts 5)| / 2
    + |sig (pts 0) (pts 5) (pts 6)| / 2 = _
  rw [abs_of_pos h012, abs_of_pos h023, abs_of_pos h034, abs_of_pos h045,
    abs_of_pos h056]
  ring

end HullBridge
