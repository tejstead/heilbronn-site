/-
n = 3: h_convex 3 = 1.

For three points the hull IS the triangle, so unit hull area forces
|sig| = 2 and minTri is pinned at 2 for every admissible configuration. The
admissible set is the single point {1}.
-/
import Solution.Common

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- With three points the only ordered triple is `(0, 1, 2)`. -/
theorem minTri_three (p : Fin 3 → ℝ × ℝ) :
    minTri p = |sig (p 0) (p 1) (p 2)| := by
  apply le_antisymm
  · exact minTri_le p 0 1 2 (by decide) (by decide)
  · apply le_minTri
    intro t ht
    have hmem : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and]
        using ht
    obtain ⟨h0, h1, h2⟩ := triple_cases3 t.1 t.2.1 t.2.2 hmem.1 hmem.2
    rw [h0, h1, h2]

/-- Unit hull area pins the minimum triangle at 2. -/
theorem minTri_three_eq_two (p : Fin 3 → ℝ × ℝ)
    (hvol : volume (convexHull ℝ (Set.range p)) = 1) : minTri p = 2 := by
  rw [volume_hull_fin3] at hvol
  have h : |sig (p 0) (p 1) (p 2)| / 2 = 1 := ENNReal.ofReal_eq_one.mp hvol
  rw [minTri_three]
  linarith

/-- Witness: the triangle `(0,0), (2,0), (0,1)`, of Lebesgue area 1. -/
noncomputable def cfg3 : Fin 3 → ℝ × ℝ := ![(0, 0), (2, 0), (0, 1)]

theorem cfg3_sig : sig (cfg3 0) (cfg3 1) (cfg3 2) = 2 := by
  have e0 : cfg3 0 = ((0 : ℝ), (0 : ℝ)) := by simp [cfg3]
  have e1 : cfg3 1 = ((2 : ℝ), (0 : ℝ)) := by simp [cfg3]
  have e2 : cfg3 2 = ((0 : ℝ), (1 : ℝ)) := by simp [cfg3]
  rw [e0, e1, e2]
  simp only [sig]
  norm_num

theorem cfg3_volume : volume (convexHull ℝ (Set.range cfg3)) = 1 := by
  have habs : |(2 : ℝ)| / 2 = 1 := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [volume_hull_fin3, cfg3_sig, habs, ENNReal.ofReal_one]

theorem cfg3_minTri : minTri cfg3 = 2 * v3 := by
  rw [minTri_three, cfg3_sig, v3]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ## Challenge theorems -/

theorem heilbronn_convex_three_attained :
    ∃ p : Fin 3 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v3 :=
  ⟨cfg3, cfg3_volume, cfg3_minTri⟩

theorem heilbronn_convex_three : h_convex 3 = v3 := by
  apply h_convex_eq
  · refine ⟨by norm_num [v3], by norm_num [v3], heilbronn_convex_three_attained⟩
  · rintro r ⟨_, _, p, hvol, hmin⟩
    have h2 := minTri_three_eq_two p hvol
    rw [hmin] at h2
    rw [v3]
    linarith

noncomputable def witness3 : Fin 3 → ℝ × ℝ :=
  heilbronn_convex_three_attained.choose

theorem witness3_spec :
    MeasureTheory.volume (convexHull ℝ (Set.range witness3)) = 1 ∧
      minTri witness3 = 2 * v3 :=
  heilbronn_convex_three_attained.choose_spec

/-! ## Uniqueness

Any two unit-area triangles are related by a positive-determinant affine map,
after possibly swapping two labels to fix the orientation. -/

theorem heilbronn_convex_three_unique_from_witness
    (p : Fin 3 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hatt : minTri p = 2 * v3) :
    GaugeEquivalent witness3 p := by
  obtain ⟨hwvol, _⟩ := witness3_spec
  have hw : |sig (witness3 0) (witness3 1) (witness3 2)| = 2 := by
    have := minTri_three_eq_two witness3 hwvol
    rw [minTri_three] at this
    exact this
  have hp : |sig (p 0) (p 1) (p 2)| = 2 := by
    have := minTri_three_eq_two p hvol
    rw [minTri_three] at this
    exact this
  have hwne : sig (witness3 0) (witness3 1) (witness3 2) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    norm_num at hw
  have hpne : sig (p 0) (p 1) (p 2) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hp
    norm_num at hp
  have hratio :
      sig (p 0) (p 1) (p 2) / sig (witness3 0) (witness3 1) (witness3 2) ≠ 0 :=
    div_ne_zero hpne hwne
  -- choose the relabelling that matches the two orientations
  rcases lt_or_gt_of_ne hratio with hneg | hpos
  · -- opposite orientation: swap labels 1 and 2 of the witness
    have hswap : sig (witness3 0) (witness3 2) (witness3 1)
        = -sig (witness3 0) (witness3 1) (witness3 2) := by
      simp only [sig]; ring
    have hwne' : sig (witness3 0) (witness3 2) (witness3 1) ≠ 0 := by
      rw [hswap]
      exact neg_ne_zero.mpr hwne
    have hpos' :
        0 < sig (p 0) (p 1) (p 2) / sig (witness3 0) (witness3 2) (witness3 1) := by
      rw [hswap, div_neg]
      linarith
    obtain ⟨a, b, c, d, e, f, hdet, h0, h1, h2⟩ :=
      HullBridge.exists_affMap_triangle (witness3 0) (witness3 2) (witness3 1)
        (p 0) (p 1) (p 2) hwne' hpos'
    refine ⟨Equiv.swap 1 2, ⟨a, b, c, d, e, f, hdet⟩, ?_⟩
    funext i
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact h0.symm
    · rw [Equiv.swap_apply_left]
      exact h1.symm
    · rw [Equiv.swap_apply_right]
      exact h2.symm
  · -- same orientation: identity relabelling
    obtain ⟨a, b, c, d, e, f, hdet, h0, h1, h2⟩ :=
      HullBridge.exists_affMap_triangle (witness3 0) (witness3 1) (witness3 2)
        (p 0) (p 1) (p 2) hwne hpos
    refine ⟨Equiv.refl _, ⟨a, b, c, d, e, f, hdet⟩, ?_⟩
    funext i
    rcases fin3_cases i with rfl | rfl | rfl
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm

end HeilbronnChallenge
