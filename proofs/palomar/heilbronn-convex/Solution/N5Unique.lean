/-
n = 5 uniqueness.

`Heil5.Structure` pins five doubled areas of an optimal configuration: after a
relabeling, three triangles have doubled area `2 * v5` and the two diagonals
`phi * (2 * v5)`. Those five numbers determine the configuration once the frame
`(0, 1, 4)` is fixed: the frame carries six of the ten coordinates and the four
remaining ones are cut out by `HullBridge.point_unique_of_sigs`. So two optimal
configurations differ only by the affine map matching their frames, which is the
map with determinant one supplied by `HullBridge.exists_affMap_triangle`.
-/
import Solution.N5
import Heil5.Structure

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- The `n = 5` structure theorem in the challenge's vocabulary, with the
relabeling packaged as a permutation. -/
lemma five_optimal_perm (v : Fin 5 → ℝ × ℝ)
    (hvol : volume (convexHull ℝ (Set.range v)) = 1)
    (hmin : minTri v = 2 * v5) :
    ∃ σ : Equiv.Perm (Fin 5),
      sig (v (σ 0)) (v (σ 1)) (v (σ 4)) = 2 * v5 ∧
      sig (v (σ 0)) (v (σ 1)) (v (σ 2)) = 2 * v5 ∧
      sig (v (σ 0)) (v (σ 3)) (v (σ 4)) = 2 * v5 ∧
      sig (v (σ 0)) (v (σ 2)) (v (σ 4)) = Heilbronn5.phi * (2 * v5) ∧
      sig (v (σ 0)) (v (σ 1)) (v (σ 3)) = Heilbronn5.phi * (2 * v5) := by
  have hmin5 : Heilbronn5.minTri v = 2 * Heilbronn5.tau := by
    rw [minTri_eq_five, hmin, tau_eq_v5]
  obtain ⟨g, hg, e1, e2, e3, e4, e5⟩ :=
    Heilbronn5.five_optimal_structure v hvol hmin5
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← sig_eq_five, ← tau_eq_v5]; exact e1
  · rw [← sig_eq_five, ← tau_eq_v5]; exact e2
  · rw [← sig_eq_five, ← tau_eq_v5]; exact e3
  · rw [← sig_eq_five, ← tau_eq_v5]; exact e4
  · rw [← sig_eq_five, ← tau_eq_v5]; exact e5

theorem heilbronn_convex_five_unique_from_witness
    (p : Fin 5 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hatt : minTri p = 2 * v5) :
    GaugeEquivalent witness5 p := by
  have hv5 : 0 < v5 := by linarith [v5_spec.1]
  have hframe : (0 : ℝ) < 2 * v5 := by linarith
  obtain ⟨hwvol, hwatt⟩ := witness5_spec
  obtain ⟨sw, w014, w012, w034, w024, w013⟩ :=
    five_optimal_perm witness5 hwvol hwatt
  obtain ⟨sp, p014, p012, p034, p024, p013⟩ := five_optimal_perm p hvol hatt
  -- The same statements against `HullBridge.sig`, which has the same body.
  have hw014 : HullBridge.sig (witness5 (sw 0)) (witness5 (sw 1))
      (witness5 (sw 4)) = 2 * v5 := w014
  have hw012 : HullBridge.sig (witness5 (sw 0)) (witness5 (sw 1))
      (witness5 (sw 2)) = 2 * v5 := w012
  have hw034 : HullBridge.sig (witness5 (sw 0)) (witness5 (sw 3))
      (witness5 (sw 4)) = 2 * v5 := w034
  have hw024 : HullBridge.sig (witness5 (sw 0)) (witness5 (sw 2))
      (witness5 (sw 4)) = Heilbronn5.phi * (2 * v5) := w024
  have hw013 : HullBridge.sig (witness5 (sw 0)) (witness5 (sw 1))
      (witness5 (sw 3)) = Heilbronn5.phi * (2 * v5) := w013
  have hp014 : HullBridge.sig (p (sp 0)) (p (sp 1)) (p (sp 4)) = 2 * v5 := p014
  have hp012 : HullBridge.sig (p (sp 0)) (p (sp 1)) (p (sp 2)) = 2 * v5 := p012
  have hp034 : HullBridge.sig (p (sp 0)) (p (sp 3)) (p (sp 4)) = 2 * v5 := p034
  have hp024 : HullBridge.sig (p (sp 0)) (p (sp 2)) (p (sp 4))
      = Heilbronn5.phi * (2 * v5) := p024
  have hp013 : HullBridge.sig (p (sp 0)) (p (sp 1)) (p (sp 3))
      = Heilbronn5.phi * (2 * v5) := p013
  have hwne : HullBridge.sig (witness5 (sw 0)) (witness5 (sw 1))
      (witness5 (sw 4)) ≠ 0 := by rw [hw014]; exact hframe.ne'
  have hpne : HullBridge.sig (p (sp 0)) (p (sp 1)) (p (sp 4)) ≠ 0 := by
    rw [hp014]; exact hframe.ne'
  have hratio : 0 < HullBridge.sig (p (sp 0)) (p (sp 1)) (p (sp 4))
      / HullBridge.sig (witness5 (sw 0)) (witness5 (sw 1)) (witness5 (sw 4)) := by
    rw [hw014, hp014]; exact div_pos hframe hframe
  obtain ⟨a, b, c, d, e, f, hdet, h0, h1, h4⟩ :=
    HullBridge.exists_affMap_triangle (witness5 (sw 0)) (witness5 (sw 1))
      (witness5 (sw 4)) (p (sp 0)) (p (sp 1)) (p (sp 4)) hwne hratio
  -- Both frames have the same doubled area, so the matching map is area preserving.
  have hdet1 : a * d - b * c = 1 := by
    have hs := HullBridge.sig_affMap a b c d e f (witness5 (sw 0))
      (witness5 (sw 1)) (witness5 (sw 4))
    rw [h0, h1, h4, hp014, hw014] at hs
    have hz : (a * d - b * c - 1) * (2 * v5) = 0 := by
      linear_combination (-1 : ℝ) * hs
    rcases mul_eq_zero.mp hz with hq | hq
    · linarith
    · exact absurd hq hframe.ne'
  have himg : ∀ i j k : Fin 5,
      HullBridge.sig (HullBridge.affMap a b c d e f (witness5 (sw i)))
          (HullBridge.affMap a b c d e f (witness5 (sw j)))
          (HullBridge.affMap a b c d e f (witness5 (sw k)))
        = HullBridge.sig (witness5 (sw i)) (witness5 (sw j))
            (witness5 (sw k)) := by
    intro i j k
    rw [HullBridge.sig_affMap, hdet1, one_mul]
  have i012 : HullBridge.sig (p (sp 0)) (p (sp 1))
      (HullBridge.affMap a b c d e f (witness5 (sw 2))) = 2 * v5 := by
    rw [← h0, ← h1, himg 0 1 2, hw012]
  have i024 : HullBridge.sig (p (sp 0))
      (HullBridge.affMap a b c d e f (witness5 (sw 2))) (p (sp 4))
      = Heilbronn5.phi * (2 * v5) := by
    rw [← h0, ← h4, himg 0 2 4, hw024]
  have i013 : HullBridge.sig (p (sp 0)) (p (sp 1))
      (HullBridge.affMap a b c d e f (witness5 (sw 3)))
      = Heilbronn5.phi * (2 * v5) := by
    rw [← h0, ← h1, himg 0 1 3, hw013]
  have i034 : HullBridge.sig (p (sp 0))
      (HullBridge.affMap a b c d e f (witness5 (sw 3))) (p (sp 4)) = 2 * v5 := by
    rw [← h0, ← h4, himg 0 3 4, hw034]
  have key : ∀ i : Fin 5,
      p (sp i) = HullBridge.affMap a b c d e f (witness5 (sw i)) := by
    intro i
    rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact h0.symm
    · exact h1.symm
    · exact HullBridge.point_unique_of_sigs (p (sp 0)) (p (sp 1)) (p (sp 4))
        (p (sp 2)) (HullBridge.affMap a b c d e f (witness5 (sw 2))) hpne
        (by rw [hp012, i012]) (by rw [hp024, i024])
    · exact HullBridge.point_unique_of_sigs (p (sp 0)) (p (sp 1)) (p (sp 4))
        (p (sp 3)) (HullBridge.affMap a b c d e f (witness5 (sw 3))) hpne
        (by rw [hp013, i013]) (by rw [hp034, i034])
    · exact h4.symm
  refine ⟨sp.symm.trans sw, ⟨a, b, c, d, e, f, hdet⟩, ?_⟩
  funext i
  have hj := key (sp.symm i)
  rw [Equiv.apply_symm_apply] at hj
  rw [Equiv.trans_apply]
  exact hj

end HeilbronnChallenge
