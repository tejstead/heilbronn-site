import Heil7.N7UpperFinal
import Heil7.OptimizerEqualityCases
import Heil7.Hull6EqualityFamily
import Heil7.N7FamilyAffine

/-!
# Exhaustive classification of the seven-point optimizers

This is the thin final assembly layer.  Strictness in hull sizes three, four,
five, and seven first forces an equality configuration into the hull-six
packet.  The hull-six sign dispatcher and tight equality reconstruction then
identify it with the full real family up to an arbitrary nonsingular affine
map and relabeling.
-/

set_option linter.style.header false

namespace HeilbronnChallenge

namespace N7Upper

/-- Every positive-area equality configuration belongs to the displayed
optimizer family up to arbitrary nonsingular-affine equivalence. -/
theorem sevenPointEquality_exists_family
    (v : Configuration7) (hm : 0 < minTri v)
    (heq : 9 * minTri v = HullBridge.doubledHullArea v) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 4 / 3 ∧
      AffineEquivalent (sevenFamilyAt t) v := by
  obtain ⟨sigma, hgauge, hdata⟩ :=
    areaEquality_relabel_hullSix_proved v hm heq
  obtain ⟨t, ht1, ht4, hfamily⟩ :=
    hullSixEqualityData_exists_family (v ∘ sigma) hdata
  have hback : AffineEquivalent (v ∘ sigma) v :=
    affineEquivalent_symm (affineEquivalent_of_gaugeEquivalent hgauge)
  exact ⟨t, ht1, ht4, affineEquivalent_trans hfamily hback⟩

end N7Upper

/-- Every parameter in the exact interval `[1,4/3]` gives a unit-area
optimizer. -/
theorem heilbronn_convex_seven_family_attains
    (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 4 / 3) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (sevenFamilyAt t))) = 1 ∧
      minTri (sevenFamilyAt t) = 2 * v7 := by
  rw [sevenFamilyAt_eq_cfg7Family]
  constructor
  · exact volume_convexHull_cfg7Family t ht
  · rw [minTri_cfg7Family t ht, v7]
    norm_num

/-- Exhaustive equality classification for the sharp seven-point bound: a
unit-hull configuration is optimal exactly when it belongs to the displayed
family modulo arbitrary nonsingular affine maps and relabeling. -/
theorem heilbronn_convex_seven_optimizer_classification
    (p : Fin 7 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p = 2 * v7 ↔
      ∃ t : ℝ, 1 ≤ t ∧ t ≤ 4 / 3 ∧
        AffineEquivalent (sevenFamilyAt t) p := by
  constructor
  · intro hatt
    have hm : 0 < minTri p := by
      rw [hatt, v7]
      norm_num
    have harea := HullBridge.doubledHullArea_of_unit_volume hvol
    have heq : 9 * minTri p = HullBridge.doubledHullArea p := by
      rw [hatt, harea, v7]
      norm_num
    exact N7Upper.sevenPointEquality_exists_family p hm heq
  · rintro ⟨t, ht1, ht4, sigma, T, hmap⟩
    have hfamily :=
      heilbronn_convex_seven_family_attains t ⟨ht1, ht4⟩
    have hrange : Set.range (sevenFamilyAt t ∘ sigma) =
        Set.range (sevenFamilyAt t) :=
      sigma.surjective.range_comp (sevenFamilyAt t)
    have hsourcevol : MeasureTheory.volume
        (convexHull ℝ (Set.range (sevenFamilyAt t ∘ sigma))) = 1 := by
      rw [hrange]
      exact hfamily.1
    have htargetvol : MeasureTheory.volume
        (convexHull ℝ
          (Set.range (fun i ↦ T.map ((sevenFamilyAt t ∘ sigma) i)))) = 1 := by
      simpa only [Function.comp_apply, ← hmap] using hvol
    have hscale := volume_convexHull_nonsingularAffine T
      (sevenFamilyAt t ∘ sigma)
    rw [hsourcevol, mul_one, htargetvol] at hscale
    have habsdet : |T.det| = 1 := by
      apply ENNReal.ofReal_eq_one.mp
      exact hscale.symm
    calc
      minTri p = minTri (fun i ↦ T.map (sevenFamilyAt t (sigma i))) :=
        congrArg minTri hmap
      _ = |T.det| * minTri (sevenFamilyAt t ∘ sigma) := by
        simpa only [Function.comp_apply] using
          minTri7_nonsingularAffine (sevenFamilyAt t ∘ sigma) T
      _ = |T.det| * minTri (sevenFamilyAt t) := by
        rw [minTri7_perm]
      _ = 2 * v7 := by rw [habsdet, one_mul, hfamily.2]

/-- A continuum of parameters gives pairwise affine-inequivalent unit-hull
optimizers. -/
theorem heilbronn_convex_seven_infinite_optimizers :
    Cardinal.mk (Set.Icc ((6 : ℝ) / 5) (5 / 4)) = Cardinal.continuum ∧
    (∀ t : ℝ, t ∈ Set.Icc ((6 : ℝ) / 5) (5 / 4) →
      MeasureTheory.volume
          (convexHull ℝ (Set.range (sevenFamilyAt t))) = 1 ∧
        minTri (sevenFamilyAt t) = 2 * v7) ∧
    ∀ s t : ℝ,
      s ∈ Set.Icc ((6 : ℝ) / 5) (5 / 4) →
      t ∈ Set.Icc ((6 : ℝ) / 5) (5 / 4) →
      AffineEquivalent (sevenFamilyAt s) (sevenFamilyAt t) → s = t := by
  constructor
  · exact Cardinal.mk_Icc_real (by norm_num)
  · constructor
    · intro t ht
      exact heilbronn_convex_seven_family_attains t (by
        constructor <;> nlinarith only [ht.1, ht.2])
    · intro s t hs ht hequiv
      exact heilbronn_convex_seven_real_family_inequivalent s t hs ht hequiv

end HeilbronnChallenge
