/-
Bridge from the internal shoelace-area proof to the unified challenge format.

The internal proof (Main.lean) establishes:
  main_bound : IsHullArea v H -> minTri v / 2 <= tau * H
  exists_hullArea : forall v, exists H, IsHullArea v H
  golden_attains : minTri golden = tau * penArea golden

where IsHullArea witnesses H as the shoelace area of the convex hull
(already halved: H = penArea/2, quadArea/2, or sig/2).

The challenge format (CHALLENGE_UNIFIED.lean) uses Lebesgue volume:
  MeasureTheory.volume (convexHull R (Set.range p)) = 1

This module bridges the gap. The key theorem:

  volume_triangle: vol(convexHull {a,b,c}) = |sig a b c| / 2

is proven in proofs/convex-n8/heil8/Heil8/TriVolume.lean (generic, does
not depend on n) using addHaar_image_linearMap and the standard-triangle
volume. From this, fan decomposition gives:

  isHullArea_eq_volume: IsHullArea v H -> H = vol(convexHull(range v))

for each hull topology (pentagon, quadrilateral, triangle). The fan
machinery (decomposition + AE-disjointness) is proven for 7-gons in
proofs/convex-n8/heil8/Heil8/PolyVolume.lean and needs only adaptation
to 3/4/5-gons.

SORRY COUNT: 7. All are mechanical ports from the n=8 codebase.
See proof sketches in comments.
-/
import Heil5.Main
import Heil5.Golden
import HullBridge

namespace Heilbronn5

open MeasureTheory

lemma sig_eq (p q r : ℝ × ℝ) : sig p q r = HullBridge.sig p q r := rfl

/-! ## Part A: Triangle volume

The proof (ported verbatim from Heil8.TriVolume) proceeds:
1. Define the standard triangle {(0,0),(1,0),(0,1)} and prove its
   Lebesgue volume is 1/2 (unit square = standard + reflected,
   intersection is a segment with zero measure).
2. Any triangle {a,b,c} is the affine image of the standard triangle
   under x -> a + triangleLinear(a,b,c)(x), where triangleLinear has
   det = sig(a,b,c).
3. addHaar_image_linearMap gives vol = |det| * vol(standard) = |sig|/2.

The full proof is ~220 lines (TriVolume.lean:54-265). The helper defs
(standardTriangle, triangleLinear, etc.) are identical to the n=8
versions since sig is the same. -/

theorem volume_triangle (a b c : ℝ × ℝ) :
    MeasureTheory.volume (convexHull ℝ {a, b, c}) =
      ENNReal.ofReal (|sig a b c| / 2) := by
  simpa only [sig_eq] using HullBridge.volume_triangle a b c

theorem volume_segment_eq_zero (p q : ℝ × ℝ) :
    MeasureTheory.volume (segment ℝ p q) = 0 := by
  exact HullBridge.volume_segment_eq_zero p q

/-! ## Part B: IsHullArea equals Lebesgue volume of hull

For each IsHullArea case, the shoelace area H equals the Lebesgue volume
of convexHull(range v). The argument uses fan decomposition: the polygon
decomposes into fan triangles from vertex 0, which are pairwise
AE-disjoint (adjacent share a segment, non-adjacent share at most a
point; both null by volume_segment_eq_zero). The sum of triangle volumes
(via volume_triangle) equals the shoelace fan sum.

The fan machinery is proven for 7-gons in PolyVolume.lean (n=8). For
n=5 the cases are simpler: pentagon = 3-fan, quadrilateral = 2-fan,
triangle = 1 triangle. -/

theorem isHullArea_eq_volume_pent (v : Fin 5 → ℝ × ℝ) (f : Fin 5 → Fin 5)
    (hf : Function.Injective f) (hc : ConvexPos (v ∘ f)) (hmin : 0 < minTri v) :
    ENNReal.ofReal (penArea (v ∘ f) / 2) =
      MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hrange : Set.range (v ∘ f) = Set.range v := hsurj.range_comp v
  have hmin' : 0 < minTri (v ∘ f) :=
    lt_of_lt_of_le hmin (minTri_comp_inj_le v f hf)
  obtain ⟨c012, c013, c014, c023, c024, c034, c123, c124, c134, c234⟩ := hc
  have h012 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) :=
    lt_of_le_of_ne c012 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_012 _))).symm
  have h013 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 3) :=
    lt_of_le_of_ne c013 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_013 _))).symm
  have h014 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 4) :=
    lt_of_le_of_ne c014 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_014 _))).symm
  have h023 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 2) ((v ∘ f) 3) :=
    lt_of_le_of_ne c023 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_023 _))).symm
  have h024 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 2) ((v ∘ f) 4) :=
    lt_of_le_of_ne c024 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_024 _))).symm
  have h034 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 3) ((v ∘ f) 4) :=
    lt_of_le_of_ne c034 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_034 _))).symm
  have h123 : 0 < sig ((v ∘ f) 1) ((v ∘ f) 2) ((v ∘ f) 3) :=
    lt_of_le_of_ne c123 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_123 _))).symm
  have h124 : 0 < sig ((v ∘ f) 1) ((v ∘ f) 2) ((v ∘ f) 4) :=
    lt_of_le_of_ne c124 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_124 _))).symm
  have h134 : 0 < sig ((v ∘ f) 1) ((v ∘ f) 3) ((v ∘ f) 4) :=
    lt_of_le_of_ne c134 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_134 _))).symm
  have h234 : 0 < sig ((v ∘ f) 2) ((v ∘ f) 3) ((v ∘ f) 4) :=
    lt_of_le_of_ne c234 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_234 _))).symm
  rw [← hrange, HullBridge.range_fin5]
  symm
  simpa only [← sig_eq, penArea] using
    HullBridge.volume_convexHull_pent
      ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) ((v ∘ f) 3) ((v ∘ f) 4)
      (by simpa only [← sig_eq] using h012) (by simpa only [← sig_eq] using h013)
      (by simpa only [← sig_eq] using h014) (by simpa only [← sig_eq] using h023)
      (by simpa only [← sig_eq] using h024) (by simpa only [← sig_eq] using h034)
      (by simpa only [← sig_eq] using h123) (by simpa only [← sig_eq] using h124)
      (by simpa only [← sig_eq] using h134) (by simpa only [← sig_eq] using h234)

theorem isHullArea_eq_volume_quad (v : Fin 5 → ℝ × ℝ) (f : Fin 5 → Fin 5)
    (hf : Function.Injective f) (hq : QuadPos (v ∘ f))
    (hw : ∃ x y z t : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ t ∧
      x + y + z + t = 1 ∧
      (v ∘ f) 4 = x • (v ∘ f) 0 + y • (v ∘ f) 1 +
        z • (v ∘ f) 2 + t • (v ∘ f) 3) (hmin : 0 < minTri v) :
    ENNReal.ofReal (quadArea (v ∘ f) / 2) =
      MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hrange : Set.range (v ∘ f) = Set.range v := hsurj.range_comp v
  have hmin' : 0 < minTri (v ∘ f) :=
    lt_of_lt_of_le hmin (minTri_comp_inj_le v f hf)
  obtain ⟨c012, c013, c023, c123⟩ := hq
  have h012 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) :=
    lt_of_le_of_ne c012 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_012 _))).symm
  have h013 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 3) :=
    lt_of_le_of_ne c013 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_013 _))).symm
  have h023 : 0 < sig ((v ∘ f) 0) ((v ∘ f) 2) ((v ∘ f) 3) :=
    lt_of_le_of_ne c023 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_023 _))).symm
  have h123 : 0 < sig ((v ∘ f) 1) ((v ∘ f) 2) ((v ∘ f) 3) :=
    lt_of_le_of_ne c123 (abs_pos.mp (lt_of_lt_of_le hmin' (minTri_le_123 _))).symm
  obtain ⟨x, y, z, t, hx, hy, hz, ht, hsum, heq⟩ := hw
  have h4mem : (v ∘ f) 4 ∈ convexHull ℝ
      ({(v ∘ f) 0, (v ∘ f) 1, (v ∘ f) 2, (v ∘ f) 3} : Set (ℝ × ℝ)) := by
    let weights : Fin 4 → ℝ := ![x, y, z, t]
    let points : Fin 4 → ℝ × ℝ :=
      ![(v ∘ f) 0, (v ∘ f) 1, (v ∘ f) 2, (v ∘ f) 3]
    rw [heq]
    apply mem_convexHull_of_exists_fintype weights points
    · intro i
      fin_cases i <;> simpa [weights]
    · simpa [weights, Fin.sum_univ_succ, add_assoc] using hsum
    · intro i
      fin_cases i <;> simp [points]
    · simp [weights, points, Fin.sum_univ_succ, add_assoc]
  have hs : Set.range (v ∘ f) ⊆ convexHull ℝ
      ({(v ∘ f) 0, (v ∘ f) 1, (v ∘ f) 2, (v ∘ f) 3} : Set (ℝ × ℝ)) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact h4mem
  have hmem (i : Fin 5) : (v ∘ f) i ∈ Set.range v := by
    rw [← hrange]
    exact ⟨i, rfl⟩
  have hhull : convexHull ℝ (Set.range v) = convexHull ℝ
      ({(v ∘ f) 0, (v ∘ f) 1, (v ∘ f) 2, (v ∘ f) 3} : Set (ℝ × ℝ)) := by
    apply Set.Subset.antisymm
    · apply convexHull_min
      · rwa [← hrange]
      · exact convex_convexHull ℝ _
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact subset_convexHull ℝ _ (hmem 0)
      · exact subset_convexHull ℝ _ (hmem 1)
      · exact subset_convexHull ℝ _ (hmem 2)
      · exact subset_convexHull ℝ _ (hmem 3)
  rw [hhull]
  symm
  simpa only [← sig_eq, quadArea] using
    HullBridge.volume_convexHull_quad
      ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) ((v ∘ f) 3)
      (by simpa only [← sig_eq] using h012) (by simpa only [← sig_eq] using h013)
      (by simpa only [← sig_eq] using h023) (by simpa only [← sig_eq] using h123)

theorem isHullArea_eq_volume_tri (v : Fin 5 → ℝ × ℝ) (f : Fin 5 → Fin 5)
    (hf : Function.Injective f)
    (h012 : 0 ≤ sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2))
    (h3 : InTri ((v ∘ f) 3) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2))
    (h4 : InTri ((v ∘ f) 4) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2))
    (hmin : 0 < minTri v) :
    ENNReal.ofReal (sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) / 2) =
      MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hrange : Set.range (v ∘ f) = Set.range v := hsurj.range_comp v
  change HullBridge.InTri ((v ∘ f) 3) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) at h3
  change HullBridge.InTri ((v ∘ f) 4) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) at h4
  have h3mem := (HullBridge.inTri_iff_mem_convexHull
    ((v ∘ f) 3) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2)).mp h3
  have h4mem := (HullBridge.inTri_iff_mem_convexHull
    ((v ∘ f) 4) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2)).mp h4
  have hs : Set.range v ⊆ convexHull ℝ
      ({(v ∘ f) 0, (v ∘ f) 1, (v ∘ f) 2} : Set (ℝ × ℝ)) := by
    rw [← hrange]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact h3mem
    · exact h4mem
  have hmem (i : Fin 5) : (v ∘ f) i ∈ Set.range v := by
    rw [← hrange]
    exact ⟨i, rfl⟩
  have hhull := HullBridge.convexHull_eq_triangle_of_inTri
    (Set.range v) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2)
    hs (hmem 0) (hmem 1) (hmem 2)
  rw [hhull, HullBridge.volume_triangle]
  simp only [← sig_eq, abs_of_nonneg h012]

/-- The shoelace hull area equals the Lebesgue volume in all cases. -/
theorem isHullArea_eq_volume (v : Fin 5 → ℝ × ℝ) (H : ℝ)
    (h : IsHullArea v H) (hmin : 0 < minTri v) :
    ENNReal.ofReal H =
      MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  cases h with
  | pent f hf hc => exact isHullArea_eq_volume_pent v f hf hc hmin
  | quad f hf hq hw => exact isHullArea_eq_volume_quad v f hf hq hw hmin
  | tri f hf h012 h3 h4 =>
      exact isHullArea_eq_volume_tri v f hf h012 h3 h4 hmin

/-! ## Part C: Challenge-format theorems -/

/-- Upper bound in challenge terms: for any unit-volume configuration,
    the half-minimum triangle area is at most tau. -/
theorem upper_bound_volume (v : Fin 5 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1) :
    minTri v / 2 ≤ tau := by
  rcases le_or_gt (minTri v) 0 with hz | hpos
  · have htau : 0 < tau := by linarith [quarter_le_tau]
    linarith
  obtain ⟨H, hH⟩ := exists_hullArea v
  have hHvol := isHullArea_eq_volume v H hH hpos
  rw [hvol] at hHvol
  have hHone : H = 1 := ENNReal.ofReal_eq_one.mp hHvol
  have hbound := main_bound v H hH
  rw [hHone] at hbound
  linarith

/-- The golden pentagon normalized to unit Lebesgue volume.
    Rescales the x-coordinate by 2 / penArea(golden). -/
noncomputable def goldenNorm : Fin 5 → ℝ × ℝ :=
  fun i => (2 / penArea golden * (golden i).1, (golden i).2)

theorem golden_penArea_pos : 0 < penArea golden := by
  obtain ⟨e1, _, _, e4, _⟩ := golden_sig_ears
  obtain ⟨_, n2, _, _, _⟩ := golden_sig_nonears
  unfold penArea; rw [e1, n2, e4]
  linarith [phi_pos]

/-- The normalized golden pentagon has Lebesgue hull volume 1. -/
theorem volume_goldenNorm :
    MeasureTheory.volume (convexHull ℝ (Set.range goldenNorm)) = 1 := by
  have hscale : 0 < 2 / penArea golden := div_pos (by norm_num) golden_penArea_pos
  have hdet : 0 < (2 / penArea golden) * 1 - 0 * 0 := by
    simpa using hscale
  have hmin : 0 < minTri golden := by
    rw [golden_attains]
    exact mul_pos tau_pos golden_penArea_pos
  have hgold := isHullArea_eq_volume_pent golden id Function.injective_id
    (by simpa only [Function.comp_id] using golden_convexPos) hmin
  simp only [Function.comp_id] at hgold
  have hnorm : goldenNorm = fun i =>
      HullBridge.affMap (2 / penArea golden) 0 0 1 0 0 (golden i) := by
    funext i
    simp [goldenNorm, HullBridge.affMap]
  rw [hnorm, HullBridge.range_affMap]
  rw [HullBridge.volume_convexHull_image_affMap _ _ _ _ _ _ hdet]
  simp only [mul_one, zero_mul, sub_zero]
  rw [← hgold, ← ENNReal.ofReal_mul hscale.le]
  have hpenne : penArea golden ≠ 0 := ne_of_gt golden_penArea_pos
  rw [show (2 / penArea golden) * (penArea golden / 2) = 1 by
    field_simp]
  exact ENNReal.ofReal_one

/-- The minimum triangle of the normalized golden pentagon. -/
theorem minTri_goldenNorm :
    minTri goldenNorm = 2 * tau := by
  have hscale : 0 < 2 / penArea golden := div_pos (by norm_num) golden_penArea_pos
  have hnorm (i : Fin 5) : goldenNorm i =
      HullBridge.affMap (2 / penArea golden) 0 0 1 0 0 (golden i) := by
    simp [goldenNorm, HullBridge.affMap]
  have hsig (i j k : Fin 5) :
      |sig (goldenNorm i) (goldenNorm j) (goldenNorm k)| =
        (2 / penArea golden) * |sig (golden i) (golden j) (golden k)| := by
    rw [hnorm i, hnorm j, hnorm k, sig_eq, HullBridge.sig_affMap, ← sig_eq]
    simp only [mul_one, zero_mul, sub_zero, abs_mul, abs_of_pos hscale]
  have hscale_min : minTri goldenNorm = (2 / penArea golden) * minTri golden := by
    unfold minTri
    rw [hsig 0 1 2, hsig 0 1 3, hsig 0 1 4, hsig 0 2 3, hsig 0 2 4,
      hsig 0 3 4, hsig 1 2 3, hsig 1 2 4, hsig 1 3 4, hsig 2 3 4]
    repeat' rw [← mul_min_of_nonneg _ _ hscale.le]
  rw [hscale_min, golden_attains]
  have hpenne : penArea golden ≠ 0 := ne_of_gt golden_penArea_pos
  field_simp

/-- Attainment: there exists a unit-volume configuration achieving tau. -/
theorem attainment_volume :
    ∃ p : Fin 5 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * tau :=
  ⟨goldenNorm, volume_goldenNorm, minTri_goldenNorm⟩

/-! ## Connection to CHALLENGE_UNIFIED.lean

The challenge defines:
  h_convex 5 = sSup {r | AdmissibleScore 5 r}
  AdmissibleScore 5 r := 0 <= r /\ r <= 1 /\
    exists p, volume(convexHull(range p)) = 1 /\ minTri p = 2 * r

From the theorems above:
  upper_bound_volume: for all unit-volume v, minTri v / 2 <= tau
    => for all r in {r | AdmissibleScore 5 r}, r <= tau
    => h_convex 5 <= tau

  attainment_volume: exists p, volume = 1 /\ minTri p = 2 * tau
    => tau in {r | AdmissibleScore 5 r} (given 0 <= tau <= 1)
    => tau <= h_convex 5

  Combining: h_convex 5 = tau = v5 = (5 - sqrt 5) / 10.

Remaining bookkeeping (not mathematically interesting):
  1. tau = v5 (root identification): tau is the smaller root of
     5x^2 - 5x + 1 in (0.276, 0.277). IVT + monotonicity.
  2. minTri compatibility: Heilbronn5.minTri (explicit min-chain) and
     HeilbronnChallenge.minTri (Finset.inf') agree after unfolding.
-/

end Heilbronn5
