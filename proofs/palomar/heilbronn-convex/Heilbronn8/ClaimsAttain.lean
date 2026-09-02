import Heilbronn8.Attain
import Heilbronn8.PolyVolume

namespace Heilbronn8

/-! # Attainment of the eight-point Heilbronn constant

This file is the final, measure-theoretic audit surface for the attaining
configuration. The internal doubled-area calculations appear only in the
proofs; the final theorem is stated entirely with convex hulls and volume.
-/

/-- The diagonal normalization `(x, y) ↦ ((2 / H2w) * x, y)`. -/
private noncomputable def normalizeLinear :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(2 / H2w : ℝ), 0; 0, 1]

/-- The explicit witness, rescaled in one coordinate to have hull volume one. -/
noncomputable def wN (i : Fin 8) : ℝ × ℝ :=
  ((2 / H2w) * (w i).1, (w i).2)

private lemma normalizeLinear_apply (p : ℝ × ℝ) :
    normalizeLinear p = ((2 / H2w) * p.1, p.2) := by
  rw [normalizeLinear, Matrix.toLin_finTwoProd_apply]
  simp

private lemma det_normalizeLinear :
    LinearMap.det normalizeLinear = 2 / H2w := by
  simp [normalizeLinear, Matrix.det_fin_two]

private lemma range_wN :
    Set.range wN = normalizeLinear '' Set.range w := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨w i, ⟨i, rfl⟩, by simp [wN, normalizeLinear_apply]⟩
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp [wN, normalizeLinear_apply]⟩

/-- Every doubled triangle area is multiplied by the normalization factor. -/
lemma sig_wN (i j k : Fin 8) :
    sig (wN i) (wN j) (wN k) =
      (2 / H2w) * sig (w i) (w j) (w k) := by
  simp only [wN, sig]
  ring

/-- The normalized witness has convex-hull volume exactly one. -/
theorem volume_convexHull_wN :
    MeasureTheory.volume (convexHull ℝ (Set.range wN)) = 1 := by
  have hscale : 0 < 2 / H2w := div_pos (by norm_num) H2w_pos
  calc
    MeasureTheory.volume (convexHull ℝ (Set.range wN)) =
        MeasureTheory.volume
          (normalizeLinear '' convexHull ℝ (Set.range w)) := by
      rw [normalizeLinear.image_convexHull, range_wN]
    _ = ENNReal.ofReal |LinearMap.det normalizeLinear| *
          MeasureTheory.volume (convexHull ℝ (Set.range w)) := by
      rw [MeasureTheory.Measure.addHaar_image_linearMap]
    _ = ENNReal.ofReal (|2 / H2w| * (H2w / 2)) := by
      rw [volume_convexHull_w, det_normalizeLinear,
        ENNReal.ofReal_mul (abs_nonneg (2 / H2w))]
    _ = 1 := by
      rw [abs_of_pos hscale, ENNReal.ofReal_eq_one]
      field_simp [ne_of_gt H2w_pos]

private lemma scale_mul_H2w (x : ℝ) :
    (2 / H2w) * (x * H2w) = 2 * x := by
  field_simp [ne_of_gt H2w_pos]

/-- The normalized doubled minimum triangle area is `2 * v8`. -/
theorem minTri_wN : minTri wN = 2 * v8 := by
  have hscale : 0 < 2 / H2w := div_pos (by norm_num) H2w_pos
  apply le_antisymm
  · calc
      minTri wN ≤ |sig (wN 0) (wN 1) (wN 2)| :=
        minTri_le wN (by decide) (by decide)
      _ = |(2 / H2w) * sig (w 0) (w 1) (w 2)| := by
        rw [sig_wN]
      _ = (2 / H2w) * (v8 * H2w) := by
        rw [abs_mul, abs_of_pos hscale, sig_w_012,
          abs_of_pos v8H2w_pos]
      _ = 2 * v8 := scale_mul_H2w v8
  · apply le_minTri
    intro i j k hij hjk
    have hmin : v8 * H2w ≤ |sig (w i) (w j) (w k)| := by
      rw [← witness_attains.1]
      exact minTri_le w hij hjk
    calc
      2 * v8 = (2 / H2w) * (v8 * H2w) :=
        (scale_mul_H2w v8).symm
      _ ≤ (2 / H2w) * |sig (w i) (w j) (w k)| :=
        mul_le_mul_of_nonneg_left hmin hscale.le
      _ = |sig (wN i) (wN j) (wN k)| := by
        rw [sig_wN, abs_mul, abs_of_pos hscale]

/--
The defining constant is the unique root of `P` in the certified interval.
In particular, the unique point exhibited here is `v8` by `v8_spec`.
-/
theorem v8_unique_root :
    ∃! x : ℝ,
      x ∈ Set.Icc (79 / 1000 : ℝ) (81 / 1000) ∧ P x = 0 :=
  v8_existsUnique

/--
There is a unit-volume configuration of eight points for which every triangle
has volume at least `v8`, and an increasing triple has volume exactly `v8`.
-/
theorem attainment_claims :
    ∃ p : Fin 8 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      (∀ i j k : Fin 8, i < j → j < k →
        ENNReal.ofReal v8 ≤
          MeasureTheory.volume (convexHull ℝ {p i, p j, p k})) ∧
      ∃ i j k : Fin 8,
        i < j ∧ j < k ∧
        MeasureTheory.volume (convexHull ℝ {p i, p j, p k}) =
          ENNReal.ofReal v8 := by
  refine ⟨wN, volume_convexHull_wN, ?_, 0, 1, 2,
    by decide, by decide, ?_⟩
  · intro i j k hij hjk
    rw [volume_convexHull_triple]
    apply ENNReal.ofReal_le_ofReal
    have hmin := minTri_le wN hij hjk
    rw [minTri_wN] at hmin
    linarith
  · rw [volume_convexHull_triple, sig_wN, sig_w_012,
      scale_mul_H2w, abs_of_pos (mul_pos (by norm_num) v8_pos)]
    congr 1
    ring

end Heilbronn8
