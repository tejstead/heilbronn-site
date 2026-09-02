import Heilbronn8.Defs
import Mathlib

namespace Heilbronn8

/-! ## Barycentric membership -/

lemma mem_convexHull_of_inTri (p a b c : ℝ × ℝ) :
    InTri p a b c → p ∈ convexHull ℝ {a, b, c} := by
  rintro ⟨x, y, z, hx, hy, hz, hsum, rfl⟩
  let w : Fin 3 → ℝ := ![x, y, z]
  let v : Fin 3 → ℝ × ℝ := ![a, b, c]
  apply mem_convexHull_of_exists_fintype w v
  · intro i
    fin_cases i <;> simpa [w]
  · simpa [w, Fin.sum_univ_succ, add_assoc] using hsum
  · intro i
    fin_cases i <;> simp [v]
  · simp [w, v, Fin.sum_univ_succ, add_assoc]

private lemma inTri_of_mem_convexHull (p a b c : ℝ × ℝ) :
    p ∈ convexHull ℝ {a, b, c} → InTri p a b c := by
  apply convexHull_min
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by positivity, by positivity, by positivity,
        by norm_num, by simp⟩
    · exact ⟨0, 1, 0, by positivity, by positivity, by positivity,
        by norm_num, by simp⟩
    · exact ⟨0, 0, 1, by positivity, by positivity, by positivity,
        by norm_num, by simp⟩
  · rintro p ⟨x₁, y₁, z₁, hx₁, hy₁, hz₁, hs₁, hp⟩
      q ⟨x₂, y₂, z₂, hx₂, hy₂, hz₂, hs₂, hq⟩
      u v hu hv huv
    refine ⟨u * x₁ + v * x₂, u * y₁ + v * y₂, u * z₁ + v * z₂,
      add_nonneg (mul_nonneg hu hx₁) (mul_nonneg hv hx₂),
      add_nonneg (mul_nonneg hu hy₁) (mul_nonneg hv hy₂),
      add_nonneg (mul_nonneg hu hz₁) (mul_nonneg hv hz₂), ?_, ?_⟩
    · nlinarith
    · rw [hp, hq]
      module

theorem inTri_iff_mem_convexHull (p a b c : ℝ × ℝ) :
    InTri p a b c ↔ p ∈ convexHull ℝ {a, b, c} :=
  ⟨mem_convexHull_of_inTri p a b c, inTri_of_mem_convexHull p a b c⟩

lemma InTri.mem_convexHull {p a b c : ℝ × ℝ} (h : InTri p a b c) :
    p ∈ convexHull ℝ {a, b, c} :=
  mem_convexHull_of_inTri p a b c h

/-! ## The standard triangle -/

private def standardTriangle : Set (ℝ × ℝ) :=
  convexHull ℝ
    {((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))}

private lemma mem_standardTriangle_iff (p : ℝ × ℝ) :
    p ∈ standardTriangle ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [standardTriangle, ← inTri_iff_mem_convexHull]
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hsum, hp⟩
    have hfst : p.1 = y := by
      rw [hp]
      simp
    have hsnd : p.2 = z := by
      rw [hp]
      simp
    constructor
    · simpa [hfst] using hy
    constructor
    · simpa [hsnd] using hz
    · rw [hfst, hsnd]
      linarith
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨1 - p.1 - p.2, p.1, p.2, by linarith, hx, hy, by ring, ?_⟩
    ext <;> simp

private def reflectPoint (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, 1 - p.2)

private def upperTriangle : Set (ℝ × ℝ) :=
  reflectPoint '' standardTriangle

private lemma mem_upperTriangle_iff (p : ℝ × ℝ) :
    p ∈ upperTriangle ↔
      p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1 + p.2 := by
  rw [upperTriangle]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_standardTriangle_iff] at hq
    dsimp [reflectPoint]
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨reflectPoint p, ?_, ?_⟩
    · rw [mem_standardTriangle_iff]
      dsimp [reflectPoint]
      constructor
      · linarith
      constructor <;> linarith
    · ext <;> simp [reflectPoint]

private lemma standard_union_upper :
    standardTriangle ∪ upperTriangle =
      Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ)) := by
  ext p
  rw [Set.mem_union, mem_standardTriangle_iff, mem_upperTriangle_iff]
  simp only [Set.mem_Icc, Prod.le_def]
  constructor
  · rintro (h | h)
    · constructor <;> constructor <;> linarith
    · constructor <;> constructor <;> linarith
  · rintro ⟨⟨hx0, hy0⟩, hx1, hy1⟩
    by_cases h : p.1 + p.2 ≤ 1
    · exact Or.inl ⟨hx0, hy0, h⟩
    · exact Or.inr ⟨hx1, hy1, le_of_not_ge h⟩

private noncomputable def diagonalLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(1 : ℝ), 0; -1, 0]

private def diagonalAffine : Set (ℝ × ℝ) :=
  (fun x => ((0 : ℝ), (1 : ℝ)) + x) ''
    (diagonalLinear '' Set.univ)

private lemma volume_diagonalLinear_range :
    MeasureTheory.volume (diagonalLinear '' Set.univ) = 0 := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap]
  simp [diagonalLinear, Matrix.det_fin_two]

private lemma volume_diagonalAffine :
    MeasureTheory.volume diagonalAffine = 0 := by
  rw [diagonalAffine, Set.image_add_left,
    MeasureTheory.measure_preimage_add]
  exact volume_diagonalLinear_range

private lemma standard_inter_upper_subset_diagonalAffine :
    standardTriangle ∩ upperTriangle ⊆ diagonalAffine := by
  intro p hp
  rw [Set.mem_inter_iff, mem_standardTriangle_iff,
    mem_upperTriangle_iff] at hp
  have hsum : p.1 + p.2 = 1 := le_antisymm hp.1.2.2 hp.2.2.2
  refine ⟨diagonalLinear (p.1, 0), ?_, ?_⟩
  · exact ⟨(p.1, 0), Set.mem_univ _, rfl⟩
  · rw [diagonalLinear, Matrix.toLin_finTwoProd_apply]
    ext
    · simp
    · dsimp
      linarith

private lemma volume_standard_inter_upper :
    MeasureTheory.volume (standardTriangle ∩ upperTriangle) = 0 :=
  MeasureTheory.measure_mono_null
    standard_inter_upper_subset_diagonalAffine volume_diagonalAffine

private noncomputable def negLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(-1 : ℝ), 0; 0, -1]

private lemma upperTriangle_eq_translate :
    upperTriangle =
      (fun y => ((1 : ℝ), (1 : ℝ)) + y) ''
        (negLinear '' standardTriangle) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨negLinear x, ⟨x, hx, rfl⟩, ?_⟩
    rw [negLinear, Matrix.toLin_finTwoProd_apply]
    ext <;> simp [reflectPoint, sub_eq_add_neg]
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [negLinear, Matrix.toLin_finTwoProd_apply]
    ext <;> simp [reflectPoint, sub_eq_add_neg]

private lemma volume_upper_eq_standard :
    MeasureTheory.volume upperTriangle =
      MeasureTheory.volume standardTriangle := by
  rw [upperTriangle_eq_translate, Set.image_add_left,
    MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap]
  simp [negLinear, Matrix.det_fin_two]

private lemma measurableSet_upperTriangle : MeasurableSet upperTriangle := by
  have hc : Continuous reflectPoint :=
    (continuous_const.sub continuous_fst).prodMk
      (continuous_const.sub continuous_snd)
  exact ((Set.Finite.isCompact_convexHull ℝ (by simp)).image hc).measurableSet

private lemma volume_unitSquare :
    MeasureTheory.volume
      (Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ))) = 1 := by
  have hsquare :
      Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ)) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Prod.le_def]
  rw [hsquare, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Measure.prod_prod]
  norm_num

theorem volume_standardTriangle :
    MeasureTheory.volume standardTriangle =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := MeasureTheory.measure_union_add_inter
    (μ := MeasureTheory.volume) standardTriangle measurableSet_upperTriangle
  rw [standard_union_upper, volume_unitSquare,
    volume_standard_inter_upper, volume_upper_eq_standard] at h
  have hdouble :
      MeasureTheory.volume standardTriangle +
        MeasureTheory.volume standardTriangle = 1 := by
    simpa using h.symm
  calc
    MeasureTheory.volume standardTriangle = (1 : ENNReal) / 2 := by
      apply (ENNReal.eq_div_iff (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)).2
      simpa [two_mul] using hdouble
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-! ## Affine images of the standard triangle -/

private noncomputable def triangleLinear (a b c : ℝ × ℝ) :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![b.1 - a.1, c.1 - a.1; b.2 - a.2, c.2 - a.2]

private lemma det_triangleLinear (a b c : ℝ × ℝ) :
    LinearMap.det (triangleLinear a b c) = sig a b c := by
  simp [triangleLinear, Matrix.det_fin_two, sig]

private lemma convexHull_triple_eq_affine_image (a b c : ℝ × ℝ) :
    convexHull ℝ {a, b, c} =
      (fun x => a + x) '' (triangleLinear a b c '' standardTriangle) := by
  ext p
  rw [← inTri_iff_mem_convexHull]
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hsum, hp⟩
    refine ⟨triangleLinear a b c (y, z), ⟨(y, z), ?_, rfl⟩, ?_⟩
    · rw [mem_standardTriangle_iff]
      exact ⟨hy, hz, by linarith⟩
    · have hx' : x = 1 - y - z := by linarith
      rw [triangleLinear, Matrix.toLin_finTwoProd_apply, hp, hx']
      ext <;> dsimp <;> ring
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨r, hr, rfl⟩
    rw [mem_standardTriangle_iff] at hr
    refine ⟨1 - r.1 - r.2, r.1, r.2, by linarith,
      hr.1, hr.2.1, by ring, ?_⟩
    rw [triangleLinear, Matrix.toLin_finTwoProd_apply]
    ext <;> dsimp <;> ring

theorem volume_triangle (a b c : ℝ × ℝ) :
    MeasureTheory.volume (convexHull ℝ {a, b, c}) =
      ENNReal.ofReal (|sig a b c| / 2) := by
  rw [convexHull_triple_eq_affine_image, Set.image_add_left,
    MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap,
    det_triangleLinear, volume_standardTriangle,
    ← ENNReal.ofReal_mul (abs_nonneg (sig a b c))]
  congr 1
  ring

theorem volume_convexHull_triple (a b c : ℝ × ℝ) :
    MeasureTheory.volume (convexHull ℝ {a, b, c}) =
      ENNReal.ofReal (|sig a b c| / 2) :=
  volume_triangle a b c

theorem volumeReal_convexHull_triple (a b c : ℝ × ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).real
        (convexHull ℝ {a, b, c}) =
      |sig a b c| / 2 := by
  rw [MeasureTheory.measureReal_def, volume_triangle,
    ENNReal.toReal_ofReal]
  positivity

theorem volume_convexHull_triple_eq_zero_iff (a b c : ℝ × ℝ) :
    MeasureTheory.volume (convexHull ℝ {a, b, c}) = 0 ↔
      sig a b c = 0 := by
  rw [volume_triangle, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have habs : |sig a b c| = 0 := by
      nlinarith [abs_nonneg (sig a b c)]
    exact abs_eq_zero.mp habs
  · rintro h
    simp [h]

theorem volume_segment_eq_zero (p q : ℝ × ℝ) :
    MeasureTheory.volume (segment ℝ p q) = 0 := by
  rw [← convexHull_pair]
  simpa [sig] using volume_triangle p q q

end Heilbronn8
