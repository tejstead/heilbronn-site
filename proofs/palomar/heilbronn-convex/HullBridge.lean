import Mathlib

set_option linter.style.header false

/-!
# Measure-theoretic hull bridge

Shared library for the convex Heilbronn submission. It connects the
combinatorial/algebraic hull area used by the per-`n` proofs (shoelace fan
sums of the doubled signed area `sig`) to `MeasureTheory.volume` of the
convex hull, which is what the challenge file speaks about.

Nothing here mentions a particular `n`: statements are either about three,
four or five explicit points, or generic over `p : Fin n → ℝ × ℝ`.

The triangle-volume core and the fan a.e.-disjointness arguments follow the
n = 8 development (`Heilbronn8.TriVolume`, `Heilbronn8.PolyVolume`); the fan
decomposition is instantiated here for 3-, 4- and 5-gons.
-/

namespace HullBridge

open MeasureTheory

/-! ## Doubled signed area -/

/-- Doubled signed area of the triangle `p q r` (the 2x2 determinant).
Identical to `HeilbronnChallenge.sig`. -/
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

lemma sig_rotate (p q r : ℝ × ℝ) : sig p q r = sig q r p := by
  simp only [sig]; ring

lemma sig_swap (p q r : ℝ × ℝ) : sig p q r = -sig p r q := by
  simp only [sig]; ring

lemma sig_reverse (p q x : ℝ × ℝ) : sig q p x = -sig p q x := by
  simp only [sig]; ring

lemma sig_self_left (p r : ℝ × ℝ) : sig p p r = 0 := by
  simp only [sig]; ring

lemma sig_self_right (p q : ℝ × ℝ) : sig p q q = 0 := by
  simp only [sig]; ring

/-- `sig` is affine in its first argument. -/
lemma sig_affine_fst (a b c q r : ℝ × ℝ) (x y z : ℝ) (hxyz : x + y + z = 1) :
    sig (x • a + y • b + z • c) q r
      = x * sig a q r + y * sig b q r + z * sig c q r := by
  have hz : z = 1 - x - y := by linarith
  subst hz
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  ring

/-- `sig` is affine in its third argument. -/
lemma sig_affine_third (p q a b c : ℝ × ℝ) (x y z : ℝ) (hxyz : x + y + z = 1) :
    sig p q (x • a + y • b + z • c) =
      x * sig p q a + y * sig p q b + z * sig p q c := by
  rw [← sig_rotate (x • a + y • b + z • c) p q,
    sig_affine_fst a b c p q x y z hxyz,
    sig_rotate a p q, sig_rotate b p q, sig_rotate c p q]

lemma sig_affine_third_two (p q a b : ℝ × ℝ) (x y : ℝ) (hxy : x + y = 1) :
    sig p q (x • a + y • b) = x * sig p q a + y * sig p q b := by
  have h := sig_affine_third p q a b b x y 0 (by linarith)
  simpa using h

/-- The cocycle identity for four points. -/
lemma cocycle (p q r s : ℝ × ℝ) :
    sig q r s - sig p r s + sig p q s - sig p q r = 0 := by
  simp only [sig]; ring

/-- A point is pinned by its two doubled areas against a nondegenerate frame:
if `sig A B E ≠ 0`, the pair `(sig A B X, sig A X E)` determines `X`. Both are
affine functionals of `X - A`, and their Jacobian determinant is `sig A B E`. -/
lemma point_unique_of_sigs (A B E X Y : ℝ × ℝ) (hne : sig A B E ≠ 0)
    (h1 : sig A B X = sig A B Y) (h2 : sig A X E = sig A Y E) : X = Y := by
  have hd1 : (X.1 - Y.1) * sig A B E = 0 := by
    simp only [sig] at h1 h2 ⊢
    linear_combination (E.1 - A.1) * h1 + (B.1 - A.1) * h2
  have hd2 : (X.2 - Y.2) * sig A B E = 0 := by
    simp only [sig] at h1 h2 ⊢
    linear_combination (E.2 - A.2) * h1 + (B.2 - A.2) * h2
  have e1 : X.1 - Y.1 = 0 := by
    rcases mul_eq_zero.mp hd1 with h | h
    · exact h
    · exact absurd h hne
  have e2 : X.2 - Y.2 = 0 := by
    rcases mul_eq_zero.mp hd2 with h | h
    · exact h
    · exact absurd h hne
  exact Prod.ext_iff.mpr ⟨by linarith, by linarith⟩

/-! ## Barycentric membership -/

/-- Membership in the convex hull of three points, coordinate form. -/
def InTri (p a b c : ℝ × ℝ) : Prop :=
  ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 1 ∧
    p = x • a + y • b + z • c

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

lemma inTri_perm23 (p a b c : ℝ × ℝ) (h : InTri p a b c) : InTri p a c b := by
  obtain ⟨x, y, z, hx, hy, hz, hs, he⟩ := h
  exact ⟨x, z, y, hx, hz, hy, by linarith, by rw [he]; module⟩

lemma inTri_vertexA (a b c : ℝ × ℝ) : InTri a a b c :=
  ⟨1, 0, 0, by norm_num, le_refl 0, le_refl 0, by norm_num, by simp⟩

lemma inTri_vertexB (a b c : ℝ × ℝ) : InTri b a b c :=
  ⟨0, 1, 0, le_refl 0, by norm_num, le_refl 0, by norm_num, by simp⟩

lemma inTri_vertexC (a b c : ℝ × ℝ) : InTri c a b c :=
  ⟨0, 0, 1, le_refl 0, le_refl 0, by norm_num, by norm_num, by simp⟩

lemma sig_nonneg_on_convexHull (p q : ℝ × ℝ) (s : Set (ℝ × ℝ))
    (h : ∀ x ∈ s, 0 ≤ sig p q x) :
    ∀ x ∈ convexHull ℝ s, 0 ≤ sig p q x := by
  apply convexHull_min h
  rintro x hx y hy u v hu hv huv
  change 0 ≤ sig p q x at hx
  change 0 ≤ sig p q y at hy
  change 0 ≤ sig p q (u • x + v • y)
  rw [sig_affine_third_two p q x y u v huv]
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)

/-- Orientation description of a nondegenerate triangle. -/
theorem mem_triangle_iff_orientations (x a b c : ℝ × ℝ) (habc : 0 < sig a b c) :
    x ∈ convexHull ℝ {a, b, c} ↔
      0 ≤ sig a b x ∧ 0 ≤ sig b c x ∧ 0 ≤ sig c a x := by
  rw [← inTri_iff_mem_convexHull]
  constructor
  · rintro ⟨u, v, t, hu, hv, ht, huv, rfl⟩
    have h₁ := sig_affine_third a b a b c u v t huv
    have h₂ := sig_affine_third b c a b c u v t huv
    have h₃ := sig_affine_third c a a b c u v t huv
    have h₁' : sig a b (u • a + v • b + t • c) = t * sig a b c := by
      rw [h₁]; simp [sig]
    have h₂' : sig b c (u • a + v • b + t • c) = u * sig a b c := by
      rw [h₂]
      have hcyc : sig b c a = sig a b c := by simp only [sig]; ring
      rw [hcyc]; simp [sig]
    have h₃' : sig c a (u • a + v • b + t • c) = v * sig a b c := by
      rw [h₃]
      have hcyc : sig c a b = sig a b c := by simp only [sig]; ring
      rw [hcyc]; simp [sig]
    rw [h₁', h₂', h₃']
    exact ⟨mul_nonneg ht habc.le, mul_nonneg hu habc.le, mul_nonneg hv habc.le⟩
  · rintro ⟨h₁, h₂, h₃⟩
    let D := sig a b c
    refine ⟨sig b c x / D, sig c a x / D, sig a b x / D,
      div_nonneg h₂ habc.le, div_nonneg h₃ habc.le,
      div_nonneg h₁ habc.le, ?_, ?_⟩
    · dsimp [D]
      field_simp [habc.ne']
      simp only [sig]
      ring
    · dsimp [D]
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
        Prod.snd_add, smul_eq_mul]
      · field_simp [habc.ne']
        simp only [sig]
        ring
      · field_simp [habc.ne']
        simp only [sig]
        ring

/-- Barycentric criterion for membership in a positively oriented triangle. -/
lemma inTri_of_sig (x A B C : ℝ × ℝ) (hD : 0 < sig A B C)
    (h1 : 0 ≤ sig x B C) (h2 : 0 ≤ sig A x C) (h3 : 0 ≤ sig A B x) :
    InTri x A B C := by
  have hDne : sig A B C ≠ 0 := ne_of_gt hD
  have hsum : sig x B C + sig A x C + sig A B x = sig A B C := by
    simp only [sig]; ring
  refine ⟨sig x B C / sig A B C, sig A x C / sig A B C, sig A B x / sig A B C,
    div_nonneg h1 hD.le, div_nonneg h2 hD.le, div_nonneg h3 hD.le, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hDne]
  · have hx1 : x.1 * sig A B C
        = sig x B C * A.1 + sig A x C * B.1 + sig A B x * C.1 := by
      simp only [sig]; ring
    have hx2 : x.2 * sig A B C
        = sig x B C * A.2 + sig A x C * B.2 + sig A B x * C.2 := by
      simp only [sig]; ring
    have hxx : x = (x.1, x.2) := rfl
    rw [hxx, Prod.ext_iff]
    constructor
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linarith [hx1]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith [hx2]

/-- Mirror of `inTri_of_sig` for negatively oriented `A B C`. -/
lemma inTri_of_sig_neg (x A B C : ℝ × ℝ) (hD : sig A B C < 0)
    (h1 : sig x B C ≤ 0) (h2 : sig A x C ≤ 0) (h3 : sig A B x ≤ 0) :
    InTri x A B C := by
  have hD' : 0 < sig A C B := by rw [sig_swap A C B]; linarith
  have h1' : 0 ≤ sig x C B := by rw [sig_swap x C B]; linarith
  have h2' : 0 ≤ sig A x B := by rw [sig_swap A x B]; linarith
  have h3' : 0 ≤ sig A C x := by rw [sig_swap A C x]; linarith
  obtain ⟨a, b, c, ha, hb, hc, hsum, hx⟩ := inTri_of_sig x A C B hD' h1' h2' h3'
  exact ⟨a, c, b, ha, hc, hb, by linarith, by rw [hx]; module⟩

/-! ## The standard triangle and the triangle volume formula -/

private def standardTriangle : Set (ℝ × ℝ) :=
  convexHull ℝ
    {((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))}

private lemma mem_standardTriangle_iff (p : ℝ × ℝ) :
    p ∈ standardTriangle ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [standardTriangle, ← inTri_iff_mem_convexHull]
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hsum, hp⟩
    have hfst : p.1 = y := by rw [hp]; simp
    have hsnd : p.2 = z := by rw [hp]; simp
    refine ⟨by simpa [hfst] using hy, by simpa [hsnd] using hz, ?_⟩
    rw [hfst, hsnd]; linarith
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨1 - p.1 - p.2, p.1, p.2, by linarith, hx, hy, by ring, ?_⟩
    ext <;> simp

private def reflectPoint (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.1, 1 - p.2)

private def upperTriangle : Set (ℝ × ℝ) := reflectPoint '' standardTriangle

private lemma mem_upperTriangle_iff (p : ℝ × ℝ) :
    p ∈ upperTriangle ↔ p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1 + p.2 := by
  rw [upperTriangle]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_standardTriangle_iff] at hq
    dsimp [reflectPoint]
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨reflectPoint p, ?_, ?_⟩
    · rw [mem_standardTriangle_iff]
      dsimp [reflectPoint]
      refine ⟨by linarith, by linarith, by linarith⟩
    · ext <;> simp [reflectPoint]

private lemma standard_union_upper :
    standardTriangle ∪ upperTriangle =
      Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ)) := by
  ext p
  rw [Set.mem_union, mem_standardTriangle_iff, mem_upperTriangle_iff]
  simp only [Set.mem_Icc, Prod.le_def]
  constructor
  · rintro (h | h)
    · exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨hx0, hy0⟩, hx1, hy1⟩
    by_cases h : p.1 + p.2 ≤ 1
    · exact Or.inl ⟨hx0, hy0, h⟩
    · exact Or.inr ⟨hx1, hy1, le_of_not_ge h⟩

private noncomputable def diagonalLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(1 : ℝ), 0; -1, 0]

private def diagonalAffine : Set (ℝ × ℝ) :=
  (fun x => ((0 : ℝ), (1 : ℝ)) + x) '' (diagonalLinear '' Set.univ)

private lemma volume_diagonalLinear_range :
    volume (diagonalLinear '' Set.univ) = 0 := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap]
  simp [diagonalLinear, Matrix.det_fin_two]

private lemma volume_diagonalAffine : volume diagonalAffine = 0 := by
  rw [diagonalAffine, Set.image_add_left, MeasureTheory.measure_preimage_add]
  exact volume_diagonalLinear_range

private lemma standard_inter_upper_subset_diagonalAffine :
    standardTriangle ∩ upperTriangle ⊆ diagonalAffine := by
  intro p hp
  rw [Set.mem_inter_iff, mem_standardTriangle_iff, mem_upperTriangle_iff] at hp
  have hsum : p.1 + p.2 = 1 := le_antisymm hp.1.2.2 hp.2.2.2
  refine ⟨diagonalLinear (p.1, 0), ⟨(p.1, 0), Set.mem_univ _, rfl⟩, ?_⟩
  rw [diagonalLinear, Matrix.toLin_finTwoProd_apply]
  ext
  · simp
  · dsimp
    linarith

private lemma volume_standard_inter_upper :
    volume (standardTriangle ∩ upperTriangle) = 0 :=
  MeasureTheory.measure_mono_null
    standard_inter_upper_subset_diagonalAffine volume_diagonalAffine

private noncomputable def negLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(-1 : ℝ), 0; 0, -1]

private lemma upperTriangle_eq_translate :
    upperTriangle =
      (fun y => ((1 : ℝ), (1 : ℝ)) + y) '' (negLinear '' standardTriangle) := by
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
    volume upperTriangle = volume standardTriangle := by
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
    volume (Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ))) = 1 := by
  have hsquare :
      Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ)) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Prod.le_def]
  rw [hsquare, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Measure.prod_prod]
  norm_num

private theorem volume_standardTriangle :
    volume standardTriangle = ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := MeasureTheory.measure_union_add_inter
    (μ := MeasureTheory.volume) standardTriangle measurableSet_upperTriangle
  rw [standard_union_upper, volume_unitSquare,
    volume_standard_inter_upper, volume_upper_eq_standard] at h
  have hdouble : volume standardTriangle + volume standardTriangle = 1 := by
    simpa using h.symm
  calc
    volume standardTriangle = (1 : ENNReal) / 2 := by
      apply (ENNReal.eq_div_iff (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)).2
      simpa [two_mul] using hdouble
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

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
    refine ⟨1 - r.1 - r.2, r.1, r.2, by linarith, hr.1, hr.2.1, by ring, ?_⟩
    rw [triangleLinear, Matrix.toLin_finTwoProd_apply]
    ext <;> dsimp <;> ring

/-- **Triangle volume**: the Lebesgue area of a triangle is half the absolute
doubled signed area. -/
theorem volume_triangle (a b c : ℝ × ℝ) :
    volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (|sig a b c| / 2) := by
  rw [convexHull_triple_eq_affine_image, Set.image_add_left,
    MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap,
    det_triangleLinear, volume_standardTriangle,
    ← ENNReal.ofReal_mul (abs_nonneg (sig a b c))]
  congr 1
  ring

theorem volumeReal_triangle (a b c : ℝ × ℝ) :
    (volume (convexHull ℝ {a, b, c})).toReal = |sig a b c| / 2 := by
  rw [volume_triangle, ENNReal.toReal_ofReal]
  positivity

theorem volume_triangle_eq_zero_iff (a b c : ℝ × ℝ) :
    volume (convexHull ℝ {a, b, c}) = 0 ↔ sig a b c = 0 := by
  rw [volume_triangle, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have habs : |sig a b c| = 0 := by nlinarith [abs_nonneg (sig a b c)]
    exact abs_eq_zero.mp habs
  · rintro h
    simp [h]

theorem volume_segment_eq_zero (p q : ℝ × ℝ) : volume (segment ℝ p q) = 0 := by
  rw [← convexHull_pair]
  simpa [sig] using volume_triangle p q q

/-! ## Enumeration of ordered index triples -/

lemma triple_cases3 (i j k : Fin 3) (hij : i < j) (hjk : j < k) :
    i = 0 ∧ j = 1 ∧ k = 2 := by
  revert i j k
  decide

lemma triple_cases4 (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3) := by
  revert i j k
  decide

lemma triple_cases5 (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 1 ∧ k = 4) ∨ (i = 0 ∧ j = 2 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 4) ∨ (i = 0 ∧ j = 3 ∧ k = 4) ∨
      (i = 1 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 4) ∨
      (i = 1 ∧ j = 3 ∧ k = 4) ∨ (i = 2 ∧ j = 3 ∧ k = 4) := by
  revert i j k
  decide

/-! ## Ranges of small tuples -/

lemma range_fin3 (p : Fin 3 → ℝ × ℝ) : Set.range p = {p 0, p 1, p 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

lemma range_fin4 (p : Fin 4 → ℝ × ℝ) : Set.range p = {p 0, p 1, p 2, p 3} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

lemma range_fin5 (p : Fin 5 → ℝ × ℝ) :
    Set.range p = {p 0, p 1, p 2, p 3, p 4} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩

/-! ## Volume of the hull of a finite configuration -/

/-- The doubled Lebesgue area of the convex hull of a configuration. -/
noncomputable def doubledHullArea {n : ℕ} (v : Fin n → ℝ × ℝ) : ℝ :=
  2 * (volume (convexHull ℝ (Set.range v))).toReal

lemma isCompact_convexHull_range {n : ℕ} (v : Fin n → ℝ × ℝ) :
    IsCompact (convexHull ℝ (Set.range v)) :=
  Set.finite_range v |>.isCompact_convexHull ℝ

lemma volume_convexHull_range_ne_top {n : ℕ} (v : Fin n → ℝ × ℝ) :
    volume (convexHull ℝ (Set.range v)) ≠ ⊤ :=
  (isCompact_convexHull_range v).measure_ne_top

lemma doubledHullArea_nonneg {n : ℕ} (v : Fin n → ℝ × ℝ) :
    0 ≤ doubledHullArea v :=
  mul_nonneg (by norm_num) ENNReal.toReal_nonneg

/-- Unit Lebesgue hull area means doubled hull area 2.

This is bookkeeping, not the shoelace-to-measure bridge: `doubledHullArea` is
*defined* as `2 * (volume …).toReal`, so the proof is `simp`. The real content,
turning a Lebesgue measure into a signed-area polynomial, is
`volume_triangle` together with `volume_convexHull_eq_sum_fan` and the
`volume_convexHull_strictCCW3/4/5` corollaries. -/
theorem doubledHullArea_of_unit_volume {n : ℕ} {v : Fin n → ℝ × ℝ}
    (hvolume : volume (convexHull ℝ (Set.range v)) = 1) :
    doubledHullArea v = 2 := by
  simp [doubledHullArea, hvolume]

/-- Every triangle spanned by the configuration sits inside the hull. -/
theorem abs_sig_le_doubledHullArea {n : ℕ} (v : Fin n → ℝ × ℝ) (i j k : Fin n) :
    |sig (v i) (v j) (v k)| ≤ doubledHullArea v := by
  have hsubset :
      convexHull ℝ {v i, v j, v k} ⊆ convexHull ℝ (Set.range v) := by
    apply convexHull_mono
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_range]
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩⟩
  have hmeasure :=
    MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsubset
  have hreal := ENNReal.toReal_mono (volume_convexHull_range_ne_top v) hmeasure
  rw [volume_triangle,
    ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (by norm_num))] at hreal
  rw [doubledHullArea]
  linarith

/-! ## Orientation-preserving affine images -/

/-- Coefficient form of an affine map of the plane. -/
def affMap (a b c d e f : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f)

private noncomputable def affLinear (a b c d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![a, b; c, d]

private lemma affLinear_apply (a b c d : ℝ) (p : ℝ × ℝ) :
    affLinear a b c d p = (a * p.1 + b * p.2, c * p.1 + d * p.2) := by
  rw [affLinear, Matrix.toLin_finTwoProd_apply]

private lemma det_affLinear (a b c d : ℝ) :
    LinearMap.det (affLinear a b c d) = a * d - b * c := by
  simp [affLinear, Matrix.det_fin_two]

private noncomputable def affAffine (a b c d e f : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  (affLinear a b c d).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) (e, f)

private lemma affAffine_apply (a b c d e f : ℝ) (p : ℝ × ℝ) :
    affAffine a b c d e f p = affMap a b c d e f p := by
  simp [affAffine, affLinear_apply, affMap]

private lemma affAffine_image_eq (a b c d e f : ℝ) (s : Set (ℝ × ℝ)) :
    affAffine a b c d e f '' s = (fun x => (e, f) + x) '' (affLinear a b c d '' s) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨affLinear a b c d q, ⟨q, hq, rfl⟩, ?_⟩
    rw [affAffine_apply, affMap, affLinear_apply]
    ext <;> dsimp <;> ring
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨r, hr, ?_⟩
    rw [affAffine_apply, affMap, affLinear_apply]
    ext <;> dsimp <;> ring

/-- Volume scaling under an arbitrary affine map.  The absolute value makes
the statement independent of orientation. -/
theorem volume_image_affMap_abs (a b c d e f : ℝ)
    (s : Set (ℝ × ℝ)) :
    volume (affMap a b c d e f '' s) =
      ENNReal.ofReal |a * d - b * c| * volume s := by
  have himg : affMap a b c d e f '' s = affAffine a b c d e f '' s := by
    apply Set.image_congr'
    intro x
    exact (affAffine_apply a b c d e f x).symm
  rw [himg, affAffine_image_eq, Set.image_add_left,
    MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap, det_affLinear]

/-- Volume of the convex hull after an arbitrary affine map. -/
theorem volume_convexHull_image_affMap_abs (a b c d e f : ℝ)
    (s : Set (ℝ × ℝ)) :
    volume (convexHull ℝ (affMap a b c d e f '' s)) =
      ENNReal.ofReal |a * d - b * c| *
        volume (convexHull ℝ s) := by
  have himg : ∀ t : Set (ℝ × ℝ),
      affMap a b c d e f '' t = affAffine a b c d e f '' t := by
    intro t
    apply Set.image_congr'
    intro x
    exact (affAffine_apply a b c d e f x).symm
  rw [himg, ← (affAffine a b c d e f).image_convexHull, ← himg,
    volume_image_affMap_abs]

/-- Volume scaling under an orientation-preserving affine map. -/
theorem volume_image_affMap (a b c d e f : ℝ) (hdet : 0 < a * d - b * c)
    (s : Set (ℝ × ℝ)) :
    volume (affMap a b c d e f '' s) = ENNReal.ofReal (a * d - b * c) * volume s := by
  have himg : affMap a b c d e f '' s = affAffine a b c d e f '' s := by
    apply Set.image_congr'
    intro x
    exact (affAffine_apply a b c d e f x).symm
  rw [himg, affAffine_image_eq, Set.image_add_left,
    MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap, det_affLinear,
    abs_of_pos hdet]

/-- Volume of the hull of an affinely transformed configuration. -/
theorem volume_convexHull_image_affMap (a b c d e f : ℝ) (hdet : 0 < a * d - b * c)
    (s : Set (ℝ × ℝ)) :
    volume (convexHull ℝ (affMap a b c d e f '' s)) =
      ENNReal.ofReal (a * d - b * c) * volume (convexHull ℝ s) := by
  have himg : ∀ t : Set (ℝ × ℝ), affMap a b c d e f '' t = affAffine a b c d e f '' t := by
    intro t
    apply Set.image_congr'
    intro x
    exact (affAffine_apply a b c d e f x).symm
  rw [himg, ← (affAffine a b c d e f).image_convexHull, ← himg,
    volume_image_affMap a b c d e f hdet]

/-- `sig` scales by the determinant under an affine map. -/
theorem sig_affMap (a b c d e f : ℝ) (p q r : ℝ × ℝ) :
    sig (affMap a b c d e f p) (affMap a b c d e f q) (affMap a b c d e f r) =
      (a * d - b * c) * sig p q r := by
  simp only [sig, affMap]
  ring

lemma range_affMap {n : ℕ} (a b c d e f : ℝ) (v : Fin n → ℝ × ℝ) :
    Set.range (fun i => affMap a b c d e f (v i)) = affMap a b c d e f '' Set.range v := by
  ext x
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-! ## Fan decomposition -/

/-- **The bridge lemma.** A finite family of fan triangles has volume equal to
the sum of its triangle volumes when it covers the hull and is pairwise a.e.
disjoint.

This is where a Lebesgue measure becomes a signed-area polynomial: combined
with `volume_triangle` it turns `volume (convexHull ℝ (Set.range p)) = 1` into a
shoelace identity on the coordinates of `p`. Callers normally use the packaged
corollaries `volume_convexHull_strictCCW3/4/5`, or the raw-point wrappers
`volume_convexHull_triangle_pos`, `volume_convexHull_quad` and
`volume_convexHull_pent`. -/
theorem volume_convexHull_eq_sum_fan {ι : Type*} [Fintype ι]
    (s : Set (ℝ × ℝ)) (p : ℝ × ℝ) (a b : ι → ℝ × ℝ)
    (hunion : convexHull ℝ s = ⋃ i : ι, convexHull ℝ {p, a i, b i})
    (hpair : ∀ ⦃i j : ι⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {p, a i, b i}) (convexHull ℝ {p, a j, b j})) :
    volume (convexHull ℝ s) =
      ∑ i : ι, ENNReal.ofReal (|sig p (a i) (b i)| / 2) := by
  rw [hunion, MeasureTheory.measure_iUnion₀ hpair]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro i _
    exact volume_triangle p (a i) (b i)
  · intro i
    exact (convex_convexHull ℝ _).nullMeasurableSet MeasureTheory.volume

private lemma adjacent_inter_subset_segment (p a b c : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) :
    convexHull ℝ {p, a, b} ∩ convexHull ℝ {p, b, c} ⊆ segment ℝ p b := by
  intro x hx
  have hleft := (mem_triangle_iff_orientations x p a b hpab).1 hx.1
  have hright := (mem_triangle_iff_orientations x p b c hpbc).1 hx.2
  have hrev := sig_reverse b p x
  have hzero : sig p b x = 0 := by nlinarith [hleft.2.2, hright.1]
  have hxright : InTri x p b c := (inTri_iff_mem_convexHull x p b c).2 hx.2
  rcases hxright with ⟨u, v, t, hu, hv, ht, huv, hxe⟩
  have hsig : sig p b x = t * sig p b c := by
    rw [hxe, sig_affine_third p b p b c u v t huv]
    simp [sig]
  have htzero : t = 0 := by nlinarith
  have hin : InTri x p b b := by
    refine ⟨u, v, 0, hu, hv, by positivity, by linarith, ?_⟩
    simpa [htzero] using hxe
  rw [← convexHull_pair]
  have hconv := (inTri_iff_mem_convexHull x p b b).1 hin
  simpa using hconv

private lemma separated_inter_subset_singleton (p a b c d : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) (hpbd : 0 < sig p b d) :
    convexHull ℝ {p, a, b} ∩ convexHull ℝ {p, c, d} ⊆ {p} := by
  intro x hx
  have hleft := (mem_triangle_iff_orientations x p a b hpab).1 hx.1
  have hrev := sig_reverse b p x
  have hxright : InTri x p c d := (inTri_iff_mem_convexHull x p c d).2 hx.2
  rcases hxright with ⟨u, v, t, hu, hv, ht, huv, hxe⟩
  have hsig : sig p b x = v * sig p b c + t * sig p b d := by
    rw [hxe, sig_affine_third p b p c d u v t huv]
    simp [sig]
  have hvzero : v = 0 := by nlinarith
  have htzero : t = 0 := by nlinarith
  have huone : u = 1 := by linarith
  rw [Set.mem_singleton_iff, hxe, hvzero, htzero, huone]
  module

theorem adjacent_triangles_aeDisjoint (p a b c : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {p, a, b}) (convexHull ℝ {p, b, c}) :=
  MeasureTheory.measure_mono_null
    (adjacent_inter_subset_segment p a b c hpab hpbc)
    (volume_segment_eq_zero p b)

private lemma volume_singleton_eq_zero (p : ℝ × ℝ) :
    MeasureTheory.volume ({p} : Set (ℝ × ℝ)) = 0 := by
  have h : ({p} : Set (ℝ × ℝ)) ⊆ segment ℝ p p := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact left_mem_segment ℝ p p
  exact MeasureTheory.measure_mono_null h (volume_segment_eq_zero p p)

theorem separated_triangles_aeDisjoint (p a b c d : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) (hpbd : 0 < sig p b d) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {p, a, b}) (convexHull ℝ {p, c, d}) :=
  MeasureTheory.measure_mono_null
    (separated_inter_subset_singleton p a b c d hpab hpbc hpbd)
    (volume_singleton_eq_zero p)

/-- Consecutive edges of a strictly convex cycle are supporting lines. -/
lemma strictCCW_consecutive_halfplane {n : ℕ} (pts : Fin n → ℝ × ℝ)
    (hpos : ∀ i j k : Fin n, i < j → j < k → 0 < sig (pts i) (pts j) (pts k))
    (i j : Fin n) (hij : i.val + 1 = j.val) :
    ∀ k : Fin n, 0 ≤ sig (pts i) (pts j) (pts k) := by
  intro k
  have hij' : i < j := by omega
  by_cases hki : k < i
  · rw [← sig_rotate (pts k) (pts i) (pts j)]
    exact (hpos k i j hki hij').le
  by_cases hki' : k = i
  · subst k
    simp [sig]
  by_cases hkj : k = j
  · subst k
    simp [sig]
  have hjk : j < k := by omega
  exact (hpos i j k hij' hjk).le

/-- The closing edge of a strictly convex cycle is a supporting line. -/
lemma strictCCW_closing_halfplane {n : ℕ} (pts : Fin n → ℝ × ℝ)
    (hpos : ∀ i j k : Fin n, i < j → j < k → 0 < sig (pts i) (pts j) (pts k))
    (z l : Fin n) (hz : z.val = 0) (hl : ∀ k : Fin n, k ≤ l)
    (_hzl : z < l) :
    ∀ k : Fin n, 0 ≤ sig (pts l) (pts z) (pts k) := by
  intro k
  by_cases hkz : k = z
  · subst k
    simp [sig]
  by_cases hkl : k = l
  · subst k
    simp [sig]
  have hzk : z < k := by
    have hzle : z ≤ k := by
      rw [Fin.le_def, hz]
      exact Nat.zero_le _
    exact lt_of_le_of_ne hzle (fun hh => hkz hh.symm)
  have hkl' : k < l := lt_of_le_of_ne (hl k) hkl
  calc
    (0 : ℝ) ≤ sig (pts z) (pts k) (pts l) := (hpos z k l hzk hkl').le
    _ = sig (pts l) (pts z) (pts k) := by
      rw [sig_rotate (pts z) (pts k) (pts l), sig_rotate (pts k) (pts l) (pts z)]

/-! ### Triangles -/

theorem volume_convexHull_strictCCW3 (pts : Fin 3 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 3, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal (sig (pts 0) (pts 1) (pts 2) / 2) := by
  have hr : Set.range pts = {pts 0, pts 1, pts 2} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [hr, volume_triangle,
    abs_of_pos (hpos 0 1 2 (by decide) (by decide))]

/-! ### Quadrilaterals -/

private def fanLeft4 (pts : Fin 4 → ℝ × ℝ) : Fin 2 → ℝ × ℝ := ![pts 1, pts 2]
private def fanRight4 (pts : Fin 4 → ℝ × ℝ) : Fin 2 → ℝ × ℝ := ![pts 2, pts 3]

private lemma strictCCW4_fan_decomposition (pts : Fin 4 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 4, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 2, convexHull ℝ {pts 0, fanLeft4 pts i, fanRight4 pts i} := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 := strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 := strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 := strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h30 := strictCCW_closing_halfplane pts hpos 0 3 (by decide)
      (by decide) (by decide)
    have h01x := sig_nonneg_on_convexHull (pts 0) (pts 1) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := sig_nonneg_on_convexHull (pts 1) (pts 2) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := sig_nonneg_on_convexHull (pts 2) (pts 3) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h30x := sig_nonneg_on_convexHull (pts 3) (pts 0) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h30 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      exact (mem_triangle_iff_orientations x _ _ _ hp023).2
        ⟨le_of_not_ge h02, h23x, h30x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    apply (convexHull_mono
      (s := {pts 0, fanLeft4 pts i, fanRight4 pts i})
      (t := Set.range pts) ?_) hi
    fin_cases i
    all_goals
      rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    · exact ⟨⟨0, rfl⟩, ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩⟩

private lemma strictCCW4_fan_pairwise (pts : Fin 4 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 4, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    ∀ ⦃i j : Fin 2⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft4 pts i, fanRight4 pts i})
        (convexHull ℝ {pts 0, fanLeft4 pts j, fanRight4 pts j}) := by
  have haux : ∀ {i j : Fin 2}, i < j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft4 pts i, fanRight4 pts i})
        (convexHull ℝ {pts 0, fanLeft4 pts j, fanRight4 pts j}) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp only [Fin.mk_lt_mk] at hij
    all_goals try omega
    exact adjacent_triangles_aeDisjoint (pts 0) (pts 1) (pts 2) (pts 3)
      (hpos 0 1 2 (by decide) (by decide))
      (hpos 0 2 3 (by decide) (by decide))
  intro i j hij
  by_cases hlt : i < j
  · exact haux hlt
  · exact (haux (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm

/-- Two-triangle fan formula for a strictly convex quadrilateral. -/
theorem volume_convexHull_strictCCW4 (pts : Fin 4 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 4, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal
        ((sig (pts 0) (pts 1) (pts 2) + sig (pts 0) (pts 2) (pts 3)) / 2) := by
  have h012 := hpos 0 1 2 (by decide) (by decide)
  have h023 := hpos 0 2 3 (by decide) (by decide)
  rw [volume_convexHull_eq_sum_fan (Set.range pts) (pts 0)
    (fanLeft4 pts) (fanRight4 pts)
    (strictCCW4_fan_decomposition pts hpos) (strictCCW4_fan_pairwise pts hpos)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Fin.sum_univ_two]
  change |sig (pts 0) (pts 1) (pts 2)| / 2 + |sig (pts 0) (pts 2) (pts 3)| / 2 = _
  rw [abs_of_pos h012, abs_of_pos h023]
  ring

/-! ### Pentagons -/

private def fanLeft5 (pts : Fin 5 → ℝ × ℝ) : Fin 3 → ℝ × ℝ :=
  ![pts 1, pts 2, pts 3]
private def fanRight5 (pts : Fin 5 → ℝ × ℝ) : Fin 3 → ℝ × ℝ :=
  ![pts 2, pts 3, pts 4]

private lemma strictCCW5_fan_decomposition (pts : Fin 5 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 5, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 3, convexHull ℝ {pts 0, fanLeft5 pts i, fanRight5 pts i} := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 := strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 := strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 := strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 := strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h40 := strictCCW_closing_halfplane pts hpos 0 4 (by decide)
      (by decide) (by decide)
    have h01x := sig_nonneg_on_convexHull (pts 0) (pts 1) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := sig_nonneg_on_convexHull (pts 1) (pts 2) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := sig_nonneg_on_convexHull (pts 2) (pts 3) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h34x := sig_nonneg_on_convexHull (pts 3) (pts 4) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h34 k) x hx
    have h40x := sig_nonneg_on_convexHull (pts 4) (pts 0) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h40 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
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
    · refine Set.mem_iUnion.2 ⟨2, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 3, pts 4}
      exact (mem_triangle_iff_orientations x _ _ _ hp034).2
        ⟨le_of_not_ge h03, h34x, h40x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    apply (convexHull_mono
      (s := {pts 0, fanLeft5 pts i, fanRight5 pts i})
      (t := Set.range pts) ?_) hi
    fin_cases i
    all_goals
      rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    · exact ⟨⟨0, rfl⟩, ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨3, rfl⟩, ⟨4, rfl⟩⟩⟩

private lemma strictCCW5_fan_pairwise (pts : Fin 5 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 5, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    ∀ ⦃i j : Fin 3⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft5 pts i, fanRight5 pts i})
        (convexHull ℝ {pts 0, fanLeft5 pts j, fanRight5 pts j}) := by
  have haux : ∀ {i j : Fin 3}, i < j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft5 pts i, fanRight5 pts i})
        (convexHull ℝ {pts 0, fanLeft5 pts j, fanRight5 pts j}) := by
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
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 2) (pts 3) (pts 4)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
  intro i j hij
  by_cases hlt : i < j
  · exact haux hlt
  · exact (haux (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm

/-- Three-triangle fan formula for a strictly convex pentagon. -/
theorem volume_convexHull_strictCCW5 (pts : Fin 5 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 5, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal
        ((sig (pts 0) (pts 1) (pts 2) + sig (pts 0) (pts 2) (pts 3)
          + sig (pts 0) (pts 3) (pts 4)) / 2) := by
  have h012 := hpos 0 1 2 (by decide) (by decide)
  have h023 := hpos 0 2 3 (by decide) (by decide)
  have h034 := hpos 0 3 4 (by decide) (by decide)
  rw [volume_convexHull_eq_sum_fan (Set.range pts) (pts 0)
    (fanLeft5 pts) (fanRight5 pts)
    (strictCCW5_fan_decomposition pts hpos) (strictCCW5_fan_pairwise pts hpos)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Fin.sum_univ_three]
  change |sig (pts 0) (pts 1) (pts 2)| / 2 + |sig (pts 0) (pts 2) (pts 3)| / 2
    + |sig (pts 0) (pts 3) (pts 4)| / 2 = _
  rw [abs_of_pos h012, abs_of_pos h023, abs_of_pos h034]
  ring

/-! ### Hexagons -/

private def fanLeft6 (pts : Fin 6 → ℝ × ℝ) : Fin 4 → ℝ × ℝ :=
  ![pts 1, pts 2, pts 3, pts 4]

private def fanRight6 (pts : Fin 6 → ℝ × ℝ) : Fin 4 → ℝ × ℝ :=
  ![pts 2, pts 3, pts 4, pts 5]

private lemma strictCCW6_fan_decomposition (pts : Fin 6 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 6, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 4, convexHull ℝ {pts 0, fanLeft6 pts i, fanRight6 pts i} := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 := strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 := strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 := strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 := strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h45 := strictCCW_consecutive_halfplane pts hpos 4 5 (by decide)
    have h50 := strictCCW_closing_halfplane pts hpos 0 5 (by decide)
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
    have h50x := sig_nonneg_on_convexHull (pts 5) (pts 0) (Set.range pts)
      (by rintro _ ⟨k, rfl⟩; exact h50 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
    have hp045 := hpos 0 4 5 (by decide) (by decide)
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
    · refine Set.mem_iUnion.2 ⟨3, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 4, pts 5}
      exact (mem_triangle_iff_orientations x _ _ _ hp045).2
        ⟨le_of_not_ge h04, h45x, h50x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    apply (convexHull_mono
      (s := {pts 0, fanLeft6 pts i, fanRight6 pts i})
      (t := Set.range pts) ?_) hi
    fin_cases i
    all_goals
      rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    · exact ⟨⟨0, rfl⟩, ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨3, rfl⟩, ⟨4, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨4, rfl⟩, ⟨5, rfl⟩⟩⟩

private lemma strictCCW6_fan_pairwise (pts : Fin 6 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 6, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    ∀ ⦃i j : Fin 4⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft6 pts i, fanRight6 pts i})
        (convexHull ℝ {pts 0, fanLeft6 pts j, fanRight6 pts j}) := by
  have haux : ∀ {i j : Fin 4}, i < j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {pts 0, fanLeft6 pts i, fanRight6 pts i})
        (convexHull ℝ {pts 0, fanLeft6 pts j, fanRight6 pts j}) := by
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
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 2) (pts 3) (pts 4)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint (pts 0) (pts 2) (pts 3) (pts 4) (pts 5)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 3 5 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint (pts 0) (pts 3) (pts 4) (pts 5)
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 4 5 (by decide) (by decide))
  intro i j hij
  by_cases hlt : i < j
  · exact haux hlt
  · exact (haux (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm

/-- Four-triangle fan formula for a strictly convex hexagon. -/
theorem volume_convexHull_strictCCW6 (pts : Fin 6 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 6, i < j → j < k → 0 < sig (pts i) (pts j) (pts k)) :
    volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal
        ((sig (pts 0) (pts 1) (pts 2) + sig (pts 0) (pts 2) (pts 3)
          + sig (pts 0) (pts 3) (pts 4) + sig (pts 0) (pts 4) (pts 5)) / 2) := by
  have h012 := hpos 0 1 2 (by decide) (by decide)
  have h023 := hpos 0 2 3 (by decide) (by decide)
  have h034 := hpos 0 3 4 (by decide) (by decide)
  have h045 := hpos 0 4 5 (by decide) (by decide)
  rw [volume_convexHull_eq_sum_fan (Set.range pts) (pts 0)
    (fanLeft6 pts) (fanRight6 pts)
    (strictCCW6_fan_decomposition pts hpos) (strictCCW6_fan_pairwise pts hpos)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Fin.sum_univ_four]
  change |sig (pts 0) (pts 1) (pts 2)| / 2 + |sig (pts 0) (pts 2) (pts 3)| / 2
    + |sig (pts 0) (pts 3) (pts 4)| / 2 + |sig (pts 0) (pts 4) (pts 5)| / 2 = _
  rw [abs_of_pos h012, abs_of_pos h023, abs_of_pos h034, abs_of_pos h045]
  ring

/-! ### Raw-point restatements of the fan formulas

These avoid making callers reduce `Matrix` notation. -/

theorem volume_convexHull_triangle_pos (a b c : ℝ × ℝ) (h : 0 < sig a b c) :
    volume (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)))
      = ENNReal.ofReal (sig a b c / 2) := by
  rw [volume_triangle, abs_of_pos h]

theorem volume_convexHull_quad (a b c d : ℝ × ℝ)
    (h1 : 0 < sig a b c) (h2 : 0 < sig a b d) (h3 : 0 < sig a c d)
    (h4 : 0 < sig b c d) :
    volume (convexHull ℝ ({a, b, c, d} : Set (ℝ × ℝ)))
      = ENNReal.ofReal ((sig a b c + sig a c d) / 2) := by
  set pts : Fin 4 → ℝ × ℝ := ![a, b, c, d] with hpts
  have e0 : pts 0 = a := by simp [hpts]
  have e1 : pts 1 = b := by simp [hpts]
  have e2 : pts 2 = c := by simp [hpts]
  have e3 : pts 3 = d := by simp [hpts]
  have hstrict : ∀ i j k : Fin 4, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    rcases triple_cases4 i j k hij hjk with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [e0, e1, e2]; exact h1
    · rw [e0, e1, e3]; exact h2
    · rw [e0, e2, e3]; exact h3
    · rw [e1, e2, e3]; exact h4
  have hrange : Set.range pts = ({a, b, c, d} : Set (ℝ × ℝ)) := by
    rw [range_fin4, e0, e1, e2, e3]
  have hfan := volume_convexHull_strictCCW4 pts hstrict
  rw [hrange, e0, e1, e2, e3] at hfan
  exact hfan

theorem volume_convexHull_pent (a b c d e : ℝ × ℝ)
    (h012 : 0 < sig a b c) (h013 : 0 < sig a b d) (h014 : 0 < sig a b e)
    (h023 : 0 < sig a c d) (h024 : 0 < sig a c e) (h034 : 0 < sig a d e)
    (h123 : 0 < sig b c d) (h124 : 0 < sig b c e) (h134 : 0 < sig b d e)
    (h234 : 0 < sig c d e) :
    volume (convexHull ℝ ({a, b, c, d, e} : Set (ℝ × ℝ)))
      = ENNReal.ofReal ((sig a b c + sig a c d + sig a d e) / 2) := by
  set pts : Fin 5 → ℝ × ℝ := ![a, b, c, d, e] with hpts
  have e0 : pts 0 = a := by simp [hpts]
  have e1 : pts 1 = b := by simp [hpts]
  have e2 : pts 2 = c := by simp [hpts]
  have e3 : pts 3 = d := by simp [hpts]
  have e4 : pts 4 = e := by simp [hpts]
  have hstrict : ∀ i j k : Fin 5, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    rcases triple_cases5 i j k hij hjk with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [e0, e1, e2]; exact h012
    · rw [e0, e1, e3]; exact h013
    · rw [e0, e1, e4]; exact h014
    · rw [e0, e2, e3]; exact h023
    · rw [e0, e2, e4]; exact h024
    · rw [e0, e3, e4]; exact h034
    · rw [e1, e2, e3]; exact h123
    · rw [e1, e2, e4]; exact h124
    · rw [e1, e3, e4]; exact h134
    · rw [e2, e3, e4]; exact h234
  have hrange : Set.range pts = ({a, b, c, d, e} : Set (ℝ × ℝ)) := by
    rw [range_fin5, e0, e1, e2, e3, e4]
  have hfan := volume_convexHull_strictCCW5 pts hstrict
  rw [hrange, e0, e1, e2, e3, e4] at hfan
  exact hfan

/-! ## Planar Radon dichotomy for four points -/

/-- The quadrilateral `q0 q1 q2 q3` is convex and CCW (weak form). -/
def QuadCCW (q0 q1 q2 q3 : ℝ × ℝ) : Prop :=
  0 ≤ sig q0 q1 q2 ∧ 0 ≤ sig q0 q1 q3 ∧ 0 ≤ sig q0 q2 q3 ∧ 0 ≤ sig q1 q2 q3

/-- Radon dichotomy for four points in the plane. -/
theorem radon4 (p0 p1 p2 p3 : ℝ × ℝ) :
    (QuadCCW p0 p1 p2 p3 ∨ QuadCCW p0 p1 p3 p2 ∨ QuadCCW p0 p2 p1 p3 ∨
     QuadCCW p0 p3 p2 p1 ∨ QuadCCW p0 p2 p3 p1 ∨ QuadCCW p0 p3 p1 p2) ∨
    (InTri p0 p1 p2 p3 ∨ InTri p1 p0 p2 p3 ∨ InTri p2 p0 p1 p3 ∨
     InTri p3 p0 p1 p2) := by
  have hc := cocycle p0 p1 p2 p3
  have e021 : sig p0 p2 p1 = -sig p0 p1 p2 := by simp only [sig]; ring
  have e031 : sig p0 p3 p1 = -sig p0 p1 p3 := by simp only [sig]; ring
  have e032 : sig p0 p3 p2 = -sig p0 p2 p3 := by simp only [sig]; ring
  have e132 : sig p1 p3 p2 = -sig p1 p2 p3 := by simp only [sig]; ring
  have e213 : sig p2 p1 p3 = -sig p1 p2 p3 := by simp only [sig]; ring
  have e231 : sig p2 p3 p1 = sig p1 p2 p3 := by simp only [sig]; ring
  have e312 : sig p3 p1 p2 = sig p1 p2 p3 := by simp only [sig]; ring
  have e321 : sig p3 p2 p1 = -sig p1 p2 p3 := by simp only [sig]; ring
  have e103 : sig p1 p0 p3 = -sig p0 p1 p3 := by simp only [sig]; ring
  have e120 : sig p1 p2 p0 = sig p0 p1 p2 := by simp only [sig]; ring
  rcases le_or_gt 0 (sig p0 p1 p2) with h1 | h1 <;>
    rcases le_or_gt 0 (sig p0 p1 p3) with h2 | h2 <;>
    rcases le_or_gt 0 (sig p0 p2 p3) with h3 | h3 <;>
    rcases le_or_gt 0 (sig p1 p2 p3) with h4 | h4
  · exact Or.inl (Or.inl ⟨h1, h2, h3, h4⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (inTri_of_sig p2 p0 p1 p3 (by linarith) (by linarith) h3 h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (inTri_of_sig p3 p0 p1 p2 (by linarith) (by linarith) (by linarith) h2))))
  · exact Or.inl (Or.inr (Or.inl ⟨h2, h1, by linarith, by linarith⟩))
  · exact Or.inr (Or.inl
      (inTri_of_sig p0 p1 p2 p3 (by linarith) h3 (by linarith) (by linarith)))
  · exfalso; linarith
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by linarith, by linarith, h1, by linarith⟩)))))
  · exact Or.inr (Or.inr (Or.inl
      (inTri_of_sig_neg p1 p0 p2 p3 h3 h4.le h2.le (by linarith))))
  · exact Or.inr (Or.inr (Or.inl
      (inTri_of_sig p1 p0 p2 p3 (by linarith) h4 h2 (by linarith))))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨by linarith, h3, h2, by linarith⟩)))
  · exfalso; linarith
  · exact Or.inr (Or.inl
      (inTri_of_sig_neg p0 p1 p2 p3 h4 h3.le (by linarith) (by linarith)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h3, by linarith, by linarith, by linarith⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (inTri_of_sig_neg p3 p0 p1 p2 h1 (by linarith) (by linarith) h2.le))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (inTri_of_sig_neg p2 p0 p1 p3 h2 (by linarith) h3.le h1.le))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by linarith, by linarith, by linarith, by linarith⟩))))

/-! ## Hulls that collapse to a smaller face -/

/-- If two extra points lie in the triangle `a b c`, the hull is the triangle. -/
theorem convexHull_eq_triangle_of_inTri (s : Set (ℝ × ℝ)) (a b c : ℝ × ℝ)
    (hs : s ⊆ convexHull ℝ {a, b, c})
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    convexHull ℝ s = convexHull ℝ {a, b, c} := by
  apply Set.Subset.antisymm
  · exact convexHull_min hs (convex_convexHull ℝ _)
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_convexHull ℝ s ha
    · exact subset_convexHull ℝ s hb
    · exact subset_convexHull ℝ s hc

/-! ## Existence of the affine map matching two nondegenerate triangles -/

/-- If `w0 w1 w2` is nondegenerate and `p0 p1 p2` has doubled area of the same
sign, there is an orientation-preserving affine map carrying the first triangle
to the second, vertex by vertex. -/
theorem exists_affMap_triangle (w0 w1 w2 p0 p1 p2 : ℝ × ℝ)
    (hw : sig w0 w1 w2 ≠ 0)
    (hsign : 0 < sig p0 p1 p2 / sig w0 w1 w2) :
    ∃ a b c d e f : ℝ, 0 < a * d - b * c ∧
      affMap a b c d e f w0 = p0 ∧ affMap a b c d e f w1 = p1 ∧
      affMap a b c d e f w2 = p2 := by
  set s := sig w0 w1 w2 with hs
  refine ⟨((p1.1 - p0.1) * (w2.2 - w0.2) - (p2.1 - p0.1) * (w1.2 - w0.2)) / s,
    ((p2.1 - p0.1) * (w1.1 - w0.1) - (p1.1 - p0.1) * (w2.1 - w0.1)) / s,
    ((p1.2 - p0.2) * (w2.2 - w0.2) - (p2.2 - p0.2) * (w1.2 - w0.2)) / s,
    ((p2.2 - p0.2) * (w1.1 - w0.1) - (p1.2 - p0.2) * (w2.1 - w0.1)) / s,
    p0.1 - (((p1.1 - p0.1) * (w2.2 - w0.2)
        - (p2.1 - p0.1) * (w1.2 - w0.2)) / s * w0.1
      + ((p2.1 - p0.1) * (w1.1 - w0.1)
        - (p1.1 - p0.1) * (w2.1 - w0.1)) / s * w0.2),
    p0.2 - (((p1.2 - p0.2) * (w2.2 - w0.2)
        - (p2.2 - p0.2) * (w1.2 - w0.2)) / s * w0.1
      + ((p2.2 - p0.2) * (w1.1 - w0.1)
        - (p1.2 - p0.2) * (w2.1 - w0.1)) / s * w0.2), ?_, ?_, ?_, ?_⟩
  · have hkey :
        ((p1.1 - p0.1) * (w2.2 - w0.2) - (p2.1 - p0.1) * (w1.2 - w0.2)) / s
          * (((p2.2 - p0.2) * (w1.1 - w0.1)
              - (p1.2 - p0.2) * (w2.1 - w0.1)) / s)
        - ((p2.1 - p0.1) * (w1.1 - w0.1) - (p1.1 - p0.1) * (w2.1 - w0.1)) / s
          * (((p1.2 - p0.2) * (w2.2 - w0.2)
              - (p2.2 - p0.2) * (w1.2 - w0.2)) / s)
          = sig p0 p1 p2 / s := by
      rw [div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
        div_eq_div_iff (by exact mul_ne_zero hw hw) hw]
      simp only [hs, sig]
      ring
    rw [hkey]
    exact hsign
  · apply Prod.ext
    · simp only [affMap]
      ring
    · simp only [affMap]
      ring
  · apply Prod.ext
    · simp only [affMap]
      field_simp
      simp only [hs, sig]
      ring
    · simp only [affMap]
      field_simp
      simp only [hs, sig]
      ring
  · apply Prod.ext
    · simp only [affMap]
      field_simp
      simp only [hs, sig]
      ring
    · simp only [affMap]
      field_simp
      simp only [hs, sig]
      ring

/-! ### Interior point counting -/

/-- A triangle containing `s.card` of the points splits into `2 * s.card + 1`
cells, so its doubled area is at least that many times the minimum. -/
theorem interior_count_bound {n : ℕ} (v : Fin n → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |sig (v i) (v j) (v k)|)
    (s : Finset (Fin n)) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (has : a ∉ s) (hbs : b ∉ s) (hcs : c ∉ s)
    (habc : 0 < sig (v a) (v b) (v c))
    (hin : ∀ p ∈ s, InTri (v p) (v a) (v b) (v c)) :
    (2 * s.card + 1) * m ≤ sig (v a) (v b) (v c) := by
  classical
  have count :
      ∀ (N : ℕ) (t : Finset (Fin n)) (A B C : Fin n),
        t.card ≤ N →
        A ≠ B → A ≠ C → B ≠ C →
        A ∉ t → B ∉ t → C ∉ t →
        0 < sig (v A) (v B) (v C) →
        (∀ p ∈ t, InTri (v p) (v A) (v B) (v C)) →
        (2 * t.card + 1) * m ≤ sig (v A) (v B) (v C) := by
    intro N
    induction N with
    | zero =>
        intro t A B C ht_card hAB hAC hBC _ _ _ hpos _
        have ht : t = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero ht_card)
        subst t
        simpa [abs_of_pos hpos] using hmin A B C hAB hAC hBC
    | succ N ih =>
        intro t A B C ht_card hAB hAC hBC hAt hBt hCt hpos ht_in
        by_cases ht_empty : t = ∅
        · subst t
          simpa [abs_of_pos hpos] using hmin A B C hAB hAC hBC
        · obtain ⟨p, hp_mem⟩ := Finset.nonempty_iff_ne_empty.mpr ht_empty
          let t' := t.erase p
          let t1 := t'.filter (fun q => InTri (v q) (v p) (v A) (v B))
          let t2 :=
            (t'.filter (fun q => ¬InTri (v q) (v p) (v A) (v B))).filter
              (fun q => InTri (v q) (v p) (v B) (v C))
          let t3 :=
            (t'.filter (fun q => ¬InTri (v q) (v p) (v A) (v B))).filter
              (fun q => ¬InTri (v q) (v p) (v B) (v C))
          have ht'_card_add : t'.card + 1 = t.card := by
            exact Finset.card_erase_add_one hp_mem
          have ht'_card : t'.card ≤ N := by omega
          have ht'_sub : t' ⊆ t := by
            exact Finset.erase_subset p t
          have ht1_sub : t1 ⊆ t' := by
            exact Finset.filter_subset _ _
          have ht2_sub : t2 ⊆ t' := by
            intro q hq
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
          have ht3_sub : t3 ⊆ t' := by
            intro q hq
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
          have ht1_card : t1.card ≤ N :=
            (Finset.card_le_card ht1_sub).trans ht'_card
          have ht2_card : t2.card ≤ N :=
            (Finset.card_le_card ht2_sub).trans ht'_card
          have ht3_card : t3.card ≤ N :=
            (Finset.card_le_card ht3_sub).trans ht'_card
          have hp_ne_A : p ≠ A := by
            intro h
            exact hAt (h ▸ hp_mem)
          have hp_ne_B : p ≠ B := by
            intro h
            exact hBt (h ▸ hp_mem)
          have hp_ne_C : p ≠ C := by
            intro h
            exact hCt (h ▸ hp_mem)
          have hp_in := ht_in p hp_mem
          have hp_orient :=
            (mem_triangle_iff_orientations (v p) (v A) (v B) (v C) hpos).1
              ((inTri_iff_mem_convexHull (v p) (v A) (v B) (v C)).1 hp_in)
          obtain ⟨hABp, hBCp, hCAp⟩ := hp_orient
          have hpAB_pos : 0 < sig (v p) (v A) (v B) := by
            have hpAB_nonneg : 0 ≤ sig (v p) (v A) (v B) := by
              rwa [sig_rotate]
            rcases eq_or_lt_of_le hpAB_nonneg with hpAB_zero | hpAB_pos
            · have hp_bound := hmin p A B hp_ne_A hp_ne_B hAB
              rw [← hpAB_zero, abs_zero] at hp_bound
              linarith
            · exact hpAB_pos
          have hpBC_pos : 0 < sig (v p) (v B) (v C) := by
            have hpBC_nonneg : 0 ≤ sig (v p) (v B) (v C) := by
              rwa [sig_rotate]
            rcases eq_or_lt_of_le hpBC_nonneg with hpBC_zero | hpBC_pos
            · have hp_bound := hmin p B C hp_ne_B hp_ne_C hBC
              rw [← hpBC_zero, abs_zero] at hp_bound
              linarith
            · exact hpBC_pos
          have hpCA_pos : 0 < sig (v p) (v C) (v A) := by
            have hpCA_nonneg : 0 ≤ sig (v p) (v C) (v A) := by
              rwa [sig_rotate]
            rcases eq_or_lt_of_le hpCA_nonneg with hpCA_zero | hpCA_pos
            · have hp_bound := hmin p C A hp_ne_C hp_ne_A hAC.symm
              rw [← hpCA_zero, abs_zero] at hp_bound
              linarith
            · exact hpCA_pos
          obtain ⟨px, py, pz, hpx, hpy, hpz, hpsum, hp_eq⟩ := hp_in
          have hpAB_coeff : sig (v p) (v A) (v B) = pz * sig (v A) (v B) (v C) := by
            calc
              sig (v p) (v A) (v B) = sig (v A) (v B) (v p) :=
                sig_rotate (v p) (v A) (v B)
              _ = pz * sig (v A) (v B) (v C) := by
                rw [hp_eq, sig_affine_third (v A) (v B) (v A) (v B) (v C)
                  px py pz hpsum]
                simp [sig]
          have hpBC_coeff : sig (v p) (v B) (v C) = px * sig (v A) (v B) (v C) := by
            calc
              sig (v p) (v B) (v C) = sig (v B) (v C) (v p) :=
                sig_rotate (v p) (v B) (v C)
              _ = px * sig (v A) (v B) (v C) := by
                rw [hp_eq, sig_affine_third (v B) (v C) (v A) (v B) (v C)
                  px py pz hpsum]
                simp only [sig]
                ring
          have hpCA_coeff : sig (v p) (v C) (v A) = py * sig (v A) (v B) (v C) := by
            calc
              sig (v p) (v C) (v A) = sig (v C) (v A) (v p) :=
                sig_rotate (v p) (v C) (v A)
              _ = py * sig (v A) (v B) (v C) := by
                rw [hp_eq, sig_affine_third (v C) (v A) (v A) (v B) (v C)
                  px py pz hpsum]
                simp only [sig]
                ring
          have hpx_pos : 0 < px := by
            by_contra h
            have hnonpos : px * sig (v A) (v B) (v C) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hpos.le
            rw [hpBC_coeff] at hpBC_pos
            linarith
          have hpy_pos : 0 < py := by
            by_contra h
            have hnonpos : py * sig (v A) (v B) (v C) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hpos.le
            rw [hpCA_coeff] at hpCA_pos
            linarith
          have hpz_pos : 0 < pz := by
            by_contra h
            have hnonpos : pz * sig (v A) (v B) (v C) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hpos.le
            rw [hpAB_coeff] at hpAB_pos
            linarith
          have fan_partition : ∀ q,
              InTri (v q) (v A) (v B) (v C) →
                InTri (v q) (v p) (v A) (v B) ∨
                InTri (v q) (v p) (v B) (v C) ∨
                InTri (v q) (v p) (v C) (v A) := by
            intro q hq_in
            have hq_orient :=
              (mem_triangle_iff_orientations (v q) (v A) (v B) (v C) hpos).1
                ((inTri_iff_mem_convexHull (v q) (v A) (v B) (v C)).1 hq_in)
            obtain ⟨qx, qy, qz, _, _, _, hqsum, hq_eq⟩ := hq_in
            have hpz_form : pz = 1 - px - py := by linarith
            have hqz_form : qz = 1 - qx - qy := by linarith
            have hpAq : sig (v p) (v A) (v q) =
                (pz * qy - py * qz) * sig (v A) (v B) (v C) := by
              rw [hp_eq, hq_eq, hpz_form, hqz_form]
              simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
                Prod.snd_add, smul_eq_mul]
              ring
            have hpBq : sig (v p) (v B) (v q) =
                (px * qz - pz * qx) * sig (v A) (v B) (v C) := by
              rw [hp_eq, hq_eq, hpz_form, hqz_form]
              simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
                Prod.snd_add, smul_eq_mul]
              ring
            have hpCq : sig (v p) (v C) (v q) =
                (py * qx - px * qy) * sig (v A) (v B) (v C) := by
              rw [hp_eq, hq_eq, hpz_form, hqz_form]
              simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
                Prod.snd_add, smul_eq_mul]
              ring
            let ra := qx / px
            let rb := qy / py
            let rc := qz / pz
            have in_pAB (hca : rc ≤ ra) (hcb : rc ≤ rb) :
                InTri (v q) (v p) (v A) (v B) := by
              have hca_cross : qz * px ≤ qx * pz :=
                (div_le_div_iff₀ hpz_pos hpx_pos).mp (by simpa [rc, ra] using hca)
              have hcb_cross : qz * py ≤ qy * pz :=
                (div_le_div_iff₀ hpz_pos hpy_pos).mp (by simpa [rc, rb] using hcb)
              have hpAq_nonneg : 0 ≤ sig (v p) (v A) (v q) := by
                rw [hpAq]
                refine mul_nonneg ?_ hpos.le
                exact sub_nonneg.mpr
                  (by rw [mul_comm py qz, mul_comm pz qy]; exact hcb_cross)
              have hpBq_nonpos : sig (v p) (v B) (v q) ≤ 0 := by
                rw [hpBq]
                refine mul_nonpos_of_nonpos_of_nonneg ?_ hpos.le
                exact sub_nonpos.mpr
                  (by rw [mul_comm px qz, mul_comm pz qx]; exact hca_cross)
              have hBpQ_nonneg : 0 ≤ sig (v B) (v p) (v q) := by
                rw [sig_reverse]
                exact neg_nonneg.mpr hpBq_nonpos
              apply inTri_of_sig (v q) (v p) (v A) (v B) hpAB_pos
              · rw [sig_rotate]
                exact hq_orient.1
              · rw [← sig_rotate (v B) (v p) (v q)]
                exact hBpQ_nonneg
              · exact hpAq_nonneg
            have in_pBC (habr : ra ≤ rb) (hacr : ra ≤ rc) :
                InTri (v q) (v p) (v B) (v C) := by
              have hab_cross : qx * py ≤ qy * px :=
                (div_le_div_iff₀ hpx_pos hpy_pos).mp (by simpa [ra, rb] using habr)
              have hac_cross : qx * pz ≤ qz * px :=
                (div_le_div_iff₀ hpx_pos hpz_pos).mp (by simpa [ra, rc] using hacr)
              have hpBq_nonneg : 0 ≤ sig (v p) (v B) (v q) := by
                rw [hpBq]
                refine mul_nonneg ?_ hpos.le
                exact sub_nonneg.mpr
                  (by rw [mul_comm pz qx, mul_comm px qz]; exact hac_cross)
              have hpCq_nonpos : sig (v p) (v C) (v q) ≤ 0 := by
                rw [hpCq]
                refine mul_nonpos_of_nonpos_of_nonneg ?_ hpos.le
                exact sub_nonpos.mpr
                  (by rw [mul_comm py qx, mul_comm px qy]; exact hab_cross)
              have hCpQ_nonneg : 0 ≤ sig (v C) (v p) (v q) := by
                rw [sig_reverse]
                exact neg_nonneg.mpr hpCq_nonpos
              apply inTri_of_sig (v q) (v p) (v B) (v C) hpBC_pos
              · rw [sig_rotate]
                exact hq_orient.2.1
              · rw [← sig_rotate (v C) (v p) (v q)]
                exact hCpQ_nonneg
              · exact hpBq_nonneg
            have in_pCA (hba : rb ≤ ra) (hbc : rb ≤ rc) :
                InTri (v q) (v p) (v C) (v A) := by
              have hba_cross : qy * px ≤ qx * py :=
                (div_le_div_iff₀ hpy_pos hpx_pos).mp (by simpa [rb, ra] using hba)
              have hbc_cross : qy * pz ≤ qz * py :=
                (div_le_div_iff₀ hpy_pos hpz_pos).mp (by simpa [rb, rc] using hbc)
              have hpCq_nonneg : 0 ≤ sig (v p) (v C) (v q) := by
                rw [hpCq]
                refine mul_nonneg ?_ hpos.le
                exact sub_nonneg.mpr
                  (by rw [mul_comm px qy, mul_comm py qx]; exact hba_cross)
              have hpAq_nonpos : sig (v p) (v A) (v q) ≤ 0 := by
                rw [hpAq]
                refine mul_nonpos_of_nonpos_of_nonneg ?_ hpos.le
                exact sub_nonpos.mpr
                  (by rw [mul_comm pz qy, mul_comm py qz]; exact hbc_cross)
              have hApQ_nonneg : 0 ≤ sig (v A) (v p) (v q) := by
                rw [sig_reverse]
                exact neg_nonneg.mpr hpAq_nonpos
              apply inTri_of_sig (v q) (v p) (v C) (v A) hpCA_pos
              · rw [sig_rotate]
                exact hq_orient.2.2
              · rw [← sig_rotate (v A) (v p) (v q)]
                exact hApQ_nonneg
              · exact hpCq_nonneg
            by_cases habr : ra ≤ rb
            · by_cases hacr : ra ≤ rc
              · exact Or.inr (Or.inl (in_pBC habr hacr))
              · have hca : rc ≤ ra := le_of_not_ge hacr
                exact Or.inl (in_pAB hca (hca.trans habr))
            · have hba : rb ≤ ra := le_of_not_ge habr
              by_cases hbcr : rb ≤ rc
              · exact Or.inr (Or.inr (in_pCA hba hbcr))
              · have hcb : rc ≤ rb := le_of_not_ge hbcr
                exact Or.inl (in_pAB (hcb.trans hba) hcb)
          have hp_not_t' : p ∉ t' := by
            exact Finset.notMem_erase p t
          have hA_not_t' : A ∉ t' := fun h => hAt (ht'_sub h)
          have hB_not_t' : B ∉ t' := fun h => hBt (ht'_sub h)
          have hC_not_t' : C ∉ t' := fun h => hCt (ht'_sub h)
          have ht1_in : ∀ q ∈ t1, InTri (v q) (v p) (v A) (v B) := by
            intro q hq
            exact (Finset.mem_filter.mp hq).2
          have ht2_in : ∀ q ∈ t2, InTri (v q) (v p) (v B) (v C) := by
            intro q hq
            exact (Finset.mem_filter.mp hq).2
          have ht3_in : ∀ q ∈ t3, InTri (v q) (v p) (v C) (v A) := by
            intro q hq
            have hq_outer := Finset.mem_filter.mp hq
            have hq_inner := Finset.mem_filter.mp hq_outer.1
            have hq_in := ht_in q (ht'_sub hq_inner.1)
            rcases fan_partition q hq_in with h1 | h2 | h3
            · exact (hq_inner.2 h1).elim
            · exact (hq_outer.2 h2).elim
            · exact h3
          have h1 := ih t1 p A B ht1_card hp_ne_A hp_ne_B hAB
            (fun h => hp_not_t' (ht1_sub h))
            (fun h => hA_not_t' (ht1_sub h))
            (fun h => hB_not_t' (ht1_sub h)) hpAB_pos ht1_in
          have h2 := ih t2 p B C ht2_card hp_ne_B hp_ne_C hBC
            (fun h => hp_not_t' (ht2_sub h))
            (fun h => hB_not_t' (ht2_sub h))
            (fun h => hC_not_t' (ht2_sub h)) hpBC_pos ht2_in
          have h3 := ih t3 p C A ht3_card hp_ne_C hp_ne_A hAC.symm
            (fun h => hp_not_t' (ht3_sub h))
            (fun h => hC_not_t' (ht3_sub h))
            (fun h => hA_not_t' (ht3_sub h)) hpCA_pos ht3_in
          have hparts : t1.card + t2.card + t3.card = t'.card := by
            calc
              t1.card + t2.card + t3.card =
                  t1.card + (t2.card + t3.card) := by omega
              _ = t1.card +
                  (t'.filter (fun q => ¬InTri (v q) (v p) (v A) (v B))).card := by
                rw [Finset.card_filter_add_card_filter_not]
              _ = t'.card := by
                exact Finset.card_filter_add_card_filter_not _
          have hcoeff_nat :
              (2 * t1.card + 1) + (2 * t2.card + 1) + (2 * t3.card + 1) =
                2 * t.card + 1 := by
            omega
          have hcoeff :
              ((2 * t.card + 1 : ℕ) : ℝ) =
                ((2 * t1.card + 1 : ℕ) : ℝ) +
                ((2 * t2.card + 1 : ℕ) : ℝ) +
                ((2 * t3.card + 1 : ℕ) : ℝ) := by
            exact_mod_cast hcoeff_nat.symm
          norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcoeff
          calc
            (2 * t.card + 1) * m =
                (2 * t1.card + 1) * m +
                (2 * t2.card + 1) * m +
                (2 * t3.card + 1) * m := by rw [hcoeff]; ring
            _ ≤ sig (v p) (v A) (v B) + sig (v p) (v B) (v C) +
                sig (v p) (v C) (v A) := add_le_add (add_le_add h1 h2) h3
            _ = sig (v A) (v B) (v C) := by
              have hcocycle := cocycle (v p) (v A) (v B) (v C)
              have hswap := sig_swap (v p) (v A) (v C)
              linarith
  exact count s.card s a b c (le_refl _) hab hac hbc has hbs hcs habc hin

end HullBridge
