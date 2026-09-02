import Heilbronn8.CoverGeometry

/-!
# Concrete sixfold reference-triangle quotient

This file formalizes the `gauge_quotient_021`, ..., `gauge_quotient_210`
rows emitted by the pilot.  A permutation of the three barycentric corners
acts by its affine symmetry of the standard reference triangle and by the
inverse relabeling of slots `0,1,2`; the five free labels remain fixed.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

abbrev ReferenceSymmetry := Equiv.Perm (Fin 3)

/-- Embedding of the three fixed reference slots into the eight labels. -/
def referenceSlot : Fin 3 ↪ Fin 8 where
  toFun := Fin.castAdd 5
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) h

@[simp] lemma referenceSlot_zero : referenceSlot 0 = (0 : Fin 8) := by
  apply Fin.ext
  rfl

@[simp] lemma referenceSlot_one : referenceSlot 1 = (1 : Fin 8) := by
  apply Fin.ext
  rfl

@[simp] lemma referenceSlot_two : referenceSlot 2 = (2 : Fin 8) := by
  apply Fin.ext
  rfl

/-- The standard gauge corners in the same order as the machine model. -/
def referenceCorner : Fin 3 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1)]

/-- The affine map taking corner `i` to corner `g i`. -/
def affineCombination
    (p a b c : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - p.1 - p.2) * a.1 + p.1 * b.1 + p.2 * c.1,
   (1 - p.1 - p.2) * a.2 + p.1 * b.2 + p.2 * c.2)

def referenceTransform (g : ReferenceSymmetry) (p : ℝ × ℝ) : ℝ × ℝ :=
  affineCombination p (referenceCorner (g 0))
    (referenceCorner (g 1)) (referenceCorner (g 2))

/-- Linear part of the affine symmetry of the standard triangle. -/
noncomputable def referenceLinear (g : ReferenceSymmetry) :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(referenceCorner (g 1)).1 - (referenceCorner (g 0)).1,
       (referenceCorner (g 2)).1 - (referenceCorner (g 0)).1;
       (referenceCorner (g 1)).2 - (referenceCorner (g 0)).2,
       (referenceCorner (g 2)).2 - (referenceCorner (g 0)).2]

lemma referenceLinear_apply (g : ReferenceSymmetry) (p : ℝ × ℝ) :
    referenceLinear g p =
      (((referenceCorner (g 1)).1 - (referenceCorner (g 0)).1) * p.1 +
        ((referenceCorner (g 2)).1 - (referenceCorner (g 0)).1) * p.2,
       ((referenceCorner (g 1)).2 - (referenceCorner (g 0)).2) * p.1 +
        ((referenceCorner (g 2)).2 - (referenceCorner (g 0)).2) * p.2) := by
  rw [referenceLinear, Matrix.toLin_finTwoProd_apply]

/-- Bundled affine map used to transport convex-hull measure. -/
noncomputable def referenceAffine (g : ReferenceSymmetry) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  (referenceLinear g).toAffineMap +
    AffineMap.const ℝ (ℝ × ℝ) (referenceCorner (g 0))

lemma referenceAffine_apply (g : ReferenceSymmetry) (p : ℝ × ℝ) :
    referenceAffine g p = referenceTransform g p := by
  apply Prod.ext <;>
    simp [referenceAffine, referenceLinear_apply, referenceTransform,
      affineCombination] <;>
    ring

/-- Extend the inverse corner relabeling by fixing the five free slots. -/
noncomputable def referenceRelabel (g : ReferenceSymmetry) :
  Equiv.Perm (Fin 8) :=
  Equiv.Perm.extendDomain (g⁻¹) referenceSlot.toEquivRange

/-- Concrete action on a labelled gauge configuration. -/
noncomputable def referenceAction
    (g : ReferenceSymmetry) (v : Configuration) : Configuration :=
  fun i => referenceTransform g (v (referenceRelabel g i))

lemma referenceTransform_corner (g : ReferenceSymmetry) (i : Fin 3) :
    referenceTransform g (referenceCorner i) = referenceCorner (g i) := by
  fin_cases i <;>
    simp [referenceTransform, affineCombination, referenceCorner]

lemma referenceTransform_one (p : ℝ × ℝ) :
    referenceTransform (1 : ReferenceSymmetry) p = p := by
  apply Prod.ext <;>
    simp [referenceTransform, affineCombination, referenceCorner]

lemma referenceTransform_affineCombination
    (g : ReferenceSymmetry) (p a b c : ℝ × ℝ) :
    referenceTransform g (affineCombination p a b c) =
      affineCombination p (referenceTransform g a)
        (referenceTransform g b) (referenceTransform g c) := by
  apply Prod.ext <;>
    simp only [referenceTransform, affineCombination] <;>
    ring

lemma referenceTransform_mul (g h : ReferenceSymmetry) (p : ℝ × ℝ) :
    referenceTransform (g * h) p =
      referenceTransform g (referenceTransform h p) := by
  rw [show referenceTransform h p = affineCombination p
      (referenceCorner (h 0)) (referenceCorner (h 1))
      (referenceCorner (h 2)) by rfl]
  rw [referenceTransform_affineCombination]
  simp only [referenceTransform_corner]
  rfl

lemma referenceRelabel_one :
    referenceRelabel (1 : ReferenceSymmetry) = 1 := by
  unfold referenceRelabel
  exact
    (Equiv.Perm.extendDomain_one referenceSlot.toEquivRange)

lemma referenceRelabel_mul (g h : ReferenceSymmetry) :
    referenceRelabel (g * h) = referenceRelabel h * referenceRelabel g := by
  unfold referenceRelabel
  rw [mul_inv_rev]
  exact (Equiv.Perm.extendDomain_mul
    referenceSlot.toEquivRange h⁻¹ g⁻¹).symm

@[simp] lemma referenceRelabel_corner
    (g : ReferenceSymmetry) (i : Fin 3) :
    referenceRelabel g (referenceSlot i) = referenceSlot (g⁻¹ i) := by
  unfold referenceRelabel
  simpa using Equiv.Perm.extendDomain_apply_image
    (g⁻¹) referenceSlot.toEquivRange i

@[simp] lemma referenceRelabel_freeSlot
    (g : ReferenceSymmetry) (i : Fin 5) :
    referenceRelabel g (freeSlot i) = freeSlot i := by
  unfold referenceRelabel
  apply Equiv.Perm.extendDomain_apply_not_subtype
  rintro ⟨j, hj⟩
  have hval := congrArg (fun k : Fin 8 => k.val) hj
  change j.val = 3 + i.val at hval
  omega

noncomputable instance referenceConfigurationSMul :
    SMul ReferenceSymmetry Configuration where
  smul := referenceAction

noncomputable instance referenceConfigurationMulAction :
    MulAction ReferenceSymmetry Configuration where
  one_smul v := by
    change referenceAction (1 : ReferenceSymmetry) v = v
    funext i
    rw [referenceAction, referenceRelabel_one]
    simp [referenceTransform_one]
  mul_smul g h v := by
    change referenceAction (g * h) v =
      referenceAction g (referenceAction h v)
    funext i
    simp only [referenceAction]
    rw [referenceRelabel_mul]
    change referenceTransform (g * h)
      (v (referenceRelabel h (referenceRelabel g i))) = _
    rw [referenceTransform_mul]

@[simp] lemma referenceAction_freeSlot
    (g : ReferenceSymmetry) (v : Configuration) (i : Fin 5) :
    (g • v) (freeSlot i) = referenceTransform g (v (freeSlot i)) := by
  change referenceTransform g
    (v (referenceRelabel g (freeSlot i))) = _
  rw [referenceRelabel_freeSlot]

/-- The signed determinant of a reference-triangle symmetry. -/
def referenceDet (g : ReferenceSymmetry) : ℝ :=
  sig (referenceCorner (g 0)) (referenceCorner (g 1))
    (referenceCorner (g 2))

lemma sig_referenceTransform (g : ReferenceSymmetry) (p q r : ℝ × ℝ) :
    sig (referenceTransform g p) (referenceTransform g q)
        (referenceTransform g r) =
      referenceDet g * sig p q r := by
  simp only [referenceTransform, affineCombination, referenceDet, sig]
  ring

lemma abs_sig_referenceCorner_of_pairwise_ne
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    |sig (referenceCorner a) (referenceCorner b) (referenceCorner c)| = 1 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [referenceCorner, sig]

lemma abs_referenceDet (g : ReferenceSymmetry) : |referenceDet g| = 1 := by
  exact abs_sig_referenceCorner_of_pairwise_ne
    (g.injective.ne (by decide))
    (g.injective.ne (by decide))
    (g.injective.ne (by decide))

lemma referenceLinear_det (g : ReferenceSymmetry) :
    LinearMap.det (referenceLinear g) = referenceDet g := by
  simp [referenceLinear, referenceDet, Matrix.det_fin_two, sig]

lemma range_referenceTransform (g : ReferenceSymmetry) (v : Configuration) :
    Set.range (fun i => referenceTransform g (v i)) =
      referenceAffine g '' Set.range v := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨v i, ⟨i, rfl⟩, referenceAffine_apply g (v i)⟩
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (referenceAffine_apply g (v i)).symm⟩

lemma referenceAffine_image_eq (g : ReferenceSymmetry)
    (s : Set (ℝ × ℝ)) :
    referenceAffine g '' s =
      (fun x => referenceCorner (g 0) + x) '' (referenceLinear g '' s) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨referenceLinear g q, ⟨q, hq, rfl⟩, ?_⟩
    rw [referenceAffine_apply, referenceTransform, affineCombination,
      referenceLinear_apply]
    ext <;> dsimp <;> ring
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨r, hr, ?_⟩
    rw [referenceAffine_apply, referenceTransform, affineCombination,
      referenceLinear_apply]
    ext <;> dsimp <;> ring

/-- Every reference-triangle symmetry, including the three reflections,
preserves Lebesgue area. -/
lemma volume_convexHull_referenceTransform (g : ReferenceSymmetry)
    (v : Configuration) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (fun i => referenceTransform g (v i)))) =
      MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  rw [range_referenceTransform, ← (referenceAffine g).image_convexHull]
  rw [referenceAffine_image_eq, Set.image_add_left,
    MeasureTheory.measure_preimage_add]
  rw [MeasureTheory.Measure.addHaar_image_linearMap, referenceLinear_det,
    abs_referenceDet]
  simp

lemma doubledHullArea_referenceTransform (g : ReferenceSymmetry)
    (v : Configuration) :
    doubledHullArea (fun i => referenceTransform g (v i)) =
      doubledHullArea v := by
  simp only [doubledHullArea, volume_convexHull_referenceTransform]

@[simp] lemma abs_sig_referenceTransform
    (g : ReferenceSymmetry) (p q r : ℝ × ℝ) :
    |sig (referenceTransform g p) (referenceTransform g q)
        (referenceTransform g r)| = |sig p q r| := by
  rw [sig_referenceTransform, abs_mul, abs_referenceDet, one_mul]

lemma minTri_referenceTransform (g : ReferenceSymmetry) (v : Configuration) :
    minTri (fun i => referenceTransform g (v i)) = minTri v := by
  unfold minTri
  congr 1
  funext t
  exact abs_sig_referenceTransform g _ _ _

@[simp] lemma minTri_referenceAction
    (g : ReferenceSymmetry) (v : Configuration) :
    minTri (g • v) = minTri v := by
  change minTri (fun i => referenceTransform g (v (referenceRelabel g i))) = _
  rw [minTri_referenceTransform, minTri_relabel]

@[simp] lemma doubledHullArea_referenceAction
    (g : ReferenceSymmetry) (v : Configuration) :
    doubledHullArea (g • v) = doubledHullArea v := by
  change doubledHullArea
    (fun i => referenceTransform g (v (referenceRelabel g i))) = _
  rw [doubledHullArea_referenceTransform, doubledHullArea_relabel]

@[simp] lemma areaRatio_referenceAction
    (g : ReferenceSymmetry) (v : Configuration) :
    areaRatio doubledHullArea (g • v) =
      areaRatio doubledHullArea v := by
  simp [areaRatio]

theorem GaugeNormalized.referenceAction
    {v : Configuration} (hv : GaugeNormalized v) (g : ReferenceSymmetry) :
    GaugeNormalized (g • v) := by
  have hcorner : ∀ i : Fin 3,
      v (referenceSlot i) = referenceCorner i := by
    intro i
    fin_cases i
    · change v 0 = (0, 0)
      exact hv.map_zero
    · change v 1 = (1, 0)
      exact hv.map_one
    · change v 2 = (0, 1)
      exact hv.map_two
  have hslot : ∀ i : Fin 3,
      (g • v) (referenceSlot i) = referenceCorner i := by
    intro i
    change referenceTransform g
      (v (referenceRelabel g (referenceSlot i))) = referenceCorner i
    rw [referenceRelabel_corner, hcorner, referenceTransform_corner]
    simp
  have hzero : (g • v) 0 = (0, 0) := by
    change (g • v) (referenceSlot 0) = (0, 0)
    simpa [referenceCorner] using hslot 0
  have hone : (g • v) 1 = (1, 0) := by
    change (g • v) (referenceSlot 1) = (1, 0)
    simpa [referenceCorner] using hslot 1
  have htwo : (g • v) 2 = (0, 1) := by
    change (g • v) (referenceSlot 2) = (0, 1)
    simpa [referenceCorner] using hslot 2
  have hmax : ∀ a b c : Fin 8,
      |sig ((g • v) a) ((g • v) b) ((g • v) c)| ≤ 1 := by
    intro a b c
    change
      |sig (referenceTransform g (v (referenceRelabel g a)))
        (referenceTransform g (v (referenceRelabel g b)))
        (referenceTransform g (v (referenceRelabel g c)))| ≤ 1
    rw [abs_sig_referenceTransform]
    exact hv.maximal _ _ _
  exact ⟨hzero, hone, htwo, hmax,
    inMaximalityBox_of_normalized (g • v) 0 1 2 hzero hone htwo hmax⟩

/-- The concrete stability premise needed by the finite-orbit minimizer. -/
theorem referenceAction_stable :
    ∀ (g : ReferenceSymmetry) (v : Configuration),
      GaugeNormalized v → GaugeNormalized (g • v) :=
  fun g _ hv => hv.referenceAction g

/-- Sum of the five free x-coordinates. -/
noncomputable def freeXSum (v : Configuration) : ℝ :=
  ∑ i : Fin 5, (v (freeSlot i)).1

/-- Sum of the five free y-coordinates. -/
noncomputable def freeYSum (v : Configuration) : ℝ :=
  ∑ i : Fin 5, (v (freeSlot i)).2

/-- Weak fundamental chamber selected by the five emitted quotient rows. -/
def GaugeQuotientChamber (v : Configuration) : Prop :=
  (-3 * freeXSum v + 3 * freeYSum v ≤ 0) ∧
  (4 * freeXSum v + 2 * freeYSum v ≤ 10) ∧
  (-freeXSum v + 7 * freeYSum v ≤ 10) ∧
  (7 * freeXSum v + 8 * freeYSum v ≤ 25) ∧
  (5 * freeXSum v + 10 * freeYSum v ≤ 25)

def symmetry021 : ReferenceSymmetry := Equiv.swap 1 2

def symmetry102 : ReferenceSymmetry := Equiv.swap 0 1

def symmetry120 : ReferenceSymmetry := Equiv.swap 0 1 * Equiv.swap 1 2

def symmetry201 : ReferenceSymmetry := Equiv.swap 1 2 * Equiv.swap 0 1

def symmetry210 : ReferenceSymmetry := Equiv.swap 0 2

@[simp] lemma symmetry021_zero : symmetry021 0 = 0 := by decide
@[simp] lemma symmetry021_one : symmetry021 1 = 2 := by decide
@[simp] lemma symmetry021_two : symmetry021 2 = 1 := by decide
@[simp] lemma symmetry102_zero : symmetry102 0 = 1 := by decide
@[simp] lemma symmetry102_one : symmetry102 1 = 0 := by decide
@[simp] lemma symmetry102_two : symmetry102 2 = 2 := by decide
@[simp] lemma symmetry120_zero : symmetry120 0 = 1 := by decide
@[simp] lemma symmetry120_one : symmetry120 1 = 2 := by decide
@[simp] lemma symmetry120_two : symmetry120 2 = 0 := by decide
@[simp] lemma symmetry201_zero : symmetry201 0 = 2 := by decide
@[simp] lemma symmetry201_one : symmetry201 1 = 0 := by decide
@[simp] lemma symmetry201_two : symmetry201 2 = 1 := by decide
@[simp] lemma symmetry210_zero : symmetry210 0 = 2 := by decide
@[simp] lemma symmetry210_one : symmetry210 1 = 1 := by decide
@[simp] lemma symmetry210_two : symmetry210 2 = 0 := by decide

lemma pilotFunctional_eq_sums (v : Configuration) :
    pilotFunctional v =
      2 * freeXSum v + 5 * freeYSum v := by
  simp [pilotFunctional, freeXSum, freeYSum, Finset.sum_add_distrib,
    Finset.mul_sum]

lemma pilotFunctional_symmetry021 (v : Configuration) :
    pilotFunctional (symmetry021 • v) =
      5 * freeXSum v + 2 * freeYSum v := by
  rw [pilotFunctional_eq_sums]
  simp only [freeXSum, freeYSum]
  simp_rw [referenceAction_freeSlot]
  simp [
    referenceTransform, affineCombination, referenceCorner,
    freeSlot, Fin.sum_univ_succ]
  ring

lemma pilotFunctional_symmetry102 (v : Configuration) :
    pilotFunctional (symmetry102 • v) =
      10 - 2 * freeXSum v + 3 * freeYSum v := by
  rw [pilotFunctional_eq_sums]
  simp only [freeXSum, freeYSum]
  simp_rw [referenceAction_freeSlot]
  simp [
    referenceTransform, affineCombination, referenceCorner,
    freeSlot, Fin.sum_univ_succ]
  ring

lemma pilotFunctional_symmetry120 (v : Configuration) :
    pilotFunctional (symmetry120 • v) =
      10 + 3 * freeXSum v - 2 * freeYSum v := by
  rw [pilotFunctional_eq_sums]
  simp only [freeXSum, freeYSum]
  simp_rw [referenceAction_freeSlot]
  simp [
    referenceTransform, affineCombination, referenceCorner,
    freeSlot, Fin.sum_univ_succ]
  ring

lemma pilotFunctional_symmetry201 (v : Configuration) :
    pilotFunctional (symmetry201 • v) =
      25 - 5 * freeXSum v - 3 * freeYSum v := by
  rw [pilotFunctional_eq_sums]
  simp only [freeXSum, freeYSum]
  simp_rw [referenceAction_freeSlot]
  simp [
    referenceTransform, affineCombination, referenceCorner,
    freeSlot, Fin.sum_univ_succ]
  ring

lemma pilotFunctional_symmetry210 (v : Configuration) :
    pilotFunctional (symmetry210 • v) =
      25 - 3 * freeXSum v - 5 * freeYSum v := by
  rw [pilotFunctional_eq_sums]
  simp only [freeXSum, freeYSum]
  simp_rw [referenceAction_freeSlot]
  simp [
    referenceTransform, affineCombination, referenceCorner,
    freeSlot, Fin.sum_univ_succ]
  ring

theorem GaugeQuotientChamber.of_orbit_minimal
    (v : Configuration)
    (hmin : ∀ h : ReferenceSymmetry,
      pilotFunctional v ≤ pilotFunctional (h • v)) :
    GaugeQuotientChamber v := by
  have h021 := hmin symmetry021
  have h102 := hmin symmetry102
  have h120 := hmin symmetry120
  have h201 := hmin symmetry201
  have h210 := hmin symmetry210
  rw [pilotFunctional_eq_sums, pilotFunctional_symmetry021] at h021
  rw [pilotFunctional_eq_sums, pilotFunctional_symmetry102] at h102
  rw [pilotFunctional_eq_sums, pilotFunctional_symmetry120] at h120
  rw [pilotFunctional_eq_sums, pilotFunctional_symmetry201] at h201
  rw [pilotFunctional_eq_sums, pilotFunctional_symmetry210] at h210
  unfold GaugeQuotientChamber
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Concrete finite-group representative selected by exactly the functional
used by the machine corpus.  Weak inequalities retain every tied minimizer. -/
theorem exists_referenceTriangle_quotientRepresentative
    (v : Configuration) (hv : GaugeNormalized v) :
    ∃ g : ReferenceSymmetry,
      GaugeNormalized (g • v) ∧
      GaugeQuotientChamber (g • v) ∧
      minTri (g • v) = minTri v := by
  obtain ⟨g, hnorm, hmin⟩ :=
    exists_orbit_functional_minimizer GaugeNormalized
      referenceAction_stable pilotFunctional v hv
  exact ⟨g, hnorm, GaugeQuotientChamber.of_orbit_minimal _ hmin,
    minTri_referenceAction g v⟩

/-- The exact domain assumptions installed by `ExactModel.build_base_rows`:
gauge normalization, nondecreasing free x-coordinates, and the five quotient
rows. -/
def ReferenceMachineDomain (v : Configuration) : Prop :=
  GaugeNormalized v ∧
  Monotone (xCoordsOf v) ∧
  GaugeQuotientChamber v

/-- Sorting the five free labels preserves the quotient chamber because all
five quotient rows depend only on the free-coordinate sums. -/
theorem exists_referenceMachineDomain_representative
    (v : Configuration) (hv : GaugeNormalized v) :
    ∃ w : Configuration,
      ReferenceMachineDomain w ∧
      minTri w = minTri v ∧
      doubledHullArea w = doubledHullArea v ∧
      areaRatio doubledHullArea w = areaRatio doubledHullArea v := by
  obtain ⟨g, hgu, hchamber, hmin⟩ :=
    exists_referenceTriangle_quotientRepresentative v hv
  let u : Configuration := g • v
  let key : Fin 5 → ℝ := xCoordsOf u
  let tau : Equiv.Perm (Fin 5) := Tuple.sort key
  let sigma : Equiv.Perm (Fin 8) := tau.viaFintypeEmbedding freeSlot
  let w : Configuration := fun i => u (sigma i)
  have hfix : ∀ i : Fin 8, i.val < 3 → sigma i = i := by
    intro i hi
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨j, hj⟩
    have hval := congrArg Fin.val hj
    change 3 + j.val = i.val at hval
    omega
  have hfree (i : Fin 5) :
      sigma (freeSlot i) = freeSlot (tau i) := by
    exact Equiv.Perm.viaFintypeEmbedding_apply_image tau freeSlot i
  have hnorm : GaugeNormalized w := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change u (sigma 0) = (0, 0)
      rw [hfix 0 (by decide)]
      exact hgu.map_zero
    · change u (sigma 1) = (1, 0)
      rw [hfix 1 (by decide)]
      exact hgu.map_one
    · change u (sigma 2) = (0, 1)
      rw [hfix 2 (by decide)]
      exact hgu.map_two
    · intro a b c
      exact hgu.maximal (sigma a) (sigma b) (sigma c)
    · intro i
      exact hgu.box (sigma i)
  have hmono : Monotone (xCoordsOf w) := by
    intro i j hij
    have hsort := Tuple.monotone_sort key hij
    simpa only [key, xCoordsOf, Function.comp_apply, w, hfree] using hsort
  have hxsum : freeXSum w = freeXSum u := by
    simp only [freeXSum, w, hfree]
    exact Equiv.sum_comp tau (fun i => (u (freeSlot i)).1)
  have hysum : freeYSum w = freeYSum u := by
    simp only [freeYSum, w, hfree]
    exact Equiv.sum_comp tau (fun i => (u (freeSlot i)).2)
  have hchamber' : GaugeQuotientChamber w := by
    unfold GaugeQuotientChamber at hchamber ⊢
    simpa only [hxsum, hysum] using hchamber
  have hmin' : minTri w = minTri v := by
    calc
      minTri w = minTri u := minTri_relabel u sigma
      _ = minTri v := hmin
  have harea' : doubledHullArea w = doubledHullArea v := by
    calc
      doubledHullArea w = doubledHullArea u :=
        doubledHullArea_relabel u sigma
      _ = doubledHullArea v := doubledHullArea_referenceAction g v
  refine ⟨w, ⟨hnorm, hmono, hchamber'⟩, hmin', harea', ?_⟩
  simp only [areaRatio, hmin', harea']

#print axioms exists_referenceTriangle_quotientRepresentative
#print axioms exists_referenceMachineDomain_representative

end Heilbronn8
