import Heilbronn8.QuadHull.Dihedral
import Heilbronn8.QuadHull.Bridge
import Heilbronn8.QuadHull.OrbitISemanticSelector

/-!
# Sound output interface for the global hull-four classification

The existing `OrbitCertificate` constructors describe all of the hard
normalized leaves, but the coarse orbit-I placement has easy fan patterns
which prove the target hull bound directly before reaching the nested
`OrbitICommonGeometryCertificate`.  Consequently, an exhaustive geometric
classifier should return the disjunction below rather than falsely forcing
every orbit-I configuration into the nested residual record.

This module supplies the output and its consumers.  It deliberately does not
assert the still-missing theorem which classifies every strict four-hull
configuration.
-/

namespace Heilbronn8.QuadHull

/-- The normalized `63/5` hull lower bound, stated without dividing by
`minTri`. -/
def DirectHullFourBound
    (v : Fin 8 → Point) (A B C D : Fin 8) : Prop :=
  (63 : ℝ) / 5 * (minTri v / 2) ≤
    quadHullArea (v A) (v B) (v C) (v D)

/-- Sound output of the future exhaustive classifier.  Easy geometry may
close the target directly; hard geometry is retained as an ordinary
`OrbitCertificate`. -/
inductive HullFourClosureCertificate
    (v : Fin 8 → Point) (A B C D : Fin 8) : Prop
  | direct (h : DirectHullFourBound v A B C D)
  | orbit (h : OrbitCertificate v A B C D)

/-- An ordinary orbit certificate implies the direct normalized lower bound
as soon as the labelled quadrilateral has nonnegative area. -/
theorem directHullFourBound_of_orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (harea : 0 ≤ quadHullArea (v A) (v B) (v C) (v D))
    (hcert : OrbitCertificate v A B C D) :
    DirectHullFourBound v A B C D := by
  rcases hcert with hzero | ⟨H, hscale, hcase⟩
  · simp [DirectHullFourBound, hzero, harea]
  · have hH : (63 : ℝ) / 5 ≤ H :=
      normalized_quadHull8_bound crossApexIdentity47_holds
        crossApexIdentity48_holds orbitI_residual_bound hcase
    have hm : 0 ≤ minTri v / 2 := by
      linarith [minTri_nonneg v]
    have hmul := mul_le_mul_of_nonneg_left hH hm
    unfold DirectHullFourBound
    rw [hscale]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Every closure-certificate output has the same direct semantic meaning. -/
theorem HullFourClosureCertificate.directBound
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate v A B C D)
    (harea : 0 ≤ quadHullArea (v A) (v B) (v C) (v D)) :
    DirectHullFourBound v A B C D := by
  cases h with
  | direct hdirect => exact hdirect
  | orbit hcert =>
      exact directHullFourBound_of_orbitCertificate harea hcert

/-- Scale-free form used by the production hull-four join. -/
theorem HullFourClosureCertificate.scaleFreeBound
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate v A B C D)
    (harea : 0 ≤ quadHullArea (v A) (v B) (v C) (v D)) :
    minTri v ≤ (5 : ℝ) / 63 *
      (2 * quadHullArea (v A) (v B) (v C) (v D)) := by
  have hbound := h.directBound harea
  unfold DirectHullFourBound at hbound
  nlinarith

/-- The exact honest output needed from the missing top-level orbit-I
reduction: either its easy fan arithmetic is already done, or the selected
configuration reaches the existing nested residual producer. -/
def OrbitIClassificationOutcome
    (v : Fin 8 → Point) (A B C D : Fin 8) : Prop :=
  DirectHullFourBound v A B C D ∨
    Nonempty (OrbitICommonGeometryCertificate v A B C D)

/-- Convert the orbit-I-specific output to the common global output. -/
theorem OrbitIClassificationOutcome.toClosure
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIClassificationOutcome v A B C D) :
    HullFourClosureCertificate v A B C D := by
  rcases h with hdirect | hcommon
  · exact .direct hdirect
  · rcases hcommon with ⟨certificate⟩
    exact .orbit certificate.orbitCertificate

/-- Cyclic normalization is sound for either output branch. -/
theorem HullFourClosureCertificate.rotateBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate v B C D A) :
    HullFourClosureCertificate v A B C D := by
  cases h with
  | direct hdirect =>
      apply HullFourClosureCertificate.direct
      unfold DirectHullFourBound at hdirect ⊢
      rw [quadHullArea_rotate] at hdirect
      exact hdirect
  | orbit hcert => exact .orbit hcert.rotateBack

/-- Transport back across two cyclic hull steps. -/
theorem HullFourClosureCertificate.rotateTwoBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate v C D A B) :
    HullFourClosureCertificate v A B C D :=
  h.rotateBack.rotateBack

/-- Transport back across three cyclic hull steps. -/
theorem HullFourClosureCertificate.rotateThreeBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate v D A B C) :
    HullFourClosureCertificate v A B C D :=
  h.rotateBack.rotateBack.rotateBack

/-- Reflection plus reversal is sound for either output branch. -/
theorem HullFourClosureCertificate.mirrorReverseBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate
      (mirrorConfiguration v) A D C B) :
    HullFourClosureCertificate v A B C D := by
  cases h with
  | direct hdirect =>
      apply HullFourClosureCertificate.direct
      unfold DirectHullFourBound at hdirect ⊢
      rw [minTri_mirrorConfiguration] at hdirect
      change (63 : ℝ) / 5 * (minTri v / 2) ≤
        quadHullArea (mirrorPoint (v A)) (mirrorPoint (v D))
          (mirrorPoint (v C)) (mirrorPoint (v B)) at hdirect
      rw [quadHullArea_mirrorReverse] at hdirect
      exact hdirect
  | orbit hcert => exact .orbit hcert.mirrorReverseBack

/-- The first cyclic chart of the mirrored/reversed hull. -/
theorem HullFourClosureCertificate.mirrorReverseRotateBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate
      (mirrorConfiguration v) D C B A) :
    HullFourClosureCertificate v A B C D :=
  h.rotateBack.mirrorReverseBack

/-- The second cyclic chart of the mirrored/reversed hull. -/
theorem HullFourClosureCertificate.mirrorReverseRotateTwoBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate
      (mirrorConfiguration v) C B A D) :
    HullFourClosureCertificate v A B C D :=
  h.rotateTwoBack.mirrorReverseBack

/-- The third cyclic chart of the mirrored/reversed hull. -/
theorem HullFourClosureCertificate.mirrorReverseRotateThreeBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourClosureCertificate
      (mirrorConfiguration v) B A D C) :
    HullFourClosureCertificate v A B C D :=
  h.rotateThreeBack.mirrorReverseBack

/-- Coarse canonical geometry for sector census `(4,0,0,0)`.  The future
side-minimal/fan-exclusion theorem should consume this structure and return
`OrbitIClassificationOutcome`; it must not return
`OrbitICommonGeometryCertificate` unconditionally. -/
structure OrbitICoarseGeometryCertificate
    (v : Fin 8 → Point) (A B C D : Fin 8) where
  P : Fin 8
  Q : Fin 8
  R : Fin 8
  S : Fin 8
  labels_injective : Function.Injective (quadLabels A B C D P Q R S)
  ccw : CCWQuad (v A) (v B) (v C) (v D)
  P_in_ABC : TriHull.InTriStrict (v P) (v A) (v B) (v C)
  Q_in_ABC : TriHull.InTriStrict (v Q) (v A) (v B) (v C)
  R_in_ABC : TriHull.InTriStrict (v R) (v A) (v B) (v C)
  S_in_ABC : TriHull.InTriStrict (v S) (v A) (v B) (v C)
  P_in_DAB : TriHull.InTriStrict (v P) (v D) (v A) (v B)
  Q_in_DAB : TriHull.InTriStrict (v Q) (v D) (v A) (v B)
  R_in_DAB : TriHull.InTriStrict (v R) (v D) (v A) (v B)
  S_in_DAB : TriHull.InTriStrict (v S) (v D) (v A) (v B)

end Heilbronn8.QuadHull
