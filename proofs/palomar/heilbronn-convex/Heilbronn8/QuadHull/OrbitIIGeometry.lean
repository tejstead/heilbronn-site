import Heilbronn8.QuadHull.OrbitIIJ0
import Heilbronn8.QuadHull.OrbitIIJ1
import Heilbronn8.QuadHull.OrbitIIJ2
import Heilbronn8.QuadHull.OrbitIIJ3
import Heilbronn8.QuadHull.OrbitIISemantic

/-!
# A coarse geometric producer for the Orbit II branch

The public certificate is defined in OrbitIICommon.  This facade combines the
independently compiled scalar leaves with the semantic three-determinant fan
split, leaving only a small exhaustive dispatcher in this module.
-/

namespace Heilbronn8.QuadHull

open OrbitIIInternal

/-- The coarse Orbit II placement constructs one of the four existing
normalized Orbit II cases.  The public proof is only the finite semantic
dispatcher; normalization and each scalar leaf are separate declarations. -/
theorem OrbitIIGeometryCertificate.orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D) :
    OrbitCertificate v A B C D := by
  by_cases hmzero : minTri v = 0
  · exact Or.inl hmzero
  · have hm : 0 < minTri v :=
      lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hmzero)
    have split := semanticFanSplit h hmzero
    rcases split.P with hP_QAB | hP_QDA
    · rcases split.R with hR_QAB | hR_QDA
      · rcases split.S with hS_QAB | hS_QDA
        · exact orbitIIJ3_orbitCertificate h hm hP_QAB hR_QAB hS_QAB
        · exact orbitIIJ2_orbitCertificate h h.P h.R h.S
            h.labels_injective hP_QAB hR_QAB hS_QDA
      · rcases split.S with hS_QAB | hS_QDA
        · exact orbitIIJ2_orbitCertificate h h.P h.S h.R
            (labels_PSR_injective h) hP_QAB hS_QAB hR_QDA
        · exact orbitIIJ1_orbitCertificate h hm h.P h.R h.S
            h.labels_injective hP_QAB hR_QDA hS_QDA
    · rcases split.R with hR_QAB | hR_QDA
      · rcases split.S with hS_QAB | hS_QDA
        · exact orbitIIJ2_orbitCertificate h h.R h.S h.P
            (labels_RSP_injective h) hR_QAB hS_QAB hP_QDA
        · exact orbitIIJ1_orbitCertificate h hm h.R h.P h.S
            (labels_RPS_injective h) hR_QAB hP_QDA hS_QDA
      · rcases split.S with hS_QAB | hS_QDA
        · exact orbitIIJ1_orbitCertificate h hm h.S h.P h.R
            (labels_SPR_injective h) hS_QAB hP_QDA hR_QDA
        · exact orbitIIJ0_orbitCertificate h hm hP_QDA hR_QDA hS_QDA


end Heilbronn8.QuadHull
