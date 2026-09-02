import Heilbronn8.QuadHull.OrbitIICommon

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-- Canonical two-QAB/one-QDA leaf, delegated to the direct j = 2 producer. -/
theorem orbitIIJ2_orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D)
    (X Y Z : Fin 8)
    (hperm : Function.Injective (orbitIILabels A B C D h.Q X Y Z))
    (hX : TriHull.InTriStrict (v X) (v h.Q) (v A) (v B))
    (hY : TriHull.InTriStrict (v Y) (v h.Q) (v A) (v B))
    (hZ : TriHull.InTriStrict (v Z) (v h.Q) (v D) (v A)) :
    OrbitCertificate v A B C D := by
  let fine : OrbitIIJ2GeometryCertificate v A B C D :=
    { Q := h.Q
      P := X
      R := Y
      Z := Z
      labels_injective := by
        simpa [orbitIILabels] using hperm
      ccw := h.ccw
      Q_in_ABC := h.Q_in_ABC
      Q_in_BCD := h.Q_in_BCD
      P_in_QAB := hX
      R_in_QAB := hY
      Z_in_QDA := hZ }
  exact fine.orbitCertificate

end OrbitIIInternal
end Heilbronn8.QuadHull
