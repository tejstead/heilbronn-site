import Heilbronn8.QuadHull.OrbitIICommon

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-- Canonical all-QDA leaf, namely Orbit II with j = 0. -/
theorem orbitIIJ0_orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D)
    (hm : 0 < minTri v)
    (hP : TriHull.InTriStrict (v h.P) (v h.Q) (v D) (v A))
    (hR : TriHull.InTriStrict (v h.R) (v h.Q) (v D) (v A))
    (hS : TriHull.InTriStrict (v h.S) (v h.Q) (v D) (v A)) :
    OrbitCertificate v A B C D := by
  let n := normalizedData h hm
  let labels : Fin 8 → Fin 8 :=
    orbitIILabels A B C D h.Q h.P h.R h.S
  have hlabels : Function.Injective labels := by
    simpa [labels] using h.labels_injective
  let slots : Fin 6 → Fin 8 := ![4, 3, 0, 5, 6, 7]
  have hslots : Function.Injective slots := by decide
  let e : Fin 6 → Fin 8 := fun i => labels (slots i)
  have he : Function.Injective e := hlabels.comp hslots
  have hdeltaRaw :
      (17 : ℝ) / 2 ≤ sig (v h.Q) (v D) (v A) / minTri v := by
    simpa [e, slots, labels, orbitIILabels] using
      TriHull.threePointTriangle_normalized_lower_bound_unconditional
        v e he hm n.delta_pos
        (by simpa [e, slots, labels, orbitIILabels] using hP)
        (by simpa [e, slots, labels, orbitIILabels] using hR)
        (by simpa [e, slots, labels, orbitIILabels] using hS)
  have hdelta : (17 : ℝ) / 2 ≤ n.fan.δ := by
    rw [n.delta_eq]
    exact hdeltaRaw
  exact Or.inr ⟨n.H, n.scale, .orbit_II_j0 n.fan hdelta⟩

end OrbitIIInternal
end Heilbronn8.QuadHull
