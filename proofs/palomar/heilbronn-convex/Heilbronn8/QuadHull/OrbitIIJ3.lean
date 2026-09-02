import Heilbronn8.QuadHull.OrbitIICommon

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-- Canonical all-QAB leaf, namely Orbit II with j = 3. -/
theorem orbitIIJ3_orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D)
    (hm : 0 < minTri v)
    (hP : TriHull.InTriStrict (v h.P) (v h.Q) (v A) (v B))
    (hR : TriHull.InTriStrict (v h.R) (v h.Q) (v A) (v B))
    (hS : TriHull.InTriStrict (v h.S) (v h.Q) (v A) (v B)) :
    OrbitCertificate v A B C D := by
  let n := normalizedData h hm
  let labels : Fin 8 → Fin 8 :=
    orbitIILabels A B C D h.Q h.P h.R h.S
  have hlabels : Function.Injective labels := by
    simpa [labels] using h.labels_injective
  let slots : Fin 6 → Fin 8 := ![4, 0, 1, 5, 6, 7]
  have hslots : Function.Injective slots := by decide
  let e : Fin 6 → Fin 8 := fun i => labels (slots i)
  have he : Function.Injective e := hlabels.comp hslots
  have halphaRaw :
      (17 : ℝ) / 2 ≤ sig (v h.Q) (v A) (v B) / minTri v := by
    simpa [e, slots, labels, orbitIILabels] using
      TriHull.threePointTriangle_normalized_lower_bound_unconditional
        v e he hm n.alpha_pos
        (by simpa [e, slots, labels, orbitIILabels] using hP)
        (by simpa [e, slots, labels, orbitIILabels] using hR)
        (by simpa [e, slots, labels, orbitIILabels] using hS)
  have halpha : (17 : ℝ) / 2 ≤ n.fan.α := by
    rw [n.alpha_eq]
    exact halphaRaw
  exact Or.inr ⟨n.H, n.scale,
    .orbit_II_j3 n.fan halpha n.diagonal_AC n.diagonal_BD⟩

end OrbitIIInternal
end Heilbronn8.QuadHull
