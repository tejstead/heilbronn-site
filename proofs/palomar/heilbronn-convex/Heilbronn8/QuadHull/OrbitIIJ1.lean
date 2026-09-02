import Heilbronn8.QuadHull.OrbitIICommon

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

lemma onePointTriangle_normalized_lower_bound
    (v : Fin 8 → Point) (e : Fin 4 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : TriHull.InTriStrict (v (e 3))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    3 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := TriHull.inTriStrict_fan_pos hpos hP
  have hPBCmin := minTri_le_abs_sig_of_pairwise_ne v
    (he.ne (by decide : (3 : Fin 4) ≠ 1))
    (he.ne (by decide : (3 : Fin 4) ≠ 2))
    (he.ne (by decide : (1 : Fin 4) ≠ 2))
  have hPCAmin := minTri_le_abs_sig_of_pairwise_ne v
    (he.ne (by decide : (3 : Fin 4) ≠ 2))
    (he.ne (by decide : (3 : Fin 4) ≠ 0))
    (he.ne (by decide : (2 : Fin 4) ≠ 0))
  have hPABmin := minTri_le_abs_sig_of_pairwise_ne v
    (he.ne (by decide : (3 : Fin 4) ≠ 0))
    (he.ne (by decide : (3 : Fin 4) ≠ 1))
    (he.ne (by decide : (0 : Fin 4) ≠ 1))
  rw [abs_of_pos hPBC] at hPBCmin
  rw [abs_of_pos hPCA] at hPCAmin
  rw [abs_of_pos hPAB] at hPABmin
  have hsum := TriHull.fan_sum
    (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))
  rw [le_div_iff₀ hm]
  nlinarith

/-- Canonical one-QAB/two-QDA leaf, namely Orbit II with j = 1. -/
theorem orbitIIJ1_orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D)
    (hm : 0 < minTri v)
    (X Y Z : Fin 8)
    (hperm : Function.Injective (orbitIILabels A B C D h.Q X Y Z))
    (hX : TriHull.InTriStrict (v X) (v h.Q) (v A) (v B))
    (hY : TriHull.InTriStrict (v Y) (v h.Q) (v D) (v A))
    (hZ : TriHull.InTriStrict (v Z) (v h.Q) (v D) (v A)) :
    OrbitCertificate v A B C D := by
  let n := normalizedData h hm
  let labels : Fin 8 → Fin 8 := orbitIILabels A B C D h.Q X Y Z
  have hlabels : Function.Injective labels := by
    simpa [labels] using hperm
  have halphaRaw : 3 ≤ sig (v h.Q) (v A) (v B) / minTri v := by
    let slots : Fin 4 → Fin 8 := ![4, 0, 1, 5]
    have hslots : Function.Injective slots := by decide
    let e : Fin 4 → Fin 8 := fun i => labels (slots i)
    have he : Function.Injective e := hlabels.comp hslots
    simpa [e, slots, labels, orbitIILabels] using
      onePointTriangle_normalized_lower_bound v e he hm n.alpha_pos
        (by simpa [e, slots, labels, orbitIILabels] using hX)
  have hdeltaMain :
      4 + 2 * Real.sqrt 3 ≤
        sig (v h.Q) (v D) (v A) / minTri v := by
    let slots : Fin 5 → Fin 8 := ![4, 3, 0, 6, 7]
    have hslots : Function.Injective slots := by decide
    let e : Fin 5 → Fin 8 := fun i => labels (slots i)
    have he : Function.Injective e := hlabels.comp hslots
    simpa [e, slots, labels, orbitIILabels] using
      TriHull.twoPointTriangle_normalized_lower_bound v e he hm n.delta_pos
        (by simpa [e, slots, labels, orbitIILabels] using hY)
        (by simpa [e, slots, labels, orbitIILabels] using hZ)
  have hdeltaRaw : F2 <
      sig (v h.Q) (v D) (v A) / minTri v := by
    norm_num [F2] at ⊢
    nlinarith [TriHull.sixty_nine_fortieths_lt_sqrt_three]
  have halpha : 3 ≤ n.fan.α := by
    rw [n.alpha_eq]
    exact halphaRaw
  have hdelta : F2 < n.fan.δ := by
    rw [n.delta_eq]
    exact hdeltaRaw
  exact Or.inr ⟨n.H, n.scale, .orbit_II_j1 n.fan halpha hdelta⟩

end OrbitIIInternal
end Heilbronn8.QuadHull
