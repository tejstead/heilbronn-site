import Heilbronn8.QuadHull.OrbitIISemanticFan

/-!
# Exhaustive semantic fan splitting for coarse Orbit II
-/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-- The three semantic fan memberships, separated from scalar normalization. -/
structure OrbitIISemanticFanSplit
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D) : Prop where
  P :
    TriHull.InTriStrict (v h.P) (v h.Q) (v A) (v B) ∨
      TriHull.InTriStrict (v h.P) (v h.Q) (v D) (v A)
  R :
    TriHull.InTriStrict (v h.R) (v h.Q) (v A) (v B) ∨
      TriHull.InTriStrict (v h.R) (v h.Q) (v D) (v A)
  S :
    TriHull.InTriStrict (v h.S) (v h.Q) (v A) (v B) ∨
      TriHull.InTriStrict (v h.S) (v h.Q) (v D) (v A)

/-- Nonzero determinants make all three coarse fan splits exhaustive. -/
theorem semanticFanSplit
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) :
    OrbitIISemanticFanSplit h := by
  let labels : Fin 8 → Fin 8 :=
    orbitIILabels A B C D h.Q h.P h.R h.S
  have hlabels : Function.Injective labels := by
    simpa [labels] using h.labels_injective
  have label_ne (i j : Fin 8) (hij : i ≠ j) :
      labels i ≠ labels j := hlabels.ne hij
  have hABDpos : 0 < sig (v A) (v B) (v D) := by
    calc
      0 < sig (v D) (v A) (v B) := h.ccw.2.2.2
      _ = sig (v A) (v B) (v D) := sig_rotate _ _ _
  obtain ⟨_, _, hαpos⟩ :=
    TriHull.inTriStrict_fan_pos h.ccw.1 h.Q_in_ABC
  obtain ⟨_, hvpos, _⟩ :=
    TriHull.inTriStrict_fan_pos h.ccw.2.1 h.Q_in_BCD
  have hδpos : 0 < sig (v h.Q) (v D) (v A) := by
    obtain ⟨qx, qy, qz, _hqx, hqy, hqz, hqsum, hQeq⟩ := h.Q_in_ABC
    have hBDApos : 0 < sig (v B) (v D) (v A) := by
      calc
        0 < sig (v D) (v A) (v B) := h.ccw.2.2.2
        _ = sig (v A) (v B) (v D) := sig_rotate _ _ _
        _ = sig (v B) (v D) (v A) := sig_rotate _ _ _
    have hCDApos : 0 < sig (v C) (v D) (v A) := h.ccw.2.2.1
    rw [hQeq,
      sig_affine_fst (v A) (v B) (v C) (v D) (v A)
        qx qy qz hqsum]
    simp only [sig_eq13, mul_zero, zero_add]
    exact add_pos (mul_pos hqy hBDApos) (mul_pos hqz hCDApos)
  have hQAPne : sig (v h.Q) (v A) (v h.P) ≠ 0 := by
    apply sig_ne_zero_of_minTri_ne_zero hmzero
    · simpa [labels, orbitIILabels] using label_ne 4 0 (by decide)
    · simpa [labels, orbitIILabels] using label_ne 4 5 (by decide)
    · simpa [labels, orbitIILabels] using label_ne 0 5 (by decide)
  have hQARne : sig (v h.Q) (v A) (v h.R) ≠ 0 := by
    apply sig_ne_zero_of_minTri_ne_zero hmzero
    · simpa [labels, orbitIILabels] using label_ne 4 0 (by decide)
    · simpa [labels, orbitIILabels] using label_ne 4 6 (by decide)
    · simpa [labels, orbitIILabels] using label_ne 0 6 (by decide)
  have hQASne : sig (v h.Q) (v A) (v h.S) ≠ 0 := by
    apply sig_ne_zero_of_minTri_ne_zero hmzero
    · simpa [labels, orbitIILabels] using label_ne 4 0 (by decide)
    · simpa [labels, orbitIILabels] using label_ne 4 7 (by decide)
    · simpa [labels, orbitIILabels] using label_ne 0 7 (by decide)
  exact
    { P := in_QAB_or_QDA hαpos hδpos hvpos hABDpos h.P_in_ABD hQAPne
      R := in_QAB_or_QDA hαpos hδpos hvpos hABDpos h.R_in_ABD hQARne
      S := in_QAB_or_QDA hαpos hδpos hvpos hABDpos h.S_in_ABD hQASne }

end OrbitIIInternal
end Heilbronn8.QuadHull
