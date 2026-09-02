import Heilbronn8.QuadHull.Bridge

/-!
# Common coarse Orbit II geometry and normalized scalar data

This module owns the stable public geometry certificate and the common
Plucker normalization used by the scalar secondary cases.
-/

namespace Heilbronn8.QuadHull

/-- The eight labels used throughout Orbit II.  Naming this function keeps
finite-vector expansion out of every permuted injectivity theorem. -/
def orbitIILabels
    (A B C D Q P R S : Fin 8) : Fin 8 → Fin 8 :=
  quadLabels A B C D Q P R S

/-- Coarse geometric data sufficient for every Orbit II secondary case. -/
structure OrbitIIGeometryCertificate
    (v : Fin 8 → Point) (A B C D : Fin 8) where
  Q : Fin 8
  P : Fin 8
  R : Fin 8
  S : Fin 8
  labels_injective : Function.Injective (orbitIILabels A B C D Q P R S)
  ccw : CCWQuad (v A) (v B) (v C) (v D)
  Q_in_ABC : TriHull.InTriStrict (v Q) (v A) (v B) (v C)
  Q_in_BCD : TriHull.InTriStrict (v Q) (v B) (v C) (v D)
  P_in_ABD : TriHull.InTriStrict (v P) (v A) (v B) (v D)
  R_in_ABD : TriHull.InTriStrict (v R) (v A) (v B) (v D)
  S_in_ABD : TriHull.InTriStrict (v S) (v A) (v B) (v D)

namespace OrbitIIInternal

/-- Common normalized scalar data shared by the non-direct Orbit II leaves. -/
structure OrbitIINormalizedData
    (v : Fin 8 → Point) (A B C D Q : Fin 8) where
  H : ℝ
  fan : PositivePluckerFan H
  scale :
    quadHullArea (v A) (v B) (v C) (v D) = minTri v / 2 * H
  alpha_pos : 0 < sig (v Q) (v A) (v B)
  delta_pos : 0 < sig (v Q) (v D) (v A)
  alpha_eq : fan.α = sig (v Q) (v A) (v B) / minTri v
  gamma_eq : fan.γ = sig (v Q) (v C) (v D) / minTri v
  delta_eq : fan.δ = sig (v Q) (v D) (v A) / minTri v
  u_eq : fan.u = sig (v Q) (v C) (v A) / minTri v
  diagonal_AC : fan.u ≤ fan.γ + fan.δ - 1
  diagonal_BD : fan.v ≤ fan.α + fan.δ - (17 : ℝ) / 2

/-- Construct the common Plücker fan and the two diagonal estimates once.
Keeping this term separate prevents every secondary case from embedding the
full normalization proof. -/
noncomputable def normalizedData
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    OrbitIINormalizedData v A B C D h.Q := by
  let labels : Fin 8 → Fin 8 :=
    orbitIILabels A B C D h.Q h.P h.R h.S
  have hlabels : Function.Injective labels := by
    simpa [labels] using h.labels_injective
  have hABDpos : 0 < sig (v A) (v B) (v D) := by
    calc
      0 < sig (v D) (v A) (v B) := h.ccw.2.2.2
      _ = sig (v A) (v B) (v D) := sig_rotate _ _ _
  have hACDpos : 0 < sig (v A) (v C) (v D) := by
    calc
      0 < sig (v C) (v D) (v A) := h.ccw.2.2.1
      _ = sig (v D) (v A) (v C) := sig_rotate _ _ _
      _ = sig (v A) (v C) (v D) := sig_rotate _ _ _
  obtain ⟨hβpos, hupos, hαpos⟩ :=
    TriHull.inTriStrict_fan_pos h.ccw.1 h.Q_in_ABC
  obtain ⟨hγpos, hvpos, _⟩ :=
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
  have unit_of_pos (i j k : Fin 8)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpos : 0 < sig (v (labels i)) (v (labels j)) (v (labels k))) :
      1 ≤ sig (v (labels i)) (v (labels j)) (v (labels k)) /
        minTri v := by
    have hmin := minTri_le_abs_sig_of_pairwise_ne v
      (hlabels.ne hij) (hlabels.ne hik) (hlabels.ne hjk)
    rw [abs_of_pos hpos] at hmin
    rw [le_div_iff₀ hm]
    simpa using hmin
  have hαunit :
      1 ≤ sig (v h.Q) (v A) (v B) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 4 0 1 (by decide) (by decide) (by decide) hαpos
  have hβunit :
      1 ≤ sig (v h.Q) (v B) (v C) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 4 1 2 (by decide) (by decide) (by decide) hβpos
  have hγunit :
      1 ≤ sig (v h.Q) (v C) (v D) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 4 2 3 (by decide) (by decide) (by decide) hγpos
  have hδunit :
      1 ≤ sig (v h.Q) (v D) (v A) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 4 3 0 (by decide) (by decide) (by decide) hδpos
  have huunit :
      1 ≤ sig (v h.Q) (v C) (v A) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 4 2 0 (by decide) (by decide) (by decide) hupos
  have hvunit :
      1 ≤ sig (v h.Q) (v D) (v B) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 4 3 1 (by decide) (by decide) (by decide) hvpos
  have hACDunit :
      1 ≤ sig (v A) (v C) (v D) / minTri v := by
    simpa [labels, orbitIILabels] using
      unit_of_pos 0 2 3 (by decide) (by decide) (by decide) hACDpos
  have hABDthree :
      (17 : ℝ) / 2 ≤ sig (v A) (v B) (v D) / minTri v := by
    let slots : Fin 6 → Fin 8 := ![0, 1, 3, 5, 6, 7]
    have hslots : Function.Injective slots := by decide
    let e : Fin 6 → Fin 8 := fun i => labels (slots i)
    have he : Function.Injective e := hlabels.comp hslots
    simpa [e, slots, labels, orbitIILabels] using
      TriHull.threePointTriangle_normalized_lower_bound_unconditional
        v e he hm hABDpos
        (by simpa [e, slots, labels, orbitIILabels] using h.P_in_ABD)
        (by simpa [e, slots, labels, orbitIILabels] using h.R_in_ABD)
        (by simpa [e, slots, labels, orbitIILabels] using h.S_in_ABD)
  let H : ℝ :=
    (sig (v A) (v B) (v C) + sig (v A) (v C) (v D)) / minTri v
  let α : ℝ := sig (v h.Q) (v A) (v B) / minTri v
  let β : ℝ := sig (v h.Q) (v B) (v C) / minTri v
  let γ : ℝ := sig (v h.Q) (v C) (v D) / minTri v
  let δ : ℝ := sig (v h.Q) (v D) (v A) / minTri v
  let u : ℝ := sig (v h.Q) (v C) (v A) / minTri v
  let qdb : ℝ := sig (v h.Q) (v D) (v B) / minTri v
  let hfan : PositivePluckerFan H := by
    refine
      { α := α
        β := β
        γ := γ
        δ := δ
        u := u
        v := qdb
        hull_eq := ?_
        α_unit := by simpa [α] using hαunit
        β_unit := by simpa [β] using hβunit
        γ_unit := by simpa [γ] using hγunit
        δ_unit := by simpa [δ] using hδunit
        u_unit := by simpa [u] using huunit
        v_unit := by simpa [qdb] using hvunit
        plucker := ?_ }
    · dsimp [H, α, β, γ, δ]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    · dsimp [α, β, γ, δ, u, qdb]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
  have hscale :
      quadHullArea (v A) (v B) (v C) (v D) = minTri v / 2 * H := by
    dsimp [H, quadHullArea, oarea]
    field_simp [ne_of_gt hm]
  have huDiag : u ≤ γ + δ - 1 := by
    have hdecomp :
        sig (v A) (v C) (v D) / minTri v = γ + δ - u := by
      dsimp [γ, δ, u]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    rw [hdecomp] at hACDunit
    linarith
  have hvDiag : qdb ≤ α + δ - (17 : ℝ) / 2 := by
    have hdecomp :
        sig (v A) (v B) (v D) / minTri v = α + δ - qdb := by
      dsimp [α, δ, qdb]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    rw [hdecomp] at hABDthree
    linarith
  refine
    { H := H
      fan := hfan
      scale := hscale
      alpha_pos := hαpos
      delta_pos := hδpos
      alpha_eq := ?_
      gamma_eq := ?_
      delta_eq := ?_
      u_eq := ?_
      diagonal_AC := ?_
      diagonal_BD := ?_ }
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [hfan] using huDiag
  · simpa [hfan] using hvDiag

end OrbitIIInternal

end Heilbronn8.QuadHull
