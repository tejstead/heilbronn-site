/-
# Mechanical unified-API wrappers for n = 3, 4, 5

Source-only staging file.  It imports the already-green small-n modules and
shows how their witness-based uniqueness endpoints imply the final pairwise
nonsingular-affine Challenge API.  The six public wrappers use the exact names
and namespace selected by the unified Challenge.
-/
import Solution.N3
import Solution.N4
import Solution.N5Unique
import Solution.AffineDefs

set_option relaxedAutoImplicit false

namespace HeilbronnChallenge

open HeilbronnChallenge

private def posDet (T : PosAffine) : ℝ :=
  T.a * T.d - T.b * T.c

private lemma posDet_pos (T : PosAffine) : 0 < posDet T := by
  exact T.det_pos

private lemma posDet_ne (T : PosAffine) : posDet T ≠ 0 :=
  ne_of_gt (posDet_pos T)

/-- Composition, with `outer` applied after `inner`. -/
private noncomputable def posAffineComp
    (outer inner : PosAffine) : PosAffine where
  a := outer.a * inner.a + outer.b * inner.c
  b := outer.a * inner.b + outer.b * inner.d
  c := outer.c * inner.a + outer.d * inner.c
  d := outer.c * inner.b + outer.d * inner.d
  tx := outer.a * inner.tx + outer.b * inner.ty + outer.tx
  ty := outer.c * inner.tx + outer.d * inner.ty + outer.ty
  det_pos := by
    have hfactor :
        (outer.a * inner.a + outer.b * inner.c) *
              (outer.c * inner.b + outer.d * inner.d) -
            (outer.a * inner.b + outer.b * inner.d) *
              (outer.c * inner.a + outer.d * inner.c) =
          posDet outer * posDet inner := by
      simp only [posDet]
      ring
    rw [hfactor]
    exact mul_pos (posDet_pos outer) (posDet_pos inner)

private lemma posAffineComp_map (outer inner : PosAffine) (p : ℝ × ℝ) :
    (posAffineComp outer inner).map p = outer.map (inner.map p) := by
  apply Prod.ext
  · simp only [posAffineComp, PosAffine.map]
    ring
  · simp only [posAffineComp, PosAffine.map]
    ring

private lemma posAffineInv_det_pos (T : PosAffine) :
    0 < (T.d / posDet T) * (T.a / posDet T) -
      (-T.b / posDet T) * (-T.c / posDet T) := by
  have hdet :
      (T.d / posDet T) * (T.a / posDet T) -
          (-T.b / posDet T) * (-T.c / posDet T) =
        1 / posDet T := by
    field_simp [posDet_ne T]
    simp only [posDet]
    ring
  rw [hdet]
  exact one_div_pos.mpr (posDet_pos T)

/-- The inverse of a positive-determinant affine map. -/
private noncomputable def posAffineInv (T : PosAffine) : PosAffine where
  a := T.d / posDet T
  b := -T.b / posDet T
  c := -T.c / posDet T
  d := T.a / posDet T
  tx := (-T.d * T.tx + T.b * T.ty) / posDet T
  ty := (T.c * T.tx - T.a * T.ty) / posDet T
  det_pos := posAffineInv_det_pos T

private lemma posAffineInv_map (T : PosAffine) (p : ℝ × ℝ) :
    (posAffineInv T).map (T.map p) = p := by
  apply Prod.ext
  · simp only [posAffineInv, PosAffine.map]
    field_simp [posDet_ne T]
    simp only [posDet]
    ring
  · simp only [posAffineInv, PosAffine.map]
    field_simp [posDet_ne T]
    simp only [posDet]
    ring

private theorem gaugeEquivalent_symm {n : Nat}
    {v u : Fin n → ℝ × ℝ} (h : GaugeEquivalent v u) :
    GaugeEquivalent u v := by
  obtain ⟨sigma, T, hmap⟩ := h
  refine ⟨sigma.symm, posAffineInv T, ?_⟩
  funext i
  rw [congrFun hmap (sigma.symm i)]
  simp only [Equiv.apply_symm_apply]
  exact (posAffineInv_map T (v i)).symm

private theorem gaugeEquivalent_trans {n : Nat}
    {v u w : Fin n → ℝ × ℝ}
    (hvu : GaugeEquivalent v u) (huw : GaugeEquivalent u w) :
    GaugeEquivalent v w := by
  obtain ⟨sigma, T, hu⟩ := hvu
  obtain ⟨tau, S, hw⟩ := huw
  refine ⟨tau.trans sigma, posAffineComp S T, ?_⟩
  funext i
  calc
    w i = S.map (u (tau i)) := congrFun hw i
    _ = S.map (T.map (v (sigma (tau i)))) := by
      rw [congrFun hu (tau i)]
    _ = (posAffineComp S T).map (v (sigma (tau i))) :=
      (posAffineComp_map S T _).symm
    _ = (posAffineComp S T).map (v ((tau.trans sigma) i)) := by
      rfl

/-! ## Pointwise upper bounds -/

theorem heilbronn_convex_three_upper_bound
    (p : Fin 3 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v3 := by
  simpa [v3] using (HeilbronnChallenge.minTri_three_eq_two p hvol).le

theorem heilbronn_convex_four_upper_bound
    (p : Fin 4 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v4 := by
  simpa [v4] using HeilbronnChallenge.minTri_four_le_one p hvol

theorem heilbronn_convex_five_upper_bound
    (p : Fin 5 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v5 := by
  have hbound := Heilbronn5.upper_bound_volume p hvol
  rw [HeilbronnChallenge.minTri_eq_five,
    HeilbronnChallenge.tau_eq_v5] at hbound
  linarith

/-! ## Pairwise optimizer uniqueness -/

theorem heilbronn_convex_three_unique
    (p q : Fin 3 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v3) (hqopt : minTri q = 2 * v3) :
    AffineEquivalent p q := by
  apply affineEquivalent_of_gaugeEquivalent
  exact gaugeEquivalent_trans
    (gaugeEquivalent_symm
      (HeilbronnChallenge.heilbronn_convex_three_unique_from_witness
        p hpvol hpopt))
    (HeilbronnChallenge.heilbronn_convex_three_unique_from_witness
      q hqvol hqopt)

theorem heilbronn_convex_four_unique
    (p q : Fin 4 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v4) (hqopt : minTri q = 2 * v4) :
    AffineEquivalent p q := by
  apply affineEquivalent_of_gaugeEquivalent
  exact gaugeEquivalent_trans
    (gaugeEquivalent_symm
      (HeilbronnChallenge.heilbronn_convex_four_unique_from_witness
        p hpvol hpopt))
    (HeilbronnChallenge.heilbronn_convex_four_unique_from_witness
      q hqvol hqopt)

theorem heilbronn_convex_five_unique
    (p q : Fin 5 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v5) (hqopt : minTri q = 2 * v5) :
    AffineEquivalent p q := by
  apply affineEquivalent_of_gaugeEquivalent
  exact gaugeEquivalent_trans
    (gaugeEquivalent_symm
      (HeilbronnChallenge.heilbronn_convex_five_unique_from_witness
        p hpvol hpopt))
    (HeilbronnChallenge.heilbronn_convex_five_unique_from_witness
      q hqvol hqopt)

end HeilbronnChallenge
