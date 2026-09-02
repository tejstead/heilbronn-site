import Heilbronn8.TriHull.HullFive210MaxFree
import Heilbronn8.CoverGeometry

/-!
# Homogeneous wrappers for the maximality-free hull-five `2 + 1` dispatch

`HullFive210MaxFree` is normalized to doubled minimum triangle area two.
This file transports its two end-zero endpoints to an arbitrary configuration
with positive `minTri`.  It is the form needed by a universal hull-custody
dispatcher, whose contradiction hypothesis supplies positivity but does not
replace the configuration by a normalized one.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private def h5ScaleFirst (r : ℝ) (p : Point) : Point :=
  (r * p.1, p.2)

private def h5ScaledConfiguration
    (r : ℝ) (v : Fin 8 → Point) : Fin 8 → Point :=
  fun i ↦ h5ScaleFirst r (v i)

private lemma sig_h5ScaleFirst (r : ℝ) (P Q R : Point) :
    sig (h5ScaleFirst r P) (h5ScaleFirst r Q) (h5ScaleFirst r R) =
      r * sig P Q R := by
  simp only [h5ScaleFirst, sig]
  ring

private lemma inTriStrict_h5ScaleFirst
    (r : ℝ) {P A B C : Point}
    (hP : InTriStrict P A B C) :
    InTriStrict (h5ScaleFirst r P)
      (h5ScaleFirst r A) (h5ScaleFirst r B) (h5ScaleFirst r C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hPe⟩ := hP
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hPe]
  simp only [h5ScaleFirst, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul]
  apply Prod.ext <;> simp <;> ring

private lemma inTriStrict_h5ScaleFirst_iff
    (r : ℝ) (hr : r ≠ 0) {P A B C : Point} :
    InTriStrict (h5ScaleFirst r P)
        (h5ScaleFirst r A) (h5ScaleFirst r B) (h5ScaleFirst r C) ↔
      InTriStrict P A B C := by
  constructor
  · intro hP
    have hback := inTriStrict_h5ScaleFirst (r⁻¹) hP
    simpa only [h5ScaleFirst, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
      using hback
  · exact inTriStrict_h5ScaleFirst r

private lemma h5Scaled_minimum
    (v : Fin 8 → Point) (hm : 0 < minTri v) :
    AllTrianglesMinAreaOne
      (h5ScaledConfiguration (2 / minTri v) v) := by
  intro i j k hij hik hjk
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  have hrpos : 0 < (2 / minTri v) := div_pos (by norm_num) hm
  have hrm : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hrm.symm
    _ ≤ (2 / minTri v) * |sig (v i) (v j) (v k)| :=
      mul_le_mul_of_nonneg_left hmin hrpos.le
    _ = |sig
        (h5ScaledConfiguration (2 / minTri v) v i)
        (h5ScaledConfiguration (2 / minTri v) v j)
        (h5ScaledConfiguration (2 / minTri v) v k)| := by
      simp only [h5ScaledConfiguration, sig_h5ScaleFirst,
        abs_mul, abs_of_pos hrpos]

private theorem unscale_hullFive_endZero_result
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (hm : 0 < minTri v)
    (hresult :
      HullFive300Cell
          (h5ScaledConfiguration (2 / minTri v) v) e ∨
        25 ≤
          sig (h5ScaledConfiguration (2 / minTri v) v (e 0))
              (h5ScaledConfiguration (2 / minTri v) v (e 1))
              (h5ScaledConfiguration (2 / minTri v) v (e 2)) +
            sig (h5ScaledConfiguration (2 / minTri v) v (e 0))
              (h5ScaledConfiguration (2 / minTri v) v (e 2))
              (h5ScaledConfiguration (2 / minTri v) v (e 3)) +
            sig (h5ScaledConfiguration (2 / minTri v) v (e 0))
              (h5ScaledConfiguration (2 / minTri v) v (e 3))
              (h5ScaledConfiguration (2 / minTri v) v (e 4))) :
    HullFive300Cell v e ∨
      minTri v * 25 ≤ 2 *
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) +
            sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let r : ℝ := 2 / minTri v
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have hr : r ≠ 0 := ne_of_gt hrpos
  rcases hresult with hcell | hbound
  · left
    have unscaleMem {p a b c : Fin 8}
        (hmem : InTriStrict
          (h5ScaledConfiguration r v p)
          (h5ScaledConfiguration r v a)
          (h5ScaledConfiguration r v b)
          (h5ScaledConfiguration r v c)) :
        InTriStrict (v p) (v a) (v b) (v c) := by
      exact (inTriStrict_h5ScaleFirst_iff r hr).1 hmem
    cases hcell with
    | central hP hQ hR =>
        exact .central (unscaleMem hP) (unscaleMem hQ) (unscaleMem hR)
    | right hP hQ hR =>
        exact .right (unscaleMem hP) (unscaleMem hQ) (unscaleMem hR)
  · right
    have hfan :
        sig (h5ScaledConfiguration r v (e 0))
              (h5ScaledConfiguration r v (e 1))
              (h5ScaledConfiguration r v (e 2)) +
            sig (h5ScaledConfiguration r v (e 0))
              (h5ScaledConfiguration r v (e 2))
              (h5ScaledConfiguration r v (e 3)) +
            sig (h5ScaledConfiguration r v (e 0))
              (h5ScaledConfiguration r v (e 3))
              (h5ScaledConfiguration r v (e 4)) =
          r * (sig (v (e 0)) (v (e 1)) (v (e 2)) +
            sig (v (e 0)) (v (e 2)) (v (e 3)) +
              sig (v (e 0)) (v (e 3)) (v (e 4))) := by
      simp only [h5ScaledConfiguration, sig_h5ScaleFirst]
      ring
    change 25 ≤
      sig (h5ScaledConfiguration r v (e 0))
          (h5ScaledConfiguration r v (e 1))
          (h5ScaledConfiguration r v (e 2)) +
        sig (h5ScaledConfiguration r v (e 0))
          (h5ScaledConfiguration r v (e 2))
          (h5ScaledConfiguration r v (e 3)) +
        sig (h5ScaledConfiguration r v (e 0))
          (h5ScaledConfiguration r v (e 3))
          (h5ScaledConfiguration r v (e 4)) at hbound
    rw [hfan] at hbound
    have hmr : minTri v * r = 2 := by
      dsimp [r]
      field_simp [ne_of_gt hm]
    calc
      minTri v * 25 ≤ minTri v *
          (r * (sig (v (e 0)) (v (e 1)) (v (e 2)) +
            sig (v (e 0)) (v (e 2)) (v (e 3)) +
              sig (v (e 0)) (v (e 3)) (v (e 4)))) :=
        mul_le_mul_of_nonneg_left hbound hm.le
      _ = 2 * (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) +
            sig (v (e 0)) (v (e 3)) (v (e 4))) := by
        rw [← mul_assoc, hmr]

/-- Homogeneous `ABX,ABX,AXC` end-zero dispatcher. -/
theorem hullFive_endZero_ax_major_dispatch_210_minTri_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hACD : 0 < sig (v (e 0)) (v (e 3)) (v (e 4)))
    (hPABX : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQABX : InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hRAXC : InTriStrict (v (e 7))
      (v (e 0)) (v (e 2)) (v (e 3))) :
    HullFive300Cell v e ∨
      minTri v * 25 ≤ 2 *
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) +
            sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let r : ℝ := 2 / minTri v
  let w : Fin 8 → Point := h5ScaledConfiguration r v
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have scaledPos (i j k : Fin 8)
      (hpos : 0 < sig (v i) (v j) (v k)) :
      0 < sig (w i) (w j) (w k) := by
    rw [show sig (w i) (w j) (w k) =
      r * sig (v i) (v j) (v k) by
        simp only [w, h5ScaledConfiguration, sig_h5ScaleFirst]]
    exact mul_pos hrpos hpos
  have scaledMem {p a b c : Fin 8}
      (hmem : InTriStrict (v p) (v a) (v b) (v c)) :
      InTriStrict (w p) (w a) (w b) (w c) := by
    simpa only [w, h5ScaledConfiguration] using
      inTriStrict_h5ScaleFirst r hmem
  have hwmin : AllTrianglesMinAreaOne w := by
    simpa only [w, r] using h5Scaled_minimum v hm
  have hresult := hullFive_endZero_ax_major_dispatch_210_maxFree_reindex
    w e he hwmin
      (scaledPos _ _ _ hABC) (scaledPos _ _ _ hBXC)
      (scaledPos _ _ _ hABX) (scaledPos _ _ _ hAXC)
      (scaledPos _ _ _ hACD)
      (scaledMem hPABX) (scaledMem hQABX) (scaledMem hRAXC)
  exact unscale_hullFive_endZero_result v e hm (by
    simpa only [w, r] using hresult)

/-- Homogeneous `AXC,AXC,ABX` end-zero dispatcher. -/
theorem hullFive_endZero_axc_major_dispatch_210_minTri_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hACD : 0 < sig (v (e 0)) (v (e 3)) (v (e 4)))
    (hPAXC : InTriStrict (v (e 5))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hQAXC : InTriStrict (v (e 6))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hRABX : InTriStrict (v (e 7))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    HullFive300Cell v e ∨
      minTri v * 25 ≤ 2 *
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) +
            sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let r : ℝ := 2 / minTri v
  let w : Fin 8 → Point := h5ScaledConfiguration r v
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have scaledPos (i j k : Fin 8)
      (hpos : 0 < sig (v i) (v j) (v k)) :
      0 < sig (w i) (w j) (w k) := by
    rw [show sig (w i) (w j) (w k) =
      r * sig (v i) (v j) (v k) by
        simp only [w, h5ScaledConfiguration, sig_h5ScaleFirst]]
    exact mul_pos hrpos hpos
  have scaledMem {p a b c : Fin 8}
      (hmem : InTriStrict (v p) (v a) (v b) (v c)) :
      InTriStrict (w p) (w a) (w b) (w c) := by
    simpa only [w, h5ScaledConfiguration] using
      inTriStrict_h5ScaleFirst r hmem
  have hwmin : AllTrianglesMinAreaOne w := by
    simpa only [w, r] using h5Scaled_minimum v hm
  have hresult := hullFive_endZero_axc_major_dispatch_210_maxFree_reindex
    w e he hwmin
      (scaledPos _ _ _ hABC) (scaledPos _ _ _ hBXC)
      (scaledPos _ _ _ hABX) (scaledPos _ _ _ hAXC)
      (scaledPos _ _ _ hACD)
      (scaledMem hPAXC) (scaledMem hQAXC) (scaledMem hRABX)
  exact unscale_hullFive_endZero_result v e hm (by
    simpa only [w, r] using hresult)

#print axioms hullFive_endZero_ax_major_dispatch_210_minTri_reindex
#print axioms hullFive_endZero_axc_major_dispatch_210_minTri_reindex

end Heilbronn8.TriHull
