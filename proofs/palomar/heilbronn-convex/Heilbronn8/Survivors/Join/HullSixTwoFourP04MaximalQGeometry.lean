import Heilbronn8.Survivors.Join.HullSixTwoFourP04MaximalQScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# The maximal-q `p = (0,4)` partial frontier

This adapter decodes only the positive second `X` row.  In particular it
uses no `Q` cross-chord sign and performs no exact-table split.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The maximal-q frontier record with first cuts `p = (0,4)`. -/
def HullSixTwoFourIsP04MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 0 ∧ T.p1 = 4

namespace HullSixCompactCrossChordResidual

/-- The `p = (0,4)` partial `X` frontier is incompatible with a beating
oriented `2 + 4` view. -/
theorem twoFourP04MaximalQAt_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 2,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i))))
    (hlower : ∀ j : Fin 4,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0)
    (T : HullSixTwoFourCuts) (_hp0 : T.p0 = 0) (hp1 : T.p1 = 4)
    (hFrontier : HullSixQBlindFrontierHolds T.p T.q (minTri cfg)
      (fun i j => sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let a := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) (U 0) m
  let b := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) (U 1) m
  let c := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 0) m
  let d := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 1) m
  let e := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 2) m
  let f := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 3) m
  let A := sig (cfg P) (U 0) (U 1) / m
  let C := sig (cfg P) (U 1) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E1 := sig (cfg P) (L 1) (L 2) / m
  let E2 := sig (cfg P) (L 2) (L 3) / m
  let F := sig (cfg P) (L 3) (U 0) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let X12 := sig (cfg P) (U 1) (L 2) / m
  let X13 := sig (cfg P) (U 1) (L 3) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hnorm {s : ℝ} (hs : m ≤ s) : (1 : ℝ) ≤ s / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hs)

  have ha1 : 1 ≤ a := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, U] using h)
  have hb1 : 1 ≤ b := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, U] using h)
  have hc1 : 1 ≤ c := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 0) := by
      simpa [m, L] using h
    simpa [c, hullSixThreeThreeLowerHeight] using hnorm hraw
  have hd1 : 1 ≤ d := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 1) := by
      simpa [m, L] using h
    simpa [d, hullSixThreeThreeLowerHeight] using hnorm hraw
  have he1 : 1 ≤ e := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 2) := by
      simpa [m, L] using h
    simpa [e, hullSixThreeThreeLowerHeight] using hnorm hraw
  have hf1 : 1 ≤ f := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 3)
    rw [abs_of_neg (hlower 3)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 3) := by
      simpa [m, L] using h
    simpa [f, hullSixThreeThreeLowerHeight] using hnorm hraw

  have hA1 : 1 ≤ A := by
    have h := R.twoFour_P_boundary_floor V rotation 0
    exact hnorm (by simpa [m, A, U, hullSixTwoFourUpperOffset] using h)
  have hC1 : 1 ≤ C := by
    have h := R.twoFour_P_boundary_floor V rotation 1
    exact hnorm (by simpa [m, C, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)
  have hE01 : 1 ≤ E0 := by
    have h := R.twoFour_P_boundary_floor V rotation 2
    exact hnorm (by simpa [m, E0, L, hullSixTwoFourLowerOffset] using h)
  have hE11 : 1 ≤ E1 := by
    have h := R.twoFour_P_boundary_floor V rotation 3
    exact hnorm (by simpa [m, E1, L, hullSixTwoFourLowerOffset] using h)
  have hE21 : 1 ≤ E2 := by
    have h := R.twoFour_P_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  rcases hFrontier with ⟨hLeft, _hNegative, _hStrong⟩
  have hX11Raw : m ≤ sig (cfg P) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (1 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp1])
  have hX12Raw : m ≤ sig (cfg P) (U 1) (L 2) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (2 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp1])
  have hX13Raw : m ≤ sig (cfg P) (U 1) (L 3) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (3 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp1])
  have hX11 : 1 ≤ X11 := hnorm (by simpa [X11] using hX11Raw)
  have hX12 : 1 ≤ X12 := hnorm (by simpa [X12] using hX12Raw)
  have hX13 : 1 ≤ X13 := hnorm (by simpa [X13] using hX13Raw)

  have hFpBase : Fp = F - a - f := by
    dsimp [Fp, F, a, f, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hF : a + f + 1 ≤ F := by linarith [hFpBase, hFp1]
  have hAFIdentity : f * A = a * X13 + b * F := by
    dsimp [a, b, f, A, F, X13,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hAF : a + b * F ≤ f * A := by
    have haX : a ≤ a * X13 := by
      simpa using mul_le_mul_of_nonneg_left hX13
        (le_trans zero_le_one ha1)
    rw [hAFIdentity]
    linarith

  have hRec1 : b * E1 = e * X11 - d * X12 := by
    dsimp [b, d, e, E1, X11, X12,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hRec2 : b * E2 = f * X12 - e * X13 := by
    dsimp [b, e, f, E2, X12, X13,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring

  let ear0 := sig (L 0) (L 1) (L 2) / m
  let ear1 := sig (L 1) (L 2) (L 3) / m
  let earP := sig (U 1) (L 0) (L 1) / m
  have hEar0Floor : 1 ≤ ear0 := by
    have h := R.twoFour_hullEar_floor rotation 2
    exact hnorm (by simpa [m, ear0, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
  have hEar1Floor : 1 ≤ ear1 := by
    have h := R.twoFour_hullEar_floor rotation 3
    exact hnorm (by simpa [m, ear1, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
  have hEarPFloor : 1 ≤ earP := by
    have h := R.twoFour_hullEar_floor rotation 1
    exact hnorm (by simpa [m, earP, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using h)
  have hEar0Identity :
      (d - c) * E1 - (e - d) * E0 = d * ear0 := by
    dsimp [c, d, e, E0, E1, ear0,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar1Identity :
      (e - f) * E1 + (e - d) * E2 = e * ear1 := by
    dsimp [d, e, f, E1, E2, ear1,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEarPIdentity : C + E0 - X11 = earP := by
    dsimp [C, E0, X11, earP]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0 : d ≤ (d - c) * E1 - (e - d) * E0 := by
    rw [hEar0Identity]
    simpa using mul_le_mul_of_nonneg_left hEar0Floor
      (le_trans zero_le_one hd1)
  have hEar1 : e ≤ (e - f) * E1 + (e - d) * E2 := by
    rw [hEar1Identity]
    simpa using mul_le_mul_of_nonneg_left hEar1Floor
      (le_trans zero_le_one he1)
  have hHull : 1 ≤ C + E0 - X11 := by
    rw [hEarPIdentity]
    exact hEarPFloor

  have hE1pBase :
      sig (cfg Q) (L 1) (L 2) / m = E1 - d + e := by
    dsimp [E1, d, e, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hE2pBase :
      sig (cfg Q) (L 2) (L 3) / m = E2 - e + f := by
    dsimp [E2, e, f, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hE1p : 1 ≤ E1 - d + e := by
    have h := R.twoFour_Q_boundary_floor V rotation 3
    have hraw : 1 ≤ sig (cfg Q) (L 1) (L 2) / m :=
      hnorm (by simpa [m, L, hullSixTwoFourLowerOffset] using h)
    rwa [hE1pBase] at hraw
  have hE2p : 1 ≤ E2 - e + f := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    have hraw : 1 ≤ sig (cfg Q) (L 2) (L 3) / m :=
      hnorm (by simpa [m, L, hullSixTwoFourLowerOffset] using h)
    rwa [hE2pBase] at hraw
  have hLong : 5 ≤ E0 + E1 + E2 := by
    have h := hullSixTwoFour_longSide_sum_five
      (m := (1 : ℝ)) (v0 := c) (v1 := d) (v2 := e) (v3 := f)
      (E0 := E0) (E1 := E1) (E2 := E2)
      (by norm_num) hc1 hE01 hE11 hE21 hE1p hE2p
      (by nlinarith [hEar0])
      (by nlinarith [hEar1])
    norm_num at h ⊢
    exact h

  have hPFanNorm : H = A + C + E0 + E1 + E2 + F := by
    have hFan := R.twoFour_P_fan_sum V rotation
    dsimp [H]
    rw [hFan]
    dsimp [A, C, E0, E1, E2, F, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hScalar : (25 : ℝ) / 2 < H := by
    rw [hPFanNorm]
    exact Survivors.Join.hullSixTwoFour_p04MaximalQ_scalar
      ha1 hb1 hc1 hd1 he1 hf1 hC1 hE01 hE11 hE21 hE2p hF hAF
      hRec1 hRec2 hX13 hHull hEar0 hEar1 hLong

  have hwide : 25 * m < 2 * doubledHullArea cfg := by
    dsimp [H] at hScalar
    have hscaled : (25 : ℝ) / 2 * m < doubledHullArea cfg :=
      (lt_div_iff₀ hm).1 hScalar
    nlinarith
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hwide, hcut]

end HullSixCompactCrossChordResidual

/-- Global provider for the maximal-q `p = (0,4)` fibre. -/
theorem hullSixTwoFourP04MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider HullSixTwoFourIsP04MaximalQFrontier := by
  intro cfg cycle p q R F T hLegal hPacket hFrontier
  change HullSixQBlindFrontierHolds T.p T.q (minTri cfg)
    (fun i j =>
      sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j)))) at hFrontier
  exact R.twoFourP04MaximalQAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hPacket.2.1 hPacket.2.2
      hFrontier

end Heilbronn8
