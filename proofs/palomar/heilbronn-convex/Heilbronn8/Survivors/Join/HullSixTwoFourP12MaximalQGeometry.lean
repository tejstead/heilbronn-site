import Heilbronn8.Survivors.Join.HullSixTwoFourP12MaximalQScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# The maximal-q `p = (1,2)` partial frontier

This adapter decodes only `X00 >= 1`, `X01 <= -1`, `X11 >= 1`, and
`X12 <= -1`.  These four signs give the four transitions consumed by the
scalar closer.  No exact chamber-table information is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The maximal-q frontier record with first cuts `p = (1,2)`. -/
def HullSixTwoFourIsP12MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 1 ∧ T.p1 = 2

namespace HullSixCompactCrossChordResidual

/-- The `p = (1,2)` partial `X` frontier is incompatible with a beating
oriented `2 + 4` view. -/
theorem twoFourP12MaximalQAt_false
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
    (T : HullSixTwoFourCuts) (hp0 : T.p0 = 1) (hp1 : T.p1 = 2)
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
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X01 := sig (cfg P) (U 0) (L 1) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let X12 := sig (cfg P) (U 1) (L 2) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hnorm {s : ℝ} (hs : m ≤ s) : (1 : ℝ) ≤ s / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hs)
  have hnormNeg {s : ℝ} (hs : s ≤ -m) : s / m ≤ (-1 : ℝ) := by
    exact (div_le_iff₀ hm).2 (by simpa using hs)

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

  rcases hFrontier with ⟨hLeft, hNegative, _hStrong⟩
  have hX00Raw : m ≤ sig (cfg P) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp0] using
      hLeft (0 : Fin 2) (0 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp0])
  have hX01Raw : sig (cfg P) (U 0) (L 1) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp0] using
      hNegative (0 : Fin 2) (1 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp0])
  have hX11Raw : m ≤ sig (cfg P) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (1 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp1])
  have hX12Raw : sig (cfg P) (U 1) (L 2) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hNegative (1 : Fin 2) (2 : Fin 4)
        (by simp [HullSixTwoFourCuts.p, hp1])
  have hX00 : 1 ≤ X00 := hnorm (by simpa [X00] using hX00Raw)
  have hX01 : X01 ≤ -1 := hnormNeg (by simpa [X01] using hX01Raw)
  have hX11 : 1 ≤ X11 := hnorm (by simpa [X11] using hX11Raw)
  have hX12 : X12 ≤ -1 := hnormNeg (by simpa [X12] using hX12Raw)

  have hFpBase : Fp = F - a - f := by
    dsimp [Fp, F, a, f, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hF : a + f + 1 ≤ F := by linarith [hFpBase, hFp1]

  have hE0Identity : a * E0 = d * X00 - c * X01 := by
    dsimp [a, c, d, E0, X00, X01,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE0Transition : c + d ≤ a * E0 := by
    have hdX : d ≤ d * X00 := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hd1)
    have hcX : c * X01 ≤ -c := by
      simpa using mul_le_mul_of_nonneg_left hX01
        (le_trans zero_le_one hc1)
    linarith [hE0Identity]
  have hE1Identity : b * E1 = e * X11 - d * X12 := by
    dsimp [b, d, e, E1, X11, X12,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE1Transition : d + e ≤ b * E1 := by
    have heX : e ≤ e * X11 := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one he1)
    have hdX : d * X12 ≤ -d := by
      simpa using mul_le_mul_of_nonneg_left hX12
        (le_trans zero_le_one hd1)
    linarith [hE1Identity]
  have hAIdentity : d * A = a * X11 - b * X01 := by
    dsimp [a, b, d, A, X01, X11,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hATransition : a + b ≤ d * A := by
    have haX : a ≤ a * X11 := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one ha1)
    have hbX : b * X01 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hX01
        (le_trans zero_le_one hb1)
    linarith [hAIdentity]
  have hCIdentity : a * C = c * A + b * X00 := by
    dsimp [a, b, c, A, C, X00,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hCTransition : c * A + b ≤ a * C := by
    have hbX : b ≤ b * X00 := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hb1)
    linarith [hCIdentity]

  let ear0 := sig (L 0) (L 1) (L 2) / m
  let ear1 := sig (L 1) (L 2) (L 3) / m
  have hEar0Floor : 1 ≤ ear0 := by
    have h := R.twoFour_hullEar_floor rotation 2
    exact hnorm (by simpa [m, ear0, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
  have hEar1Floor : 1 ≤ ear1 := by
    have h := R.twoFour_hullEar_floor rotation 3
    exact hnorm (by simpa [m, ear1, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
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
  have hEar0 : d ≤ (d - c) * E1 - (e - d) * E0 := by
    rw [hEar0Identity]
    simpa using mul_le_mul_of_nonneg_left hEar0Floor
      (le_trans zero_le_one hd1)
  have hEar1 : e ≤ (e - f) * E1 + (e - d) * E2 := by
    rw [hEar1Identity]
    simpa using mul_le_mul_of_nonneg_left hEar1Floor
      (le_trans zero_le_one he1)

  have hE2pBase :
      sig (cfg Q) (L 2) (L 3) / m = E2 - e + f := by
    dsimp [E2, e, f, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hE2p : 1 ≤ E2 - e + f := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    have hraw : 1 ≤ sig (cfg Q) (L 2) (L 3) / m :=
      hnorm (by simpa [m, L, hullSixTwoFourLowerOffset] using h)
    rwa [hE2pBase] at hraw

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
    exact Survivors.Join.hullSixTwoFour_p12MaximalQ_scalar
      ha1 hb1 hc1 hd1 he1 hf1 hA1 hE01 hE11 hE21 hE2p hF
      hE0Transition hE1Transition hATransition hCTransition hEar0 hEar1

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

/-- Global provider for the maximal-q `p = (1,2)` fibre. -/
theorem hullSixTwoFourP12MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider HullSixTwoFourIsP12MaximalQFrontier := by
  intro cfg cycle p q R F T hLegal hPacket hFrontier
  change HullSixQBlindFrontierHolds T.p T.q (minTri cfg)
    (fun i j =>
      sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j)))) at hFrontier
  exact R.twoFourP12MaximalQAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hPacket.2.1 hPacket.2.2
      hFrontier

end Heilbronn8
