import Heilbronn8.Survivors.Join.HullSixTwoFourP11Y13NegScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ24UniversalScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# The maximal-q `p = (1,1)` partial frontier

The partial `X` frontier fixes `X00,X10 >= m` and `X11 <= -m`.
The residual absolute floor for `Y13` is then split honestly.  Its negative
half is closed by `hullSixTwoFourP11Y13Neg_orderedCore`; its positive half
is exactly the universal q24 scalar packet.  No exact table or `Y02` sign is
assumed.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The one maximal-q frontier record with first cuts `p = (1,1)`. -/
def HullSixTwoFourIsP11MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 1 ∧ T.p1 = 1

namespace HullSixCompactCrossChordResidual

/-- The `p = (1,1)` partial `X` frontier is incompatible with a beating
oriented `2 + 4` view. -/
theorem twoFourP11MaximalQAt_false
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
    (T : HullSixTwoFourCuts) (hp0 : T.p0 = 1) (hp1 : T.p1 = 1)
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
  let Ap := sig (cfg Q) (U 0) (U 1) / m
  let C := sig (cfg P) (U 1) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E0p := sig (cfg Q) (L 0) (L 1) / m
  let E1 := sig (cfg P) (L 1) (L 2) / m
  let E1p := sig (cfg Q) (L 1) (L 2) / m
  let E2 := sig (cfg P) (L 2) (L 3) / m
  let E2p := sig (cfg Q) (L 2) (L 3) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X10 := sig (cfg P) (U 1) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let Y13 := sig (cfg Q) (U 1) (L 3) / m
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
  have hAp1 : 1 ≤ Ap := by
    have h := R.twoFour_Q_boundary_floor V rotation 0
    exact hnorm (by simpa [m, Ap, U, hullSixTwoFourUpperOffset] using h)
  have hC1 : 1 ≤ C := by
    have h := R.twoFour_P_boundary_floor V rotation 1
    exact hnorm (by simpa [m, C, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)
  have hE01 : 1 ≤ E0 := by
    have h := R.twoFour_P_boundary_floor V rotation 2
    exact hnorm (by simpa [m, E0, L, hullSixTwoFourLowerOffset] using h)
  have hE0p1 : 1 ≤ E0p := by
    have h := R.twoFour_Q_boundary_floor V rotation 2
    exact hnorm (by simpa [m, E0p, L, hullSixTwoFourLowerOffset] using h)
  have hE11 : 1 ≤ E1 := by
    have h := R.twoFour_P_boundary_floor V rotation 3
    exact hnorm (by simpa [m, E1, L, hullSixTwoFourLowerOffset] using h)
  have hE1p1 : 1 ≤ E1p := by
    have h := R.twoFour_Q_boundary_floor V rotation 3
    exact hnorm (by simpa [m, E1p, L, hullSixTwoFourLowerOffset] using h)
  have hE21 : 1 ≤ E2 := by
    have h := R.twoFour_P_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2, L, hullSixTwoFourLowerOffset] using h)
  have hE2p1 : 1 ≤ E2p := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2p, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00Raw : m ≤ sig (cfg P) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp0] using
      hLeft (0 : Fin 2) (0 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp0])
  have hX10Raw : m ≤ sig (cfg P) (U 1) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (0 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp1])
  have hX11Raw : sig (cfg P) (U 1) (L 1) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hNegative (1 : Fin 2) (1 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp1])
  have hX00 : 1 ≤ X00 := hnorm (by simpa [X00] using hX00Raw)
  have hX10 : 1 ≤ X10 := hnorm (by simpa [X10] using hX10Raw)
  have hX11 : X11 ≤ -1 := hnormNeg (by simpa [X11] using hX11Raw)

  have hCIdentity : a * C = c * A + b * X00 := by
    dsimp [a, b, c, A, C, X00,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hCTransition : b + 1 ≤ a * C := by
    rw [hCIdentity]
    have hcA : 1 ≤ c * A := by
      have hmul := mul_le_mul hc1 hA1 (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans zero_le_one hc1)
      norm_num at hmul ⊢
      exact hmul
    have hbX : b ≤ b * X00 := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hb1)
    linarith
  have hE0Identity : b * E0 = d * X10 - c * X11 := by
    dsimp [b, c, d, E0, X10, X11,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE0Transition : d * C + 1 ≤ b * E0 := by
    have hXC : X10 = C := rfl
    rw [hE0Identity, hXC]
    have hcX : c * X11 ≤ -c := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one hc1)
    linarith
  have hFpIdentity : b * Fp = f * Ap - a * Y13 := by
    dsimp [a, b, f, Ap, Fp, Y13,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring

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
  have hPEar0Identity :
      (d - c) * E1 + (d - e) * E0 = d * ear0 := by
    dsimp [c, d, e, E0, E1, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hQEar0Identity :
      (d - e) * E0p + (d - c) * E1p = d * ear0 := by
    dsimp [c, d, e, E0p, E1p, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hPEar1Identity :
      (e - f) * E1 + (e - d) * E2 = e * ear1 := by
    dsimp [d, e, f, E1, E2, ear1, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hQEar1Identity :
      (e - f) * E1p + (e - d) * E2p = e * ear1 := by
    dsimp [d, e, f, E1p, E2p, ear1, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hPEar0 : d ≤ (d - c) * E1 + (d - e) * E0 := by
    rw [hPEar0Identity]
    simpa using mul_le_mul_of_nonneg_left hEar0Floor
      (le_trans zero_le_one hd1)
  have hQEar0 : d ≤ (d - e) * E0p + (d - c) * E1p := by
    rw [hQEar0Identity]
    simpa using mul_le_mul_of_nonneg_left hEar0Floor
      (le_trans zero_le_one hd1)
  have hPEar1 : e ≤ (e - f) * E1 + (e - d) * E2 := by
    rw [hPEar1Identity]
    simpa using mul_le_mul_of_nonneg_left hEar1Floor
      (le_trans zero_le_one he1)
  have hQEar1 : e ≤ (e - f) * E1p + (e - d) * E2p := by
    rw [hQEar1Identity]
    simpa using mul_le_mul_of_nonneg_left hEar1Floor
      (le_trans zero_le_one he1)

  have hE2pBase : E2p = E2 - e + f := by
    dsimp [E2p, E2, e, f, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hH1 : H = a + e + A + C + E0 + E1 + E2p + Fp := by
    have hFan := R.twoFour_P_fan_sum V rotation
    dsimp [H]
    rw [hFan]
    dsimp [a, e, A, C, E0, E1, E2p, Fp,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
      U, L, hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hH2 : H = b + d + Ap + C + E0 + E1p + E2p + Fp := by
    have hFan := R.twoFour_Q_fan_sum V rotation
    dsimp [H]
    rw [hFan]
    dsimp [b, d, Ap, C, E0, E1p, E2p, Fp,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
      U, L, hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hHQ24 : H = Ap + b + f + E0 + E1 + E2 + C + Fp := by
    have hFan := R.twoFour_Q_fan_sum V rotation
    dsimp [H]
    rw [hFan]
    dsimp [Ap, b, f, E0, E1, E2, C, Fp,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
      U, L, hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring

  have hClose : (25 : ℝ) / 2 < H → False := by
    intro hNorm
    have hwide : 25 * m < 2 * doubledHullArea cfg := by
      dsimp [H] at hNorm
      have hscaled : (25 : ℝ) / 2 * m < doubledHullArea cfg :=
        (lt_div_iff₀ hm).1 hNorm
      nlinarith
    have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
      change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
      exact R.cut_margin
    nlinarith only [hwide, hcut]

  have hU1Q : Q ≠ cycle (rotation + hullSixTwoFourUpperOffset 1) := by
    intro h
    exact V.Q_outside ⟨rotation + hullSixTwoFourUpperOffset 1, h.symm⟩
  have hL3Q : Q ≠ cycle (rotation + hullSixTwoFourLowerOffset 3) := by
    intro h
    exact V.Q_outside ⟨rotation + hullSixTwoFourLowerOffset 3, h.symm⟩
  have hU1L3 :
      cycle (rotation + hullSixTwoFourUpperOffset 1) ≠
        cycle (rotation + hullSixTwoFourLowerOffset 3) := by
    apply R.cycle_injective.ne
    fin_cases rotation <;> decide
  have hY13FloorRaw :
      m ≤ |sig (cfg Q) (U 1) (L 3)| := by
    simpa [m, U, L] using minTri_le_abs_sig_of_pairwise_ne cfg
      hU1Q hL3Q hU1L3
  have hY13Abs : 1 ≤ |Y13| := by
    have h := hnorm hY13FloorRaw
    dsimp [Y13]
    rw [abs_div, abs_of_pos hm]
    exact h

  by_cases hY13nonneg : 0 ≤ Y13
  · have hY13pos : 1 ≤ Y13 := by
      rw [abs_of_nonneg hY13nonneg] at hY13Abs
      exact hY13Abs
    have hApTransition : 1 + b ≤ f * Ap := by
      have hbFp : b ≤ b * Fp := by
        simpa using mul_le_mul_of_nonneg_left hFp1
          (le_trans zero_le_one hb1)
      have haY : a ≤ a * Y13 := by
        simpa using mul_le_mul_of_nonneg_left hY13pos
          (le_trans zero_le_one ha1)
      linarith [hFpIdentity]
    have hE0TransitionQ24 : 1 + d ≤ b * E0 := by
      have hdC : d ≤ d * C := by
        simpa using mul_le_mul_of_nonneg_left hC1
          (le_trans zero_le_one hd1)
      linarith [hE0Transition]
    have hEar0Q24 : d ≤ (d - e) * E0 + (d - 1) * E1 := by
      have hcoef : d - c ≤ d - 1 := by linarith
      have hmul : (d - c) * E1 ≤ (d - 1) * E1 :=
        mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one hE11)
      nlinarith [hPEar0]
    have hQ : 1 ≤ E2 - e + f := by
      rw [← hE2pBase]
      exact hE2p1
    have hScalar := Heilbronn8.hullSixTwoFourQBlindQ24Universal_scalar
      hb1 hd1 he1 hf1 hAp1 hE01 hE11 hE21 hQ hEar0Q24 hPEar1
        hApTransition hE0TransitionQ24
    apply hClose
    rw [hHQ24]
    nlinarith
  · have hY13neg : Y13 ≤ -1 := by
      have hnonpos : Y13 ≤ 0 := le_of_not_ge hY13nonneg
      rw [abs_of_nonpos hnonpos] at hY13Abs
      linarith
    have hFpTransition : a + 1 ≤ b * Fp := by
      rw [hFpIdentity]
      have hfAp : 1 ≤ f * Ap := by
        have hmul := mul_le_mul hf1 hAp1 (by norm_num : (0 : ℝ) ≤ 1)
          (le_trans zero_le_one hf1)
        norm_num at hmul ⊢
        exact hmul
      have haY : a * Y13 ≤ -a := by
        simpa using mul_le_mul_of_nonneg_left hY13neg
          (le_trans zero_le_one ha1)
      linarith
    by_cases hde : d ≤ e
    · have hE1Reduced : d ≤ (d - 1) * E1 := by
        have hneg : (d - e) * E0 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hde)
            (le_trans zero_le_one hE01)
        have hcoef : d - c ≤ d - 1 := by linarith
        have hmul : (d - c) * E1 ≤ (d - 1) * E1 :=
          mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one hE11)
        nlinarith [hPEar0]
      have hE1pReduced : d ≤ (d - 1) * E1p := by
        have hneg : (d - e) * E0p ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hde)
            (le_trans zero_le_one hE0p1)
        have hcoef : d - c ≤ d - 1 := by linarith
        have hmul : (d - c) * E1p ≤ (d - 1) * E1p :=
          mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one hE1p1)
        nlinarith [hQEar0]
      have hd : 1 < d := by
        by_contra hnot
        have hdle : d ≤ 1 := le_of_not_gt hnot
        have hmul : (d - 1) * E1 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdle)
            (le_trans zero_le_one hE11)
        linarith [hd1, hE1Reduced]
      have hE1Ratio : d / (d - 1) ≤ E1 := by
        exact (div_le_iff₀ (sub_pos.mpr hd)).2
          (by simpa [mul_comm] using hE1Reduced)
      have hE1pRatio : d / (d - 1) ≤ E1p := by
        exact (div_le_iff₀ (sub_pos.mpr hd)).2
          (by simpa [mul_comm] using hE1pReduced)
      by_cases hba : b ≤ a
      · have hHLow : a + d + 2 + C + E0 + E1 + Fp ≤ H := by
          rw [hH1]
          nlinarith
        exact hClose (hullSixTwoFourP11Y13Neg_orderedCore
          (lt_of_lt_of_le zero_lt_one ha1)
          (lt_of_lt_of_le zero_lt_one hb1) hd le_rfl hba
          hCTransition hE0Transition hFpTransition hE1Ratio hHLow)
      · have hab : a ≤ b := le_of_lt (lt_of_not_ge hba)
        have hHLow : b + d + 2 + C + E0 + E1p + Fp ≤ H := by
          rw [hH2]
          nlinarith
        exact hClose (hullSixTwoFourP11Y13Neg_orderedCore
          (lt_of_lt_of_le zero_lt_one ha1)
          (lt_of_lt_of_le zero_lt_one hb1) hd hab le_rfl
          hCTransition hE0Transition hFpTransition hE1pRatio hHLow)
    · have hed : e < d := lt_of_not_ge hde
      have hE1Reduced : e ≤ (e - 1) * E1 := by
        have hneg : (e - d) * E2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_lt hed))
            (le_trans zero_le_one hE21)
        have hcoef : e - f ≤ e - 1 := by linarith
        have hmul : (e - f) * E1 ≤ (e - 1) * E1 :=
          mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one hE11)
        nlinarith [hPEar1]
      have hE1pReduced : e ≤ (e - 1) * E1p := by
        have hneg : (e - d) * E2p ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_lt hed))
            (le_trans zero_le_one hE2p1)
        have hcoef : e - f ≤ e - 1 := by linarith
        have hmul : (e - f) * E1p ≤ (e - 1) * E1p :=
          mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one hE1p1)
        nlinarith [hQEar1]
      have he : 1 < e := by
        by_contra hnot
        have hele : e ≤ 1 := le_of_not_gt hnot
        have hmul : (e - 1) * E1 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hele)
            (le_trans zero_le_one hE11)
        linarith [he1, hE1Reduced]
      have hE1Ratio : e / (e - 1) ≤ E1 := by
        exact (div_le_iff₀ (sub_pos.mpr he)).2
          (by simpa [mul_comm] using hE1Reduced)
      have hE1pRatio : e / (e - 1) ≤ E1p := by
        exact (div_le_iff₀ (sub_pos.mpr he)).2
          (by simpa [mul_comm] using hE1pReduced)
      have hE0e : e * C + 1 ≤ b * E0 := by
        have hmul : e * C ≤ d * C :=
          mul_le_mul_of_nonneg_right (le_of_lt hed)
            (le_trans zero_le_one hC1)
        linarith [hE0Transition]
      by_cases hba : b ≤ a
      · have hHLow : a + e + 2 + C + E0 + E1 + Fp ≤ H := by
          rw [hH1]
          nlinarith
        exact hClose (hullSixTwoFourP11Y13Neg_orderedCore
          (lt_of_lt_of_le zero_lt_one ha1)
          (lt_of_lt_of_le zero_lt_one hb1) he le_rfl hba
          hCTransition hE0e hFpTransition hE1Ratio hHLow)
      · have hab : a ≤ b := le_of_lt (lt_of_not_ge hba)
        have hHLow : b + e + 2 + C + E0 + E1p + Fp ≤ H := by
          rw [hH2]
          nlinarith
        exact hClose (hullSixTwoFourP11Y13Neg_orderedCore
          (lt_of_lt_of_le zero_lt_one ha1)
          (lt_of_lt_of_le zero_lt_one hb1) he hab le_rfl
          hCTransition hE0e hFpTransition hE1pRatio hHLow)

end HullSixCompactCrossChordResidual

/-- Global provider for the maximal-q `p = (1,1)` fibre. -/
theorem hullSixTwoFourP11MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider HullSixTwoFourIsP11MaximalQFrontier := by
  intro cfg cycle p q R F T hLegal hPacket hFrontier
  change HullSixQBlindFrontierHolds T.p T.q (minTri cfg)
    (fun i j =>
      sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j)))) at hFrontier
  exact R.twoFourP11MaximalQAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hPacket.2.1 hPacket.2.2
      hFrontier

end Heilbronn8
