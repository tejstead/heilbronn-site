import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindAdjacentAMGM
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCases

/-!
# Geometry and table adapter for the q-blind `q = 34` chamber

The finite bridge calls this cut record `qBlindTop`; its table is
`MMMR / LMMM`.  This adapter derives every premise of the compact q34 scalar
theorem directly from that exact table, the two lower hull ears, and the
normalized `Q`-fan sum.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixTwoFourCuts

private theorem qBlindTop_table00 :
    qBlindTop.table 0 0 = HullSixChamberLabel.M := by decide

private theorem qBlindTop_table02 :
    qBlindTop.table 0 2 = HullSixChamberLabel.M := by decide

private theorem qBlindTop_table03 :
    qBlindTop.table 0 3 = HullSixChamberLabel.R := by decide

private theorem qBlindTop_table10 :
    qBlindTop.table 1 0 = HullSixChamberLabel.L := by decide

private theorem qBlindTop_table11 :
    qBlindTop.table 1 1 = HullSixChamberLabel.M := by decide

private theorem qBlindTop_table13 :
    qBlindTop.table 1 3 = HullSixChamberLabel.M := by decide

end HullSixTwoFourCuts

private lemma qBlind34_q_fan_base_change
    (P Q C0 C1 C2 C3 C4 C5 : ℝ × ℝ) :
    sig Q C0 C1 + sig Q C1 C2 + sig Q C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 =
      sig P C0 C1 + sig P C1 C2 + sig Q C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 +
        sig P Q C0 - sig P Q C2 := by
  simp only [sig]
  ring

namespace HullSixCompactCrossChordResidual

/-- The exact `MMMR / LMMM` q-blind top table is impossible in a beating
oriented `2 + 4` view. -/
theorem twoFourQBlindQ34At_false
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
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds
        (HullSixTwoFourCuts.qBlindTop.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
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
  let w := sig (cfg Q) (L 0) (L 1) / m
  let x := sig (cfg Q) (L 1) (L 2) / m
  let y := sig (cfg Q) (L 2) (L 3) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X10 := sig (cfg P) (U 1) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let Y02 := sig (cfg Q) (U 0) (L 2) / m
  let Y03 := sig (cfg Q) (U 0) (L 3) / m
  let Y13 := sig (cfg Q) (U 1) (L 3) / m

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
  have hC1 : 1 ≤ C := by
    have h := R.twoFour_P_boundary_floor V rotation 1
    exact hnorm (by simpa [m, C, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)
  have hw1 : 1 ≤ w := by
    have h := R.twoFour_Q_boundary_floor V rotation 2
    exact hnorm (by simpa [m, w, L, hullSixTwoFourLowerOffset] using h)
  have hx1 : 1 ≤ x := by
    have h := R.twoFour_Q_boundary_floor V rotation 3
    exact hnorm (by simpa [m, x, L, hullSixTwoFourLowerOffset] using h)
  have hy1 : 1 ≤ y := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    exact hnorm (by simpa [m, y, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  have hM00 :
      sig (cfg P) (U 0) (L 0) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlindTop_table00,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (0 : Fin 4)
  have hM02 :
      sig (cfg P) (U 0) (L 2) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 2) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlindTop_table02,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (2 : Fin 4)
  have hR03 : sig (cfg Q) (U 0) (L 3) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlindTop_table03,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (3 : Fin 4)
  have hL10 : m ≤ sig (cfg P) (U 1) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlindTop_table10,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (0 : Fin 4)
  have hM11 :
      sig (cfg P) (U 1) (L 1) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlindTop_table11,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (1 : Fin 4)
  have hM13 :
      sig (cfg P) (U 1) (L 3) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 3) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlindTop_table13,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (3 : Fin 4)
  have hX00 : X00 ≤ -1 := hnormNeg (by simpa [X00] using hM00.1)
  have hX10 : 1 ≤ X10 := hnorm (by simpa [X10] using hL10)
  have hX11 : X11 ≤ -1 := hnormNeg (by simpa [X11] using hM11.1)
  have hY02 : 1 ≤ Y02 := hnorm (by simpa [Y02] using hM02.2)
  have hY03 : Y03 ≤ -1 := hnormNeg (by simpa [Y03] using hR03)
  have hY13 : 1 ≤ Y13 := hnorm (by simpa [Y13] using hM13.2)

  have hAIdentity : c * A = a * X10 - b * X00 := by
    dsimp [a, b, c, A, X10, X00,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hAtransition : a + b ≤ c * A := by
    rw [hAIdentity]
    have haX : a ≤ a * X10 := by
      simpa using mul_le_mul_of_nonneg_left hX10
        (le_trans zero_le_one ha1)
    have hbX : b * X00 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hb1)
    linarith

  have hE0Base : w = E0 - c + d := by
    dsimp [w, E0, c, d, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hWIdentity : b * E0 = d * X10 - c * X11 := by
    dsimp [b, c, d, E0, X10, X11,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hwTransitionE0 : c + d ≤ b * E0 := by
    rw [hWIdentity]
    have hdX : d ≤ d * X10 := by
      simpa using mul_le_mul_of_nonneg_left hX10
        (le_trans zero_le_one hd1)
    have hcX : c * X11 ≤ -c := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one hc1)
    linarith
  have hwTransition : c + d ≤ b * (w + c - d) := by
    have hshape : E0 = w + c - d := by linarith [hE0Base]
    rwa [hshape] at hwTransitionE0

  have hVerticalIdentity :
      f * (A + a - b) = a * Y13 - b * Y03 := by
    dsimp [a, b, f, A, Y13, Y03,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hVerticalTransition : a + b ≤ f * (A + a - b) := by
    rw [hVerticalIdentity]
    have haY : a ≤ a * Y13 := by
      simpa using mul_le_mul_of_nonneg_left hY13
        (le_trans zero_le_one ha1)
    have hbY : b * Y03 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hY03
        (le_trans zero_le_one hb1)
    linarith

  have hTopIdentity : a * y = f * Y02 - e * Y03 := by
    dsimp [a, e, f, y, Y02, Y03,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hTop : e + f ≤ a * y := by
    rw [hTopIdentity]
    have hfY : f ≤ f * Y02 := by
      simpa using mul_le_mul_of_nonneg_left hY02
        (le_trans zero_le_one hf1)
    have heY : e * Y03 ≤ -e := by
      simpa using mul_le_mul_of_nonneg_left hY03
        (le_trans zero_le_one he1)
    linarith

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
      (d - c) * x - (e - d) * w = d * ear0 := by
    dsimp [c, d, e, w, x, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar1Identity :
      (e - d) * y - (f - e) * x = e * ear1 := by
    dsimp [d, e, f, x, y, ear1, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0 : d ≤ (d - c) * x - (e - d) * w := by
    have hmul : d ≤ d * ear0 := by
      simpa using mul_le_mul_of_nonneg_left hEar0Floor
        (le_trans zero_le_one hd1)
    rw [hEar0Identity]
    exact hmul
  have hEar1 : e ≤ (e - d) * y - (f - e) * x := by
    have hmul : e ≤ e * ear1 := by
      simpa using mul_le_mul_of_nonneg_left hEar1Floor
        (le_trans zero_le_one he1)
    rw [hEar1Identity]
    exact hmul

  have hScalar := Heilbronn8.hullSixTwoFourQ34_scalar
    ha1 hb1 hc1 hd1 he1 hf1 hA1 hC1 hw1 hx1 hy1 hFp1
    hAtransition hwTransition hVerticalTransition hTop hEar0 hEar1
  have hFan := R.twoFour_Q_fan_sum V rotation
  have hFan' :
      doubledHullArea cfg =
        sig (cfg Q) (U 0) (U 1) + sig (cfg Q) (U 1) (L 0) +
            sig (cfg Q) (L 0) (L 1) + sig (cfg Q) (L 1) (L 2) +
          sig (cfg Q) (L 2) (L 3) + sig (cfg Q) (L 3) (U 0) := by
    simpa [U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using hFan
  have hchange := qBlind34_q_fan_base_change
    (cfg P) (cfg Q) (U 0) (U 1) (L 0) (L 1) (L 2) (L 3)
  have hFanNorm : doubledHullArea cfg / m =
      A + C + w + x + y + Fp + a + c := by
    rw [hFan', hchange]
    dsimp only [A, C, w, x, y, Fp, a, c,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    ring
  have hwide : 25 * m < 2 * doubledHullArea cfg := by
    rw [← hFanNorm] at hScalar
    have hscaled : (25 : ℝ) / 2 * m < doubledHullArea cfg :=
      (lt_div_iff₀ hm).1 hScalar
    nlinarith
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hwide, hcut]

end HullSixCompactCrossChordResidual
end Heilbronn8
