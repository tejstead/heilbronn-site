import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCoincidentAMGM
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCases

/-!
# Conditional geometry adapter for the coincident q22 chamber

The current compact coincident scalar theorem is one-sided.  Its exact
geometric packet is the q22 table `MMRR / LMRR`, and it additionally needs
the middle lower-height order `d <= e`.  This module records only that honest
conditional endpoint.  It deliberately does not claim closure of q22 in the
opposite height order, nor closure of the shifted q11/q33 tables.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixTwoFourCuts

private theorem qBlind22_table00 :
    qBlind22.table 0 0 = HullSixChamberLabel.M := by decide

private theorem qBlind22_table01 :
    qBlind22.table 0 1 = HullSixChamberLabel.M := by decide

private theorem qBlind22_table02 :
    qBlind22.table 0 2 = HullSixChamberLabel.R := by decide

private theorem qBlind22_table10 :
    qBlind22.table 1 0 = HullSixChamberLabel.L := by decide

private theorem qBlind22_table11 :
    qBlind22.table 1 1 = HullSixChamberLabel.M := by decide

end HullSixTwoFourCuts

private lemma qBlind22_q_fan_base_change_three
    (P Q C0 C1 C2 C3 C4 C5 : ℝ × ℝ) :
    sig Q C0 C1 + sig Q C1 C2 + sig Q C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 =
      sig P C0 C1 + sig P C1 C2 + sig P C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 +
        sig P Q C0 - sig P Q C3 := by
  simp only [sig]
  ring

namespace HullSixCompactCrossChordResidual

/-- Conditional q22 endpoint.  The explicit last premise is exactly the
normalized order `d <= e` required by the one-sided scalar theorem. -/
theorem twoFourQBlindQ22At_false_of_d_le_e
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
        (HullSixTwoFourCuts.qBlind22.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j)))))
    (hde :
      hullSixThreeThreeLowerHeight (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset 1)))
          (minTri cfg) ≤
        hullSixThreeThreeLowerHeight (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset 2)))
          (minTri cfg)) :
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
  let A := sig (cfg P) (U 0) (U 1) / m
  let C := sig (cfg P) (U 1) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E1p := sig (cfg Q) (L 1) (L 2) / m
  let E2p := sig (cfg Q) (L 2) (L 3) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X10 := sig (cfg P) (U 1) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let Y01 := sig (cfg Q) (U 0) (L 1) / m
  let Y02 := sig (cfg Q) (U 0) (L 2) / m

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
  have hde' : d ≤ e := by
    simpa [d, e, m, L] using hde

  have hC1 : 1 ≤ C := by
    have h := R.twoFour_P_boundary_floor V rotation 1
    exact hnorm (by simpa [m, C, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)
  have hE1p1 : 1 ≤ E1p := by
    have h := R.twoFour_Q_boundary_floor V rotation 3
    exact hnorm (by simpa [m, E1p, L, hullSixTwoFourLowerOffset] using h)
  have hE2p1 : 1 ≤ E2p := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2p, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)
  have hE0pBase :
      E0 + d - c = sig (cfg Q) (L 0) (L 1) / m := by
    dsimp [E0, c, d, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change
      (cfg P) (cfg Q) (L 0) (L 1)]
    ring
  have hE0p1 : 1 ≤ E0 + d - c := by
    have h := R.twoFour_Q_boundary_floor V rotation 2
    have hraw : 1 ≤ sig (cfg Q) (L 0) (L 1) / m :=
      hnorm (by simpa [m, L, hullSixTwoFourLowerOffset] using h)
    rw [hE0pBase]
    exact hraw

  have hM00 :
      sig (cfg P) (U 0) (L 0) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind22_table00,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (0 : Fin 4)
  have hM01 :
      sig (cfg P) (U 0) (L 1) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind22_table01,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (1 : Fin 4)
  have hR02 : sig (cfg Q) (U 0) (L 2) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind22_table02,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (2 : Fin 4)
  have hL10 : m ≤ sig (cfg P) (U 1) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind22_table10,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (0 : Fin 4)
  have hM11 :
      sig (cfg P) (U 1) (L 1) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind22_table11,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (1 : Fin 4)

  have hX00 : X00 ≤ -1 := hnormNeg (by simpa [X00] using hM00.1)
  have hX10 : 1 ≤ X10 := hnorm (by simpa [X10] using hL10)
  have hX11 : X11 ≤ -1 := hnormNeg (by simpa [X11] using hM11.1)
  have hY01 : 1 ≤ Y01 := hnorm (by simpa [Y01] using hM01.2)
  have hY02 : Y02 ≤ -1 := hnormNeg (by simpa [Y02] using hR02)

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

  have hE0Identity : b * E0 = d * X10 - c * X11 := by
    dsimp [b, c, d, E0, X10, X11,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE0transition : c + d ≤ b * E0 := by
    rw [hE0Identity]
    have hdX : d ≤ d * X10 := by
      simpa using mul_le_mul_of_nonneg_left hX10
        (le_trans zero_le_one hd1)
    have hcX : c * X11 ≤ -c := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one hc1)
    linarith

  have hE1Identity : a * E1p = e * Y01 - d * Y02 := by
    dsimp [a, d, e, E1p, Y01, Y02,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE1transition : d + e ≤ a * E1p := by
    rw [hE1Identity]
    have heY : e ≤ e * Y01 := by
      have he0 : 0 ≤ e := le_trans zero_le_one (hd1.trans hde')
      simpa using mul_le_mul_of_nonneg_left hY01 he0
    have hdY : d * Y02 ≤ -d := by
      simpa using mul_le_mul_of_nonneg_left hY02
        (le_trans zero_le_one hd1)
    linarith

  let ear0 := sig (L 0) (L 1) (L 2) / m
  have hEar0Floor : 1 ≤ ear0 := by
    have h := R.twoFour_hullEar_floor rotation 2
    exact hnorm (by simpa [m, ear0, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
  have hEarIdentity :
      (E1p + d - e) * (d - c) - E0 * (e - d) = d * ear0 := by
    dsimp [c, d, e, E0, E1p, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0 :
      d ≤ (E1p + d - e) * (d - c) - E0 * (e - d) := by
    have hmul : d ≤ d * ear0 := by
      simpa using mul_le_mul_of_nonneg_left hEar0Floor
        (le_trans zero_le_one hd1)
    rw [hEarIdentity]
    exact hmul

  have hScalar := Heilbronn8.hullSixTwoFourCoincident_scalar
    ha1 hb1 hc1 hd1 hde' hE1p1 hE0p1 hC1 hE2p1 hFp1
    hAtransition hE0transition hE1transition hEar0
  have hFan := R.twoFour_Q_fan_sum V rotation
  have hFan' :
      doubledHullArea cfg =
        sig (cfg Q) (U 0) (U 1) + sig (cfg Q) (U 1) (L 0) +
            sig (cfg Q) (L 0) (L 1) + sig (cfg Q) (L 1) (L 2) +
          sig (cfg Q) (L 2) (L 3) + sig (cfg Q) (L 3) (U 0) := by
    simpa [U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using hFan
  have hchange := qBlind22_q_fan_base_change_three
    (cfg P) (cfg Q) (U 0) (U 1) (L 0) (L 1) (L 2) (L 3)
  have hFanNorm : doubledHullArea cfg / m =
      A + C + E0 + E1p + E2p + Fp + a + d := by
    rw [hFan', hchange]
    dsimp only [A, C, E0, E1p, E2p, Fp, a, d,
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
