import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixHardChamberElimination
import Heilbronn8.Survivors.Join.HullSixTwoFourFiniteCensus

/-!
# Geometry adapter for the hard `MMRR / LLMM` table

The scalar elimination for this table already lives in
`HullSixHardChamberElimination`.  This file supplies the missing exact-table
adapter.  Its five inequalities are direct four-point determinant
recurrences; no weakening, symmetry transport, or generated certificate is
used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixTwoFourCuts

private theorem hard_table00 :
    hard.table 0 0 = HullSixChamberLabel.M := by decide
private theorem hard_table01 :
    hard.table 0 1 = HullSixChamberLabel.M := by decide
private theorem hard_table02 :
    hard.table 0 2 = HullSixChamberLabel.R := by decide
private theorem hard_table03 :
    hard.table 0 3 = HullSixChamberLabel.R := by decide
private theorem hard_table10 :
    hard.table 1 0 = HullSixChamberLabel.L := by decide
private theorem hard_table11 :
    hard.table 1 1 = HullSixChamberLabel.L := by decide
private theorem hard_table12 :
    hard.table 1 2 = HullSixChamberLabel.M := by decide
private theorem hard_table13 :
    hard.table 1 3 = HullSixChamberLabel.M := by decide

end HullSixTwoFourCuts

private lemma hard_six_fan_base_change
    (P Q C0 C1 C2 C3 C4 C5 : ℝ × ℝ) :
    sig P C0 C1 + sig P C1 C2 + sig P C2 C3 +
          sig P C3 C4 + sig P C4 C5 + sig P C5 C0 =
      sig P C0 C1 + sig P C1 C2 + sig P C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 +
        sig P Q C0 - sig P Q C3 := by
  simp only [sig]
  ring

namespace HullSixCompactCrossChordResidual

/-- The exact hard `MMRR / LLMM` table is impossible in a beating oriented
`2 + 4` residual. -/
theorem twoFourHardAt_false
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
    (T : HullSixTwoFourCuts) (hHard : T.IsHard)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  have hT : T = HullSixTwoFourCuts.hard := by
    simpa [HullSixTwoFourCuts.IsHard] using hHard
  subst T

  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let a := sig (cfg P) (cfg Q) (U 0) / m
  let b := sig (cfg P) (cfg Q) (U 1) / m
  let c := -sig (cfg P) (cfg Q) (L 0) / m
  let d := -sig (cfg P) (cfg Q) (L 1) / m
  let e := -sig (cfg P) (cfg Q) (L 2) / m
  let f := -sig (cfg P) (cfg Q) (L 3) / m
  let A := sig (cfg P) (U 0) (U 1) / m
  let C := sig (cfg P) (U 1) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E1p := sig (cfg Q) (L 1) (L 2) / m
  let E2p := sig (cfg Q) (L 2) (L 3) / m
  let Dp := sig (cfg Q) (L 3) (U 0) / m
  let H := doubledHullArea cfg / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X10 := sig (cfg P) (U 1) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let X12 := sig (cfg P) (U 1) (L 2) / m
  let Y01 := sig (cfg Q) (U 0) (L 1) / m
  let Y02 := sig (cfg Q) (U 0) (L 2) / m
  let Y12 := sig (cfg Q) (U 1) (L 2) / m
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
    exact hnorm (by simpa [m, a, U] using h)
  have hb1 : 1 ≤ b := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, b, U] using h)
  have hc1 : 1 ≤ c := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 0) := by
      simpa [m, L] using h
    simpa [c] using hnorm hraw
  have hd1 : 1 ≤ d := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 1) := by
      simpa [m, L] using h
    simpa [d] using hnorm hraw
  have he1 : 1 ≤ e := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 2) := by
      simpa [m, L] using h
    simpa [e] using hnorm hraw
  have hf1 : 1 ≤ f := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 3)
    rw [abs_of_neg (hlower 3)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 3) := by
      simpa [m, L] using h
    simpa [f] using hnorm hraw
  have hE01 : 1 ≤ E0 := by
    have h := R.twoFour_P_boundary_floor V rotation 2
    exact hnorm (by simpa [m, E0, L, hullSixTwoFourLowerOffset] using h)
  have hE2p1 : 1 ≤ E2p := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2p, L, hullSixTwoFourLowerOffset] using h)

  have hM00 :
      sig (cfg P) (U 0) (L 0) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table00,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (0 : Fin 4)
  have hM01 :
      sig (cfg P) (U 0) (L 1) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table01,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (1 : Fin 4)
  have hR02 : sig (cfg Q) (U 0) (L 2) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table02,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (2 : Fin 4)
  have hL10 : m ≤ sig (cfg P) (U 1) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table10,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (0 : Fin 4)
  have hL11 : m ≤ sig (cfg P) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table11,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (1 : Fin 4)
  have hM12 :
      sig (cfg P) (U 1) (L 2) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 2) := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table12,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (2 : Fin 4)
  have hM13 :
      sig (cfg P) (U 1) (L 3) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 3) := by
    simpa [m, U, L, HullSixTwoFourCuts.hard_table13,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (3 : Fin 4)

  have hX00 : X00 ≤ -1 := hnormNeg (by simpa [X00] using hM00.1)
  have hX10 : 1 ≤ X10 := hnorm (by simpa [X10] using hL10)
  have hX11 : 1 ≤ X11 := hnorm (by simpa [X11] using hL11)
  have hX12 : X12 ≤ -1 := hnormNeg (by simpa [X12] using hM12.1)
  have hY01 : 1 ≤ Y01 := hnorm (by simpa [Y01] using hM01.2)
  have hY02 : Y02 ≤ -1 := hnormNeg (by simpa [Y02] using hR02)
  have hY12 : 1 ≤ Y12 := hnorm (by simpa [Y12] using hM12.2)
  have hY13 : 1 ≤ Y13 := hnorm (by simpa [Y13] using hM13.2)

  have hLeftRowIdentity : d * C - c * X11 = b * E0 := by
    dsimp [b, c, d, C, E0, X11]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hLeftRow : c + b * E0 ≤ d * C := by
    have hcX : c ≤ c * X11 := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one hc1)
    linarith [hLeftRowIdentity]

  have hLeftColumnIdentity : c * A = a * C - b * X00 := by
    dsimp [a, b, c, A, C, X00]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hLeftColumn : a * C + b ≤ c * A := by
    have hbX : b * X00 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hb1)
    linarith [hLeftColumnIdentity]

  have hY12Base : Y12 = X12 + b + e := by
    dsimp [Y12, X12, b, e]
    rw [sig_crossChord_base_change]
    ring
  have hY12Upper : Y12 ≤ b + e - 1 := by linarith
  have hRightRowIdentity : b * E2p = f * Y12 - e * Y13 := by
    dsimp [b, e, f, E2p, Y12, Y13]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hRightRow : b + e ≤ f * (b + e - 1) := by
    have hbE : b ≤ b * E2p := by
      simpa using mul_le_mul_of_nonneg_left hE2p1
        (le_trans zero_le_one hb1)
    have heY : e ≤ e * Y13 := by
      simpa using mul_le_mul_of_nonneg_left hY13
        (le_trans zero_le_one he1)
    have hfY : f * Y12 ≤ f * (b + e - 1) :=
      mul_le_mul_of_nonneg_left hY12Upper (le_trans zero_le_one hf1)
    linarith [hRightRowIdentity]

  have hRightColumnIdentity :
      f * Y02 + e * Dp = a * E2p := by
    dsimp [a, e, f, Y02, Dp, E2p]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hRightColumn : f + a * E2p ≤ e * Dp := by
    have hfY : f * Y02 ≤ -f := by
      simpa using mul_le_mul_of_nonneg_left hY02
        (le_trans zero_le_one hf1)
    linarith [hRightColumnIdentity]

  have hMiddleIdentity : e * Y01 - d * Y02 = a * E1p := by
    dsimp [a, d, e, Y01, Y02, E1p]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hMiddle : d + e ≤ a * E1p := by
    have heY : e ≤ e * Y01 := by
      simpa using mul_le_mul_of_nonneg_left hY01
        (le_trans zero_le_one he1)
    have hdY : d * Y02 ≤ -d := by
      simpa using mul_le_mul_of_nonneg_left hY02
        (le_trans zero_le_one hd1)
    linarith [hMiddleIdentity]

  have hFan := R.twoFour_P_fan_sum V rotation
  have hFan' :
      doubledHullArea cfg =
        sig (cfg P) (U 0) (U 1) + sig (cfg P) (U 1) (L 0) +
            sig (cfg P) (L 0) (L 1) + sig (cfg P) (L 1) (L 2) +
          sig (cfg P) (L 2) (L 3) + sig (cfg P) (L 3) (U 0) := by
    simpa [U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using hFan
  have hchange := hard_six_fan_base_change
    (cfg P) (cfg Q) (U 0) (U 1) (L 0) (L 1) (L 2) (L 3)
  have harea : H = A + C + E0 + E1p + E2p + Dp + a + d := by
    calc
      H = doubledHullArea cfg / m := by rfl
      _ = (sig (cfg P) (U 0) (U 1) + sig (cfg P) (U 1) (L 0) +
              sig (cfg P) (L 0) (L 1) + sig (cfg Q) (L 1) (L 2) +
            sig (cfg Q) (L 2) (L 3) + sig (cfg Q) (L 3) (U 0) +
              sig (cfg P) (cfg Q) (U 0) -
                sig (cfg P) (cfg Q) (L 1)) / m := by
          rw [hFan', hchange]
      _ = A + C + E0 + E1p + E2p + Dp + a + d := by
          dsimp only [A, C, E0, E1p, E2p, Dp, a, d]
          ring

  have hScalar : (25 : ℝ) / 2 < H :=
    hullSixHardChamber_finish_of_elimination
      ha1 hb1 hd1 he1 hc1 hf1 hE01 hE2p1 harea
      hLeftRow hLeftColumn hRightRow hRightColumn hMiddle
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
end Heilbronn8
