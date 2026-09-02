import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourAdjacentQ12Scratch
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCases

/-!
# Geometry and table adapter for the q-blind `q = 12` chamber

This adapter wires the exact `MRRR / LMRR` table to the adjacent-q12 scalar
theorem.  The two middle-row cells are kept as the exact shared determinants
`J` and `K`; their coupling identities are not weakened into independent
transition bounds.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixTwoFourCuts

private theorem qBlind12_table00 :
    qBlind12.table 0 0 = HullSixChamberLabel.M := by decide

private theorem qBlind12_table01 :
    qBlind12.table 0 1 = HullSixChamberLabel.R := by decide

private theorem qBlind12_table11 :
    qBlind12.table 1 1 = HullSixChamberLabel.M := by decide

private theorem qBlind12_table12 :
    qBlind12.table 1 2 = HullSixChamberLabel.R := by decide

end HullSixTwoFourCuts

private lemma qBlind12_q_fan_base_change
    (P Q C0 C1 C2 C3 C4 C5 : ℝ × ℝ) :
    sig Q C0 C1 + sig Q C1 C2 + sig Q C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 =
      sig P C0 C1 + sig P C1 C2 + sig Q C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 +
        sig P Q C0 - sig P Q C2 := by
  simp only [sig]
  ring

namespace HullSixCompactCrossChordResidual

/-- The exact q12 table is impossible in a beating oriented `2 + 4` view. -/
theorem twoFourQBlindQ12At_false
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
        (HullSixTwoFourCuts.qBlind12.table i j) (minTri cfg)
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
  let x := sig (cfg Q) (L 0) (L 1) / m
  let y := sig (cfg Q) (L 1) (L 2) / m
  let z := sig (cfg Q) (L 2) (L 3) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let Y00 := sig (cfg Q) (U 0) (L 0) / m
  let Y01 := sig (cfg Q) (U 0) (L 1) / m
  let J := sig (cfg Q) (U 1) (L 1) / m
  let K := -(sig (cfg Q) (U 1) (L 2) / m)

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
  have hx1 : 1 ≤ x := by
    have h := R.twoFour_Q_boundary_floor V rotation 2
    exact hnorm (by simpa [m, x, L, hullSixTwoFourLowerOffset] using h)
  have hy1 : 1 ≤ y := by
    have h := R.twoFour_Q_boundary_floor V rotation 3
    exact hnorm (by simpa [m, y, L, hullSixTwoFourLowerOffset] using h)
  have hz1 : 1 ≤ z := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    exact hnorm (by simpa [m, z, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  have hM00 :
      sig (cfg P) (U 0) (L 0) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind12_table00,
      HullSixChamberLabel.Holds] using
        hTable (0 : Fin 2) (0 : Fin 4)
  have hY01Raw : sig (cfg Q) (U 0) (L 1) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind12_table01,
      HullSixChamberLabel.Holds] using
        hTable (0 : Fin 2) (1 : Fin 4)
  have hM11 :
      sig (cfg P) (U 1) (L 1) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind12_table11,
      HullSixChamberLabel.Holds] using
        hTable (1 : Fin 2) (1 : Fin 4)
  have hY12Raw : sig (cfg Q) (U 1) (L 2) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind12_table12,
      HullSixChamberLabel.Holds] using
        hTable (1 : Fin 2) (2 : Fin 4)

  have hX00 : X00 ≤ -1 := by
    exact hnormNeg (by simpa [X00] using hM00.1)
  have hY00 : 1 ≤ Y00 := by
    exact hnorm (by simpa [Y00] using hM00.2)
  have hY01 : Y01 ≤ -1 := by
    exact hnormNeg (by simpa [Y01] using hY01Raw)
  have hJ1 : 1 ≤ J := by
    exact hnorm (by simpa [J] using hM11.2)
  have hK1 : 1 ≤ K := by
    have hY12 : sig (cfg Q) (U 1) (L 2) / m ≤ (-1 : ℝ) :=
      hnormNeg hY12Raw
    dsimp [K]
    linarith

  have hAidentity : c * A = a * C - b * X00 := by
    dsimp [a, b, c, A, C, X00,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have haC : a ≤ a * C := by
    simpa using mul_le_mul_of_nonneg_left hC1
      (le_trans zero_le_one ha1)
  have hbX00 : b * X00 ≤ -b := by
    have h := mul_le_mul_of_nonneg_left hX00
      (le_trans zero_le_one hb1)
    simpa using h
  have hAtransition : a + b ≤ c * A := by
    rw [hAidentity]
    linarith

  have hxIdentity : a * x = d * Y00 - c * Y01 := by
    dsimp [a, c, d, x, Y00, Y01,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hdY00 : d ≤ d * Y00 := by
    simpa using mul_le_mul_of_nonneg_left hY00
      (le_trans zero_le_one hd1)
  have hcY01 : c * Y01 ≤ -c := by
    have h := mul_le_mul_of_nonneg_left hY01
      (le_trans zero_le_one hc1)
    simpa using h
  have hxtransition : c + d ≤ a * x := by
    rw [hxIdentity]
    linarith

  have hJidentity : b * x + c * J = d * (b + c + C) := by
    dsimp [b, c, d, C, x, J,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hKidentity : d * K = b * y - e * J := by
    dsimp [b, d, e, y, J, K,
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
  have hEar0Identity :
      (d - c) * y - (e - d) * x = d * ear0 := by
    dsimp [c, d, e, x, y, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar1Identity :
      (e - d) * z - (f - e) * y = e * ear1 := by
    dsimp [d, e, f, y, z, ear1, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0 : d ≤ (d - c) * y - (e - d) * x := by
    have hmul : d ≤ d * ear0 := by
      simpa using mul_le_mul_of_nonneg_left hEar0Floor
        (le_trans zero_le_one hd1)
    rw [hEar0Identity]
    exact hmul
  have hEar1 : e ≤ (e - d) * z - (f - e) * y := by
    have hmul : e ≤ e * ear1 := by
      simpa using mul_le_mul_of_nonneg_left hEar1Floor
        (le_trans zero_le_one he1)
    rw [hEar1Identity]
    exact hmul

  have hScalar := Survivors.Join.hullSixTwoFour_q12_scalar
    ha1 hb1 hc1 hd1 he1 hf1 hA1 hC1 hx1 hy1 hz1 hFp1 hJ1 hK1
    hAtransition hxtransition hJidentity hKidentity hEar0 hEar1
  have hFan := R.twoFour_Q_fan_sum V rotation
  have hFan' :
      doubledHullArea cfg =
        sig (cfg Q) (U 0) (U 1) + sig (cfg Q) (U 1) (L 0) +
            sig (cfg Q) (L 0) (L 1) + sig (cfg Q) (L 1) (L 2) +
          sig (cfg Q) (L 2) (L 3) + sig (cfg Q) (L 3) (U 0) := by
    simpa [U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using hFan
  have hchange := qBlind12_q_fan_base_change
    (cfg P) (cfg Q) (U 0) (U 1) (L 0) (L 1) (L 2) (L 3)
  have hFanNorm : doubledHullArea cfg / m =
      A + C + x + y + z + Fp + a + c := by
    rw [hFan', hchange]
    dsimp only [A, C, x, y, z, Fp, a, c,
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
