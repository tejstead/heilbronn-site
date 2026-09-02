import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ24UniversalScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCases

/-!
# Geometry and table adapter for the q-blind `q = 24` chamber

The exact table is `MMRR / LMMM`.  Its two separated transitions provide a
primed upper edge and the first unprimed lower edge.  Together with the two
lower hull ears they match the universal eight-variable q24 scalar packet.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixTwoFourCuts

private theorem qBlind24_table03 :
    qBlind24.table 0 3 = HullSixChamberLabel.R := by decide

private theorem qBlind24_table10 :
    qBlind24.table 1 0 = HullSixChamberLabel.L := by decide

private theorem qBlind24_table11 :
    qBlind24.table 1 1 = HullSixChamberLabel.M := by decide

private theorem qBlind24_table13 :
    qBlind24.table 1 3 = HullSixChamberLabel.M := by decide

end HullSixTwoFourCuts

private lemma qBlind24_q_fan_base_change_middle_four
    (P Q C0 C1 C2 C3 C4 C5 : ℝ × ℝ) :
    sig Q C0 C1 + sig Q C1 C2 + sig Q C2 C3 +
          sig Q C3 C4 + sig Q C4 C5 + sig Q C5 C0 =
      sig Q C0 C1 + sig P C1 C2 + sig P C2 C3 +
          sig P C3 C4 + sig P C4 C5 + sig Q C5 C0 +
        sig P Q C1 - sig P Q C5 := by
  simp only [sig]
  ring

namespace HullSixCompactCrossChordResidual

/-- The exact `MMRR / LMMM` q24 table is impossible in a beating oriented
`2 + 4` view. -/
theorem twoFourQBlindQ24At_false
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
        (HullSixTwoFourCuts.qBlind24.table i j) (minTri cfg)
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
  let Ap := sig (cfg Q) (U 0) (U 1) / m
  let C := sig (cfg P) (U 1) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E1 := sig (cfg P) (L 1) (L 2) / m
  let E2 := sig (cfg P) (L 2) (L 3) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X10 := sig (cfg P) (U 1) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
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

  have hR03 : sig (cfg Q) (U 0) (L 3) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind24_table03,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (3 : Fin 4)
  have hL10 : m ≤ sig (cfg P) (U 1) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind24_table10,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (0 : Fin 4)
  have hM11 :
      sig (cfg P) (U 1) (L 1) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind24_table11,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (1 : Fin 4)
  have hM13 :
      sig (cfg P) (U 1) (L 3) ≤ -m ∧
        m ≤ sig (cfg Q) (U 1) (L 3) := by
    simpa [m, U, L, HullSixTwoFourCuts.qBlind24_table13,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (3 : Fin 4)

  have hX10 : 1 ≤ X10 := hnorm (by simpa [X10] using hL10)
  have hX11 : X11 ≤ -1 := hnormNeg (by simpa [X11] using hM11.1)
  have hY03 : Y03 ≤ -1 := hnormNeg (by simpa [Y03] using hR03)
  have hY13 : 1 ≤ Y13 := hnorm (by simpa [Y13] using hM13.2)

  have hE0Identity : b * E0 = d * X10 - c * X11 := by
    dsimp [b, c, d, E0, X10, X11,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE0Transition : 1 + d ≤ b * E0 := by
    rw [hE0Identity]
    have hdX : d ≤ d * X10 := by
      simpa using mul_le_mul_of_nonneg_left hX10
        (le_trans zero_le_one hd1)
    have hcX : c * X11 ≤ -c := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one hc1)
    linarith

  have hApIdentity : f * Ap = a * Y13 - b * Y03 := by
    dsimp [a, b, f, Ap, Y03, Y13,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hApTransition : 1 + b ≤ f * Ap := by
    rw [hApIdentity]
    have haY : a ≤ a * Y13 := by
      simpa using mul_le_mul_of_nonneg_left hY13
        (le_trans zero_le_one ha1)
    have hbY : b * Y03 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hY03
        (le_trans zero_le_one hb1)
    linarith

  have hE2Base :
      sig (cfg Q) (L 2) (L 3) / m = E2 - e + f := by
    dsimp [E2, e, f, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hQ : 1 ≤ E2 - e + f := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    have hraw : 1 ≤ sig (cfg Q) (L 2) (L 3) / m :=
      hnorm (by simpa [m, L, hullSixTwoFourLowerOffset] using h)
    rwa [hE2Base] at hraw

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
    dsimp [c, d, e, E0, E1, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar1Identity :
      (e - d) * E2 - (f - e) * E1 = e * ear1 := by
    dsimp [d, e, f, E1, E2, ear1, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0Raw : d ≤ (d - c) * E1 - (e - d) * E0 := by
    have hmul : d ≤ d * ear0 := by
      simpa using mul_le_mul_of_nonneg_left hEar0Floor
        (le_trans zero_le_one hd1)
    rw [hEar0Identity]
    exact hmul
  have hEar0 : d ≤ (d - e) * E0 + (d - 1) * E1 := by
    have hcoef : d - c ≤ d - 1 := by linarith
    have hmul : (d - c) * E1 ≤ (d - 1) * E1 :=
      mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one hE11)
    nlinarith
  have hEar1Raw : e ≤ (e - d) * E2 - (f - e) * E1 := by
    have hmul : e ≤ e * ear1 := by
      simpa using mul_le_mul_of_nonneg_left hEar1Floor
        (le_trans zero_le_one he1)
    rw [hEar1Identity]
    exact hmul
  have hEar1 : e ≤ (e - f) * E1 + (e - d) * E2 := by
    nlinarith [hEar1Raw]

  have hScalar := Heilbronn8.hullSixTwoFourQBlindQ24Universal_scalar
    hb1 hd1 he1 hf1 hAp1 hE01 hE11 hE21 hQ hEar0 hEar1
      hApTransition hE0Transition
  have hFan := R.twoFour_Q_fan_sum V rotation
  have hFan' :
      doubledHullArea cfg =
        sig (cfg Q) (U 0) (U 1) + sig (cfg Q) (U 1) (L 0) +
            sig (cfg Q) (L 0) (L 1) + sig (cfg Q) (L 1) (L 2) +
          sig (cfg Q) (L 2) (L 3) + sig (cfg Q) (L 3) (U 0) := by
    simpa [U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using hFan
  have hchange := qBlind24_q_fan_base_change_middle_four
    (cfg P) (cfg Q) (U 0) (U 1) (L 0) (L 1) (L 2) (L 3)
  have hFanNorm : doubledHullArea cfg / m =
      Ap + b + f + E0 + E1 + E2 + C + Fp := by
    rw [hFan', hchange]
    dsimp only [Ap, b, f, E0, E1, E2, C, Fp,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    ring
  have hNorm : (25 : ℝ) / 2 < doubledHullArea cfg / m := by
    rw [hFanNorm]
    nlinarith
  have hwide : 25 * m < 2 * doubledHullArea cfg := by
    have hscaled : (25 : ℝ) / 2 * m < doubledHullArea cfg :=
      (lt_div_iff₀ hm).1 hNorm
    nlinarith
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hwide, hcut]

end HullSixCompactCrossChordResidual
end Heilbronn8
