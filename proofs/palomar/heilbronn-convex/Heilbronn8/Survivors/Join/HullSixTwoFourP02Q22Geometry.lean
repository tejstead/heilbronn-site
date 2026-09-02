import Heilbronn8.Survivors.Join.HullSixTwoFourP02Q22Scalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# Exact geometry adapter for `p = 02`, `q = 22`

The table is `MMRR / LLRR`.  This adapter reads only `X00 <= -m`,
`X11 >= m`, and `Y12 <= -m` from that table.  In particular it does not use
any hidden sign of `Y00`, `Y01`, or `Y02`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The exact `p02/q22` cut record. -/
def HullSixTwoFourP02Q22Cuts : HullSixTwoFourCuts := ⟨0, 2, 2, 2⟩

namespace HullSixTwoFourCuts

private theorem p02q22_table00 :
    HullSixTwoFourP02Q22Cuts.table 0 0 = HullSixChamberLabel.M := by
  decide

private theorem p02q22_table11 :
    HullSixTwoFourP02Q22Cuts.table 1 1 = HullSixChamberLabel.L := by
  decide

private theorem p02q22_table12 :
    HullSixTwoFourP02Q22Cuts.table 1 2 = HullSixChamberLabel.R := by
  decide

end HullSixTwoFourCuts

namespace HullSixCompactCrossChordResidual

/-- The exact `MMRR / LLRR` packet is impossible in a beating normalized
`2 + 4` frame. -/
theorem twoFourP02Q22At_false
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
        (HullSixTwoFourP02Q22Cuts.table i j) (minTri cfg)
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
  let E1 := sig (cfg P) (L 1) (L 2) / m
  let E2 := sig (cfg P) (L 2) (L 3) / m
  let F := sig (cfg P) (L 3) (U 0) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let X12 := sig (cfg P) (U 1) (L 2) / m
  let Y12 := sig (cfg Q) (U 1) (L 2) / m

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
  have hE01 : 1 ≤ E0 := by
    have h := R.twoFour_P_boundary_floor V rotation 2
    exact hnorm (by simpa [m, E0, L, hullSixTwoFourLowerOffset] using h)
  have hE21 : 1 ≤ E2 := by
    have h := R.twoFour_P_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  have hM00 :
      sig (cfg P) (U 0) (L 0) ≤ -m ∧
        m ≤ sig (cfg Q) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.p02q22_table00,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (0 : Fin 4)
  have hL11 : m ≤ sig (cfg P) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.p02q22_table11,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (1 : Fin 4)
  have hR12 : sig (cfg Q) (U 1) (L 2) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p02q22_table12,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (2 : Fin 4)
  have hX00 : X00 ≤ -1 := hnormNeg (by simpa [X00] using hM00.1)
  have hX11 : 1 ≤ X11 := hnorm (by simpa [X11] using hL11)
  have hY12 : Y12 ≤ -1 := hnormNeg (by simpa [Y12] using hR12)

  have hFpBase : Fp = F - a - f := by
    dsimp [Fp, F, a, f, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hFcap : a + f + 1 ≤ F := by linarith
  have hY12Base : Y12 = X12 + b + e := by
    dsimp [Y12, X12, b, e, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hX12Strong : X12 ≤ -(b + e + 1) := by
    linarith
  have hAIdentity : c * A = a * C - b * X00 := by
    dsimp [a, b, c, A, C, X00,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hARec : a * C + b ≤ c * A := by
    rw [hAIdentity]
    have hbX : b * X00 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hb1)
    linarith
  have hCIdentity : d * C = b * E0 + c * X11 := by
    dsimp [b, c, d, C, E0, X11,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hCRec : b * E0 + c ≤ d * C := by
    rw [hCIdentity]
    have hcX : c ≤ c * X11 := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one hc1)
    linarith
  have hE1Identity : b * E1 = e * X11 - d * X12 := by
    dsimp [b, d, e, E1, X11, X12,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE1Rec : b * d + 2 * d + 1 ≤ b * E1 := by
    have heX : e ≤ e * X11 := by
      simpa using mul_le_mul_of_nonneg_left hX11
        (le_trans zero_le_one he1)
    have hdX : d * X12 ≤ -d * (b + e + 1) := by
      calc
        d * X12 ≤ d * (-(b + e + 1)) :=
          mul_le_mul_of_nonneg_left hX12Strong
            (le_trans zero_le_one hd1)
        _ = -d * (b + e + 1) := by ring
    have hgap : 0 ≤ (d + 1) * (e - 1) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr he1)
    rw [hE1Identity]
    nlinarith

  have hScalar := hullSixTwoFour_p02q22_scalar
    ha1 hb1 hc1 hd1 hf1 hE01 hE21 hARec hCRec hE1Rec hFcap
  have hFan := R.twoFour_P_fan_sum V rotation
  have hFanNorm : doubledHullArea cfg / m =
      A + C + E0 + E1 + E2 + F := by
    rw [hFan]
    dsimp [A, C, E0, E1, E2, F, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
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

/-- Exact-packet predicate exported for reflected consumers. -/
def HullSixTwoFourIsExactP02Q22 (T : HullSixTwoFourCuts) : Prop :=
  T = HullSixTwoFourP02Q22Cuts

/-- Global exact provider for `p02/q22`. -/
theorem hullSixTwoFourP02Q22ExactPacketProvider :
    HullSixTwoFourExactPacketProvider HullSixTwoFourIsExactP02Q22 := by
  intro cfg cycle p q R F T _hLegal hPacket hTable
  subst T
  exact R.twoFourP02Q22At_false F.view F.rotation
    F.upper_pos F.lower_neg
    (by simpa [HullSixTwoFourGeometricFrame.TableHolds] using hTable)

end Heilbronn8
