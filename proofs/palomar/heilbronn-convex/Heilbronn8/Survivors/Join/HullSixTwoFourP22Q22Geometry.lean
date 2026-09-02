import Heilbronn8.Survivors.Join.HullSixTwoFourP22Q22OrderedScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourReflectedCustody
import Heilbronn8.Survivors.Join.HullSixTwoFourP02Q22Geometry

/-!
# Exact geometry for the `p22/q22` packet

The ordered closer assumes that the second upper height is no larger than the
first.  It uses only three positive `X` cells and the exact negative `Y12`
cell.  The unordered exact closer physically reflects the whole frame, which
swaps the two upper vertices and preserves this self-complementary table.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-- The exact `p22/q22` cut record. -/
def HullSixTwoFourP22Q22Cuts : HullSixTwoFourCuts := ⟨2, 2, 2, 2⟩

namespace HullSixTwoFourCuts

private theorem p22q22_table00 :
    HullSixTwoFourP22Q22Cuts.table 0 0 = HullSixChamberLabel.L := by decide

private theorem p22q22_table01 :
    HullSixTwoFourP22Q22Cuts.table 0 1 = HullSixChamberLabel.L := by decide

private theorem p22q22_table11 :
    HullSixTwoFourP22Q22Cuts.table 1 1 = HullSixChamberLabel.L := by decide

private theorem p22q22_table12 :
    HullSixTwoFourP22Q22Cuts.table 1 2 = HullSixChamberLabel.R := by decide

end HullSixTwoFourCuts

namespace HullSixCompactCrossChordResidual

/-- Ordered exact `LLRR / LLRR` closure. -/
theorem twoFourP22Q22OrderedAt_false
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
    (hOrder :
      sig (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1))) ≤
        sig (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0))))
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds
        (HullSixTwoFourP22Q22Cuts.table i j) (minTri cfg)
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
  let E2p := sig (cfg Q) (L 2) (L 3) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X01 := sig (cfg P) (U 0) (L 1) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let X12 := sig (cfg P) (U 1) (L 2) / m
  let Y12 := sig (cfg Q) (U 1) (L 2) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hnorm {s : ℝ} (hs : m ≤ s) : (1 : ℝ) ≤ s / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hs)
  have hnormNeg {s : ℝ} (hs : s ≤ -m) : s / m ≤ (-1 : ℝ) := by
    exact (div_le_iff₀ hm).2 (by simpa using hs)

  have ha1 : 1 ≤ a := by
    have h := V.lineLevel_floor (rotation + hullSixTwoFourUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, U] using h)
  have hb1 : 1 ≤ b := by
    have h := V.lineLevel_floor (rotation + hullSixTwoFourUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, U] using h)
  have hc1 : 1 ≤ c := by
    have h := V.lineLevel_floor (rotation + hullSixTwoFourLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 0) := by
      simpa [m, L] using h
    simpa [c, hullSixThreeThreeLowerHeight] using hnorm hraw
  have hd1 : 1 ≤ d := by
    have h := V.lineLevel_floor (rotation + hullSixTwoFourLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 1) := by
      simpa [m, L] using h
    simpa [d, hullSixThreeThreeLowerHeight] using hnorm hraw
  have he1 : 1 ≤ e := by
    have h := V.lineLevel_floor (rotation + hullSixTwoFourLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 2) := by
      simpa [m, L] using h
    simpa [e, hullSixThreeThreeLowerHeight] using hnorm hraw
  have hf1 : 1 ≤ f := by
    have h := V.lineLevel_floor (rotation + hullSixTwoFourLowerOffset 3)
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
  have hE2p1 : 1 ≤ E2p := by
    have h := R.twoFour_Q_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2p, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  have hba : b ≤ a := by
    dsimp [a, b, hullSixThreeThreeUpperHeight]
    exact (div_le_div_iff_of_pos_right hm).2 (by simpa [U] using hOrder)

  have hL00 : m ≤ sig (cfg P) (U 0) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.p22q22_table00,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (0 : Fin 4)
  have hL01 : m ≤ sig (cfg P) (U 0) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.p22q22_table01,
      HullSixChamberLabel.Holds] using hTable (0 : Fin 2) (1 : Fin 4)
  have hL11 : m ≤ sig (cfg P) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.p22q22_table11,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (1 : Fin 4)
  have hR12 : sig (cfg Q) (U 1) (L 2) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p22q22_table12,
      HullSixChamberLabel.Holds] using hTable (1 : Fin 2) (2 : Fin 4)
  have hX00 : 1 ≤ X00 := hnorm (by simpa [X00] using hL00)
  have hX01 : 1 ≤ X01 := hnorm (by simpa [X01] using hL01)
  have hX11 : 1 ≤ X11 := hnorm (by simpa [X11] using hL11)
  have hY12 : Y12 ≤ -1 := hnormNeg (by simpa [Y12] using hR12)

  have hY12Base : Y12 = X12 + b + e := by
    dsimp [Y12, X12, b, e, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hX12Strong : X12 ≤ -(b + e + 1) := by linarith
  have hX12Three : X12 ≤ -3 := by linarith [hb1, he1]
  have hCIdentity : a * C = c * A + b * X00 := by
    dsimp [a, b, c, A, C, X00, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE0Identity : a * E0 = d * X00 - c * X01 := by
    dsimp [a, c, d, E0, X00, X01, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hE1Identity : b * E1 = e * X11 - d * X12 := by
    dsimp [b, d, e, E1, X11, X12, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring

  have hdX00 : a + c ≤ d * X00 := by
    have haE0 : a ≤ a * E0 := by
      simpa using mul_le_mul_of_nonneg_left hE01
        (le_trans (by norm_num) ha1)
    have hcX01 : c ≤ c * X01 := by
      simpa using mul_le_mul_of_nonneg_left hX01
        (le_trans (by norm_num) hc1)
    rw [hE0Identity] at haE0
    nlinarith
  have hCRec : d + a * b + b ≤ a * d * C := by
    have hcA : (1 : ℝ) ≤ c * A :=
      one_le_mul_of_one_le_of_one_le hc1 hA1
    have hdcA : d ≤ d * (c * A) := by
      simpa using mul_le_mul_of_nonneg_left hcA
        (le_trans (by norm_num) hd1)
    have hbDX : b * (a + c) ≤ b * (d * X00) :=
      mul_le_mul_of_nonneg_left hdX00 (le_trans (by norm_num) hb1)
    have hbc : b ≤ b * c := by
      simpa using mul_le_mul_of_nonneg_left hc1
        (le_trans (by norm_num) hb1)
    have hcid := congrArg (fun z : ℝ ↦ d * z) hCIdentity
    nlinarith [hcid]
  have heX : e ≤ e * X11 := by
    simpa using mul_le_mul_of_nonneg_left hX11
      (le_trans (by norm_num) he1)
  have hdX : d * X12 ≤ -3 * d := by
    have hx := mul_le_mul_of_nonneg_left hX12Three
      (le_trans (by norm_num) hd1)
    nlinarith [hx]
  have hE1Rec : e + 3 * d ≤ b * E1 := by
    rw [hE1Identity]
    nlinarith

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
      (d - c) * E1 + (d - e) * E0 = d * ear0 := by
    dsimp [c, d, e, E0, E1, ear0, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar1Identity :
      (e - f) * E1 + (e - d) * E2 = e * ear1 := by
    dsimp [d, e, f, E1, E2, ear1, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0 : d ≤ e → d ≤ (d - 1) * E1 := by
    intro hde
    have hbase : d ≤ d * ear0 := by
      simpa using mul_le_mul_of_nonneg_left hEar0Floor
        (le_trans (by norm_num) hd1)
    rw [← hEar0Identity] at hbase
    have hneg : (d - e) * E0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hde)
        (le_trans (by norm_num) hE01)
    have hmono : (d - c) * E1 ≤ (d - 1) * E1 :=
      mul_le_mul_of_nonneg_right (by linarith [hc1])
        (le_trans (by norm_num) hE11)
    linarith
  have hEar1 : e < d → e ≤ (e - 1) * E1 := by
    intro hed
    have hbase : e ≤ e * ear1 := by
      simpa using mul_le_mul_of_nonneg_left hEar1Floor
        (le_trans (by norm_num) he1)
    rw [← hEar1Identity] at hbase
    have hneg : (e - d) * E2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_lt hed)) (le_trans (by norm_num) hE21)
    have hmono : (e - f) * E1 ≤ (e - 1) * E1 :=
      mul_le_mul_of_nonneg_right (by linarith [hf1])
        (le_trans (by norm_num) hE11)
    linarith

  have hE2pBase : E2p = E2 - e + f := by
    dsimp [E2p, E2, e, f, hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hFpBase : Fp = F - a - f := by
    dsimp [Fp, F, a, f, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hFan : H = A + C + E0 + E1 + E2 + F := by
    have h := R.twoFour_P_fan_sum V rotation
    dsimp [H]
    rw [h]
    dsimp [A, C, E0, E1, E2, F, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hTail : E2 + F = a + e + E2p + Fp := by
    rw [hE2pBase, hFpBase]
    ring
  have hH : a + e + C + E1 + 4 ≤ H := by
    rw [hFan]
    nlinarith [hTail, hA1, hE01, hE2p1, hFp1]

  have hScalar := hullSixTwoFour_p22q22_ordered_scalar
    ha1 hb1 hd1 he1 hba hCRec hE1Rec hEar0 hEar1 hH
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

namespace HullSixTwoFourGeometricFrame

/-- The exact `p22/q22` packet is impossible with either ordering of the
two upper heights.  The second ordering is reduced to the first by honest
physical reflection of the whole normalized frame. -/
theorem twoFourP22Q22At_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (hTable : F.TableHolds HullSixTwoFourP22Q22Cuts) :
    False := by
  by_cases hOrder :
      sig (cfg F.P) (cfg F.Q)
          (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset 1))) ≤
        sig (cfg F.P) (cfg F.Q)
          (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset 0)))
  · exact R.twoFourP22Q22OrderedAt_false F.view F.rotation
      F.upper_pos F.lower_neg hOrder
      (by simpa [TableHolds] using hTable)
  · let F' := F.reflectedRotateComplement
    have hLegal : HullSixTwoFourP22Q22Cuts.Legal := by decide
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hLegal hTable
    have hFixed :
        HullSixTwoFourP22Q22Cuts.rotateComplement =
          HullSixTwoFourP22Q22Cuts := by
      decide
    rw [hFixed] at hReflected
    have hTable' : F'.TableHolds HullSixTwoFourP22Q22Cuts := by
      simpa [F'] using hReflected
    have hswap (i : Fin 2) :
        sig ((hullSixReflectedConfiguration cfg) F.Q)
            ((hullSixReflectedConfiguration cfg) F.P)
            ((hullSixReflectedConfiguration cfg)
              ((hullSixReflectedCycle cycle F.rotation)
                (hullSixTwoFourUpperOffset i))) =
          sig (cfg F.P) (cfg F.Q)
            (cfg (cycle
              (F.rotation + hullSixTwoFourUpperOffset
                (hullSixReverseFinTwo i)))) := by
      simp only [hullSixReflectedConfiguration, hullSixReflectedCycle]
      rw [sig_hullSixReflectionPoint_swapFirst,
        hullSixReverseAt_upperOffset]
    have hOrder' :
        sig ((hullSixReflectedConfiguration cfg) F'.P)
            ((hullSixReflectedConfiguration cfg) F'.Q)
            ((hullSixReflectedConfiguration cfg)
              ((hullSixReflectedCycle cycle F.rotation)
                (F'.rotation + hullSixTwoFourUpperOffset 1))) ≤
          sig ((hullSixReflectedConfiguration cfg) F'.P)
            ((hullSixReflectedConfiguration cfg) F'.Q)
            ((hullSixReflectedConfiguration cfg)
              ((hullSixReflectedCycle cycle F.rotation)
                (F'.rotation + hullSixTwoFourUpperOffset 0))) := by
      simp only [F', reflectedRotateComplement_P,
        reflectedRotateComplement_Q, reflectedRotateComplement_rotation,
        zero_add]
      rw [hswap 1, hswap 0]
      simpa [hullSixReverseFinTwo] using (not_le.mp hOrder).le
    exact (R.reflectReverse F.rotation).twoFourP22Q22OrderedAt_false
      F'.view F'.rotation F'.upper_pos F'.lower_neg hOrder'
      (by simpa [TableHolds] using hTable')

end HullSixTwoFourGeometricFrame

/-- Exact-packet predicate exported for reflected consumers. -/
def HullSixTwoFourIsExactP22Q22 (T : HullSixTwoFourCuts) : Prop :=
  T = HullSixTwoFourP22Q22Cuts

/-- Global exact provider for the self-reflected `p22/q22` packet. -/
theorem hullSixTwoFourP22Q22ExactPacketProvider :
    HullSixTwoFourExactPacketProvider HullSixTwoFourIsExactP22Q22 := by
  intro cfg cycle p q R F T _hLegal hPacket hTable
  subst T
  exact F.twoFourP22Q22At_false hTable

end Heilbronn8
