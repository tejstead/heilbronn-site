import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixLocalProductChambers
import Heilbronn8.Survivors.Join.HullSixTwoFourFiniteCensus
import Heilbronn8.Survivors.Join.HullSixTwoFourWideTableAdapter

/-!
# Exact geometry adapter for adjacent product-twelve tables

The finite census calls the adjacent `RR / LR` and `LR / LL` blocks
"currently covered", but the scalar product theorem alone is not a geometry
adapter.  This file supplies that missing seam directly in the realized
table's orientation.  It uses no table weakening and no complement symmetry.

For `RR / LR` the selected product lies in the `P` fan.  For `LR / LL` it
lies in the `Q` fan.  In either fan the opposite cross-block boundary edge is
at least `3 * minTri`: its boundary floor is augmented by the two line-level
floors under base change.  The remaining two lower boundary edges complete
the six-term fan decomposition.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

private def adjacentOther0 : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 0
  | 2 => 0

private def adjacentOther1 : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 2
  | 2 => 1

private lemma adjacentLowerEdges_perm
    (E : Fin 3 → ℝ) (j : Fin 3) :
    E 0 + E 1 + E 2 =
      E j + E (adjacentOther0 j) + E (adjacentOther1 j) := by
  fin_cases j <;> simp [adjacentOther0, adjacentOther1] <;> ring

namespace HullSixTwoFourCuts

/-- The census's two adjacent local-product families really are recognized
by the dimension-neutral adjacent-cell predicate. -/
theorem adjacentProduct_hasLocalPattern : ∀ T : HullSixTwoFourCuts,
    (T.RRLR ∨ T.LRLL) →
      HullSixTableHasLocalProductTwelvePattern T.table := by
  intro T hpattern
  rcases hpattern with hrrlr | hlrll
  · rcases hrrlr with ⟨j, h00, h01, h10, h11⟩
    refine ⟨0, 1, j.castSucc, j.succ, rfl, rfl, ?_⟩
    exact Or.inl ⟨h00, h01, h10, h11⟩
  · rcases hlrll with ⟨j, h00, h01, h10, h11⟩
    refine ⟨0, 1, j.castSucc, j.succ, rfl, rfl, ?_⟩
    exact Or.inr ⟨h00, h01, h10, h11⟩

/-- A wide table already belonging to the old finite census is in one of
the two adjacent families.  The census's separate hard table is not wide. -/
theorem wide_currentlyCovered_isAdjacent : ∀ T : HullSixTwoFourCuts,
    T.Legal → T.HasWideProductTwelve → T.CurrentlyCovered →
      T.RRLR ∨ T.LRLL := by
  letI : DecidablePred fun T : HullSixTwoFourCuts =>
      T.Legal → T.HasWideProductTwelve → T.CurrentlyCovered →
        T.RRLR ∨ T.LRLL := fun T => by
    letI : Decidable T.Legal := inferInstance
    letI : Decidable T.HasWideProductTwelve := inferInstance
    letI : Decidable T.CurrentlyCovered := inferInstance
    letI : Decidable T.RRLR := inferInstance
    letI : Decidable T.LRLL := inferInstance
    exact inferInstance
  decide

end HullSixTwoFourCuts

namespace HullSixCompactCrossChordResidual

/-- Any exact `2 x 4` table containing an adjacent product-twelve block is
impossible in a beating compact residual. -/
theorem twoFourAdjacentProductAt_false
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
    (T : HullSixTwoFourCuts)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j)))))
    (hLocal : HullSixTableHasLocalProductTwelvePattern T.table) :
    False := by
  rcases hLocal with ⟨i0, i1, j0, j1, hi, hj, hCells⟩
  have hi0 : i0 = 0 := by
    apply Fin.ext
    omega
  have hi1 : i1 = 1 := by
    apply Fin.ext
    omega
  have hj0lt : j0.val < 3 := by omega
  let j : Fin 3 := ⟨j0.val, hj0lt⟩
  have hj0 : j0 = j.castSucc := by
    apply Fin.ext
    rfl
  have hj1 : j1 = j.succ := by
    apply Fin.ext
    dsimp [j]
    omega
  have hCells' : HullSixLocalProductTwelveCells
      (T.table 0 j.castSucc) (T.table 0 j.succ)
      (T.table 1 j.castSucc) (T.table 1 j.succ) := by
    simpa [hi0, hi1, hj0, hj1] using hCells

  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun k ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset k))
  let u : Fin 2 → ℝ := fun i ↦ sig (cfg P) (cfg Q) (U i)
  let v : Fin 4 → ℝ := fun k ↦ -sig (cfg P) (cfg Q) (L k)
  let x : Fin 2 → Fin 4 → ℝ := fun i k ↦ sig (cfg P) (U i) (L k)
  let y : Fin 2 → Fin 4 → ℝ := fun i k ↦ sig (cfg Q) (U i) (L k)
  let EP : Fin 3 → ℝ := fun k ↦ sig (cfg P) (L k.castSucc) (L k.succ)
  let EQ : Fin 3 → ℝ := fun k ↦ sig (cfg Q) (L k.castSucc) (L k.succ)
  let AP := sig (cfg P) (U 0) (U 1)
  let AQ := sig (cfg Q) (U 0) (U 1)
  let CP := sig (cfg P) (U 1) (L 0)
  let CQ := sig (cfg Q) (U 1) (L 0)
  let FP := sig (cfg P) (L 3) (U 0)
  let FQ := sig (cfg Q) (L 3) (U 0)

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hu (i : Fin 2) : m ≤ u i := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset i)
    rw [abs_of_pos (hupper i)] at h
    simpa [m, u, U] using h
  have hv (k : Fin 4) : m ≤ v k := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset k)
    rw [abs_of_neg (hlower k)] at h
    simpa [m, v, L] using h
  have hbase (i : Fin 2) (k : Fin 4) :
      y i k = x i k + u i + v k := by
    have h := sig_crossChord_base_change (cfg P) (cfg Q) (U i) (L k)
    dsimp [x, y, u, v]
    linarith only [h]

  have hAP : m ≤ AP := by
    simpa [m, AP, U, hullSixTwoFourUpperOffset] using
      R.twoFour_P_boundary_floor V rotation 0
  have hAQ : m ≤ AQ := by
    simpa [m, AQ, U, hullSixTwoFourUpperOffset] using
      R.twoFour_Q_boundary_floor V rotation 0
  have hCP : m ≤ CP := by
    simpa [m, CP, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset] using
        R.twoFour_P_boundary_floor V rotation 1
  have hFQ : m ≤ FQ := by
    simpa [m, FQ, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset] using
        R.twoFour_Q_boundary_floor V rotation 5
  have hEP (k : Fin 3) : m ≤ EP k := by
    have hfloor := R.twoFour_P_boundary_floor V rotation
      (hullSixTwoFourLowerOffset k.castSucc)
    fin_cases k <;>
      simpa [m, EP, L, hullSixTwoFourLowerOffset, add_assoc] using hfloor
  have hEQ (k : Fin 3) : m ≤ EQ k := by
    have hfloor := R.twoFour_Q_boundary_floor V rotation
      (hullSixTwoFourLowerOffset k.castSucc)
    fin_cases k <;>
      simpa [m, EQ, L, hullSixTwoFourLowerOffset, add_assoc] using hfloor

  have hCQStrong : 3 * m ≤ CQ := by
    have hCQBase : CQ = CP + u 1 + v 0 := by
      simpa [CQ, CP] using hbase 1 0
    linarith [hCP, hu 1, hv 0, hCQBase]
  have hWrapBase : FQ = FP - v 3 - u 0 := by
    have h := sig_crossChord_base_change
      (cfg P) (cfg Q) (L 3) (U 0)
    dsimp [FQ, FP, u, v]
    linarith only [h]
  have hFPStrong : 3 * m ≤ FP := by
    linarith [hFQ, hu 0, hv 3, hWrapBase]

  have hPfan : doubledHullArea cfg =
      AP + CP + EP 0 + EP 1 + EP 2 + FP := by
    simpa [AP, CP, EP, FP, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset] using R.twoFour_P_fan_sum V rotation
  have hQfan : doubledHullArea cfg =
      AQ + CQ + EQ 0 + EQ 1 + EQ 2 + FQ := by
    simpa [AQ, CQ, EQ, FQ, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset] using R.twoFour_Q_fan_sum V rotation

  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin

  rcases hCells' with hRRLR | hLRLL
  · rcases hRRLR with ⟨h00, h01, h10, h11⟩
    have hPlucker :
        AP * EP j = x 0 j.castSucc * x 1 j.succ -
          x 0 j.succ * x 1 j.castSucc := by
      have h := sig_crossChord_plucker
        (cfg P) (U 0) (U 1) (L j.castSucc) (L j.succ)
      simpa [AP, EP, x] using h.symm
    have hPattern : HullSixLocalProductTwelvePattern m (AP) (EP j)
        (x 0 j.castSucc) (x 0 j.succ)
        (x 1 j.castSucc) (x 1 j.succ)
        (y 0 j.castSucc) (y 0 j.succ)
        (y 1 j.castSucc) (y 1 j.succ) := by
      apply hullSixLocalProductTwelvePattern_of_RR_LR
        (hu 0) (hu 1) (hv j.castSucc) (hv j.succ)
        (hbase 0 j.castSucc) (hbase 0 j.succ)
        (hbase 1 j.castSucc) (hbase 1 j.succ)
      · simpa [h00] using hTable 0 j.castSucc
      · simpa [h01] using hTable 0 j.succ
      · simpa [h10] using hTable 1 j.castSucc
      · simpa [h11] using hTable 1 j.succ
      · exact hPlucker
    have harea : doubledHullArea cfg =
        AP + EP j + CP + FP +
          EP (adjacentOther0 j) + EP (adjacentOther1 j) := by
      rw [hPfan]
      linarith [adjacentLowerEdges_perm EP j]
    have hwide : 25 * m < 2 * doubledHullArea cfg :=
      hullSixSixFan_finish_of_localProductTwelvePattern
        hm hAP (hEP j) hCP hFPStrong
        (hEP (adjacentOther0 j)) (hEP (adjacentOther1 j))
        harea hPattern
    nlinarith only [hwide, hcut]
  · rcases hLRLL with ⟨h00, h01, h10, h11⟩
    have hPlucker :
        AQ * EQ j = y 0 j.castSucc * y 1 j.succ -
          y 0 j.succ * y 1 j.castSucc := by
      have h := sig_crossChord_plucker
        (cfg Q) (U 0) (U 1) (L j.castSucc) (L j.succ)
      simpa [AQ, EQ, y] using h.symm
    have hPattern : HullSixLocalProductTwelvePattern m (AQ) (EQ j)
        (x 0 j.castSucc) (x 0 j.succ)
        (x 1 j.castSucc) (x 1 j.succ)
        (y 0 j.castSucc) (y 0 j.succ)
        (y 1 j.castSucc) (y 1 j.succ) := by
      apply hullSixLocalProductTwelvePattern_of_LR_LL
        (hu 0) (hu 1) (hv j.castSucc) (hv j.succ)
        (hbase 0 j.castSucc) (hbase 0 j.succ)
        (hbase 1 j.castSucc) (hbase 1 j.succ)
      · simpa [h00] using hTable 0 j.castSucc
      · simpa [h01] using hTable 0 j.succ
      · simpa [h10] using hTable 1 j.castSucc
      · simpa [h11] using hTable 1 j.succ
      · exact hPlucker
    have harea : doubledHullArea cfg =
        AQ + EQ j + FQ + CQ +
          EQ (adjacentOther0 j) + EQ (adjacentOther1 j) := by
      rw [hQfan]
      linarith [adjacentLowerEdges_perm EQ j]
    have hwide : 25 * m < 2 * doubledHullArea cfg :=
      hullSixSixFan_finish_of_localProductTwelvePattern
        hm hAQ (hEQ j) hFQ hCQStrong
        (hEQ (adjacentOther0 j)) (hEQ (adjacentOther1 j))
        harea hPattern
    nlinarith only [hwide, hcut]

/-- The two adjacent product families from the finite census are therefore
honestly closed in their exact geometric frame. -/
theorem twoFourAdjacentCensusAt_false
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
    (T : HullSixTwoFourCuts)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j)))))
    (hAdjacent : T.RRLR ∨ T.LRLL) :
    False := by
  apply R.twoFourAdjacentProductAt_false V rotation hupper hlower T hTable
  exact HullSixTwoFourCuts.adjacentProduct_hasLocalPattern T hAdjacent

/-- Every wide product-twelve table is now closed in its exact orientation:
the adjacent census cases use `twoFourAdjacentCensusAt_false`, and the eight
genuinely nonadjacent cases use the existing wide retriangulation adapter. -/
theorem twoFourAllWideAt_false
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
    (T : HullSixTwoFourCuts) (hLegal : T.Legal)
    (hWide : T.HasWideProductTwelve)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  by_cases hCurrent : T.CurrentlyCovered
  · exact R.twoFourAdjacentCensusAt_false V rotation hupper hlower T hTable
      (HullSixTwoFourCuts.wide_currentlyCovered_isAdjacent
        T hLegal hWide hCurrent)
  · exact R.twoFourNewlyWideAt_false V rotation hupper hlower
      T hLegal hWide hCurrent hTable

end HullSixCompactCrossChordResidual
end Heilbronn8
