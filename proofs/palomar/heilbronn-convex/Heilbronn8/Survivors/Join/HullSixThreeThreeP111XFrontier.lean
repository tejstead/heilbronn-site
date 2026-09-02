import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Y22NegGeometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Q113SwapGeometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Q223Q233Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ123Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ133Geometry

/-!
# Complete maximal-q closure for the `p = 111` frontier

The maximal-X packet does not carry an exact second-cut record.  We therefore
reconstruct the honest Ferrers table from all absolute cross-chord floors,
prove that its first cuts are `111`, and kernel-enumerate the nine possible
second-cut masks.  Each mask is then sent to its exact geometric consumer.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

private def p111Mask111 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 1, 1⟩
private def p111Mask112 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 1, 2⟩
private def p111Mask113 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 1, 3⟩
private def p111Mask122 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 2, 2⟩
private def p111Mask123 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 2, 3⟩
private def p111Mask133 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 3, 3⟩
private def p111Mask222 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 2, 2, 2⟩
private def p111Mask223 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 2, 2, 3⟩
private def p111Mask233 : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 2, 3, 3⟩

private theorem p111_firstCuts_of_labels :
    forall T : HullSixThreeThreeCuts, T.Legal ->
      (forall i : Fin 3, T.table i 0 = HullSixChamberLabel.L) ->
      (forall i : Fin 3, T.table i 1 ≠ HullSixChamberLabel.L) ->
      T.p0 = 1 ∧ T.p1 = 1 ∧ T.p2 = 1 := by
  decide

private theorem p111_nineMasks :
    forall T : HullSixThreeThreeCuts, T.Legal ->
      T.p0 = 1 -> T.p1 = 1 -> T.p2 = 1 ->
      T = p111Mask111 ∨ T = p111Mask112 ∨ T = p111Mask113 ∨
      T = p111Mask122 ∨ T = p111Mask123 ∨ T = p111Mask133 ∨
      T = p111Mask222 ∨ T = p111Mask223 ∨ T = p111Mask233 := by
  decide

namespace HullSixThreeThreeGeometricFrame

/-- The first-cut triple `111` among the remaining maximal-q frontiers. -/
def IsP111RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 1 ∧ T.p1 = 1 ∧ T.p2 = 1

/-- Reconstruct the exact Y-mask and dispatch all nine possibilities. -/
theorem p111_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 1) (hp1 : T.p1 = 1) (hp2 : T.p2 = 1) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, _hStrong⟩
  let m := minTri cfg
  let U : Fin 3 -> Real × Real := fun i =>
    cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 -> Real × Real := fun j =>
    cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset j))
  let X : Fin 3 -> Fin 3 -> Real := fun i j => sig (cfg F.P) (U i) (L j)
  let Y : Fin 3 -> Fin 3 -> Real := fun i j => sig (cfg F.Q) (U i) (L j)

  have hX0 (i : Fin 3) : m <= X i 0 := by
    have h := hLeft i 0 (by
      fin_cases i <;>
        simp [HullSixThreeThreeCuts.p, hp0, hp1, hp2])
    simpa [m, X, U, L, HullSixThreeThreeGeometricFrame.X] using h
  have hX1 (i : Fin 3) : X i 1 <= -m := by
    have h := hNegative i 1 (by
      fin_cases i <;>
        simp [HullSixThreeThreeCuts.p, hp0, hp1, hp2])
    simpa [m, X, U, L, HullSixThreeThreeGeometricFrame.X] using h
  have hX21 : X 2 1 <= -m := hX1 2

  have hu (i : Fin 3) : m <= sig (cfg F.P) (cfg F.Q) (U i) := by
    have h := F.view.lineLevel_floor
      (F.rotation + hullSixThreeThreeUpperOffset i)
    rw [abs_of_pos (F.upper_pos i)] at h
    simpa [m, U] using h
  have hv (j : Fin 3) : m <= -sig (cfg F.P) (cfg F.Q) (L j) := by
    have h := F.view.lineLevel_floor
      (F.rotation + hullSixThreeThreeLowerOffset j)
    rw [abs_of_neg (F.lower_neg j)] at h
    simpa [m, L] using h
  have hbase (i j : Fin 3) :
      Y i j = X i j + sig (cfg F.P) (cfg F.Q) (U i) -
        sig (cfg F.P) (cfg F.Q) (L j) := by
    exact sig_crossChord_base_change (cfg F.P) (cfg F.Q) (U i) (L j)
  have hY0 (i : Fin 3) : m <= Y i 0 := by
    nlinarith [hX0 i, hu i, hv 0, hbase i 0, R.minTri_pos]

  obtain ⟨S, hSLegal, hSTable⟩ :=
    R.threeThreeFerrersTable_exists F.pair F.view F.rotation
      F.upper_pos F.lower_neg
  have hCol0 (i : Fin 3) : S.table i 0 = HullSixChamberLabel.L := by
    have hcell := hSTable i 0
    cases htag : S.table i 0 with
    | L => rfl
    | M =>
        rw [htag] at hcell
        simp only [HullSixChamberLabel.Holds] at hcell
        exfalso
        nlinarith [hcell.1, hX0 i, R.minTri_pos]
    | R =>
        rw [htag] at hcell
        simp only [HullSixChamberLabel.Holds] at hcell
        exfalso
        nlinarith [hY0 i, R.minTri_pos]
  have hCol1 (i : Fin 3) : S.table i 1 ≠ HullSixChamberLabel.L := by
    intro htag
    have hcell := hSTable i 1
    rw [htag] at hcell
    simp only [HullSixChamberLabel.Holds] at hcell
    nlinarith [hX1 i, R.minTri_pos]
  obtain ⟨hSp0, hSp1, hSp2⟩ :=
    p111_firstCuts_of_labels S hSLegal hCol0 hCol1
  have hMasks := p111_nineMasks S hSLegal hSp0 hSp1 hSp2

  have hX00raw : minTri cfg <= sig (cfg F.P) (U 0) (L 0) := by
    simpa [m, X] using hX0 0
  have hX10raw : minTri cfg <= sig (cfg F.P) (U 1) (L 0) := by
    simpa [m, X] using hX0 1
  have hX21raw : sig (cfg F.P) (U 2) (L 1) <= -minTri cfg := by
    simpa [m, X] using hX21

  rcases hMasks with hS | hS | hS | hS | hS | hS | hS | hS | hS
  · subst S
    have hy := hSTable 2 2
    rw [show p111Mask111.table 2 2 = HullSixChamberLabel.R by decide] at hy
    simp only [HullSixChamberLabel.Holds] at hy
    exact R.threeThreeP111Y22NegAt_false F.view F.rotation
      F.upper_pos F.lower_neg hX00raw hX10raw (by simpa [Y, U, L] using hy)
  · subst S
    have hy := hSTable 2 2
    rw [show p111Mask112.table 2 2 = HullSixChamberLabel.R by decide] at hy
    simp only [HullSixChamberLabel.Holds] at hy
    exact R.threeThreeP111Y22NegAt_false F.view F.rotation
      F.upper_pos F.lower_neg hX00raw hX10raw (by simpa [Y, U, L] using hy)
  · subst S
    have hy11 := hSTable 1 1
    have hy22 := hSTable 2 2
    rw [show p111Mask113.table 1 1 = HullSixChamberLabel.R by decide] at hy11
    rw [show p111Mask113.table 2 2 = HullSixChamberLabel.M by decide] at hy22
    simp only [HullSixChamberLabel.Holds] at hy11 hy22
    exact R.threeThreeP111Q113At_false_of_X00 F.view F.rotation
      F.upper_pos F.lower_neg hX00raw
      (by simpa [Y, U, L] using hy11)
      (by simpa [Y, U, L] using hy22.2)
  · subst S
    have hy := hSTable 2 2
    rw [show p111Mask122.table 2 2 = HullSixChamberLabel.R by decide] at hy
    simp only [HullSixChamberLabel.Holds] at hy
    exact R.threeThreeP111Y22NegAt_false F.view F.rotation
      F.upper_pos F.lower_neg hX00raw hX10raw (by simpa [Y, U, L] using hy)
  · subst S
    have hy01 := hSTable 0 1
    have hy11 := hSTable 1 1
    have hy12 := hSTable 1 2
    have hy22 := hSTable 2 2
    rw [show p111Mask123.table 0 1 = HullSixChamberLabel.R by decide] at hy01
    rw [show p111Mask123.table 1 1 = HullSixChamberLabel.M by decide] at hy11
    rw [show p111Mask123.table 1 2 = HullSixChamberLabel.R by decide] at hy12
    rw [show p111Mask123.table 2 2 = HullSixChamberLabel.M by decide] at hy22
    simp only [HullSixChamberLabel.Holds] at hy01 hy11 hy12 hy22
    exact R.threeThreeQ123At_false_of_crossFloors F.view F.rotation
      F.upper_pos F.lower_neg hX10raw hX21raw
      (by simpa [Y, U, L] using hy01)
      (by simpa [Y, U, L] using hy11.2)
      (by simpa [Y, U, L] using hy12)
      (by simpa [Y, U, L] using hy22.2)
  · subst S
    have hy01 := hSTable 0 1
    have hy12 := hSTable 1 2
    rw [show p111Mask133.table 0 1 = HullSixChamberLabel.R by decide] at hy01
    rw [show p111Mask133.table 1 2 = HullSixChamberLabel.M by decide] at hy12
    simp only [HullSixChamberLabel.Holds] at hy01 hy12
    exact R.threeThreeQ133At_false_of_crossFloors F.view F.rotation
      F.upper_pos F.lower_neg hX10raw hX21raw
      (by simpa [Y, U, L] using hy01)
      (by simpa [Y, U, L] using hy12.2)
  · subst S
    have hy := hSTable 2 2
    rw [show p111Mask222.table 2 2 = HullSixChamberLabel.R by decide] at hy
    simp only [HullSixChamberLabel.Holds] at hy
    exact R.threeThreeP111Y22NegAt_false F.view F.rotation
      F.upper_pos F.lower_neg hX00raw hX10raw (by simpa [Y, U, L] using hy)
  · subst S
    have hy01 := hSTable 0 1
    have hy12 := hSTable 1 2
    have hy22 := hSTable 2 2
    rw [show p111Mask223.table 0 1 = HullSixChamberLabel.M by decide] at hy01
    rw [show p111Mask223.table 1 2 = HullSixChamberLabel.R by decide] at hy12
    rw [show p111Mask223.table 2 2 = HullSixChamberLabel.M by decide] at hy22
    simp only [HullSixChamberLabel.Holds] at hy01 hy12 hy22
    exact R.threeThreeP111Q223At_false F.view F.rotation
      F.upper_pos F.lower_neg hX00raw hX21raw
      (by simpa [Y, U, L] using hy01.2)
      (by simpa [Y, U, L] using hy12)
      (by simpa [Y, U, L] using hy22.2)
  · subst S
    have hy02 := hSTable 0 2
    have hy12 := hSTable 1 2
    rw [show p111Mask233.table 0 2 = HullSixChamberLabel.R by decide] at hy02
    rw [show p111Mask233.table 1 2 = HullSixChamberLabel.M by decide] at hy12
    simp only [HullSixChamberLabel.Holds] at hy02 hy12
    exact R.threeThreeP111Q233At_false F.view F.rotation
      F.upper_pos F.lower_neg hX00raw hX21raw
      (by simpa [Y, U, L] using hy02)
      (by simpa [Y, U, L] using hy12.2)

end HullSixThreeThreeGeometricFrame

theorem hullSixThreeThreeP111XFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨_hRemaining, hp0, hp1, hp2⟩
  exact F.p111_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
