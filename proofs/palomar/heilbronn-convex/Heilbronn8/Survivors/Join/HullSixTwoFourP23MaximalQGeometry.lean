import Heilbronn8.Survivors.Join.HullSixTwoFourP11MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP12MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourAdjacentProductGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourReflectedCustody

/-!
# The maximal-q `p = (2,3)` frontier

The partial `X` frontier fixes every chamber except the two cells based at
`Y02` and `Y13`; the top-right `Y03` sign is the closing boundary face.
Splitting the two remaining absolute floors gives four exact tables.  Honest
physical reflection sends them respectively to

```text
MRRR / LMRR,   LRRR / LMRR,   MRRR / LLRR,   LRRR / LLRR.
```

The first and third reflect to already closed exact `p = (0,1)` and wide
packets.  The other two weaken, within their reflected frames, to the existing
maximal-q `p = (1,1)` and `p = (1,2)` frontiers.  No same-configuration
complement custody is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-- The maximal-q frontier record with first cuts `p = (2,3)`. -/
def HullSixTwoFourIsP23MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 2 ∧ T.p1 = 3

namespace HullSixTwoFourGeometricFrame

/-- The `p = (2,3)` partial `X` frontier is impossible.  Each hidden-`Y`
branch is first completed to an exact table and then transported through the
honest physically reflected frame. -/
theorem twoFourP23MaximalQAt_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (T : HullSixTwoFourCuts) (hp0 : T.p0 = 2) (hp1 : T.p1 = 3)
    (hFrontier : F.XFrontierHolds T) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j))
  let X : Fin 2 → Fin 4 → ℝ := fun i j ↦
    sig (cfg F.P) (U i) (L j)
  let Y : Fin 2 → Fin 4 → ℝ := fun i j ↦
    sig (cfg F.Q) (U i) (L j)

  have hFrontier' :
      HullSixQBlindFrontierHolds T.p T.q m F.X := by
    simpa [HullSixTwoFourGeometricFrame.XFrontierHolds, m] using hFrontier
  rcases hFrontier' with ⟨hLeft, hNegative, _hStrong⟩

  have hX00 : m ≤ X 0 0 := by
    have h := hLeft (0 : Fin 2) (0 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp0])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hX01 : m ≤ X 0 1 := by
    have h := hLeft (0 : Fin 2) (1 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp0])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hX10 : m ≤ X 1 0 := by
    have h := hLeft (1 : Fin 2) (0 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp1])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hX11 : m ≤ X 1 1 := by
    have h := hLeft (1 : Fin 2) (1 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp1])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hX12 : m ≤ X 1 2 := by
    have h := hLeft (1 : Fin 2) (2 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp1])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hX02 : X 0 2 ≤ -m := by
    have h := hNegative (0 : Fin 2) (2 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp0])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hX13 : X 1 3 ≤ -m := by
    have h := hNegative (1 : Fin 2) (3 : Fin 4)
      (by simp [HullSixTwoFourCuts.p, hp1])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h

  /- The top-right `Q` chord is the negative of the closing boundary face
  based at `Q`. -/
  have hWrap : m ≤ sig (cfg F.Q) (L 3) (U 0) := by
    have h := R.twoFour_Q_boundary_floor F.view F.rotation 5
    simpa [m, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset] using h
  have hWrapIdentity : sig (cfg F.Q) (L 3) (U 0) = -Y 0 3 := by
    dsimp [Y]
    simp only [sig]
    ring
  have hY03 : Y 0 3 ≤ -m := by
    rw [hWrapIdentity] at hWrap
    linarith

  /- The two remaining `Q` cross-chords have the ordinary absolute triangle
  floor. -/
  have hU0Q :
      F.Q ≠ cycle (F.rotation + hullSixTwoFourUpperOffset 0) := by
    intro h
    exact F.view.Q_outside
      ⟨F.rotation + hullSixTwoFourUpperOffset 0, h.symm⟩
  have hL2Q :
      F.Q ≠ cycle (F.rotation + hullSixTwoFourLowerOffset 2) := by
    intro h
    exact F.view.Q_outside
      ⟨F.rotation + hullSixTwoFourLowerOffset 2, h.symm⟩
  have hU0L2 :
      cycle (F.rotation + hullSixTwoFourUpperOffset 0) ≠
        cycle (F.rotation + hullSixTwoFourLowerOffset 2) := by
    apply R.cycle_injective.ne
    have hindices : ∀ rotation : Fin 6,
        rotation + hullSixTwoFourUpperOffset 0 ≠
          rotation + hullSixTwoFourLowerOffset 2 := by decide
    exact hindices F.rotation
  have hY02Floor : m ≤ |Y 0 2| := by
    simpa [m, Y, U, L] using minTri_le_abs_sig_of_pairwise_ne cfg
      hU0Q hL2Q hU0L2

  have hU1Q :
      F.Q ≠ cycle (F.rotation + hullSixTwoFourUpperOffset 1) := by
    intro h
    exact F.view.Q_outside
      ⟨F.rotation + hullSixTwoFourUpperOffset 1, h.symm⟩
  have hL3Q :
      F.Q ≠ cycle (F.rotation + hullSixTwoFourLowerOffset 3) := by
    intro h
    exact F.view.Q_outside
      ⟨F.rotation + hullSixTwoFourLowerOffset 3, h.symm⟩
  have hU1L3 :
      cycle (F.rotation + hullSixTwoFourUpperOffset 1) ≠
        cycle (F.rotation + hullSixTwoFourLowerOffset 3) := by
    apply R.cycle_injective.ne
    have hindices : ∀ rotation : Fin 6,
        rotation + hullSixTwoFourUpperOffset 1 ≠
          rotation + hullSixTwoFourLowerOffset 3 := by decide
    exact hindices F.rotation
  have hY13Floor : m ≤ |Y 1 3| := by
    simpa [m, Y, U, L] using minTri_le_abs_sig_of_pairwise_ne cfg
      hU1Q hL3Q hU1L3

  let F' := F.reflectedRotateComplement

  by_cases hY02nonneg : 0 ≤ Y 0 2
  · have hY02pos : m ≤ Y 0 2 := by
      rw [abs_of_nonneg hY02nonneg] at hY02Floor
      exact hY02Floor
    by_cases hY13nonneg : 0 ≤ Y 1 3
    · have hY13pos : m ≤ Y 1 3 := by
        rw [abs_of_nonneg hY13nonneg] at hY13Floor
        exact hY13Floor
      let Tpospos : HullSixTwoFourCuts := ⟨2, 3, 3, 4⟩
      let T01 : HullSixTwoFourCuts := ⟨0, 1, 1, 2⟩
      have hTposposLegal : Tpospos.Legal := by decide
      have hTablePosPos : F.TableHolds Tpospos := by
        intro i j
        fin_cases i <;> fin_cases j
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX00
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX01
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, Y, U, L] using
            And.intro hX02 hY02pos
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY03
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX10
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX11
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX12
        · simpa [Tpospos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, Y, U, L] using
            And.intro hX13 hY13pos
      have hReflected := F.tableHolds_reflectedRotateComplement
        hTposposLegal hTablePosPos
      have hRotate : Tpospos.rotateComplement = T01 := by decide
      have hTable01 : F'.TableHolds T01 := by
        rw [hRotate] at hReflected
        simpa [F'] using hReflected
      exact F'.closedP01Packet_exact T01 (by decide) (by
        exact Or.inl (Or.inl (by decide))) hTable01
    · have hY13nonpos : Y 1 3 ≤ 0 := le_of_not_ge hY13nonneg
      have hY13neg : Y 1 3 ≤ -m := by
        rw [abs_of_nonpos hY13nonpos] at hY13Floor
        linarith
      let Tposneg : HullSixTwoFourCuts := ⟨2, 3, 3, 3⟩
      let T11 : HullSixTwoFourCuts := ⟨1, 1, 1, 2⟩
      let U11 : HullSixTwoFourCuts := ⟨1, 1, 3, 4⟩
      have hTposnegLegal : Tposneg.Legal := by decide
      have hTablePosNeg : F.TableHolds Tposneg := by
        intro i j
        fin_cases i <;> fin_cases j
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX00
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX01
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, Y, U, L] using
            And.intro hX02 hY02pos
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY03
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX10
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX11
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX12
        · simpa [Tposneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY13neg
      have hReflected := F.tableHolds_reflectedRotateComplement
        hTposnegLegal hTablePosNeg
      have hRotate : Tposneg.rotateComplement = T11 := by decide
      have hTable11 : F'.TableHolds T11 := by
        rw [hRotate] at hReflected
        simpa [F'] using hReflected
      have hT11Legal : T11.Legal := by decide
      have hU11Legal : U11.Legal := by decide
      have hWeak : HullSixTwoFourCuts.Weak T11 U11 := by decide
      have hFrontier11 : F'.XFrontierHolds U11 :=
        F'.xFrontierHolds_of_table_weak hT11Legal hWeak hTable11
      have hPacket11 : HullSixTwoFourIsP11MaximalQFrontier U11 := by
        simp [HullSixTwoFourIsP11MaximalQFrontier,
          HullSixTwoFourIsMaximalQFrontier, U11]
      exact hullSixTwoFourP11MaximalQFrontierProvider
        F' U11 hU11Legal hPacket11 hFrontier11
  · have hY02nonpos : Y 0 2 ≤ 0 := le_of_not_ge hY02nonneg
    have hY02neg : Y 0 2 ≤ -m := by
      rw [abs_of_nonpos hY02nonpos] at hY02Floor
      linarith
    by_cases hY13nonneg : 0 ≤ Y 1 3
    · have hY13pos : m ≤ Y 1 3 := by
        rw [abs_of_nonneg hY13nonneg] at hY13Floor
        exact hY13Floor
      let Tnegpos : HullSixTwoFourCuts := ⟨2, 3, 2, 4⟩
      let T02 : HullSixTwoFourCuts := ⟨0, 2, 1, 2⟩
      have hTnegposLegal : Tnegpos.Legal := by decide
      have hTableNegPos : F.TableHolds Tnegpos := by
        intro i j
        fin_cases i <;> fin_cases j
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX00
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX01
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY02neg
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY03
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX10
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX11
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX12
        · simpa [Tnegpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, Y, U, L] using
            And.intro hX13 hY13pos
      have hReflected := F.tableHolds_reflectedRotateComplement
        hTnegposLegal hTableNegPos
      have hRotate : Tnegpos.rotateComplement = T02 := by decide
      have hTable02 : F'.TableHolds T02 := by
        rw [hRotate] at hReflected
        simpa [F'] using hReflected
      exact (R.reflectReverse F.rotation).twoFourAllWideAt_false
        F'.view F'.rotation F'.upper_pos F'.lower_neg
        T02 (by decide) (by decide)
        (by simpa [HullSixTwoFourGeometricFrame.TableHolds] using hTable02)
    · have hY13nonpos : Y 1 3 ≤ 0 := le_of_not_ge hY13nonneg
      have hY13neg : Y 1 3 ≤ -m := by
        rw [abs_of_nonpos hY13nonpos] at hY13Floor
        linarith
      let Tnegneg : HullSixTwoFourCuts := ⟨2, 3, 2, 3⟩
      let T12 : HullSixTwoFourCuts := ⟨1, 2, 1, 2⟩
      let U12 : HullSixTwoFourCuts := ⟨1, 2, 3, 4⟩
      have hTnegnegLegal : Tnegneg.Legal := by decide
      have hTableNegNeg : F.TableHolds Tnegneg := by
        intro i j
        fin_cases i <;> fin_cases j
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX00
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX01
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY02neg
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY03
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX10
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX11
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, X, U, L] using hX12
        · simpa [Tnegneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
            HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
            HullSixChamberLabel.Holds, m, Y, U, L] using hY13neg
      have hReflected := F.tableHolds_reflectedRotateComplement
        hTnegnegLegal hTableNegNeg
      have hRotate : Tnegneg.rotateComplement = T12 := by decide
      have hTable12 : F'.TableHolds T12 := by
        rw [hRotate] at hReflected
        simpa [F'] using hReflected
      have hT12Legal : T12.Legal := by decide
      have hU12Legal : U12.Legal := by decide
      have hWeak : HullSixTwoFourCuts.Weak T12 U12 := by decide
      have hFrontier12 : F'.XFrontierHolds U12 :=
        F'.xFrontierHolds_of_table_weak hT12Legal hWeak hTable12
      have hPacket12 : HullSixTwoFourIsP12MaximalQFrontier U12 := by
        simp [HullSixTwoFourIsP12MaximalQFrontier,
          HullSixTwoFourIsMaximalQFrontier, U12]
      exact hullSixTwoFourP12MaximalQFrontierProvider
        F' U12 hU12Legal hPacket12 hFrontier12

end HullSixTwoFourGeometricFrame

/-- Global provider for the maximal-q `p = (2,3)` fibre. -/
theorem hullSixTwoFourP23MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider HullSixTwoFourIsP23MaximalQFrontier := by
  intro cfg cycle p q R F T _hLegal hPacket hFrontier
  exact F.twoFourP23MaximalQAt_false
    T hPacket.2.1 hPacket.2.2 hFrontier

end Heilbronn8
