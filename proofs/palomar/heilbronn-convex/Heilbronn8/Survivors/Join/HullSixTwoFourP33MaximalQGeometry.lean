import Heilbronn8.Survivors.Join.HullSixTwoFourP11MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ11Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourReflectedCustody

/-!
# The maximal-q `p = (3,3)` partial frontier

The partial `X` frontier makes the first three cells in both rows `L`.
The final top-row cell is always `R`, because its `Q` determinant is the
negative of a positive boundary-fan face.  Splitting the remaining absolute
floor `|Y13|` therefore gives the two exact packets

```text
LLLR / LLLM    and    LLLR / LLLR.
```

Both branches use the honest physical reflection from
`HullSixTwoFourReflectedCustody`; no same-configuration
`RotateComplementCustody` is assumed.  The first packet reflects exactly to
`qBlind11`.  The second reflects to `LRRR / LRRR`, then weakens in that same
reflected frame to the already closed maximal-q `p = (1,1)` frontier.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-- The one maximal-q frontier record with first cuts `p = (3,3)`. -/
def HullSixTwoFourIsP33MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 3 ∧ T.p1 = 3

namespace HullSixTwoFourGeometricFrame

/-- The `p = (3,3)` partial `X` frontier is impossible.  The theorem is
stated at frame level because both branches deliberately construct the
physically reflected frame. -/
theorem twoFourP33MaximalQAt_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (T : HullSixTwoFourCuts) (hp0 : T.p0 = 3) (hp1 : T.p1 = 3)
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

  have hLeft3 (i : Fin 2) (j : Fin 4) (hj : j.val < 3) :
      m ≤ X i j := by
    have h := hLeft i j (by
      fin_cases i <;>
        simpa [HullSixTwoFourCuts.p, hp0, hp1] using hj)
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h
  have hNegative3 (i : Fin 2) : X i (3 : Fin 4) ≤ -m := by
    have h := hNegative i (3 : Fin 4) (by
      fin_cases i <;> simp [HullSixTwoFourCuts.p, hp0, hp1])
    simpa [X, U, L, HullSixTwoFourGeometricFrame.X] using h

  /- The top-right `Q` chord is the negative of the positive closing
  boundary face based at `Q`. -/
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

  /- The only `Y` sign not fixed by the frontier and boundary orientation is
  `Y13`; obtain its absolute floor directly from `minTri`. -/
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

  by_cases hY13nonneg : 0 ≤ Y 1 3
  · have hY13pos : m ≤ Y 1 3 := by
      rw [abs_of_nonneg hY13nonneg] at hY13Floor
      exact hY13Floor
    let Tpos : HullSixTwoFourCuts := ⟨3, 3, 3, 4⟩
    have hTposLegal : Tpos.Legal := by decide
    have hTablePos : F.TableHolds Tpos := by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 0 0 (by decide)
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 0 1 (by decide)
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 0 2 (by decide)
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, Y, U, L] using hY03
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 1 0 (by decide)
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 1 1 (by decide)
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 1 2 (by decide)
      · simpa [Tpos, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, Y, U, L] using
          And.intro (hNegative3 1) hY13pos
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hTposLegal hTablePos
    have hRotate :
        Tpos.rotateComplement = HullSixTwoFourCuts.qBlind11 := by decide
    have hQ11 : F'.TableHolds HullSixTwoFourCuts.qBlind11 := by
      rw [hRotate] at hReflected
      simpa [F'] using hReflected
    exact (R.reflectReverse F.rotation).twoFourQBlindQ11At_false
      F'.view F'.rotation F'.upper_pos F'.lower_neg
      (by simpa [HullSixTwoFourGeometricFrame.TableHolds] using hQ11)
  · have hY13nonpos : Y 1 3 ≤ 0 := le_of_not_ge hY13nonneg
    have hY13neg : Y 1 3 ≤ -m := by
      rw [abs_of_nonpos hY13nonpos] at hY13Floor
      linarith
    let Tneg : HullSixTwoFourCuts := ⟨3, 3, 3, 3⟩
    let T11 : HullSixTwoFourCuts := ⟨1, 1, 1, 1⟩
    let U11 : HullSixTwoFourCuts := ⟨1, 1, 3, 4⟩
    have hTnegLegal : Tneg.Legal := by decide
    have hTableNeg : F.TableHolds Tneg := by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 0 0 (by decide)
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 0 1 (by decide)
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 0 2 (by decide)
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, Y, U, L] using hY03
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 1 0 (by decide)
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 1 1 (by decide)
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, X, U, L] using
          hLeft3 1 2 (by decide)
      · simpa [Tneg, HullSixTwoFourCuts.table, hullSixFerrersLabel,
          HullSixTwoFourCuts.p, HullSixTwoFourCuts.q,
          HullSixChamberLabel.Holds, m, Y, U, L] using hY13neg
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hTnegLegal hTableNeg
    have hRotate : Tneg.rotateComplement = T11 := by decide
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

end HullSixTwoFourGeometricFrame

/-- Global provider for the maximal-q `p = (3,3)` fibre. -/
theorem hullSixTwoFourP33MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsP33MaximalQFrontier := by
  intro cfg cycle p q R F T _hLegal hPacket hFrontier
  exact F.twoFourP33MaximalQAt_false T hPacket.2.1 hPacket.2.2 hFrontier

end Heilbronn8
