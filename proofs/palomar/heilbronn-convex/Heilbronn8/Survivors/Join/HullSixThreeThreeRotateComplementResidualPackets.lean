import Heilbronn8.Survivors.Join.HullSixThreeThreeRotateComplementCustody
import Heilbronn8.Survivors.Join.HullSixThreeThreeP111XFrontier

/-!
# Three residual `3 + 3` packets closed by honest reflection

The physical `rotateComplement` custody sends the three exact packets which
form the remaining complement-transpose cycles to existing acyclic sinks:

```text
001 / 222  ->  111 / 233,
002 / 223  ->  011 / 133,
002 / 222  ->  111 / 133.
```

The middle target is one of the native exact `p = 011` packets.  The two
`p = 111` targets weaken, in their reflected frames, to the already closed
maximal-q `111 / 233` frontier.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

private def p001q222RotateSource : HullSixThreeThreeCuts :=
  ⟨0, 0, 1, 2, 2, 2⟩

private def p002q223RotateSource : HullSixThreeThreeCuts :=
  ⟨0, 0, 2, 2, 2, 3⟩

private def p002q222RotateSource : HullSixThreeThreeCuts :=
  ⟨0, 0, 2, 2, 2, 2⟩

private def p111q233RotateTarget : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 2, 3, 3⟩

private def p011q133RotateTarget : HullSixThreeThreeCuts :=
  ⟨0, 1, 1, 1, 3, 3⟩

private def p111q133RotateTarget : HullSixThreeThreeCuts :=
  ⟨1, 1, 1, 1, 3, 3⟩

private theorem rotate_p001q222 :
    HullSixThreeThreeCuts.act
        HullSixThreeThreeCuts.Symmetry.rotateComplement
        p001q222RotateSource =
      p111q233RotateTarget := by
  decide

private theorem rotate_p002q223 :
    HullSixThreeThreeCuts.act
        HullSixThreeThreeCuts.Symmetry.rotateComplement
        p002q223RotateSource =
      p011q133RotateTarget := by
  decide

private theorem rotate_p002q222 :
    HullSixThreeThreeCuts.act
        HullSixThreeThreeCuts.Symmetry.rotateComplement
        p002q222RotateSource =
      p111q133RotateTarget := by
  decide

private theorem p111q233_isP111RemainingFrontier :
    HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier
      p111q233RotateTarget := by
  norm_num [HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier,
    HullSixThreeThreeIsRemainingMaximalQFrontier,
    HullSixThreeThreeIsMaximalQFrontier,
    HullSixThreeThreeGeometricFrame.IsQBlindP011Packet,
    p111q233RotateTarget]

namespace HullSixThreeThreeGeometricFrame

/-- The three direct representatives left after orienting the
complement-transpose dispatcher acyclically. -/
def IsRotateComplementResidualPacket (T : HullSixThreeThreeCuts) : Prop :=
  T = p001q222RotateSource ∨
    T = p002q223RotateSource ∨
    T = p002q222RotateSource

end HullSixThreeThreeGeometricFrame

/-- Honest reflected closure of the three residual exact packets. -/
theorem hullSixThreeThreeRotateComplementResidualPacketProvider :
    HullSixThreeThreeExactPacketProvider
      HullSixThreeThreeGeometricFrame.IsRotateComplementResidualPacket := by
  intro cfg cycle p q R F
  intro T hLegal hPacket hTable
  rcases hPacket with rfl | rfl | rfl
  · have hTableTarget :
        F.reflectedRotateComplement.TableHolds p111q233RotateTarget := by
      simpa [rotate_p001q222] using
        (F.tableHolds_reflectedRotateComplement hLegal hTable)
    have hFrontier :
        F.reflectedRotateComplement.XFrontierHolds
          p111q233RotateTarget :=
      F.reflectedRotateComplement.xFrontierHolds_of_table_weak
        (by decide) (by decide) hTableTarget
    exact
      (hullSixThreeThreeP111XFrontierProvider
        F.reflectedRotateComplement p111q233RotateTarget
        (by decide) p111q233_isP111RemainingFrontier) hFrontier
  · have hTableTarget :
        F.reflectedRotateComplement.TableHolds p011q133RotateTarget := by
      simpa [rotate_p002q223] using
        (F.tableHolds_reflectedRotateComplement hLegal hTable)
    exact hullSixThreeThreeClosedNativePacketProvider
      F.reflectedRotateComplement p011q133RotateTarget
      (by decide)
      (Or.inr ⟨rfl, rfl, rfl⟩)
      hTableTarget
  · have hTableTarget :
        F.reflectedRotateComplement.TableHolds p111q133RotateTarget := by
      simpa [rotate_p002q222] using
        (F.tableHolds_reflectedRotateComplement hLegal hTable)
    have hFrontier :
        F.reflectedRotateComplement.XFrontierHolds
          p111q233RotateTarget :=
      F.reflectedRotateComplement.xFrontierHolds_of_table_weak
        (by decide) (by decide) hTableTarget
    exact
      (hullSixThreeThreeP111XFrontierProvider
        F.reflectedRotateComplement p111q233RotateTarget
        (by decide) p111q233_isP111RemainingFrontier) hFrontier

end Heilbronn8
