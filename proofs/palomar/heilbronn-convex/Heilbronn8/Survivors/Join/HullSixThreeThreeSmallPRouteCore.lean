import Heilbronn8.Survivors.Join.HullSixThreeThreeCornerSpanningXFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP012XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP013XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP022XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP023MergedXFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP033XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP111XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP112P122MergedXFrontiers
import Heilbronn8.Survivors.Join.HullSixThreeThreeP222XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeRotateComplementResidualPackets

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

def hullSixThreeThreeMaximalQ
    (T : HullSixThreeThreeCuts) : HullSixThreeThreeCuts :=
  ⟨T.p0, T.p1, T.p2, 2, 3, 3⟩

namespace HullSixThreeThreeGeometricFrame

/-- Exact first-cut family underlying the final three maximal-q frontiers. -/
def IsSmallPExactPacket (T : HullSixThreeThreeCuts) : Prop :=
  (T.p0 = 0 ∧ T.p1 = 0 ∧ T.p2 = 1) ∨
    (T.p0 = 0 ∧ T.p1 = 0 ∧ T.p2 = 2) ∨
    (T.p0 = 0 ∧ T.p1 = 0 ∧ T.p2 = 3)

/-- The completed maximal-q sinks reached by complement-transposing a
non-high-q small-p exact table. -/
def IsKnownSinkFrontier (T : HullSixThreeThreeCuts) : Prop :=
  IsCornerSpanningRemainingFrontier T ∨
    IsP013RemainingFrontier T ∨
    IsP023RemainingFrontier T ∨
    IsP112P122RemainingFrontier T ∨
    IsP033RemainingFrontier T ∨
    IsP222RemainingFrontier T ∨
    IsP022RemainingFrontier T ∨
    IsP012RemainingFrontier T ∨
    IsP111RemainingFrontier T

/-- Direct exact sinks before the optional complement-transpose. -/
def IsSmallPDirectExactSink (T : HullSixThreeThreeCuts) : Prop :=
  IsClosedNativePacket T ∨
    IsRotateComplementResidualPacket T ∨
    IsClosedNativePacket
      (HullSixThreeThreeCuts.act
        HullSixThreeThreeCuts.Symmetry.rotateComplement T)

end HullSixThreeThreeGeometricFrame

def hullSixThreeThreeSmallPRoute
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink T ∨
    HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink
      T.complementTranspose ∨
    HullSixThreeThreeGeometricFrame.IsClosedNativePacket
      T.complementTranspose ∨
    HullSixThreeThreeGeometricFrame.IsKnownSinkFrontier
      (hullSixThreeThreeMaximalQ T.complementTranspose)

def hullSixThreeThreeSmallPRouteDecidable
    (T : HullSixThreeThreeCuts) :
    Decidable (hullSixThreeThreeSmallPRoute T) := by
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsQBlindP011Packet := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsQBlindP011Packet
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsClosedNativePacket := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsClosedNativePacket
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsRotateComplementResidualPacket :=
    fun U => by
      unfold HullSixThreeThreeGeometricFrame.IsRotateComplementResidualPacket
      infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink
    infer_instance
  letI : DecidablePred HullSixThreeThreeIsMaximalQFrontier := fun U => by
    unfold HullSixThreeThreeIsMaximalQFrontier
    infer_instance
  letI : DecidablePred HullSixThreeThreeIsRemainingMaximalQFrontier :=
    fun U => by
      unfold HullSixThreeThreeIsRemainingMaximalQFrontier
      infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsCornerSpanningRemainingFrontier :=
    fun U => by
      unfold HullSixThreeThreeGeometricFrame.IsCornerSpanningRemainingFrontier
      infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP013RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP013RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP023RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP023RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP112RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP112RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP122RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP122RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP112P122RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP112P122RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP033RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP033RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP222RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP222RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP022RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP022RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP012RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP012RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier
    infer_instance
  letI : DecidablePred
      HullSixThreeThreeGeometricFrame.IsKnownSinkFrontier := fun U => by
    unfold HullSixThreeThreeGeometricFrame.IsKnownSinkFrontier
    infer_instance
  unfold hullSixThreeThreeSmallPRoute
  infer_instance

end Heilbronn8
