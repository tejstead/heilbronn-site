import Heilbronn8.Survivors.Join.HullSixTwoFourExactOrbitCover
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindExactSemanticProvider
import Heilbronn8.Survivors.Join.HullSixTwoFourReflectedCustody

/-!
# Semantic assembly of the exact `2 + 4` orbit cover

Native exact adapters close 36 tables.  Honest physical reflection closes
their nine additional complement-rotation images.  This file exposes two
sound ways to finish the remaining geometry:

* exact callbacks for the eighteen residual orbit representatives; or
* partial-X callbacks for the nine first-cut fibres in which residual exact
  tables remain.

Neither route treats an exact q-weakening as an exact table realization.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

/-- Exact provider for the 36-table native predicate used by the finite
orbit census. -/
theorem hullSixTwoFourExactNativeProvider :
    HullSixTwoFourExactPacketProvider HullSixTwoFourCuts.IsExactNative := by
  intro cfg cycle p q R F
  intro T hLegal hNative hTable
  exact R.twoFourNativeExactAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hLegal hNative hTable

/-- Exact provider for the nine additional reflected-native tables. -/
theorem hullSixTwoFourExactReflectedNativeProvider :
    HullSixTwoFourExactPacketProvider
      (fun T ↦ T.rotateComplement.IsExactNative) :=
  hullSixTwoFourExactPacketProvider_rotateComplement
    hullSixTwoFourExactNativeProvider

/-- The nine first-cut fibres containing the thirty-one residual exact
tables after native and reflected-native adapters are removed. -/
def HullSixTwoFourIsResidualFirstCuts (T : HullSixTwoFourCuts) : Prop :=
  (T.p0 = 0 ∧ T.p1 = 2) ∨
  (T.p0 = 0 ∧ T.p1 = 3) ∨
  (T.p0 = 0 ∧ T.p1 = 4) ∨
  (T.p0 = 1 ∧ T.p1 = 1) ∨
  (T.p0 = 1 ∧ T.p1 = 2) ∨
  (T.p0 = 1 ∧ T.p1 = 3) ∨
  (T.p0 = 2 ∧ T.p1 = 2) ∨
  (T.p0 = 2 ∧ T.p1 = 3) ∨
  (T.p0 = 3 ∧ T.p1 = 3)

/-- A maximal-q partial X-frontier whose first cuts belong to a residual
fibre. -/
def HullSixTwoFourIsResidualMaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧
    HullSixTwoFourIsResidualFirstCuts T

/-- After consuming native and reflected-native tables exactly, same-frame
weakening is needed only in the nine residual first-cut fibres. -/
theorem hullSixTwoFour_exactOrbit_or_residualMaximalQ_cover :
    HullSixTwoFourFixedOrientationCover
      (fun T ↦
        T.IsExactNative ∨ T.rotateComplement.IsExactNative)
      HullSixTwoFourIsResidualMaximalQFrontier := by
  unfold HullSixTwoFourFixedOrientationCover
  letI : DecidablePred fun T : HullSixTwoFourCuts =>
      T.Legal →
        (T.IsExactNative ∨ T.rotateComplement.IsExactNative) ∨
          ∃ U : HullSixTwoFourCuts,
            HullSixTwoFourCuts.Weak T U ∧ U.Legal ∧
              HullSixTwoFourIsResidualMaximalQFrontier U := fun T => by
    letI : DecidablePred fun U : HullSixTwoFourCuts =>
        HullSixTwoFourCuts.Weak T U ∧ U.Legal ∧
          HullSixTwoFourIsResidualMaximalQFrontier U := fun U => by
      letI : Decidable (HullSixTwoFourCuts.Weak T U) := inferInstance
      letI : Decidable U.Legal := inferInstance
      letI : Decidable (HullSixTwoFourIsResidualMaximalQFrontier U) :=
        by
          unfold HullSixTwoFourIsResidualMaximalQFrontier
            HullSixTwoFourIsMaximalQFrontier
            HullSixTwoFourIsResidualFirstCuts
          infer_instance
      exact inferInstance
    letI : Decidable T.Legal := inferInstance
    letI : Decidable T.IsExactNative := inferInstance
    letI : Decidable T.rotateComplement.IsExactNative := inferInstance
    exact inferInstance
  decide

/-- Combined exact provider for native and reflected-native tables. -/
theorem hullSixTwoFourExactOrbitBaseProvider :
    HullSixTwoFourExactPacketProvider
      (fun T ↦
        T.IsExactNative ∨ T.rotateComplement.IsExactNative) := by
  intro cfg cycle p q R F
  intro T hLegal hPacket hTable
  rcases hPacket with hNative | hReflected
  · exact hullSixTwoFourExactNativeProvider F
      T hLegal hNative hTable
  · exact hullSixTwoFourExactReflectedNativeProvider F
      T hLegal hReflected hTable

/-- Conditional `2 + 4` closure requiring only the nine residual maximal-q
partial-X fibres. -/
theorem hullSixTwoFourFerrersClosed_of_residualMaximalQFrontiers
    (hFrontier : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontier) :
    HullSixTwoFourFerrersClosed :=
  hullSixTwoFourFerrersClosed_of_fixedOrientationCover
    hullSixTwoFour_exactOrbit_or_residualMaximalQ_cover
    hullSixTwoFourExactOrbitBaseProvider hFrontier

/-! ## Exact-only alternative -/

/-- Exact providers for the eighteen residual representatives and their
reflections, together with the native providers, close every legal exact
table. -/
theorem hullSixTwoFourAllLegalExactProvider_of_residualReps
    (hResidual : HullSixTwoFourExactPacketProvider
      HullSixTwoFourCuts.IsExactResidualRep) :
    HullSixTwoFourExactPacketProvider (fun T ↦ T.Legal) := by
  have hResidualReflected :
      HullSixTwoFourExactPacketProvider
        (fun T ↦ T.rotateComplement.IsExactResidualRep) :=
    hullSixTwoFourExactPacketProvider_rotateComplement hResidual
  intro cfg cycle p q R F
  intro T hLegal _hPacket hTable
  rcases HullSixTwoFourCuts.exact_native_or_reflected_or_residualRep
      T hLegal with hNative | hNativeReflected | hRep | hRepReflected
  · exact hullSixTwoFourExactNativeProvider F
      T hLegal hNative hTable
  · exact hullSixTwoFourExactReflectedNativeProvider F
      T hLegal hNativeReflected hTable
  · exact hResidual F T hLegal hRep hTable
  · exact hResidualReflected F T hLegal hRepReflected hTable

private theorem hullSixTwoFour_allLegal_fixedOrientationCover :
    HullSixTwoFourFixedOrientationCover
      (fun T ↦ T.Legal) (fun _ ↦ False) := by
  intro T hLegal
  exact Or.inl hLegal

private theorem hullSixTwoFour_noFalseFrontier :
    HullSixTwoFourXFrontierProvider (fun _ ↦ False) := by
  intro cfg cycle p q R F U hLegal hFalse
  exact False.elim hFalse

/-- Exact callbacks for the eighteen canonical residual representatives are
sufficient for global `2 + 4` Ferrers closure. -/
theorem hullSixTwoFourFerrersClosed_of_exactResidualReps
    (hResidual : HullSixTwoFourExactPacketProvider
      HullSixTwoFourCuts.IsExactResidualRep) :
    HullSixTwoFourFerrersClosed :=
  hullSixTwoFourFerrersClosed_of_fixedOrientationCover
    hullSixTwoFour_allLegal_fixedOrientationCover
    (hullSixTwoFourAllLegalExactProvider_of_residualReps hResidual)
    hullSixTwoFour_noFalseFrontier

/-- Direct hull-six endpoint through the exact-only `2 + 4` route. -/
theorem geometricHullSixExclusion_of_exactTwoFourResidualReps
    (hResidual : HullSixTwoFourExactPacketProvider
      HullSixTwoFourCuts.IsExactResidualRep)
    (hThreeThree : HullSixThreeThreeFerrersClosed) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_ferrersClosed
    (hullSixTwoFourFerrersClosed_of_exactResidualReps hResidual)
    hThreeThree

end Heilbronn8
