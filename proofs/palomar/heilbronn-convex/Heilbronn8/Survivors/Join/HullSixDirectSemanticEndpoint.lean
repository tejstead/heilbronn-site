import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge
import Heilbronn8.Survivors.Join.HullSixTwoFourExactOrbitSemanticProvider

/-!
# Direct sound hull-six semantic endpoint

The line-sign-block geometry has already eliminated `1 + 5`.  The two
theorems here expose the smallest currently honest inputs for `2 + 4` and
`3 + 3`, without retained classifiers, generated routes, exact-table
q-weakening, or same-frame symmetry assumptions.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Direct H6 endpoint using partial-X frontiers in the two remaining split
shapes: nine `2 + 4` first-cut fibres and seventeen `3 + 3` first-cut
fibres. -/
theorem geometricHullSixExclusion_of_residualFrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontier)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingMaximalQFrontier) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_ferrersClosed
    (hullSixTwoFourFerrersClosed_of_residualMaximalQFrontiers hTwoFour)
    (hullSixThreeThreeFerrersClosed_of_remainingMaximalQFrontiers
      hThreeThree)

/-- Exact-only `2 + 4` alternative: callbacks for the eighteen canonical
residual orbit representatives, together with the seventeen honest `3 + 3`
partial-X frontiers, imply the direct H6 endpoint. -/
theorem geometricHullSixExclusion_of_exactTwoFourAndThreeThreeFrontiers
    (hTwoFour : HullSixTwoFourExactPacketProvider
      HullSixTwoFourCuts.IsExactResidualRep)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingMaximalQFrontier) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_ferrersClosed
    (hullSixTwoFourFerrersClosed_of_exactResidualReps hTwoFour)
    (hullSixThreeThreeFerrersClosed_of_remainingMaximalQFrontiers
      hThreeThree)

end Heilbronn8
