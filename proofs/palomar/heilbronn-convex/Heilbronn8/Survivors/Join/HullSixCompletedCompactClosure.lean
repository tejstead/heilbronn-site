import Heilbronn8.Survivors.Join.HullSixThreeThreeSmallPResidualXFrontier

/-!
# Completed compact hull-six closure

Phase-two scratch source.  The live final H6 module currently exposes only a
`GeometricHullSizeExclusion`, thereby hiding the rational compact closure that
the optimizer boundary proof needs.  This file assembles exactly the same
completed frontier providers but stops one layer earlier, at
`HullSixCompactCrossChordClosed`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- All completed `2 + 4` providers, assembled without entering the `Beats`
wrapper. -/
theorem hullSixTwoFourResidualMaximalQFrontierProvider_completed :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontier :=
  hullSixTwoFourResidualMaximalQFrontierProvider_of_exceptP11
    (hullSixTwoFourResidualExceptP11Provider_of_afterP11P03
      (hullSixTwoFourResidualAfterP11P03Provider_of_afterP04
        (hullSixTwoFourResidualAfterP04Provider_of_afterP12
          (hullSixTwoFourResidualAfterP12Provider_of_afterP33
            (hullSixTwoFourResidualAfterP33Provider_of_afterP13
              (hullSixTwoFourResidualAfterP13Provider_of_afterP23
                hullSixTwoFourResidualAfterP23FrontierProvider))))))

/-- All completed `3 + 3` providers, assembled without entering the `Beats`
wrapper. -/
theorem hullSixThreeThreeRemainingMaximalQFrontierProvider_completed :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingMaximalQFrontier :=
  hullSixThreeThreeRemainingMaximalQFrontierProvider_of_nonCorner
    (hullSixThreeThreeNonCornerProvider_of_afterP013
      (hullSixThreeThreeAfterP013Provider_of_afterP023
        (hullSixThreeThreeAfterP023Provider_of_afterP112P122
          (hullSixThreeThreeAfterMergedPathProvider_of_afterP033
            (hullSixThreeThreeAfterP033Provider_of_afterP222
              (hullSixThreeThreeAfterP033P222Provider_of_afterP022
                (hullSixThreeThreeAfterP022Provider_of_afterP012
                  (hullSixThreeThreeAfterP012Provider_of_afterP111
                    hullSixThreeThreeSmallPResidualXFrontierProvider))))))))

/-- The rational core hidden immediately below the completed H6 exclusion. -/
theorem hullSixCompactCrossChordClosed_of_completedDirectFrontiers :
    HullSixCompactCrossChordClosed := by
  have h24 : HullSixTwoFourFerrersClosed :=
    hullSixTwoFourFerrersClosed_of_residualMaximalQFrontiers
      hullSixTwoFourResidualMaximalQFrontierProvider_completed
  have h33 : HullSixThreeThreeFerrersClosed :=
    hullSixThreeThreeFerrersClosed_of_remainingMaximalQFrontiers
      hullSixThreeThreeRemainingMaximalQFrontierProvider_completed
  obtain ⟨h24', h33'⟩ :=
    hullSixOrientedPacketsClosed_of_ferrersClosed h24 h33
  exact hullSixCompactCrossChordClosed_of_orientedPackets h24' h33'

end Heilbronn8
