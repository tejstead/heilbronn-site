import Heilbronn8.Survivors.Join.HullSixThreeThreeSmallPRouteCore

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

theorem hullSixThreeThree_smallP_route_002 :
    ∀ q0 q1 q2 : Fin 4,
      let T : HullSixThreeThreeCuts := ⟨0, 0, 2, q0, q1, q2⟩
      T.Legal → hullSixThreeThreeSmallPRoute T := by
  letI : DecidablePred hullSixThreeThreeSmallPRoute :=
    hullSixThreeThreeSmallPRouteDecidable
  decide

end Heilbronn8
