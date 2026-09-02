import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ12Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ23Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ34Geometry

/-!
# Exact-table dispatcher for adjacent q-blind `2 + 4` transitions

The adjacent transition packet consists exactly of the q12, q23, and q34
tables.  Their scalar arguments have separate small adapters; this module is
only the finite three-way dispatch and adds no metric hypotheses.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixCompactCrossChordResidual

/-- Every exact table in the adjacent q-blind transition packet contradicts
the compact beating residual. -/
theorem twoFourQBlindAdjacentAt_false
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
    (hAdjacent : T.IsAdjacentStaggerPacket)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds
        (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  rcases hAdjacent with rfl | rfl | rfl
  · exact R.twoFourQBlindQ12At_false V rotation hupper hlower hTable
  · exact R.twoFourQBlindQ23At_false V rotation hupper hlower hTable
  · exact R.twoFourQBlindQ34At_false V rotation hupper hlower hTable

end HullSixCompactCrossChordResidual
end Heilbronn8
