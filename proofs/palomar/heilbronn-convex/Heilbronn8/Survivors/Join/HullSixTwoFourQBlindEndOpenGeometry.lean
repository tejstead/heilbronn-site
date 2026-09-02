import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ04Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ14Geometry

/-!
# Exact-table dispatch for the end-open `2 + 4` packet

The finite packet consists exactly of `q = 04` and `q = 14`.  Their scalar
arguments use different first-edge compatibility, so the geometry is decoded
in the two dedicated adapters and joined here without weakening either table.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8
namespace HullSixCompactCrossChordResidual

/-- Every exact end-open q-blind table is impossible in a beating oriented
`2 + 4` view. -/
theorem twoFourQBlindEndOpenAt_false
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
    (hPacket : T.IsEndOpenTransitionPacket)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  rcases hPacket with rfl | rfl
  · exact R.twoFourQBlindQ04At_false V rotation hupper hlower hTable
  · exact R.twoFourQBlindQ14At_false V rotation hupper hlower hTable

end HullSixCompactCrossChordResidual
end Heilbronn8
