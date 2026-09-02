import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCoincidentQ22ConditionalGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ22ReverseGeometry

/-!
# Complete geometry adapter for the q-blind q22 chamber

The existing compact coincident theorem closes the order `d <= e`; the
q22-specific reverse certificate closes `e < d`.  This file contains only
the honest order dispatcher.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixCompactCrossChordResidual

/-- The exact `MMRR / LMRR` q22 table is impossible in a beating oriented
`2 + 4` view, in either order of the two middle lower heights. -/
theorem twoFourQBlindQ22At_false
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
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds
        (HullSixTwoFourCuts.qBlind22.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  by_cases hde :
      hullSixThreeThreeLowerHeight (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset 1)))
          (minTri cfg) ≤
        hullSixThreeThreeLowerHeight (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset 2)))
          (minTri cfg)
  · exact twoFourQBlindQ22At_false_of_d_le_e
      R V rotation hupper hlower hTable hde
  · have hed :
        hullSixThreeThreeLowerHeight (cfg P) (cfg Q)
            (cfg (cycle (rotation + hullSixTwoFourLowerOffset 2)))
            (minTri cfg) <
          hullSixThreeThreeLowerHeight (cfg P) (cfg Q)
            (cfg (cycle (rotation + hullSixTwoFourLowerOffset 1)))
            (minTri cfg) := lt_of_not_ge hde
    exact twoFourQBlindQ22At_false_of_e_lt_d
      R V rotation hupper hlower hTable hed

end HullSixCompactCrossChordResidual
end Heilbronn8
