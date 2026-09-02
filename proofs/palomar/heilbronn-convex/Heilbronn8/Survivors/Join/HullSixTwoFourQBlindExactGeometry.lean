import Heilbronn8.Survivors.Join.HullSixTwoFourAdjacentProductGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourHardGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindAdjacentGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindEndOpenGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ11Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ13Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ22Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ24Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ33Geometry

/-!
# Exact geometry dispatch for the `2 + 4` q-blind fibre

This file joins the five exact packets above first cuts `p = (0,1)`.  It
also records the explicitly limited native union consisting of a wide
product table, the separate hard table, or this q-blind fibre.  The latter
is deliberately not presented as a closure of all legal Ferrers tables.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixCompactCrossChordResidual

/-- Every exact table with first cuts `p = (0,1)` contradicts the compact
beating residual. -/
theorem twoFourQBlindP01At_false
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
    (T : HullSixTwoFourCuts) (hLegal : T.Legal)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 1)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  rcases HullSixTwoFourCuts.qBlind01_packet_cases T hLegal hp0 hp1 with
    hWide | hCoincident | hAdjacent | hSeparated | hEndOpen
  · exact R.twoFourAllWideAt_false V rotation hupper hlower
      T hLegal hWide hTable
  · rcases hCoincident with rfl | rfl | rfl
    · exact R.twoFourQBlindQ11At_false V rotation hupper hlower hTable
    · exact R.twoFourQBlindQ22At_false V rotation hupper hlower hTable
    · exact R.twoFourQBlindQ33At_false V rotation hupper hlower hTable
  · exact R.twoFourQBlindAdjacentAt_false V rotation hupper hlower
      T hAdjacent hTable
  · rcases hSeparated with rfl | rfl
    · exact R.twoFourQBlindQ13At_false V rotation hupper hlower hTable
    · exact R.twoFourQBlindQ24At_false V rotation hupper hlower hTable
  · exact R.twoFourQBlindEndOpenAt_false V rotation hupper hlower
      T hEndOpen hTable

/-- Exact closure for the presently implemented native union.  Its explicit
premise is intentionally weaker than a claim covering every legal table. -/
theorem twoFourNativeExactAt_false
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
    (T : HullSixTwoFourCuts) (hLegal : T.Legal)
    (hNative :
      T.HasWideProductTwelve ∨ T.IsHard ∨ (T.p0 = 0 ∧ T.p1 = 1))
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  rcases hNative with hWide | hHard | hp01
  · exact R.twoFourAllWideAt_false V rotation hupper hlower
      T hLegal hWide hTable
  · exact R.twoFourHardAt_false V rotation hupper hlower T hHard hTable
  · exact R.twoFourQBlindP01At_false V rotation hupper hlower
      T hLegal hp01.1 hp01.2 hTable

end HullSixCompactCrossChordResidual
end Heilbronn8
