import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadGeometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeFiniteBridge

/-!
# Ferrers-table wrapper for the broad `3 x 3` geometry

The geometric theorem consumes only seven cells (eight signed floors) of the
exceptional table `001 / 233`.  This file performs that finite decoding.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

namespace HullSixCompactCrossChordResidual

/-- The canonical broad Ferrers table supplies exactly the cross floors used
by `threeThreeBroadAt_false_of_crossFloors`. -/
theorem threeThreeBroadAt_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hpair : HullSixIsOrientedPair p q P Q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hBroad : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.broad.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h10 := hBroad 1 0
  have h11 := hBroad 1 1
  have h20 := hBroad 2 0
  have h21 := hBroad 2 1
  have h01 := hBroad 0 1
  have h02 := hBroad 0 2
  have h12 := hBroad 1 2
  rw [show HullSixThreeThreeCuts.broad.table 1 0 =
    HullSixChamberLabel.M by decide] at h10
  rw [show HullSixThreeThreeCuts.broad.table 1 1 =
    HullSixChamberLabel.M by decide] at h11
  rw [show HullSixThreeThreeCuts.broad.table 2 0 =
    HullSixChamberLabel.L by decide] at h20
  rw [show HullSixThreeThreeCuts.broad.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.broad.table 0 1 =
    HullSixChamberLabel.M by decide] at h01
  rw [show HullSixThreeThreeCuts.broad.table 0 2 =
    HullSixChamberLabel.R by decide] at h02
  rw [show HullSixThreeThreeCuts.broad.table 1 2 =
    HullSixChamberLabel.M by decide] at h12
  simp only [HullSixChamberLabel.Holds] at h10 h11 h20 h21 h01 h02 h12
  apply R.threeThreeBroadAt_false_of_crossFloors hpair V rotation
    hupper hlower
  · linarith [h10.1]
  · linarith [h11.1]
  · exact h20
  · linarith [h21.1]
  · exact h01.2
  · linarith [h02]
  · exact h11.2
  · exact h12.2

end HullSixCompactCrossChordResidual

end Heilbronn8
