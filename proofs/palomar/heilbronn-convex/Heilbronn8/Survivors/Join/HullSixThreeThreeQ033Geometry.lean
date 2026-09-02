import Heilbronn8.Survivors.Join.HullSixThreeThreeQ133Geometry

/-!
# Ferrers-table wrapper for the q-blind `011 / 033` chamber

The `033` table supplies the same four signed floors used by the `133`
scalar certificate.  This file keeps the already-built `Q133` geometry
module unchanged and adds only the missing finite decoder.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

namespace HullSixThreeThreeCuts

/-- The signed q-blind branch `p = 011`, `q = 033`. -/
def q033 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 0
  q1 := 3
  q2 := 3

end HullSixThreeThreeCuts

namespace HullSixCompactCrossChordResidual

/-- The `011 / 033` table feeds the common `Q133` signed-floor core. -/
theorem threeThreeQ033At_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hQ033 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q033.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h10 := hQ033 1 0
  have h21 := hQ033 2 1
  have h01 := hQ033 0 1
  have h12 := hQ033 1 2
  rw [show HullSixThreeThreeCuts.q033.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q033.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.q033.table 0 1 =
    HullSixChamberLabel.R by decide] at h01
  rw [show HullSixThreeThreeCuts.q033.table 1 2 =
    HullSixChamberLabel.M by decide] at h12
  simp only [HullSixChamberLabel.Holds] at h10 h21 h01 h12
  exact R.threeThreeQ133At_false_of_crossFloors V rotation hupper hlower
    h10 h21.1 h01 h12.2

end HullSixCompactCrossChordResidual

end Heilbronn8
