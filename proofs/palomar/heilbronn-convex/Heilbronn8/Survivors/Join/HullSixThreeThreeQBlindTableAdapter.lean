import Heilbronn8.Survivors.Join.HullSixThreeThreeQ033Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ111Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ112Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ113Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ122Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ123Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ233Geometry

/-!
# Master Ferrers adapter for the q-blind `011 / q` family

Ferrers legality leaves exactly fifteen second-cut triples above `p = 011`.
The scalar and geometric adapters are most naturally organized in seven
sign families; this file performs the final finite dispatch among them.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixThreeThreeCuts

/-- Exact finite classification of legal second cuts above `p = 011`. -/
theorem qBlind011_cases : ∀ T : HullSixThreeThreeCuts,
    T.Legal → T.p0 = 0 → T.p1 = 1 → T.p2 = 1 →
      T = q011 ∨ T = q012 ∨ T = q013 ∨
      T = q022 ∨ T = q023 ∨ T = q033 ∨
      T = q111 ∨ T = q112 ∨ T = q113 ∨
      T = q122 ∨ T = q123 ∨ T = q133 ∨
      T = q222 ∨ T = q223 ∨ T = q233 := by
  rintro ⟨p0, p1, p2, q0, q1, q2⟩ hLegal hp0 hp1 hp2
  dsimp only at hp0 hp1 hp2
  subst p0
  subst p1
  subst p2
  fin_cases q0 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp_all [HullSixThreeThreeCuts.Legal, q011, q012, q013,
      q022, q023, q033, q111, q112, q113, q122, q123, q133,
      q222, q223, q233]

end HullSixThreeThreeCuts

namespace HullSixCompactCrossChordResidual

/-- Every legal q-blind Ferrers table above `p = 011` contradicts the
compact beating residual. -/
theorem threeThreeQBlindAt_false
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
    (T : HullSixThreeThreeCuts)
    (hLegal : T.Legal)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 1) (hp2 : T.p2 = 1)
    (hTable : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  rcases HullSixThreeThreeCuts.qBlind011_cases T hLegal hp0 hp1 hp2 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact R.threeThreeQ011At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ012At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ013At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ022At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ023At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ033At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ111At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ112At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ113At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ122At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ123At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ133At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ222At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ223At_false V rotation hupper hlower hTable
  · exact R.threeThreeQ233At_false V rotation hupper hlower hTable

end HullSixCompactCrossChordResidual

end Heilbronn8
