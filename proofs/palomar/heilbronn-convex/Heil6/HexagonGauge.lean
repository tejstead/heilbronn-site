import Heil6.GaugeAlgebra
import Heil6.HexagonGeometryRigidity
import Solution.N6

set_option linter.style.header false

/-!
# Positive-affine gauge for the rigid six-hull table

The equality table reconstructs a configuration in affine coordinates of its
first three vertices.  This module writes the corresponding
positive-determinant affine map explicitly and shows that it maps the retained
unit-area witness `hex6` to that configuration.  Relabelling and pairwise
uniqueness are then immediate from `GaugeAlgebra`.
-/

namespace N6Scratch
namespace HexagonGauge

open HeilbronnChallenge

/-- The unique affine map taking the first three vertices of `hex6` to
`A,B,C`.  Positivity follows from the orientation of that target frame. -/
def frameGauge (A B C : ℝ × ℝ)
    (hABC : 0 < PlanarDet.sig A B C) : PosAffine where
  a := 3 * (B.1 - C.1)
  b := -A.1 + 2 * B.1 - C.1
  c := 3 * (B.2 - C.2)
  d := -A.2 + 2 * B.2 - C.2
  tx := A.1 - B.1 + C.1
  ty := A.2 - B.2 + C.2
  det_pos := by
    have hid :
        (3 * (B.1 - C.1)) * (-A.2 + 2 * B.2 - C.2) -
            (-A.1 + 2 * B.1 - C.1) * (3 * (B.2 - C.2)) =
          3 * PlanarDet.sig A B C := by
      simp only [PlanarDet.sig]
      ring
    rw [hid]
    exact mul_pos (by norm_num) hABC

theorem frameGauge_map (A B C : ℝ × ℝ)
    (hABC : 0 < PlanarDet.sig A B C) (p : ℝ × ℝ) :
    (frameGauge A B C hABC).map p =
      HexagonFrameRigidity.framePoint A B C
        (3 * p.1 + 2 * p.2 - 1) (1 - 3 * p.1 - p.2) := by
  ext <;>
    simp only [frameGauge, PosAffine.map,
      HexagonFrameRigidity.framePoint] <;>
    ring

/-- Any configuration with the rigid determinant table is gauge-equivalent
to the explicit affinely regular witness. -/
theorem affineRegularFrame_gauge
    (v : Fin 6 → ℝ × ℝ)
    (h012 : 0 < PlanarDet.sig (v 0) (v 1) (v 2))
    (hframe : HexagonFrameRigidity.IsAffineRegularFrame
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :
    GaugeEquivalent hex6 v := by
  refine ⟨Equiv.refl _, frameGauge (v 0) (v 1) (v 2) h012, ?_⟩
  simp only [Equiv.refl_apply]
  funext i
  fin_cases i
  · change v 0 = (frameGauge (v 0) (v 1) (v 2) h012).map (hex6 0)
    rw [hex6_zero, frameGauge_map]
    simp only [HexagonFrameRigidity.framePoint]
    ext <;> norm_num
  · change v 1 = (frameGauge (v 0) (v 1) (v 2) h012).map (hex6 1)
    rw [hex6_one, frameGauge_map]
    simp only [HexagonFrameRigidity.framePoint]
    ext <;> norm_num
  · change v 2 = (frameGauge (v 0) (v 1) (v 2) h012).map (hex6 2)
    rw [hex6_two, frameGauge_map]
    simp only [HexagonFrameRigidity.framePoint]
    ext <;> norm_num
  · change v 3 = (frameGauge (v 0) (v 1) (v 2) h012).map (hex6 3)
    rw [hex6_three, frameGauge_map]
    convert hframe.1 using 1 <;> norm_num
  · change v 4 = (frameGauge (v 0) (v 1) (v 2) h012).map (hex6 4)
    rw [hex6_four, frameGauge_map]
    convert hframe.2.1 using 1 <;> norm_num
  · change v 5 = (frameGauge (v 0) (v 1) (v 2) h012).map (hex6 5)
    rw [hex6_five, frameGauge_map]
    convert hframe.2.2 using 1 <;> norm_num

/-- Packet-facing equality classification in gauge language. -/
theorem hullSixPacket_gauge
    (v : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (P : FiniteHullCases.Hull6Packet v)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (harea : HexagonGeometryRigidity.fanArea v = 6 * m) :
    GaugeEquivalent hex6 v := by
  have hframe := HexagonGeometryRigidity.hullSixPacket_rigid
    v m hm P hmin harea
  exact affineRegularFrame_gauge v
    (P.strict 0 1 2 (by decide) (by decide)) hframe

/-- The same conclusion transported back through the relabelling returned by
the finite hull classifier. -/
theorem relabelledHullSixPacket_gauge
    (u v : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (hrel : FiniteHullCases.Relabels u v)
    (P : FiniteHullCases.Hull6Packet v)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (harea : HexagonGeometryRigidity.fanArea v = 6 * m) :
    GaugeEquivalent hex6 u := by
  apply GaugeAlgebra.gaugeEquivalent_of_relabels_right hrel
  exact hullSixPacket_gauge v m hm P hmin harea

/-- Two configurations individually gauge-equivalent to `hex6` are
gauge-equivalent to each other. -/
theorem pairwise_gauge
    {u v : Fin 6 → ℝ × ℝ}
    (hu : GaugeEquivalent hex6 u) (hv : GaugeEquivalent hex6 v) :
    GaugeEquivalent u v :=
  GaugeAlgebra.gaugeEquivalent_trans
    (GaugeAlgebra.gaugeEquivalent_symm hu) hv

end HexagonGauge
end N6Scratch
