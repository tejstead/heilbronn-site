import Heil6.FiniteHullCases
import Heil6.HexagonGeometry
import Heil6.HexagonFrameRigidity

set_option linter.style.header false

/-!
# Equality rigidity for the convex-hexagon case

`HexagonGeometry.strictCCW_cycle_bound` proves the sharp inequality.  This
module runs the same short determinant dictionary through
`HexagonScalar.cycle_rigidity` when equality holds, and then applies
`HexagonFrameRigidity.determinant_table_rigid`.

The final corollary is stated directly for `FiniteHullCases.Hull6Packet`, so
the finite hull classifier can use it without exposing any scalar variables.
-/

namespace N6Scratch
namespace HexagonGeometryRigidity

open PlanarDet

/-- The four-triangle fan from the first vertex of a labelled hexagon. -/
def fanArea (v : Fin 6 → ℝ × ℝ) : ℝ :=
  sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) +
    sig (v 0) (v 3) (v 4) + sig (v 0) (v 4) (v 5)

private lemma floor_of_abs_of_pos {m x : ℝ}
    (hfloor : m ≤ |x|) (hpos : 0 < x) : m ≤ x := by
  simpa only [abs_of_pos hpos] using hfloor

/-- Equality in the strict-CCW six-hull inequality forces the affine-regular
determinant table. -/
theorem strictCCW_cycle_rigid
    (v : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (hpos : ∀ i j k : Fin 6, i < j → j < k →
      0 < sig (v i) (v j) (v k))
    (hmin : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |sig (v i) (v j) (v k)|)
    (harea : fanArea v = 6 * m) :
    HexagonFrameRigidity.IsAffineRegularFrame
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  let T := sig (v 0) (v 2) (v 4)
  let E0 := sig (v 0) (v 1) (v 5)
  let E1 := sig (v 0) (v 1) (v 2)
  let E2 := sig (v 1) (v 2) (v 3)
  let E3 := sig (v 2) (v 3) (v 4)
  let E4 := sig (v 3) (v 4) (v 5)
  let E5 := sig (v 0) (v 4) (v 5)
  let P := sig (v 0) (v 1) (v 4)
  let Pc := sig (v 1) (v 2) (v 4)
  let Q := sig (v 0) (v 2) (v 3)
  let Qc := sig (v 0) (v 3) (v 4)
  let R := sig (v 0) (v 2) (v 5)
  let Rc := sig (v 2) (v 4) (v 5)
  let H := fanArea v

  have hT : 0 < T := hpos 0 2 4 (by decide) (by decide)
  have hE1 : 0 < E1 := hpos 0 1 2 (by decide) (by decide)
  have hE3 : 0 < E3 := hpos 2 3 4 (by decide) (by decide)
  have hE5 : 0 < E5 := hpos 0 4 5 (by decide) (by decide)
  have hP : 0 < P := hpos 0 1 4 (by decide) (by decide)
  have hPc : 0 < Pc := hpos 1 2 4 (by decide) (by decide)
  have hQ : 0 < Q := hpos 0 2 3 (by decide) (by decide)
  have hQc : 0 < Qc := hpos 0 3 4 (by decide) (by decide)
  have hR : 0 < R := hpos 0 2 5 (by decide) (by decide)
  have hRc : 0 < Rc := hpos 2 4 5 (by decide) (by decide)

  have hmT : m ≤ T := floor_of_abs_of_pos
    (hmin 0 2 4 (by decide) (by decide) (by decide)) hT
  have hmE0 : m ≤ E0 := floor_of_abs_of_pos
    (hmin 0 1 5 (by decide) (by decide) (by decide))
    (hpos 0 1 5 (by decide) (by decide))
  have hmE1 : m ≤ E1 := floor_of_abs_of_pos
    (hmin 0 1 2 (by decide) (by decide) (by decide)) hE1
  have hmE2 : m ≤ E2 := floor_of_abs_of_pos
    (hmin 1 2 3 (by decide) (by decide) (by decide))
    (hpos 1 2 3 (by decide) (by decide))
  have hmE3 : m ≤ E3 := floor_of_abs_of_pos
    (hmin 2 3 4 (by decide) (by decide) (by decide)) hE3
  have hmE4 : m ≤ E4 := floor_of_abs_of_pos
    (hmin 3 4 5 (by decide) (by decide) (by decide))
    (hpos 3 4 5 (by decide) (by decide))
  have hmE5 : m ≤ E5 := floor_of_abs_of_pos
    (hmin 0 4 5 (by decide) (by decide) (by decide)) hE5

  have harea' : T + E1 + E3 + E5 = H := by
    dsimp [T, E1, E3, E5, H, fanArea, sig]
    ring
  have hsumP : P + Pc = T + E1 := by
    dsimp [P, Pc, T, E1, sig]
    ring
  have hsumQ : Q + Qc = T + E3 := by
    dsimp [Q, Qc, T, E3, sig]
    ring
  have hsumR : R + Rc = T + E5 := by
    dsimp [R, Rc, T, E5, sig]
    ring
  have hprodP : P * R = E1 * E5 + E0 * T := by
    dsimp [P, R, E1, E5, E0, T, sig]
    ring
  have hprodQ : Q * Pc = E1 * E3 + E2 * T := by
    dsimp [Q, Pc, E1, E3, E2, T, sig]
    ring
  have hprodR : Qc * Rc = E3 * E5 + E4 * T := by
    dsimp [Qc, Rc, E3, E5, E4, T, sig]
    ring

  have hrig := HexagonScalar.cycle_rigidity
    m H T E0 E1 E2 E3 E4 E5 P Pc Q Qc R Rc
    hm hT hE1 hE3 hE5 hP hPc hQ hQc hR hRc
    hmT hmE0 hmE1 hmE2 hmE3 hmE4 hmE5
    harea' (by simpa only [H] using harea)
    hsumP hsumQ hsumR hprodP hprodQ hprodR
  rcases hrig with
    ⟨hE0eq, hE1eq, hE2eq, hE3eq, hE4eq, hE5eq,
      hTeq, hPeq, hPceq, hQeq, hQceq, hReq, hRceq⟩

  apply HexagonFrameRigidity.determinant_table_rigid
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) m hm
  · simpa only [E1, HexagonFrameRigidity.sig, PlanarDet.sig] using hE1eq
  · simpa only [Q, HexagonFrameRigidity.sig, PlanarDet.sig] using hQeq
  · simpa only [E2, HexagonFrameRigidity.sig, PlanarDet.sig] using hE2eq
  · simpa only [P, HexagonFrameRigidity.sig, PlanarDet.sig] using hPeq
  · simpa only [T, HexagonFrameRigidity.sig, PlanarDet.sig] using hTeq
  · simpa only [E0, HexagonFrameRigidity.sig, PlanarDet.sig] using hE0eq
  · simpa only [R, HexagonFrameRigidity.sig, PlanarDet.sig] using hReq

/-- Packet-facing equality rigidity for the six-hull output of the finite
classifier. -/
theorem hullSixPacket_rigid
    (v : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (P : FiniteHullCases.Hull6Packet v)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (harea : fanArea v = 6 * m) :
    HexagonFrameRigidity.IsAffineRegularFrame
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  exact strictCCW_cycle_rigid v m hm P.strict hmin harea

end HexagonGeometryRigidity
end N6Scratch
