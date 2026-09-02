import Heil6.PlanarDet
import Heil6.HexagonScalar

set_option linter.style.header false

/-!
# Geometry adapter for the convex-hexagon scalar theorem

This file is the entire geometric input needed after six points have been
relabelled in strict counter-clockwise hull order.  It turns the determinant
table into `HexagonScalar.cycle_bound`; all three additive identities and all
three Pluecker identities are proved here by their polynomial definitions.

The right-hand side is the usual four-triangle fan from vertex zero.  In the
Palomar package `HullBridge.volume_convexHull_strictCCW6` identifies it with
the doubled Lebesgue area of the hull.
-/

namespace N6Scratch
namespace HexagonGeometry

open PlanarDet

private lemma floor_of_abs_of_pos {m x : ℝ}
    (hfloor : m ≤ |x|) (hpos : 0 < x) : m ≤ x := by
  simpa only [abs_of_pos hpos] using hfloor

/-- A strict CCW hexagon whose every labelled triangle has doubled area at
least `m` has doubled hull area at least `6m`.

No convex-hull machinery is hidden in the statement: `hpos` says precisely
that `v 0,…,v 5` are already in strict CCW order, and `hmin` is the global
triangle floor inherited from the six-point configuration. -/
theorem strictCCW_cycle_bound
    (v : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (hpos : ∀ i j k : Fin 6, i < j → j < k →
      0 < sig (v i) (v j) (v k))
    (hmin : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |sig (v i) (v j) (v k)|) :
    6 * m ≤
      sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)
        + sig (v 0) (v 3) (v 4) + sig (v 0) (v 4) (v 5) := by
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
  let H :=
    sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)
      + sig (v 0) (v 3) (v 4) + sig (v 0) (v 4) (v 5)

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

  have harea : T + E1 + E3 + E5 = H := by
    dsimp [T, E1, E3, E5, H, sig]
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

  have hbound := HexagonScalar.cycle_bound
    m H T E0 E1 E2 E3 E4 E5 P Pc Q Qc R Rc
    hm hT hE1 hE3 hE5 hP hPc hQ hQc hR hRc
    hmT hmE0 hmE1 hmE2 hmE3 hmE4 hmE5
    harea hsumP hsumQ hsumR hprodP hprodQ hprodR
  simpa only [H] using hbound

end HexagonGeometry
end N6Scratch
