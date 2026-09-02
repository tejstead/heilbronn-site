import Heil6.PlanarDet
import Heil6.PentagonScalar

set_option linter.style.header false

/-!
# Geometry adapter for a pentagonal hull with one interior point

The labelling is deliberately concrete.  `x 0,…,x 4` are the hull vertices in
strict counter-clockwise order and `x 5` is the interior point.  The five
`hfan` assumptions are exactly the strict interior condition expressed by the
five boundary half-planes.  The theorem then derives every hypothesis of
`PentagonScalar.pentagon_strict` by determinant algebra.

The conclusion uses the three-triangle fan from the first hull vertex, hence
is ready for `HullBridge.volume_convexHull_strictCCW5` after integration.
-/

namespace N6Scratch
namespace PentagonGeometry

open PlanarDet

private lemma floor_of_abs_of_pos {m x : ℝ}
    (hfloor : m ≤ |x|) (hpos : 0 < x) : m ≤ x := by
  simpa only [abs_of_pos hpos] using hfloor

/-- The `h = 5` hull case is not merely bounded by `6m`: it is strict. -/
theorem interior_pentagon_strict
    (x : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (hHull : ∀ i j k : Fin 5, i < j → j < k →
      0 < sig (x i.castSucc) (x j.castSucc) (x k.castSucc))
    (hfan0 : 0 < sig (x 5) (x 0) (x 1))
    (hfan1 : 0 < sig (x 5) (x 1) (x 2))
    (hfan2 : 0 < sig (x 5) (x 2) (x 3))
    (hfan3 : 0 < sig (x 5) (x 3) (x 4))
    (hfan4 : 0 < sig (x 5) (x 4) (x 0))
    (hmin : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |sig (x i) (x j) (x k)|) :
    6 * m <
      sig (x 0) (x 1) (x 2) + sig (x 0) (x 2) (x 3)
        + sig (x 0) (x 3) (x 4) := by
  let a0 := sig (x 5) (x 0) (x 1)
  let a1 := sig (x 5) (x 1) (x 2)
  let a2 := sig (x 5) (x 2) (x 3)
  let a3 := sig (x 5) (x 3) (x 4)
  let a4 := sig (x 5) (x 4) (x 0)
  let b0 := sig (x 5) (x 0) (x 2)
  let b1 := sig (x 5) (x 1) (x 3)
  let b2 := sig (x 5) (x 2) (x 4)
  let b3 := sig (x 5) (x 3) (x 0)
  let b4 := sig (x 5) (x 4) (x 1)

  have ha0 : m ≤ a0 := floor_of_abs_of_pos
    (hmin 5 0 1 (by decide) (by decide) (by decide)) hfan0
  have ha1 : m ≤ a1 := floor_of_abs_of_pos
    (hmin 5 1 2 (by decide) (by decide) (by decide)) hfan1
  have ha2 : m ≤ a2 := floor_of_abs_of_pos
    (hmin 5 2 3 (by decide) (by decide) (by decide)) hfan2
  have ha3 : m ≤ a3 := floor_of_abs_of_pos
    (hmin 5 3 4 (by decide) (by decide) (by decide)) hfan3
  have ha4 : m ≤ a4 := floor_of_abs_of_pos
    (hmin 5 4 0 (by decide) (by decide) (by decide)) hfan4
  have hab0 : m ≤ |b0| := hmin 5 0 2 (by decide) (by decide) (by decide)
  have hab1 : m ≤ |b1| := hmin 5 1 3 (by decide) (by decide) (by decide)
  have hab2 : m ≤ |b2| := hmin 5 2 4 (by decide) (by decide) (by decide)
  have hab3 : m ≤ |b3| := hmin 5 3 0 (by decide) (by decide) (by decide)
  have hab4 : m ≤ |b4| := hmin 5 4 1 (by decide) (by decide) (by decide)

  have he0pos : 0 < sig (x 0) (x 1) (x 2) :=
    hHull 0 1 2 (by decide) (by decide)
  have he1pos : 0 < sig (x 1) (x 2) (x 3) :=
    hHull 1 2 3 (by decide) (by decide)
  have he2pos : 0 < sig (x 2) (x 3) (x 4) :=
    hHull 2 3 4 (by decide) (by decide)
  have he3pos : 0 < sig (x 3) (x 4) (x 0) := by
    rw [← sig_rotate (x 0) (x 3) (x 4)]
    exact hHull 0 3 4 (by decide) (by decide)
  have he4pos : 0 < sig (x 4) (x 0) (x 1) := by
    rw [sig_rotate (x 4) (x 0) (x 1)]
    exact hHull 0 1 4 (by decide) (by decide)

  have hear0id : a0 + a1 - b0 = sig (x 0) (x 1) (x 2) := by
    dsimp [a0, a1, b0, sig]
    ring
  have hear1id : a1 + a2 - b1 = sig (x 1) (x 2) (x 3) := by
    dsimp [a1, a2, b1, sig]
    ring
  have hear2id : a2 + a3 - b2 = sig (x 2) (x 3) (x 4) := by
    dsimp [a2, a3, b2, sig]
    ring
  have hear3id : a3 + a4 - b3 = sig (x 3) (x 4) (x 0) := by
    dsimp [a3, a4, b3, sig]
    ring
  have hear4id : a4 + a0 - b4 = sig (x 4) (x 0) (x 1) := by
    dsimp [a4, a0, b4, sig]
    ring
  have hear0 : m ≤ a0 + a1 - b0 := by
    rw [hear0id]
    exact floor_of_abs_of_pos
      (hmin 0 1 2 (by decide) (by decide) (by decide)) he0pos
  have hear1 : m ≤ a1 + a2 - b1 := by
    rw [hear1id]
    exact floor_of_abs_of_pos
      (hmin 1 2 3 (by decide) (by decide) (by decide)) he1pos
  have hear2 : m ≤ a2 + a3 - b2 := by
    rw [hear2id]
    exact floor_of_abs_of_pos
      (hmin 2 3 4 (by decide) (by decide) (by decide)) he2pos
  have hear3 : m ≤ a3 + a4 - b3 := by
    rw [hear3id]
    exact floor_of_abs_of_pos
      (hmin 3 4 0 (by decide) (by decide) (by decide)) he3pos
  have hear4 : m ≤ a4 + a0 - b4 := by
    rw [hear4id]
    exact floor_of_abs_of_pos
      (hmin 4 0 1 (by decide) (by decide) (by decide)) he4pos

  have hq0id : a0 + b1 + b3 = sig (x 0) (x 1) (x 3) := by
    dsimp [a0, b1, b3, sig]
    ring
  have hq1id : a1 + b2 + b4 = sig (x 1) (x 2) (x 4) := by
    dsimp [a1, b2, b4, sig]
    ring
  have hq2id : a2 + b3 + b0 = sig (x 0) (x 2) (x 3) := by
    dsimp [a2, b3, b0, sig]
    ring
  have hq3id : a3 + b4 + b1 = sig (x 1) (x 3) (x 4) := by
    dsimp [a3, b4, b1, sig]
    ring
  have hq4id : a4 + b0 + b2 = sig (x 0) (x 2) (x 4) := by
    dsimp [a4, b0, b2, sig]
    ring
  have hq0 : 0 < a0 + b1 + b3 := by
    rw [hq0id]
    exact hHull 0 1 3 (by decide) (by decide)
  have hq1 : 0 < a1 + b2 + b4 := by
    rw [hq1id]
    exact hHull 1 2 4 (by decide) (by decide)
  have hq2 : 0 < a2 + b3 + b0 := by
    rw [hq2id]
    exact hHull 0 2 3 (by decide) (by decide)
  have hq3 : 0 < a3 + b4 + b1 := by
    rw [hq3id]
    exact hHull 1 3 4 (by decide) (by decide)
  have hq4 : 0 < a4 + b0 + b2 := by
    rw [hq4id]
    exact hHull 0 2 4 (by decide) (by decide)

  have hR0 : a0 * a2 = b0 * b1 + a1 * b3 := by
    dsimp [a0, a2, b0, b1, a1, b3, sig]
    ring
  have hR1 : a1 * a3 = b1 * b2 + a2 * b4 := by
    dsimp [a1, a3, b1, b2, a2, b4, sig]
    ring
  have hR2 : a2 * a4 = b2 * b3 + a3 * b0 := by
    dsimp [a2, a4, b2, b3, a3, b0, sig]
    ring
  have hR3 : a3 * a0 = b3 * b4 + a4 * b1 := by
    dsimp [a3, a0, b3, b4, a4, b1, sig]
    ring
  have hR4 : a4 * a1 = b4 * b0 + a0 * b2 := by
    dsimp [a4, a1, b4, b0, a0, b2, sig]
    ring

  have hscalar := PentagonScalar.pentagon_strict
    m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hm
    ha0 ha1 ha2 ha3 ha4 hab0 hab1 hab2 hab3 hab4
    hear0 hear1 hear2 hear3 hear4 hq0 hq1 hq2 hq3 hq4
    hR0 hR1 hR2 hR3 hR4
  have harea :
      a0 + a1 + a2 + a3 + a4 =
        sig (x 0) (x 1) (x 2) + sig (x 0) (x 2) (x 3)
          + sig (x 0) (x 3) (x 4) := by
    dsimp [a0, a1, a2, a3, a4, sig]
    ring
  linarith

end PentagonGeometry
end N6Scratch
