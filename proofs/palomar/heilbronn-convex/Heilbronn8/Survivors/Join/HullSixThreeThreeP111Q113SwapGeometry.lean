import Heilbronn8.Survivors.Join.HullSixThreeThreeP022XFrontier

/-!
# Honest complement-transpose custody for the `3 + 3` q113 seam

Swapping the two exterior points and rotating a `3 + 3` frame by three
places exchanges its upper and lower blocks.  In the resulting frame the
cross determinants are

```text
X' i j = sig Q L_i U_j = -Y j i.
```

Consequently the three diagonal q113 floors become exactly the three
`p = 022` floors consumed by `threeThreeP022At_false`.  This is a geometric
frame transport, not merely a finite-table identity.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private noncomputable def threeThree_swapOrientedView
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {P Q : Fin 8}
    (V : HullSixOrientedView cfg cycle P Q) :
    HullSixOrientedView cfg cycle Q P where
  P_outside := V.Q_outside
  Q_outside := V.P_outside
  P_boundary_pos := V.Q_boundary_pos
  Q_boundary_pos := V.P_boundary_pos
  P_fan_sum := by
    calc
      sumFinSix (fun i =>
          sig (cfg Q) (cfg (cycle i)) (cfg (cycle (i + 1)))) =
          fanSum cfg cycle :=
        sumFinSix_boundary_eq_fanSum cfg cycle Q
      _ = sumFinSix (fun i =>
          sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))) :=
        (sumFinSix_boundary_eq_fanSum cfg cycle P).symm
      _ = doubledHullArea cfg := V.P_fan_sum
  lineLevel_floor := by
    intro i
    have h := V.lineLevel_floor i
    rw [sig_swap_first, abs_neg]
    exact h

private theorem threeThree_add_three_upper
    (rotation : Fin 6) (i : Fin 3) :
    (rotation + 3) + hullSixThreeThreeUpperOffset i =
      rotation + hullSixThreeThreeLowerOffset i := by
  fin_cases rotation <;> fin_cases i <;> decide

private theorem threeThree_add_three_lower
    (rotation : Fin 6) (i : Fin 3) :
    (rotation + 3) + hullSixThreeThreeLowerOffset i =
      rotation + hullSixThreeThreeUpperOffset i := by
  fin_cases rotation <;> fin_cases i <;> decide

namespace HullSixCompactCrossChordResidual

/-- The q113 diagonal signs close after honest complement-transpose custody.
The statement deliberately needs no `X` signs or height ordering. -/
theorem threeThreeP111Q113At_false
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : forall i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : forall j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hY00 : minTri cfg <= sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hY11 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) <=
        -minTri cfg)
    (hY22 : minTri cfg <= sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let Vswap : HullSixOrientedView cfg cycle Q P :=
    threeThree_swapOrientedView V
  let rotationSwap : Fin 6 := rotation + 3

  have hupperSwap : forall i : Fin 3,
      0 < sig (cfg Q) (cfg P)
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeUpperOffset i))) := by
    intro i
    rw [show rotationSwap + hullSixThreeThreeUpperOffset i =
      rotation + hullSixThreeThreeLowerOffset i by
        simpa [rotationSwap] using threeThree_add_three_upper rotation i]
    rw [sig_swap_first]
    exact neg_pos.mpr (hlower i)

  have hlowerSwap : forall j : Fin 3,
      sig (cfg Q) (cfg P)
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeLowerOffset j))) < 0 := by
    intro j
    rw [show rotationSwap + hullSixThreeThreeLowerOffset j =
      rotation + hullSixThreeThreeUpperOffset j by
        simpa [rotationSwap] using threeThree_add_three_lower rotation j]
    rw [sig_swap_first]
    linarith [hupper j]

  have hX00Swap : sig (cfg Q)
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeUpperOffset 0)))
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeLowerOffset 0))) <=
      -minTri cfg := by
    rw [show rotationSwap + hullSixThreeThreeUpperOffset 0 =
      rotation + hullSixThreeThreeLowerOffset 0 by
        simpa [rotationSwap] using threeThree_add_three_upper rotation 0]
    rw [show rotationSwap + hullSixThreeThreeLowerOffset 0 =
      rotation + hullSixThreeThreeUpperOffset 0 by
        simpa [rotationSwap] using threeThree_add_three_lower rotation 0]
    rw [sig_swap]
    exact neg_le_neg hY00

  have hX11Swap : minTri cfg <= sig (cfg Q)
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeLowerOffset 1))) := by
    rw [show rotationSwap + hullSixThreeThreeUpperOffset 1 =
      rotation + hullSixThreeThreeLowerOffset 1 by
        simpa [rotationSwap] using threeThree_add_three_upper rotation 1]
    rw [show rotationSwap + hullSixThreeThreeLowerOffset 1 =
      rotation + hullSixThreeThreeUpperOffset 1 by
        simpa [rotationSwap] using threeThree_add_three_lower rotation 1]
    rw [sig_swap]
    linarith

  have hX22Swap : sig (cfg Q)
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeUpperOffset 2)))
        (cfg (cycle
          (rotationSwap + hullSixThreeThreeLowerOffset 2))) <=
      -minTri cfg := by
    rw [show rotationSwap + hullSixThreeThreeUpperOffset 2 =
      rotation + hullSixThreeThreeLowerOffset 2 by
        simpa [rotationSwap] using threeThree_add_three_upper rotation 2]
    rw [show rotationSwap + hullSixThreeThreeLowerOffset 2 =
      rotation + hullSixThreeThreeUpperOffset 2 by
        simpa [rotationSwap] using threeThree_add_three_lower rotation 2]
    rw [sig_swap]
    exact neg_le_neg hY22

  exact R.threeThreeP022At_false Vswap rotationSwap
    hupperSwap hlowerSwap hX00Swap hX11Swap hX22Swap

/-- In a `p = 111` frame the positive `X00` floor and the two line-level
floors imply the positive `Y00` floor needed by complement-transpose. -/
theorem threeThreeP111Q113At_false_of_X00
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : forall i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : forall j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hX00 : minTri cfg <= sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hY11 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) <=
        -minTri cfg)
    (hY22 : minTri cfg <= sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let U0 :=
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0))
  let L0 :=
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))
  have hu0 : minTri cfg <= sig (cfg P) (cfg Q) U0 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    simpa [U0] using h
  have hv0 : minTri cfg <= -sig (cfg P) (cfg Q) L0 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    simpa [L0] using h
  have hbase := sig_crossChord_base_change (cfg P) (cfg Q) U0 L0
  have hY00 : minTri cfg <= sig (cfg Q) U0 L0 := by
    have hX00' : minTri cfg <= sig (cfg P) U0 L0 := by
      simpa [U0, L0] using hX00
    nlinarith [R.minTri_pos]
  apply R.threeThreeP111Q113At_false V rotation hupper hlower
  · simpa [U0, L0] using hY00
  · exact hY11
  · exact hY22

end HullSixCompactCrossChordResidual

end Heilbronn8
