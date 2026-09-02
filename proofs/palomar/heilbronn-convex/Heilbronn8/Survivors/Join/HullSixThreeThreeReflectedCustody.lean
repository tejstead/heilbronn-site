import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeFiniteBridge

/-!
# Honest complement-transpose custody for `3 + 3` frames

Unlike the rectangular `2 + 4` split, a `3 + 3` frame stays in the same
configuration after exchanging its two exterior base points: advancing the
rotation by three exchanges the two equal-sized sign blocks.  If the source
cross determinants are `X,Y`, the resulting frame has

```text
X' i j = sig Q L_i U_j = -Y j i,
Y' i j = sig P L_i U_j = -X j i.
```

This is exactly the determinant action represented by the finite
`complementTranspose` cut operation.  The construction below carries the
full geometric frame and therefore does not assume an abstract table
symmetry.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-! ## The swapped oriented view and the block exchange -/

/-- Exchange the two actual off-cycle base points in an oriented view. -/
private noncomputable def threeThreeSwapOrientedView
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

/-- Advancing by three turns a new upper offset into the corresponding old
lower offset. -/
private theorem threeThreeSwap_add_three_upper
    (rotation : Fin 6) (i : Fin 3) :
    (rotation + 3) + hullSixThreeThreeUpperOffset i =
      rotation + hullSixThreeThreeLowerOffset i := by
  fin_cases rotation <;> fin_cases i <;> decide

/-- Advancing by three turns a new lower offset into the corresponding old
upper offset. -/
private theorem threeThreeSwap_add_three_lower
    (rotation : Fin 6) (i : Fin 3) :
    (rotation + 3) + hullSixThreeThreeLowerOffset i =
      rotation + hullSixThreeThreeUpperOffset i := by
  fin_cases rotation <;> fin_cases i <;> decide

/-- Exchanging the selected orientation of the two off-cycle labels still
selects the same unordered residual pair. -/
private theorem threeThreeIsOrientedPair_swap
    {p q P Q : Fin 8} (h : HullSixIsOrientedPair p q P Q) :
    HullSixIsOrientedPair p q Q P := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

namespace HullSixThreeThreeGeometricFrame

/-- Exchange `P,Q` and advance the cyclic frame by three places.  Because
both sign blocks have size three, this is an honest frame on the same
configuration, cycle, and compact residual. -/
noncomputable def swapRotateThree
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    HullSixThreeThreeGeometricFrame R where
  P := F.Q
  Q := F.P
  pair := threeThreeIsOrientedPair_swap F.pair
  view := threeThreeSwapOrientedView F.view
  rotation := F.rotation + 3
  upper_pos := by
    intro i
    rw [threeThreeSwap_add_three_upper, sig_swap_first]
    exact neg_pos.mpr (F.lower_neg i)
  lower_neg := by
    intro j
    rw [threeThreeSwap_add_three_lower, sig_swap_first]
    linarith [F.upper_pos j]

@[simp] theorem swapRotateThree_P
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.swapRotateThree.P = F.Q := rfl

@[simp] theorem swapRotateThree_Q
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.swapRotateThree.Q = F.P := rfl

@[simp] theorem swapRotateThree_rotation
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.swapRotateThree.rotation = F.rotation + 3 := rfl

/-- The new `P`-based determinant is the negated transpose of the old
`Q`-based determinant. -/
theorem swapRotateThree_pDet
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) (i j : Fin 3) :
    sig (cfg F.swapRotateThree.P)
        (cfg (cycle (F.swapRotateThree.rotation +
          hullSixThreeThreeUpperOffset i)))
        (cfg (cycle (F.swapRotateThree.rotation +
          hullSixThreeThreeLowerOffset j))) =
      -sig (cfg F.Q)
        (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset j)))
        (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset i))) := by
  change sig (cfg F.Q)
      (cfg (cycle ((F.rotation + 3) +
        hullSixThreeThreeUpperOffset i)))
      (cfg (cycle ((F.rotation + 3) +
        hullSixThreeThreeLowerOffset j))) = _
  rw [threeThreeSwap_add_three_upper,
    threeThreeSwap_add_three_lower, sig_swap]

/-- The new `Q`-based determinant is the negated transpose of the old
`P`-based determinant. -/
theorem swapRotateThree_qDet
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) (i j : Fin 3) :
    sig (cfg F.swapRotateThree.Q)
        (cfg (cycle (F.swapRotateThree.rotation +
          hullSixThreeThreeUpperOffset i)))
        (cfg (cycle (F.swapRotateThree.rotation +
          hullSixThreeThreeLowerOffset j))) =
      -sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset j)))
        (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset i))) := by
  change sig (cfg F.P)
      (cfg (cycle ((F.rotation + 3) +
        hullSixThreeThreeUpperOffset i)))
      (cfg (cycle ((F.rotation + 3) +
        hullSixThreeThreeLowerOffset j))) = _
  rw [threeThreeSwap_add_three_upper,
    threeThreeSwap_add_three_lower, sig_swap]

/-- Exact table realization transports to complement-transposition in the
explicit swapped-and-rotated geometric frame. -/
theorem tableHolds_complementTranspose
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    {T : HullSixThreeThreeCuts} (hLegal : T.Legal)
    (hTable : F.TableHolds T) :
    F.swapRotateThree.TableHolds T.complementTranspose := by
  intro i j
  rw [HullSixThreeThreeCuts.table_complementTranspose T hLegal i j]
  have hsource := hTable j i
  have hcomplement :=
    (HullSixChamberLabel.holds_complement_neg_swap_iff
      (T.table j i) (minTri cfg)
      (sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset j)))
        (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset i))))
      (sig (cfg F.Q)
        (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset j)))
        (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset i))))).2
      hsource
  rw [swapRotateThree_pDet F i j, swapRotateThree_qDet F i j]
  exact hcomplement

end HullSixThreeThreeGeometricFrame

/-! ## Provider-level exact custody -/

/-- Pull an exact packet provider back through the honest physical `P/Q`
swap and three-place rotation. -/
theorem hullSixThreeThreeExactPacketProvider_complementTranspose
    {Packet : HullSixThreeThreeCuts -> Prop}
    (hPacket : HullSixThreeThreeExactPacketProvider Packet) :
    HullSixThreeThreeExactPacketProvider
      (fun T => Packet T.complementTranspose) := by
  intro cfg cycle p q R F
  intro T hLegal hTarget hTable
  have hLegalTarget : T.complementTranspose.Legal := by
    simpa [HullSixThreeThreeCuts.act] using
      (HullSixThreeThreeCuts.legal_act
        HullSixThreeThreeCuts.Symmetry.complementTranspose T hLegal)
  exact hPacket F.swapRotateThree T.complementTranspose
    hLegalTarget hTarget
    (F.tableHolds_complementTranspose hLegal hTable)

end Heilbronn8
