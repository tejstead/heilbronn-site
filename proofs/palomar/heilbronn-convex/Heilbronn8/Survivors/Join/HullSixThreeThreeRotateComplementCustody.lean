import Heilbronn8.Survivors.Join.HullSixTwoFourReflectedCustody
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeFiniteBridge

/-!
# Honest reflected rotate-complement custody for `3 + 3` frames

The reflection-and-cycle-reversal construction used for `2 + 4` frames is
independent of the sign-block sizes.  For equal blocks of size three, reverse
the cycle about `rotation + 2`, exchange the two oriented residual labels, and
reverse both three-element blocks.  The resulting cross determinants are

```text
X' i j = -Y (2-i) (2-j),
Y' i j = -X (2-i) (2-j).
```

This is the honest geometric realization of the finite
`rotateComplement` action.  The complete compact residual is rebuilt by the
public reflection custody from `HullSixTwoFourReflectedCustody`; no abstract
table symmetry is assumed.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-! ## Reversal of the two three-element blocks -/

@[simp] theorem hullSixReverseAt_threeThreeUpperOffset
    (rotation : Fin 6) (i : Fin 3) :
    hullSixReverseAt (rotation + 1) (hullSixThreeThreeUpperOffset i) =
      rotation +
        hullSixThreeThreeUpperOffset (hullSixReverseFinThree i) := by
  fin_cases rotation <;> fin_cases i <;> decide

@[simp] theorem hullSixReverseAt_threeThreeLowerOffset
    (rotation : Fin 6) (j : Fin 3) :
    hullSixReverseAt (rotation + 1) (hullSixThreeThreeLowerOffset j) =
      rotation +
        hullSixThreeThreeLowerOffset (hullSixReverseFinThree j) := by
  fin_cases rotation <;> fin_cases j <;> decide

private theorem threeThreeReflected_isOrientedPair_swap
    {p q P Q : Fin 8} (h : HullSixIsOrientedPair p q P Q) :
    HullSixIsOrientedPair p q Q P := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

private noncomputable def threeThreeReflected_orientedViewOfPair
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (h : HullSixIsOrientedPair p q P Q) :
    HullSixOrientedView cfg cycle P Q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact R.forwardOrientedView
  · exact R.swappedOrientedView

/-! ## The reflected `3 + 3` frame -/

namespace HullSixThreeThreeGeometricFrame

/-- The honest reflected frame realizing finite complement-rotation. -/
noncomputable def reflectedRotateComplement
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    HullSixThreeThreeGeometricFrame
      (R.reflectReverse (F.rotation + 1)) where
  P := F.Q
  Q := F.P
  pair := threeThreeReflected_isOrientedPair_swap F.pair
  view := threeThreeReflected_orientedViewOfPair
    (R.reflectReverse (F.rotation + 1))
    (threeThreeReflected_isOrientedPair_swap F.pair)
  rotation := 0
  upper_pos := by
    intro i
    have h := F.upper_pos (hullSixReverseFinThree i)
    simp only [hullSixReflectedConfiguration, hullSixReflectedCycle,
      zero_add]
    rw [sig_hullSixReflectionPoint_swapFirst,
      hullSixReverseAt_threeThreeUpperOffset]
    exact h
  lower_neg := by
    intro j
    have h := F.lower_neg (hullSixReverseFinThree j)
    simp only [hullSixReflectedConfiguration, hullSixReflectedCycle,
      zero_add]
    rw [sig_hullSixReflectionPoint_swapFirst,
      hullSixReverseAt_threeThreeLowerOffset]
    exact h

@[simp] theorem reflectedRotateComplement_P
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.reflectedRotateComplement.P = F.Q := rfl

@[simp] theorem reflectedRotateComplement_Q
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.reflectedRotateComplement.Q = F.P := rfl

@[simp] theorem reflectedRotateComplement_rotation
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.reflectedRotateComplement.rotation = 0 := rfl

/-- Exact realization transports to complement-rotation in the reflected
configuration. -/
theorem tableHolds_reflectedRotateComplement
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    {T : HullSixThreeThreeCuts} (hLegal : T.Legal)
    (hTable : F.TableHolds T) :
    F.reflectedRotateComplement.TableHolds
      (HullSixThreeThreeCuts.act
        HullSixThreeThreeCuts.Symmetry.rotateComplement T) := by
  intro i j
  rw [HullSixThreeThreeCuts.table_rotateComplement T hLegal i j]
  have hsource := hTable
    (hullSixReverseFinThree i) (hullSixReverseFinThree j)
  have hcomplement :=
    (HullSixChamberLabel.holds_complement_neg_swap_iff
      (T.table (hullSixReverseFinThree i) (hullSixReverseFinThree j))
      (minTri cfg)
      (sig (cfg F.P)
        (cfg (cycle (F.rotation +
          hullSixThreeThreeUpperOffset (hullSixReverseFinThree i))))
        (cfg (cycle (F.rotation +
          hullSixThreeThreeLowerOffset (hullSixReverseFinThree j)))))
      (sig (cfg F.Q)
        (cfg (cycle (F.rotation +
          hullSixThreeThreeUpperOffset (hullSixReverseFinThree i))))
        (cfg (cycle (F.rotation +
          hullSixThreeThreeLowerOffset (hullSixReverseFinThree j)))))).2
      hsource
  simpa [TableHolds, reflectedRotateComplement,
    hullSixReflectedConfiguration, hullSixReflectedCycle] using hcomplement

end HullSixThreeThreeGeometricFrame

/-! ## Provider-level exact custody -/

/-- Pull an exact packet provider back through honest physical reflection. -/
theorem hullSixThreeThreeExactPacketProvider_rotateComplement
    {Packet : HullSixThreeThreeCuts -> Prop}
    (hPacket : HullSixThreeThreeExactPacketProvider Packet) :
    HullSixThreeThreeExactPacketProvider
      (fun T => Packet
        (HullSixThreeThreeCuts.act
          HullSixThreeThreeCuts.Symmetry.rotateComplement T)) := by
  intro cfg cycle p q R F
  intro T hLegal hTarget hTable
  exact hPacket F.reflectedRotateComplement
    (HullSixThreeThreeCuts.act
      HullSixThreeThreeCuts.Symmetry.rotateComplement T)
    (HullSixThreeThreeCuts.legal_act
      HullSixThreeThreeCuts.Symmetry.rotateComplement T hLegal)
    hTarget
    (F.tableHolds_reflectedRotateComplement hLegal hTable)

end Heilbronn8
