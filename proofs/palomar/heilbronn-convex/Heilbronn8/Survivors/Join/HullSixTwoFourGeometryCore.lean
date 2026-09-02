import Heilbronn8.HullSixSplitResidualView

/-!
# Shared geometric core for oriented `2 + 4` residual views

This file fixes the cyclic offsets

```text
U0, U1, L0, L1, L2, L3
```

and exposes the shifted boundary and consecutive-hull-triple floors used by
both the wide-product adapter and the q-blind top adapter.  It contains no
chamber dispatch and no scalar inequality.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- Offset of an upper vertex in a rotated `2 + 4` frame. -/
def hullSixTwoFourUpperOffset (i : Fin 2) : Fin 6 :=
  ⟨i.val, by omega⟩

/-- Offset of a lower vertex in a rotated `2 + 4` frame. -/
def hullSixTwoFourLowerOffset (j : Fin 4) : Fin 6 :=
  ⟨j.val + 2, by omega⟩

/-- A boundary triangle based at either exterior point, after a cyclic
translation of the six-cycle. -/
theorem hullSixTwoFour_shiftedBoundary_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : ∀ i,
      0 < sig (cfg base) (cfg (cycle i)) (cfg (cycle (i + 1))))
    (rotation offset : Fin 6) :
    minTri cfg ≤ sig (cfg base) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig cfg cycle R.cycle_injective
    base hOutside (rotation + offset) (hpos (rotation + offset))
  have hnext : (rotation + offset) + 1 = rotation + (offset + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

/-- Every cyclically consecutive hull triple has positive orientation. -/
theorem hullSixTwoFour_shiftedConsecutiveTriple_pos
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (start : Fin 6) :
    0 < sig (cfg (cycle start)) (cfg (cycle (start + 1)))
      (cfg (cycle (start + 2))) := by
  have h012 := R.cycle_strict.pos 0 1 2 (by decide) (by decide)
  have h123 := R.cycle_strict.pos 1 2 3 (by decide) (by decide)
  have h234 := R.cycle_strict.pos 2 3 4 (by decide) (by decide)
  have h345 := R.cycle_strict.pos 3 4 5 (by decide) (by decide)
  have h045 := R.cycle_strict.pos 0 4 5 (by decide) (by decide)
  have h015 := R.cycle_strict.pos 0 1 5 (by decide) (by decide)
  have h450 :
      0 < sig (cfg (cycle 4)) (cfg (cycle 5)) (cfg (cycle 0)) := by
    rw [← sig_rotate]
    exact h045
  have h501 :
      0 < sig (cfg (cycle 5)) (cfg (cycle 0)) (cfg (cycle 1)) := by
    rw [← sig_rotate, ← sig_rotate]
    exact h015
  fin_cases start <;>
    first
    | simpa using h012
    | simpa using h123
    | simpa using h234
    | simpa using h345
    | simpa using h450
    | simpa using h501

/-- Every cyclically consecutive hull triple has the `minTri` floor. -/
theorem hullSixTwoFour_shiftedConsecutiveTriple_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (start : Fin 6) :
    minTri cfg ≤ sig (cfg (cycle start)) (cfg (cycle (start + 1)))
      (cfg (cycle (start + 2))) := by
  have h01 : start ≠ start + 1 := by
    fin_cases start <;> decide
  have h02 : start ≠ start + 2 := by
    fin_cases start <;> decide
  have h12 : start + 1 ≠ start + 2 := by
    fin_cases start <;> decide
  exact minTri_le_pos_sig_of_pairwise_ne cfg
    (R.cycle_injective.ne h01) (R.cycle_injective.ne h02)
    (R.cycle_injective.ne h12)
    (hullSixTwoFour_shiftedConsecutiveTriple_pos R start)

/-- The nonconsecutive lower hull triple `L0,L2,L3` stays positive after
cyclic translation.  This is the second hull face in the `L0-L3` wide
retriangulation. -/
theorem hullSixTwoFour_shiftedLower023_pos
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (rotation : Fin 6) :
    0 < sig
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 0)))
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 2)))
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 3))) := by
  have h245 := R.cycle_strict.pos 2 4 5 (by decide) (by decide)
  have h035 := R.cycle_strict.pos 0 3 5 (by decide) (by decide)
  have h014 := R.cycle_strict.pos 0 1 4 (by decide) (by decide)
  have h125 := R.cycle_strict.pos 1 2 5 (by decide) (by decide)
  have h023 := R.cycle_strict.pos 0 2 3 (by decide) (by decide)
  have h134 := R.cycle_strict.pos 1 3 4 (by decide) (by decide)
  fin_cases rotation <;>
    first
    | simpa [hullSixTwoFourLowerOffset] using h245
    | (rw [sig_rotate, sig_rotate] <;>
       simpa [hullSixTwoFourLowerOffset] using h035)
    | (rw [sig_rotate] <;>
       simpa [hullSixTwoFourLowerOffset] using h014)
    | (rw [sig_rotate] <;>
       simpa [hullSixTwoFourLowerOffset] using h125)
    | simpa [hullSixTwoFourLowerOffset] using h023
    | simpa [hullSixTwoFourLowerOffset] using h134

/-- `minTri` floor for the shifted lower hull triple `L0,L2,L3`. -/
theorem hullSixTwoFour_shiftedLower023_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (rotation : Fin 6) :
    minTri cfg ≤ sig
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 0)))
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 2)))
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 3))) := by
  have h02 :
      rotation + hullSixTwoFourLowerOffset 0 ≠
        rotation + hullSixTwoFourLowerOffset 2 := by
    fin_cases rotation <;> decide
  have h03 :
      rotation + hullSixTwoFourLowerOffset 0 ≠
        rotation + hullSixTwoFourLowerOffset 3 := by
    fin_cases rotation <;> decide
  have h23 :
      rotation + hullSixTwoFourLowerOffset 2 ≠
        rotation + hullSixTwoFourLowerOffset 3 := by
    fin_cases rotation <;> decide
  exact minTri_le_pos_sig_of_pairwise_ne cfg
    (R.cycle_injective.ne h02) (R.cycle_injective.ne h03)
    (R.cycle_injective.ne h23)
    (hullSixTwoFour_shiftedLower023_pos R rotation)

namespace HullSixCompactCrossChordResidual

/-- The signed boundary-fan sum is independent of its base point.  This
small telescoping seam lets a single oriented view expose both fan sums. -/
lemma twoFour_fan_sum_base_change
    (P Q : ℝ × ℝ) (c : Fin 6 → ℝ × ℝ) :
    sumFinSix (fun i ↦ sig Q (c i) (c (i + 1))) =
      sumFinSix (fun i ↦ sig P (c i) (c (i + 1))) := by
  change
    sig Q (c 0) (c 1) + sig Q (c 1) (c 2) +
        sig Q (c 2) (c 3) + sig Q (c 3) (c 4) +
          sig Q (c 4) (c 5) + sig Q (c 5) (c 0) =
      sig P (c 0) (c 1) + sig P (c 1) (c 2) +
        sig P (c 2) (c 3) + sig P (c 3) (c 4) +
          sig P (c 4) (c 5) + sig P (c 5) (c 0)
  rw [sig_crossChord_base_change P Q (c 0) (c 1),
    sig_crossChord_base_change P Q (c 1) (c 2),
    sig_crossChord_base_change P Q (c 2) (c 3),
    sig_crossChord_base_change P Q (c 3) (c 4),
    sig_crossChord_base_change P Q (c 4) (c 5),
    sig_crossChord_base_change P Q (c 5) (c 0)]
  ring

/-- The rotated `P`-fan is the six-term hull-area decomposition used by all
`2 + 4` scalar adapters. -/
theorem twoFour_P_fan_sum
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6) :
    doubledHullArea cfg =
      sig (cfg P) (cfg (cycle rotation)) (cfg (cycle (rotation + 1))) +
      sig (cfg P) (cfg (cycle (rotation + 1)))
        (cfg (cycle (rotation + 2))) +
      sig (cfg P) (cfg (cycle (rotation + 2)))
        (cfg (cycle (rotation + 3))) +
      sig (cfg P) (cfg (cycle (rotation + 3)))
        (cfg (cycle (rotation + 4))) +
      sig (cfg P) (cfg (cycle (rotation + 4)))
        (cfg (cycle (rotation + 5))) +
      sig (cfg P) (cfg (cycle (rotation + 5)))
        (cfg (cycle rotation)) := by
  let fan : Fin 6 → ℝ := fun i ↦
    sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i ↦
        sig (cfg P) (cfg (cycle (rotation + i)))
          (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun : (fun i ↦
          sig (cfg P) (cfg (cycle (rotation + i)))
            (cfg (cycle (rotation + (i + 1))))) =
        (fun i ↦ fan (rotation + i)) := by
      funext i
      simp [fan, add_assoc]
    rw [hfun, sumFinSix_add_left]
    exact V.P_fan_sum
  rw [← hshifted]
  simp [sumFinSix] <;> ring

/-- The rotated `Q`-fan has the same six-term hull-area decomposition.  The
oriented view stores only the `P` sum; base-point independence supplies this
companion without enlarging that shared API. -/
theorem twoFour_Q_fan_sum
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6) :
    doubledHullArea cfg =
      sig (cfg Q) (cfg (cycle rotation)) (cfg (cycle (rotation + 1))) +
      sig (cfg Q) (cfg (cycle (rotation + 1)))
        (cfg (cycle (rotation + 2))) +
      sig (cfg Q) (cfg (cycle (rotation + 2)))
        (cfg (cycle (rotation + 3))) +
      sig (cfg Q) (cfg (cycle (rotation + 3)))
        (cfg (cycle (rotation + 4))) +
      sig (cfg Q) (cfg (cycle (rotation + 4)))
        (cfg (cycle (rotation + 5))) +
      sig (cfg Q) (cfg (cycle (rotation + 5)))
        (cfg (cycle rotation)) := by
  have hbase :
      sumFinSix (fun i ↦
        sig (cfg Q) (cfg (cycle i)) (cfg (cycle (i + 1)))) =
        doubledHullArea cfg := by
    rw [twoFour_fan_sum_base_change (cfg P) (cfg Q)
      (fun i ↦ cfg (cycle i))]
    exact V.P_fan_sum
  let fan : Fin 6 → ℝ := fun i ↦
    sig (cfg Q) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i ↦
        sig (cfg Q) (cfg (cycle (rotation + i)))
          (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun : (fun i ↦
          sig (cfg Q) (cfg (cycle (rotation + i)))
            (cfg (cycle (rotation + (i + 1))))) =
        (fun i ↦ fan (rotation + i)) := by
      funext i
      simp [fan, add_assoc]
    rw [hfun, sumFinSix_add_left]
    exact hbase
  rw [← hshifted]
  simp [sumFinSix] <;> ring

/-- `P`-fan floor for a boundary edge at a rotated `2 + 4` offset. -/
theorem twoFour_P_boundary_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation offset : Fin 6) :
    minTri cfg ≤ sig (cfg P) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) :=
  hullSixTwoFour_shiftedBoundary_floor R V P V.P_outside
    V.P_boundary_pos rotation offset

/-- `Q`-fan floor for a boundary edge at a rotated `2 + 4` offset. -/
theorem twoFour_Q_boundary_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation offset : Fin 6) :
    minTri cfg ≤ sig (cfg Q) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) :=
  hullSixTwoFour_shiftedBoundary_floor R V Q V.Q_outside
    V.Q_boundary_pos rotation offset

/-- Hull-ear floor at a rotated cyclic offset. -/
theorem twoFour_hullEar_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (rotation offset : Fin 6) :
    minTri cfg ≤
      sig (cfg (cycle (rotation + offset)))
        (cfg (cycle (rotation + (offset + 1))))
        (cfg (cycle (rotation + (offset + 2)))) := by
  have h := hullSixTwoFour_shiftedConsecutiveTriple_floor R
    (rotation + offset)
  have h1 : (rotation + offset) + 1 = rotation + (offset + 1) := by
    simp [add_assoc]
  have h2 : (rotation + offset) + 2 = rotation + (offset + 2) := by
    simp [add_assoc]
  simpa only [h1, h2] using h

end HullSixCompactCrossChordResidual

end Heilbronn8
