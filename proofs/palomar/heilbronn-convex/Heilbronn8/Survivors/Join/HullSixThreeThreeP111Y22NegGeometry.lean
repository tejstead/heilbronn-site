import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Y22NegScalar
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# Geometry for the negative-`Y22` `p = 111` branch

The adapter records exactly the two endpoint `Q`-fan floors, four hull
triangle floors, two positive first-column `X` floors, and three determinant
transports consumed by the scalar theorem.  No other `Y` sign is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma p111Neg_shiftedBoundary_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : ∀ i, 0 < sig (cfg base) (cfg (cycle i)) (cfg (cycle (i + 1))))
    (rotation offset : Fin 6) :
    minTri cfg ≤ sig (cfg base) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig cfg cycle R.cycle_injective
    base hOutside (rotation + offset) (hpos (rotation + offset))
  have hnext : (rotation + offset) + 1 = rotation + (offset + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

private lemma p111Neg_shiftedTriple_pos
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
  have h450 : 0 < sig (cfg (cycle 4)) (cfg (cycle 5))
      (cfg (cycle 0)) := by
    rw [← sig_rotate]
    exact h045
  have h501 : 0 < sig (cfg (cycle 5)) (cfg (cycle 0))
      (cfg (cycle 1)) := by
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

private lemma p111Neg_shiftedTriple_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (start : Fin 6) :
    minTri cfg ≤ sig (cfg (cycle start)) (cfg (cycle (start + 1)))
      (cfg (cycle (start + 2))) := by
  have h01 : start ≠ start + 1 := by fin_cases start <;> decide
  have h02 : start ≠ start + 2 := by fin_cases start <;> decide
  have h12 : start + 1 ≠ start + 2 := by fin_cases start <;> decide
  exact minTri_le_pos_sig_of_pairwise_ne cfg
    (R.cycle_injective.ne h01) (R.cycle_injective.ne h02)
    (R.cycle_injective.ne h12)
    (p111Neg_shiftedTriple_pos R start)

namespace HullSixCompactCrossChordResidual

/-- The negative `Y22` absolute-floor branch closes for every height order. -/
theorem threeThreeP111Y22NegAt_false
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
    (hX00 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX10 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hY22 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) ≤
        -minTri cfg) :
    False := by
  let s := minTri cfg
  let U : Fin 3 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let u0 := sig (cfg P) (cfg Q) (U 0) / s
  let u1 := sig (cfg P) (cfg Q) (U 1) / s
  let u2 := sig (cfg P) (cfg Q) (U 2) / s
  let v0 := (-sig (cfg P) (cfg Q) (L 0)) / s
  let v2 := (-sig (cfg P) (cfg Q) (L 2)) / s
  let A0 := sig (cfg P) (U 0) (U 1) / s
  let A1 := sig (cfg P) (U 1) (U 2) / s
  let A2 := sig (cfg P) (U 2) (L 0) / s
  let A3 := sig (cfg P) (L 0) (L 1) / s
  let A4 := sig (cfg P) (L 1) (L 2) / s
  let A5 := sig (cfg P) (L 2) (U 0) / s
  let X00 := sig (cfg P) (U 0) (L 0) / s
  let X10 := sig (cfg P) (U 1) (L 0) / s
  let X12 := sig (cfg P) (U 1) (L 2) / s
  let X22 := sig (cfg P) (U 2) (L 2) / s
  let Y22 := sig (cfg Q) (U 2) (L 2) / s
  let L02 := sig (cfg P) (L 0) (L 2) / s
  let B0 := sig (cfg Q) (U 0) (U 1) / s
  let B5 := sig (cfg Q) (L 2) (U 0) / s
  let T015 := sig (L 2) (U 0) (U 1) / s
  let T012 := sig (U 0) (U 1) (U 2) / s
  let T123 := sig (U 1) (U 2) (L 0) / s
  let T345 := sig (L 0) (L 1) (L 2) / s
  let H := doubledHullArea cfg / s

  have hs : 0 < s := by simpa [s] using R.minTri_pos
  have hsNe : s ≠ 0 := ne_of_gt hs
  have hnorm {w : ℝ} (hw : s ≤ w) : 1 ≤ w / s :=
    (le_div_iff₀ hs).2 (by simpa using hw)

  have hu0 : 1 ≤ u0 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [s, u0, U] using h)
  have hu1 : 1 ≤ u1 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [s, u1, U] using h)
  have hu2 : 1 ≤ u2 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at h
    exact hnorm (by simpa [s, u2, U] using h)
  have hv0 : 1 ≤ v0 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    exact hnorm (by simpa [s, v0, L] using h)
  have hv2 : 1 ≤ v2 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [s, v2, L] using h)

  have hA0Raw : s ≤ sig (cfg P) (U 0) (U 1) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p111Neg_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 0
  have hA0 : 1 ≤ A0 := hnorm (by simpa [A0] using hA0Raw)
  have hA1Raw : s ≤ sig (cfg P) (U 1) (U 2) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p111Neg_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 1
  have hA1 : 1 ≤ A1 := hnorm (by simpa [A1] using hA1Raw)
  have hA2Raw : s ≤ sig (cfg P) (U 2) (L 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using
      p111Neg_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 2
  have hA2 : 1 ≤ A2 := hnorm (by simpa [A2] using hA2Raw)
  have hA3Raw : s ≤ sig (cfg P) (L 0) (L 1) := by
    simpa [s, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p111Neg_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 3
  have hA3 : 1 ≤ A3 := hnorm (by simpa [A3] using hA3Raw)
  have hA4Raw : s ≤ sig (cfg P) (L 1) (L 2) := by
    simpa [s, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p111Neg_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 4
  have hA4 : 1 ≤ A4 := hnorm (by simpa [A4] using hA4Raw)
  have hA5Raw : s ≤ sig (cfg P) (L 2) (U 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p111Neg_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 5
  have hA5 : 1 ≤ A5 := hnorm (by simpa [A5] using hA5Raw)
  have hX00n : 1 ≤ X00 := hnorm (by simpa [s, X00, U, L] using hX00)
  have hX10n : 1 ≤ X10 := hnorm (by simpa [s, X10, U, L] using hX10)

  have hB0Raw : s ≤ sig (cfg Q) (U 0) (U 1) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p111Neg_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 0
  have hB0n : 1 ≤ B0 := hnorm (by simpa [B0] using hB0Raw)
  have hB5Raw : s ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p111Neg_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hB5n : 1 ≤ B5 := hnorm (by simpa [B5] using hB5Raw)
  have hB0Identity : B0 = A0 + u0 - u1 := by
    dsimp [B0, A0, u0, u1, U]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hB5Identity : B5 = A5 - u0 - v2 := by
    dsimp [B5, A5, u0, v2, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hB0 : 1 ≤ A0 + u0 - u1 := by simpa [hB0Identity] using hB0n
  have hB5 : 1 ≤ A5 - u0 - v2 := by simpa [hB5Identity] using hB5n

  have hY22n : Y22 ≤ -1 := by
    apply (div_le_iff₀ hs).2
    simpa [s, Y22, U, L, mul_comm] using hY22
  have hY22Identity : Y22 = X22 + u2 + v2 := by
    dsimp [Y22, X22, u2, v2, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hY22Scalar : X22 + u2 + v2 ≤ -1 := by
    rw [← hY22Identity]
    exact hY22n

  have hColumn0 : v0 * A0 = u0 * X10 - u1 * X00 := by
    dsimp [v0, A0, u0, X10, u1, X00, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hColumn2 : u2 * (-X12) - u1 * (-X22) = v2 * A1 := by
    dsimp [u2, X12, u1, X22, v2, A1, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hL02Identity : u2 * L02 = v2 * A2 + v0 * (-X22) := by
    dsimp [u2, L02, v2, A2, v0, X22, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring

  have hT015Raw : s ≤ sig (L 2) (U 0) (U 1) := by
    have h := p111Neg_shiftedTriple_floor R (rotation + 5)
    have hnext0 : (rotation + (5 : Fin 6)) + 1 = rotation := by
      fin_cases rotation <;> decide
    have hnext1 : (rotation + (5 : Fin 6)) + 2 = rotation + 1 := by
      fin_cases rotation <;> decide
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, hnext0, hnext1] using h
  have hT012Raw : s ≤ sig (U 0) (U 1) (U 2) := by
    simpa [s, U, hullSixThreeThreeUpperOffset, add_assoc] using
      p111Neg_shiftedTriple_floor R rotation
  have hT123Raw : s ≤ sig (U 1) (U 2) (L 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p111Neg_shiftedTriple_floor R (rotation + 1)
  have hT345Raw : s ≤ sig (L 0) (L 1) (L 2) := by
    simpa [s, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p111Neg_shiftedTriple_floor R (rotation + 3)
  have hT015 : 1 ≤ T015 := hnorm (by simpa [T015] using hT015Raw)
  have hT012 : 1 ≤ T012 := hnorm (by simpa [T012] using hT012Raw)
  have hT123 : 1 ≤ T123 := hnorm (by simpa [T123] using hT123Raw)
  have hT345 : 1 ≤ T345 := hnorm (by simpa [T345] using hT345Raw)
  have hT015Identity : T015 = A0 + A5 + X12 := by
    dsimp [T015, A0, A5, X12, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hT012Identity :
      u1 * T012 = A0 * (u1 - u2) + A1 * (u1 - u0) := by
    dsimp [u1, T012, A0, u2, A1, u0, U]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hT123Identity : T123 = A1 + A2 - X10 := by
    dsimp [T123, A1, A2, X10, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hT345Identity : T345 = A3 + A4 - L02 := by
    dsimp [T345, A3, A4, L02, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hHull015 : 1 ≤ A0 + A5 + X12 := by
    simpa [hT015Identity] using hT015
  have hHull012 : u1 ≤ A0 * (u1 - u2) + A1 * (u1 - u0) := by
    rw [← hT012Identity]
    have hmul := mul_le_mul_of_nonneg_left hT012 (le_trans zero_le_one hu1)
    nlinarith
  have hHull123 : 1 ≤ A1 + A2 - X10 := by
    simpa [hT123Identity] using hT123
  have hHull345 : 1 ≤ A3 + A4 - L02 := by
    simpa [hT345Identity] using hT345

  have hscalar : 25 / 2 < A0 + A1 + A2 + A3 + A4 + A5 :=
    hullSixThreeThreeP111Y22Neg_scalar
      hu0 hu1 hu2 hv0 hv2 hA0 hA1 hA2 hA3 hA4 hA5 hB0 hB5
      hX00n hX10n hY22Scalar hColumn0 hColumn2 hL02Identity
      hHull015 hHull012 hHull123 hHull345

  let fan : Fin 6 → ℝ := fun i ↦
    sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i ↦ sig (cfg P) (cfg (cycle (rotation + i)))
        (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun : (fun i ↦ sig (cfg P) (cfg (cycle (rotation + i)))
          (cfg (cycle (rotation + (i + 1))))) =
        (fun i ↦ fan (rotation + i)) := by
      funext i
      simp [fan, add_assoc]
    rw [hfun, sumFinSix_add_left]
    exact V.P_fan_sum
  have hSumRaw : doubledHullArea cfg =
      sig (cfg P) (U 0) (U 1) + sig (cfg P) (U 1) (U 2) +
      sig (cfg P) (U 2) (L 0) + sig (cfg P) (L 0) (L 1) +
      sig (cfg P) (L 1) (L 2) + sig (cfg P) (L 2) (U 0) := by
    have hraw : doubledHullArea cfg =
        sig (cfg P) (cfg (cycle rotation)) (cfg (cycle (rotation + 1))) +
        sig (cfg P) (cfg (cycle (rotation + 1)))
          (cfg (cycle (rotation + 2))) +
        sig (cfg P) (cfg (cycle (rotation + 2)))
          (cfg (cycle (rotation + 3))) +
        sig (cfg P) (cfg (cycle (rotation + 3)))
          (cfg (cycle (rotation + 4))) +
        sig (cfg P) (cfg (cycle (rotation + 4)))
          (cfg (cycle (rotation + 5))) +
        sig (cfg P) (cfg (cycle (rotation + 5))) (cfg (cycle rotation)) := by
      rw [← hshifted]
      simp [sumFinSix] <;> ring
    simpa [U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using hraw
  have hFan : H = A0 + A1 + A2 + A3 + A4 + A5 := by
    dsimp [H, A0, A1, A2, A3, A4, A5]
    rw [hSumRaw]
    ring
  have hnormArea : 25 / 2 < H := by simpa [hFan] using hscalar
  have hmul : ((25 : ℝ) / 2) * s < doubledHullArea cfg :=
    (lt_div_iff₀ hs).1 hnormArea
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < s := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

end Heilbronn8
