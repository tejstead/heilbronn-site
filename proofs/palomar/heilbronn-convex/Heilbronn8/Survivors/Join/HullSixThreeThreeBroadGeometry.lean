import Heilbronn8.HullSixSplitResidualView
import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadNonnegative

/-!
# Geometric adapter for the broad `3 x 3` chamber

Fix an oriented `3 + 3` view with cyclic order

```text
U0, U1, U2, L0, L1, L2.
```

This module turns the eight signed cross-chord floors of the broad table
`001 / 233` into the normalized positive ear residuals.  The final
contradiction uses the line-level spread retained by the compact residual;
no hull-area estimate or coordinate normalization is introduced.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- Offset of an upper vertex in a rotated `3 + 3` frame. -/
def hullSixThreeThreeUpperOffset (i : Fin 3) : Fin 6 :=
  ⟨i.val, by omega⟩

/-- Offset of a lower vertex in a rotated `3 + 3` frame. -/
def hullSixThreeThreeLowerOffset (j : Fin 3) : Fin 6 :=
  ⟨j.val + 3, by omega⟩

private lemma threeThree_shiftedBoundary_floor
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

private lemma threeThree_shiftedConsecutiveTriple_pos
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
  have h450 : 0 < sig (cfg (cycle 4)) (cfg (cycle 5)) (cfg (cycle 0)) := by
    rw [← sig_rotate]
    exact h045
  have h501 : 0 < sig (cfg (cycle 5)) (cfg (cycle 0)) (cfg (cycle 1)) := by
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

private lemma threeThree_shiftedConsecutiveTriple_floor
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
    (threeThree_shiftedConsecutiveTriple_pos R start)

namespace HullSixCompactCrossChordResidual

/-- A broad table at an arbitrary rotated, oriented `3 + 3` frame is
incompatible with a beating compact residual.

Only the eight cross-chord floors actually consumed by the scalar proof are
listed.  A Ferrers-table wrapper can obtain them definitionally from the
`001 / 233` chamber labels. -/
theorem threeThreeBroadAt_false_of_crossFloors
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hpair : HullSixIsOrientedPair p q P Q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hX10 : minTri cfg ≤ -sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX11 : minTri cfg ≤ -sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hX20 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX21 : minTri cfg ≤ -sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY01 : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY02 : minTri cfg ≤ -sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))))
    (hY11 : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY12 : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let m := minTri cfg
  let U0 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0))
  let U1 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1))
  let U2 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2))
  let L0 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))
  let L1 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))
  let L2 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))

  let x := (-sig (cfg P) U1 L1) / m - 1
  let y := sig (cfg Q) U1 L1 / m - 1
  let U := sig (cfg Q) U0 U1 / m
  let vFan := sig (cfg P) U1 U2 / m
  let L := sig (cfg Q) L1 L2 / m
  let ell := sig (cfg P) L0 L1 / m
  let B := sig (cfg P) (cfg Q) U1 / m - 1
  let E := (-sig (cfg P) (cfg Q) L1) / m - 1
  let TU := sig U0 U1 U2 / m
  let TL := sig L0 L1 L2 / m
  let p0 := sig (cfg P) U0 U1 / m
  let q0 := sig (cfg Q) U1 U2 / m
  let P0 := sig (cfg P) L1 L2 / m
  let Q0 := sig (cfg Q) L0 L1 / m
  let y0 := sig (cfg Q) U0 L1 / m
  let h0 := (-sig (cfg P) U2 L1) / m
  let x0 := (-sig (cfg P) U1 L0) / m
  let z0 := sig (cfg Q) U1 L2 / m
  let g := sig (cfg P) U2 L0 / m
  let c := (-sig (cfg Q) U0 L2) / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {a : ℝ} (ha : m ≤ a) : 1 ≤ a / m := by
    exact (le_div_iff₀ hm).2 (by simpa using ha)

  have hx0 : 0 ≤ x := by
    have h := hnorm (by simpa [m, U1, L1] using hX11)
    dsimp [x]
    linarith
  have hy0 : 0 ≤ y := by
    have h := hnorm (by simpa [m, U1, L1] using hY11)
    dsimp [y]
    linarith
  have hx0Floor : 1 ≤ x0 := by
    apply hnorm
    simpa [m, U1, L0] using hX10
  have hh0Floor : 1 ≤ h0 := by
    apply hnorm
    simpa [m, U2, L1] using hX21
  have hgFloor : 1 ≤ g := by
    apply hnorm
    simpa [m, U2, L0] using hX20
  have hy0Floor : 1 ≤ y0 := by
    apply hnorm
    simpa [m, U0, L1] using hY01
  have hcFloor : 1 ≤ c := by
    apply hnorm
    simpa [m, U0, L2] using hY02
  have hz0Floor : 1 ≤ z0 := by
    apply hnorm
    simpa [m, U1, L2] using hY12

  have hbRaw : m ≤ sig (cfg P) (cfg Q) U1 := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    have hpos := hupper 1
    rw [abs_of_pos hpos] at hfloor
    simpa [m, U1] using hfloor
  have heRaw : m ≤ -sig (cfg P) (cfg Q) L1 := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    have hneg := hlower 1
    rw [abs_of_neg hneg] at hfloor
    simpa [m, L1] using hfloor
  have hB0 : 0 ≤ B + 1 := by
    have h := hnorm hbRaw
    dsimp [B]
    linarith
  have hE0 : 0 ≤ E + 1 := by
    have h := hnorm heRaw
    dsimp [E]
    linarith

  have hp0Raw : m ≤ sig (cfg P) U0 U1 := by
    simpa [m, U0, U1, hullSixThreeThreeUpperOffset] using
      threeThree_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 0
  have hvRaw : m ≤ sig (cfg P) U1 U2 := by
    simpa [m, U1, U2, hullSixThreeThreeUpperOffset] using
      threeThree_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 1
  have hellRaw : m ≤ sig (cfg P) L0 L1 := by
    simpa [m, L0, L1, hullSixThreeThreeLowerOffset] using
      threeThree_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 3
  have hP0Raw : m ≤ sig (cfg P) L1 L2 := by
    simpa [m, L1, L2, hullSixThreeThreeLowerOffset] using
      threeThree_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 4
  have hURaw : m ≤ sig (cfg Q) U0 U1 := by
    simpa [m, U0, U1, hullSixThreeThreeUpperOffset] using
      threeThree_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 0
  have hq0Raw : m ≤ sig (cfg Q) U1 U2 := by
    simpa [m, U1, U2, hullSixThreeThreeUpperOffset] using
      threeThree_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 1
  have hQ0Raw : m ≤ sig (cfg Q) L0 L1 := by
    simpa [m, L0, L1, hullSixThreeThreeLowerOffset] using
      threeThree_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 3
  have hLRaw : m ≤ sig (cfg Q) L1 L2 := by
    simpa [m, L1, L2, hullSixThreeThreeLowerOffset] using
      threeThree_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 4

  have hU : 1 ≤ U := hnorm (by simpa [U] using hURaw)
  have hv : 1 ≤ vFan := hnorm (by simpa [vFan] using hvRaw)
  have hL : 1 ≤ L := hnorm (by simpa [L] using hLRaw)
  have hell : 1 ≤ ell := hnorm (by simpa [ell] using hellRaw)
  have hp0 : 0 ≤ p0 := le_trans zero_le_one
    (hnorm (by simpa [p0] using hp0Raw))
  have hq0 : 0 ≤ q0 := le_trans zero_le_one
    (hnorm (by simpa [q0] using hq0Raw))
  have hP0 : 0 ≤ P0 := le_trans zero_le_one
    (hnorm (by simpa [P0] using hP0Raw))
  have hQ0 : 0 ≤ Q0 := le_trans zero_le_one
    (hnorm (by simpa [Q0] using hQ0Raw))

  have hTURaw : m ≤ sig U0 U1 U2 := by
    simpa [m, U0, U1, U2, hullSixThreeThreeUpperOffset] using
      threeThree_shiftedConsecutiveTriple_floor R rotation
  have hTLRaw : m ≤ sig L0 L1 L2 := by
    simpa [m, L0, L1, L2, hullSixThreeThreeLowerOffset, add_assoc] using
      threeThree_shiftedConsecutiveTriple_floor R (rotation + 3)
  have hTU : 1 ≤ TU := hnorm (by simpa [TU] using hTURaw)
  have hTL : 1 ≤ TL := hnorm (by simpa [TL] using hTLRaw)

  have hBE : B + E = x + y := by
    simpa [x, y, B, E] using
      sig_threeThree_broad_central_base_change
        (cfg P) (cfg Q) U1 L1 hmNe
  have hQProduct : U * L = (y + 1) * c + y0 * z0 := by
    simpa [y, U, L, c, y0, z0] using
      sig_threeThree_broad_q_product_identity
        (cfg P) (cfg Q) U0 U1 L1 L2 hmNe
  have hPProduct : vFan * ell = (x + 1) * g + x0 * h0 := by
    simpa [x, vFan, ell, g, x0, h0] using
      sig_threeThree_broad_p_product_identity
        (cfg P) U1 U2 L0 L1 hmNe
  have hUL : y + 2 ≤ U * L := by
    have hfirst : y + 1 ≤ (y + 1) * c := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ y + 1)
        (sub_nonneg.mpr hcFloor)]
    have hsecond : 1 ≤ y0 * z0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy0Floor)
        (sub_nonneg.mpr hz0Floor)]
    rw [hQProduct]
    linarith
  have hvell : x + 2 ≤ vFan * ell := by
    have hfirst : x + 1 ≤ (x + 1) * g := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1)
        (sub_nonneg.mpr hgFloor)]
    have hsecond : 1 ≤ x0 * h0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx0Floor)
        (sub_nonneg.mpr hh0Floor)]
    rw [hPProduct]
    linarith

  have hDbEq := sig_threeThree_broad_upper_earResidual_identity
    (cfg P) (cfg Q) U0 U1 U2 L1 hmNe
  have hDeEq := sig_threeThree_broad_lower_earResidual_identity
    (cfg P) (cfg Q) U1 L0 L1 L2 hmNe
  have hxy : 9 ≤ x * y :=
    hullSixThreeThree_broad_product_ge_nine_of_earResiduals_nonnegative
      hx0 hy0 hU hv hL hell hBE hUL hvell hTU hTL hp0 hq0 hP0 hQ0
      hy0Floor hh0Floor hx0Floor hz0Floor hB0 hE0
      (by simpa [x, y, U, vFan, B, E, TU, p0, q0, y0, h0] using hDbEq)
      (by simpa [x, y, L, ell, B, E, TL, P0, Q0, x0, z0] using hDeEq)
  have hsum : 8 ≤ (x + 1) + (y + 1) :=
    hullSixThreeThree_broad_sum_ge_eight_nonnegative hx0 hy0 hxy

  have hspreadRaw :
      sig (cfg P) (cfg Q) U1 - sig (cfg P) (cfg Q) L1 < 13 * m / 2 := by
    rcases hpair with hforward | hswapped
    · rcases hforward with ⟨rfl, rfl⟩
      simpa [m, U1, L1] using R.lineLevel_spread_lt
        (rotation + hullSixThreeThreeLowerOffset 1)
        (rotation + hullSixThreeThreeUpperOffset 1)
    · rcases hswapped with ⟨hP, hQ⟩
      subst P
      subst Q
      have h := R.lineLevel_spread_lt
        (rotation + hullSixThreeThreeUpperOffset 1)
        (rotation + hullSixThreeThreeLowerOffset 1)
      rw [sig_swap_first (cfg p) (cfg q) U1,
        sig_swap_first (cfg p) (cfg q) L1]
      dsimp [m, U1, L1]
      nlinarith only [h]
  have hcentralLt :
      sig (cfg P) (cfg Q) U1 / m +
          (-sig (cfg P) (cfg Q) L1) / m < 13 / 2 := by
    calc
      sig (cfg P) (cfg Q) U1 / m +
          (-sig (cfg P) (cfg Q) L1) / m =
          (sig (cfg P) (cfg Q) U1 - sig (cfg P) (cfg Q) L1) / m := by
            ring
      _ < 13 / 2 := by
        apply (div_lt_iff₀ hm).2
        nlinarith only [hspreadRaw]
  have hsumEq :
      (x + 1) + (y + 1) =
        sig (cfg P) (cfg Q) U1 / m +
          (-sig (cfg P) (cfg Q) L1) / m := by
    dsimp [x, y]
    have hbase := sig_threeThree_broad_central_base_change
      (cfg P) (cfg Q) U1 L1 hmNe
    dsimp at hbase
    linarith
  rw [hsumEq] at hsum
  linarith

end HullSixCompactCrossChordResidual

end Heilbronn8
