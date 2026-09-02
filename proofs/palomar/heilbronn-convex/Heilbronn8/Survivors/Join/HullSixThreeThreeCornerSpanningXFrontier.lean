import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# Five corner-spanning maximal-q `3 x 3` frontiers

This module closes the five partial `X` frontiers whose first cuts satisfy
`1 <= p0` and `p2 = 3`, namely

```text
113, 123, 133, 223, 233.
```

Only the retained `X` information is used.  If `X02` denotes the wrap
corner, the positive `Q`-fan boundary edge makes `-X02` at least the sum of
the two adjacent line heights plus `m`.  A positive `X` entry in the top row
and another in the last column then force one upper and one lower chord by
two determinant transport identities.  Triangulating the skipped upper and
lower vertices leaves exactly three further copies of `m`.  The remaining
two-variable inequality is a rational AM-GM estimate.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The normalized two-variable inequality used by all five packets. -/
theorem hullSixThreeThree_cornerSpanning_scalar
    {u v A E D H : Real}
    (hu : 1 <= u) (hv : 1 <= v)
    (hA : u + 3 <= v * A) (hE : v + 3 <= u * E)
    (hD : u + v + 1 <= D) (hH : A + E + D + 3 <= H) :
    25 / 2 < H := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hAlower : (u + 3) / v <= A := by
    apply (div_le_iff₀ hv0).2
    simpa [mul_comm] using hA
  have hElower : (v + 3) / u <= E := by
    apply (div_le_iff₀ hu0).2
    simpa [mul_comm] using hE
  have huRat : 13 / 4 < u + 3 / u := by
    have hsq := sq_nonneg (u - 13 / 8)
    have hmul : (13 / 4) * u < u * u + 3 := by
      nlinarith
    calc
      13 / 4 < (u * u + 3) / u := (lt_div_iff₀ hu0).2 hmul
      _ = u + 3 / u := by
        field_simp [ne_of_gt hu0]
        <;> ring
  have hvRat : 13 / 4 < v + 3 / v := by
    have hsq := sq_nonneg (v - 13 / 8)
    have hmul : (13 / 4) * v < v * v + 3 := by
      nlinarith
    calc
      13 / 4 < (v * v + 3) / v := (lt_div_iff₀ hv0).2 hmul
      _ = v + 3 / v := by
        field_simp [ne_of_gt hv0]
        <;> ring
  have huvRat : 2 <= u / v + v / u := by
    have hsq := sq_nonneg (u - v)
    calc
      2 <= (u * u + v * v) / (u * v) := by
        apply (le_div_iff₀ (mul_pos hu0 hv0)).2
        nlinarith
      _ = u / v + v / u := by
        field_simp [ne_of_gt hu0, ne_of_gt hv0]
        <;> ring
  have hchords :
      17 / 2 < u + v + (u + 3) / v + (v + 3) / u := by
    have hshape :
        u + v + (u + 3) / v + (v + 3) / u =
          (u + 3 / u) + (v + 3 / v) + (u / v + v / u) := by
      ring
    rw [hshape]
    linarith
  nlinarith

private lemma cornerSpanning_shiftedBoundary_floor
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : ∀ i, 0 < sig (cfg base) (cfg (cycle i)) (cfg (cycle (i + 1))))
    (rotation offset : Fin 6) :
    minTri cfg <= sig (cfg base) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig cfg cycle R.cycle_injective
    base hOutside (rotation + offset) (hpos (rotation + offset))
  have hnext : (rotation + offset) + 1 = rotation + (offset + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

private lemma cornerSpanning_shiftedTriple_pos
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
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

private lemma cornerSpanning_shiftedTriple_floor
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (start : Fin 6) :
    minTri cfg <= sig (cfg (cycle start)) (cfg (cycle (start + 1)))
      (cfg (cycle (start + 2))) := by
  have h01 : start ≠ start + 1 := by fin_cases start <;> decide
  have h02 : start ≠ start + 2 := by fin_cases start <;> decide
  have h12 : start + 1 ≠ start + 2 := by fin_cases start <;> decide
  exact minTri_le_pos_sig_of_pairwise_ne cfg
    (R.cycle_injective.ne h01) (R.cycle_injective.ne h02)
    (R.cycle_injective.ne h12)
    (cornerSpanning_shiftedTriple_pos R start)

namespace HullSixCompactCrossChordResidual

/-- One positive top-row entry and one positive last-column entry, together
with the negative wrap corner, contradict a beating normalized `3 + 3`
frame.  The indices `r` and `s` select the positive entries. -/
theorem threeThreeCornerSpanningAt_false
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (r s : Fin 3) (hr : r = 0 ∨ r = 1) (hs : s = 1 ∨ s = 2)
    (hX0r : minTri cfg <= sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset r))))
    (hXs2 : minTri cfg <= sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset s)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let m := minTri cfg
  let U : Fin 3 -> Real × Real := fun i =>
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 -> Real × Real := fun j =>
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let u := sig (cfg P) (cfg Q) (U 0) / m
  let us := sig (cfg P) (cfg Q) (U s) / m
  let v := (-sig (cfg P) (cfg Q) (L 2)) / m
  let vr := (-sig (cfg P) (cfg Q) (L r)) / m
  let X0r := sig (cfg P) (U 0) (L r) / m
  let Xs2 := sig (cfg P) (U s) (L 2) / m
  let A := sig (cfg P) (U 0) (U s) / m
  let E := sig (cfg P) (L r) (L 2) / m
  let D := sig (cfg P) (L 2) (U 0) / m
  let Dq := sig (cfg Q) (L 2) (U 0) / m
  let A0 := sig (cfg P) (U 0) (U 1) / m
  let A1 := sig (cfg P) (U 1) (U 2) / m
  let C := sig (cfg P) (U 2) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E1 := sig (cfg P) (L 1) (L 2) / m
  let TU := sig (U 0) (U 1) (U 2) / m
  let TL := sig (L 0) (L 1) (L 2) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {a : Real} (ha : m <= a) : 1 <= a / m := by
    exact (le_div_iff₀ hm).2 (by simpa using ha)

  have hu : 1 <= u := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, u, U] using h)
  have hus : 1 <= us := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset s)
    rw [abs_of_pos (hupper s)] at h
    exact hnorm (by simpa [m, us, U] using h)
  have hv : 1 <= v := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [m, v, L] using h)
  have hvr : 1 <= vr := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset r)
    rw [abs_of_neg (hlower r)] at h
    exact hnorm (by simpa [m, vr, L] using h)
  have hX0rNorm : 1 <= X0r := hnorm (by simpa [m, X0r, U, L] using hX0r)
  have hXs2Norm : 1 <= Xs2 := hnorm (by simpa [m, Xs2, U, L] using hXs2)

  have hDqRaw : m <= sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      cornerSpanning_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 5
  have hDq : 1 <= Dq := hnorm (by simpa [Dq] using hDqRaw)
  have hDbase : Dq = D - u - v := by
    dsimp [Dq, D, u, v, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hD : u + v + 1 <= D := by linarith
  have hDthree : 3 <= D := by linarith

  have hUpperTransport : v * A = u * Xs2 + us * D := by
    dsimp [v, A, u, Xs2, us, D, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hLowerTransport : u * E = v * X0r + vr * D := by
    dsimp [u, E, v, X0r, vr, D, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hu0 : 0 <= u := le_trans zero_le_one hu
  have hv0 : 0 <= v := le_trans zero_le_one hv
  have hD0 : 0 <= D := by linarith
  have huX : u <= u * Xs2 := by
    simpa using mul_le_mul_of_nonneg_left hXs2Norm hu0
  have husD : D <= us * D := by
    simpa using mul_le_mul_of_nonneg_right hus hD0
  have hvX : v <= v * X0r := by
    simpa using mul_le_mul_of_nonneg_left hX0rNorm hv0
  have hvrD : D <= vr * D := by
    simpa using mul_le_mul_of_nonneg_right hvr hD0
  have hAprod : u + 3 <= v * A := by
    rw [hUpperTransport]
    linarith
  have hEprod : v + 3 <= u * E := by
    rw [hLowerTransport]
    linarith

  have hA0 : 1 <= A0 := by
    apply hnorm
    simpa [m, A0, U, hullSixThreeThreeUpperOffset] using
      cornerSpanning_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 0
  have hA1 : 1 <= A1 := by
    apply hnorm
    simpa [m, A1, U, hullSixThreeThreeUpperOffset] using
      cornerSpanning_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 1
  have hC : 1 <= C := by
    apply hnorm
    simpa [m, C, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using
      cornerSpanning_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 2
  have hE0 : 1 <= E0 := by
    apply hnorm
    simpa [m, E0, L, hullSixThreeThreeLowerOffset] using
      cornerSpanning_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 3
  have hE1 : 1 <= E1 := by
    apply hnorm
    simpa [m, E1, L, hullSixThreeThreeLowerOffset] using
      cornerSpanning_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 4
  have hTU : 1 <= TU := by
    apply hnorm
    simpa [m, TU, U, hullSixThreeThreeUpperOffset] using
      cornerSpanning_shiftedTriple_floor R rotation
  have hTL : 1 <= TL := by
    apply hnorm
    simpa [m, TL, L, hullSixThreeThreeLowerOffset, add_assoc] using
      cornerSpanning_shiftedTriple_floor R (rotation + 3)

  let fan : Fin 6 -> Real := fun i =>
    sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i => sig (cfg P) (cfg (cycle (rotation + i)))
        (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun : (fun i => sig (cfg P) (cfg (cycle (rotation + i)))
          (cfg (cycle (rotation + (i + 1))))) =
        (fun i => fan (rotation + i)) := by
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
        sig (cfg P) (cfg (cycle (rotation + 5)))
          (cfg (cycle rotation)) := by
      rw [← hshifted]
      simp [sumFinSix] <;> ring
    simpa [U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using hraw
  have hFan : H = A0 + A1 + C + E0 + E1 + D := by
    dsimp [H, A0, A1, C, E0, E1, D]
    rw [hSumRaw]
    ring

  have hFanLower : A + E + D + 3 <= H := by
    rcases hr with rfl | rfl
    · rcases hs with rfl | rfl
      · have hAid : A = A0 := by rfl
        have hEid : E0 + E1 = E + TL := by
          dsimp [E0, E1, E, TL, L]
          field_simp [hmNe] <;> simp only [sig] <;> ring
        nlinarith
      · have hAid : A0 + A1 = A + TU := by
          dsimp [A0, A1, A, TU, U]
          field_simp [hmNe] <;> simp only [sig] <;> ring
        have hEid : E0 + E1 = E + TL := by
          dsimp [E0, E1, E, TL, L]
          field_simp [hmNe] <;> simp only [sig] <;> ring
        nlinarith
    · rcases hs with rfl | rfl
      · have hAid : A = A0 := by rfl
        have hEid : E = E1 := by rfl
        nlinarith
      · have hAid : A0 + A1 = A + TU := by
          dsimp [A0, A1, A, TU, U]
          field_simp [hmNe] <;> simp only [sig] <;> ring
        have hEid : E = E1 := by rfl
        nlinarith

  have hscalar : 25 / 2 < H :=
    hullSixThreeThree_cornerSpanning_scalar hu hv hAprod hEprod hD hFanLower
  have hmul : ((25 : Real) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : Real) * doubledHullArea cfg < m := by
    change (2 / 25 : Real) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- A legal partial frontier whose top row has a positive `X` entry and
whose bottom row reaches the last column.  On maximal-q records these are
exactly `113`, `123`, `133`, `223`, and `233`. -/
def IsCornerSpanningRemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    (1 : Fin 4) <= T.p0 ∧ T.p2 = 3

/-- All five corner-spanning partial frontiers are closed in their original
geometric frame, without any `Y`-sign premise. -/
theorem cornerSpanning_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts) (hLegal : T.Legal)
    (hp0 : (1 : Fin 4) <= T.p0) (hp2 : T.p2 = 3) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hLegal with
    ⟨hp01, hp12, hq01, hq12, hpq0, hpq1, hpq2, hp2floor, hq0⟩
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hp0cases : T.p0 = 1 ∨ T.p0 = 2 := by omega
  by_cases hp1three : T.p1 = 3
  · have hXs2 : minTri cfg <= F.X 1 2 := by
      apply hLeft
      simp [HullSixThreeThreeCuts.p, hp1three]
    rcases hp0cases with hp0one | hp0two
    · have hX0r : minTri cfg <= F.X 0 0 := by
        apply hLeft
        simp [HullSixThreeThreeCuts.p, hp0one]
      exact R.threeThreeCornerSpanningAt_false F.view F.rotation
        F.upper_pos F.lower_neg 0 1 (Or.inl rfl) (Or.inl rfl)
        (by simpa [X] using hX0r) (by simpa [X] using hXs2)
    · have hX0r : minTri cfg <= F.X 0 1 := by
        apply hLeft
        simp [HullSixThreeThreeCuts.p, hp0two]
      exact R.threeThreeCornerSpanningAt_false F.view F.rotation
        F.upper_pos F.lower_neg 1 1 (Or.inr rfl) (Or.inl rfl)
        (by simpa [X] using hX0r) (by simpa [X] using hXs2)
  · have hXs2 : minTri cfg <= F.X 2 2 := by
      apply hLeft
      simp [HullSixThreeThreeCuts.p, hp2]
    rcases hp0cases with hp0one | hp0two
    · have hX0r : minTri cfg <= F.X 0 0 := by
        apply hLeft
        simp [HullSixThreeThreeCuts.p, hp0one]
      exact R.threeThreeCornerSpanningAt_false F.view F.rotation
        F.upper_pos F.lower_neg 0 2 (Or.inl rfl) (Or.inr rfl)
        (by simpa [X] using hX0r) (by simpa [X] using hXs2)
    · have hX0r : minTri cfg <= F.X 0 1 := by
        apply hLeft
        simp [HullSixThreeThreeCuts.p, hp0two]
      exact R.threeThreeCornerSpanningAt_false F.view F.rotation
        F.upper_pos F.lower_neg 1 2 (Or.inr rfl) (Or.inr rfl)
        (by simpa [X] using hX0r) (by simpa [X] using hXs2)

end HullSixThreeThreeGeometricFrame

/-- Provider for the five corner-spanning members of the honest remaining
maximal-q frontier family. -/
theorem hullSixThreeThreeCornerSpanningXFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsCornerSpanningRemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp2⟩
  exact F.cornerSpanning_xFrontierClosed T hLegal hp0 hp2

end Heilbronn8
