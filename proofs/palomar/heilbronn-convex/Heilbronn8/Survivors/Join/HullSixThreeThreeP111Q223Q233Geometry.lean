import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Q223RawScalar
import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Q233RawScalar
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# Geometry for the `p = 111`, `q = 223/233` cells

Both cells use the same normalized six-fan frame.  The adapter constructs it
once and passes the relevant signed `Y` floors to the two small raw scalar
reductions.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

private lemma p111Q_shiftedBoundary_floor
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : forall i,
      0 < sig (cfg base) (cfg (cycle i)) (cfg (cycle (i + 1))))
    (rotation offset : Fin 6) :
    minTri cfg <= sig (cfg base) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig cfg cycle R.cycle_injective
    base hOutside (rotation + offset) (hpos (rotation + offset))
  have hnext : (rotation + offset) + 1 =
      rotation + (offset + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

private lemma p111Q_shiftedTriple_pos
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

private lemma p111Q_shiftedTriple_floor
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
    (R.cycle_injective.ne h12) (p111Q_shiftedTriple_pos R start)

namespace HullSixCompactCrossChordResidual

/-- The two remaining high-`Y22` masks are incompatible with a beating
`p = 111` frame. -/
theorem threeThreeP111Q223Q233At_false
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
    (hX21 : sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) <=
        -minTri cfg)
    (hmask :
      (minTri cfg <= sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ∧
        sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) <=
            -minTri cfg ∧
        minTri cfg <= sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) ∨
      (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) <=
            -minTri cfg ∧
        minTri cfg <= sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))))) :
    False := by
  let s := minTri cfg
  let U : Fin 3 -> Real × Real := fun i =>
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 -> Real × Real := fun j =>
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let a := sig (cfg P) (cfg Q) (U 0) / s
  let b := sig (cfg P) (cfg Q) (U 1) / s
  let c := sig (cfg P) (cfg Q) (U 2) / s
  let d := (-sig (cfg P) (cfg Q) (L 0)) / s
  let e := (-sig (cfg P) (cfg Q) (L 1)) / s
  let f := (-sig (cfg P) (cfg Q) (L 2)) / s
  let A := sig (cfg P) (U 0) (U 1) / s
  let B := sig (cfg P) (U 1) (U 2) / s
  let C := sig (cfg P) (U 2) (L 0) / s
  let D := sig (cfg P) (L 0) (L 1) / s
  let E := sig (cfg P) (L 1) (L 2) / s
  let F := sig (cfg P) (L 2) (U 0) / s
  let X00 := sig (cfg P) (U 0) (L 0) / s
  let X21 := (-sig (cfg P) (U 2) (L 1)) / s
  let Y01 := sig (cfg Q) (U 0) (L 1) / s
  let Y02 := sig (cfg Q) (U 0) (L 2) / s
  let Y12 := sig (cfg Q) (U 1) (L 2) / s
  let Y22 := sig (cfg Q) (U 2) (L 2) / s
  let TU := sig (U 0) (U 1) (U 2) / s
  let TL := sig (L 0) (L 1) (L 2) / s
  let E02 := sig (cfg P) (U 0) (U 2) / s
  let H := doubledHullArea cfg / s
  let g1 := A / (a * b)
  let g2 := B / (b * c)
  let g3 := X21 / (c * e)
  let g4 := E / (e * f)

  have hs : 0 < s := by simpa [s] using R.minTri_pos
  have hsNe : s ≠ 0 := ne_of_gt hs
  have hnorm {x : Real} (hx : s <= x) : 1 <= x / s :=
    (le_div_iff₀ hs).2 (by simpa using hx)
  have hU0Ne : sig (cfg P) (cfg Q) (U 0) ≠ 0 := by
    exact ne_of_gt (by simpa [U] using hupper 0)
  have hU1Ne : sig (cfg P) (cfg Q) (U 1) ≠ 0 := by
    exact ne_of_gt (by simpa [U] using hupper 1)
  have hU2Ne : sig (cfg P) (cfg Q) (U 2) ≠ 0 := by
    exact ne_of_gt (by simpa [U] using hupper 2)
  have hL0Ne : sig (cfg P) (cfg Q) (L 0) ≠ 0 := by
    exact ne_of_lt (by simpa [L] using hlower 0)
  have hL1Ne : sig (cfg P) (cfg Q) (L 1) ≠ 0 := by
    exact ne_of_lt (by simpa [L] using hlower 1)
  have hL2Ne : sig (cfg P) (cfg Q) (L 2) ≠ 0 := by
    exact ne_of_lt (by simpa [L] using hlower 2)

  have ha1 : 1 <= a := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [a, U] using h)
  have hb1 : 1 <= b := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [b, U] using h)
  have hc1 : 1 <= c := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at h
    exact hnorm (by simpa [c, U] using h)
  have hd1 : 1 <= d := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    exact hnorm (by simpa [d, L] using h)
  have he1 : 1 <= e := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    exact hnorm (by simpa [e, L] using h)
  have hf1 : 1 <= f := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [f, L] using h)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1

  have hfanFloor (offset : Fin 6) :
      s <= sig (cfg P) (cfg (cycle (rotation + offset)))
        (cfg (cycle (rotation + (offset + 1)))) :=
    p111Q_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
      rotation offset
  have hA : 1 <= A := hnorm (by
    simpa [A, U, hullSixThreeThreeUpperOffset] using hfanFloor 0)
  have hB : 1 <= B := hnorm (by
    simpa [B, U, hullSixThreeThreeUpperOffset] using hfanFloor 1)
  have hC : 1 <= C := hnorm (by
    simpa [C, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using hfanFloor 2)
  have hD : 1 <= D := hnorm (by
    simpa [D, L, hullSixThreeThreeLowerOffset, add_assoc] using hfanFloor 3)
  have hE : 1 <= E := hnorm (by
    simpa [E, L, hullSixThreeThreeLowerOffset, add_assoc] using hfanFloor 4)
  have hF : 1 <= F := hnorm (by
    simpa [F, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using hfanFloor 5)
  have hX00n : 1 <= X00 := hnorm (by simpa [X00, U, L] using hX00)
  have hX21n : 1 <= X21 := by
    apply hnorm
    dsimp [X21, U, L]
    linarith

  have hTURaw : s <= sig (U 0) (U 1) (U 2) := by
    simpa [s, U, hullSixThreeThreeUpperOffset, add_assoc] using
      p111Q_shiftedTriple_floor R rotation
  have hTU : 1 <= TU := hnorm (by simpa [TU] using hTURaw)
  have hTLRaw : s <= sig (L 0) (L 1) (L 2) := by
    simpa [s, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p111Q_shiftedTriple_floor R (rotation + 3)
  have hTL : 1 <= TL := hnorm (by simpa [TL] using hTLRaw)

  have hB0Raw : s <= sig (cfg Q) (U 0) (U 1) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p111Q_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 0
  have hEp : 1 <= A + a - b := by
    have hB0n := hnorm hB0Raw
    have hid : sig (cfg Q) (U 0) (U 1) / s = A + a - b := by
      dsimp [A, a, b, U]
      field_simp [hsNe]
      <;> simp only [sig]
      <;> ring
    rwa [hid] at hB0n

  have hAdef : A = a * b * g1 := by
    dsimp only [g1]
    field_simp [ha.ne', hb.ne']
    <;> ring
  have hBdef : B = b * c * g2 := by
    dsimp only [g2]
    field_simp [hb.ne', hc.ne']
    <;> ring
  have hFirstGap :
      hullSixThreeThreeRGap (cfg P) (cfg Q) (U 0) (U 1) s =
        hullSixThreeThreeTGap (cfg P) (cfg Q) (U 0) (U 1) s := by
    simp only [hullSixThreeThreeRGap, hullSixThreeThreeTGap,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hsNe, hU0Ne, hU1Ne] <;> ring
  have hSameGap :
      hullSixThreeThreeSGap (cfg P) (cfg Q) (U 1) (U 1) s = 0 := by
    simp [hullSixThreeThreeSGap, sig]
  have hFdef : F = a * f * (g1 + g2 + g3 + g4) := by
    have hwrap := sig_threeThree_qBlind_wrap_identity
      (cfg P) (cfg Q) (U 0) (U 1) (U 2) (U 1) (L 1) (L 2)
      hsNe hU0Ne hU1Ne hU2Ne hU1Ne hL1Ne hL2Ne
    rw [hFirstGap, hSameGap] at hwrap
    simp only [add_zero] at hwrap
    simpa only [F, a, b, c, e, f, g1, g2, g3, g4, A, B, X21, E,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
      hullSixThreeThreeTGap, hullSixThreeThreeWGap,
      hullSixThreeThreeZGap] using hwrap.symm
  have hLowerEar :
      D + E = TL + (d / a) * F + (f / a) * X00 := by
    have hCocycle :
        sig (L 0) (L 1) (L 2) =
          sig (cfg P) (L 0) (L 1) + sig (cfg P) (L 1) (L 2) -
            sig (cfg P) (L 0) (L 2) := by
      rw [sig_crossChord_base_change (cfg P) (L 0) (L 1) (L 2)]
      ring
    have hPlucker :
        sig (cfg P) (cfg Q) (U 0) * sig (cfg P) (L 0) (L 2) =
          (-sig (cfg P) (cfg Q) (L 0)) * sig (cfg P) (L 2) (U 0) +
            (-sig (cfg P) (cfg Q) (L 2)) * sig (cfg P) (U 0) (L 0) := by
      have hp := sig_crossChord_plucker
        (cfg P) (cfg Q) (L 0) (U 0) (L 2)
      rw [sig_swap (cfg P) (L 0) (U 0),
        sig_swap (cfg P) (U 0) (L 2)] at hp
      nlinarith only [hp]
    have hda :
        d / a = (-sig (cfg P) (cfg Q) (L 0)) /
          sig (cfg P) (cfg Q) (U 0) := by
      dsimp only [d, a]
      field_simp [hsNe, hU0Ne] <;> ring
    have hfa :
        f / a = (-sig (cfg P) (cfg Q) (L 2)) /
          sig (cfg P) (cfg Q) (U 0) := by
      dsimp only [f, a]
      field_simp [hsNe, hU0Ne] <;> ring
    have hRatio :
        sig (cfg P) (L 0) (L 2) / s =
          (d / a) * F + (f / a) * X00 := by
      rw [hda, hfa]
      dsimp only [F, X00]
      field_simp [hsNe, hU0Ne]
      nlinarith only [hPlucker]
    calc
      D + E = TL + sig (cfg P) (L 0) (L 2) / s := by
        dsimp only [D, E, TL]
        rw [hCocycle]
        ring
      _ = TL + (d / a) * F + (f / a) * X00 := by
        rw [hRatio]
        ring
  have hTUidentity : TU = A + B - E02 := by
    have hbase := sig_crossChord_base_change
      (cfg P) (U 0) (U 1) (U 2)
    dsimp only [TU, A, B, E02]
    field_simp [hsNe]
    nlinarith only [hbase]
  have hE02identity : E02 = c * A / b + a * B / b := by
    have hPlucker :
        sig (cfg P) (cfg Q) (U 1) * sig (cfg P) (U 0) (U 2) =
          sig (cfg P) (cfg Q) (U 2) * sig (cfg P) (U 0) (U 1) +
            sig (cfg P) (cfg Q) (U 0) * sig (cfg P) (U 1) (U 2) := by
      have hp := sig_crossChord_plucker
        (cfg P) (cfg Q) (U 1) (U 0) (U 2)
      rw [sig_swap (cfg P) (U 1) (U 0)] at hp
      nlinarith only [hp]
    dsimp only [E02, c, A, b, a, B]
    field_simp [hsNe, hU1Ne]
    linear_combination hPlucker
  have hCidentity : C = (c / a) * X00 + (d / a) * E02 := by
    have hPlucker :
        sig (cfg P) (cfg Q) (U 0) * sig (cfg P) (U 2) (L 0) =
          sig (cfg P) (cfg Q) (U 2) * sig (cfg P) (U 0) (L 0) +
            (-sig (cfg P) (cfg Q) (L 0)) * sig (cfg P) (U 0) (U 2) := by
      have hp := sig_crossChord_plucker
        (cfg P) (cfg Q) (U 0) (U 2) (L 0)
      nlinarith only [hp]
    dsimp only [C, c, a, X00, d, E02]
    field_simp [hsNe, hU0Ne]
    linear_combination hPlucker

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
  have hH : H = A + B + C + D + E + F := by
    have hraw : doubledHullArea cfg =
        sig (cfg P) (U 0) (U 1) + sig (cfg P) (U 1) (U 2) +
        sig (cfg P) (U 2) (L 0) + sig (cfg P) (L 0) (L 1) +
        sig (cfg P) (L 1) (L 2) + sig (cfg P) (L 2) (U 0) := by
      rw [← hshifted]
      simp [sumFinSix, U, L, hullSixThreeThreeUpperOffset,
        hullSixThreeThreeLowerOffset]
      <;> ring
    dsimp [H, A, B, C, D, E, F]
    rw [hraw]
    ring

  have hY01identity :
      Y01 = a + e -
        (e * A / b + a * e * B / (b * c) + a * e * g3) := by
    have hneg := sig_threeThree_qBlind_qY01Neg_identity
      (cfg P) (cfg Q) (U 0) (U 1) (U 2) (U 1) (L 1)
      hsNe hU0Ne hU1Ne hU2Ne hU1Ne hL1Ne
    rw [hFirstGap, hSameGap] at hneg
    simp only [add_zero] at hneg
    have hneg' : a * e * (g1 + g2 + g3) - a - e = -Y01 := by
      simpa only [Y01, a, b, c, e, g1, g2, g3, A, B, X21,
        hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
        hullSixThreeThreeTGap, hullSixThreeThreeWGap, neg_div] using hneg
    have hg1 : a * e * g1 = e * A / b := by
      dsimp only [g1]
      field_simp [ha.ne', hb.ne'] <;> ring
    have hg2 : a * e * g2 = a * e * B / (b * c) := by
      dsimp only [g2]
      field_simp [hb.ne', hc.ne'] <;> ring
    have hsum :
        a * e * (g1 + g2 + g3) =
          e * A / b + a * e * B / (b * c) + a * e * g3 := by
      calc
        a * e * (g1 + g2 + g3) =
            a * e * g1 + a * e * g2 + a * e * g3 := by ring
        _ = e * A / b + a * e * B / (b * c) + a * e * g3 := by
          rw [hg1, hg2]
    rw [← hsum]
    nlinarith only [hneg']
  have hY12identity : Y12 = b + f - b * f * (g2 + g3 + g4) := by
    have hy := sig_threeThree_qBlind_qY12Pos_identity
      (cfg P) (cfg Q) (U 1) (U 2) (L 1) (L 2)
      hsNe hU1Ne hU2Ne hL1Ne hL2Ne
    simpa only [Y12, b, c, e, f, g2, g3, g4, B, X21, E,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
      hullSixThreeThreeTGap, hullSixThreeThreeWGap,
      hullSixThreeThreeZGap] using hy.symm
  have hY22identity : Y22 = c + f - c * f * (g3 + g4) := by
    have hzero :
        hullSixThreeThreeTGap (cfg P) (cfg Q) (U 2) (U 2) s = 0 := by
      simp [hullSixThreeThreeTGap, sig]
    have hy := sig_threeThree_qBlind_qY12Pos_identity
      (cfg P) (cfg Q) (U 2) (U 2) (L 1) (L 2)
      hsNe hU2Ne hU2Ne hL1Ne hL2Ne
    rw [hzero] at hy
    simp only [zero_add] at hy
    simpa only [Y22, c, e, f, g3, g4, X21, E,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight,
      hullSixThreeThreeWGap, hullSixThreeThreeZGap] using hy.symm
  have hY02identity : Y02 = a + f - F := by
    have hbase := sig_crossChord_base_change
      (cfg P) (cfg Q) (U 0) (L 2)
    rw [sig_swap (cfg P) (U 0) (L 2)] at hbase
    dsimp only [Y02, a, f, F]
    field_simp [hsNe]
    nlinarith only [hbase]

  have hscalar : (25 : Real) / 2 < H := by
    rcases hmask with h223 | h233
    · have hY01n : 1 <= Y01 := hnorm (by simpa [Y01, U, L] using h223.1)
      have hY12n : Y12 <= -1 := by
        apply (div_le_iff₀ hs).2
        dsimp [Y12, U, L]
        nlinarith [h223.2.1]
      have hY22n : 1 <= Y22 := hnorm (by
        simpa [Y22, U, L] using h223.2.2)
      have hY01raw :
          e * A / b + a * e * B / (b * c) + a * e * g3 <=
            a + e - 1 := by
        rw [hY01identity] at hY01n
        linarith
      have hY12raw :
          b + f + 1 <= b * f * (g2 + g3 + g4) := by
        rw [hY12identity] at hY12n
        linarith
      have hY22raw : 1 <= c + f - c * f * (g3 + g4) := by
        rwa [← hY22identity]
      have hX21raw : 1 <= c * e * g3 := by
        dsimp [g3]
        field_simp [hc.ne', he.ne']
        <;> nlinarith [hX21n]
      exact hullSixThreeThreeP111Q223_raw_scalar
        ha1 hb1 hc1 hd1 he1 hf1 hB hC hX00n hTL hEp
        hY12raw hY22raw hX21raw hY01raw hAdef hBdef hFdef
        hLowerEar hH
    · have hY02n : Y02 <= -1 := by
        apply (div_le_iff₀ hs).2
        dsimp [Y02, U, L]
        nlinarith [h233.1]
      have hY12n : 1 <= Y12 := hnorm (by
        simpa [Y12, U, L] using h233.2)
      have hFstrong : a + f + 1 <= F := by
        rw [hY02identity] at hY02n
        linarith
      have hY12upper :
          b * f * (g2 + g3 + g4) <= b + f - 1 := by
        rw [hY12identity] at hY12n
        linarith
      have hAsign : b - a + (a + b) / f <= A := by
        have hFsplit :
            F = (f / b) * A + (a / b) *
              (b * f * (g2 + g3 + g4)) := by
          rw [hAdef, hFdef]
          field_simp [hb.ne']
          <;> ring
        have hupperF :
            F <= (f / b) * A + (a / b) * (b + f - 1) := by
          rw [hFsplit]
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hY12upper
              (div_nonneg ha.le hb.le))
        have hupperFmul :
            b * F <= f * A + a * (b + f - 1) := by
          calc
            b * F <= b * ((f / b) * A + (a / b) * (b + f - 1)) :=
              mul_le_mul_of_nonneg_left hupperF (le_of_lt hb)
            _ = f * A + a * (b + f - 1) := by
              field_simp [hb.ne']
              <;> ring
        have hFstrongMul : b * (a + f + 1) <= b * F :=
          mul_le_mul_of_nonneg_left hFstrong (le_of_lt hb)
        have hscaled :
            (b - a + (a + b) / f) * f <= A * f := by
          field_simp [hf.ne']
          nlinarith [hFstrongMul, hupperFmul]
        exact le_of_mul_le_mul_right hscaled hf
      have hE02lower : (c * A + a) / b <= E02 := by
        rw [hE02identity]
        have hBscaled : a <= a * B := by
          nlinarith [mul_le_mul_of_nonneg_left hB (le_of_lt ha)]
        apply (div_le_iff₀ hb).2
        field_simp [hb.ne']
        nlinarith
      have hE02nonneg : 0 <= E02 := by
        have : 0 < (c * A + a) / b := by positivity
        exact le_trans (le_of_lt this) hE02lower
      have hUdiag :
          1 + c / a + (1 + 1 / a) * E02 <= A + B + C := by
        have hAB : 1 + E02 <= A + B := by
          rw [hTUidentity] at hTU
          linarith
        have hcx : c / a <= (c / a) * X00 := by
          simpa using mul_le_mul_of_nonneg_left hX00n
            (div_nonneg hc.le ha.le)
        have hde : (1 / a) * E02 <= (d / a) * E02 := by
          apply mul_le_mul_of_nonneg_right _ hE02nonneg
          exact (div_le_div_iff_of_pos_right ha).2 hd1
        rw [hCidentity]
        nlinarith
      have hUfan : A + 2 <= A + B + C := by linarith
      have hLlower : 1 + (F + f) / a <= D + E := by
        have hdf : (1 / a) * F <= (d / a) * F := by
          apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hF)
          exact (div_le_div_iff_of_pos_right ha).2 hd1
        have hfx : f / a <= (f / a) * X00 := by
          simpa using mul_le_mul_of_nonneg_left hX00n
            (div_nonneg hf.le ha.le)
        rw [hLowerEar]
        have hshape :
            1 + (F + f) / a = 1 + (1 / a) * F + f / a := by
          field_simp [ha.ne'] <;> ring
        rw [hshape]
        linarith [hTL, hdf, hfx]
      have hH' : H = (A + B + C) + (D + E) + F := by
        rw [hH]
        ring
      exact hullSixThreeThreeP111Q233_raw_scalar
        ha1 hb1 hc1 hf1 hA hAsign hE02lower hUdiag hUfan
        hLlower hFstrong hH'

  have hmul : ((25 : Real) / 2) * s < doubledHullArea cfg :=
    (lt_div_iff₀ hs).1 hscalar
  have hcut : (2 / 25 : Real) * doubledHullArea cfg < s := by
    change (2 / 25 : Real) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

/-- Direct q223 cross-floor wrapper. -/
theorem threeThreeP111Q223At_false
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q) (rotation : Fin 6)
    (hupper : forall i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : forall j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hX00 : minTri cfg <= sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX21 : sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) <=
        -minTri cfg)
    (hY01 : minTri cfg <= sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY12 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) <=
        -minTri cfg)
    (hY22 : minTri cfg <= sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False :=
  R.threeThreeP111Q223Q233At_false V rotation hupper hlower hX00 hX21
    (Or.inl ⟨hY01, hY12, hY22⟩)

/-- Direct q233 cross-floor wrapper. -/
theorem threeThreeP111Q233At_false
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q) (rotation : Fin 6)
    (hupper : forall i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : forall j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hX00 : minTri cfg <= sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX21 : sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) <=
        -minTri cfg)
    (hY02 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) <=
        -minTri cfg)
    (hY12 : minTri cfg <= sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False :=
  R.threeThreeP111Q223Q233At_false V rotation hupper hlower hX00 hX21
    (Or.inr ⟨hY02, hY12⟩)

end HullSixCompactCrossChordResidual

end Heilbronn8
