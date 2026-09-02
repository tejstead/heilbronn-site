import Heilbronn8.Survivors.Join.HullSixThreeThreeP033ScalarAMGM
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# The maximal-q `p = 033` X-frontier

This file closes the partial `X`-frontier with first cuts `033`.  It uses no
`Y` sign and no nonboundary `Q` chord.  Around `P`, the six rays have merged
slope order

```text
U0, L0, L1, L2, U1, U2.
```

Besides the five successive-ray floors, the proof uses only the consecutive
hull triangles `U2 L0 L1`, `L0 L1 L2`, and the two boundary `Q`-fan edges
`L1 L2`, `L2 U0`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma p033_shiftedBoundary_floor
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

private lemma p033_shiftedTriple_pos
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

private lemma p033_shiftedTriple_floor
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
    (p033_shiftedTriple_pos R start)

namespace HullSixCompactCrossChordResidual

/-- The `p = 033` successive-ray and two consecutive hull-triangle floors
contradict a beating normalized `3 + 3` frame. -/
theorem threeThreeP033At_false
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
    (hX00 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))) ≤
      -minTri cfg)
    (hX12 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let m := minTri cfg
  let U : Fin 3 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let a := sig (cfg P) (cfg Q) (U 0) / m
  let b := (-sig (cfg P) (cfg Q) (L 0)) / m
  let c := sig (cfg P) (cfg Q) (U 1) / m
  let d := (-sig (cfg P) (cfg Q) (L 1)) / m
  let e := (-sig (cfg P) (cfg Q) (L 2)) / m
  let f := sig (cfg P) (cfg Q) (U 2) / m
  let r1 := (-sig (cfg P) (U 0) (L 0)) / m
  let r4 := sig (cfg P) (U 1) (L 2) / m
  let A := sig (cfg P) (U 0) (U 1) / m
  let B := sig (cfg P) (U 1) (U 2) / m
  let C := sig (cfg P) (U 2) (L 0) / m
  let D := sig (cfg P) (L 0) (L 1) / m
  let E := sig (cfg P) (L 1) (L 2) / m
  let F := sig (cfg P) (L 2) (U 0) / m
  let X21 := sig (cfg P) (U 2) (L 1) / m
  let TM := sig (U 2) (L 0) (L 1) / m
  let TL := sig (L 0) (L 1) (L 2) / m
  let Eq := sig (cfg Q) (L 1) (L 2) / m
  let Fq := sig (cfg Q) (L 2) (U 0) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {z : ℝ} (hz : m ≤ z) : 1 ≤ z / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hz)

  have ha : 1 ≤ a := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, a, U] using h)
  have hb : 1 ≤ b := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    exact hnorm (by simpa [m, b, L] using h)
  have hc : 1 ≤ c := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, c, U] using h)
  have hd : 1 ≤ d := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    exact hnorm (by simpa [m, d, L] using h)
  have he : 1 ≤ e := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [m, e, L] using h)
  have hf : 1 ≤ f := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at h
    exact hnorm (by simpa [m, f, U] using h)

  have hr1 : 1 ≤ r1 := by
    apply hnorm
    dsimp [m, r1, U, L]
    linarith
  have hr4 : 1 ≤ r4 :=
    hnorm (by simpa [m, r4, U, L] using hX12)
  have hBraw : m ≤ sig (cfg P) (U 1) (U 2) := by
    simpa [m, U, hullSixThreeThreeUpperOffset] using
      p033_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 1
  have hB : 1 ≤ B := hnorm (by simpa [B] using hBraw)
  have hDraw : m ≤ sig (cfg P) (L 0) (L 1) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p033_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 3
  have hD : 1 ≤ D := hnorm (by simpa [D] using hDraw)
  have hEraw : m ≤ sig (cfg P) (L 1) (L 2) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p033_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 4
  have hE : 1 ≤ E := hnorm (by simpa [E] using hEraw)
  have hTMraw : m ≤ sig (U 2) (L 0) (L 1) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p033_shiftedTriple_floor R (rotation + 2)
  have hTM : 1 ≤ TM := hnorm (by simpa [TM] using hTMraw)
  have hTLraw : m ≤ sig (L 0) (L 1) (L 2) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p033_shiftedTriple_floor R (rotation + 3)
  have hTL : 1 ≤ TL := hnorm (by simpa [TL] using hTLraw)
  have hEqRaw : m ≤ sig (cfg Q) (L 1) (L 2) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p033_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 4
  have hEq : 1 ≤ Eq := hnorm (by simpa [Eq] using hEqRaw)
  have hFqRaw : m ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p033_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hFq : 1 ≤ Fq := hnorm (by simpa [Fq] using hFqRaw)

  have hEqBase : Eq = E - d + e := by
    dsimp [Eq, E, d, e, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hQE : d - e + 1 ≤ E := by linarith
  have hFbase : Fq = F - a - e := by
    dsimp [Fq, F, a, e, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFlower : e + 2 ≤ F := by linarith

  have hAtransport :
      b * d * e * A = c * d * e * r1 + a * c * e * D +
        a * b * c * E + a * b * d * r4 := by
    dsimp [b, d, e, A, c, r1, a, D, E, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hX21transport :
      e * c * X21 = f * c * E + f * d * r4 + d * e * B := by
    dsimp [e, c, X21, f, E, d, r4, B, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hMixedTransport : C + D = X21 + TM := by
    dsimp [C, D, X21, TM, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hLowerTransport :
      d * (D + E) = e * D + b * E + d * TL := by
    dsimp [d, D, E, e, b, TL, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring

  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hf0 : 0 ≤ f := le_trans zero_le_one hf
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  have hr10 : 0 ≤ r1 := le_trans zero_le_one hr1
  have hr40 : 0 ≤ r4 := le_trans zero_le_one hr4
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hTM0 : 0 ≤ TM := le_trans zero_le_one hTM

  have hAprod :
      c * d * e + c * D * e + b * c * E + b * d ≤
        b * d * e * A := by
    rw [hAtransport]
    have h1 : c * d * e ≤ c * d * e * r1 := by
      simpa using mul_le_mul_of_nonneg_left hr1
        (mul_nonneg (mul_nonneg hc0 hd0) he0)
    have h2 : c * D * e ≤ a * c * e * D := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right ha
          (mul_nonneg (mul_nonneg hc0 hD0) he0)
    have h3 : b * c * E ≤ a * b * c * E := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right ha
          (mul_nonneg (mul_nonneg hb0 hc0) hE0)
    have h4 : b * d ≤ a * b * d * r4 := by
      calc
        b * d = 1 * (b * d) := by ring
        _ ≤ a * (b * d) :=
          mul_le_mul_of_nonneg_right ha (mul_nonneg hb0 hd0)
        _ = a * b * d := by ring
        _ ≤ a * b * d * r4 := by
          simpa using mul_le_mul_of_nonneg_left hr4
            (mul_nonneg (mul_nonneg ha0 hb0) hd0)
    nlinarith
  have hX21prod : c * E + d + d * e ≤ e * c * X21 := by
    rw [hX21transport]
    have h1 : c * E ≤ f * c * E := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hf (mul_nonneg hc0 hE0)
    have h2 : d ≤ f * d * r4 := by
      calc
        d = 1 * d := by ring
        _ ≤ f * d := mul_le_mul_of_nonneg_right hf hd0
        _ ≤ f * d * r4 := by
          simpa using mul_le_mul_of_nonneg_left hr4 (mul_nonneg hf0 hd0)
    have h3 : d * e ≤ d * e * B := by
      simpa using mul_le_mul_of_nonneg_left hB (mul_nonneg hd0 he0)
    nlinarith
  have hCDprod : e * c + c * E + d + d * e ≤ e * c * (C + D) := by
    have hsector : e * c * (C + D) = e * c * X21 + e * c * TM := by
      rw [hMixedTransport]
      ring
    rw [hsector]
    have htri : e * c ≤ e * c * TM := by
      simpa using mul_le_mul_of_nonneg_left hTM (mul_nonneg he0 hc0)
    nlinarith
  have hLowerProd : e * D + b * E + d ≤ d * (D + E) := by
    rw [hLowerTransport]
    have htri : d ≤ d * TL := by
      simpa using mul_le_mul_of_nonneg_left hTL hd0
    linarith

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
        sig (cfg P) (cfg (cycle (rotation + 5)))
          (cfg (cycle rotation)) := by
      rw [← hshifted]
      simp [sumFinSix] <;> ring
    simpa [U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using hraw
  have hFan : H = A + B + C + D + E + F := by
    dsimp [H, A, B, C, D, E, F]
    rw [hSumRaw]
    ring

  have hscalar : 25 / 2 < H :=
    hullSixThreeThree_p033_scalar hb hc hd he hD hE hAprod hCDprod
      hLowerProd hQE hB hFlower (le_of_eq hFan.symm)
  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- The single maximal-q remaining frontier with first cuts `033`. -/
def IsP033RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 0 ∧ T.p1 = 3 ∧ T.p2 = 3

/-- The `033` X-frontier is closed in its original frame. -/
theorem p033_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 3) (hp2 : T.p2 = 3) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : F.X 0 0 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX12 : minTri cfg ≤ F.X 1 2 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  exact R.threeThreeP033At_false F.view F.rotation F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX12)

end HullSixThreeThreeGeometricFrame

/-- Provider for the `p = 033`, `q = 233` X-frontier fibre. -/
theorem hullSixThreeThreeP033XFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP033RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp1, hp2⟩
  exact F.p033_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
