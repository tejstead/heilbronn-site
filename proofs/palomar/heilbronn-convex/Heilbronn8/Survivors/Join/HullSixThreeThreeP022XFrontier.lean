import Heilbronn8.Survivors.Join.HullSixThreeThreeP022XFrontierScalarAMGM
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# The maximal-q `p = 022` partial-X frontier

Around `P`, the six rays occur in the merged order

```text
U0, L0, L1, U1, U2, L2.
```

The retained partial frontier supplies `-X00`, `X11`, and `-X22`.  Two
ordinary boundary edges complete the five adjacent floors.  The sign of
`Y01` is not retained, so its universal absolute triangle floor is split
directly into `Y01 >= 1` and `Y01 <= -1`.  Exact determinant transport
then feeds the two compact scalar certificates.  The negative branch also
uses the consecutive hull triangle `U2 L0 L1`; the upper hull triangle and
the cell `Y00` are not needed.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma p022_shiftedBoundary_floor
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

private lemma p022_shiftedTriple_pos
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

private lemma p022_shiftedTriple_floor
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
    (p022_shiftedTriple_pos R start)

namespace HullSixCompactCrossChordResidual

/-- The three retained `X` floors of the `022` frontier, the unsigned
`Y01` floor, and one consecutive hull triangle contradict a beating
normalized `3 + 3` frame. -/
theorem threeThreeP022At_false
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
    (hX11 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hX22 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) ≤
      -minTri cfg) :
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
  let r2 := sig (cfg P) (L 0) (L 1) / m
  let r3 := sig (cfg P) (U 1) (L 1) / m
  let r4 := sig (cfg P) (U 1) (U 2) / m
  let r5 := (-sig (cfg P) (U 2) (L 2)) / m
  let A := sig (cfg P) (U 0) (U 1) / m
  let B := sig (cfg P) (U 1) (U 2) / m
  let C := sig (cfg P) (U 2) (L 0) / m
  let D := sig (cfg P) (L 0) (L 1) / m
  let E := sig (cfg P) (L 1) (L 2) / m
  let F := sig (cfg P) (L 2) (U 0) / m
  let Fq := sig (cfg Q) (L 2) (U 0) / m
  let Y := sig (cfg Q) (U 0) (L 1) / m
  let TC := sig (U 2) (L 0) (L 1) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {x : ℝ} (hx : m ≤ x) : 1 ≤ x / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hx)
  have hnormAbs {x : ℝ} (hx : m ≤ |x|) : 1 ≤ |x / m| := by
    rw [abs_div, abs_of_pos hm]
    exact (le_div_iff₀ hm).2 (by simpa using hx)

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
    dsimp [r1, U, L]
    linarith
  have hr2Raw : m ≤ sig (cfg P) (L 0) (L 1) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p022_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 3
  have hr2 : 1 ≤ r2 := hnorm (by simpa [r2] using hr2Raw)
  have hr3 : 1 ≤ r3 := hnorm (by simpa [m, r3, U, L] using hX11)
  have hr4Raw : m ≤ sig (cfg P) (U 1) (U 2) := by
    simpa [m, U, hullSixThreeThreeUpperOffset, add_assoc] using
      p022_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 1
  have hr4 : 1 ≤ r4 := hnorm (by simpa [r4] using hr4Raw)
  have hr5 : 1 ≤ r5 := by
    apply hnorm
    dsimp [r5, U, L]
    linarith

  have hFqRaw : m ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p022_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hFq : 1 ≤ Fq := hnorm (by simpa [Fq] using hFqRaw)
  have hFbase : Fq = F - a - e := by
    dsimp [Fq, F, a, e, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFlower : a + e + 1 ≤ F := by linarith

  have hQU0 : Q ≠ cycle (rotation + hullSixThreeThreeUpperOffset 0) := by
    intro h
    exact V.Q_outside ⟨_, h.symm⟩
  have hQL1 : Q ≠ cycle (rotation + hullSixThreeThreeLowerOffset 1) := by
    intro h
    exact V.Q_outside ⟨_, h.symm⟩
  have hU0L1Index :
      rotation + hullSixThreeThreeUpperOffset 0 ≠
        rotation + hullSixThreeThreeLowerOffset 1 := by
    fin_cases rotation <;> decide
  have hU0L1 :
      cycle (rotation + hullSixThreeThreeUpperOffset 0) ≠
        cycle (rotation + hullSixThreeThreeLowerOffset 1) :=
    R.cycle_injective.ne hU0L1Index
  have hYabsRaw : m ≤ |sig (cfg Q) (U 0) (L 1)| := by
    simpa [m, U, L] using
      minTri_le_abs_sig_of_pairwise_ne cfg hQU0 hQL1 hU0L1
  have hYabs : 1 ≤ |Y| := by
    simpa [Y] using hnormAbs hYabsRaw

  have hTCRaw : m ≤ sig (U 2) (L 0) (L 1) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p022_shiftedTriple_floor R (rotation + 2)
  have hTC : 1 ≤ TC := hnorm (by simpa [TC] using hTCRaw)

  have hAtransport :
      b * d * A = c * d * r1 + a * c * r2 + a * b * r3 := by
    dsimp [b, d, A, c, r1, a, r2, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hBid : B = r4 := by rfl
  have hCtransport :
      c * d * C = c * f * r2 + b * f * r3 + b * d * r4 := by
    dsimp [c, d, C, f, r2, b, r3, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hDid : D = r2 := by rfl
  have hEtransport :
      c * f * E = e * f * r3 + d * e * r4 + c * d * r5 := by
    dsimp [c, f, E, e, r3, d, r4, r5, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hYcoupling :
      a * E = d * F - e * (a + d - Y) := by
    dsimp [a, E, d, F, e, Y, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hYStrongA :
      d * A = c * (a + d - Y) + a * r3 := by
    dsimp [d, A, c, a, Y, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hTCtransport :
      c * TC = c * (C + D) - f * r3 - d * r4 := by
    dsimp [c, TC, C, D, f, r3, d, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring

  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hf0 : 0 ≤ f := le_trans zero_le_one hf

  have hAprod : c * d + a * c + a * b ≤ b * d * A := by
    rw [hAtransport]
    have h1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hc0 hd0)
    have h2 := mul_le_mul_of_nonneg_left hr2 (mul_nonneg ha0 hc0)
    have h3 := mul_le_mul_of_nonneg_left hr3 (mul_nonneg ha0 hb0)
    nlinarith
  have hBprod : 1 ≤ B := by simpa [hBid] using hr4
  have hCprod : c * f + b * f + b * d ≤ c * d * C := by
    rw [hCtransport]
    have h2 := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hc0 hf0)
    have h3 := mul_le_mul_of_nonneg_left hr3 (mul_nonneg hb0 hf0)
    have h4 := mul_le_mul_of_nonneg_left hr4 (mul_nonneg hb0 hd0)
    nlinarith
  have hDprod : 1 ≤ D := by simpa [hDid] using hr2
  have hEprod : e * f + d * e + c * d ≤ c * f * E := by
    rw [hEtransport]
    have h3 := mul_le_mul_of_nonneg_left hr3 (mul_nonneg he0 hf0)
    have h4 := mul_le_mul_of_nonneg_left hr4 (mul_nonneg hd0 he0)
    have h5 := mul_le_mul_of_nonneg_left hr5 (mul_nonneg hc0 hd0)
    nlinarith
  have hCDprod : c + f + d ≤ c * (C + D) := by
    have hcTC := mul_le_mul_of_nonneg_left hTC hc0
    have hfr3 := mul_le_mul_of_nonneg_left hr3 hf0
    have hdr4 := mul_le_mul_of_nonneg_left hr4 hd0
    rw [hTCtransport] at hcTC
    nlinarith

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

  have hscalar : (25 : ℝ) / 2 < H := by
    rw [hFan]
    by_cases hY0 : 0 ≤ Y
    · have hYpos : 1 ≤ Y := by
        rwa [abs_of_nonneg hY0] at hYabs
      have hdF := mul_le_mul_of_nonneg_left hFlower hd0
      have heY := mul_le_mul_of_nonneg_left hYpos he0
      have hEstrong : a * (d - e) + d + e ≤ a * E := by
        rw [hYcoupling]
        nlinarith
      exact hullSixThreeThreeP022YPos_scalar ha hb hc hd he hf
        hAprod hBprod hCprod hDprod hEstrong hFlower
    · have hYnonpos : Y ≤ 0 := le_of_not_ge hY0
      have hYneg : Y ≤ -1 := by
        rw [abs_of_nonpos hYnonpos] at hYabs
        linarith
      have hGap : a + d + 1 ≤ a + d - Y := by linarith
      have hcGap := mul_le_mul_of_nonneg_left hGap hc0
      have har3 := mul_le_mul_of_nonneg_left hr3 ha0
      have hAstrong : c * d + a * c + c + a ≤ d * A := by
        rw [hYStrongA]
        nlinarith
      exact hullSixThreeThreeP022YNeg_scalar ha hb hc hd he hf
        hAstrong hBprod hCDprod hEprod hFlower

  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- The single maximal-q remaining frontier with first cuts `022`. -/
def IsP022RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 0 ∧ T.p1 = 2 ∧ T.p2 = 2

theorem p022_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 2) (hp2 : T.p2 = 2) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : F.X 0 0 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX11 : minTri cfg ≤ F.X 1 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX22 : F.X 2 2 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp2]
  exact R.threeThreeP022At_false F.view F.rotation
    F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX11)
    (by simpa [X] using hX22)

end HullSixThreeThreeGeometricFrame

theorem hullSixThreeThreeP022XFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP022RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp1, hp2⟩
  exact F.p022_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
