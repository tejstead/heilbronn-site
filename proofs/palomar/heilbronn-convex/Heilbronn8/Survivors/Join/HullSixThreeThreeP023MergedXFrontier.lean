import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeMergedPathXFrontierScalarAMGM

/-!
# The maximal-q `p = 023` merged-path X-frontier

Only the retained `X` signs are used.  The slope order is

```text
U0, L0, L1, U1, L2, U2.
```

The five adjacent floors are `-X00`, the `P`-boundary edge `L0L1`, `X11`,
`-X12`, and `X22`.  Exact determinant transport expands every `P`-fan
sector in these five floors and feeds the source-only scalar certificate.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma p023Merged_shiftedBoundary_floor
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

namespace HullSixCompactCrossChordResidual

/-- The four retained cross floors of the `023` merged path contradict a
beating normalized `3 + 3` frame. -/
theorem threeThreeP023MergedAt_false
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
    (hX12 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) ≤
      -minTri cfg)
    (hX22 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let m := minTri cfg
  let U : Fin 3 → ℝ × ℝ := fun i =>
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 → ℝ × ℝ := fun j =>
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let a := sig (cfg P) (cfg Q) (U 0) / m
  let b := sig (cfg P) (cfg Q) (U 1) / m
  let c := sig (cfg P) (cfg Q) (U 2) / m
  let d := (-sig (cfg P) (cfg Q) (L 0)) / m
  let e := (-sig (cfg P) (cfg Q) (L 1)) / m
  let f := (-sig (cfg P) (cfg Q) (L 2)) / m
  let r0 := (-sig (cfg P) (U 0) (L 0)) / m
  let r1 := sig (cfg P) (L 0) (L 1) / m
  let r2 := sig (cfg P) (U 1) (L 1) / m
  let r3 := (-sig (cfg P) (U 1) (L 2)) / m
  let r4 := sig (cfg P) (U 2) (L 2) / m
  let A := sig (cfg P) (U 0) (U 1) / m
  let B := sig (cfg P) (U 1) (U 2) / m
  let C := sig (cfg P) (U 2) (L 0) / m
  let D := sig (cfg P) (L 0) (L 1) / m
  let E := sig (cfg P) (L 1) (L 2) / m
  let F := sig (cfg P) (L 2) (U 0) / m
  let Fq := sig (cfg Q) (L 2) (U 0) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {x : ℝ} (hx : m ≤ x) : 1 ≤ x / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hx)

  have ha : 1 ≤ a := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, a, U] using h)
  have hb : 1 ≤ b := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, b, U] using h)
  have hc : 1 ≤ c := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at h
    exact hnorm (by simpa [m, c, U] using h)
  have hd : 1 ≤ d := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    exact hnorm (by simpa [m, d, L] using h)
  have he : 1 ≤ e := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    exact hnorm (by simpa [m, e, L] using h)
  have hf : 1 ≤ f := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [m, f, L] using h)

  have hr0 : 1 ≤ r0 := by
    apply hnorm
    dsimp [r0, U, L]
    linarith
  have hr1raw : m ≤ sig (cfg P) (L 0) (L 1) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p023Merged_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 3
  have hr1 : 1 ≤ r1 := hnorm (by simpa [r1] using hr1raw)
  have hr2 : 1 ≤ r2 := hnorm (by simpa [m, r2, U, L] using hX11)
  have hr3 : 1 ≤ r3 := by
    apply hnorm
    dsimp [r3, U, L]
    linarith
  have hr4 : 1 ≤ r4 := hnorm (by simpa [m, r4, U, L] using hX22)

  have hFqRaw : m ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p023Merged_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hFq : 1 ≤ Fq := hnorm (by simpa [Fq] using hFqRaw)
  have hFbase : Fq = F - a - f := by
    dsimp [Fq, F, a, f, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFlower : a + f + 1 ≤ F := by linarith

  have hAtransport :
      d * e * A = b * e * r0 + a * b * r1 + a * d * r2 := by
    dsimp [d, e, A, b, r0, a, r1, r2, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hBtransport : f * B = c * r3 + b * r4 := by
    dsimp [f, B, c, r3, b, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hCtransport :
      b * e * f * C =
        b * c * f * r1 + c * d * f * r2 +
          c * d * e * r3 + b * d * e * r4 := by
    dsimp [b, e, f, C, c, r1, d, r2, r3, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hDid : D = r1 := by rfl
  have hEtransport : b * E = f * r2 + e * r3 := by
    dsimp [b, E, f, r2, e, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring

  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hf0 : 0 ≤ f := le_trans zero_le_one hf
  have hAprod : b * e + a * b + a * d ≤ d * e * A := by
    rw [hAtransport]
    have h0 := mul_le_mul_of_nonneg_left hr0 (mul_nonneg hb0 he0)
    have h1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg ha0 hb0)
    have h2 := mul_le_mul_of_nonneg_left hr2 (mul_nonneg ha0 hd0)
    nlinarith
  have hBprod : c + b ≤ f * B := by
    rw [hBtransport]
    have h3 := mul_le_mul_of_nonneg_left hr3 hc0
    have h4 := mul_le_mul_of_nonneg_left hr4 hb0
    nlinarith
  have hCprod :
      b * c * f + c * d * f + c * d * e + b * d * e ≤
        b * e * f * C := by
    rw [hCtransport]
    have h1 := mul_le_mul_of_nonneg_left hr1
      (mul_nonneg (mul_nonneg hb0 hc0) hf0)
    have h2 := mul_le_mul_of_nonneg_left hr2
      (mul_nonneg (mul_nonneg hc0 hd0) hf0)
    have h3 := mul_le_mul_of_nonneg_left hr3
      (mul_nonneg (mul_nonneg hc0 hd0) he0)
    have h4 := mul_le_mul_of_nonneg_left hr4
      (mul_nonneg (mul_nonneg hb0 hd0) he0)
    nlinarith
  have hDprod : 1 ≤ D := by simpa [hDid] using hr1
  have hEprod : f + e ≤ b * E := by
    rw [hEtransport]
    have h2 := mul_le_mul_of_nonneg_left hr2 hf0
    have h3 := mul_le_mul_of_nonneg_left hr3 he0
    nlinarith

  let fan : Fin 6 → ℝ := fun i =>
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
  have hFan : H = A + B + C + D + E + F := by
    dsimp [H, A, B, C, D, E, F]
    rw [hSumRaw]
    ring

  have hscalar : 25 / 2 < H := by
    rw [hFan]
    exact hullSixThreeThreeP023Merged_scalar ha hb hc hd he hf
      hAprod hBprod hCprod hDprod hEprod hFlower
  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- The single maximal-q remaining frontier with first cuts `023`. -/
def IsP023RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 0 ∧ T.p1 = 2 ∧ T.p2 = 3

theorem p023_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 2) (hp2 : T.p2 = 3) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : F.X 0 0 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX11 : minTri cfg ≤ F.X 1 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX12 : F.X 1 2 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX22 : minTri cfg ≤ F.X 2 2 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp2]
  exact R.threeThreeP023MergedAt_false F.view F.rotation
    F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX11)
    (by simpa [X] using hX12) (by simpa [X] using hX22)

end HullSixThreeThreeGeometricFrame

theorem hullSixThreeThreeP023MergedXFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP023RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp1, hp2⟩
  exact F.p023_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
