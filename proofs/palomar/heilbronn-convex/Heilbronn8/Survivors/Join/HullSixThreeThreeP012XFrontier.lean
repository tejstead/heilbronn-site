import Heilbronn8.Survivors.Join.HullSixThreeThreeP012XFrontierScalar
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# The maximal-q `p = 012` X-frontier

Around `P`, the six rays have merged slope order

```text
U0, L0, U1, L1, U2, L2.
```

The five adjacent cross determinants provide the five gap floors.  The
maximal-q strengthened cell `X02 ≤ -3 * minTri` supplies the wrap lower
bound.  No `Y` sign, `Q` determinant, or nonboundary hull-triple floor is
used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Heilbronn8

namespace HullSixCompactCrossChordResidual

/-- The `p = 012`, `q = 233` adjacent-X floors and strengthened wrap
contradict a beating normalized `3 + 3` frame. -/
theorem threeThreeP012At_false
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
    (hX10 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX11 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
      -minTri cfg)
    (hX21 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hX22 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) ≤
      -minTri cfg)
    (hX02 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) ≤
      -3 * minTri cfg) :
    False := by
  let m := minTri cfg
  let U : Fin 3 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))

  let a := sig (cfg P) (cfg Q) (U 0) / m
  let b := sig (cfg P) (cfg Q) (U 1) / m
  let c := sig (cfg P) (cfg Q) (U 2) / m
  let d := (-sig (cfg P) (cfg Q) (L 0)) / m
  let e := (-sig (cfg P) (cfg Q) (L 1)) / m
  let f := (-sig (cfg P) (cfg Q) (L 2)) / m

  let r1 := (-sig (cfg P) (U 0) (L 0)) / m
  let r2 := sig (cfg P) (U 1) (L 0) / m
  let r3 := (-sig (cfg P) (U 1) (L 1)) / m
  let r4 := sig (cfg P) (U 2) (L 1) / m
  let r5 := (-sig (cfg P) (U 2) (L 2)) / m

  let g1 := r1 / (a * d)
  let g2 := r2 / (b * d)
  let g3 := r3 / (b * e)
  let g4 := r4 / (c * e)
  let g5 := r5 / (c * f)

  let A := sig (cfg P) (U 0) (U 1) / m
  let B := sig (cfg P) (U 1) (U 2) / m
  let C := sig (cfg P) (U 2) (L 0) / m
  let D := sig (cfg P) (L 0) (L 1) / m
  let E := sig (cfg P) (L 1) (L 2) / m
  let F := sig (cfg P) (L 2) (U 0) / m
  let G := sig (cfg P) (U 0) (U 2) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by
    simpa [m] using R.minTri_pos
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

  have hr1 : 1 ≤ r1 := by
    apply hnorm
    dsimp [r1, U, L]
    linarith
  have hr2 : 1 ≤ r2 :=
    hnorm (by simpa [m, r2, U, L] using hX10)
  have hr3 : 1 ≤ r3 := by
    apply hnorm
    dsimp [r3, U, L]
    linarith
  have hr4 : 1 ≤ r4 :=
    hnorm (by simpa [m, r4, U, L] using hX21)
  have hr5 : 1 ≤ r5 := by
    apply hnorm
    dsimp [r5, U, L]
    linarith

  have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hbPos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hcPos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hdPos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hePos : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hfPos : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have hr1Pos : 0 < r1 := lt_of_lt_of_le zero_lt_one hr1
  have hr2Pos : 0 < r2 := lt_of_lt_of_le zero_lt_one hr2
  have hr3Pos : 0 < r3 := lt_of_lt_of_le zero_lt_one hr3
  have hr4Pos : 0 < r4 := lt_of_lt_of_le zero_lt_one hr4
  have hr5Pos : 0 < r5 := lt_of_lt_of_le zero_lt_one hr5

  have hg1 : 0 < g1 := by
    change 0 < r1 / (a * d)
    exact div_pos hr1Pos (mul_pos haPos hdPos)
  have hg2 : 0 < g2 := by
    change 0 < r2 / (b * d)
    exact div_pos hr2Pos (mul_pos hbPos hdPos)
  have hg3 : 0 < g3 := by
    change 0 < r3 / (b * e)
    exact div_pos hr3Pos (mul_pos hbPos hePos)
  have hg4 : 0 < g4 := by
    change 0 < r4 / (c * e)
    exact div_pos hr4Pos (mul_pos hcPos hePos)
  have hg5 : 0 < g5 := by
    change 0 < r5 / (c * f)
    exact div_pos hr5Pos (mul_pos hcPos hfPos)

  have hgap1 : a * d * g1 = r1 := by
    change a * d * (r1 / (a * d)) = r1
    field_simp [haPos.ne', hdPos.ne'] <;> ring
  have hgap2 : b * d * g2 = r2 := by
    change b * d * (r2 / (b * d)) = r2
    field_simp [hbPos.ne', hdPos.ne'] <;> ring
  have hgap3 : b * e * g3 = r3 := by
    change b * e * (r3 / (b * e)) = r3
    field_simp [hbPos.ne', hePos.ne'] <;> ring
  have hgap4 : c * e * g4 = r4 := by
    change c * e * (r4 / (c * e)) = r4
    field_simp [hcPos.ne', hePos.ne'] <;> ring
  have hgap5 : c * f * g5 = r5 := by
    change c * f * (r5 / (c * f)) = r5
    field_simp [hcPos.ne', hfPos.ne'] <;> ring

  have hfloor1 : 1 ≤ a * d * g1 := by linarith
  have hfloor2 : 1 ≤ b * d * g2 := by linarith
  have hfloor3 : 1 ≤ b * e * g3 := by linarith
  have hfloor4 : 1 ≤ c * e * g4 := by linarith
  have hfloor5 : 1 ≤ c * f * g5 := by linarith

  have hAraw : d * A = b * r1 + a * r2 := by
    dsimp [d, A, b, r1, a, r2, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hBraw : e * B = c * r3 + b * r4 := by
    dsimp [e, B, c, r3, b, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hCraw :
      b * e * C = c * e * r2 + c * d * r3 + b * d * r4 := by
    dsimp [b, e, C, c, r2, d, r3, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hDraw : b * D = e * r2 + d * r3 := by
    dsimp [b, D, e, r2, d, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hEraw : c * E = f * r4 + e * r5 := by
    dsimp [c, E, f, r4, e, r5, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hGraw : d * G = c * r1 + a * C := by
    dsimp [d, G, c, r1, a, C, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFraw : c * F = f * G + a * r5 := by
    dsimp [c, F, f, G, a, r5, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring

  have hAtransport : A = a * b * (g1 + g2) := by
    calc
      A = (b * r1 + a * r2) / d := by
        apply (eq_div_iff hdPos.ne').2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hAraw
      _ = a * b * (g1 + g2) := by
        rw [← hgap1, ← hgap2]
        field_simp [hdPos.ne'] <;> ring
  have hBtransport : B = b * c * (g3 + g4) := by
    calc
      B = (c * r3 + b * r4) / e := by
        apply (eq_div_iff hePos.ne').2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hBraw
      _ = b * c * (g3 + g4) := by
        rw [← hgap3, ← hgap4]
        field_simp [hePos.ne'] <;> ring
  have hCtransport : C = c * d * (g2 + g3 + g4) := by
    calc
      C = (c * e * r2 + c * d * r3 + b * d * r4) / (b * e) := by
        apply (eq_div_iff (mul_ne_zero hbPos.ne' hePos.ne')).2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hCraw
      _ = c * d * (g2 + g3 + g4) := by
        rw [← hgap2, ← hgap3, ← hgap4]
        field_simp [hbPos.ne', hePos.ne'] <;> ring
  have hDtransport : D = d * e * (g2 + g3) := by
    calc
      D = (e * r2 + d * r3) / b := by
        apply (eq_div_iff hbPos.ne').2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hDraw
      _ = d * e * (g2 + g3) := by
        rw [← hgap2, ← hgap3]
        field_simp [hbPos.ne'] <;> ring
  have hEtransport : E = e * f * (g4 + g5) := by
    calc
      E = (f * r4 + e * r5) / c := by
        apply (eq_div_iff hcPos.ne').2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hEraw
      _ = e * f * (g4 + g5) := by
        rw [← hgap4, ← hgap5]
        field_simp [hcPos.ne'] <;> ring
  have hGtransport : G = a * c * (g1 + g2 + g3 + g4) := by
    calc
      G = (c * r1 + a * C) / d := by
        apply (eq_div_iff hdPos.ne').2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hGraw
      _ = a * c * (g1 + g2 + g3 + g4) := by
        rw [hCtransport, ← hgap1]
        field_simp [hdPos.ne'] <;> ring
  have hFtransport :
      F = a * f * (g1 + g2 + g3 + g4 + g5) := by
    calc
      F = (f * G + a * r5) / c := by
        apply (eq_div_iff hcPos.ne').2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hFraw
      _ = a * f * (g1 + g2 + g3 + g4 + g5) := by
        rw [hGtransport, ← hgap5]
        field_simp [hcPos.ne'] <;> ring

  have hFstrong : 3 ≤ F := by
    change 3 ≤ sig (cfg P) (L 2) (U 0) / m
    apply (le_div_iff₀ hm).2
    have hswap :
        sig (cfg P) (L 2) (U 0) = -sig (cfg P) (U 0) (L 2) := by
      simp only [sig]
      ring
    rw [hswap]
    dsimp [U, L] at hX02 ⊢
    linarith
  have hwrap : 3 ≤ a * f * (g1 + g2 + g3 + g4 + g5) := by
    rw [← hFtransport]
    exact hFstrong

  let fan : Fin 6 → ℝ := fun i ↦
    sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i ↦ sig (cfg P) (cfg (cycle (rotation + i)))
        (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun :
        (fun i ↦ sig (cfg P) (cfg (cycle (rotation + i)))
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
    hullSixThreeThree_p012_scalar
      ha hb hc hd he hf hg1 hg2 hg3 hg4 hg5
      hfloor1 hfloor2 hfloor3 hfloor4 hfloor5
      (le_of_eq hAtransport.symm) (le_of_eq hBtransport.symm)
      (le_of_eq hCtransport.symm) (le_of_eq hDtransport.symm)
      (le_of_eq hEtransport.symm) (le_of_eq hFtransport.symm)
      hwrap (le_of_eq hFan.symm)
  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- The single maximal-q remaining frontier with first cuts `012`. -/
def IsP012RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 0 ∧ T.p1 = 1 ∧ T.p2 = 2

/-- The `012` X-frontier is closed in its original frame. -/
theorem p012_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 1) (hp2 : T.p2 = 2)
    (hq0 : T.q0 = 2) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : F.X 0 0 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX10 : minTri cfg ≤ F.X 1 0 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX11 : F.X 1 1 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX21 : minTri cfg ≤ F.X 2 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp2]
  have hX22 : F.X 2 2 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp2]
  have hX02 : F.X 0 2 ≤ -3 * minTri cfg := by
    apply hStrong
    simp [HullSixThreeThreeCuts.q, hq0]
  exact R.threeThreeP012At_false F.view F.rotation
    F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX10)
    (by simpa [X] using hX11) (by simpa [X] using hX21)
    (by simpa [X] using hX22) (by simpa [X] using hX02)

end HullSixThreeThreeGeometricFrame

/-- Provider for the `p = 012`, `q = 233` X-frontier fibre. -/
theorem hullSixThreeThreeP012XFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP012RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp1, hp2⟩
  exact F.p012_xFrontierClosed T hp0 hp1 hp2 hRemaining.1.1

end Heilbronn8
