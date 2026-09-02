import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeMergedPathXFrontierScalarAMGM

/-!
# The maximal-q `p = 112` and `p = 122` merged-path X-frontiers

These two adapters use only four retained `X` floors, one ordinary
`P`-boundary floor, the six line-height floors, and the positive `Q`-wrap
floor.  Exact determinant transport expands the six `P`-fan sectors in the
five adjacent rays of the corresponding merged slope order.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma p112p122_shiftedBoundary_floor
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

/-! ## The frontier `p = 112` -/

/-- The four retained cross floors of the `112` merged path contradict a
beating normalized `3 + 3` frame. -/
theorem threeThreeP112MergedAt_false
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
      -minTri cfg) :
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
  let r0 := sig (cfg P) (U 0) (L 0) / m
  let r1 := sig (cfg P) (U 0) (U 1) / m
  let r2 := (-sig (cfg P) (U 1) (L 1)) / m
  let r3 := sig (cfg P) (U 2) (L 1) / m
  let r4 := (-sig (cfg P) (U 2) (L 2)) / m
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

  have hr0 : 1 ≤ r0 := hnorm (by simpa [m, r0, U, L] using hX00)
  have hr1raw : m ≤ sig (cfg P) (U 0) (U 1) := by
    simpa [m, U, hullSixThreeThreeUpperOffset, add_assoc] using
      p112p122_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 0
  have hr1 : 1 ≤ r1 := hnorm (by simpa [r1] using hr1raw)
  have hr2 : 1 ≤ r2 := by
    apply hnorm
    dsimp [r2, U, L]
    linarith
  have hr3 : 1 ≤ r3 := hnorm (by simpa [m, r3, U, L] using hX21)
  have hr4 : 1 ≤ r4 := by
    apply hnorm
    dsimp [r4, U, L]
    linarith

  have hFqRaw : m ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p112p122_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hFq : 1 ≤ Fq := hnorm (by simpa [Fq] using hFqRaw)
  have hFbase : Fq = F - a - f := by
    dsimp [Fq, F, a, f, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFlower : a + f + 1 ≤ F := by linarith

  have hAid : A = r1 := by rfl
  have hBtransport : e * B = c * r2 + b * r3 := by
    dsimp [e, B, c, r2, b, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hCtransport :
      a * b * e * C =
        b * c * e * r0 + c * d * e * r1 +
          a * c * d * r2 + a * b * d * r3 := by
    dsimp [a, b, e, C, c, r0, d, r1, r2, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hDtransport :
      a * b * D = b * e * r0 + d * e * r1 + a * d * r2 := by
    dsimp [a, b, D, e, r0, d, r1, r2, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hEtransport : c * E = f * r3 + e * r4 := by
    dsimp [c, E, f, r3, e, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring

  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hf0 : 0 ≤ f := le_trans zero_le_one hf
  have hAprod : 1 ≤ A := by simpa [hAid] using hr1
  have hBprod : c + b ≤ e * B := by
    rw [hBtransport]
    have h2 := mul_le_mul_of_nonneg_left hr2 hc0
    have h3 := mul_le_mul_of_nonneg_left hr3 hb0
    nlinarith
  have hCprod :
      b * c * e + c * d * e + a * c * d + a * b * d ≤
        a * b * e * C := by
    rw [hCtransport]
    have h0 := mul_le_mul_of_nonneg_left hr0
      (mul_nonneg (mul_nonneg hb0 hc0) he0)
    have h1 := mul_le_mul_of_nonneg_left hr1
      (mul_nonneg (mul_nonneg hc0 hd0) he0)
    have h2 := mul_le_mul_of_nonneg_left hr2
      (mul_nonneg (mul_nonneg ha0 hc0) hd0)
    have h3 := mul_le_mul_of_nonneg_left hr3
      (mul_nonneg (mul_nonneg ha0 hb0) hd0)
    nlinarith
  have hDprod : b * e + d * e + a * d ≤ a * b * D := by
    rw [hDtransport]
    have h0 := mul_le_mul_of_nonneg_left hr0 (mul_nonneg hb0 he0)
    have h1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hd0 he0)
    have h2 := mul_le_mul_of_nonneg_left hr2 (mul_nonneg ha0 hd0)
    nlinarith
  have hEprod : f + e ≤ c * E := by
    rw [hEtransport]
    have h3 := mul_le_mul_of_nonneg_left hr3 hf0
    have h4 := mul_le_mul_of_nonneg_left hr4 he0
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
    exact hullSixThreeThreeP112Merged_scalar ha hb hc hd he hf
      hAprod hBprod hCprod hDprod hEprod hFlower
  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

/-! ## The frontier `p = 122` -/

/-- The four retained cross floors of the `122` merged path contradict a
beating normalized `3 + 3` frame. -/
theorem threeThreeP122MergedAt_false
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
    (hX01 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
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
  let r0 := sig (cfg P) (U 0) (L 0) / m
  let r1 := (-sig (cfg P) (U 0) (L 1)) / m
  let r2 := sig (cfg P) (U 1) (L 1) / m
  let r3 := sig (cfg P) (U 1) (U 2) / m
  let r4 := (-sig (cfg P) (U 2) (L 2)) / m
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

  have hr0 : 1 ≤ r0 := hnorm (by simpa [m, r0, U, L] using hX00)
  have hr1 : 1 ≤ r1 := by
    apply hnorm
    dsimp [r1, U, L]
    linarith
  have hr2 : 1 ≤ r2 := hnorm (by simpa [m, r2, U, L] using hX11)
  have hr3raw : m ≤ sig (cfg P) (U 1) (U 2) := by
    simpa [m, U, hullSixThreeThreeUpperOffset, add_assoc] using
      p112p122_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 1
  have hr3 : 1 ≤ r3 := hnorm (by simpa [r3] using hr3raw)
  have hr4 : 1 ≤ r4 := by
    apply hnorm
    dsimp [r4, U, L]
    linarith

  have hFqRaw : m ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p112p122_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hFq : 1 ≤ Fq := hnorm (by simpa [Fq] using hFqRaw)
  have hFbase : Fq = F - a - f := by
    dsimp [Fq, F, a, f, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFlower : a + f + 1 ≤ F := by linarith

  have hAtransport : e * A = b * r1 + a * r2 := by
    dsimp [e, A, b, r1, a, r2, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hBid : B = r3 := by rfl
  have hCtransport :
      a * b * e * C =
        b * c * e * r0 + b * c * d * r1 +
          a * c * d * r2 + a * d * e * r3 := by
    dsimp [a, b, e, C, c, r0, d, r1, r2, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hDtransport : a * D = e * r0 + d * r1 := by
    dsimp [a, D, e, r0, d, r1, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hEtransport :
      b * c * E = c * f * r2 + e * f * r3 + b * e * r4 := by
    dsimp [b, c, E, f, r2, e, r3, r4, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring

  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hf0 : 0 ≤ f := le_trans zero_le_one hf
  have hAprod : b + a ≤ e * A := by
    rw [hAtransport]
    have h1 := mul_le_mul_of_nonneg_left hr1 hb0
    have h2 := mul_le_mul_of_nonneg_left hr2 ha0
    nlinarith
  have hBprod : 1 ≤ B := by simpa [hBid] using hr3
  have hCprod :
      b * c * e + b * c * d + a * c * d + a * d * e ≤
        a * b * e * C := by
    rw [hCtransport]
    have h0 := mul_le_mul_of_nonneg_left hr0
      (mul_nonneg (mul_nonneg hb0 hc0) he0)
    have h1 := mul_le_mul_of_nonneg_left hr1
      (mul_nonneg (mul_nonneg hb0 hc0) hd0)
    have h2 := mul_le_mul_of_nonneg_left hr2
      (mul_nonneg (mul_nonneg ha0 hc0) hd0)
    have h3 := mul_le_mul_of_nonneg_left hr3
      (mul_nonneg (mul_nonneg ha0 hd0) he0)
    nlinarith
  have hDprod : e + d ≤ a * D := by
    rw [hDtransport]
    have h0 := mul_le_mul_of_nonneg_left hr0 he0
    have h1 := mul_le_mul_of_nonneg_left hr1 hd0
    nlinarith
  have hEprod : c * f + e * f + b * e ≤ b * c * E := by
    rw [hEtransport]
    have h2 := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hc0 hf0)
    have h3 := mul_le_mul_of_nonneg_left hr3 (mul_nonneg he0 hf0)
    have h4 := mul_le_mul_of_nonneg_left hr4 (mul_nonneg hb0 he0)
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
    exact hullSixThreeThreeP122Merged_scalar ha hb hc hd he hf
      hAprod hBprod hCprod hDprod hEprod hFlower
  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

def IsP112RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 1 ∧ T.p1 = 1 ∧ T.p2 = 2

def IsP122RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 1 ∧ T.p1 = 2 ∧ T.p2 = 2

theorem p112_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 1) (hp1 : T.p1 = 1) (hp2 : T.p2 = 2) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : minTri cfg ≤ F.X 0 0 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX11 : F.X 1 1 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX21 : minTri cfg ≤ F.X 2 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp2]
  have hX22 : F.X 2 2 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp2]
  exact R.threeThreeP112MergedAt_false F.view F.rotation
    F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX11)
    (by simpa [X] using hX21) (by simpa [X] using hX22)

theorem p122_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 1) (hp1 : T.p1 = 2) (hp2 : T.p2 = 2) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : minTri cfg ≤ F.X 0 0 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX01 : F.X 0 1 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX11 : minTri cfg ≤ F.X 1 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX22 : F.X 2 2 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp2]
  exact R.threeThreeP122MergedAt_false F.view F.rotation
    F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX01)
    (by simpa [X] using hX11) (by simpa [X] using hX22)

def IsP112P122RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  IsP112RemainingFrontier T ∨ IsP122RemainingFrontier T

end HullSixThreeThreeGeometricFrame

theorem hullSixThreeThreeP112P122MergedXFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP112P122RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with h112 | h122
  · rcases h112 with ⟨hRemaining, hp0, hp1, hp2⟩
    exact F.p112_xFrontierClosed T hp0 hp1 hp2
  · rcases h122 with ⟨hRemaining, hp0, hp1, hp2⟩
    exact F.p122_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
