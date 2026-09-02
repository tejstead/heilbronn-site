import Heilbronn8.Survivors.Join.HullSixThreeThreeP222XFrontierScalarAMGM
import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge

/-!
# Exact recurrence provider for the `p = 222` partial-X frontier

This module isolates the determinant algebra needed by the geometric
adapter.  The three cross-cell recurrences produce the middle-sector lower
bound; the wrap recurrence and the positive `Q`-fan floor produce the final
sector lower bound.  The resulting packet is discharged by the source-only
AM--GM theorem in `HullSixThreeThreeP222XFrontierScalarAMGM`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Heilbronn8

private lemma p222_shiftedBoundary_floor
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

private lemma p222_shiftedTriple_pos
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

private lemma p222_shiftedTriple_floor
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
    (p222_shiftedTriple_pos R start)

/--
Abstract provider from the exact `p = 222` determinant recurrences.

In the geometric application `x,y,z` are the three positive line heights,
`p,q,r` the three negative line-height magnitudes, `a,b,g,C,l,m` the six
successive `P`-fan sectors, and `c,d,e` the first three retained cross-cell
magnitudes.
-/
theorem hullSixThreeThreeP222XFrontier_fromRecurrences
    {x y z p q r a b g C l m c d e : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hg1 : 1 ≤ g)
    (hC : 1 ≤ C) (hl1 : 1 ≤ l) (hm1 : 1 ≤ m)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hB0 : 1 ≤ a + x - y)
    (hB5 : 1 ≤ m - x - r)
    (hE0 : y ≤ a * (y - z) + b * (y - x))
    (hE1 : z ≤ b * (z + p) + g * (z - y))
    (hxd : x * d = y * c + q * a)
    (hye : y * e = z * d + q * b)
    (hqg : q * g = p * e + z * C)
    (hqm : q * m = x * l - r * c) :
    (25 : ℝ) / 2 < a + b + g + C + l + m := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc

  have hdIdentity : d = (y * c + q * a) / x := by
    apply (eq_div_iff hx0.ne').2
    simpa [mul_comm] using hxd
  have heIdentity :
      e = z * c / x + q * z * a / (x * y) + q * b / y := by
    calc
      e = (z * d + q * b) / y := by
        apply (eq_div_iff hy0.ne').2
        simpa [mul_comm] using hye
      _ = z * c / x + q * z * a / (x * y) + q * b / y := by
        rw [hdIdentity]
        field_simp [hx0.ne', hy0.ne']
        <;> ring
  have hzc : z / x ≤ z * c / x := by
    have hscale : z ≤ z * c := by
      have hz0 : 0 ≤ z := le_trans zero_le_one hz
      have hmul := mul_nonneg (sub_nonneg.mpr hc) hz0
      nlinarith
    exact (div_le_div_iff_of_pos_right hx0).2 hscale
  have heLower :
      z / x + q * z * a / (x * y) + q * b / y ≤ e := by
    rw [heIdentity]
    linarith
  have hpELower :
      p * (z / x + q * z * a / (x * y) + q * b / y) ≤ p * e :=
    mul_le_mul_of_nonneg_left heLower (le_of_lt hp0)
  have hqgIdentity : g = (p * e + z * C) / q := by
    apply (eq_div_iff hq0.ne').2
    simpa [mul_comm] using hqg
  have hgBound :
      p * z / (q * x) + p * z * a / (x * y) + p * b / y +
        z * C / q ≤ g := by
    rw [hqgIdentity]
    apply (le_div_iff₀ hq0).2
    calc
      (p * z / (q * x) + p * z * a / (x * y) + p * b / y +
          z * C / q) * q =
          p * (z / x + q * z * a / (x * y) + q * b / y) + z * C := by
        field_simp [hx0.ne', hy0.ne', hq0.ne']
        <;> ring
      _ ≤ p * e + z * C := add_le_add hpELower le_rfl

  have hmBound : 1 + x + r ≤ m := by linarith
  have hqmLower : q * (1 + x + r) ≤ q * m :=
    mul_le_mul_of_nonneg_left hmBound (le_of_lt hq0)
  have hrc : r ≤ r * c := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc) (le_of_lt hr0)
    nlinarith
  have hxlIdentity : x * l = q * m + r * c := by linarith
  have hxlLower : q * x + q + q * r + r ≤ x * l := by
    rw [hxlIdentity]
    nlinarith
  have hlBound : q + (q + r + q * r) / x ≤ l := by
    calc
      q + (q + r + q * r) / x =
          (q * x + q + q * r + r) / x := by
        field_simp [hx0.ne']
        <;> ring
      _ ≤ l := by
        apply (div_le_iff₀ hx0).2
        simpa [mul_comm] using hxlLower

  exact hullSixThreeThreeP222PartialX_scalar
    hx hy hz hp hq hr ha hb hg1 hC hl1 hm1
    hB0 hE0 hE1 hgBound hlBound hmBound

namespace HullSixCompactCrossChordResidual

/-- The three retained column-one cross floors close the `p = 222` packet. -/
theorem threeThreeP222At_false
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
    (hX01 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hX11 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hX21 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1)))) :
    False := by
  let s := minTri cfg
  let U : Fin 3 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let x := sig (cfg P) (cfg Q) (U 0) / s
  let y := sig (cfg P) (cfg Q) (U 1) / s
  let z := sig (cfg P) (cfg Q) (U 2) / s
  let p0 := (-sig (cfg P) (cfg Q) (L 0)) / s
  let q0 := (-sig (cfg P) (cfg Q) (L 1)) / s
  let r := (-sig (cfg P) (cfg Q) (L 2)) / s
  let c := sig (cfg P) (U 0) (L 1) / s
  let d := sig (cfg P) (U 1) (L 1) / s
  let e := sig (cfg P) (U 2) (L 1) / s
  let a := sig (cfg P) (U 0) (U 1) / s
  let b := sig (cfg P) (U 1) (U 2) / s
  let g := sig (cfg P) (U 2) (L 0) / s
  let C := sig (cfg P) (L 0) (L 1) / s
  let l := sig (cfg P) (L 1) (L 2) / s
  let M := sig (cfg P) (L 2) (U 0) / s
  let aq := sig (cfg Q) (U 0) (U 1) / s
  let Mq := sig (cfg Q) (L 2) (U 0) / s
  let T0 := sig (U 0) (U 1) (U 2) / s
  let T1 := sig (U 1) (U 2) (L 0) / s
  let H := doubledHullArea cfg / s

  have hs : 0 < s := by simpa [s] using R.minTri_pos
  have hsNe : s ≠ 0 := ne_of_gt hs
  have hnorm {w : ℝ} (hw : s ≤ w) : 1 ≤ w / s := by
    exact (le_div_iff₀ hs).2 (by simpa using hw)

  have hx : 1 ≤ x := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [s, x, U] using h)
  have hy : 1 ≤ y := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [s, y, U] using h)
  have hz : 1 ≤ z := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at h
    exact hnorm (by simpa [s, z, U] using h)
  have hp0 : 1 ≤ p0 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    exact hnorm (by simpa [s, p0, L] using h)
  have hq0 : 1 ≤ q0 := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    exact hnorm (by simpa [s, q0, L] using h)
  have hr : 1 ≤ r := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [s, r, L] using h)

  have hc : 1 ≤ c := hnorm (by simpa [s, c, U, L] using hX01)
  have hd : 1 ≤ d := hnorm (by simpa [s, d, U, L] using hX11)
  have he : 1 ≤ e := hnorm (by simpa [s, e, U, L] using hX21)

  have haRaw : s ≤ sig (cfg P) (U 0) (U 1) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p222_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 0
  have ha : 1 ≤ a := hnorm (by simpa [a] using haRaw)
  have hbRaw : s ≤ sig (cfg P) (U 1) (U 2) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p222_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 1
  have hb : 1 ≤ b := hnorm (by simpa [b] using hbRaw)
  have hgRaw : s ≤ sig (cfg P) (U 2) (L 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using
      p222_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 2
  have hg : 1 ≤ g := hnorm (by simpa [g] using hgRaw)
  have hCRaw : s ≤ sig (cfg P) (L 0) (L 1) := by
    simpa [s, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p222_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 3
  have hC : 1 ≤ C := hnorm (by simpa [C] using hCRaw)
  have hlRaw : s ≤ sig (cfg P) (L 1) (L 2) := by
    simpa [s, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p222_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 4
  have hl : 1 ≤ l := hnorm (by simpa [l] using hlRaw)
  have hMRaw : s ≤ sig (cfg P) (L 2) (U 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p222_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 5
  have hM : 1 ≤ M := hnorm (by simpa [M] using hMRaw)

  have haqRaw : s ≤ sig (cfg Q) (U 0) (U 1) := by
    simpa [s, U, hullSixThreeThreeUpperOffset] using
      p222_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 0
  have haq : 1 ≤ aq := hnorm (by simpa [aq] using haqRaw)
  have hMqRaw : s ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p222_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hMq : 1 ≤ Mq := hnorm (by simpa [Mq] using hMqRaw)

  have hT0Raw : s ≤ sig (U 0) (U 1) (U 2) := by
    simpa [s, U, hullSixThreeThreeUpperOffset, add_assoc] using
      p222_shiftedTriple_floor R rotation
  have hT0 : 1 ≤ T0 := hnorm (by simpa [T0] using hT0Raw)
  have hT1Raw : s ≤ sig (U 1) (U 2) (L 0) := by
    simpa [s, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p222_shiftedTriple_floor R (rotation + 1)
  have hT1 : 1 ≤ T1 := hnorm (by simpa [T1] using hT1Raw)

  have haqIdentity : aq = a + x - y := by
    dsimp [aq, a, x, y, U]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hB0 : 1 ≤ a + x - y := by simpa [haqIdentity] using haq
  have hMqIdentity : Mq = M - x - r := by
    dsimp [Mq, M, x, r, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hB5 : 1 ≤ M - x - r := by simpa [hMqIdentity] using hMq

  have hxd : x * d = y * c + q0 * a := by
    dsimp [x, d, y, c, q0, a, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hye : y * e = z * d + q0 * b := by
    dsimp [y, e, z, d, q0, b, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hqg : q0 * g = p0 * e + z * C := by
    dsimp [q0, g, p0, e, z, C, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hqM : q0 * M = x * l - r * c := by
    dsimp [q0, M, x, l, r, c, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring

  have hEar0Identity : y * T0 = a * (y - z) + b * (y - x) := by
    dsimp [y, T0, a, z, b, x, U]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hEar0 : y ≤ a * (y - z) + b * (y - x) := by
    rw [← hEar0Identity]
    have := mul_le_mul_of_nonneg_left hT0 (le_trans zero_le_one hy)
    nlinarith
  have hEar1Identity : z * T1 = b * (z + p0) + g * (z - y) := by
    dsimp [z, T1, b, p0, g, y, U, L]
    field_simp [hsNe] <;> simp only [sig] <;> ring
  have hEar1 : z ≤ b * (z + p0) + g * (z - y) := by
    rw [← hEar1Identity]
    have := mul_le_mul_of_nonneg_left hT1 (le_trans zero_le_one hz)
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
  have hFan : H = a + b + g + C + l + M := by
    dsimp [H, a, b, g, C, l, M]
    rw [hSumRaw]
    ring

  have hscalar : 25 / 2 < H := by
    rw [hFan]
    exact hullSixThreeThreeP222XFrontier_fromRecurrences
      hx hy hz hp0 hq0 hr ha hb hg hC hl hM hc hd he
      hB0 hB5 hEar0 hEar1 hxd hye hqg hqM
  have hmul : ((25 : ℝ) / 2) * s < doubledHullArea cfg :=
    (lt_div_iff₀ hs).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < s := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- The single maximal-q remaining frontier with first cuts `222`. -/
def IsP222RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 2 ∧ T.p1 = 2 ∧ T.p2 = 2

/-- The `222` X-frontier is closed in its original frame. -/
theorem p222_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 2) (hp1 : T.p1 = 2) (hp2 : T.p2 = 2) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX01 : minTri cfg ≤ F.X 0 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX11 : minTri cfg ≤ F.X 1 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX21 : minTri cfg ≤ F.X 2 1 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp2]
  exact R.threeThreeP222At_false F.view F.rotation F.upper_pos F.lower_neg
    (by simpa [X] using hX01) (by simpa [X] using hX11)
    (by simpa [X] using hX21)

end HullSixThreeThreeGeometricFrame

/-- Provider for the `p = 222` maximal-q X-frontier fibre. -/
theorem hullSixThreeThreeP222XFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP222RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp1, hp2⟩
  exact F.p222_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
