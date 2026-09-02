import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenChordSelector

/-!
# Point-geometry adapter for the population-100 C24 hull-seven chamber

This file is the geometric front end of `HullSevenChordInput`.  Its input is
an actual configuration, a counterclockwise seven-cycle, the unique off-cycle
point, and precisely the signed determinants selected by the retained C24
router.  None of the scalar recurrences is postulated:

* all fifteen unit floors come from `minTri`;
* the three ear bounds come from consecutive hull triangles;
* the two endpoint bounds come from Pluecker rows and hull-ear floors;
* `L_rec`, `R_rec`, and `LR_rec` are Pluecker rows;
* the closing recurrence is the exact rank-two determinant identity;
* the area row is the fan boundary identity.

Thus the only upstream obligation is to construct this point packet for the
presentation selected by the exact C24 classifier.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

abbrev HullSevenC24Index := Fin 7

/-- Actual geometric data in a counterclockwise C24 presentation.

The seven boundary signs are written cyclically.  The remaining eight signs
are exactly the C24 packet `13,24,35,14,25,04,26 > 0` and `15 < 0`.
-/
structure HullSevenC24PointData (v : Configuration) where
  cycle : HullSevenC24Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  boundary_pos : ∀ i,
    0 < sig (v point) (v (cycle i)) (v (cycle (i + 1)))
  d13_pos : 0 < sig (v point) (v (cycle 1)) (v (cycle 3))
  d24_pos : 0 < sig (v point) (v (cycle 2)) (v (cycle 4))
  d35_pos : 0 < sig (v point) (v (cycle 3)) (v (cycle 5))
  d14_pos : 0 < sig (v point) (v (cycle 1)) (v (cycle 4))
  d25_pos : 0 < sig (v point) (v (cycle 2)) (v (cycle 5))
  d04_pos : 0 < sig (v point) (v (cycle 0)) (v (cycle 4))
  d26_pos : 0 < sig (v point) (v (cycle 2)) (v (cycle 6))
  d15_neg : sig (v point) (v (cycle 1)) (v (cycle 5)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- Common positive normalization of the point-based determinants. -/
noncomputable def HullSevenC24PointData.bracket
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j : HullSevenC24Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma hullSevenC24Index_ne_add_one (i : HullSevenC24Index) :
    i ≠ i + 1 := by
  intro h
  have h' := congrArg (fun x : HullSevenC24Index ↦ x - i) h
  norm_num at h'

private lemma HullSevenC24PointData.labels_ne
    {v : Configuration} (X : HullSevenC24PointData v)
    {i j : HullSevenC24Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenC24PointData.positive_floor
    {v : Configuration} (X : HullSevenC24PointData v)
    {i j : HullSevenC24Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenC24PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenC24PointData.negative_floor
    {v : Configuration} (X : HullSevenC24PointData v)
    {i j : HullSevenC24Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenC24PointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenC24PointData.cycle_floor
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j k : HullSevenC24Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

/-- Every increasing hull ear gives its normalized two-step cap. -/
private lemma HullSevenC24PointData.ear_cap
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j k : HullSevenC24Index) (hij : i < j) (hjk : j < k) :
    X.bracket i k ≤ X.bracket i j + X.bracket j k - 1 := by
  have hfloor := X.cycle_floor i j k hij hjk
  have hsplit := split3 (v X.point)
    (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k))
  have hswap := sig_swap (v X.point) (v (X.cycle i)) (v (X.cycle k))
  have hraw :
      sig (v X.point) (v (X.cycle i)) (v (X.cycle k)) ≤
        sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) +
          sig (v X.point) (v (X.cycle j)) (v (X.cycle k)) - minTri v := by
    nlinarith
  have hrhs :
      X.bracket i j + X.bracket j k - 1 =
        (sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) +
            sig (v X.point) (v (X.cycle j)) (v (X.cycle k)) - minTri v) /
          minTri v := by
    unfold HullSevenC24PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenC24PointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

private lemma HullSevenC24PointData.bracket_skew
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j : HullSevenC24Index) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenC24PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenC24PointData.bracket_plucker
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j k l : HullSevenC24Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenC24PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- The actual C24 point packet constructs the complete abstract chord input.
In particular, the cubic closing recurrence is proved from coordinates rather
than added as a premise. -/
noncomputable def HullSevenC24PointData.toChordInput
    {v : Configuration} (X : HullSevenC24PointData v) :
    HullSevenChordInput (doubledHullArea v / minTri v) := by
  let b := X.bracket
  have hboundaryFloor : ∀ i, 1 ≤ b i (i + 1) := by
    intro i
    exact X.positive_floor (hullSevenC24Index_ne_add_one i)
      (X.boundary_pos i)
  have ha0 := hboundaryFloor 0
  have hA := hboundaryFloor 1
  have hB := hboundaryFloor 2
  have hC := hboundaryFloor 3
  have hD := hboundaryFloor 4
  have ha5 := hboundaryFloor 5
  have hG := hboundaryFloor 6
  have hp : 1 ≤ b 1 3 := X.positive_floor (by decide) X.d13_pos
  have hq : 1 ≤ b 2 4 := X.positive_floor (by decide) X.d24_pos
  have hr : 1 ≤ b 3 5 := X.positive_floor (by decide) X.d35_pos
  have hL : 1 ≤ b 1 4 := X.positive_floor (by decide) X.d14_pos
  have hR : 1 ≤ b 2 5 := X.positive_floor (by decide) X.d25_pos
  have hc : 1 ≤ -b 1 5 := X.negative_floor (by decide) X.d15_neg
  have hl : 1 ≤ b 0 4 := X.positive_floor (by decide) X.d04_pos
  have hm : 1 ≤ b 2 6 := X.positive_floor (by decide) X.d26_pos
  have hear012 := X.ear_cap 0 1 2 (by decide) (by decide)
  have hear123 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear234 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear345 := X.ear_cap 3 4 5 (by decide) (by decide)
  have hear456 := X.ear_cap 4 5 6 (by decide) (by decide)
  have hleft :
      b 1 2 * b 0 4 + b 0 1 * b 2 4 ≤
        b 1 4 * (b 0 1 + b 1 2 - 1) := by
    have hplucker := X.bracket_plucker 0 1 2 4
    have hL0 : 0 ≤ b 1 4 := le_trans (by norm_num) hL
    have hmul := mul_le_mul_of_nonneg_right hear012 hL0
    nlinarith
  have hright :
      b 4 5 * b 2 6 + b 5 6 * b 2 4 ≤
        b 2 5 * (b 5 6 + b 4 5 - 1) := by
    have hplucker := X.bracket_plucker 2 4 5 6
    have hR0 : 0 ≤ b 2 5 := le_trans (by norm_num) hR
    have hmul := mul_le_mul_of_nonneg_right hear456 hR0
    nlinarith
  have hboundary := fanSum_seven_eq_boundary v X.cycle (v X.point)
  have hraw :
      doubledHullArea v =
        sig (v X.point) (v (X.cycle 0)) (v (X.cycle 1)) +
        sig (v X.point) (v (X.cycle 1)) (v (X.cycle 2)) +
        sig (v X.point) (v (X.cycle 2)) (v (X.cycle 3)) +
        sig (v X.point) (v (X.cycle 3)) (v (X.cycle 4)) +
        sig (v X.point) (v (X.cycle 4)) (v (X.cycle 5)) +
        sig (v X.point) (v (X.cycle 5)) (v (X.cycle 6)) +
        sig (v X.point) (v (X.cycle 6)) (v (X.cycle 0)) := by
    exact X.hull_area_eq.trans hboundary
  have harea :
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 6 + b 6 0 ≤
        doubledHullArea v / minTri v := by
    dsimp [b, HullSevenC24PointData.bracket]
    apply le_of_eq
    field_simp [X.minTri_pos.ne']
    nlinarith [hraw]
  refine
    { a0 := b 0 1
      A := b 1 2
      B := b 2 3
      C := b 3 4
      D := b 4 5
      a5 := b 5 6
      p := b 1 3
      q := b 2 4
      r := b 3 5
      L := b 1 4
      R := b 2 5
      c := -b 1 5
      l := b 0 4
      m := b 2 6
      G := b 6 0
      a0_ge := by simpa [b] using ha0
      A_ge := by simpa [b] using hA
      B_ge := by simpa [b] using hB
      C_ge := by simpa [b] using hC
      D_ge := by simpa [b] using hD
      a5_ge := by simpa [b] using ha5
      p_ge := hp
      q_ge := hq
      r_ge := hr
      L_ge := hL
      R_ge := hR
      c_ge := hc
      l_ge := hl
      m_ge := hm
      G_ge := by simpa [b] using hG
      p_ear := hear123
      q_ear := hear234
      r_ear := hear345
      L_rec := ?_
      R_rec := ?_
      LR_rec := ?_
      left_endpoint := hleft
      right_endpoint := hright
      closing_rec := ?_
      area := harea }
  · have hplucker := X.bracket_plucker 1 2 3 4
    nlinarith only [hplucker]
  · have hplucker := X.bracket_plucker 2 3 4 5
    nlinarith only [hplucker]
  · have hplucker := X.bracket_plucker 1 2 4 5
    nlinarith only [hplucker]
  · dsimp [b, HullSevenC24PointData.bracket]
    field_simp [X.minTri_pos.ne']
    simp only [sig]
    ring

/-- Sharp C24 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_c24_point
    {v : Configuration} (X : HullSevenC24PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_chord_input X.toChordInput

/-- An actual C24 point packet contradicts the strict beating margin. -/
theorem HullSevenC24PointData.not_beats
    {v : Configuration} (X : HullSevenC24PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_c24_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
