import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType1Bracket

/-!
# Point-geometry adapter for the population-185 hull-seven chamber

This module links the abstract type-1 bracket packet to an actual
configuration.  The input contains a strict seven-cycle, its unique off-hull
label, the complete type-1 chord sign packet, and the already-certified fan
identity for the doubled hull area.  Everything metric is then derived:

* all unit floors come from `minTri`;
* all three ear caps come from the fan split of a hull ear;
* both endpoint caps come from one Pluecker row and a hull-ear floor;
* skew-symmetry and every recurrence come from `sig_swap` and `gp`.

Thus a dispatcher never has to manufacture an algebraic recurrence or a
high-point witness.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The positive pairs in the preferred type-1 presentation. -/
def HullSevenType1PositivePair
    (i j : HullSevenType1Index) : Prop :=
  i < j ∧ (i, j) ≠ (0, 6) ∧ (i, j) ≠ (1, 6)

private instance hullSevenType1PositivePairDecidable
    (i j : HullSevenType1Index) :
    Decidable (HullSevenType1PositivePair i j) := by
  unfold HullSevenType1PositivePair
  infer_instance

/-- Actual geometric data selected by the population-185 sign classifier.

The two exceptional signs are exactly `06` and `16`.  The fan identity is
the standard output of the seven-hull certificate (`IsHullArea.hull7` plus
`doubledHullArea_eq_of_isHullArea`).
-/
structure HullSevenType1PointData (v : Configuration) where
  cycle : HullSevenType1Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType1PositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  negative16 : sig (v point) (v (cycle 1)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- The commonly normalized signed determinant based at the off-hull point. -/
noncomputable def HullSevenType1PointData.bracket
    {v : Configuration} (X : HullSevenType1PointData v)
    (i j : HullSevenType1Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma HullSevenType1PointData.labels_ne
    {v : Configuration} (X : HullSevenType1PointData v)
    {i j : HullSevenType1Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType1PointData.positive_floor
    {v : Configuration} (X : HullSevenType1PointData v)
    {i j : HullSevenType1Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType1PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType1PointData.negative_floor
    {v : Configuration} (X : HullSevenType1PointData v)
    {i j : HullSevenType1Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType1PointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType1PointData.cycle_floor
    {v : Configuration} (X : HullSevenType1PointData v)
    (i j k : HullSevenType1Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

/-- Every increasing hull ear gives the normalized two-step cap. -/
private lemma HullSevenType1PointData.ear_cap
    {v : Configuration} (X : HullSevenType1PointData v)
    (i j k : HullSevenType1Index) (hij : i < j) (hjk : j < k) :
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
    unfold HullSevenType1PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType1PointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

private lemma HullSevenType1PointData.bracket_skew
    {v : Configuration} (X : HullSevenType1PointData v)
    (i j : HullSevenType1Index) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenType1PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenType1PointData.bracket_plucker
    {v : Configuration} (X : HullSevenType1PointData v)
    (i j k l : HullSevenType1Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType1PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- The actual point configuration constructs the complete abstract bracket
packet, including both endpoint caps and the normalized hull-area row. -/
noncomputable def HullSevenType1PointData.toBracketData
    {v : Configuration} (X : HullSevenType1PointData v) :
    HullSevenType1BracketData (doubledHullArea v / minTri v) := by
  let b := X.bracket
  have hrawpos : ∀ i j, HullSevenType1PositivePair i j →
      0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) := by
    intro i j hij
    exact X.positive i j hij
  have hfloor : ∀ i j, HullSevenType1PositivePair i j →
      1 ≤ b i j := by
    intro i j hij
    exact X.positive_floor (ne_of_lt hij.1) (hrawpos i j hij)
  have hear012 := X.ear_cap 0 1 2 (by decide) (by decide)
  have hear123 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear234 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear345 := X.ear_cap 3 4 5 (by decide) (by decide)
  have hear456 := X.ear_cap 4 5 6 (by decide) (by decide)
  have hleft : b 1 2 * b 0 4 + b 0 1 * b 2 4 ≤
      b 1 4 * (b 0 1 + b 1 2 - 1) := by
    have hp := X.bracket_plucker 0 1 2 4
    have hL0 : 0 ≤ b 1 4 :=
      le_trans (by norm_num)
        (hfloor 1 4 (by decide : HullSevenType1PositivePair 1 4))
    have hm := mul_le_mul_of_nonneg_right hear012 hL0
    nlinarith
  have hright : b 4 5 * b 2 6 + b 5 6 * b 2 4 ≤
      b 2 5 * (b 5 6 + b 4 5 - 1) := by
    have hp := X.bracket_plucker 2 4 5 6
    have hR0 : 0 ≤ b 2 5 :=
      le_trans (by norm_num)
        (hfloor 2 5 (by decide : HullSevenType1PositivePair 2 5))
    have hm := mul_le_mul_of_nonneg_right hear456 hR0
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
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 6 - b 0 6 ≤
        doubledHullArea v / minTri v := by
    have hswap := sig_swap (v X.point) (v (X.cycle 0)) (v (X.cycle 6))
    dsimp [b, HullSevenType1PointData.bracket]
    apply le_of_eq
    field_simp [X.minTri_pos.ne']
    nlinarith [hraw, hswap]
  refine
    { bracket := b
      skew := X.bracket_skew
      plucker := X.bracket_plucker
      d01_ge := hfloor 0 1 (by decide)
      d12_ge := hfloor 1 2 (by decide)
      d23_ge := hfloor 2 3 (by decide)
      d34_ge := hfloor 3 4 (by decide)
      d45_ge := hfloor 4 5 (by decide)
      d56_ge := hfloor 5 6 (by decide)
      neg_d06_ge := X.negative_floor (by decide) X.negative06
      d13_ge := hfloor 1 3 (by decide)
      d24_ge := hfloor 2 4 (by decide)
      d35_ge := hfloor 3 5 (by decide)
      d14_ge := hfloor 1 4 (by decide)
      d25_ge := hfloor 2 5 (by decide)
      d15_ge := hfloor 1 5 (by decide)
      d04_ge := hfloor 0 4 (by decide)
      d26_ge := hfloor 2 6 (by decide)
      d05_ge := hfloor 0 5 (by decide)
      neg_d16_ge := X.negative_floor (by decide) X.negative16
      ear13 := hear123
      ear24 := hear234
      ear35 := hear345
      left_endpoint := hleft
      right_endpoint := hright
      area := harea }

/-- Sharp type-1 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_type1_point
    {v : Configuration} (X : HullSevenType1PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type1_bracket X.toBracketData

/-- An actual type-1 point packet contradicts the strict beating margin. -/
theorem HullSevenType1PointData.not_beats
    {v : Configuration} (X : HullSevenType1PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type1_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
