import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType4Bracket

/-!
# Point-geometry adapter for hull-seven type 4

This module instantiates the preferred cyclic type-4 bracket chart by the
normalized radial determinants of an actual configuration.  In increasing
cycle order the only negative pairs are `05`, `06`, `16`, and `26`.  After
passing to cyclic indices this says:

* every one-step and two-step bracket is positive;
* every three-step bracket is positive except those starting at `4` and `5`.

All determinant floors, the four ear caps used by the scalar closer,
skew-symmetry, Pluecker, and the normalized fan-area row are derived here
from point geometry.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

open scoped BigOperators

/-- The type-4 chart uses cyclic `ZMod 7` addition, while its preferred
increasing presentation uses the usual order on the representatives `0, ..., 6`.
This is definitionally the standard order on `Fin 7`. -/
private instance hullSevenType4IndexLinearOrder :
    LinearOrder HullSevenType4Index :=
  inferInstanceAs (LinearOrder (Fin 7))

/-- Positive increasing pairs in the preferred type-4 presentation. -/
def HullSevenType4PositivePair
    (i j : HullSevenType4Index) : Prop :=
  i < j ∧ (i, j) ≠ (0, 5) ∧ (i, j) ≠ (0, 6) ∧
    (i, j) ≠ (1, 6) ∧ (i, j) ≠ (2, 6)

private instance hullSevenType4PositivePairDecidable
    (i j : HullSevenType4Index) :
    Decidable (HullSevenType4PositivePair i j) := by
  unfold HullSevenType4PositivePair
  infer_instance

/-- Actual point data selected by the exact preferred type-4 sign theorem. -/
structure HullSevenType4PointData (v : Configuration) where
  cycle : HullSevenType4Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType4PositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative05 : sig (v point) (v (cycle 0)) (v (cycle 5)) < 0
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  negative16 : sig (v point) (v (cycle 1)) (v (cycle 6)) < 0
  negative26 : sig (v point) (v (cycle 2)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- Common positive normalization of the signed radial determinants. -/
noncomputable def HullSevenType4PointData.bracket
    {v : Configuration} (X : HullSevenType4PointData v)
    (i j : HullSevenType4Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma HullSevenType4PointData.labels_ne
    {v : Configuration} (X : HullSevenType4PointData v)
    {i j : HullSevenType4Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType4PointData.positive_floor
    {v : Configuration} (X : HullSevenType4PointData v)
    {i j : HullSevenType4Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType4PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType4PointData.negative_floor
    {v : Configuration} (X : HullSevenType4PointData v)
    {i j : HullSevenType4Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType4PointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType4PointData.cycle_floor
    {v : Configuration} (X : HullSevenType4PointData v)
    (i j k : HullSevenType4Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

/-- An increasing hull ear gives its normalized radial cap. -/
private lemma HullSevenType4PointData.ear_cap
    {v : Configuration} (X : HullSevenType4PointData v)
    (i j k : HullSevenType4Index) (hij : i < j) (hjk : j < k) :
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
    unfold HullSevenType4PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType4PointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

private lemma HullSevenType4PointData.bracket_skew
    {v : Configuration} (X : HullSevenType4PointData v)
    (i j : HullSevenType4Index) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenType4PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenType4PointData.bracket_plucker
    {v : Configuration} (X : HullSevenType4PointData v)
    (i j k l : HullSevenType4Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType4PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

private lemma HullSevenType4PointData.adjacent_floor
    {v : Configuration} (X : HullSevenType4PointData v)
    (i : HullSevenType4Index) : 1 ≤ X.bracket i (i + 1) := by
  fin_cases i
  · change 1 ≤ X.bracket 0 1
    exact X.positive_floor (by decide) (X.positive 0 1 (by decide))
  · change 1 ≤ X.bracket 1 2
    exact X.positive_floor (by decide) (X.positive 1 2 (by decide))
  · change 1 ≤ X.bracket 2 3
    exact X.positive_floor (by decide) (X.positive 2 3 (by decide))
  · change 1 ≤ X.bracket 3 4
    exact X.positive_floor (by decide) (X.positive 3 4 (by decide))
  · change 1 ≤ X.bracket 4 5
    exact X.positive_floor (by decide) (X.positive 4 5 (by decide))
  · change 1 ≤ X.bracket 5 6
    exact X.positive_floor (by decide) (X.positive 5 6 (by decide))
  · have h := X.negative_floor (i := 0) (j := 6) (by decide) X.negative06
    change 1 ≤ X.bracket 6 0
    rw [X.bracket_skew 6 0]
    exact h

private lemma HullSevenType4PointData.twoStep_floor
    {v : Configuration} (X : HullSevenType4PointData v)
    (i : HullSevenType4Index) : 1 ≤ X.bracket i (i + 2) := by
  fin_cases i
  · change 1 ≤ X.bracket 0 2
    exact X.positive_floor (by decide) (X.positive 0 2 (by decide))
  · change 1 ≤ X.bracket 1 3
    exact X.positive_floor (by decide) (X.positive 1 3 (by decide))
  · change 1 ≤ X.bracket 2 4
    exact X.positive_floor (by decide) (X.positive 2 4 (by decide))
  · change 1 ≤ X.bracket 3 5
    exact X.positive_floor (by decide) (X.positive 3 5 (by decide))
  · change 1 ≤ X.bracket 4 6
    exact X.positive_floor (by decide) (X.positive 4 6 (by decide))
  · have h := X.negative_floor (i := 0) (j := 5) (by decide) X.negative05
    change 1 ≤ X.bracket 5 0
    rw [X.bracket_skew 5 0]
    exact h
  · have h := X.negative_floor (i := 1) (j := 6) (by decide) X.negative16
    change 1 ≤ X.bracket 6 1
    rw [X.bracket_skew 6 1]
    exact h

private lemma HullSevenType4PointData.threeStepMagnitude_floor
    {v : Configuration} (X : HullSevenType4PointData v)
    (i : HullSevenType4Index) :
    1 ≤ hullSevenType4ThreeStepMagnitude X.bracket i := by
  fin_cases i
  · change 1 ≤ X.bracket 0 3
    exact X.positive_floor (by decide) (X.positive 0 3 (by decide))
  · change 1 ≤ X.bracket 1 4
    exact X.positive_floor (by decide) (X.positive 1 4 (by decide))
  · change 1 ≤ X.bracket 2 5
    exact X.positive_floor (by decide) (X.positive 2 5 (by decide))
  · change 1 ≤ X.bracket 3 6
    exact X.positive_floor (by decide) (X.positive 3 6 (by decide))
  · change 1 ≤ -X.bracket 4 0
    rw [X.bracket_skew 4 0, neg_neg]
    exact X.positive_floor (by decide) (X.positive 0 4 (by decide))
  · change 1 ≤ -X.bracket 5 1
    rw [X.bracket_skew 5 1, neg_neg]
    exact X.positive_floor (by decide) (X.positive 1 5 (by decide))
  · have h := X.negative_floor (i := 2) (j := 6) (by decide) X.negative26
    change 1 ≤ X.bracket 6 2
    rw [X.bracket_skew 6 2]
    exact h

/-- Point geometry constructs the complete preferred type-4 bracket packet. -/
noncomputable def HullSevenType4PointData.toBracketData
    {v : Configuration} (X : HullSevenType4PointData v) :
    HullSevenType4BracketData (doubledHullArea v / minTri v) := by
  have hear0 := X.ear_cap 0 1 2 (by decide) (by decide)
  have hear1 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear2 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear3 := X.ear_cap 3 4 5 (by decide) (by decide)
  refine
    { bracket := X.bracket
      skew := X.bracket_skew
      plucker := X.bracket_plucker
      adjacent_ge := X.adjacent_floor
      twoStep_ge := X.twoStep_floor
      threeStepMagnitude_ge := X.threeStepMagnitude_floor
      ear0 := hear0
      ear1 := hear1
      ear2 := hear2
      ear3 := hear3
      area := ?_ }
  have hsum :
      (∑ i : HullSevenType4Index,
        sig (v X.point) (v (X.cycle i)) (v (X.cycle (i + 1)))) =
          doubledHullArea v := by
    classical
    rw [X.hull_area_eq]
    rw [fanSum_seven_eq_boundary v X.cycle (v X.point)]
    rw [show (Finset.univ : Finset (ZMod 7)) =
      {0, 1, 2, 3, 4, 5, 6} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num
    rw [show (7 : HullSevenType4Index) = 0 by decide]
    abel
  unfold HullSevenType4PointData.bracket
  rw [← Finset.sum_div, hsum]

/-- Sharp type-4 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_type4_point
    {v : Configuration} (X : HullSevenType4PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type4_bracket X.toBracketData

/-- An actual preferred type-4 packet contradicts the strict beating row. -/
theorem HullSevenType4PointData.not_beats
    {v : Configuration} (X : HullSevenType4PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type4_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
