import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType7Cyclic

/-!
# Point-geometry adapter for the cyclic type-7 chamber

The population-18 chamber has positive one-, two-, and three-step cyclic
brackets in every normalized presentation.  This file instantiates the
generic type-7 bracket interface by `sig / minTri`, deriving skew-symmetry,
Pluecker, all unit floors, the area row, and the contradiction to `Beats`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Actual normalized-sign data for the cyclic population-18 chamber. -/
structure HullSevenType7PointData (v : Configuration) where
  cycle : HullSevenCycleIndex → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  adjacent_pos : ∀ i,
    0 < sig (v point) (v (cycle i)) (v (cycle (i + 1)))
  twoStep_pos : ∀ i,
    0 < sig (v point) (v (cycle i)) (v (cycle (i + 2)))
  threeStep_pos : ∀ i,
    0 < sig (v point) (v (cycle i)) (v (cycle (i + 3)))
  hull_area_eq :
    (∑ i, sig (v point) (v (cycle i)) (v (cycle (i + 1)))) =
      doubledHullArea v

/-- The normalized signed bracket based at the unique off-cycle point. -/
noncomputable def HullSevenType7PointData.bracket
    {v : Configuration} (X : HullSevenType7PointData v)
    (i j : HullSevenCycleIndex) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma hullSevenCycleIndex_ne_add_one (i : HullSevenCycleIndex) :
    i ≠ i + 1 := by
  intro h
  have h' := congrArg (fun x : HullSevenCycleIndex ↦ x - i) h
  norm_num at h'
  exact (by decide : (0 : HullSevenCycleIndex) ≠ 1) h'

private lemma hullSevenCycleIndex_ne_add_two (i : HullSevenCycleIndex) :
    i ≠ i + 2 := by
  intro h
  have h' := congrArg (fun x : HullSevenCycleIndex ↦ x - i) h
  norm_num at h'
  exact (by decide : (0 : HullSevenCycleIndex) ≠ 2) h'

private lemma hullSevenCycleIndex_ne_add_three (i : HullSevenCycleIndex) :
    i ≠ i + 3 := by
  intro h
  have h' := congrArg (fun x : HullSevenCycleIndex ↦ x - i) h
  norm_num at h'
  exact (by decide : (0 : HullSevenCycleIndex) ≠ 3) h'

private lemma HullSevenType7PointData.labels_ne
    {v : Configuration} (X : HullSevenType7PointData v)
    {i j : HullSevenCycleIndex} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType7PointData.positive_floor
    {v : Configuration} (X : HullSevenType7PointData v)
    {i j : HullSevenCycleIndex} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType7PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType7PointData.bracket_skew
    {v : Configuration} (X : HullSevenType7PointData v)
    (i j : HullSevenCycleIndex) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenType7PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenType7PointData.bracket_plucker
    {v : Configuration} (X : HullSevenType7PointData v)
    (i j k l : HullSevenCycleIndex) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType7PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- The point packet constructs the complete generic cyclic bracket data. -/
noncomputable def HullSevenType7PointData.toBracketData
    {v : Configuration} (X : HullSevenType7PointData v) :
    HullSevenType7BracketData (doubledHullArea v / minTri v) where
  bracket := X.bracket
  skew := X.bracket_skew
  plucker := X.bracket_plucker
  adjacent_ge := fun i =>
    X.positive_floor (hullSevenCycleIndex_ne_add_one i) (X.adjacent_pos i)
  twoStep_ge := fun i =>
    X.positive_floor (hullSevenCycleIndex_ne_add_two i) (X.twoStep_pos i)
  threeStep_ge := fun i =>
    X.positive_floor (hullSevenCycleIndex_ne_add_three i) (X.threeStep_pos i)
  area := by
    unfold HullSevenType7PointData.bracket
    rw [← Finset.sum_div, X.hull_area_eq]

/-- Sharp type-7 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_type7_point
    {v : Configuration} (X : HullSevenType7PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type7_bracket X.toBracketData

/-- An actual cyclic type-7 packet contradicts the beating margin. -/
theorem HullSevenType7PointData.not_beats
    {v : Configuration} (X : HullSevenType7PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type7_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
