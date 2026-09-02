import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType6RawAreaAdapter

/-!
# Point adapter for the honest hull-seven type-6 reflection chart

This file constructs the rotation-one bracket packet from an actual strict
seven-cycle and its off-hull point.  All 21 determinant floors, all twelve
Pluecker identities, the four reflected ear floors, and the normalized area
row are consequences of point geometry.

The cap-free raw-area closer consumes this bracket packet directly.  The
older conditional conversion to the compact reflection payload remains below
as an independently useful interface.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Positive increasing pairs in the rotation-one type-6 chart. -/
def HullSevenType6PositivePair (i j : HullSevenType6Index) : Prop :=
  i < j ∧
    (i, j) ≠ (0, 4) ∧ (i, j) ≠ (0, 5) ∧ (i, j) ≠ (0, 6) ∧
    (i, j) ≠ (1, 5) ∧ (i, j) ≠ (1, 6)

private instance hullSevenType6PositivePairDecidable
    (i j : HullSevenType6Index) :
    Decidable (HullSevenType6PositivePair i j) := by
  unfold HullSevenType6PositivePair
  infer_instance

/-- Actual geometry selected by the exact rotation-one sign theorem. -/
structure HullSevenType6PointData (v : Configuration) where
  cycle : HullSevenType6Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType6PositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative04 : sig (v point) (v (cycle 0)) (v (cycle 4)) < 0
  negative05 : sig (v point) (v (cycle 0)) (v (cycle 5)) < 0
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  negative15 : sig (v point) (v (cycle 1)) (v (cycle 5)) < 0
  negative16 : sig (v point) (v (cycle 1)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- Common positive normalization of the signed radial determinants. -/
noncomputable def HullSevenType6PointData.bracket
    {v : Configuration} (X : HullSevenType6PointData v)
    (i j : HullSevenType6Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma HullSevenType6PointData.labels_ne
    {v : Configuration} (X : HullSevenType6PointData v)
    {i j : HullSevenType6Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType6PointData.positive_floor
    {v : Configuration} (X : HullSevenType6PointData v)
    {i j : HullSevenType6Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType6PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType6PointData.negative_floor
    {v : Configuration} (X : HullSevenType6PointData v)
    {i j : HullSevenType6Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType6PointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType6PointData.cycle_floor
    {v : Configuration} (X : HullSevenType6PointData v)
    (i j k : HullSevenType6Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

private lemma HullSevenType6PointData.ear_cap
    {v : Configuration} (X : HullSevenType6PointData v)
    (i j k : HullSevenType6Index) (hij : i < j) (hjk : j < k) :
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
    unfold HullSevenType6PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType6PointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

/-- The wrap ear `(5,6,0)` in the normalized radial diagram. -/
private lemma HullSevenType6PointData.wrap_ear_floor
    {v : Configuration} (X : HullSevenType6PointData v) :
    1 ≤ X.bracket 5 6 - X.bracket 0 6 + X.bracket 0 5 := by
  have h056 := X.cycle_floor 0 5 6 (by decide) (by decide)
  have hcyclic :
      sig (v (X.cycle 5)) (v (X.cycle 6)) (v (X.cycle 0)) =
        sig (v (X.cycle 0)) (v (X.cycle 5)) (v (X.cycle 6)) := by
    simp only [sig]
    ring
  have hfloor :
      minTri v ≤
        sig (v (X.cycle 5)) (v (X.cycle 6)) (v (X.cycle 0)) := by
    rw [hcyclic]
    exact h056
  have hsplit := split3 (v X.point)
    (v (X.cycle 5)) (v (X.cycle 6)) (v (X.cycle 0))
  have hswap := sig_swap (v X.point) (v (X.cycle 0)) (v (X.cycle 6))
  have heq :
      X.bracket 5 6 - X.bracket 0 6 + X.bracket 0 5 =
        sig (v (X.cycle 5)) (v (X.cycle 6)) (v (X.cycle 0)) /
          minTri v := by
    unfold HullSevenType6PointData.bracket
    field_simp [X.minTri_pos.ne']
    nlinarith
  rw [heq]
  apply (le_div_iff₀ X.minTri_pos).2
  simpa using hfloor

private lemma HullSevenType6PointData.bracket_skew
    {v : Configuration} (X : HullSevenType6PointData v)
    (i j : HullSevenType6Index) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenType6PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenType6PointData.bracket_plucker
    {v : Configuration} (X : HullSevenType6PointData v)
    (i j k l : HullSevenType6Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType6PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- Point geometry constructs the entire raw bracket packet. -/
noncomputable def HullSevenType6PointData.toBracketData
    {v : Configuration} (X : HullSevenType6PointData v) :
    HullSevenType6BracketData (doubledHullArea v / minTri v) := by
  let b := X.bracket
  have hfloor : ∀ i j, HullSevenType6PositivePair i j → 1 ≤ b i j := by
    intro i j hij
    exact X.positive_floor (ne_of_lt hij.1) (X.positive i j hij)
  have hear123 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear234 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear456 := X.ear_cap 4 5 6 (by decide) (by decide)
  have hear560 := X.wrap_ear_floor
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
    dsimp [b, HullSevenType6PointData.bracket]
    apply le_of_eq
    field_simp [X.minTri_pos.ne']
    nlinarith [hraw, hswap]
  refine
    { bracket := b
      skew := X.bracket_skew
      plucker := X.bracket_plucker
      d01_ge := hfloor 0 1 (by decide)
      d02_ge := hfloor 0 2 (by decide)
      d03_ge := hfloor 0 3 (by decide)
      neg_d04_ge := X.negative_floor (by decide) X.negative04
      neg_d05_ge := X.negative_floor (by decide) X.negative05
      neg_d06_ge := X.negative_floor (by decide) X.negative06
      d12_ge := hfloor 1 2 (by decide)
      d13_ge := hfloor 1 3 (by decide)
      d14_ge := hfloor 1 4 (by decide)
      neg_d15_ge := X.negative_floor (by decide) X.negative15
      neg_d16_ge := X.negative_floor (by decide) X.negative16
      d23_ge := hfloor 2 3 (by decide)
      d24_ge := hfloor 2 4 (by decide)
      d25_ge := hfloor 2 5 (by decide)
      d26_ge := hfloor 2 6 (by decide)
      d34_ge := hfloor 3 4 (by decide)
      d35_ge := hfloor 3 5 (by decide)
      d36_ge := hfloor 3 6 (by decide)
      d45_ge := hfloor 4 5 (by decide)
      d46_ge := hfloor 4 6 (by decide)
      d56_ge := hfloor 5 6 (by decide)
      ear123 := by dsimp [b]; linarith [hear123]
      ear560 := hear560
      ear234 := by dsimp [b]; linarith [hear234]
      ear456 := by dsimp [b]; linarith [hear456]
      area := harea }

/-- The point packet unconditionally supplies rows 3--8 and the area row. -/
noncomputable def HullSevenType6PointData.toReflectionCoreData
    {v : Configuration} (X : HullSevenType6PointData v) :
    HullSevenType6ReflectionCoreData (doubledHullArea v / minTri v) :=
  X.toBracketData.toRawReflectionData.toCoreData

/-- Honest point-to-reflection conversion.  The only extra inputs are the
two cap inequalities that are not consequences of the raw ear floors. -/
noncomputable def HullSevenType6PointData.toReflectionData
    {v : Configuration} (X : HullSevenType6PointData v)
    (p_cap : Real.sqrt (X.bracket 1 3 * (-X.bracket 0 5)) ≤
      Real.sqrt (X.bracket 1 2 * (-X.bracket 0 6)) +
        Real.sqrt (X.bracket 2 3 * X.bracket 5 6) - 1)
    (q_cap : Real.sqrt (X.bracket 2 4 * X.bracket 4 6) ≤
      Real.sqrt (X.bracket 2 3 * X.bracket 5 6) +
        Real.sqrt (X.bracket 3 4 * X.bracket 4 5) - 1) :
    HullSevenType6ReflectionData (doubledHullArea v / minTri v) :=
  X.toBracketData.toRawReflectionData.toReflectionData p_cap q_cap

/-- Sharp type-6 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_type6_point
    {v : Configuration} (X : HullSevenType6PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type6_raw X.toBracketData.toRawReflectionData

/-- An actual type-6 point packet contradicts the strict beating row. -/
theorem HullSevenType6PointData.not_beats
    {v : Configuration} (X : HullSevenType6PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type6_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
