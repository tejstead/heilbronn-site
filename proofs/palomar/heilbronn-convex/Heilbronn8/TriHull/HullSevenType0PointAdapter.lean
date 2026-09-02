import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType0Bracket

/-!
# Point geometry adapter for the population-138 hull-seven chamber

This module links the complete type 0 sign packet to an actual configuration.
Only `d06` is negative in a preferred presentation.  Floors, ear caps,
endpoint caps, all Pluecker rows, and the normalized area row are derived from
the point geometry.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The positive pairs in a preferred type 0 presentation. -/
def HullSevenType0PositivePair
    (i j : HullSevenType0Index) : Prop :=
  i < j ∧ (i, j) ≠ (0, 6)

private instance hullSevenType0PositivePairDecidable
    (i j : HullSevenType0Index) :
    Decidable (HullSevenType0PositivePair i j) := by
  unfold HullSevenType0PositivePair
  infer_instance

/-- Actual geometric data selected by the type 0 sign classifier. -/
structure HullSevenType0PointData (v : Configuration) where
  cycle : HullSevenType0Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType0PositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- The normalized signed determinant based at the off-hull point. -/
noncomputable def HullSevenType0PointData.bracket
    {v : Configuration} (X : HullSevenType0PointData v)
    (i j : HullSevenType0Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma HullSevenType0PointData.labels_ne
    {v : Configuration} (X : HullSevenType0PointData v)
    {i j : HullSevenType0Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType0PointData.positive_floor
    {v : Configuration} (X : HullSevenType0PointData v)
    {i j : HullSevenType0Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType0PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType0PointData.negative_floor
    {v : Configuration} (X : HullSevenType0PointData v)
    {i j : HullSevenType0Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType0PointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType0PointData.cycle_floor
    {v : Configuration} (X : HullSevenType0PointData v)
    (i j k : HullSevenType0Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

/-- Every increasing hull ear gives its normalized two-step cap. -/
private lemma HullSevenType0PointData.ear_cap
    {v : Configuration} (X : HullSevenType0PointData v)
    (i j k : HullSevenType0Index) (hij : i < j) (hjk : j < k) :
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
    unfold HullSevenType0PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType0PointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

private lemma HullSevenType0PointData.bracket_skew
    {v : Configuration} (X : HullSevenType0PointData v)
    (i j : HullSevenType0Index) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenType0PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenType0PointData.bracket_plucker
    {v : Configuration} (X : HullSevenType0PointData v)
    (i j k l : HullSevenType0Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType0PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- An actual point configuration constructs the complete abstract bracket
packet, including both endpoint caps and the normalized hull-area row. -/
noncomputable def HullSevenType0PointData.toBracketData
    {v : Configuration} (X : HullSevenType0PointData v) :
    HullSevenType0BracketData (doubledHullArea v / minTri v) := by
  let b := X.bracket
  have hrawpos : ∀ i j, HullSevenType0PositivePair i j →
      0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) := by
    intro i j hij
    exact X.positive i j hij
  have hfloor : ∀ i j, HullSevenType0PositivePair i j →
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
        (hfloor 1 4 (by decide : HullSevenType0PositivePair 1 4))
    have hm := mul_le_mul_of_nonneg_right hear012 hL0
    nlinarith
  have hright : b 4 5 * b 2 6 + b 5 6 * b 2 4 ≤
      b 2 5 * (b 5 6 + b 4 5 - 1) := by
    have hp := X.bracket_plucker 2 4 5 6
    have hR0 : 0 ≤ b 2 5 :=
      le_trans (by norm_num)
        (hfloor 2 5 (by decide : HullSevenType0PositivePair 2 5))
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
    dsimp [b, HullSevenType0PointData.bracket]
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
      d16_ge := hfloor 1 6 (by decide)
      ear13 := hear123
      ear24 := hear234
      ear35 := hear345
      left_endpoint := hleft
      right_endpoint := hright
      area := harea }

/-- Sharp type 0 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_type0_point
    {v : Configuration} (X : HullSevenType0PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type0_bracket X.toBracketData

/-- An actual type 0 point packet contradicts the strict beating margin. -/
theorem HullSevenType0PointData.not_beats
    {v : Configuration} (X : HullSevenType0PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type0_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
