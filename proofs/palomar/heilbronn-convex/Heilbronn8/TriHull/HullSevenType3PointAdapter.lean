import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType3Scalar

/-!
# Actual point-geometry adapter for retained hull-seven type 3

This file converts the exact preferred rotation-three sign presentation of an
actual seven-hull configuration into the compact type-3 chord packet.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

/-! ## Actual configuration adapter -/

abbrev HullSevenType3Index := Fin 7

/-- Positive increasing pairs in the exact rotation-three, unreflected
presentation of the retained type-3 key.  Its only negative increasing
brackets are `05`, `06`, and `16`. -/
def HullSevenType3PositivePair (i j : HullSevenType3Index) : Prop :=
  i < j ∧ (i, j) ≠ (0, 5) ∧ (i, j) ≠ (0, 6) ∧ (i, j) ≠ (1, 6)

private instance hullSevenType3PositivePairDecidable
    (i j : HullSevenType3Index) :
    Decidable (HullSevenType3PositivePair i j) := by
  unfold HullSevenType3PositivePair
  infer_instance

/-- Actual configuration data selected by the universal cutoff classifier's
rotation-three, unreflected witness for the population-61 type-3 key.

The reoriented ray chart used above is
`w=(v0,v1,v2,v4,v5,v6,-v3)`.  The adapter below implements that chart by the
smallest sign bridge: all increasing raw brackets other than `05,06,16` are
positive, and those three are negative.  It derives the reoriented chord
packet directly, so no false claim that the reorientation is a permutation
of the original hull cycle is made. -/
structure HullSevenType3PointData (v : Configuration) where
  cycle : HullSevenType3Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType3PositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative05 : sig (v point) (v (cycle 0)) (v (cycle 5)) < 0
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  negative16 : sig (v point) (v (cycle 1)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- Common positive normalization of the raw radial determinants. -/
noncomputable def HullSevenType3PointData.bracket
    {v : Configuration} (X : HullSevenType3PointData v)
    (i j : HullSevenType3Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma HullSevenType3PointData.labels_ne
    {v : Configuration} (X : HullSevenType3PointData v)
    {i j : HullSevenType3Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType3PointData.positive_floor
    {v : Configuration} (X : HullSevenType3PointData v)
    {i j : HullSevenType3Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType3PointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType3PointData.negative_floor
    {v : Configuration} (X : HullSevenType3PointData v)
    {i j : HullSevenType3Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType3PointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType3PointData.cycle_floor
    {v : Configuration} (X : HullSevenType3PointData v)
    (i j k : HullSevenType3Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

/-- An increasing raw hull ear gives its normalized radial cap. -/
private lemma HullSevenType3PointData.ear_cap
    {v : Configuration} (X : HullSevenType3PointData v)
    (i j k : HullSevenType3Index) (hij : i < j) (hjk : j < k) :
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
    unfold HullSevenType3PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType3PointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

private lemma HullSevenType3PointData.bracket_plucker
    {v : Configuration} (X : HullSevenType3PointData v)
    (i j k l : HullSevenType3Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType3PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- The actual point configuration supplies the complete compact chord
packet in the reoriented type-3 chart. -/
noncomputable def HullSevenType3PointData.toChordInput
    {v : Configuration} (X : HullSevenType3PointData v) :
    HullSevenType3ChordInput (doubledHullArea v / minTri v) := by
  let b := X.bracket
  have hfloor : ∀ i j, HullSevenType3PositivePair i j → 1 ≤ b i j := by
    intro i j hij
    exact X.positive_floor (ne_of_lt hij.1) (X.positive i j hij)
  have hear012 := X.ear_cap 0 1 2 (by decide) (by decide)
  have hear123 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear234 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear345 := X.ear_cap 3 4 5 (by decide) (by decide)
  have hear456 := X.ear_cap 4 5 6 (by decide) (by decide)
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
    dsimp [b, HullSevenType3PointData.bracket]
    apply le_of_eq
    field_simp [X.minTri_pos.ne']
    nlinarith [hraw, hswap]
  refine
    { a0 := b 0 1
      A := b 1 2
      B := b 2 3
      C := b 3 4
      D := b 4 5
      a5 := b 5 6
      G := -b 0 6
      p := b 1 3
      q := b 2 4
      r := b 3 5
      L := b 1 4
      R := b 2 5
      e0 := b 0 2
      e1 := b 4 6
      c := b 1 5
      l := b 0 4
      m := b 2 6
      n := -b 0 5
      h := -b 1 6
      a0_ge := hfloor 0 1 (by decide)
      A_ge := hfloor 1 2 (by decide)
      B_ge := hfloor 2 3 (by decide)
      C_ge := hfloor 3 4 (by decide)
      D_ge := hfloor 4 5 (by decide)
      a5_ge := hfloor 5 6 (by decide)
      G_ge := X.negative_floor (by decide) X.negative06
      p_ge := hfloor 1 3 (by decide)
      q_ge := hfloor 2 4 (by decide)
      r_ge := hfloor 3 5 (by decide)
      L_ge := hfloor 1 4 (by decide)
      R_ge := hfloor 2 5 (by decide)
      e0_ge := hfloor 0 2 (by decide)
      e1_ge := hfloor 4 6 (by decide)
      c_ge := hfloor 1 5 (by decide)
      l_ge := hfloor 0 4 (by decide)
      m_ge := hfloor 2 6 (by decide)
      n_ge := X.negative_floor (by decide) X.negative05
      h_ge := X.negative_floor (by decide) X.negative16
      e0_ear := hear012
      p_ear := hear123
      q_ear := hear234
      r_ear := hear345
      e1_ear := hear456
      e0L := ?_
      BL := ?_
      CR := ?_
      e1R := ?_
      a0D := ?_
      Aa5 := ?_
      a0a5 := ?_
      gL := ?_
      gR := ?_
      e0e1 := ?_
      area := by simpa [sub_eq_add_neg] using harea }
  · have hp := X.bracket_plucker 0 1 2 4
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 1 2 3 4
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 2 3 4 5
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 2 4 5 6
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 0 1 4 5
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 1 2 5 6
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 0 1 5 6
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 0 1 4 6
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 0 2 5 6
    dsimp [b] at hp ⊢
    nlinarith
  · have hp := X.bracket_plucker 0 2 4 6
    dsimp [b] at hp ⊢
    nlinarith

/-- Sharp type-3 bound in the normalized area of an actual configuration. -/
theorem hullSeven_v8_of_type3_point
    {v : Configuration} (X : HullSevenType3PointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type3_chord X.toChordInput

/-- An actual preferred type-3 packet contradicts the strict beating row. -/
theorem HullSevenType3PointData.not_beats
    {v : Configuration} (X : HullSevenType3PointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type3_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
