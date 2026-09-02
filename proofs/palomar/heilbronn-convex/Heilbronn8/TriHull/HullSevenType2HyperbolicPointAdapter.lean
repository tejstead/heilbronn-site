import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType2HyperbolicBracket

/-!
# Point adapter for the honest hull-seven type-2 hyperbolic chart

The canonical type-2 key `100000111001111111111` has, after the direct
rotation by two positions, exactly the three negative increasing pairs
`06`, `16`, and `26`.  This file turns that exact sign presentation into the
normalized signed-bracket packet of `HullSevenType2HyperbolicBracket`.

No scalar closer, search certificate, or chamber with the older misnamed
`Type2` scalar API is imported here.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

open scoped BigOperators

/-- The hyperbolic chart keeps cyclic `ZMod 7` addition but orders its
representatives as `0, ..., 6` when stating increasing-pair geometry. -/
private instance hullSevenType2HyperbolicIndexLinearOrder :
    LinearOrder HullSevenType2HyperbolicIndex :=
  inferInstanceAs (LinearOrder (Fin 7))

/-- Positive increasing pairs in the preferred honest type-2 presentation. -/
def HullSevenType2HyperbolicPositivePair
    (i j : HullSevenType2HyperbolicIndex) : Prop :=
  i < j ∧ (i, j) ≠ (0, 6) ∧ (i, j) ≠ (1, 6) ∧ (i, j) ≠ (2, 6)

private instance hullSevenType2HyperbolicPositivePairDecidable
    (i j : HullSevenType2HyperbolicIndex) :
    Decidable (HullSevenType2HyperbolicPositivePair i j) := by
  unfold HullSevenType2HyperbolicPositivePair
  infer_instance

/-- Actual point geometry in the exact preferred type-2 sign chart. -/
structure HullSevenType2HyperbolicPointData (v : Configuration) where
  cycle : HullSevenType2HyperbolicIndex → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType2HyperbolicPositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  negative16 : sig (v point) (v (cycle 1)) (v (cycle 6)) < 0
  negative26 : sig (v point) (v (cycle 2)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

/-- Common normalization by the positive minimum triangle area. -/
noncomputable def HullSevenType2HyperbolicPointData.bracket
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i j : HullSevenType2HyperbolicIndex) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

private lemma HullSevenType2HyperbolicPointData.labels_ne
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    {i j : HullSevenType2HyperbolicIndex} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType2HyperbolicPointData.positive_floor
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    {i j : HullSevenType2HyperbolicIndex} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.bracket i j := by
  unfold HullSevenType2HyperbolicPointData.bracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType2HyperbolicPointData.negative_floor
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    {i j : HullSevenType2HyperbolicIndex} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.bracket i j := by
  rw [show -X.bracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType2HyperbolicPointData.bracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType2HyperbolicPointData.cycle_floor
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i j k : HullSevenType2HyperbolicIndex) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

/-- An increasing hull ear gives its normalized radial cap. -/
private lemma HullSevenType2HyperbolicPointData.ear_cap
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i j k : HullSevenType2HyperbolicIndex) (hij : i < j) (hjk : j < k) :
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
    unfold HullSevenType2HyperbolicPointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType2HyperbolicPointData.bracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

/-- The positive wrap ear `(6,0,1)`, whose two-step chord is `b 6`. -/
private lemma HullSevenType2HyperbolicPointData.wrap_ear_cap
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v) :
    X.bracket 6 1 ≤ X.bracket 6 0 + X.bracket 0 1 - 1 := by
  have h016 := X.cycle_floor 0 1 6 (by decide) (by decide)
  have hcyclic :
      sig (v (X.cycle 6)) (v (X.cycle 0)) (v (X.cycle 1)) =
        sig (v (X.cycle 0)) (v (X.cycle 1)) (v (X.cycle 6)) := by
    simp only [sig]
    ring
  have hfloor : minTri v ≤
      sig (v (X.cycle 6)) (v (X.cycle 0)) (v (X.cycle 1)) := by
    rw [hcyclic]
    exact h016
  have hsplit := split3 (v X.point)
    (v (X.cycle 6)) (v (X.cycle 0)) (v (X.cycle 1))
  have hswap := sig_swap (v X.point) (v (X.cycle 6)) (v (X.cycle 1))
  have heq :
      X.bracket 6 0 + X.bracket 0 1 - X.bracket 6 1 =
        sig (v (X.cycle 6)) (v (X.cycle 0)) (v (X.cycle 1)) /
          minTri v := by
    unfold HullSevenType2HyperbolicPointData.bracket
    field_simp [X.minTri_pos.ne']
    nlinarith
  have hnormalized : 1 ≤
      X.bracket 6 0 + X.bracket 0 1 - X.bracket 6 1 := by
    rw [heq]
    apply (le_div_iff₀ X.minTri_pos).2
    simpa using hfloor
  linarith

private lemma HullSevenType2HyperbolicPointData.bracket_skew
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i j : HullSevenType2HyperbolicIndex) :
    X.bracket i j = -X.bracket j i := by
  unfold HullSevenType2HyperbolicPointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenType2HyperbolicPointData.bracket_plucker
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i j k l : HullSevenType2HyperbolicIndex) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenType2HyperbolicPointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

private lemma HullSevenType2HyperbolicPointData.adjacent_floor
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i : HullSevenType2HyperbolicIndex) : 1 ≤ X.bracket i (i + 1) := by
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

private lemma HullSevenType2HyperbolicPointData.twoStepMagnitude_floor
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i : HullSevenType2HyperbolicIndex) :
    1 ≤ hullSevenType2HyperbolicTwoStepMagnitude X.bracket i := by
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
  · change 1 ≤ -X.bracket 5 0
    rw [X.bracket_skew 5 0, neg_neg]
    exact X.positive_floor (by decide) (X.positive 0 5 (by decide))
  · have h := X.negative_floor (i := 1) (j := 6) (by decide) X.negative16
    change 1 ≤ X.bracket 6 1
    rw [X.bracket_skew 6 1]
    exact h

private lemma HullSevenType2HyperbolicPointData.threeStepMagnitude_floor
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (i : HullSevenType2HyperbolicIndex) :
    1 ≤ hullSevenType2HyperbolicThreeStepMagnitude X.bracket i := by
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

/-- Point geometry constructs the complete honest type-2 bracket packet. -/
noncomputable def HullSevenType2HyperbolicPointData.toBracketData
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v) :
    HullSevenType2HyperbolicBracketData
      (doubledHullArea v / minTri v) := by
  have hear0 := X.ear_cap 0 1 2 (by decide) (by decide)
  have hear1 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear2 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear3 := X.ear_cap 3 4 5 (by decide) (by decide)
  have hear4 := X.ear_cap 4 5 6 (by decide) (by decide)
  have hear6 := X.wrap_ear_cap
  refine
    { bracket := X.bracket
      skew := X.bracket_skew
      plucker := X.bracket_plucker
      adjacent_ge := X.adjacent_floor
      twoStepMagnitude_ge := X.twoStepMagnitude_floor
      threeStepMagnitude_ge := X.threeStepMagnitude_floor
      ear0 := hear0
      ear1 := hear1
      ear2 := hear2
      ear3 := hear3
      ear4 := hear4
      ear6 := hear6
      area := ?_ }
  have hsum :
      (∑ i : HullSevenType2HyperbolicIndex,
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
    rw [show (7 : HullSevenType2HyperbolicIndex) = 0 by decide]
    abel
  unfold HullSevenType2HyperbolicPointData.bracket
  rw [← Finset.sum_div, hsum]

/-- Public point-to-scalar semantic seam. -/
noncomputable def HullSevenType2HyperbolicPointData.toHyperbolicPacket
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v) :
    HullSevenType2HyperbolicPacket (doubledHullArea v / minTri v) :=
  X.toBracketData.toHyperbolicPacket

end Heilbronn8.TriHull
