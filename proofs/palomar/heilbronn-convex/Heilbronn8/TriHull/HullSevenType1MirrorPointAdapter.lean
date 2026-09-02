import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.TriHull.HullSevenType1Bracket

/-!
# Reflected point adapter for the chiral type-1 seven-wheel

The universal seven-wheel classifier has one chiral orbit.  In its direct
orientation the type-1 packet has negative increasing brackets `06,16`; in
the mirror orientation the negative increasing brackets are `05,06`.

This file handles the mirror without a second scalar theorem.  Reverse the
seven indices by `phi(i)=6-i` and normalize orientation by one global minus:

`reflected(i,j) = -raw(phi(i),phi(j)) = raw(phi(j),phi(i))`.

The reflected bracket has the direct type-1 signs.  Products in every
Pluecker row are unchanged, the three ears and two endpoint ears are merely
read in reverse order, and the boundary sum is the same hull fan area.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

def hullSevenType1MirrorIndex (i : HullSevenType1Index) :
    HullSevenType1Index :=
  ⟨6 - i.val, by omega⟩

/-- Positive increasing pairs in the CCW mirror chart. -/
def HullSevenType1MirrorPositivePair
    (i j : HullSevenType1Index) : Prop :=
  i < j ∧ (i, j) ≠ (0, 5) ∧ (i, j) ≠ (0, 6)

private instance hullSevenType1MirrorPositivePairDecidable
    (i j : HullSevenType1Index) :
    Decidable (HullSevenType1MirrorPositivePair i j) := by
  unfold HullSevenType1MirrorPositivePair
  infer_instance

/-- Actual geometry in the chiral mirror half of type 1. -/
structure HullSevenType1MirrorPointData (v : Configuration) where
  cycle : HullSevenType1Index → Fin 8
  point : Fin 8
  cycle_injective : Function.Injective cycle
  point_outside : point ∉ Set.range cycle
  minTri_pos : 0 < minTri v
  cycle_strict : StrictCyclicPos cycle v
  positive : ∀ i j, HullSevenType1MirrorPositivePair i j →
    0 < sig (v point) (v (cycle i)) (v (cycle j))
  negative05 : sig (v point) (v (cycle 0)) (v (cycle 5)) < 0
  negative06 : sig (v point) (v (cycle 0)) (v (cycle 6)) < 0
  hull_area_eq : doubledHullArea v = fanSum v cycle

noncomputable def HullSevenType1MirrorPointData.rawBracket
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j : HullSevenType1Index) : ℝ :=
  sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) / minTri v

/-- Orientation-normalized bracket after reversing all seven indices. -/
noncomputable def HullSevenType1MirrorPointData.reflectedBracket
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j : HullSevenType1Index) : ℝ :=
  -X.rawBracket (hullSevenType1MirrorIndex i)
    (hullSevenType1MirrorIndex j)

private lemma HullSevenType1MirrorPointData.labels_ne
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    {i j : HullSevenType1Index} (hij : i ≠ j) :
    X.point ≠ X.cycle i ∧ X.point ≠ X.cycle j ∧
      X.cycle i ≠ X.cycle j := by
  refine ⟨?_, ?_, X.cycle_injective.ne hij⟩
  · intro h
    exact X.point_outside ⟨i, h.symm⟩
  · intro h
    exact X.point_outside ⟨j, h.symm⟩

private lemma HullSevenType1MirrorPointData.positive_floor
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    {i j : HullSevenType1Index} (hij : i ≠ j)
    (hpos : 0 < sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) :
    1 ≤ X.rawBracket i j := by
  unfold HullSevenType1MirrorPointData.rawBracket
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_pos hpos] using hfloor

private lemma HullSevenType1MirrorPointData.negative_floor
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    {i j : HullSevenType1Index} (hij : i ≠ j)
    (hneg : sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) < 0) :
    1 ≤ -X.rawBracket i j := by
  rw [show -X.rawBracket i j =
      (-sig (v X.point) (v (X.cycle i)) (v (X.cycle j))) /
        minTri v by
    unfold HullSevenType1MirrorPointData.rawBracket
    ring]
  apply (le_div_iff₀ X.minTri_pos).2
  obtain ⟨hpi, hpj, hij'⟩ := X.labels_ne hij
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hij'
  simpa [abs_of_neg hneg] using hfloor

private lemma HullSevenType1MirrorPointData.cycle_floor
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j k : HullSevenType1Index) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (X.cycle i)) (v (X.cycle j)) (v (X.cycle k)) := by
  have hik : i < k := hij.trans hjk
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (X.cycle_injective.ne (ne_of_lt hij))
    (X.cycle_injective.ne (ne_of_lt hik))
    (X.cycle_injective.ne (ne_of_lt hjk))
  rwa [abs_of_pos (X.cycle_strict.pos i j k hij hjk)] at hfloor

private lemma HullSevenType1MirrorPointData.ear_cap
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j k : HullSevenType1Index) (hij : i < j) (hjk : j < k) :
    X.rawBracket i k ≤ X.rawBracket i j + X.rawBracket j k - 1 := by
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
      X.rawBracket i j + X.rawBracket j k - 1 =
        (sig (v X.point) (v (X.cycle i)) (v (X.cycle j)) +
            sig (v X.point) (v (X.cycle j)) (v (X.cycle k)) - minTri v) /
          minTri v := by
    unfold HullSevenType1MirrorPointData.rawBracket
    field_simp [X.minTri_pos.ne']
  rw [hrhs]
  unfold HullSevenType1MirrorPointData.rawBracket
  exact (div_le_div_iff_of_pos_right X.minTri_pos).2 hraw

private lemma HullSevenType1MirrorPointData.reflected_eq_raw_reverse
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j : HullSevenType1Index) :
    X.reflectedBracket i j =
      X.rawBracket (hullSevenType1MirrorIndex j)
        (hullSevenType1MirrorIndex i) := by
  unfold HullSevenType1MirrorPointData.reflectedBracket
    HullSevenType1MirrorPointData.rawBracket
  rw [sig_swap]
  ring

private lemma HullSevenType1MirrorPointData.reflected_skew
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j : HullSevenType1Index) :
    X.reflectedBracket i j = -X.reflectedBracket j i := by
  rw [X.reflected_eq_raw_reverse, X.reflected_eq_raw_reverse]
  unfold HullSevenType1MirrorPointData.rawBracket
  rw [sig_swap]
  ring

private lemma HullSevenType1MirrorPointData.reflected_plucker
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (i j k l : HullSevenType1Index) :
    X.reflectedBracket i j * X.reflectedBracket k l -
        X.reflectedBracket i k * X.reflectedBracket j l +
        X.reflectedBracket i l * X.reflectedBracket j k = 0 := by
  have hp := gp (v X.point)
    (v (X.cycle (hullSevenType1MirrorIndex i)))
    (v (X.cycle (hullSevenType1MirrorIndex j)))
    (v (X.cycle (hullSevenType1MirrorIndex k)))
    (v (X.cycle (hullSevenType1MirrorIndex l)))
  unfold HullSevenType1MirrorPointData.reflectedBracket
    HullSevenType1MirrorPointData.rawBracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

/-- The mirror chart constructs the existing direct type-1 bracket packet. -/
noncomputable def HullSevenType1MirrorPointData.toBracketData
    {v : Configuration} (X : HullSevenType1MirrorPointData v) :
    HullSevenType1BracketData (doubledHullArea v / minTri v) := by
  let r := X.rawBracket
  let b := X.reflectedBracket
  have hfloor : ∀ i j, HullSevenType1MirrorPositivePair i j →
      1 ≤ r i j := by
    intro i j hij
    exact X.positive_floor (ne_of_lt hij.1) (X.positive i j hij)
  have hear012 := X.ear_cap 0 1 2 (by decide) (by decide)
  have hear123 := X.ear_cap 1 2 3 (by decide) (by decide)
  have hear234 := X.ear_cap 2 3 4 (by decide) (by decide)
  have hear345 := X.ear_cap 3 4 5 (by decide) (by decide)
  have hear456 := X.ear_cap 4 5 6 (by decide) (by decide)
  have hear13 : b 1 3 ≤ b 1 2 + b 2 3 - 1 := by
    simpa [b, r, X.reflected_eq_raw_reverse,
      hullSevenType1MirrorIndex, add_comm] using hear345
  have hear24 : b 2 4 ≤ b 2 3 + b 3 4 - 1 := by
    simpa [b, r, X.reflected_eq_raw_reverse,
      hullSevenType1MirrorIndex, add_comm] using hear234
  have hear35 : b 3 5 ≤ b 3 4 + b 4 5 - 1 := by
    simpa [b, r, X.reflected_eq_raw_reverse,
      hullSevenType1MirrorIndex, add_comm] using hear123
  have hreflected012 : b 0 2 ≤ b 0 1 + b 1 2 - 1 := by
    simpa [b, r, X.reflected_eq_raw_reverse,
      hullSevenType1MirrorIndex, add_comm] using hear456
  have hreflected456 : b 4 6 ≤ b 4 5 + b 5 6 - 1 := by
    have hear012' :
        X.rawBracket 0 2 ≤ X.rawBracket 1 2 + X.rawBracket 0 1 - 1 := by
      linarith [hear012]
    simpa [b, r, X.reflected_eq_raw_reverse,
      hullSevenType1MirrorIndex] using hear012'
  have hleft : b 1 2 * b 0 4 + b 0 1 * b 2 4 ≤
      b 1 4 * (b 0 1 + b 1 2 - 1) := by
    have hp := X.reflected_plucker 0 1 2 4
    have hL0 : 0 ≤ b 1 4 := by
      have hf := hfloor 2 5
        (by decide : HullSevenType1MirrorPositivePair 2 5)
      have hf' : 1 ≤ b 1 4 := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hf
      exact le_trans (by norm_num) hf'
    have hm := mul_le_mul_of_nonneg_right hreflected012 hL0
    nlinarith
  have hright : b 4 5 * b 2 6 + b 5 6 * b 2 4 ≤
      b 2 5 * (b 5 6 + b 4 5 - 1) := by
    have hp := X.reflected_plucker 2 4 5 6
    have hR0 : 0 ≤ b 2 5 := by
      have hf := hfloor 1 4
        (by decide : HullSevenType1MirrorPositivePair 1 4)
      have hf' : 1 ≤ b 2 5 := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hf
      exact le_trans (by norm_num) hf'
    have hm := mul_le_mul_of_nonneg_right hreflected456 hR0
    nlinarith
  have hboundary := fanSum_seven_eq_boundary v X.cycle (v X.point)
  have hrawArea :
      doubledHullArea v =
        r 0 1 * minTri v + r 1 2 * minTri v +
        r 2 3 * minTri v + r 3 4 * minTri v +
        r 4 5 * minTri v + r 5 6 * minTri v - r 0 6 * minTri v := by
    have harea := X.hull_area_eq.trans hboundary
    have hswap := sig_swap (v X.point) (v (X.cycle 0)) (v (X.cycle 6))
    dsimp [r, HullSevenType1MirrorPointData.rawBracket]
    field_simp [X.minTri_pos.ne']
    nlinarith [harea, hswap]
  have harea :
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 6 - b 0 6 ≤
        doubledHullArea v / minTri v := by
    apply le_of_eq
    rw [show b 0 1 = r 5 6 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex],
      show b 1 2 = r 4 5 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex],
      show b 2 3 = r 3 4 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex],
      show b 3 4 = r 2 3 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex],
      show b 4 5 = r 1 2 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex],
      show b 5 6 = r 0 1 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex],
      show b 0 6 = r 0 6 by
          simp [b, r, X.reflected_eq_raw_reverse,
            hullSevenType1MirrorIndex]]
    apply (eq_div_iff X.minTri_pos.ne').2
    nlinarith [hrawArea]
  refine
    { bracket := b
      skew := X.reflected_skew
      plucker := X.reflected_plucker
      d01_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 5 6 (by decide)
      d12_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 4 5 (by decide)
      d23_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 3 4 (by decide)
      d34_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 2 3 (by decide)
      d45_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 1 2 (by decide)
      d56_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 0 1 (by decide)
      neg_d06_ge := by
        have hf := X.negative_floor (by decide) X.negative06
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hf
      d13_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 3 5 (by decide)
      d24_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 2 4 (by decide)
      d35_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 1 3 (by decide)
      d14_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 2 5 (by decide)
      d25_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 1 4 (by decide)
      d15_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 1 5 (by decide)
      d04_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 2 6 (by decide)
      d26_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 0 4 (by decide)
      d05_ge := by
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hfloor 1 6 (by decide)
      neg_d16_ge := by
        have hf := X.negative_floor (by decide) X.negative05
        simpa [b, r, X.reflected_eq_raw_reverse,
          hullSevenType1MirrorIndex] using hf
      ear13 := hear13
      ear24 := hear24
      ear35 := hear35
      left_endpoint := hleft
      right_endpoint := hright
      area := harea }

theorem hullSeven_v8_of_type1_mirror_point
    {v : Configuration} (X : HullSevenType1MirrorPointData v) :
    1 ≤ v8 * (doubledHullArea v / minTri v) :=
  hullSeven_v8_of_type1_bracket X.toBracketData

theorem HullSevenType1MirrorPointData.not_beats
    {v : Configuration} (X : HullSevenType1MirrorPointData v)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type1_mirror_point X
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end Heilbronn8.TriHull
