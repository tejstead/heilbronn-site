import Heilbronn8.Survivors.Join.HullSixDirectGeometricExclusion
import Heilbronn8.Survivors.Join.HullSixFerrersPropagation
import Heilbronn8.Survivors.Join.HullSixTwoFourFiniteBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeFiniteBridge
import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadGeometry

/-!
# Production-free Ferrers normalization for hull size six

After the geometric sign-block theorem and the `1 + 5` closure, a compact
hull-six residual has one of the cyclic frames

```text
U0 U1       L0 L1 L2 L3
U0 U1 U2    L0 L1 L2.
```

For a cross chord put `X i j = sig P (U i) (L j)` and
`Y i j = sig Q (U i) (L j)`.  Two four-point determinant identities make
the sign-selected chamber labels increase along rows and decrease down
columns.  The two cyclic boundary edges give the bottom-left `L` and
top-right `R` cells.  Small kernel-checked functions then turn these order
facts into exactly the cut records consumed by the compact providers.

No production route, retained record, search certificate, or classifier
registry occurs in this module.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

/-! ## Pure finite table recognition -/

private instance : Fintype HullSixChamberLabel where
  elems := {HullSixChamberLabel.L, HullSixChamberLabel.M,
    HullSixChamberLabel.R}
  complete := by
    intro tag
    cases tag <;> simp

/-- Numerical order `L < M < R`. -/
def hullSixChamberRank : HullSixChamberLabel -> Nat
  | .L => 0
  | .M => 1
  | .R => 2

/-- Select a chamber from the signs of its two base determinants. -/
noncomputable def hullSixChamberLabelOfSigns (x y : Real) : HullSixChamberLabel :=
  if 0 < x then .L else if 0 < y then .M else .R

/-- Implication between the two positive-sign predicates is exactly
monotonicity of the three-valued chamber label. -/
theorem chamberRank_le_of_positive_implications
    {x0 y0 x1 y1 : Real}
    (hx : 0 < x1 -> 0 < x0) (hy : 0 < y1 -> 0 < y0) :
    hullSixChamberRank (hullSixChamberLabelOfSigns x0 y0) <=
      hullSixChamberRank (hullSixChamberLabelOfSigns x1 y1) := by
  by_cases hx0 : 0 < x0
  · simp [hullSixChamberLabelOfSigns, hullSixChamberRank, hx0]
  · have hx1 : Not (0 < x1) := fun h => hx0 (hx h)
    by_cases hy0 : 0 < y0
    · by_cases hy1 : 0 < y1 <;>
        simp [hullSixChamberLabelOfSigns, hullSixChamberRank,
          hx0, hx1, hy0, hy1]
    · have hy1 : Not (0 < y1) := fun h => hy0 (hy h)
      simp [hullSixChamberLabelOfSigns, hullSixChamberRank,
        hx0, hx1, hy0, hy1]

/-- Absolute floors strengthen the sign-selected label to its advertised
closed chamber inequalities. -/
theorem chamberLabelOfSigns_holds
    {m x y : Real} (hm : 0 < m)
    (hxFloor : m <= |x|) (hyFloor : m <= |y|) :
    HullSixChamberLabel.Holds
      (hullSixChamberLabelOfSigns x y) m x y := by
  by_cases hx : 0 < x
  · simp only [hullSixChamberLabelOfSigns, if_pos hx,
      HullSixChamberLabel.Holds]
    exact (positive_iff_positive_floor hm hxFloor).1 hx
  · have hxNe : x ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hxFloor
      exact (not_le_of_gt hm) hxFloor
    have hxNeg : x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hx) hxNe
    by_cases hy : 0 < y
    · simp only [hullSixChamberLabelOfSigns, if_neg hx, if_pos hy,
        HullSixChamberLabel.Holds]
      exact ⟨(negative_iff_negative_floor hm hxFloor).1 hxNeg,
        (positive_iff_positive_floor hm hyFloor).1 hy⟩
    · have hyNe : y ≠ 0 := by
        intro hzero
        rw [hzero, abs_zero] at hyFloor
        exact (not_le_of_gt hm) hyFloor
      have hyNeg : y < 0 :=
        lt_of_le_of_ne (le_of_not_gt hy) hyNe
      simp only [hullSixChamberLabelOfSigns, if_neg hx, if_neg hy,
        HullSixChamberLabel.Holds]
      exact (negative_iff_negative_floor hm hyFloor).1 hyNeg

private def countFour (a b c d : Bool) : Fin 5 :=
  ⟨(if a then 1 else 0) + (if b then 1 else 0) +
      (if c then 1 else 0) + (if d then 1 else 0), by
    cases a <;> cases b <;> cases c <;> cases d <;> decide⟩

private def countThree (a b c : Bool) : Fin 4 :=
  ⟨(if a then 1 else 0) + (if b then 1 else 0) +
      (if c then 1 else 0), by
    cases a <;> cases b <;> cases c <;> decide⟩

private def boolWeight (b : Bool) : Nat :=
  if b then 1 else 0

private theorem boolWeight_le_one (b : Bool) : boolWeight b ≤ 1 := by
  cases b <;> decide

private def countFourL
    (a : Fin 4 → HullSixChamberLabel) : Fin 5 :=
  countFour (decide (a 0 = .L)) (decide (a 1 = .L))
    (decide (a 2 = .L)) (decide (a 3 = .L))

private def countFourNonR
    (a : Fin 4 → HullSixChamberLabel) : Fin 5 :=
  countFour (decide (a 0 ≠ .R)) (decide (a 1 ≠ .R))
    (decide (a 2 ≠ .R)) (decide (a 3 ≠ .R))

private def countThreeL
    (a : Fin 3 → HullSixChamberLabel) : Fin 4 :=
  countThree (decide (a 0 = .L)) (decide (a 1 = .L))
    (decide (a 2 = .L))

private def countThreeNonR
    (a : Fin 3 → HullSixChamberLabel) : Fin 4 :=
  countThree (decide (a 0 ≠ .R)) (decide (a 1 ≠ .R))
    (decide (a 2 ≠ .R))

private theorem countFour_mono
    {a0 a1 a2 a3 b0 b1 b2 b3 : Bool}
    (h0 : boolWeight a0 ≤ boolWeight b0)
    (h1 : boolWeight a1 ≤ boolWeight b1)
    (h2 : boolWeight a2 ≤ boolWeight b2)
    (h3 : boolWeight a3 ≤ boolWeight b3) :
    countFour a0 a1 a2 a3 ≤ countFour b0 b1 b2 b3 := by
  change boolWeight a0 + boolWeight a1 + boolWeight a2 + boolWeight a3 ≤
    boolWeight b0 + boolWeight b1 + boolWeight b2 + boolWeight b3
  exact add_le_add (add_le_add (add_le_add h0 h1) h2) h3

private theorem countThree_mono
    {a0 a1 a2 b0 b1 b2 : Bool}
    (h0 : boolWeight a0 ≤ boolWeight b0)
    (h1 : boolWeight a1 ≤ boolWeight b1)
    (h2 : boolWeight a2 ≤ boolWeight b2) :
    countThree a0 a1 a2 ≤ countThree b0 b1 b2 := by
  change boolWeight a0 + boolWeight a1 + boolWeight a2 ≤
    boolWeight b0 + boolWeight b1 + boolWeight b2
  exact add_le_add (add_le_add h0 h1) h2

/-- Both row-cut indicators are antitone in the chamber rank. -/
private theorem chamberIndicators_antitone
    {upper lower : HullSixChamberLabel}
    (h : hullSixChamberRank lower ≤ hullSixChamberRank upper) :
    boolWeight (decide (upper = .L)) ≤
        boolWeight (decide (lower = .L)) ∧
      boolWeight (decide (upper ≠ .R)) ≤
        boolWeight (decide (lower ≠ .R)) := by
  cases upper <;> cases lower <;>
    simp_all [hullSixChamberRank, boolWeight]

private theorem chamberLIndicator_le_nonR
    (a : HullSixChamberLabel) :
    boolWeight (decide (a = .L)) ≤
      boolWeight (decide (a ≠ .R)) := by
  cases a <;> decide

private theorem countFourL_le_nonR
    (a : Fin 4 → HullSixChamberLabel) :
    countFourL a ≤ countFourNonR a := by
  simpa [countFourL, countFourNonR] using
    (countFour_mono
      (chamberLIndicator_le_nonR (a 0))
      (chamberLIndicator_le_nonR (a 1))
      (chamberLIndicator_le_nonR (a 2))
      (chamberLIndicator_le_nonR (a 3)))

private theorem countThreeL_le_nonR
    (a : Fin 3 → HullSixChamberLabel) :
    countThreeL a ≤ countThreeNonR a := by
  simpa [countThreeL, countThreeNonR] using
    (countThree_mono
      (chamberLIndicator_le_nonR (a 0))
      (chamberLIndicator_le_nonR (a 1))
      (chamberLIndicator_le_nonR (a 2)))

private theorem countFour_antitone
    (upper lower : Fin 4 → HullSixChamberLabel)
    (h : ∀ j, hullSixChamberRank (lower j) ≤
      hullSixChamberRank (upper j)) :
    countFourL upper ≤ countFourL lower ∧
      countFourNonR upper ≤ countFourNonR lower := by
  have h0 := chamberIndicators_antitone (h 0)
  have h1 := chamberIndicators_antitone (h 1)
  have h2 := chamberIndicators_antitone (h 2)
  have h3 := chamberIndicators_antitone (h 3)
  constructor
  · simpa [countFourL] using
      (countFour_mono h0.1 h1.1 h2.1 h3.1)
  · simpa [countFourNonR] using
      (countFour_mono h0.2 h1.2 h2.2 h3.2)

private theorem countThree_antitone
    (upper lower : Fin 3 → HullSixChamberLabel)
    (h : ∀ j, hullSixChamberRank (lower j) ≤
      hullSixChamberRank (upper j)) :
    countThreeL upper ≤ countThreeL lower ∧
      countThreeNonR upper ≤ countThreeNonR lower := by
  have h0 := chamberIndicators_antitone (h 0)
  have h1 := chamberIndicators_antitone (h 1)
  have h2 := chamberIndicators_antitone (h 2)
  constructor
  · simpa [countThreeL] using
      (countThree_mono h0.1 h1.1 h2.1)
  · simpa [countThreeNonR] using
      (countThree_mono h0.2 h1.2 h2.2)

/-- A monotone four-cell row is recovered from its two indicator counts. -/
private theorem countFour_reconstruct
    (a : Fin 4 → HullSixChamberLabel)
    (h01 : hullSixChamberRank (a 0) ≤ hullSixChamberRank (a 1))
    (h12 : hullSixChamberRank (a 1) ≤ hullSixChamberRank (a 2))
    (h23 : hullSixChamberRank (a 2) ≤ hullSixChamberRank (a 3)) :
    ∀ j : Fin 4,
      (if j.val < (countFourL a).val then .L
       else if j.val < (countFourNonR a).val then .M else .R) = a j := by
  intro j
  fin_cases j <;>
    cases h0 : a 0 <;>
    cases h1 : a 1 <;>
    cases h2 : a 2 <;>
    cases h3 : a 3 <;>
    simp_all [countFourL, countFourNonR, countFour,
      hullSixChamberRank]

/-- A monotone three-cell row is recovered from its two indicator counts. -/
private theorem countThree_reconstruct
    (a : Fin 3 → HullSixChamberLabel)
    (h01 : hullSixChamberRank (a 0) ≤ hullSixChamberRank (a 1))
    (h12 : hullSixChamberRank (a 1) ≤ hullSixChamberRank (a 2)) :
    ∀ j : Fin 3,
      (if j.val < (countThreeL a).val then .L
       else if j.val < (countThreeNonR a).val then .M else .R) = a j := by
  intro j
  fin_cases j <;>
    cases h0 : a 0 <;>
    cases h1 : a 1 <;>
    cases h2 : a 2 <;>
    simp_all [countThreeL, countThreeNonR, countThree,
      hullSixChamberRank]

private theorem one_le_countFourL_of_first_L
    (a : Fin 4 → HullSixChamberLabel) (h : a 0 = .L) :
    (1 : Fin 5) ≤ countFourL a := by
  have hfirst : boolWeight (decide (a 0 = .L)) = 1 := by
    simp [h, boolWeight]
  change (1 : Nat) ≤
    boolWeight (decide (a 0 = .L)) +
      boolWeight (decide (a 1 = .L)) +
      boolWeight (decide (a 2 = .L)) +
      boolWeight (decide (a 3 = .L))
  rw [hfirst]
  omega

private theorem countFourNonR_le_three_of_last_R
    (a : Fin 4 → HullSixChamberLabel) (h : a 3 = .R) :
    countFourNonR a ≤ (3 : Fin 5) := by
  have h0 := boolWeight_le_one (decide (a 0 ≠ .R))
  have h1 := boolWeight_le_one (decide (a 1 ≠ .R))
  have h2 := boolWeight_le_one (decide (a 2 ≠ .R))
  have hlast : boolWeight (decide (a 3 ≠ .R)) = 0 := by
    simp [h, boolWeight]
  change
    boolWeight (decide (a 0 ≠ .R)) +
        boolWeight (decide (a 1 ≠ .R)) +
        boolWeight (decide (a 2 ≠ .R)) +
        boolWeight (decide (a 3 ≠ .R)) ≤ (3 : Nat)
  rw [hlast]
  omega

private theorem one_le_countThreeL_of_first_L
    (a : Fin 3 → HullSixChamberLabel) (h : a 0 = .L) :
    (1 : Fin 4) ≤ countThreeL a := by
  have hfirst : boolWeight (decide (a 0 = .L)) = 1 := by
    simp [h, boolWeight]
  change (1 : Nat) ≤
    boolWeight (decide (a 0 = .L)) +
      boolWeight (decide (a 1 = .L)) +
      boolWeight (decide (a 2 = .L))
  rw [hfirst]
  omega

private theorem countThreeNonR_le_two_of_last_R
    (a : Fin 3 → HullSixChamberLabel) (h : a 2 = .R) :
    countThreeNonR a ≤ (2 : Fin 4) := by
  have h0 := boolWeight_le_one (decide (a 0 ≠ .R))
  have h1 := boolWeight_le_one (decide (a 1 ≠ .R))
  have hlast : boolWeight (decide (a 2 ≠ .R)) = 0 := by
    simp [h, boolWeight]
  change
    boolWeight (decide (a 0 ≠ .R)) +
        boolWeight (decide (a 1 ≠ .R)) +
        boolWeight (decide (a 2 ≠ .R)) ≤ (2 : Nat)
  rw [hlast]
  omega

/-- Adjacent row and column order, plus the boundary cells, for `2 x 4`. -/
def HullSixTwoFourFerrersShape
    (A : Fin 2 -> Fin 4 -> HullSixChamberLabel) : Prop :=
  (∀ i : Fin 2,
    hullSixChamberRank (A i 0) <= hullSixChamberRank (A i 1) ∧
    hullSixChamberRank (A i 1) <= hullSixChamberRank (A i 2) ∧
    hullSixChamberRank (A i 2) <= hullSixChamberRank (A i 3)) ∧
  (∀ j : Fin 4,
    hullSixChamberRank (A 1 j) <= hullSixChamberRank (A 0 j)) ∧
  A 1 0 = .L ∧ A 0 3 = .R

/-- Count initial `L` cells and initial non-`R` cells in each row. -/
def hullSixTwoFourCutsOfTable
    (A : Fin 2 -> Fin 4 -> HullSixChamberLabel) :
    HullSixTwoFourCuts where
  p0 := countFour (decide (A 0 0 = .L)) (decide (A 0 1 = .L))
    (decide (A 0 2 = .L)) (decide (A 0 3 = .L))
  p1 := countFour (decide (A 1 0 = .L)) (decide (A 1 1 = .L))
    (decide (A 1 2 = .L)) (decide (A 1 3 = .L))
  q0 := countFour (decide (A 0 0 ≠ .R)) (decide (A 0 1 ≠ .R))
    (decide (A 0 2 ≠ .R)) (decide (A 0 3 ≠ .R))
  q1 := countFour (decide (A 1 0 ≠ .R)) (decide (A 1 1 ≠ .R))
    (decide (A 1 2 ≠ .R)) (decide (A 1 3 ≠ .R))

/-- Direct recognition of the `2 x 4` cut encoding, factored through its two
four-cell rows rather than enumeration of all `3^8` labeled tables. -/
theorem hullSixTwoFourCutsOfTable_spec :
    ∀ A : Fin 2 -> Fin 4 -> HullSixChamberLabel,
      HullSixTwoFourFerrersShape A ->
        (hullSixTwoFourCutsOfTable A).Legal ∧
        ∀ i j, (hullSixTwoFourCutsOfTable A).table i j = A i j := by
  intro A hshape
  rcases hshape with ⟨hrows, hcols, hbottom, htop⟩
  have hrow0 := countFour_reconstruct (A 0)
    (hrows 0).1 (hrows 0).2.1 (hrows 0).2.2
  have hrow1 := countFour_reconstruct (A 1)
    (hrows 1).1 (hrows 1).2.1 (hrows 1).2.2
  have hnested := countFour_antitone (A 0) (A 1) hcols
  refine ⟨?_, ?_⟩
  · change
      countFourL (A 0) ≤ countFourNonR (A 0) ∧
      countFourL (A 1) ≤ countFourNonR (A 1) ∧
      countFourL (A 0) ≤ countFourL (A 1) ∧
      countFourNonR (A 0) ≤ countFourNonR (A 1) ∧
      (1 : Fin 5) ≤ countFourL (A 1) ∧
      countFourNonR (A 0) ≤ (3 : Fin 5)
    exact ⟨countFourL_le_nonR (A 0), countFourL_le_nonR (A 1),
      hnested.1, hnested.2,
      one_le_countFourL_of_first_L (A 1) hbottom,
      countFourNonR_le_three_of_last_R (A 0) htop⟩
  · intro i j
    fin_cases i
    · change
        (if j.val < (countFourL (A 0)).val then .L
         else if j.val < (countFourNonR (A 0)).val then .M else .R) = A 0 j
      exact hrow0 j
    · change
        (if j.val < (countFourL (A 1)).val then .L
         else if j.val < (countFourNonR (A 1)).val then .M else .R) = A 1 j
      exact hrow1 j

/-- Adjacent row and column order, plus the boundary cells, for `3 x 3`. -/
def HullSixThreeThreeFerrersShape
    (A : Fin 3 -> Fin 3 -> HullSixChamberLabel) : Prop :=
  (∀ i : Fin 3,
    hullSixChamberRank (A i 0) <= hullSixChamberRank (A i 1) ∧
    hullSixChamberRank (A i 1) <= hullSixChamberRank (A i 2)) ∧
  (∀ j : Fin 3,
    hullSixChamberRank (A 1 j) <= hullSixChamberRank (A 0 j) ∧
    hullSixChamberRank (A 2 j) <= hullSixChamberRank (A 1 j)) ∧
  A 2 0 = .L ∧ A 0 2 = .R

/-- Count initial `L` cells and initial non-`R` cells in each row. -/
def hullSixThreeThreeCutsOfTable
    (A : Fin 3 -> Fin 3 -> HullSixChamberLabel) :
    HullSixThreeThreeCuts where
  p0 := countThree (decide (A 0 0 = .L)) (decide (A 0 1 = .L))
    (decide (A 0 2 = .L))
  p1 := countThree (decide (A 1 0 = .L)) (decide (A 1 1 = .L))
    (decide (A 1 2 = .L))
  p2 := countThree (decide (A 2 0 = .L)) (decide (A 2 1 = .L))
    (decide (A 2 2 = .L))
  q0 := countThree (decide (A 0 0 ≠ .R)) (decide (A 0 1 ≠ .R))
    (decide (A 0 2 ≠ .R))
  q1 := countThree (decide (A 1 0 ≠ .R)) (decide (A 1 1 ≠ .R))
    (decide (A 1 2 ≠ .R))
  q2 := countThree (decide (A 2 0 ≠ .R)) (decide (A 2 1 ≠ .R))
    (decide (A 2 2 ≠ .R))

/-- Direct recognition of the `3 x 3` cut encoding, factored through its three
three-cell rows rather than enumeration of all `3^9` labeled tables. -/
theorem hullSixThreeThreeCutsOfTable_spec :
    ∀ A : Fin 3 -> Fin 3 -> HullSixChamberLabel,
      HullSixThreeThreeFerrersShape A ->
        (hullSixThreeThreeCutsOfTable A).Legal ∧
        ∀ i j, (hullSixThreeThreeCutsOfTable A).table i j = A i j := by
  intro A hshape
  rcases hshape with ⟨hrows, hcols, hbottom, htop⟩
  have hrow0 := countThree_reconstruct (A 0)
    (hrows 0).1 (hrows 0).2
  have hrow1 := countThree_reconstruct (A 1)
    (hrows 1).1 (hrows 1).2
  have hrow2 := countThree_reconstruct (A 2)
    (hrows 2).1 (hrows 2).2
  have hnested01 := countThree_antitone (A 0) (A 1)
    (fun j => (hcols j).1)
  have hnested12 := countThree_antitone (A 1) (A 2)
    (fun j => (hcols j).2)
  refine ⟨?_, ?_⟩
  · change
      countThreeL (A 0) ≤ countThreeL (A 1) ∧
      countThreeL (A 1) ≤ countThreeL (A 2) ∧
      countThreeNonR (A 0) ≤ countThreeNonR (A 1) ∧
      countThreeNonR (A 1) ≤ countThreeNonR (A 2) ∧
      countThreeL (A 0) ≤ countThreeNonR (A 0) ∧
      countThreeL (A 1) ≤ countThreeNonR (A 1) ∧
      countThreeL (A 2) ≤ countThreeNonR (A 2) ∧
      (1 : Fin 4) ≤ countThreeL (A 2) ∧
      countThreeNonR (A 0) ≤ (2 : Fin 4)
    exact ⟨hnested01.1, hnested12.1, hnested01.2, hnested12.2,
      countThreeL_le_nonR (A 0), countThreeL_le_nonR (A 1),
      countThreeL_le_nonR (A 2),
      one_le_countThreeL_of_first_L (A 2) hbottom,
      countThreeNonR_le_two_of_last_R (A 0) htop⟩
  · intro i j
    fin_cases i
    · change
        (if j.val < (countThreeL (A 0)).val then .L
         else if j.val < (countThreeNonR (A 0)).val then .M else .R) = A 0 j
      exact hrow0 j
    · change
        (if j.val < (countThreeL (A 1)).val then .L
         else if j.val < (countThreeNonR (A 1)).val then .M else .R) = A 1 j
      exact hrow1 j
    · change
        (if j.val < (countThreeL (A 2)).val then .L
         else if j.val < (countThreeNonR (A 2)).val then .M else .R) = A 2 j
      exact hrow2 j

/-! ## Coordinate-free sign propagation -/

/-- Moving forward on the lower block, based at either endpoint of `PQ`. -/
private lemma lowerBlock_transport_identity
    (P Q B U L0 L1 : Prod Real Real) (hB : B = P ∨ B = Q) :
    (-sig P Q L1) * sig B U L0 -
        (-sig P Q L0) * sig B U L1 =
      sig P Q U * sig B L0 L1 := by
  rcases hB with rfl | rfl <;> simp only [sig] <;> ring

/-- Moving forward on the upper block, based at either endpoint of `PQ`. -/
private lemma upperBlock_transport_identity
    (P Q B U0 U1 L : Prod Real Real) (hB : B = P ∨ B = Q) :
    sig P Q U0 * sig B U1 L -
        sig P Q U1 * sig B U0 L =
      (-sig P Q L) * sig B U0 U1 := by
  rcases hB with rfl | rfl <;> simp only [sig] <;> ring

/-- Cross-chord floors are invariant under the selected orientation of the
two off-cycle points. -/
private theorem crossFloors_of_orientedPair
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hpair : HullSixIsOrientedPair p q P Q)
    {i j : Fin 6} (hij : i ≠ j) :
    minTri cfg <= |sig (cfg P) (cfg (cycle i)) (cfg (cycle j))| ∧
    minTri cfg <= |sig (cfg Q) (cfg (cycle i)) (cfg (cycle j))| := by
  have h := R.crossChord i j hij
  rcases hpair with hforward | hswap
  · rcases hforward with ⟨rfl, rfl⟩
    exact ⟨h.1, h.2.1⟩
  · rcases hswap with ⟨rfl, rfl⟩
    exact ⟨h.2.1, h.1⟩

/-- Positivity at a later lower vertex propagates backward along the lower
block. -/
private theorem lowerBlock_positive_backward
    (P Q B U L0 L1 : Prod Real Real) (hB : B = P ∨ B = Q)
    (hu : 0 < sig P Q U) (hL0 : sig P Q L0 < 0)
    (hL1 : sig P Q L1 < 0) (hEdge : 0 < sig B L0 L1)
    (hLater : 0 < sig B U L1) :
    0 < sig B U L0 := by
  have hv0 : 0 < -sig P Q L0 := by linarith
  have hv1 : 0 < -sig P Q L1 := by linarith
  have hdiff :
      0 < (-sig P Q L1) * sig B U L0 -
        (-sig P Q L0) * sig B U L1 := by
    rw [lowerBlock_transport_identity P Q B U L0 L1 hB]
    exact mul_pos hu hEdge
  exact positive_of_nonnegative_scaled_difference
    hv1 hv0 (le_of_lt hLater) hdiff

/-- Positivity at an earlier upper vertex propagates forward along the
upper block. -/
private theorem upperBlock_positive_forward
    (P Q B U0 U1 L : Prod Real Real) (hB : B = P ∨ B = Q)
    (hU0 : 0 < sig P Q U0) (hU1 : 0 < sig P Q U1)
    (hL : sig P Q L < 0) (hEdge : 0 < sig B U0 U1)
    (hEarlier : 0 < sig B U0 L) :
    0 < sig B U1 L := by
  have hv : 0 < -sig P Q L := by linarith
  have hdiff :
      0 < sig P Q U0 * sig B U1 L -
        sig P Q U1 * sig B U0 L := by
    rw [upperBlock_transport_identity P Q B U0 U1 L hB]
    exact mul_pos hv hEdge
  exact positive_of_nonnegative_scaled_difference
    hU0 hU1 (le_of_lt hEarlier) hdiff

/-! ## Provider-facing normalized packets -/

/-- All semantic inputs consumed by a compact `2 x 4` provider. -/
def HullSixTwoFourFerrersInput
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q) : Prop :=
  ∃ P Q : Fin 8,
    HullSixIsOrientedPair p q P Q ∧
    HullSixOrientedView cfg cycle P Q ∧
    ∃ rotation : Fin 6, ∃ T : HullSixTwoFourCuts,
      (∀ i : Fin 2,
        0 < sig (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))) ∧
      (∀ j : Fin 4,
        sig (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0) ∧
      T.Legal ∧
      ∀ i j,
        HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
          (sig (cfg P)
            (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
            (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
          (sig (cfg Q)
            (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
            (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))

/-- All semantic inputs consumed by a compact `3 x 3` provider. -/
def HullSixThreeThreeFerrersInput
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q) : Prop :=
  ∃ P Q : Fin 8,
    HullSixIsOrientedPair p q P Q ∧
    HullSixOrientedView cfg cycle P Q ∧
    ∃ rotation : Fin 6, ∃ T : HullSixThreeThreeCuts,
      (∀ i : Fin 3,
        0 < sig (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))) ∧
      (∀ j : Fin 3,
        sig (cfg P) (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0) ∧
      T.Legal ∧
      ∀ i j,
        HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
          (sig (cfg P)
            (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
            (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
          (sig (cfg Q)
            (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
            (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))

namespace HullSixCompactCrossChordResidual

/-! ## Geometric extraction of the `2 x 4` table -/

/-- An oriented `2 + 4` frame canonically determines a legal `2 x 4`
Ferrers table, with every cell carrying its exact absolute-floor chamber. -/
theorem twoFourFerrersTable_exists
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hpair : HullSixIsOrientedPair p q P Q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 2,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i))))
    (hlower : ∀ j : Fin 4,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0) :
    ∃ T : HullSixTwoFourCuts,
      T.Legal ∧
      ∀ i j,
        HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
          (sig (cfg P)
            (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
            (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
          (sig (cfg Q)
            (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
            (cfg (cycle (rotation + hullSixTwoFourLowerOffset j)))) := by
  let U : Fin 2 -> Prod Real Real := fun i =>
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 -> Prod Real Real := fun j =>
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let X : Fin 2 -> Fin 4 -> Real := fun i j => sig (cfg P) (U i) (L j)
  let Y : Fin 2 -> Fin 4 -> Real := fun i j => sig (cfg Q) (U i) (L j)
  let A : Fin 2 -> Fin 4 -> HullSixChamberLabel := fun i j =>
    hullSixChamberLabelOfSigns (X i j) (Y i j)

  have hLowerNext (j : Fin 3) :
      hullSixTwoFourLowerOffset j.castSucc + 1 =
        hullSixTwoFourLowerOffset j.succ := by
    fin_cases j <;> decide
  have hUpperNext :
      hullSixTwoFourUpperOffset (0 : Fin 2) + 1 =
        hullSixTwoFourUpperOffset (1 : Fin 2) := by
    decide

  have hrowX (i : Fin 2) (j : Fin 3) :
      0 < X i j.succ -> 0 < X i j.castSucc := by
    intro hx
    have hEdge : 0 < sig (cfg P) (L j.castSucc) (L j.succ) := by
      have h := V.P_boundary_pos
        (rotation + hullSixTwoFourLowerOffset j.castSucc)
      simpa [L, add_assoc, hLowerNext j] using h
    simpa [X, U, L] using lowerBlock_positive_backward
      (cfg P) (cfg Q) (cfg P) (U i) (L j.castSucc) (L j.succ)
      (Or.inl rfl) (hupper i) (hlower j.castSucc) (hlower j.succ)
      hEdge hx

  have hrowY (i : Fin 2) (j : Fin 3) :
      0 < Y i j.succ -> 0 < Y i j.castSucc := by
    intro hy
    have hEdge : 0 < sig (cfg Q) (L j.castSucc) (L j.succ) := by
      have h := V.Q_boundary_pos
        (rotation + hullSixTwoFourLowerOffset j.castSucc)
      simpa [L, add_assoc, hLowerNext j] using h
    simpa [Y, U, L] using lowerBlock_positive_backward
      (cfg P) (cfg Q) (cfg Q) (U i) (L j.castSucc) (L j.succ)
      (Or.inr rfl) (hupper i) (hlower j.castSucc) (hlower j.succ)
      hEdge hy

  have hcolX (j : Fin 4) : 0 < X 0 j -> 0 < X 1 j := by
    intro hx
    have hEdge : 0 < sig (cfg P) (U 0) (U 1) := by
      have h := V.P_boundary_pos
        (rotation + hullSixTwoFourUpperOffset 0)
      simpa [U, add_assoc, hUpperNext] using h
    simpa [X, U, L] using upperBlock_positive_forward
      (cfg P) (cfg Q) (cfg P) (U 0) (U 1) (L j)
      (Or.inl rfl) (hupper 0) (hupper 1) (hlower j) hEdge hx

  have hcolY (j : Fin 4) : 0 < Y 0 j -> 0 < Y 1 j := by
    intro hy
    have hEdge : 0 < sig (cfg Q) (U 0) (U 1) := by
      have h := V.Q_boundary_pos
        (rotation + hullSixTwoFourUpperOffset 0)
      simpa [U, add_assoc, hUpperNext] using h
    simpa [Y, U, L] using upperBlock_positive_forward
      (cfg P) (cfg Q) (cfg Q) (U 0) (U 1) (L j)
      (Or.inr rfl) (hupper 0) (hupper 1) (hlower j) hEdge hy

  have hbottom : A 1 0 = .L := by
    have hx : 0 < X 1 0 := by
      have h := V.P_boundary_pos
        (rotation + hullSixTwoFourUpperOffset 1)
      simpa [X, U, L, hullSixTwoFourUpperOffset,
        hullSixTwoFourLowerOffset, add_assoc] using h
    simp [A, hullSixChamberLabelOfSigns, hx]

  have htop : A 0 3 = .R := by
    have hyNeg : Y 0 3 < 0 := by
      have hclose : 0 < sig (cfg Q) (L 3) (U 0) := by
        have h := V.Q_boundary_pos
          (rotation + hullSixTwoFourLowerOffset 3)
        simpa [U, L, hullSixTwoFourUpperOffset,
          hullSixTwoFourLowerOffset, add_assoc] using h
      dsimp [Y]
      rw [sig_swap]
      linarith
    have hxNeg : X 0 3 < 0 := by
      have hbase := sig_crossChord_base_change
        (cfg P) (cfg Q) (U 0) (L 3)
      have hu0 : 0 < sig (cfg P) (cfg Q) (U 0) := by
        simpa [U] using hupper 0
      have hl3 : sig (cfg P) (cfg Q) (L 3) < 0 := by
        simpa [L] using hlower 3
      dsimp [X]
      linarith [hbase, hu0, hl3]
    simp [A, hullSixChamberLabelOfSigns,
      not_lt_of_ge hxNeg.le, not_lt_of_ge hyNeg.le]

  have hshape : HullSixTwoFourFerrersShape A := by
    refine ⟨?_, ?_, hbottom, htop⟩
    · intro i
      exact ⟨chamberRank_le_of_positive_implications
          (hrowX i 0) (hrowY i 0),
        chamberRank_le_of_positive_implications
          (hrowX i 1) (hrowY i 1),
        chamberRank_le_of_positive_implications
          (hrowX i 2) (hrowY i 2)⟩
    · intro j
      exact chamberRank_le_of_positive_implications (hcolX j) (hcolY j)

  let T := hullSixTwoFourCutsOfTable A
  have hspec := hullSixTwoFourCutsOfTable_spec A hshape
  refine ⟨T, hspec.1, ?_⟩
  intro i j
  rw [show T.table i j = A i j by exact hspec.2 i j]
  have hneq :
      rotation + hullSixTwoFourUpperOffset i ≠
        rotation + hullSixTwoFourLowerOffset j := by
    intro h
    have hoff : hullSixTwoFourUpperOffset i ≠
        hullSixTwoFourLowerOffset j := by
      fin_cases i <;> fin_cases j <;> decide
    exact hoff (add_left_cancel h)
  have hfloors := crossFloors_of_orientedPair R hpair hneq
  apply chamberLabelOfSigns_holds R.minTri_pos
  · simpa [X, U, L] using hfloors.1
  · simpa [Y, U, L] using hfloors.2

/-! ## Geometric extraction of the `3 x 3` table -/

/-- An oriented `3 + 3` frame canonically determines a legal `3 x 3`
Ferrers table. -/
theorem threeThreeFerrersTable_exists
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hpair : HullSixIsOrientedPair p q P Q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0) :
    ∃ T : HullSixThreeThreeCuts,
      T.Legal ∧
      ∀ i j,
        HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
          (sig (cfg P)
            (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
            (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
          (sig (cfg Q)
            (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
            (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j)))) := by
  let U : Fin 3 -> Prod Real Real := fun i =>
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 -> Prod Real Real := fun j =>
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let X : Fin 3 -> Fin 3 -> Real := fun i j => sig (cfg P) (U i) (L j)
  let Y : Fin 3 -> Fin 3 -> Real := fun i j => sig (cfg Q) (U i) (L j)
  let A : Fin 3 -> Fin 3 -> HullSixChamberLabel := fun i j =>
    hullSixChamberLabelOfSigns (X i j) (Y i j)

  have hLowerNext (j : Fin 2) :
      hullSixThreeThreeLowerOffset j.castSucc + 1 =
        hullSixThreeThreeLowerOffset j.succ := by
    fin_cases j <;> decide
  have hUpperNext (i : Fin 2) :
      hullSixThreeThreeUpperOffset i.castSucc + 1 =
        hullSixThreeThreeUpperOffset i.succ := by
    fin_cases i <;> decide

  have hrowX (i : Fin 3) (j : Fin 2) :
      0 < X i j.succ -> 0 < X i j.castSucc := by
    intro hx
    have hEdge : 0 < sig (cfg P) (L j.castSucc) (L j.succ) := by
      have h := V.P_boundary_pos
        (rotation + hullSixThreeThreeLowerOffset j.castSucc)
      simpa [L, add_assoc, hLowerNext j] using h
    simpa [X, U, L] using lowerBlock_positive_backward
      (cfg P) (cfg Q) (cfg P) (U i) (L j.castSucc) (L j.succ)
      (Or.inl rfl) (hupper i) (hlower j.castSucc) (hlower j.succ)
      hEdge hx

  have hrowY (i : Fin 3) (j : Fin 2) :
      0 < Y i j.succ -> 0 < Y i j.castSucc := by
    intro hy
    have hEdge : 0 < sig (cfg Q) (L j.castSucc) (L j.succ) := by
      have h := V.Q_boundary_pos
        (rotation + hullSixThreeThreeLowerOffset j.castSucc)
      simpa [L, add_assoc, hLowerNext j] using h
    simpa [Y, U, L] using lowerBlock_positive_backward
      (cfg P) (cfg Q) (cfg Q) (U i) (L j.castSucc) (L j.succ)
      (Or.inr rfl) (hupper i) (hlower j.castSucc) (hlower j.succ)
      hEdge hy

  have hcolX (i : Fin 2) (j : Fin 3) :
      0 < X i.castSucc j -> 0 < X i.succ j := by
    intro hx
    have hEdge : 0 < sig (cfg P) (U i.castSucc) (U i.succ) := by
      have h := V.P_boundary_pos
        (rotation + hullSixThreeThreeUpperOffset i.castSucc)
      simpa [U, add_assoc, hUpperNext i] using h
    simpa [X, U, L] using upperBlock_positive_forward
      (cfg P) (cfg Q) (cfg P) (U i.castSucc) (U i.succ) (L j)
      (Or.inl rfl) (hupper i.castSucc) (hupper i.succ) (hlower j)
      hEdge hx

  have hcolY (i : Fin 2) (j : Fin 3) :
      0 < Y i.castSucc j -> 0 < Y i.succ j := by
    intro hy
    have hEdge : 0 < sig (cfg Q) (U i.castSucc) (U i.succ) := by
      have h := V.Q_boundary_pos
        (rotation + hullSixThreeThreeUpperOffset i.castSucc)
      simpa [U, add_assoc, hUpperNext i] using h
    simpa [Y, U, L] using upperBlock_positive_forward
      (cfg P) (cfg Q) (cfg Q) (U i.castSucc) (U i.succ) (L j)
      (Or.inr rfl) (hupper i.castSucc) (hupper i.succ) (hlower j)
      hEdge hy

  have hbottom : A 2 0 = .L := by
    have hx : 0 < X 2 0 := by
      have h := V.P_boundary_pos
        (rotation + hullSixThreeThreeUpperOffset 2)
      simpa [X, U, L, hullSixThreeThreeUpperOffset,
        hullSixThreeThreeLowerOffset, add_assoc] using h
    simp [A, hullSixChamberLabelOfSigns, hx]

  have htop : A 0 2 = .R := by
    have hyNeg : Y 0 2 < 0 := by
      have hclose : 0 < sig (cfg Q) (L 2) (U 0) := by
        have h := V.Q_boundary_pos
          (rotation + hullSixThreeThreeLowerOffset 2)
        simpa [U, L, hullSixThreeThreeUpperOffset,
          hullSixThreeThreeLowerOffset, add_assoc] using h
      dsimp [Y]
      rw [sig_swap]
      linarith
    have hxNeg : X 0 2 < 0 := by
      have hbase := sig_crossChord_base_change
        (cfg P) (cfg Q) (U 0) (L 2)
      have hu0 : 0 < sig (cfg P) (cfg Q) (U 0) := by
        simpa [U] using hupper 0
      have hl2 : sig (cfg P) (cfg Q) (L 2) < 0 := by
        simpa [L] using hlower 2
      dsimp [X]
      linarith [hbase, hu0, hl2]
    simp [A, hullSixChamberLabelOfSigns,
      not_lt_of_ge hxNeg.le, not_lt_of_ge hyNeg.le]

  have hshape : HullSixThreeThreeFerrersShape A := by
    refine ⟨?_, ?_, hbottom, htop⟩
    · intro i
      exact ⟨chamberRank_le_of_positive_implications
          (hrowX i 0) (hrowY i 0),
        chamberRank_le_of_positive_implications
          (hrowX i 1) (hrowY i 1)⟩
    · intro j
      exact ⟨chamberRank_le_of_positive_implications
          (hcolX 0 j) (hcolY 0 j),
        chamberRank_le_of_positive_implications
          (hcolX 1 j) (hcolY 1 j)⟩

  let T := hullSixThreeThreeCutsOfTable A
  have hspec := hullSixThreeThreeCutsOfTable_spec A hshape
  refine ⟨T, hspec.1, ?_⟩
  intro i j
  rw [show T.table i j = A i j by exact hspec.2 i j]
  have hneq :
      rotation + hullSixThreeThreeUpperOffset i ≠
        rotation + hullSixThreeThreeLowerOffset j := by
    intro h
    have hoff : hullSixThreeThreeUpperOffset i ≠
        hullSixThreeThreeLowerOffset j := by
      fin_cases i <;> fin_cases j <;> decide
    exact hoff (add_left_cancel h)
  have hfloors := crossFloors_of_orientedPair R hpair hneq
  apply chamberLabelOfSigns_holds R.minTri_pos
  · simpa [X, U, L] using hfloors.1
  · simpa [Y, U, L] using hfloors.2

/-! ## From split views to provider packets -/

/-- The `last = 1` sign block supplies the complete `2 x 4` packet. -/
theorem twoFourFerrersInput_of_split
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hsplit : HullSixSplitResidualViewAt R 1) :
    HullSixTwoFourFerrersInput R := by
  obtain ⟨P, Q, hpair, V, rotation, hpositive, hnegative⟩ := hsplit
  have hupper : ∀ i : Fin 2,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i))) := by
    intro i
    exact hpositive (hullSixTwoFourUpperOffset i) (by
      simp [hullSixTwoFourUpperOffset] <;> omega)
  have hlower : ∀ j : Fin 4,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0 := by
    intro j
    exact hnegative (hullSixTwoFourLowerOffset j) (by
      simp [hullSixTwoFourLowerOffset] <;> omega)
  obtain ⟨T, hLegal, hTable⟩ :=
    R.twoFourFerrersTable_exists hpair V rotation hupper hlower
  exact ⟨P, Q, hpair, V, rotation, T,
    hupper, hlower, hLegal, hTable⟩

/-- The `last = 2` sign block supplies the complete `3 x 3` packet. -/
theorem threeThreeFerrersInput_of_split
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (hsplit : HullSixSplitResidualViewAt R 2) :
    HullSixThreeThreeFerrersInput R := by
  obtain ⟨P, Q, hpair, V, rotation, hpositive, hnegative⟩ := hsplit
  have hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))) := by
    intro i
    exact hpositive (hullSixThreeThreeUpperOffset i) (by
      simp [hullSixThreeThreeUpperOffset] <;> omega)
  have hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0 := by
    intro j
    exact hnegative (hullSixThreeThreeLowerOffset j) (by
      simp [hullSixThreeThreeLowerOffset] <;> omega)
  obtain ⟨T, hLegal, hTable⟩ :=
    R.threeThreeFerrersTable_exists hpair V rotation hupper hlower
  exact ⟨P, Q, hpair, V, rotation, T,
    hupper, hlower, hLegal, hTable⟩

/-- Every compact residual reaches one of the two honest Ferrers packets.
The `1 + 5` branch has already been contradicted by the sign-block adapter. -/
theorem twoFour_or_threeThreeFerrersInput
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q) :
    HullSixTwoFourFerrersInput R ∨ HullSixThreeThreeFerrersInput R := by
  rcases R.twoFour_or_threeThreeResidualView with h24 | h33
  · exact Or.inl (R.twoFourFerrersInput_of_split h24)
  · exact Or.inr (R.threeThreeFerrersInput_of_split h33)

end HullSixCompactCrossChordResidual

/-! ## Direct geometric hull-six endpoint -/

/-- Closure contract expected from the compact `2 x 4` provider. -/
def HullSixTwoFourFerrersClosed : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q),
      HullSixTwoFourFerrersInput R -> False

/-- Closure contract expected from the compact `3 x 3` provider. -/
def HullSixThreeThreeFerrersClosed : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q),
      HullSixThreeThreeFerrersInput R -> False

/-- Ferrers packet closures imply the existing oriented packet closures. -/
theorem hullSixOrientedPacketsClosed_of_ferrersClosed
    (hTwoFour : HullSixTwoFourFerrersClosed)
    (hThreeThree : HullSixThreeThreeFerrersClosed) :
    HullSixTwoFourOrientedClosed ∧ HullSixThreeThreeOrientedClosed := by
  constructor
  · intro cfg cycle p q R hsplit
    exact hTwoFour R (R.twoFourFerrersInput_of_split hsplit)
  · intro cfg cycle p q R hsplit
    exact hThreeThree R (R.threeThreeFerrersInput_of_split hsplit)

/-- Production-free h=6 theorem.  Its only hypotheses are the two compact
Ferrers provider closures. -/
theorem geometricHullSixExclusion_of_ferrersClosed
    (hTwoFour : HullSixTwoFourFerrersClosed)
    (hThreeThree : HullSixThreeThreeFerrersClosed) :
    GeometricHullSizeExclusion 6 StrictXOrder := by
  obtain ⟨h24, h33⟩ :=
    hullSixOrientedPacketsClosed_of_ferrersClosed hTwoFour hThreeThree
  exact geometricHullSixExclusion_of_orientedPackets h24 h33

end Heilbronn8
