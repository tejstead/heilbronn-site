import Heilbronn8.Survivors.Join.HullSixFerrersSymmetry

/-!
# Scalar sign propagation behind hull-six Ferrers tableaux

The geometry-to-tableau adapter does not need a coordinate normalization.
For positive levels `a,b,v` and a positive same-side determinant `E`, the
linear Plucker identity

```text
a * y - b * x = v * E
```

shows that positivity of `x` propagates to `y`.  Applied down adjacent rows
and, in the opposite orientation, left across adjacent columns, this proves
that both the `P`- and `Q`-positive cells are nested initial segments.  The
lemmas below isolate that argument from all finite-index bookkeeping.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- A positive scaled difference transports even nonnegativity to strict
positivity. -/
theorem positive_of_nonnegative_scaled_difference
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hdiff : 0 < a * y - b * x) :
    0 < y := by
  by_contra hnot
  have hy : y ≤ 0 := le_of_not_gt hnot
  have hay : a * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hy
  have hbx : 0 ≤ b * x := mul_nonneg (le_of_lt hb) hx
  linarith

/-- Strict-positive specialization of the preceding transport lemma. -/
theorem positive_of_positive_scaled_difference
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (hdiff : 0 < a * y - b * x) :
    0 < y :=
  positive_of_nonnegative_scaled_difference ha hb (le_of_lt hx) hdiff

/-- Contrapositive-oriented companion: if the later scaled value is
nonpositive, then the earlier one is strictly negative. -/
theorem negative_of_nonpositive_scaled_difference
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : y ≤ 0)
    (hdiff : 0 < a * y - b * x) :
    x < 0 := by
  by_contra hnot
  have hx : 0 ≤ x := le_of_not_gt hnot
  have hay : a * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hy
  have hbx : 0 ≤ b * x := mul_nonneg (le_of_lt hb) hx
  linarith

/-- An exact Plucker identity with positive right-hand side propagates a
positive cross-chord determinant down a row index. -/
theorem positive_of_plucker_transport
    {a b v E x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hE : 0 < E)
    (hx : 0 < x) (hidentity : a * y - b * x = v * E) :
    0 < y := by
  apply positive_of_nonnegative_scaled_difference ha hb (le_of_lt hx)
  rw [hidentity]
  exact mul_pos hv hE

/-- A nonzero absolute floor identifies positivity with the positive signed
floor. -/
theorem positive_iff_positive_floor
    {m x : ℝ} (hm : 0 < m) (hfloor : m ≤ |x|) :
    0 < x ↔ m ≤ x := by
  constructor
  · intro hx
    simpa [abs_of_pos hx] using hfloor
  · intro hx
    exact lt_of_lt_of_le hm hx

/-- The analogous negative half of a nonzero absolute floor. -/
theorem negative_iff_negative_floor
    {m x : ℝ} (hm : 0 < m) (hfloor : m ≤ |x|) :
    x < 0 ↔ x ≤ -m := by
  constructor
  · intro hx
    rw [abs_of_neg hx] at hfloor
    linarith
  · intro hx
    linarith

/-- In an `L` cell, base change and the two line-level floors strengthen the
`Q`-based determinant from `m` to `3m`. -/
theorem chamberLabel_L_qDet_ge_three
    {m u v x y : ℝ} (hu : m ≤ u) (hv : m ≤ v)
    (hbase : y = x + u + v)
    (hL : HullSixChamberLabel.Holds HullSixChamberLabel.L m x y) :
    3 * m ≤ y := by
  simp only [HullSixChamberLabel.Holds] at hL
  rw [hbase]
  linarith

/-- In an `R` cell, the same base change strengthens the `P`-based
determinant to at most `-3m`. -/
theorem chamberLabel_R_pDet_le_neg_three
    {m u v x y : ℝ} (hu : m ≤ u) (hv : m ≤ v)
    (hbase : y = x + u + v)
    (hR : HullSixChamberLabel.Holds HullSixChamberLabel.R m x y) :
    x ≤ -3 * m := by
  simp only [HullSixChamberLabel.Holds] at hR
  rw [hbase] at hR
  linarith

/-- The `X`-side hypotheses retained by a q-blind frontier lemma.  They know
the first cut `p`, but use the second cut only through one fixed frontier
`qFront`: cells beyond that frontier have the strengthened `R` bound. -/
def HullSixQBlindFrontierHolds {r s : ℕ}
    (p qFront : Fin r → ℕ) (m : ℝ)
    (X : Fin r → Fin s → ℝ) : Prop :=
  (∀ i j, j.val < p i → m ≤ X i j) ∧
  (∀ i j, p i ≤ j.val → X i j ≤ -m) ∧
  (∀ i j, qFront i ≤ j.val → X i j ≤ -3 * m)

/-- Lowering the second row cut only turns `M` cells into the stronger `R`
cells.  Consequently every table with `q <= qFront` satisfies the same
q-blind frontier package.  This is the logical monotonicity bridge; it does
not discard any separately supplied `Q`-side absolute floors or fan facts. -/
theorem qBlindFrontierHolds_of_ferrers
    {r s : ℕ} {p q qFront : Fin r → ℕ}
    {m : ℝ} {u : Fin r → ℝ} {v : Fin s → ℝ}
    {X Y : Fin r → Fin s → ℝ}
    (hm : 0 ≤ m) (hpq : ∀ i, p i ≤ q i)
    (hfront : ∀ i, q i ≤ qFront i)
    (hu : ∀ i, m ≤ u i) (hv : ∀ j, m ≤ v j)
    (hbase : ∀ i j, Y i j = X i j + u i + v j)
    (hholds : ∀ i j, HullSixChamberLabel.Holds
      (hullSixFerrersLabel p q i j) m (X i j) (Y i j)) :
    HullSixQBlindFrontierHolds p qFront m X := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj
    have htag := hholds i j
    simp only [hullSixFerrersLabel, if_pos hj,
      HullSixChamberLabel.Holds] at htag
    exact htag
  · intro i j hj
    have hjNot : ¬j.val < p i := by omega
    by_cases hjq : j.val < q i
    · have htag := hholds i j
      simp only [hullSixFerrersLabel, if_neg hjNot, if_pos hjq,
        HullSixChamberLabel.Holds] at htag
      exact htag.1
    · have htag := hholds i j
      simp only [hullSixFerrersLabel, if_neg hjNot, if_neg hjq,
        HullSixChamberLabel.Holds] at htag
      have hstrong := chamberLabel_R_pDet_le_neg_three
        (hu i) (hv j) (hbase i j) htag
      linarith
  · intro i j hj
    have hjq : ¬j.val < q i := by
      have := hfront i
      omega
    have hjp : ¬j.val < p i := by
      have := hpq i
      have := hfront i
      omega
    have htag := hholds i j
    simp only [hullSixFerrersLabel, if_neg hjp, if_neg hjq,
      HullSixChamberLabel.Holds] at htag
    exact chamberLabel_R_pDet_le_neg_three
      (hu i) (hv j) (hbase i j) htag

/-- With positive separation `x < y` and both absolute floors, exactly one
of the three data-valued chamber labels applies. -/
theorem chamberLabel_existsUnique
    {m x y : ℝ} (hm : 0 < m) (hxFloor : m ≤ |x|)
    (hyFloor : m ≤ |y|) (hxy : x < y) :
    ∃! tag : HullSixChamberLabel, HullSixChamberLabel.Holds tag m x y := by
  have hxCases : m ≤ x ∨ x ≤ -m := by
    by_cases hx : 0 ≤ x
    · left
      simpa [abs_of_nonneg hx] using hxFloor
    · right
      have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx'] at hxFloor
      linarith
  have hyCases : m ≤ y ∨ y ≤ -m := by
    by_cases hy : 0 ≤ y
    · left
      simpa [abs_of_nonneg hy] using hyFloor
    · right
      have hy' : y ≤ 0 := le_of_not_ge hy
      rw [abs_of_nonpos hy'] at hyFloor
      linarith
  rcases hxCases with hx | hx
  · refine ⟨HullSixChamberLabel.L, ?_, ?_⟩
    · exact hx
    · intro tag htag
      cases tag
      · rfl
      · simp only [HullSixChamberLabel.Holds] at htag
        exfalso
        linarith
      · simp only [HullSixChamberLabel.Holds] at htag
        exfalso
        linarith
  · rcases hyCases with hy | hy
    · refine ⟨HullSixChamberLabel.M, ⟨hx, hy⟩, ?_⟩
      intro tag htag
      cases tag
      · simp only [HullSixChamberLabel.Holds] at htag
        exfalso
        linarith
      · rfl
      · simp only [HullSixChamberLabel.Holds] at htag
        exfalso
        linarith
    · refine ⟨HullSixChamberLabel.R, hy, ?_⟩
      intro tag htag
      cases tag
      · simp only [HullSixChamberLabel.Holds] at htag
        exfalso
        linarith
      · simp only [HullSixChamberLabel.Holds] at htag
        exfalso
        linarith
      · rfl

end Heilbronn8
