import Heilbronn8.Survivors.Join.HullSixFerrersPropagation
import Heilbronn8.Survivors.Join.HullSixTwoFourLocalProduct

/-!
# Chamber adapter for the local product-twelve closure

This is the dimension-independent scalar seam used by both `2 + 4` and
`3 + 3`.  A local adjacent block closes when its chamber rows are either

```text
R R       L R
L R   or  L L.
```

The first pattern gives a `P`-Plucker product of at least `12 m^2`; the
second gives the same bound in the `Q`-fan.  The predicate below records the
already-strengthened determinant inequalities, so a geometric caller may
recognize a block without enumerating any global tableau label.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The two distinguished adjacent `2 x 2` cell patterns. -/
def HullSixLocalProductTwelveCells
    (a b c d : HullSixChamberLabel) : Prop :=
  (a = HullSixChamberLabel.R ∧ b = HullSixChamberLabel.R ∧
      c = HullSixChamberLabel.L ∧ d = HullSixChamberLabel.R) ∨
  (a = HullSixChamberLabel.L ∧ b = HullSixChamberLabel.R ∧
      c = HullSixChamberLabel.L ∧ d = HullSixChamberLabel.L)

/-- Complement-rotation exchanges the two local patterns. -/
theorem hullSixLocalProductTwelveCells_rotateComplement
    (a b c d : HullSixChamberLabel) :
    HullSixLocalProductTwelveCells
      (HullSixChamberLabel.complement d)
      (HullSixChamberLabel.complement c)
      (HullSixChamberLabel.complement b)
      (HullSixChamberLabel.complement a) ↔
    HullSixLocalProductTwelveCells a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [HullSixLocalProductTwelveCells, HullSixChamberLabel.complement]

/-- Complement-transposition also exchanges the two local patterns. -/
theorem hullSixLocalProductTwelveCells_complementTranspose
    (a b c d : HullSixChamberLabel) :
    HullSixLocalProductTwelveCells
      (HullSixChamberLabel.complement a)
      (HullSixChamberLabel.complement c)
      (HullSixChamberLabel.complement b)
      (HullSixChamberLabel.complement d) ↔
    HullSixLocalProductTwelveCells a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [HullSixLocalProductTwelveCells, HullSixChamberLabel.complement]

/-- A finite chamber table contains one of the two adjacent local patterns.
This predicate recognizes the whole easy family without listing global row
cuts.  Adjacency is expressed on `Fin` values to keep the definition uniform
for both `2 x 4` and `3 x 3`. -/
def HullSixTableHasLocalProductTwelvePattern {r s : ℕ}
    (T : Fin r → Fin s → HullSixChamberLabel) : Prop :=
  ∃ i0 i1 : Fin r, ∃ j0 j1 : Fin s,
    i1.val = i0.val + 1 ∧ j1.val = j0.val + 1 ∧
      HullSixLocalProductTwelveCells
        (T i0 j0) (T i0 j1) (T i1 j0) (T i1 j1)

/-- Either of the two local determinant patterns which forces a product of
at least twelve.  `E,D` are the same-side fan areas in the selected apex fan.
-/
def HullSixLocalProductTwelvePattern
    (m E D x00 x01 x10 x11 y00 y01 y10 y11 : ℝ) : Prop :=
  (x00 ≤ -3 * m ∧ x01 ≤ -3 * m ∧ m ≤ x10 ∧
      x11 ≤ -3 * m ∧
      E * D = x00 * x11 - x01 * x10) ∨
  (3 * m ≤ y00 ∧ y01 ≤ -m ∧ 3 * m ≤ y10 ∧
      3 * m ≤ y11 ∧
      E * D = y00 * y11 - y01 * y10)

/-- A recognized local pattern forces the common product bound. -/
theorem hullSixLocalProductTwelvePattern_product
    {m E D x00 x01 x10 x11 y00 y01 y10 y11 : ℝ}
    (hm : 0 ≤ m)
    (hpattern : HullSixLocalProductTwelvePattern
      m E D x00 x01 x10 x11 y00 y01 y10 y11) :
    12 * m ^ 2 ≤ E * D := by
  rcases hpattern with hP | hQ
  · rcases hP with ⟨hx00, hx01, hx10, hx11, hplucker⟩
    exact hullSixTwoFour_product_twelve_of_RR_LR hm
      hx00 hx01 hx10 hx11 hplucker
  · rcases hQ with ⟨hy00, hy01, hy10, hy11, hplucker⟩
    exact hullSixTwoFour_product_twelve_of_LR_LL hm
      hy00 hy01 hy10 hy11 hplucker

/-- One local-pattern theorem closes every matching `2 + 4` or `3 + 3`
tableau.  The four unselected fan terms are exposed explicitly: two cross
caps of strengths `m` and `3m`, and the other two same-side edges of strength
`m` each. -/
theorem hullSixSixFan_finish_of_localProductTwelvePattern
    {m H E D capOrdinary capStrong other0 other1
      x00 x01 x10 x11 y00 y01 y10 y11 : ℝ}
    (hm : 0 < m) (hE : m ≤ E) (hD : m ≤ D)
    (hcapOrdinary : m ≤ capOrdinary)
    (hcapStrong : 3 * m ≤ capStrong)
    (hother0 : m ≤ other0) (hother1 : m ≤ other1)
    (harea : H = E + D + capOrdinary + capStrong + other0 + other1)
    (hpattern : HullSixLocalProductTwelvePattern
      m E D x00 x01 x10 x11 y00 y01 y10 y11) :
    25 * m < 2 * H := by
  have hproduct : 12 * m ^ 2 ≤ E * D :=
    hullSixLocalProductTwelvePattern_product (le_of_lt hm) hpattern
  exact hullSixSixFan_finish_of_product_twelve_mul hm hE hD hproduct
    hcapOrdinary hcapStrong hother0 hother1 harea

/-- Recognition of the `RR / LR` alternative directly from chamber labels,
base change, and the `P`-Plucker identity. -/
theorem hullSixLocalProductTwelvePattern_of_RR_LR
    {m E D u0 u1 v0 v1 x00 x01 x10 x11 y00 y01 y10 y11 : ℝ}
    (hu0 : m ≤ u0) (hu1 : m ≤ u1)
    (hv0 : m ≤ v0) (hv1 : m ≤ v1)
    (hbase00 : y00 = x00 + u0 + v0)
    (hbase01 : y01 = x01 + u0 + v1)
    (hbase10 : y10 = x10 + u1 + v0)
    (hbase11 : y11 = x11 + u1 + v1)
    (h00 : HullSixChamberLabel.Holds HullSixChamberLabel.R m x00 y00)
    (h01 : HullSixChamberLabel.Holds HullSixChamberLabel.R m x01 y01)
    (h10 : HullSixChamberLabel.Holds HullSixChamberLabel.L m x10 y10)
    (h11 : HullSixChamberLabel.Holds HullSixChamberLabel.R m x11 y11)
    (hplucker : E * D = x00 * x11 - x01 * x10) :
    HullSixLocalProductTwelvePattern
      m E D x00 x01 x10 x11 y00 y01 y10 y11 := by
  left
  refine ⟨chamberLabel_R_pDet_le_neg_three hu0 hv0 hbase00 h00,
    chamberLabel_R_pDet_le_neg_three hu0 hv1 hbase01 h01, ?_,
    chamberLabel_R_pDet_le_neg_three hu1 hv1 hbase11 h11, hplucker⟩
  simpa [HullSixChamberLabel.Holds] using h10

/-- Recognition of the `LR / LL` alternative directly from chamber labels,
base change, and the `Q`-Plucker identity. -/
theorem hullSixLocalProductTwelvePattern_of_LR_LL
    {m E D u0 u1 v0 v1 x00 x01 x10 x11 y00 y01 y10 y11 : ℝ}
    (hu0 : m ≤ u0) (hu1 : m ≤ u1)
    (hv0 : m ≤ v0) (hv1 : m ≤ v1)
    (hbase00 : y00 = x00 + u0 + v0)
    (hbase01 : y01 = x01 + u0 + v1)
    (hbase10 : y10 = x10 + u1 + v0)
    (hbase11 : y11 = x11 + u1 + v1)
    (h00 : HullSixChamberLabel.Holds HullSixChamberLabel.L m x00 y00)
    (h01 : HullSixChamberLabel.Holds HullSixChamberLabel.R m x01 y01)
    (h10 : HullSixChamberLabel.Holds HullSixChamberLabel.L m x10 y10)
    (h11 : HullSixChamberLabel.Holds HullSixChamberLabel.L m x11 y11)
    (hplucker : E * D = y00 * y11 - y01 * y10) :
    HullSixLocalProductTwelvePattern
      m E D x00 x01 x10 x11 y00 y01 y10 y11 := by
  right
  refine ⟨chamberLabel_L_qDet_ge_three hu0 hv0 hbase00 h00, ?_,
    chamberLabel_L_qDet_ge_three hu1 hv0 hbase10 h10,
    chamberLabel_L_qDet_ge_three hu1 hv1 hbase11 h11, hplucker⟩
  simpa [HullSixChamberLabel.Holds] using h01

end Heilbronn8
