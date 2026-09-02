import Heilbronn8.Survivors.Join.HullSixTwoFourLocalProduct
import Heilbronn8.Survivors.Join.HullSixLocalProductChambers
import Heilbronn8.Survivors.Join.HullSixTwoFourOrbitCensus

/-!
# Wide-column product closure for `2 + 4`

The product-twelve Plucker calculation does not require the selected lower
columns to be adjacent.  If columns `j < k` have rows `RR / LR` in the
`P`-fan, or `LR / LL` in the `Q`-fan, the same calculation gives

```text
A * D(j,k) >= 12 m^2.
```

Here `A` is the unique upper same-side triangle and `D(j,k)` is the lower
triangle on the selected chord.  These two empty triangles have disjoint
interiors and extend simultaneously to a triangulation of the eight points.
Such a triangulation has eight faces.  The other six faces have area at least
`m`, so the scalar endpoint is stronger than the adjacent-fan endpoint:

```text
H >= A + D(j,k) + 6m > 25m/2.
```

The first section records this endpoint.  The second records the exact finite
gain before a geometric prescribed-triangulation adapter is attached: wide
products cover 25 of the 76 legal tables, adding eight labels (four
complement-rotation orbits) to the current census and leaving 50 labels in 28
orbits.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

/-- Scalar endpoint for a triangulation containing the two selected
product-twelve faces and six further faces of area at least `m`. -/
theorem hullSixTwoFour_finish_of_wide_product_twelve_mul
    {m H A D t0 t1 t2 t3 t4 t5 : ℝ}
    (hm : 0 < m) (hA : m ≤ A) (hD : m ≤ D)
    (hproduct : 12 * m ^ 2 ≤ A * D)
    (ht0 : m ≤ t0) (ht1 : m ≤ t1) (ht2 : m ≤ t2)
    (ht3 : m ≤ t3) (ht4 : m ≤ t4) (ht5 : m ≤ t5)
    (harea : H = A + D + t0 + t1 + t2 + t3 + t4 + t5) :
    25 * m < 2 * H := by
  have hpair : (13 : ℝ) / 2 * m < A + D :=
    hullSixTwoFour_pair_gt_thirteen_halves_mul hm hA hD hproduct
  rw [harea]
  linarith

/-- Geometry-facing form of the wide endpoint.  The local chamber adapter
supplies either the `P`- or `Q`-Plucker alternative, while a prescribed
triangulation supplies the six remaining face floors and the exact area
sum. -/
theorem hullSixTwoFour_finish_of_wideLocalProductTwelvePattern
    {m H A D t0 t1 t2 t3 t4 t5
      x00 x01 x10 x11 y00 y01 y10 y11 : ℝ}
    (hm : 0 < m) (hA : m ≤ A) (hD : m ≤ D)
    (ht0 : m ≤ t0) (ht1 : m ≤ t1) (ht2 : m ≤ t2)
    (ht3 : m ≤ t3) (ht4 : m ≤ t4) (ht5 : m ≤ t5)
    (harea : H = A + D + t0 + t1 + t2 + t3 + t4 + t5)
    (hpattern : HullSixLocalProductTwelvePattern
      m A D x00 x01 x10 x11 y00 y01 y10 y11) :
    25 * m < 2 * H := by
  have hproduct : 12 * m ^ 2 ≤ A * D :=
    hullSixLocalProductTwelvePattern_product (le_of_lt hm) hpattern
  exact hullSixTwoFour_finish_of_wide_product_twelve_mul hm hA hD hproduct
    ht0 ht1 ht2 ht3 ht4 ht5 harea

/-- Fan/retriangulation seam for the geometric `2 + 4` adapter.

The `P`-fan is split at `Q` into the upper face `A`, the opposite cross face
`C`, three adjacent lower faces `E0,E1,E2`, and three faces `capU,capV,capQ`
at the other cross cap.  Retriangulating the lower pentagon replaces the
three adjacent lower faces by the selected wide face `D` and two hull faces
`R,S`.  This produces exactly the eight-face area identity consumed above. -/
theorem hullSixTwoFour_finish_of_wideLocalProduct_and_lowerRetriangulation
    {m H A D C E0 E1 E2 R S capU capV capQ
      x00 x01 x10 x11 y00 y01 y10 y11 : ℝ}
    (hm : 0 < m) (hA : m ≤ A) (hD : m ≤ D)
    (hC : m ≤ C) (hR : m ≤ R) (hS : m ≤ S)
    (hcapU : m ≤ capU) (hcapV : m ≤ capV) (hcapQ : m ≤ capQ)
    (hfan : H = A + C + E0 + E1 + E2 + capU + capV + capQ)
    (hlower : E0 + E1 + E2 = D + R + S)
    (hpattern : HullSixLocalProductTwelvePattern
      m A D x00 x01 x10 x11 y00 y01 y10 y11) :
    25 * m < 2 * H := by
  have harea : H = A + D + C + R + S + capU + capV + capQ := by
    linarith
  exact hullSixTwoFour_finish_of_wideLocalProductTwelvePattern
    hm hA hD hC hR hS hcapU hcapV hcapQ harea hpattern

namespace HullSixTwoFourCuts

/-- Two arbitrary ordered lower columns have rows `RR / LR`. -/
@[reducible] def WideRRLR (T : HullSixTwoFourCuts) : Prop :=
  ∃ j k : Fin 4, j < k ∧
    T.table (0 : Fin 2) j = HullSixChamberLabel.R ∧
    T.table (0 : Fin 2) k = HullSixChamberLabel.R ∧
    T.table (1 : Fin 2) j = HullSixChamberLabel.L ∧
    T.table (1 : Fin 2) k = HullSixChamberLabel.R

/-- Two arbitrary ordered lower columns have rows `LR / LL`. -/
@[reducible] def WideLRLL (T : HullSixTwoFourCuts) : Prop :=
  ∃ j k : Fin 4, j < k ∧
    T.table (0 : Fin 2) j = HullSixChamberLabel.L ∧
    T.table (0 : Fin 2) k = HullSixChamberLabel.R ∧
    T.table (1 : Fin 2) j = HullSixChamberLabel.L ∧
    T.table (1 : Fin 2) k = HullSixChamberLabel.L

/-- The wide-column product-twelve family. -/
@[reducible] def HasWideProductTwelve (T : HullSixTwoFourCuts) : Prop :=
  T.WideRRLR ∨ T.WideLRLL

/-- Exact cut characterization of the wide-column family. -/
theorem hasWideProductTwelve_iff_cuts :
    ∀ T : HullSixTwoFourCuts, T.Legal →
      (T.HasWideProductTwelve ↔
        T.q0 < T.p1 ∧
          (T.q1 < (4 : Fin 5) ∨ (0 : Fin 5) < T.p0)) := by
  decide

/-- Complement-rotation exchanges the two wide patterns. -/
theorem hasWideProductTwelve_rotateComplement_iff :
    ∀ T : HullSixTwoFourCuts, T.Legal →
      (T.rotateComplement.HasWideProductTwelve ↔
        T.HasWideProductTwelve) := by
  decide

/-- All legal tables containing a wide product-twelve pair. -/
def wideProductTwelveTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Legal ∧ T.HasWideProductTwelve

/-- The wide labels not already in the adjacent/hard census coverage. -/
def newlyCoveredByWideTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦
    T.Legal ∧ T.HasWideProductTwelve ∧ ¬T.CurrentlyCovered

/-- Residual labels after adjoining the wide-column family. -/
@[reducible] def RemainingAfterWide (T : HullSixTwoFourCuts) : Prop :=
  T.Remaining ∧ ¬T.HasWideProductTwelve

def remainingAfterWideTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.RemainingAfterWide

/-- Wide products occur in exactly 25 legal labeled tables. -/
theorem wideProductTwelveTables_card : wideProductTwelveTables.card = 25 := by
  decide

/-- Eight of those labels are genuinely new relative to the current census. -/
theorem newlyCoveredByWideTables_card : newlyCoveredByWideTables.card = 8 := by
  decide

/-- Exactly 50 labeled tables remain after the wide-column compression. -/
theorem remainingAfterWideTables_card : remainingAfterWideTables.card = 50 := by
  decide

/-- The new residual remains invariant under complement-rotation. -/
theorem remainingAfterWide_rotateComplement_iff :
    ∀ T : HullSixTwoFourCuts,
      (T.rotateComplement.RemainingAfterWide ↔
        T.RemainingAfterWide) := by
  decide

/-- Canonical complement-rotation representatives after wide compression. -/
def remainingAfterWideOrbitRepresentatives : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦
    T.RemainingAfterWide ∧
      T.orbitCode ≤ T.rotateComplement.orbitCode

/-- The 50 remaining labels form exactly 28 complement-rotation orbits. -/
theorem remainingAfterWideOrbitRepresentatives_card :
    remainingAfterWideOrbitRepresentatives.card = 28 := by
  decide

end HullSixTwoFourCuts
end Heilbronn8
