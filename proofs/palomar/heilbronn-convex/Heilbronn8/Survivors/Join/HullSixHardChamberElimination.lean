import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar elimination for the hard `2 + 4` chamber

This module separates the elementary determinant elimination from both the
geometric chamber adapter and the weighted AM--GM endpoint.  The variables
and inequalities are exactly those documented in
`HullSixHardChamberAMGM.lean`; no chamber fact is implicit in the theorem.

After normalizing the minimum doubled triangle area to one, put

```text
u = u0,  w = u1,  x = v1,  y = v2.
```

The auxiliary variables are the endpoint heights `v0,v3`, the two upper fan
areas `A,C`, and the four remaining fan areas `E0,E1',E2',D'`.  A future
geometric adapter only has to establish the displayed exact hull sum and the
five inequalities below.  The conclusion is precisely the lower bound
consumed by `hullSixHardChamber_finish`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Exact elementary elimination for the canonical hard tableau

```text
M M R R
L L M M
```

The hypotheses correspond respectively to inequalities (3), (4), (2), (5),
and the second half of (7) in `HullSixHardChamberAMGM.lean`.
-/
theorem hullSixHardChamber_lower_of_elimination
    {H u w x y v0 v3 A C E0 E1p E2p Dp : ℝ}
    (hu : 1 ≤ u) (hw : 1 ≤ w) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hv0 : 1 ≤ v0) (hv3 : 1 ≤ v3)
    (hE0 : 1 ≤ E0) (hE2p : 1 ≤ E2p)
    (harea : H = A + C + E0 + E1p + E2p + Dp + u + x)
    (hleftRow : v0 + w * E0 ≤ x * C)
    (hleftColumn : u * C + w ≤ v0 * A)
    (hrightRow : w + y ≤ v3 * (w + y - 1))
    (hrightColumn : v3 + u * E2p ≤ y * Dp)
    (hmiddle : x + y ≤ u * E1p) :
    hullSixHardChamberLower u w x y ≤ H := by
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hv0Pos : 0 < v0 := lt_of_lt_of_le zero_lt_one hv0

  have hleftRow' : v0 + w ≤ x * C := by
    have hwE0 : w ≤ w * E0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hE0)]
    linarith
  have hC : (v0 + w) / x ≤ C := by
    apply (div_le_iff₀ hxPos).2
    simpa [mul_comm] using hleftRow'
  have hA : (u * C + w) / v0 ≤ A := by
    apply (div_le_iff₀ hv0Pos).2
    simpa [mul_comm] using hleftColumn

  have hcoef : 0 ≤ 1 + u / v0 := by positivity
  have hACraw :
      (u + w + v0 + w * (u + x) / v0) / x ≤ A + C := by
    calc
      (u + w + v0 + w * (u + x) / v0) / x =
          (1 + u / v0) * ((v0 + w) / x) + w / v0 := by
            field_simp [hxPos.ne', hv0Pos.ne']
            <;> ring
      _ ≤ (1 + u / v0) * C + w / v0 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hC hcoef) (le_refl _)
      _ = (u * C + w) / v0 + C := by
        field_simp [hv0Pos.ne']
        <;> ring
      _ ≤ A + C := by
        exact add_le_add hA (le_refl C)

  let z : ℝ := w * (u + x)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hsqrtSq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz0
  have hamgmScaled : 2 * Real.sqrt z * v0 ≤ v0 ^ 2 + z := by
    nlinarith [sq_nonneg (v0 - Real.sqrt z)]
  have hamgm : 2 * Real.sqrt z ≤ v0 + z / v0 := by
    calc
      2 * Real.sqrt z = (2 * Real.sqrt z * v0) / v0 := by
        field_simp [hv0Pos.ne']
      _ ≤ (v0 ^ 2 + z) / v0 :=
        div_le_div_of_nonneg_right hamgmScaled (le_of_lt hv0Pos)
      _ = v0 + z / v0 := by
        field_simp [hv0Pos.ne']
        <;> ring
  have hAC :
      (u + w + 2 * Real.sqrt (w * (u + x))) / x ≤ A + C := by
    have hnum :
        u + w + 2 * Real.sqrt (w * (u + x)) ≤
          u + w + v0 + w * (u + x) / v0 := by
      dsimp [z] at hamgm
      linarith
    exact (div_le_div_of_nonneg_right hnum hx0).trans hACraw

  have hE1p : (x + y) / u ≤ E1p := by
    apply (div_le_iff₀ huPos).2
    simpa [mul_comm] using hmiddle

  have hdenPos : 0 < w + y - 1 := by linarith
  have hv3Ratio : (w + y) / (w + y - 1) ≤ v3 := by
    apply (div_le_iff₀ hdenPos).2
    simpa [mul_comm] using hrightRow
  have hv3Lower : 1 + 1 / (w + y - 1) ≤ v3 := by
    calc
      1 + 1 / (w + y - 1) = (w + y) / (w + y - 1) := by
        field_simp [hdenPos.ne']
        <;> ring
      _ ≤ v3 := hv3Ratio
  have hrightColumn' : v3 + u ≤ y * Dp := by
    have huE2p : u ≤ u * E2p := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hE2p)]
    linarith
  have hDpRaw : (v3 + u) / y ≤ Dp := by
    apply (div_le_iff₀ hyPos).2
    simpa [mul_comm] using hrightColumn'
  have hDp : (u + 1 + 1 / (w + y - 1)) / y ≤ Dp := by
    have hnum : u + 1 + 1 / (w + y - 1) ≤ v3 + u := by
      linarith
    exact (div_le_div_of_nonneg_right hnum hy0).trans hDpRaw

  rw [harea, hullSixHardChamberLower]
  linarith

/-- End-to-end hard-tableau closure from the seven explicit scalar facts. -/
theorem hullSixHardChamber_finish_of_elimination
    {H u w x y v0 v3 A C E0 E1p E2p Dp : ℝ}
    (hu : 1 ≤ u) (hw : 1 ≤ w) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hv0 : 1 ≤ v0) (hv3 : 1 ≤ v3)
    (hE0 : 1 ≤ E0) (hE2p : 1 ≤ E2p)
    (harea : H = A + C + E0 + E1p + E2p + Dp + u + x)
    (hleftRow : v0 + w * E0 ≤ x * C)
    (hleftColumn : u * C + w ≤ v0 * A)
    (hrightRow : w + y ≤ v3 * (w + y - 1))
    (hrightColumn : v3 + u * E2p ≤ y * Dp)
    (hmiddle : x + y ≤ u * E1p) :
    (25 : ℝ) / 2 < H := by
  apply hullSixHardChamber_finish hu hw hx hy
  exact hullSixHardChamber_lower_of_elimination hu hw hx hy hv0 hv3
    hE0 hE2p harea hleftRow hleftColumn hrightRow hrightColumn hmiddle

end Heilbronn8
