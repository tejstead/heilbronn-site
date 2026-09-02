import Heilbronn8.TriHull.HullSevenType6RawArea
import Heilbronn8.TriHull.HullSevenType6ReflectionSignAudit

/-!
# Determinant adapter for the hull-seven type-6 raw-area closer

This module keeps the pure scalar theorem separate from the finite sign and
classifier imports needed by the honest determinant chart.
-/

namespace Heilbronn8.TriHull

/-- Package the raw determinant chart for the cap-free scalar closer.

The two product-ear rows are derived from adjacent ear floors and the exact
Pluecker identities.  No geometric-mean additive cap is used. -/
noncomputable def HullSevenType6RawReflectionData.toRawAreaData
    {H : ℝ} (X : HullSevenType6RawReflectionData H) :
    HullSevenType6RawAreaData H := by
  let D := X.toCoreData
  have hB0 : 0 ≤ X.B := le_trans (by norm_num) X.B_ge
  have hZ0 : 0 ≤ X.Z := le_trans (by norm_num) X.Z_ge
  refine
    { a := D.a
      A := D.A
      B := D.B
      U := D.U
      P := D.P
      Q := D.Q
      R := D.R
      E := D.E
      rawA := X.A
      rawB := X.B
      rawC := X.C
      rawG := X.G
      rawZ := X.Z
      rawD := X.D
      a_ge := D.a_ge
      A_ge := D.A_ge
      B_ge := D.B_ge
      U_ge := D.U_ge
      P_ge := D.P_ge
      Q_ge := D.Q_ge
      R_ge := D.R_ge
      E_ge := D.E_ge
      rawA_ge := X.A_ge
      rawB_ge := X.B_ge
      rawC_ge := X.C_ge
      rawG_ge := X.G_ge
      rawZ_ge := X.Z_ge
      rawD_ge := X.D_ge
      middle_sq := ?_
      A_pair := ?_
      B_pair := ?_
      U_pair := ?_
      left_product := ?_
      right_product := ?_
      central := D.central
      right_cap := D.right_cap
      p_to_a := D.p_to_a
      e_to_a := D.e_to_a
      p_e_to_r := D.p_e_to_r
      terminal := D.terminal
      area := ?_ }
  · change (Real.sqrt (X.B * X.Z)) ^ 2 = X.B * X.Z
    exact Real.sq_sqrt (mul_nonneg hB0 hZ0)
  · change 2 * Real.sqrt (X.A * X.G) ≤ X.A + X.G
    exact hullSeven_type6_two_sqrt_mul_le_add
      (le_trans (by norm_num) X.A_ge) (le_trans (by norm_num) X.G_ge)
  · change 2 * Real.sqrt (X.B * X.Z) ≤ X.B + X.Z
    exact hullSeven_type6_two_sqrt_mul_le_add hB0 hZ0
  · change 2 * Real.sqrt (X.C * X.D) ≤ X.C + X.D
    exact hullSeven_type6_two_sqrt_mul_le_add
      (le_trans (by norm_num) X.C_ge) (le_trans (by norm_num) X.D_ge)
  · exact hullSeven_type6_product_ear
      X.A_ge X.B_ge X.C_ge X.p_ge X.q_ge X.L_ge
      X.p_left_ear X.q_left_ear X.gp1234
  · exact hullSeven_type6_product_ear
      X.G_ge X.Z_ge X.D_ge X.n_ge X.S_ge X.l_ge
      X.p_right_ear (by linarith [X.q_right_ear]) X.gp0456
  · change X.a + X.A + X.B + X.C + X.G + X.Z + X.D ≤ H
    linarith [X.area]

/-- Direct cap-free area consequence of the honest raw determinant packet. -/
theorem hullSeven_type6_raw_reflection_area
    {H : ℝ} (X : HullSevenType6RawReflectionData H) :
    (25 : ℝ) / 2 < H :=
  hullSeven_type6_raw_area X.toRawAreaData

/-- Direct `v8` consequence of the honest raw determinant packet. -/
theorem hullSeven_v8_of_type6_raw
    {H : ℝ} (X : HullSevenType6RawReflectionData H) :
    1 ≤ v8 * H :=
  hullSeven_v8_of_type6_raw_area X.toRawAreaData

end Heilbronn8.TriHull
