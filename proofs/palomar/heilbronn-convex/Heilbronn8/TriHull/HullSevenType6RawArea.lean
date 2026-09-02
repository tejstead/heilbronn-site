import Heilbronn8.TriHull.HullSevenType6Reflection

/-!
# Raw-area closer for hull-seven type 6

This module removes the two additive geometric-mean caps from the type-6
argument.  The four raw ear floors and two adjacent Pluecker rows instead
give reciprocal bounds for the two boundary triples.  Averaging those bounds
before taking geometric means pays exactly for the quarter-copy lower bound
used by the existing ten-term AM-GM estimate.

The module is purely scalar.  The determinant adapter is kept in the sign
audit module, so no corpus or classifier module is imported here.
-/

namespace Heilbronn8.TriHull

/-- The cap-free scalar packet obtained from the honest type-6 raw chart.

`rawA, rawB, rawC` and `rawG, rawZ, rawD` are the two reflected boundary
triples.  `A, B, U` are their componentwise geometric means.  Only the middle
square identity is needed in the reciprocal argument; the three pair bounds
record ordinary two-term AM-GM. -/
structure HullSevenType6RawAreaData (H : ℝ) where
  a : ℝ
  A : ℝ
  B : ℝ
  U : ℝ
  P : ℝ
  Q : ℝ
  R : ℝ
  E : ℝ

  rawA : ℝ
  rawB : ℝ
  rawC : ℝ
  rawG : ℝ
  rawZ : ℝ
  rawD : ℝ

  a_ge : 1 ≤ a
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  U_ge : 1 ≤ U
  P_ge : 1 ≤ P
  Q_ge : 1 ≤ Q
  R_ge : 1 ≤ R
  E_ge : 1 ≤ E

  rawA_ge : 1 ≤ rawA
  rawB_ge : 1 ≤ rawB
  rawC_ge : 1 ≤ rawC
  rawG_ge : 1 ≤ rawG
  rawZ_ge : 1 ≤ rawZ
  rawD_ge : 1 ≤ rawD

  middle_sq : B ^ 2 = rawB * rawZ
  A_pair : 2 * A ≤ rawA + rawG
  B_pair : 2 * B ≤ rawB + rawZ
  U_pair : 2 * U ≤ rawC + rawD

  left_product :
    1 ≤ (rawB - 1) * (rawA + rawB + rawC - 2)
  right_product :
    1 ≤ (rawZ - 1) * (rawG + rawZ + rawD - 2)

  central : B + A * U ≤ P * Q
  right_cap : R + Q ≤ A * U
  p_to_a : 1 + P ≤ a * U
  e_to_a : E + A ≤ a * Q
  p_e_to_r : P + B * E ≤ A * R
  terminal : 1 + A * B ≤ R * E

  area : a + rawA + rawB + rawC + rawG + rawZ + rawD ≤ H

/-- Two adjacent raw ear floors and their Pluecker row give the product-ear
bound used by the cap-free argument. -/
lemma hullSeven_type6_product_ear
    {A B C p q L : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hL : 1 ≤ L)
    (hpEar : 1 ≤ A + B - p) (hqEar : 1 ≤ B + C - q)
    (hgp : p * q = A * C + L * B) :
    1 ≤ (B - 1) * (A + B + C - 2) := by
  have hpCap : p ≤ A + B - 1 := by linarith
  have hqCap : q ≤ B + C - 1 := by linarith
  have hpqUpper : p * q ≤ (A + B - 1) * (B + C - 1) := by
    calc
      p * q ≤ (A + B - 1) * q :=
        mul_le_mul_of_nonneg_right hpCap (by linarith)
      _ ≤ (A + B - 1) * (B + C - 1) :=
        mul_le_mul_of_nonneg_left hqCap (by linarith)
  have hLB : B ≤ L * B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (by linarith : 0 ≤ B)]
  have hpqLower : A * C + B ≤ p * q := by
    rw [hgp]
    linarith
  have hid :
      (A + B - 1) * (B + C - 1) - (A * C + B) =
        (B - 1) * (A + B + C - 2) - 1 := by
    ring
  nlinarith

/-- Reciprocal AM-GM in the exact form needed for the middle reflected pair.

The polynomial identity behind the proof is

`(s - 1) * ((x - 1) + (y - 1)) - 2 * (x - 1) * (y - 1)
  = (s + 1) * (x + y - 2 * s)`

when `s^2 = x*y`. -/
lemma hullSeven_type6_middle_reciprocal
    {x y s : ℝ}
    (hx : 1 < x) (hy : 1 < y) (hs : 1 ≤ s)
    (hsq : s ^ 2 = x * y) (hpair : 2 * s ≤ x + y) :
    1 / (s - 1) ≤
      (1 / 2 : ℝ) * (1 / (x - 1) + 1 / (y - 1)) := by
  have hspos : 0 < s - 1 := by
    have hxy : 1 < x * y := by
      nlinarith [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]
    nlinarith [hsq]
  have hxpos : 0 < x - 1 := sub_pos.mpr hx
  have hypos : 0 < y - 1 := sub_pos.mpr hy
  have hnumerator :
      2 * (x - 1) * (y - 1) ≤
        ((x - 1) + (y - 1)) * (s - 1) := by
    have hid :
        ((s - 1) * ((x - 1) + (y - 1)) -
            2 * (x - 1) * (y - 1)) =
          (s + 1) * (x + y - 2 * s) := by
      nlinarith [hsq]
    have hnonneg : 0 ≤ (s + 1) * (x + y - 2 * s) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hden : 0 < 2 * (x - 1) * (y - 1) := by positivity
  have hfrac :
      1 / (s - 1) ≤
        ((x - 1) + (y - 1)) / (2 * (x - 1) * (y - 1)) := by
    apply (div_le_div_iff₀ hspos hden).2
    nlinarith
  calc
    1 / (s - 1) ≤
        ((x - 1) + (y - 1)) / (2 * (x - 1) * (y - 1)) := hfrac
    _ = (1 / 2 : ℝ) * (1 / (x - 1) + 1 / (y - 1)) := by
      field_simp [hxpos.ne', hypos.ne']
      <;> ring

/-- The honest raw type-6 scalar packet forces area strictly above `25/2`.

No additive cap for `P` or `Q` is assumed. -/
theorem hullSeven_type6_raw_area {H : ℝ}
    (D : HullSevenType6RawAreaData H) :
    (25 : ℝ) / 2 < H := by
  let b : ℝ := D.B - 1
  let T : ℝ := D.A + D.B + D.U
  let X : ℝ := D.A * D.U - D.Q
  let Y : ℝ := X - D.B
  let S : ℝ :=
    D.rawA + D.rawB + D.rawC + D.rawG + D.rawZ + D.rawD

  have ha : 0 < D.a := lt_of_lt_of_le zero_lt_one D.a_ge
  have hA : 0 < D.A := lt_of_lt_of_le zero_lt_one D.A_ge
  have hB : 0 < D.B := lt_of_lt_of_le zero_lt_one D.B_ge
  have hU : 0 < D.U := lt_of_lt_of_le zero_lt_one D.U_ge
  have hP : 0 < D.P := lt_of_lt_of_le zero_lt_one D.P_ge
  have hQ : 0 < D.Q := lt_of_lt_of_le zero_lt_one D.Q_ge
  have hR : 0 < D.R := lt_of_lt_of_le zero_lt_one D.R_ge
  have hE : 0 < D.E := lt_of_lt_of_le zero_lt_one D.E_ge

  have hleftSum : 1 ≤ D.rawA + D.rawB + D.rawC - 2 := by
    linarith [D.rawA_ge, D.rawB_ge, D.rawC_ge]
  have hrightSum : 1 ≤ D.rawG + D.rawZ + D.rawD - 2 := by
    linarith [D.rawG_ge, D.rawZ_ge, D.rawD_ge]
  have hrawB : 0 < D.rawB - 1 := by
    by_contra hn
    have hnonpos : D.rawB - 1 ≤ 0 := le_of_not_gt hn
    have hprod :
        (D.rawB - 1) * (D.rawA + D.rawB + D.rawC - 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos (by linarith)
    linarith [D.left_product]
  have hrawZ : 0 < D.rawZ - 1 := by
    by_contra hn
    have hnonpos : D.rawZ - 1 ≤ 0 := le_of_not_gt hn
    have hprod :
        (D.rawZ - 1) * (D.rawG + D.rawZ + D.rawD - 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos (by linarith)
    linarith [D.right_product]
  have hleftReciprocal :
      1 / (D.rawB - 1) ≤ D.rawA + D.rawB + D.rawC - 2 := by
    apply (div_le_iff₀ hrawB).2
    simpa [mul_comm] using D.left_product
  have hrightReciprocal :
      1 / (D.rawZ - 1) ≤ D.rawG + D.rawZ + D.rawD - 2 := by
    apply (div_le_iff₀ hrawZ).2
    simpa [mul_comm] using D.right_product

  have hrawProduct : 1 < D.rawB * D.rawZ := by
    nlinarith [mul_pos hrawB hrawZ]
  have hBstrict : 1 < D.B := by
    nlinarith [D.middle_sq]
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hmiddleReciprocal :
      1 / b ≤
        (1 / 2 : ℝ) *
          (1 / (D.rawB - 1) + 1 / (D.rawZ - 1)) := by
    dsimp [b]
    exact hullSeven_type6_middle_reciprocal
      (by linarith) (by linarith) D.B_ge D.middle_sq D.B_pair
  have hT1raw : 2 + 1 / b ≤ S / 2 := by
    dsimp [S]
    linarith [hleftReciprocal, hrightReciprocal, hmiddleReciprocal]
  have hTraw : 2 * T ≤ S := by
    dsimp [T, S]
    linarith [D.A_pair, D.B_pair, D.U_pair]

  have hRleX : D.R ≤ X := by
    dsimp [X]
    linarith [D.right_cap]
  have hX : 0 < X := lt_of_lt_of_le hR hRleX
  have hgapPE : 0 ≤ (D.A * D.R - D.P - D.B * D.E) * X :=
    mul_nonneg (by linarith [D.p_e_to_r]) hX.le
  have hgapTerminal : 0 ≤ D.B * (D.R * D.E - 1 - D.A * D.B) :=
    mul_nonneg hB.le (by linarith [D.terminal])
  have hgapReflection :
      0 ≤ (D.A * X + D.B * D.E) * (X - D.R) :=
    mul_nonneg (by positivity) (by linarith)
  have hquadratic :
      D.P * X + D.B * (1 + D.A * D.B) ≤ D.A * X ^ 2 := by
    nlinarith [hgapPE, hgapTerminal, hgapReflection]
  have hYX : D.P * X + D.B ≤ D.A * Y * (D.B + X) := by
    dsimp [Y]
    nlinarith [hquadratic]
  have hY : 0 < Y := by
    by_contra hn
    have hY0 : Y ≤ 0 := le_of_not_gt hn
    have hleft : D.A * Y * (D.B + X) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hA.le hY0) (by positivity)
    have : 0 < D.P * X + D.B := by positivity
    linarith

  have hresidual : 0 ≤ D.P * D.Q - D.Q - D.B - X := by
    dsimp [X]
    linarith [D.central]
  have hidentity :
      D.Q * (D.P * X + D.B) - D.A * D.U * (D.B + X) =
        X * (D.P * D.Q - D.Q - D.B - X) := by
    dsimp [X]
    ring
  have hmiddle :
      D.A * D.U * (D.B + X) ≤ D.Q * (D.P * X + D.B) := by
    rw [← sub_nonneg, hidentity]
    exact mul_nonneg hX.le hresidual
  have hscaledYX :
      D.Q * (D.P * X + D.B) ≤
        D.Q * (D.A * Y * (D.B + X)) :=
    mul_le_mul_of_nonneg_left hYX hQ.le
  have hcancel :
      D.A * D.U * (D.B + X) ≤
        (D.A * D.Q * Y) * (D.B + X) := by
    calc
      D.A * D.U * (D.B + X) ≤ D.Q * (D.P * X + D.B) := hmiddle
      _ ≤ D.Q * (D.A * Y * (D.B + X)) := hscaledYX
      _ = (D.A * D.Q * Y) * (D.B + X) := by ring
  have hAUle : D.A * D.U ≤ D.A * D.Q * Y :=
    (mul_le_mul_iff_of_pos_right (by positivity : 0 < D.B + X)).mp hcancel
  have hQY : D.U ≤ D.Q * Y := by
    have hAUle' : D.A * D.U ≤ D.A * (D.Q * Y) := by
      simpa [mul_assoc] using hAUle
    have := (mul_le_mul_iff_of_pos_left hA).mp hAUle'
    simpa [mul_assoc] using this
  have hYlower : D.U / D.Q ≤ Y :=
    (div_le_iff₀ hQ).2 (by simpa [mul_comm] using hQY)
  have hAUidentity : D.A * D.U = D.B + D.Q + Y := by
    dsimp [Y, X]
    ring
  have hAUlower : D.B + D.Q + D.U / D.Q ≤ D.A * D.U := by
    rw [hAUidentity]
    linarith
  have hAlower :
      D.B / D.U + D.Q / D.U + 1 / D.Q ≤ D.A := by
    calc
      D.B / D.U + D.Q / D.U + 1 / D.Q =
          (D.B + D.Q + D.U / D.Q) / D.U := by
            field_simp [hU.ne', hQ.ne']
      _ ≤ D.A := (div_le_iff₀ hU).2 (by
        simpa [mul_comm] using hAUlower)
  have hT2 :
      D.B + D.U + D.B / D.U + D.Q / D.U + 1 / D.Q ≤ T := by
    dsimp [T]
    linarith

  have hYnumber :
      2 * D.B + 2 * D.Q + D.U / D.Q ≤
        D.A * D.U + D.B + D.Q := by
    rw [hAUidentity]
    linarith
  have hcentralPlus :
      D.A * D.U + D.B + D.Q ≤ D.Q * (D.P + 1) := by
    nlinarith [D.central]
  have hpToAScaled : D.Q * (D.P + 1) ≤ D.a * (D.U * D.Q) := by
    have hscaled := mul_le_mul_of_nonneg_left D.p_to_a hQ.le
    simpa [add_comm, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have haProduct :
      2 * D.B + 2 * D.Q + D.U / D.Q ≤ D.a * (D.U * D.Q) :=
    le_trans hYnumber (le_trans hcentralPlus hpToAScaled)
  have haLower :
      2 / D.U + 2 * D.B / (D.U * D.Q) + 1 / D.Q ^ 2 ≤ D.a := by
    calc
      2 / D.U + 2 * D.B / (D.U * D.Q) + 1 / D.Q ^ 2 =
          (2 * D.B + 2 * D.Q + D.U / D.Q) / (D.U * D.Q) := by
            field_simp [hU.ne', hQ.ne']
            ring
      _ ≤ D.a := (div_le_iff₀ (mul_pos hU hQ)).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using haProduct)

  have hconvex :
      (2 / D.U + 2 * D.B / (D.U * D.Q) + 1 / D.Q ^ 2) +
          (1 / 4 : ℝ) * (2 + 1 / b) +
          (7 / 4 : ℝ) *
            (D.B + D.U + D.B / D.U + D.Q / D.U + 1 / D.Q) ≤
        D.a + S := by
    linarith only [haLower, hT1raw, hT2, hTraw]
  have hdecompose :
      (2 / D.U + 2 * D.B / (D.U * D.Q) + 1 / D.Q ^ 2) +
          (1 / 4 : ℝ) * (2 + 1 / b) +
          (7 / 4 : ℝ) *
            (D.B + D.U + D.B / D.U + D.Q / D.U + 1 / D.Q) =
        (9 / 4 : ℝ) +
          (1 / (4 * b) + 7 * b / 4 + 7 * D.U / 4 + 15 / (4 * D.U) +
            7 * b / (4 * D.U) + 7 * D.Q / (4 * D.U) +
            2 / (D.U * D.Q) + 2 * b / (D.U * D.Q) +
            7 / (4 * D.Q) + 1 / D.Q ^ 2) := by
    field_simp [hb.ne', hU.ne', hQ.ne']
    dsimp [b]
    ring
  rw [hdecompose] at hconvex
  have hamgm := hullSeven_type6_ten_term_amgm hb hU hQ
  have hscalar : (25 : ℝ) / 2 < D.a + S := by
    linarith
  dsimp [S] at hscalar
  linarith [D.area]

/-- Direct `v8` consequence of the cap-free raw-area scalar packet. -/
theorem hullSeven_v8_of_type6_raw_area {H : ℝ}
    (D : HullSevenType6RawAreaData H) :
    1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 < H := hullSeven_type6_raw_area D
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

end Heilbronn8.TriHull
