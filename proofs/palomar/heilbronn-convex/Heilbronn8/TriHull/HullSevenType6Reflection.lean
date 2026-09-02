import Heilbronn8.V8
import Mathlib.Analysis.MeanInequalities

/-!
# The reflected one-endpoint hull-seven chamber

This module contains the scalar proof used for hull-seven order type `type6`.
It is deliberately independent of the search certificates.

In the honest rotation-one determinant chart, reflection pairs corresponding
positive quantities and replaces every pair by its geometric mean.  Paired
Pluecker rows and multiplicative Minkowski give rows 3--8 below.  The first
two additive caps are separate geometric hypotheses: they do not follow from
the two reflected ear floors alone.  Thus `HullSevenType6ReflectionData` is
the small semantic seam whose cap fields still have to be justified or
dispatched by the determinant adapter.  The exact sign audit and the
unconditional six-row core live in `HullSevenType6ReflectionSignAudit`.

The scalar proof compresses the rows to two lower bounds for
`T = A + B + U` and one for `a`.  A single ten-term, forty-copy weighted
AM-GM estimate then gives the strict rational bound `25 / 2 < H`.
-/

namespace Heilbronn8.TriHull

open scoped BigOperators

/-- The forty-copy AM-GM pattern used in the type-6 closer.

The multiplicities are `4,2,15,5,1,7,1,1,3,1`.  Writing the theorem once
keeps the geometric proof below free of a forty-entry vector. -/
private lemma ten_term_amgm_4_2_15_5_1_7_1_1_3_1
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ}
    (h0 : 0 ≤ x0) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2)
    (h3 : 0 ≤ x3) (h4 : 0 ≤ x4) (h5 : 0 ≤ x5)
    (h6 : 0 ≤ x6) (h7 : 0 ≤ x7) (h8 : 0 ≤ x8)
    (h9 : 0 ≤ x9) :
    ((x0 / 4) ^ 4 * (x1 / 2) ^ 2 * (x2 / 15) ^ 15 *
          (x3 / 5) ^ 5 * x4 * (x5 / 7) ^ 7 * x6 * x7 *
          (x8 / 3) ^ 3 * x9) ^ ((40 : ℝ)⁻¹) ≤
      (4 * (x0 / 4) + 2 * (x1 / 2) + 15 * (x2 / 15) +
        5 * (x3 / 5) + x4 + 7 * (x5 / 7) + x6 + x7 +
        3 * (x8 / 3) + x9) / 40 := by
  have h := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin 10))
    ![(4 : ℝ), 2, 15, 5, 1, 7, 1, 1, 3, 1]
    ![x0 / 4, x1 / 2, x2 / 15, x3 / 5, x4,
      x5 / 7, x6, x7, x8 / 3, x9]
    (by
      intro i hi
      fin_cases i <;> norm_num)
    (by
      norm_num [Fin.sum_univ_succ])
    (by
      intro i hi
      fin_cases i <;> simp_all <;> positivity)
  norm_num [Fin.prod_univ_succ, Fin.sum_univ_succ] at h
  simpa only [Real.rpow_natCast, one_div, pow_one, add_zero, mul_one, one_mul,
    ← add_assoc, mul_assoc] using h

/-- The exact ten-term rational AM-GM certificate.

After splitting term `i` into `n_i` equal copies, the product is

`2^38 * 5^25 * 7^21 / (3^13 * 40^40)`.

The powers of `b`, `U`, and `Q` cancel.  The final exact comparison is
equivalent to `2^118 * 5^25 * 7^21 > 3^13 * 41^40`. -/
private lemma type6_ten_term_amgm {b U Q : ℝ}
    (hb : 0 < b) (hU : 0 < U) (hQ : 0 < Q) :
    (41 : ℝ) / 4 <
      1 / (4 * b) + 7 * b / 4 + 7 * U / 4 + 15 / (4 * U) +
      7 * b / (4 * U) + 7 * Q / (4 * U) + 2 / (U * Q) +
      2 * b / (U * Q) + 7 / (4 * Q) + 1 / Q ^ 2 := by
  have hamgm := ten_term_amgm_4_2_15_5_1_7_1_1_3_1
    (x0 := 1 / (4 * b))
    (x1 := 7 * b / 4)
    (x2 := 7 * U / 4)
    (x3 := 15 / (4 * U))
    (x4 := 7 * b / (4 * U))
    (x5 := 7 * Q / (4 * U))
    (x6 := 2 / (U * Q))
    (x7 := 2 * b / (U * Q))
    (x8 := 7 / (4 * Q))
    (x9 := 1 / Q ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity)
  have hproduct :
      ((1 / (4 * b) / 4) ^ 4 * (7 * b / 4 / 2) ^ 2 *
          (7 * U / 4 / 15) ^ 15 * (15 / (4 * U) / 5) ^ 5 *
          (7 * b / (4 * U)) * (7 * Q / (4 * U) / 7) ^ 7 *
          (2 / (U * Q)) * (2 * b / (U * Q)) *
          (7 / (4 * Q) / 3) ^ 3 * (1 / Q ^ 2)) =
        ((2 : ℝ) ^ 38 * 5 ^ 25 * 7 ^ 21) /
          (3 ^ 13 * 40 ^ 40) := by
    field_simp [hb.ne', hU.ne', hQ.ne']
    ring
  have hweightedSum :
      (4 * (1 / (4 * b) / 4) + 2 * (7 * b / 4 / 2) +
          15 * (7 * U / 4 / 15) + 5 * (15 / (4 * U) / 5) +
          7 * b / (4 * U) + 7 * (7 * Q / (4 * U) / 7) +
          2 / (U * Q) + 2 * b / (U * Q) +
          3 * (7 / (4 * Q) / 3) + 1 / Q ^ 2) / 40 =
        (1 / (4 * b) + 7 * b / 4 + 7 * U / 4 + 15 / (4 * U) +
          7 * b / (4 * U) + 7 * Q / (4 * U) + 2 / (U * Q) +
          2 * b / (U * Q) + 7 / (4 * Q) + 1 / Q ^ 2) / 40 := by
    ring
  rw [hproduct, hweightedSum] at hamgm
  have hconstant :
      ((41 : ℝ) / 160) ^ 40 <
        ((2 : ℝ) ^ 38 * 5 ^ 25 * 7 ^ 21) /
          (3 ^ 13 * 40 ^ 40) := by
    norm_num
  have hroot :
      (41 : ℝ) / 160 <
        (((2 : ℝ) ^ 38 * 5 ^ 25 * 7 ^ 21) /
          (3 ^ 13 * 40 ^ 40)) ^ ((40 : ℝ)⁻¹) := by
    calc
      (41 : ℝ) / 160 =
          (((41 : ℝ) / 160) ^ 40) ^ ((40 : ℝ)⁻¹) := by
            symm
            exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
      _ < (((2 : ℝ) ^ 38 * 5 ^ 25 * 7 ^ 21) /
          (3 ^ 13 * 40 ^ 40)) ^ ((40 : ℝ)⁻¹) :=
        Real.rpow_lt_rpow (by positivity) hconstant (by positivity)
  linarith

/-- Public scalar interface to the exact type-6 ten-term AM-GM estimate. -/
lemma hullSeven_type6_ten_term_amgm {b U Q : ℝ}
    (hb : 0 < b) (hU : 0 < U) (hQ : 0 < Q) :
    (41 : ℝ) / 4 <
      1 / (4 * b) + 7 * b / 4 + 7 * U / 4 + 15 / (4 * U) +
      7 * b / (4 * U) + 7 * Q / (4 * U) + 2 / (U * Q) +
      2 * b / (U * Q) + 7 / (4 * Q) + 1 / Q ^ 2 :=
  type6_ten_term_amgm hb hU hQ

/-- Pairwise-geometric-mean data supplied by the reflected type-6 chamber.

In the honest rotation-one chart, the intended reflection pairs are

`A↔G, B↔a5, C↔D, p↔n, q↔e1, R↔k, e↔h, L↔l, x↔c`,

with `a0` and the positive middle chord `m` fixed.  Rows 3--8 are obtained
from paired Pluecker equations and multiplicative Minkowski, weakening the
auxiliary normalized floors to one.  The first two cap fields remain explicit
because reflected raw ear floors do not imply them.  Keeping this interface
independent of coordinates makes the sign and determinant adapter auditable
in isolation. -/
structure HullSevenType6ReflectionData (H : ℝ) where
  a : ℝ
  A : ℝ
  B : ℝ
  U : ℝ
  P : ℝ
  Q : ℝ
  R : ℝ
  E : ℝ
  a_ge : 1 ≤ a
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  U_ge : 1 ≤ U
  P_ge : 1 ≤ P
  Q_ge : 1 ≤ Q
  R_ge : 1 ≤ R
  E_ge : 1 ≤ E
  p_cap : P ≤ A + B - 1
  q_cap : Q ≤ B + U - 1
  central : B + A * U ≤ P * Q
  right_cap : R + Q ≤ A * U
  p_to_a : 1 + P ≤ a * U
  e_to_a : E + A ≤ a * Q
  p_e_to_r : P + B * E ≤ A * R
  terminal : 1 + A * B ≤ R * E
  area : a + 2 * (A + B + U) ≤ H

/-- The reflected type-6 scalar rows force hull area strictly above `25/2`. -/
theorem hullSeven_type6_reflection_area {H : ℝ}
    (D : HullSevenType6ReflectionData H) :
    (25 : ℝ) / 2 < H := by
  let b : ℝ := D.B - 1
  let T : ℝ := D.A + D.B + D.U
  let X : ℝ := D.A * D.U - D.Q
  let Y : ℝ := X - D.B
  have ha : 0 < D.a := lt_of_lt_of_le zero_lt_one D.a_ge
  have hA : 0 < D.A := lt_of_lt_of_le zero_lt_one D.A_ge
  have hB : 0 < D.B := lt_of_lt_of_le zero_lt_one D.B_ge
  have hU : 0 < D.U := lt_of_lt_of_le zero_lt_one D.U_ge
  have hP : 0 < D.P := lt_of_lt_of_le zero_lt_one D.P_ge
  have hQ : 0 < D.Q := lt_of_lt_of_le zero_lt_one D.Q_ge
  have hR : 0 < D.R := lt_of_lt_of_le zero_lt_one D.R_ge
  have hE : 0 < D.E := lt_of_lt_of_le zero_lt_one D.E_ge

  have hpCap : D.P ≤ D.A + b := by
    dsimp [b]
    linarith [D.p_cap]
  have hqCap : D.Q ≤ D.U + b := by
    dsimp [b]
    linarith [D.q_cap]
  have hpqCap : D.P * D.Q ≤ (D.A + b) * (D.U + b) := calc
    D.P * D.Q ≤ (D.A + b) * D.Q :=
      mul_le_mul_of_nonneg_right hpCap hQ.le
    _ ≤ (D.A + b) * (D.U + b) :=
      mul_le_mul_of_nonneg_left hqCap (by dsimp [b]; linarith [D.A_ge, D.B_ge])
  have hbProduct : 1 ≤ b * (T - 2) := by
    dsimp [b, T] at hpqCap ⊢
    nlinarith [D.central]
  have hTminus : 1 ≤ T - 2 := by
    dsimp [T]
    linarith [D.A_ge, D.B_ge, D.U_ge]
  have hb : 0 < b := by
    by_contra hn
    have hb0 : b ≤ 0 := le_of_not_gt hn
    have : b * (T - 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb0 (by linarith)
    linarith
  have hT1 : 2 + 1 / b ≤ T := by
    have : 1 / b ≤ T - 2 := (div_le_iff₀ hb).2 (by
      nlinarith [hbProduct])
    linarith

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
      _ ≤ D.A := (div_le_iff₀ hU).2 (by simpa [mul_comm] using hAUlower)
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
    have := mul_le_mul_of_nonneg_left D.p_to_a hQ.le
    nlinarith
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
        D.a + 2 * T := by
    linarith only [haLower, hT1, hT2]
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
  have hamgm := type6_ten_term_amgm hb hU hQ
  have hscalar : (25 : ℝ) / 2 < D.a + 2 * T := by
    linarith
  dsimp [T] at hscalar
  linarith [D.area]

/-- Direct `v8` consequence for the retained population-108 chamber. -/
theorem hullSeven_v8_of_type6_reflection {H : ℝ}
    (D : HullSevenType6ReflectionData H) :
    1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 < H := hullSeven_type6_reflection_area D
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

end Heilbronn8.TriHull
