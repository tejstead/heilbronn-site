import Mathlib

/-!
# The negative-outer branch of the exceptional CAB type-717 cell

This file closes the only branch not covered by the opposite-ear argument:
`DPR < 0` and `AQR > 0`.  It is a homogeneous, certificate-free scalar
argument.  Two copies of one elementary product estimate force enough area
in the outer fan variables to reach the sharp `25 / 2` threshold.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private lemma product_lt_two_sq
    {m x y : ℝ}
    (hm : 0 < m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsum : 4 * (x + y) < 11 * m) :
    x * y < 2 * m ^ 2 := by
  have hsq : 64 * x * y ≤ 16 * (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have hminus : 0 < 11 * m - 4 * (x + y) := by linarith
  have hplus : 0 < 11 * m + 4 * (x + y) := by
    nlinarith
  have hwindow := mul_pos hminus hplus
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hm
  nlinarith

/-- One side of the negative-outer CAB estimate.

In the geometry adapter, `beta = u + x`, `N = e + f + r`, and the displayed
cross inequality is obtained by combining a pair Pluecker identity with the
negative `DPR` floor.  The reflected side has exactly the same form. -/
theorem hullFive300_cab717_negative_one_side
    {m N a f r beta : ℝ}
    (hm : 0 < m) (hN : 0 < N)
    (ha : m ≤ a) (hf : m ≤ f) (hr : m ≤ r)
    (hbeta : 2 * m ≤ beta)
    (hcross :
      m * (N + 2 * a) * (f + r) ≤
        beta * (f * (a + N) - m * N)) :
    19 * m ≤ 4 * (beta + f) := by
  by_contra hnot
  have hsum : 4 * (beta + f) < 19 * m := lt_of_not_ge hnot

  have hx₁ : 0 ≤ beta - m := by nlinarith
  have hy₁ : 0 ≤ f - m := by nlinarith
  have hsum₁ : 4 * ((beta - m) + (f - m)) < 11 * m := by
    nlinarith
  have hprod₁ : (beta - m) * (f - m) < 2 * m ^ 2 :=
    product_lt_two_sq hm hx₁ hy₁ hsum₁

  have hx₂ : 0 ≤ beta - 2 * m := by nlinarith
  have hy₂ : 0 ≤ f := by linarith
  have hsum₂ : 4 * ((beta - 2 * m) + f) < 11 * m := by
    nlinarith
  have hprod₂ : (beta - 2 * m) * f < 2 * m ^ 2 :=
    product_lt_two_sq hm hx₂ hy₂ hsum₂

  let A : ℝ := (beta - m) * (f - m) - m * (r + m)
  let B : ℝ := f * (beta - 2 * m) - 2 * m * r
  have hmr : 2 * m ^ 2 ≤ m * (r + m) := by
    have hmr' : m * m ≤ m * r :=
      mul_le_mul_of_nonneg_left hr hm.le
    nlinarith
  have htwoMr : 2 * m ^ 2 ≤ 2 * m * r := by
    have hmr' : m * m ≤ m * r :=
      mul_le_mul_of_nonneg_left hr hm.le
    nlinarith
  have hAneg : A < 0 := by
    dsimp only [A]
    nlinarith
  have hBneg : B < 0 := by
    dsimp only [B]
    nlinarith

  have hdiff :
      0 ≤ beta * (f * (a + N) - m * N) -
        m * (N + 2 * a) * (f + r) := by
    linarith
  have hid :
      beta * (f * (a + N) - m * N) -
          m * (N + 2 * a) * (f + r) =
        N * A + a * B := by
    dsimp only [A, B]
    ring
  rw [hid] at hdiff
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  have hNA : N * A < 0 := mul_neg_of_pos_of_neg hN hAneg
  have haB : a * B < 0 := mul_neg_of_pos_of_neg ha0 hBneg
  linarith

/-- Symmetric closure of the `DPR < 0`, `AQR > 0` branch.

The first cross inequality is the `D`-side estimate and the second is its
`A`-side mirror.  In the geometric chart

`H = a + d + r + (beta + f) + (delta + e)`.
-/
theorem hullFive300_cab717_negative_hull_bound
    {m N a d e f r beta delta H : ℝ}
    (hm : 0 < m) (hN : 0 < N)
    (ha : m ≤ a) (hd : m ≤ d)
    (he : m ≤ e) (hf : m ≤ f) (hr : m ≤ r)
    (hbeta : 2 * m ≤ beta) (hdelta : 2 * m ≤ delta)
    (hDcross :
      m * (N + 2 * a) * (f + r) ≤
        beta * (f * (a + N) - m * N))
    (hAcross :
      m * (N + 2 * d) * (e + r) ≤
        delta * (e * (d + N) - m * N))
    (hH : H = a + d + r + (beta + f) + (delta + e)) :
    25 * m ≤ 2 * H := by
  have hD := hullFive300_cab717_negative_one_side
    hm hN ha hf hr hbeta hDcross
  have hA := hullFive300_cab717_negative_one_side
    hm hN hd he hr hdelta hAcross
  rw [hH]
  nlinarith

end Heilbronn8.TriHull
