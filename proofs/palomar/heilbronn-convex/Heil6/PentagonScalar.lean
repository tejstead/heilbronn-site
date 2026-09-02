import Mathlib

set_option linter.style.header false

/-!
# The scalar core of the `h = 5` case for six points

Let `P` be the interior point of a strictly convex pentagon and translate
`P` to the origin.  For cyclic hull vertices `v₀,…,v₄`, put

* `aᵢ = det(vᵢ,vᵢ₊₁)`;
* `bᵢ = det(vᵢ,vᵢ₊₂)`.

The doubled hull area is `a₀ + ⋯ + a₄`.  Every labelled triangle having
area at least `m` gives the fan and diagonal floors below.  The ear and long
hull-triangle formulas are

```
m ≤ aᵢ + aᵢ₊₁ - bᵢ,
0 < aᵢ + bᵢ₊₁ + bᵢ₊₃,
```

and the five Grassmann--Pluecker identities are

```
aᵢ aᵢ₊₂ = bᵢ bᵢ₊₁ + aᵢ₊₁ bᵢ₊₃.
```

This file deliberately contains only fixed real variables and polynomial
inequalities.  A later geometry adapter should derive these hypotheses from
the determinant definitions.  No cyclic-index or convex-hull API is needed
by the scalar theorem.
-/

namespace N6Scratch
namespace PentagonScalar

private lemma floor_of_abs_of_nonneg {m x : ℝ}
    (habs : m ≤ |x|) (hx : 0 ≤ x) : m ≤ x := by
  simpa only [abs_of_nonneg hx] using habs

private lemma neg_floor_of_abs {m x : ℝ}
    (habs : m ≤ |x|) (hx : x < 0) : x ≤ -m := by
  rw [abs_of_neg hx] at habs
  linarith

private lemma floor_mul_floor {m x y : ℝ}
    (hm : 0 ≤ m) (hx : m ≤ x) (hy : m ≤ y) : m * m ≤ x * y := by
  exact mul_le_mul hx hy hm (hm.trans hx)

/-- If `xy ≥ 2m²`, then the pair sum is strictly larger than `12m/5`.
The rational constant avoids introducing `Real.sqrt 2`. -/
private lemma twelve_mul_lt_five_mul_add {m x y : ℝ}
    (hm : 0 < m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hprod : 2 * m * m ≤ x * y) :
    12 * m < 5 * (x + y) := by
  by_contra h
  have hle : 5 * (x + y) ≤ 12 * m := le_of_not_gt h
  have hleft : 0 ≤ 12 * m - 5 * (x + y) := sub_nonneg.mpr hle
  have hright : 0 ≤ 12 * m + 5 * (x + y) := by
    nlinarith
  have hmul := mul_nonneg hleft hright
  have hmm : 0 < m * m := mul_pos hm hm
  nlinarith [hmul, sq_nonneg (x - y)]

/-- The all-positive-diagonal sign chamber is separated strictly from `6m`. -/
theorem all_nonnegative_strict
    (m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hm : 0 < m)
    (ha0 : m ≤ a0) (ha1 : m ≤ a1) (ha2 : m ≤ a2)
    (ha3 : m ≤ a3) (ha4 : m ≤ a4)
    (hab0 : m ≤ |b0|) (hab1 : m ≤ |b1|) (hab2 : m ≤ |b2|)
    (hab3 : m ≤ |b3|) (hab4 : m ≤ |b4|)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4)
    (hR0 : a0 * a2 = b0 * b1 + a1 * b3)
    (hR1 : a1 * a3 = b1 * b2 + a2 * b4)
    (hR2 : a2 * a4 = b2 * b3 + a3 * b0)
    (hR3 : a3 * a0 = b3 * b4 + a4 * b1)
    (hR4 : a4 * a1 = b4 * b0 + a0 * b2) :
    6 * m < a0 + a1 + a2 + a3 + a4 := by
  have hm0 : 0 ≤ m := le_of_lt hm
  have hb0m := floor_of_abs_of_nonneg hab0 hb0
  have hb1m := floor_of_abs_of_nonneg hab1 hb1
  have hb2m := floor_of_abs_of_nonneg hab2 hb2
  have hb3m := floor_of_abs_of_nonneg hab3 hb3
  have hb4m := floor_of_abs_of_nonneg hab4 hb4
  have hp0 : 2 * m * m ≤ a0 * a2 := by
    have h01 := floor_mul_floor hm0 hb0m hb1m
    have h13 := floor_mul_floor hm0 ha1 hb3m
    nlinarith [hR0]
  have hp1 : 2 * m * m ≤ a1 * a3 := by
    have h12 := floor_mul_floor hm0 hb1m hb2m
    have h24 := floor_mul_floor hm0 ha2 hb4m
    nlinarith [hR1]
  have hp2 : 2 * m * m ≤ a2 * a4 := by
    have h23 := floor_mul_floor hm0 hb2m hb3m
    have h30 := floor_mul_floor hm0 ha3 hb0m
    nlinarith [hR2]
  have hp3 : 2 * m * m ≤ a3 * a0 := by
    have h34 := floor_mul_floor hm0 hb3m hb4m
    have h41 := floor_mul_floor hm0 ha4 hb1m
    nlinarith [hR3]
  have hp4 : 2 * m * m ≤ a4 * a1 := by
    have h40 := floor_mul_floor hm0 hb4m hb0m
    have h02 := floor_mul_floor hm0 ha0 hb2m
    nlinarith [hR4]
  have h02 := twelve_mul_lt_five_mul_add hm (hm0.trans ha0) (hm0.trans ha2) hp0
  have h13 := twelve_mul_lt_five_mul_add hm (hm0.trans ha1) (hm0.trans ha3) hp1
  have h24 := twelve_mul_lt_five_mul_add hm (hm0.trans ha2) (hm0.trans ha4) hp2
  have h30 := twelve_mul_lt_five_mul_add hm (hm0.trans ha3) (hm0.trans ha0) hp3
  have h41 := twelve_mul_lt_five_mul_add hm (hm0.trans ha4) (hm0.trans ha1) hp4
  linarith

private lemma four_mul_le_three_sum_of_two_products
    {m x y z : ℝ} (hm : 0 < m)
    (hx : m ≤ x) (hy : m ≤ y) (hz : m ≤ z)
    (hxz : 2 * m * m ≤ x * z) (hyz : 2 * m * m ≤ y * z) :
    4 * m ≤ x + y + z := by
  by_contra h
  have hlt : x + y + z < 4 * m := lt_of_not_ge h
  have hsumpos : 0 < x + y + z := by linarith
  have hgap : 0 < (4 * m - (x + y + z)) * (4 * m + (x + y + z)) :=
    mul_pos (sub_pos.mpr hlt) (by linarith)
  have hprod : 4 * m * m ≤ (x + y) * z := by
    nlinarith
  nlinarith [hgap, sq_nonneg ((x + y) - z)]

/-- The chamber with exactly `b₀` negative is also strictly separated.
Equality in its preliminary AM--GM estimate would force `b₀ = 0`. -/
theorem one_negative_zero_strict
    (m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hm : 0 < m)
    (ha0 : m ≤ a0) (ha1 : m ≤ a1) (ha2 : m ≤ a2)
    (ha3 : m ≤ a3) (ha4 : m ≤ a4)
    (hab0 : m ≤ |b0|) (hab1 : m ≤ |b1|) (hab2 : m ≤ |b2|)
    (hab3 : m ≤ |b3|) (hab4 : m ≤ |b4|)
    (hb0 : b0 < 0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4)
    (hR0 : a0 * a2 = b0 * b1 + a1 * b3)
    (hR1 : a1 * a3 = b1 * b2 + a2 * b4)
    (_hR2 : a2 * a4 = b2 * b3 + a3 * b0)
    (hR3 : a3 * a0 = b3 * b4 + a4 * b1)
    (_hR4 : a4 * a1 = b4 * b0 + a0 * b2) :
    6 * m < a0 + a1 + a2 + a3 + a4 := by
  have hm0 : 0 ≤ m := le_of_lt hm
  have hb0m := neg_floor_of_abs hab0 hb0
  have hb1m := floor_of_abs_of_nonneg hab1 hb1
  have hb2m := floor_of_abs_of_nonneg hab2 hb2
  have hb3m := floor_of_abs_of_nonneg hab3 hb3
  have hb4m := floor_of_abs_of_nonneg hab4 hb4
  have hp13 : 2 * m * m ≤ a1 * a3 := by
    have h12 := floor_mul_floor hm0 hb1m hb2m
    have h24 := floor_mul_floor hm0 ha2 hb4m
    nlinarith only [hR1, h12, h24]
  have hp30 : 2 * m * m ≤ a0 * a3 := by
    have h34 := floor_mul_floor hm0 hb3m hb4m
    have h41 := floor_mul_floor hm0 ha4 hb1m
    nlinarith only [hR3, h34, h41]
  have hgroup := four_mul_le_three_sum_of_two_products hm ha0 ha1 ha3 hp30 hp13
  by_contra h
  have hsum : a0 + a1 + a2 + a3 + a4 ≤ 6 * m := le_of_not_gt h
  have hgroupEq : a0 + a1 + a3 = 4 * m := by linarith
  have ha2Eq : a2 = m := by linarith
  have ha4Eq : a4 = m := by linarith
  have hsum01 : a0 + a1 = 4 * m - a3 := by linarith
  have hprodGroup : 4 * m * m ≤ (a0 + a1) * a3 := by
    nlinarith only [hp30, hp13]
  have hprodGroup' : 4 * m * m ≤ (4 * m - a3) * a3 := by
    calc
      4 * m * m ≤ (a0 + a1) * a3 := hprodGroup
      _ = (4 * m - a3) * a3 := by rw [hsum01]
  have ha3Eq : a3 = 2 * m := by
    have hsqLe : (a3 - 2 * m) * (a3 - 2 * m) ≤ 0 := by
      nlinarith only [hprodGroup']
    have hsqEq : (a3 - 2 * m) * (a3 - 2 * m) = 0 :=
      le_antisymm hsqLe (mul_self_nonneg _)
    rcases mul_eq_zero.mp hsqEq with hz | hz <;> linarith
  have ha0Eq : a0 = m := by linarith
  have ha1Eq : a1 = m := by linarith
  rw [ha1Eq, ha2Eq, ha3Eq] at hR1
  rw [ha3Eq, ha0Eq, ha4Eq] at hR3
  rw [ha0Eq, ha1Eq, ha2Eq] at hR0
  have h12 := floor_mul_floor hm0 hb1m hb2m
  have hmb4 := floor_mul_floor hm0 (le_refl m) hb4m
  have hb12Eq : b1 * b2 = m * m := by
    nlinarith only [hR1, h12, hmb4]
  have hmb4Eq : m * b4 = m * m := by
    nlinarith only [hR1, h12, hmb4]
  have hb4Eq : b4 = m := by
    have hz : m * (b4 - m) = 0 := by nlinarith only [hmb4Eq]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact False.elim ((ne_of_gt hm) hz)
    · linarith only [hz]
  have hb2Le : b2 ≤ m := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hb1m) (hm0.trans hb2m)
    nlinarith only [hnonneg, hb12Eq, hm]
  have hb2Eq : b2 = m := le_antisymm hb2Le hb2m
  rw [hb2Eq] at hb12Eq
  have hb1Eq : b1 = m := by
    have hz : (b1 - m) * m = 0 := by nlinarith only [hb12Eq]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith only [hz]
    · exact False.elim ((ne_of_gt hm) hz)
  rw [hb4Eq, hb1Eq] at hR3
  have hb3Eq : b3 = m := by
    have hz : (b3 - m) * m = 0 := by nlinarith only [hR3]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith only [hz]
    · exact False.elim ((ne_of_gt hm) hz)
  rw [hb1Eq, hb3Eq] at hR0
  have hb0mNeg : b0 * m < 0 := mul_neg_of_neg_of_pos hb0 hm
  nlinarith only [hR0, hb0mNeg]

/-- The chamber with two adjacent negative diagonals is impossible at or below
`6m`.  The three ear estimates consume the full possible surplus and `R₀` then
has two terms of size at least `m²`. -/
theorem two_adjacent_negative_zero_one_strict
    (m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hm : 0 < m)
    (ha0 : m ≤ a0) (ha1 : m ≤ a1) (ha2 : m ≤ a2)
    (ha3 : m ≤ a3) (ha4 : m ≤ a4)
    (hab0 : m ≤ |b0|) (hab1 : m ≤ |b1|) (hab2 : m ≤ |b2|)
    (hab3 : m ≤ |b3|) (hab4 : m ≤ |b4|)
    (hb0 : b0 < 0) (hb1 : b1 < 0) (hb2 : 0 ≤ b2)
    (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4)
    (_hear0 : m ≤ a0 + a1 - b0)
    (_hear1 : m ≤ a1 + a2 - b1)
    (hear2 : m ≤ a2 + a3 - b2)
    (hear3 : m ≤ a3 + a4 - b3)
    (hear4 : m ≤ a4 + a0 - b4)
    (hR0 : a0 * a2 = b0 * b1 + a1 * b3)
    (_hR1 : a1 * a3 = b1 * b2 + a2 * b4)
    (hR2 : a2 * a4 = b2 * b3 + a3 * b0)
    (hR3 : a3 * a0 = b3 * b4 + a4 * b1)
    (_hR4 : a4 * a1 = b4 * b0 + a0 * b2) :
    6 * m < a0 + a1 + a2 + a3 + a4 := by
  have hm0 : 0 ≤ m := le_of_lt hm
  have hb0m := neg_floor_of_abs hab0 hb0
  have hb1m := neg_floor_of_abs hab1 hb1
  have hb2m := floor_of_abs_of_nonneg hab2 hb2
  have hb3m := floor_of_abs_of_nonneg hab3 hb3
  have hb4m := floor_of_abs_of_nonneg hab4 hb4
  by_contra h
  have hsum : a0 + a1 + a2 + a3 + a4 ≤ 6 * m := le_of_not_gt h
  have hcap2 : b2 ≤ a2 + a3 - m := by linarith
  have hcap3 : b3 ≤ a3 + a4 - m := by linarith
  have hcap4 : b4 ≤ a4 + a0 - m := by linarith
  have hcap2nonneg : 0 ≤ a2 + a3 - m := (hm0.trans hb2m).trans hcap2
  have hcap3nonneg : 0 ≤ a3 + a4 - m := (hm0.trans hb3m).trans hcap3
  have hcap4nonneg : 0 ≤ a4 + a0 - m := (hm0.trans hb4m).trans hcap4
  have hu23 : b2 * b3 ≤ (a2 + a3 - m) * (a3 + a4 - m) :=
    mul_le_mul hcap2 hcap3 (hm0.trans hb3m) hcap2nonneg
  have ha3b0 : a3 * b0 ≤ a3 * (-m) :=
    mul_le_mul_of_nonneg_left hb0m (hm0.trans ha3)
  have hl23 : a2 * a4 + a3 * m ≤ b2 * b3 := by
    nlinarith only [hR2, ha3b0]
  have hcore3 : m * m ≤ (a3 - m) * (a2 + a3 + a4 - 2 * m) := by
    nlinarith only [hu23, hl23]
  have hfactor3 : a2 + a3 + a4 - 2 * m ≤ 2 * m := by
    linarith
  have huCore3 :
      (a3 - m) * (a2 + a3 + a4 - 2 * m) ≤ (a3 - m) * (2 * m) :=
    mul_le_mul_of_nonneg_left hfactor3 (sub_nonneg.mpr ha3)
  have hx3 : m ≤ 2 * (a3 - m) := by
    by_contra hx
    have hxlt : 2 * (a3 - m) < m := lt_of_not_ge hx
    have := mul_lt_mul_of_pos_left hxlt hm
    nlinarith
  have hu34 : b3 * b4 ≤ (a3 + a4 - m) * (a4 + a0 - m) :=
    mul_le_mul hcap3 hcap4 (hm0.trans hb4m) hcap3nonneg
  have ha4b1 : a4 * b1 ≤ a4 * (-m) :=
    mul_le_mul_of_nonneg_left hb1m (hm0.trans ha4)
  have hl34 : a3 * a0 + a4 * m ≤ b3 * b4 := by
    nlinarith only [hR3, ha4b1]
  have hcore4 : m * m ≤ (a4 - m) * (a0 + a3 + a4 - 2 * m) := by
    nlinarith only [hu34, hl34]
  have hfactor4 : a0 + a3 + a4 - 2 * m ≤ 2 * m := by
    linarith
  have huCore4 :
      (a4 - m) * (a0 + a3 + a4 - 2 * m) ≤ (a4 - m) * (2 * m) :=
    mul_le_mul_of_nonneg_left hfactor4 (sub_nonneg.mpr ha4)
  have hx4 : m ≤ 2 * (a4 - m) := by
    by_contra hx
    have hxlt : 2 * (a4 - m) < m := lt_of_not_ge hx
    have := mul_lt_mul_of_pos_left hxlt hm
    nlinarith
  have ha0Eq : a0 = m := by
    nlinarith only [hsum, ha0, ha1, ha2, ha3, ha4, hx3, hx4]
  have ha1Eq : a1 = m := by
    nlinarith only [hsum, ha0, ha1, ha2, ha3, ha4, hx3, hx4]
  have ha2Eq : a2 = m := by
    nlinarith only [hsum, ha0, ha1, ha2, ha3, ha4, hx3, hx4]
  rw [ha0Eq, ha2Eq] at hR0
  have hnegprod : m * m ≤ b0 * b1 := by
    have h := floor_mul_floor hm0
      (show m ≤ -b0 by linarith only [hb0m])
      (show m ≤ -b1 by linarith only [hb1m])
    nlinarith only [h]
  have hposprod := floor_mul_floor hm0 ha1 hb3m
  nlinarith only [hR0, hnegprod, hposprod, hm]

/-- Under the `6m` cap, two negative `b` variables cannot be cyclically
nonadjacent.  This is exactly where the long hull-triangle rows enter. -/
theorem sign_cover_under_six
    (m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hm : 0 < m)
    (ha0 : m ≤ a0) (ha1 : m ≤ a1) (ha2 : m ≤ a2)
    (ha3 : m ≤ a3) (ha4 : m ≤ a4)
    (hab0 : m ≤ |b0|) (hab1 : m ≤ |b1|) (hab2 : m ≤ |b2|)
    (hab3 : m ≤ |b3|) (hab4 : m ≤ |b4|)
    (hsum : a0 + a1 + a2 + a3 + a4 ≤ 6 * m)
    (hq0 : 0 < a0 + b1 + b3)
    (hq1 : 0 < a1 + b2 + b4)
    (hq2 : 0 < a2 + b3 + b0)
    (hq3 : 0 < a3 + b4 + b1)
    (hq4 : 0 < a4 + b0 + b2) :
    (0 ≤ b0 ∧ 0 ≤ b1 ∧ 0 ≤ b2 ∧ 0 ≤ b3 ∧ 0 ≤ b4) ∨
    (b0 < 0 ∧ 0 ≤ b1 ∧ 0 ≤ b2 ∧ 0 ≤ b3 ∧ 0 ≤ b4) ∨
    (b1 < 0 ∧ 0 ≤ b2 ∧ 0 ≤ b3 ∧ 0 ≤ b4 ∧ 0 ≤ b0) ∨
    (b2 < 0 ∧ 0 ≤ b3 ∧ 0 ≤ b4 ∧ 0 ≤ b0 ∧ 0 ≤ b1) ∨
    (b3 < 0 ∧ 0 ≤ b4 ∧ 0 ≤ b0 ∧ 0 ≤ b1 ∧ 0 ≤ b2) ∨
    (b4 < 0 ∧ 0 ≤ b0 ∧ 0 ≤ b1 ∧ 0 ≤ b2 ∧ 0 ≤ b3) ∨
    (b0 < 0 ∧ b1 < 0 ∧ 0 ≤ b2 ∧ 0 ≤ b3 ∧ 0 ≤ b4) ∨
    (b1 < 0 ∧ b2 < 0 ∧ 0 ≤ b3 ∧ 0 ≤ b4 ∧ 0 ≤ b0) ∨
    (b2 < 0 ∧ b3 < 0 ∧ 0 ≤ b4 ∧ 0 ≤ b0 ∧ 0 ≤ b1) ∨
    (b3 < 0 ∧ b4 < 0 ∧ 0 ≤ b0 ∧ 0 ≤ b1 ∧ 0 ≤ b2) ∨
    (b4 < 0 ∧ b0 < 0 ∧ 0 ≤ b1 ∧ 0 ≤ b2 ∧ 0 ≤ b3) := by
  have ha0u : a0 ≤ 2 * m := by linarith
  have ha1u : a1 ≤ 2 * m := by linarith
  have ha2u : a2 ≤ 2 * m := by linarith
  have ha3u : a3 ≤ 2 * m := by linarith
  have ha4u : a4 ≤ 2 * m := by linarith
  have h02 : ¬ (b0 < 0 ∧ b2 < 0) := by
    rintro ⟨hb0, hb2⟩
    have h0 := neg_floor_of_abs hab0 hb0
    have h2 := neg_floor_of_abs hab2 hb2
    linarith
  have h03 : ¬ (b0 < 0 ∧ b3 < 0) := by
    rintro ⟨hb0, hb3⟩
    have h0 := neg_floor_of_abs hab0 hb0
    have h3 := neg_floor_of_abs hab3 hb3
    linarith
  have h13 : ¬ (b1 < 0 ∧ b3 < 0) := by
    rintro ⟨hb1, hb3⟩
    have h1 := neg_floor_of_abs hab1 hb1
    have h3 := neg_floor_of_abs hab3 hb3
    linarith
  have h14 : ¬ (b1 < 0 ∧ b4 < 0) := by
    rintro ⟨hb1, hb4⟩
    have h1 := neg_floor_of_abs hab1 hb1
    have h4 := neg_floor_of_abs hab4 hb4
    linarith
  have h24 : ¬ (b2 < 0 ∧ b4 < 0) := by
    rintro ⟨hb2, hb4⟩
    have h2 := neg_floor_of_abs hab2 hb2
    have h4 := neg_floor_of_abs hab4 hb4
    linarith
  by_cases hb0 : 0 ≤ b0 <;>
    by_cases hb1 : 0 ≤ b1 <;>
    by_cases hb2 : 0 ≤ b2 <;>
    by_cases hb3 : 0 ≤ b3 <;>
    by_cases hb4 : 0 ≤ b4 <;>
    simp_all only [not_le] <;> aesop

/-- Complete fixed-variable `h = 5` scalar theorem. -/
theorem pentagon_strict
    (m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ)
    (hm : 0 < m)
    (ha0 : m ≤ a0) (ha1 : m ≤ a1) (ha2 : m ≤ a2)
    (ha3 : m ≤ a3) (ha4 : m ≤ a4)
    (hab0 : m ≤ |b0|) (hab1 : m ≤ |b1|) (hab2 : m ≤ |b2|)
    (hab3 : m ≤ |b3|) (hab4 : m ≤ |b4|)
    (hear0 : m ≤ a0 + a1 - b0) (hear1 : m ≤ a1 + a2 - b1)
    (hear2 : m ≤ a2 + a3 - b2) (hear3 : m ≤ a3 + a4 - b3)
    (hear4 : m ≤ a4 + a0 - b4)
    (hq0 : 0 < a0 + b1 + b3) (hq1 : 0 < a1 + b2 + b4)
    (hq2 : 0 < a2 + b3 + b0) (hq3 : 0 < a3 + b4 + b1)
    (hq4 : 0 < a4 + b0 + b2)
    (hR0 : a0 * a2 = b0 * b1 + a1 * b3)
    (hR1 : a1 * a3 = b1 * b2 + a2 * b4)
    (hR2 : a2 * a4 = b2 * b3 + a3 * b0)
    (hR3 : a3 * a0 = b3 * b4 + a4 * b1)
    (hR4 : a4 * a1 = b4 * b0 + a0 * b2) :
    6 * m < a0 + a1 + a2 + a3 + a4 := by
  by_contra h
  have hsum : a0 + a1 + a2 + a3 + a4 ≤ 6 * m := le_of_not_gt h
  rcases sign_cover_under_six m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hm
      ha0 ha1 ha2 ha3 ha4 hab0 hab1 hab2 hab3 hab4 hsum hq0 hq1 hq2 hq3 hq4 with
    hall | h0 | h1 | h2 | h3 | h4 | h01 | h12 | h23 | h34 | h40
  · exact h (all_nonnegative_strict m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hm
      ha0 ha1 ha2 ha3 ha4 hab0 hab1 hab2 hab3 hab4
      hall.1 hall.2.1 hall.2.2.1 hall.2.2.2.1 hall.2.2.2.2 hR0 hR1 hR2 hR3 hR4)
  · exact h (one_negative_zero_strict m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hm
      ha0 ha1 ha2 ha3 ha4 hab0 hab1 hab2 hab3 hab4
      h0.1 h0.2.1 h0.2.2.1 h0.2.2.2.1 h0.2.2.2.2 hR0 hR1 hR2 hR3 hR4)
  · exact h (by
      have := one_negative_zero_strict m a1 a2 a3 a4 a0 b1 b2 b3 b4 b0 hm
        ha1 ha2 ha3 ha4 ha0 hab1 hab2 hab3 hab4 hab0
        h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2 hR1 hR2 hR3 hR4 hR0
      linarith)
  · exact h (by
      have := one_negative_zero_strict m a2 a3 a4 a0 a1 b2 b3 b4 b0 b1 hm
        ha2 ha3 ha4 ha0 ha1 hab2 hab3 hab4 hab0 hab1
        h2.1 h2.2.1 h2.2.2.1 h2.2.2.2.1 h2.2.2.2.2 hR2 hR3 hR4 hR0 hR1
      linarith)
  · exact h (by
      have := one_negative_zero_strict m a3 a4 a0 a1 a2 b3 b4 b0 b1 b2 hm
        ha3 ha4 ha0 ha1 ha2 hab3 hab4 hab0 hab1 hab2
        h3.1 h3.2.1 h3.2.2.1 h3.2.2.2.1 h3.2.2.2.2 hR3 hR4 hR0 hR1 hR2
      linarith)
  · exact h (by
      have := one_negative_zero_strict m a4 a0 a1 a2 a3 b4 b0 b1 b2 b3 hm
        ha4 ha0 ha1 ha2 ha3 hab4 hab0 hab1 hab2 hab3
        h4.1 h4.2.1 h4.2.2.1 h4.2.2.2.1 h4.2.2.2.2 hR4 hR0 hR1 hR2 hR3
      linarith)
  · exact h (two_adjacent_negative_zero_one_strict
      m a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 hm
      ha0 ha1 ha2 ha3 ha4 hab0 hab1 hab2 hab3 hab4
      h01.1 h01.2.1 h01.2.2.1 h01.2.2.2.1 h01.2.2.2.2
      hear0 hear1 hear2 hear3 hear4 hR0 hR1 hR2 hR3 hR4)
  · exact h (by
      have := two_adjacent_negative_zero_one_strict
        m a1 a2 a3 a4 a0 b1 b2 b3 b4 b0 hm
        ha1 ha2 ha3 ha4 ha0 hab1 hab2 hab3 hab4 hab0
        h12.1 h12.2.1 h12.2.2.1 h12.2.2.2.1 h12.2.2.2.2
        hear1 hear2 hear3 hear4 hear0 hR1 hR2 hR3 hR4 hR0
      linarith)
  · exact h (by
      have := two_adjacent_negative_zero_one_strict
        m a2 a3 a4 a0 a1 b2 b3 b4 b0 b1 hm
        ha2 ha3 ha4 ha0 ha1 hab2 hab3 hab4 hab0 hab1
        h23.1 h23.2.1 h23.2.2.1 h23.2.2.2.1 h23.2.2.2.2
        hear2 hear3 hear4 hear0 hear1 hR2 hR3 hR4 hR0 hR1
      linarith)
  · exact h (by
      have := two_adjacent_negative_zero_one_strict
        m a3 a4 a0 a1 a2 b3 b4 b0 b1 b2 hm
        ha3 ha4 ha0 ha1 ha2 hab3 hab4 hab0 hab1 hab2
        h34.1 h34.2.1 h34.2.2.1 h34.2.2.2.1 h34.2.2.2.2
        hear3 hear4 hear0 hear1 hear2 hR3 hR4 hR0 hR1 hR2
      linarith)
  · exact h (by
      have := two_adjacent_negative_zero_one_strict
        m a4 a0 a1 a2 a3 b4 b0 b1 b2 b3 hm
        ha4 ha0 ha1 ha2 ha3 hab4 hab0 hab1 hab2 hab3
        h40.1 h40.2.1 h40.2.2.1 h40.2.2.2.1 h40.2.2.2.2
        hear4 hear0 hear1 hear2 hear3 hR4 hR0 hR1 hR2 hR3
      linarith)

end PentagonScalar
end N6Scratch
