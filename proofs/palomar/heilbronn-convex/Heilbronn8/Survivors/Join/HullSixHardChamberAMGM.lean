import Mathlib

/-!
# Exact arithmetic certificate for the hard `2 + 4` six-hull chamber

This file records the small analytic certificate for the cross-chord tableau

```text
M M R R
L L M M
```

It deliberately contains no geometric adapter yet.  The purpose of the file is
to freeze the exact conventions and the finite arithmetic endpoint before that
adapter is written.  There are no generated certificates or logical placeholders.

Normalize the minimum doubled triangle area to one and apply an area-preserving
affine map taking the two interior points to `P = (0,0)` and `Q = (1,0)`.
Write the hull, in counterclockwise order, as

```text
U0, U1, L0, L1, L2, L3,
```

where the heights above/below `PQ` are `u0,u1 > 0` and `v0,...,v3 > 0`.
Put

```text
X i j = [P, Ui, Lj],       Y i j = [Q, Ui, Lj] = X i j + ui + vj.
```

The chamber convention is

```text
X00,X01 <= -1;  Y02,Y03 <= -1;
X10,X11 >=  1;  X12,X13 <= -1 <= Y12,Y13.
```

Let `A,C,E0,E1,E2,D` be the six consecutive `P`-fan areas and let primes
denote the corresponding `Q`-fan areas.  Thus `C = X10`, `D = -X03`, and
`D' = -Y03`.  Every fan area is at least one.  The exact translation formulas
are

```text
A'  = A + u0 - u1,
E1' = E1 - v1 + v2,
E2' = E2 - v2 + v3,
D   = D' + u0 + v3,
H   = A + C + E0 + E1 + E2' + D' + u0 + v2.
```

The only determinant identities needed are

```text
v(j+1) * X(i,j) - vj * X(i,j+1) = ui * Ej,
v(j+1) * Y(i,j) - vj * Y(i,j+1) = ui * Ej',
u0 * X(1,j) - u1 * X(0,j)       = vj * A,
u0 * Y(1,j) - u1 * Y(0,j)       = vj * A'.
```

Together with the chamber signs they give the following seven inequalities:

```text
(1) v0 * (u0 + v1 - 1) >= u0 + v1
    (top X row, columns 0,1; use E0 >= 1 and Y01 >= 1),
(2) v3 * (u1 + v2 - 1) >= u1 + v2
    (bottom Y row, columns 2,3; use E2' >= 1 and X12 <= -1),
(3) v1 * C  >= v0 + u1 * E0
    (bottom X row, columns 0,1),
(4) v0 * A  >= u0 * C + u1
    (X column 0),
(5) v2 * D' >= v3 + u0 * E2'
    (top Y row, columns 2,3, with Y03 = -D'),
(6) v3 * A' >= u0 + u1 * D'
    (Y column 3),
(7) u1 * E1  >= v1 + v2,   u0 * E1' >= v1 + v2
    (bottom X and top Y rows, columns 1,2).
```

For the closure set `u=u0`, `w=u1`, `x=v1`, and `y=v2`.  Only (2)--(5),
the second half of (7), the fan floors, and the displayed exact identities are
needed.  Eliminating `v0,v3,A,C,E1,D'` gives

```text
H >= 2 + u + x
   + (u+w+2*sqrt (w*(u+x)))/x
   + (x+y)/u
   + (u+1+1/(w+y-1))/y.
```

Since `u,w,x,y >= 1`, use

```text
sqrt (w*(u+x)) >= sqrt 2 * sqrt w * u^(1/4) * x^(1/4),
1/(y*(w+y-1)) >= 1/(w*y^2),
w/x + 1/(w*y^2) >= 2/(sqrt x*y),
sqrt w >= 1.
```

It remains to bound the sum of the following nine positive monomials.  The
second row gives their AM--GM multiplicities.

```text
u, x, u/x, 2/(sqrt x*y), 2*sqrt 2*u^(1/4)/x^(3/4), u/y, 1/y, x/u, y/u
12,17,  8,               8,                         24,   6,   5,  13,  19
```

The multiplicities sum to 112.  All variable exponents cancel, while the
constant product is `2^44`.  Applying ordinary AM--GM to `ni` copies of
`Ti/ni` therefore gives

```text
S >= 112 * (2^44 /
  (12^12*17^17*8^16*24^24*6^6*5^5*13^13*19^19))^(1/112).
```

The exact inequality below makes this strictly greater than `21/2`, hence
`H > 25/2`.  This is the complete scalar closure for the hard chamber; the
remaining formalization task is only to connect the geometric determinant
variables to this interface and invoke Mathlib's weighted AM--GM theorem.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

open scoped BigOperators

/--
Finite scalar AM--GM with positive natural multiplicities.

The formulation is chosen for certificate use.  A term `term i` is split into
`weight i` identical copies of `term i / weight i`; the theorem records the
result without constructing the (potentially much larger) type of copies.
Thus the right hand side is the unweighted sum of the original terms, while
the product on the left uses ordinary natural powers.  In the hard six-hull
chamber this replaces an explicit vector of `112` entries by nine entries.
-/
theorem scalar_weighted_amgm_nat
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight : ι → ℕ) (term : ι → ℝ)
    (hweight : ∀ i, 0 < weight i) (hterm : ∀ i, 0 ≤ term i) :
    ((↑(∑ i, weight i) : ℝ) *
        (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^
          ((↑(∑ i, weight i) : ℝ)⁻¹)) ≤
      ∑ i, term i := by
  classical
  let mass : ℕ := ∑ i, weight i
  have hmass : 0 < mass := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact Finset.sum_pos' (fun j _ => Nat.zero_le (weight j))
      ⟨i, Finset.mem_univ i, hweight i⟩
  have hmassCast : (mass : ℝ) = ∑ i, (weight i : ℝ) := by
    simp [mass]
  have hsum :
      (∑ i, (weight i : ℝ) * (term i / (weight i : ℝ))) =
        ∑ i, term i := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : (weight i : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hweight i))
    field_simp [hi]
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset ι) (fun i => (weight i : ℝ))
      (fun i => term i / (weight i : ℝ))
      (fun i _ => Nat.cast_nonneg (weight i))
      (by simpa [← hmassCast] using hmass)
      (fun i _ => div_nonneg (hterm i) (Nat.cast_nonneg (weight i)))
  have hroot :
      (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^ ((mass : ℝ)⁻¹) ≤
        (∑ i, term i) / (mass : ℝ) := by
    rw [hmassCast]
    rw [← hsum]
    simpa only [Real.rpow_natCast] using hamgm
  change (mass : ℝ) *
      (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^ ((mass : ℝ)⁻¹) ≤
    ∑ i, term i
  calc
    (mass : ℝ) *
          (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^ ((mass : ℝ)⁻¹) ≤
        (mass : ℝ) * ((∑ i, term i) / (mass : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg mass)
    _ = ∑ i, term i := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmass)]

/-- The denominator in the exact product of the nine scaled monomials. -/
def hullSixHardChamberAMGMDenominator : ℕ :=
  12 ^ 12 * 17 ^ 17 * 8 ^ 16 * 24 ^ 24 * 6 ^ 6 *
    5 ^ 5 * 13 ^ 13 * 19 ^ 19

/-- The variable-free product left after all three exponent balances cancel. -/
noncomputable def hullSixHardChamberAMGMConstant : ℝ :=
  (2 : ℝ) ^ 44 / hullSixHardChamberAMGMDenominator

/-- The nine AM--GM multiplicities have total mass `112`. -/
theorem hullSixHardChamber_weight_sum :
    12 + 17 + 8 + 8 + 24 + 6 + 5 + 13 + 19 = 112 := by
  norm_num

/-- Cancellation of the exponent of `u`. -/
theorem hullSixHardChamber_u_exponent_balance :
    (12 : ℤ) + 8 + 6 + 6 = 13 + 19 := by
  norm_num

/-- Cancellation of the exponent of `x`. -/
theorem hullSixHardChamber_x_exponent_balance :
    (17 : ℤ) + 13 = 8 + 4 + 18 := by
  norm_num

/-- Cancellation of the exponent of `y`. -/
theorem hullSixHardChamber_y_exponent_balance :
    (19 : ℤ) = 8 + 6 + 5 := by
  norm_num

/-- The two coefficient-bearing monomials contribute `2^(8+36)`. -/
theorem hullSixHardChamber_two_exponent : 8 + 36 = 44 := by
  norm_num

/-- The nine multiplicities, in the order displayed in the module comment. -/
def hullSixHardChamberAMGMWeight : Fin 9 → ℕ :=
  ![12, 17, 8, 8, 24, 6, 5, 13, 19]

theorem hullSixHardChamber_amgmWeight_pos
    (i : Fin 9) : 0 < hullSixHardChamberAMGMWeight i := by
  fin_cases i <;> norm_num [hullSixHardChamberAMGMWeight]

theorem hullSixHardChamber_amgmWeight_sum :
    ∑ i, hullSixHardChamberAMGMWeight i = 112 := by
  norm_num [hullSixHardChamberAMGMWeight, Fin.sum_univ_succ]

/-- A nonnegative square-root definition of the positive fourth root. -/
noncomputable def hullSixHardChamberFourthRoot (z : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt z)

/--
The nine positive monomials used by the hard-chamber AM--GM certificate.
Nested square roots are used instead of real powers so that the later product
cancellation needs only `Real.sq_sqrt` and polynomial normalization.
-/
noncomputable def hullSixHardChamberAMGMTerm (u x y : ℝ) : Fin 9 → ℝ :=
  ![u,
    x,
    u / x,
    2 / (Real.sqrt x * y),
    2 * Real.sqrt 2 * hullSixHardChamberFourthRoot u /
      hullSixHardChamberFourthRoot x ^ 3,
    u / y,
    1 / y,
    x / u,
    y / u]

theorem hullSixHardChamber_amgmTerm_nonneg
    {u x y : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (i : Fin 9) : 0 ≤ hullSixHardChamberAMGMTerm u x y i := by
  fin_cases i <;>
    simp [hullSixHardChamberAMGMTerm, hullSixHardChamberFourthRoot] <;>
    positivity

theorem hullSixHardChamber_fourthRoot_nonneg (z : ℝ) :
    0 ≤ hullSixHardChamberFourthRoot z := by
  unfold hullSixHardChamberFourthRoot
  positivity

theorem hullSixHardChamber_fourthRoot_sq {z : ℝ} (hz : 0 ≤ z) :
    hullSixHardChamberFourthRoot z ^ 2 = Real.sqrt z := by
  exact Real.sq_sqrt (Real.sqrt_nonneg z)

theorem hullSixHardChamber_fourthRoot_pow_four {z : ℝ} (hz : 0 ≤ z) :
    hullSixHardChamberFourthRoot z ^ 4 = z := by
  calc
    hullSixHardChamberFourthRoot z ^ 4 =
        (hullSixHardChamberFourthRoot z ^ 2) ^ 2 := by ring
    _ = (Real.sqrt z) ^ 2 := by
      rw [hullSixHardChamber_fourthRoot_sq hz]
    _ = z := Real.sq_sqrt hz

/-- All variable exponents in the nine weighted monomials cancel exactly. -/
theorem hullSixHardChamber_monomial_product
    {u x y : ℝ} (hu : 0 < u) (hx : 0 < x) (hy : 0 < y) :
    (∏ i,
        (hullSixHardChamberAMGMTerm u x y i /
          (hullSixHardChamberAMGMWeight i : ℝ)) ^
            hullSixHardChamberAMGMWeight i) =
      hullSixHardChamberAMGMConstant := by
  have hqu : hullSixHardChamberFourthRoot u ^ 24 = u ^ 6 := by
    rw [show (24 : ℕ) = 4 * 6 by norm_num, pow_mul,
      hullSixHardChamber_fourthRoot_pow_four (le_of_lt hu)]
  have hqx : hullSixHardChamberFourthRoot x ^ 72 = x ^ 18 := by
    rw [show (72 : ℕ) = 4 * 18 by norm_num, pow_mul,
      hullSixHardChamber_fourthRoot_pow_four (le_of_lt hx)]
  have hsx : (Real.sqrt x) ^ 8 = x ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul,
      Real.sq_sqrt (le_of_lt hx)]
  have hs2 : (Real.sqrt 2) ^ 24 = (2 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul,
      Real.sq_sqrt (by norm_num)]
  simp [hullSixHardChamberAMGMTerm, hullSixHardChamberAMGMWeight,
    Fin.prod_univ_succ, hullSixHardChamberAMGMConstant,
    hullSixHardChamberAMGMDenominator]
  field_simp [hu.ne', hx.ne', hy.ne',
    (Real.sqrt_pos.2 hx).ne',
    (show 0 < hullSixHardChamberFourthRoot x by
      unfold hullSixHardChamberFourthRoot
      positivity).ne']
  ring_nf at hqu hqx hsx hs2 ⊢
  rw [hqu, hqx, hsx, hs2]
  ring

/-- The fourth-root lower bound used on the cross-chord square-root term. -/
theorem hullSixHardChamber_crossSqrt_lower
    {u w x : ℝ} (hu : 1 ≤ u) (hw : 1 ≤ w) (hx : 1 ≤ x) :
    2 * Real.sqrt 2 * hullSixHardChamberFourthRoot u /
          hullSixHardChamberFourthRoot x ^ 3 ≤
      2 * Real.sqrt (w * (u + x)) / x := by
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hqu0 : 0 ≤ hullSixHardChamberFourthRoot u :=
    hullSixHardChamber_fourthRoot_nonneg u
  have hqx0 : 0 ≤ hullSixHardChamberFourthRoot x :=
    hullSixHardChamber_fourthRoot_nonneg x
  have hqx : 0 < hullSixHardChamberFourthRoot x := by
    unfold hullSixHardChamberFourthRoot
    positivity
  have hbase : 2 * Real.sqrt u * Real.sqrt x ≤ u + x := by
    nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt x),
      Real.sq_sqrt hu0, Real.sq_sqrt hx0]
  have hscale : u + x ≤ w * (u + x) := by
    have h := mul_nonneg (sub_nonneg.mpr hw) (add_nonneg hu0 hx0)
    nlinarith
  have hleftSq :
      (Real.sqrt 2 * hullSixHardChamberFourthRoot u *
          hullSixHardChamberFourthRoot x) ^ 2 =
        2 * Real.sqrt u * Real.sqrt x := by
    calc
      (Real.sqrt 2 * hullSixHardChamberFourthRoot u *
          hullSixHardChamberFourthRoot x) ^ 2 =
          (Real.sqrt 2) ^ 2 * hullSixHardChamberFourthRoot u ^ 2 *
            hullSixHardChamberFourthRoot x ^ 2 := by ring
      _ = 2 * Real.sqrt u * Real.sqrt x := by
        rw [Real.sq_sqrt (by norm_num),
          hullSixHardChamber_fourthRoot_sq hu0,
          hullSixHardChamber_fourthRoot_sq hx0]
  have hrightSq :
      (Real.sqrt (w * (u + x))) ^ 2 = w * (u + x) := by
    exact Real.sq_sqrt (mul_nonneg hw0 (add_nonneg hu0 hx0))
  have hcore :
      Real.sqrt 2 * hullSixHardChamberFourthRoot u *
          hullSixHardChamberFourthRoot x ≤
        Real.sqrt (w * (u + x)) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [hleftSq, hrightSq]
    exact hbase.trans hscale
  have hmul := mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ (2 : ℝ) / x)
  have hqx4 := hullSixHardChamber_fourthRoot_pow_four hx0
  have hqx3ne : hullSixHardChamberFourthRoot x ^ 3 ≠ 0 :=
    pow_ne_zero 3 hqx.ne'
  have hqx4ne : hullSixHardChamberFourthRoot x ^ 4 ≠ 0 :=
    pow_ne_zero 4 hqx.ne'
  calc
    2 * Real.sqrt 2 * hullSixHardChamberFourthRoot u /
          hullSixHardChamberFourthRoot x ^ 3 =
        (2 * Real.sqrt 2 * hullSixHardChamberFourthRoot u *
          hullSixHardChamberFourthRoot x) /
            hullSixHardChamberFourthRoot x ^ 4 := by
      apply (div_eq_div_iff hqx3ne hqx4ne).2
      ring
    _ =
        (2 / x) * (Real.sqrt 2 * hullSixHardChamberFourthRoot u *
          hullSixHardChamberFourthRoot x) := by
      rw [hqx4]
      ring
    _ ≤ (2 / x) * Real.sqrt (w * (u + x)) := hmul
    _ = 2 * Real.sqrt (w * (u + x)) / x := by ring

/-- The paired reciprocal estimate used after eliminating the outer heights. -/
theorem hullSixHardChamber_reciprocalPair_lower
    {w x y : ℝ} (hw : 1 ≤ w) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    2 / (Real.sqrt x * y) ≤
      w / x + 1 / (y * (w + y - 1)) := by
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  have hsx3 : (Real.sqrt x) ^ 3 = x * Real.sqrt x := by
    calc
      (Real.sqrt x) ^ 3 = (Real.sqrt x) ^ 2 * Real.sqrt x := by ring
      _ = x * Real.sqrt x := by rw [hsx2]
  have hdiff :
      0 ≤ w / x + 1 / (w * y ^ 2) - 2 / (Real.sqrt x * y) := by
    rw [show w / x + 1 / (w * y ^ 2) - 2 / (Real.sqrt x * y) =
      (w * y - Real.sqrt x) ^ 2 / (w * x * y ^ 2) by
        field_simp [hwpos.ne', hxpos.ne', hypos.ne', hsxpos.ne']
        ring_nf
        rw [hsx2, hsx3]]
    positivity
  have hpair :
      2 / (Real.sqrt x * y) ≤ w / x + 1 / (w * y ^ 2) := by
    linarith
  have hdenLe : w + y - 1 ≤ w * y := by
    have h := mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hy)
    nlinarith
  have hdenPos : 0 < w + y - 1 := by linarith
  have hinv : 1 / (w * y) ≤ 1 / (w + y - 1) :=
    one_div_le_one_div_of_le hdenPos hdenLe
  have hrecip :
      1 / (w * y ^ 2) ≤ 1 / (y * (w + y - 1)) := by
    calc
      1 / (w * y ^ 2) = (1 / (w * y)) / y := by
        field_simp [hwpos.ne', hypos.ne']
        <;> ring
      _ ≤ (1 / (w + y - 1)) / y :=
        div_le_div_of_nonneg_right hinv hy0
      _ = 1 / (y * (w + y - 1)) := by
        field_simp [hypos.ne', hdenPos.ne']
        <;> ring
  linarith

/-- The scalar lower expression obtained by eliminating the six fan variables. -/
noncomputable def hullSixHardChamberLower (u w x y : ℝ) : ℝ :=
  2 + u + x +
    (u + w + 2 * Real.sqrt (w * (u + x))) / x +
    (x + y) / u +
    (u + 1 + 1 / (w + y - 1)) / y

/--
The eliminated chamber expression dominates `2` plus the nine AM--GM terms.
This is the analytic adapter promised in the module comment; its assumptions
are exactly the four normalized height floors.
-/
theorem hullSixHardChamber_lower_dominates_monomials
    {u w x y : ℝ} (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    2 + (∑ i, hullSixHardChamberAMGMTerm u x y i) ≤
      hullSixHardChamberLower u w x y := by
  have hcross := hullSixHardChamber_crossSqrt_lower hu hw hx
  have hpair := hullSixHardChamber_reciprocalPair_lower hw hx hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hdenPos : 0 < -1 + w + y := by linarith
  have hcombinedPos : 0 < w * y - y + y ^ 2 := by
    rw [show w * y - y + y ^ 2 = y * (-1 + w + y) by ring]
    exact mul_pos hypos hdenPos
  have hrecipShape :
      y⁻¹ * (-1 + w + y)⁻¹ = (w * y - y + y ^ 2)⁻¹ := by
    rw [show w * y - y + y ^ 2 = y * (-1 + w + y) by ring,
      mul_inv]
  simp [hullSixHardChamberAMGMTerm, Fin.sum_univ_succ,
    hullSixHardChamberLower]
  ring_nf at hcross hpair ⊢
  rw [hrecipShape]
  linarith only [hcross, hpair]

/--
The exact 277-digit endpoint of the weighted AM--GM certificate.  Raising the
desired strict bound to the 112th power and clearing denominators gives exactly
this natural-number inequality.
-/
theorem hullSixHardChamber_amgm_integer_gap :
    (21 : ℕ) ^ 112 *
          (12 ^ 12 * 17 ^ 17 * 8 ^ 16 * 24 ^ 24 * 6 ^ 6 *
            5 ^ 5 * 13 ^ 13 * 19 ^ 19) <
      2 ^ 156 * 112 ^ 112 := by
  norm_num

set_option maxRecDepth 10000 in
/-- The same endpoint after cancelling prime powers. -/
theorem hullSixHardChamber_amgm_integer_gap_reduced :
    (3 : ℕ) ^ 154 * 5 ^ 5 * 13 ^ 13 * 17 ^ 17 * 19 ^ 19 < 2 ^ 454 := by
  norm_num [pow_succ]

/-- The exact product constant is positive. -/
theorem hullSixHardChamber_amgmConstant_pos :
    0 < hullSixHardChamberAMGMConstant := by
  unfold hullSixHardChamberAMGMConstant hullSixHardChamberAMGMDenominator
  positivity

/--
The integer endpoint in analytic form.  This is the strict part of the hard
chamber argument: an AM--GM lower bound with the certified constant is already
strictly larger than `21 / 2`.
-/
theorem hullSixHardChamber_amgm_root_gap :
    (21 : ℝ) / 2 <
      112 * hullSixHardChamberAMGMConstant ^ ((112 : ℝ)⁻¹) := by
  have hgapNat :
      (21 : ℕ) ^ 112 * hullSixHardChamberAMGMDenominator <
        2 ^ 156 * 112 ^ 112 := by
    simpa [hullSixHardChamberAMGMDenominator] using
      hullSixHardChamber_amgm_integer_gap
  have hgapReal :
      (21 : ℝ) ^ 112 * (hullSixHardChamberAMGMDenominator : ℝ) <
        2 ^ 156 * 112 ^ 112 := by
    exact_mod_cast hgapNat
  have hright :
      (2 : ℝ) ^ 44 * 224 ^ 112 = 2 ^ 156 * 112 ^ 112 := by
    rw [show (224 : ℝ) = 2 * 112 by norm_num, mul_pow]
    ring
  have hpow :
      ((21 : ℝ) / 224) ^ 112 < hullSixHardChamberAMGMConstant := by
    unfold hullSixHardChamberAMGMConstant
    rw [div_pow]
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 224 ^ 112)
      (by norm_num [hullSixHardChamberAMGMDenominator] :
        (0 : ℝ) < (hullSixHardChamberAMGMDenominator : ℝ))).2
    rw [hright]
    exact hgapReal
  have hpowRpow :
      ((21 : ℝ) / 224) ^ (112 : ℝ) < hullSixHardChamberAMGMConstant := by
    change ((21 : ℝ) / 224) ^ ((112 : ℕ) : ℝ) <
      hullSixHardChamberAMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (21 : ℝ) / 224 <
        hullSixHardChamberAMGMConstant ^ ((112 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixHardChamber_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/--
Certificate consumer for the hard-chamber multiplicities.  The only algebraic
input is the exact product identity; no analytic inequality is hidden in that
input.  The theorem packages the generic AM--GM theorem and the strict integer
endpoint into the `21 / 2` lower bound needed by the geometric adapter.
-/
theorem hullSixHardChamber_amgm_of_product
    (term : Fin 9 → ℝ) (hterm : ∀ i, 0 ≤ term i)
    (hproduct :
      (∏ i, (term i / (hullSixHardChamberAMGMWeight i : ℝ)) ^
        hullSixHardChamberAMGMWeight i) =
        hullSixHardChamberAMGMConstant) :
    (21 : ℝ) / 2 < ∑ i, term i := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixHardChamberAMGMWeight term hullSixHardChamber_amgmWeight_pos hterm
  rw [hullSixHardChamber_amgmWeight_sum, hproduct] at hamgm
  exact hullSixHardChamber_amgm_root_gap.trans_le (by simpa using hamgm)

/-- The specialized nine-monomial consequence, with product cancellation explicit. -/
theorem hullSixHardChamber_monomial_sum_of_product
    {u x y : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hproduct :
      (∏ i,
          (hullSixHardChamberAMGMTerm u x y i /
            (hullSixHardChamberAMGMWeight i : ℝ)) ^
              hullSixHardChamberAMGMWeight i) =
        hullSixHardChamberAMGMConstant) :
    (21 : ℝ) / 2 < ∑ i, hullSixHardChamberAMGMTerm u x y i := by
  exact hullSixHardChamber_amgm_of_product
    (hullSixHardChamberAMGMTerm u x y)
    (hullSixHardChamber_amgmTerm_nonneg hu hx hy) hproduct

/--
Final scalar adapter once the chamber elimination has supplied the displayed
lower bound by `2 +` the certified monomial sum.  This theorem deliberately
mentions no points or determinants, so the geometry layer cannot accidentally
hide an extra analytic assumption.
-/
theorem hullSixHardChamber_finish_of_monomial_product
    {H u x y : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hH :
      2 + (∑ i, hullSixHardChamberAMGMTerm u x y i) ≤ H)
    (hproduct :
      (∏ i,
          (hullSixHardChamberAMGMTerm u x y i /
            (hullSixHardChamberAMGMWeight i : ℝ)) ^
              hullSixHardChamberAMGMWeight i) =
        hullSixHardChamberAMGMConstant) :
    (25 : ℝ) / 2 < H := by
  have hsum := hullSixHardChamber_monomial_sum_of_product hu hx hy hproduct
  linarith

/--
End-to-end scalar closure from the eliminated lower expression.  A geometric
caller now has to provide only `hLower` and the exact, purely algebraic product
identity for the nine displayed monomials.
-/
theorem hullSixHardChamber_finish_of_lower
    {H u w x y : ℝ} (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hLower : hullSixHardChamberLower u w x y ≤ H)
    (hproduct :
      (∏ i,
          (hullSixHardChamberAMGMTerm u x y i /
            (hullSixHardChamberAMGMWeight i : ℝ)) ^
              hullSixHardChamberAMGMWeight i) =
        hullSixHardChamberAMGMConstant) :
    (25 : ℝ) / 2 < H := by
  apply hullSixHardChamber_finish_of_monomial_product
    (le_trans zero_le_one hu) (le_trans zero_le_one hx)
      (le_trans zero_le_one hy) _ hproduct
  exact (hullSixHardChamber_lower_dominates_monomials hu hw hx hy).trans hLower

/-- Complete scalar hard-chamber closure; only the geometric lower bound remains. -/
theorem hullSixHardChamber_finish
    {H u w x y : ℝ} (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hLower : hullSixHardChamberLower u w x y ≤ H) :
    (25 : ℝ) / 2 < H := by
  apply hullSixHardChamber_finish_of_lower hu hw hx hy hLower
  exact hullSixHardChamber_monomial_product
    (lt_of_lt_of_le zero_lt_one hu)
    (lt_of_lt_of_le zero_lt_one hx)
    (lt_of_lt_of_le zero_lt_one hy)

end Heilbronn8
