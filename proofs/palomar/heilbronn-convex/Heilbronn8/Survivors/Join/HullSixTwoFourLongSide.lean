import Mathlib

/-!
# A chamber-free long-side inequality for the hull-six `2 + 4` split

Consider four consecutive hull vertices on one side of the line through the
two interior points.  Let `v0,...,v3` be their positive line-level
magnitudes, and let `E0,E1,E2` be the three consecutive fan areas based at
the first interior point.  The corresponding fan areas based at the second
point are

```text
E0 - v0 + v1,  E1 - v1 + v2,  E2 - v2 + v3.
```

The two consecutive hull-ear floors imply a useful product inequality for
the excess fan areas:

```text
m^2 <= (E1 - m) * ((E0 - m) + (E2 - m)).
```

In particular, `E0 + E1 + E2 >= 5m`.  The proof is elementary elimination;
it uses no chamber labels, generated data, square roots, or case census.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The product form of the four-vertex long-side inequality.

The two `ear` hypotheses are the consecutive hull-triangle floors after
clearing the positive denominators `v1` and `v2`.  Only the two translated
fan floors which enter the elimination are retained in the interface. -/
theorem hullSixTwoFour_longSide_middleProduct
    {m v0 v1 v2 v3 E0 E1 E2 : ℝ}
    (hm : 0 < m) (hv0 : m ≤ v0)
    (hE0 : m ≤ E0) (hE1 : m ≤ E1) (hE2 : m ≤ E2)
    (hE1p : m ≤ E1 - v1 + v2)
    (hE2p : m ≤ E2 - v2 + v3)
    (hear0 : m * v1 ≤ E1 * (v1 - v0) - E0 * (v2 - v1))
    (hear1 : m * v2 ≤ E2 * (v2 - v1) - E1 * (v3 - v2)) :
    m ^ 2 ≤ (E1 - m) * ((E0 - m) + (E2 - m)) := by
  let x : ℝ := E0 - m
  let y : ℝ := E1 - m
  let z : ℝ := E2 - m
  let a : ℝ := v1 - v0
  let b : ℝ := v2 - v1
  let c : ℝ := v3 - v2
  have hx : 0 ≤ x := by
    dsimp [x]
    linarith
  have hy0 : 0 ≤ y := by
    dsimp [y]
    linarith
  have hz : 0 ≤ z := by
    dsimp [z]
    linarith
  have hb : -y ≤ b := by
    dsimp [y, b]
    linarith
  have hc : -z ≤ c := by
    dsimp [z, c]
    linarith
  have hfirst : m ^ 2 ≤ y * a - (m + x) * b := by
    dsimp [x, y, a, b]
    nlinarith
  have hsecond :
      m ^ 2 ≤ z * b - (m + y) * c - m * a := by
    dsimp [y, z, a, b, c]
    nlinarith
  have hy : 0 < y := by
    by_contra hnot
    have hyle : y ≤ 0 := le_of_not_gt hnot
    have hyeq : y = 0 := le_antisymm hyle hy0
    have hb0 : 0 ≤ b := by linarith
    have hmb : 0 ≤ (m + x) * b :=
      mul_nonneg (by linarith) hb0
    rw [hyeq, zero_mul, zero_sub] at hfirst
    nlinarith [sq_pos_of_pos hm]
  have hcz : 0 ≤ (m + y) * (c + z) :=
    mul_nonneg (by linarith) (by linarith)
  have haupper :
      m * a ≤ z * b + (m + y) * z - m ^ 2 := by
    nlinarith
  have hmulUpper :
      y * (m * a) ≤ y * (z * b + (m + y) * z - m ^ 2) :=
    mul_le_mul_of_nonneg_left haupper hy0
  have hmulFirst :
      m * (m ^ 2 + (m + x) * b) ≤ m * (y * a) :=
    have hfirst' : m ^ 2 + (m + x) * b ≤ y * a := by
      linarith [hfirst]
    mul_le_mul_of_nonneg_left hfirst' (le_of_lt hm)
  have hcombine :
      m * (m ^ 2 + (m + x) * b) ≤
        y * (z * b + (m + y) * z - m ^ 2) := by
    calc
      m * (m ^ 2 + (m + x) * b) ≤ m * (y * a) := hmulFirst
      _ = y * (m * a) := by ring
      _ ≤ y * (z * b + (m + y) * z - m ^ 2) := hmulUpper
  have hcore :
      (m + y) * (m ^ 2 - y * z) +
          (m ^ 2 + m * x - y * z) * b ≤ 0 := by
    nlinarith [hcombine]
  by_cases hcoef : 0 ≤ m ^ 2 + m * x - y * z
  · have hby : 0 ≤ b + y := by linarith
    have hnonneg :
        0 ≤ (m ^ 2 + m * x - y * z) * (b + y) :=
      mul_nonneg hcoef hby
    have hid :
        (m + y) * (m ^ 2 - y * z) +
              (m ^ 2 + m * x - y * z) * b =
            m * (m ^ 2 - y * (x + z)) +
              (m ^ 2 + m * x - y * z) * (b + y) := by
      ring
    rw [hid] at hcore
    nlinarith
  · have hcoefNeg : m ^ 2 + m * x - y * z < 0 :=
      lt_of_not_ge hcoef
    have hyx : 0 ≤ y * x := mul_nonneg hy0 hx
    nlinarith

/-- Additive consequence of `hullSixTwoFour_longSide_middleProduct`.
The three consecutive fan areas on the four-vertex side pay at least five
copies of the common triangle floor. -/
theorem hullSixTwoFour_longSide_sum_five
    {m v0 v1 v2 v3 E0 E1 E2 : ℝ}
    (hm : 0 < m) (hv0 : m ≤ v0)
    (hE0 : m ≤ E0) (hE1 : m ≤ E1) (hE2 : m ≤ E2)
    (hE1p : m ≤ E1 - v1 + v2)
    (hE2p : m ≤ E2 - v2 + v3)
    (hear0 : m * v1 ≤ E1 * (v1 - v0) - E0 * (v2 - v1))
    (hear1 : m * v2 ≤ E2 * (v2 - v1) - E1 * (v3 - v2)) :
    5 * m ≤ E0 + E1 + E2 := by
  have hproduct := hullSixTwoFour_longSide_middleProduct hm hv0
    hE0 hE1 hE2 hE1p hE2p hear0 hear1
  let y : ℝ := E1 - m
  let t : ℝ := (E0 - m) + (E2 - m)
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    linarith
  have hprod : m ^ 2 ≤ y * t := by
    simpa [y, t] using hproduct
  have hsum : 2 * m ≤ y + t := by
    by_contra hnot
    have hlt : y + t < 2 * m := lt_of_not_ge hnot
    have hsum0 : 0 ≤ y + t := add_nonneg hy ht
    have hfactor :
        0 < (2 * m - (y + t)) * (2 * m + (y + t)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (y - t)]
  dsimp [y, t] at hsum
  linarith

end Heilbronn8
