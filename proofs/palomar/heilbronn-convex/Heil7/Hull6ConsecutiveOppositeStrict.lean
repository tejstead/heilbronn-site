import Heil7.Hull6ConsecutiveOppositeChamber

/-!
# Strictness of the nonalternating all-positive hull-six chamber

The three consecutive negative opposite brackets force strictly more than
three units of boundary-sector excess.  The production theorem only records
the weak consequence; this file keeps the strict endpoint needed for equality
classification.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Under the total-budget constraint, the polynomial used in the block
chamber is strictly positive. -/
private lemma block_G_pos
    {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R) (hsum : q + R ≤ 3)
    (hcap : 4 * (1 + q) ≤ 4 * R + R ^ 2) :
    0 < q ^ 2 + q * R + 2 * R - 4 * q - 1 := by
  by_contra hnot
  have hGle : q ^ 2 + q * R + 2 * R - 4 * q - 1 ≤ 0 :=
    le_of_not_gt hnot
  let n : ℝ := 1 + 4 * q - q ^ 2
  let X : ℝ := R * (q + 2)
  have hq2 : 0 < q + 2 := by linarith
  have hX0 : 0 ≤ X := by
    simp only [X]
    exact mul_nonneg hR hq2.le
  have hXn : X ≤ n := by
    simp only [X, n]
    nlinarith only [hGle]
  have hn0 : 0 ≤ n := hX0.trans hXn
  have hdiff : 0 ≤ (n - X) * (n + X) :=
    mul_nonneg (sub_nonneg.mpr hXn) (add_nonneg hn0 hX0)
  have hsq : X ^ 2 ≤ n ^ 2 := by nlinarith only [hdiff]
  have hlin : 4 * X * (q + 2) ≤ 4 * n * (q + 2) := by
    have hmul := mul_le_mul_of_nonneg_right hXn
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hq2.le)
    nlinarith only [hmul]
  have hcapScaled := mul_le_mul_of_nonneg_right hcap (sq_nonneg (q + 2))
  have hpoly :
      0 ≤ q ^ 4 - 16 * q ^ 3 + 2 * q ^ 2 + 12 * q - 7 := by
    simp only [X, n] at hsq hlin
    nlinarith only [hcapScaled, hsq, hlin]
  have hpolyNeg :
      q ^ 4 - 16 * q ^ 3 + 2 * q ^ 2 + 12 * q - 7 < 0 := by
    by_cases hq1 : q ≤ 1
    · have hone : 0 ≤ 1 - q := sub_nonneg.mpr hq1
      by_cases hq0 : q = 0
      · subst q
        norm_num
      · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
        have hid :
            -(q ^ 4 - 16 * q ^ 3 + 2 * q ^ 2 + 12 * q - 7) =
              7 * (1 - q) ^ 4 + 16 * q * (1 - q) ^ 3 +
                4 * q ^ 2 * (1 - q) ^ 2 +
                4 * q ^ 3 * (1 - q) + 8 * q ^ 4 := by ring
        have h0 : 0 ≤ 7 * (1 - q) ^ 4 := by positivity
        have h1 : 0 ≤ 16 * q * (1 - q) ^ 3 := by positivity
        have h2 : 0 ≤ 4 * q ^ 2 * (1 - q) ^ 2 := by positivity
        have h3 : 0 ≤ 4 * q ^ 3 * (1 - q) := by positivity
        have h4 : 0 < 8 * q ^ 4 := by positivity
        nlinarith only [hid, h0, h1, h2, h3, h4]
    · have hqgt : 1 < q := lt_of_not_ge hq1
      have hq3 : q ≤ 3 := by linarith only [hsum, hR]
      have h15 : 0 < 15 - q := by linarith only [hq3]
      have hfac : 0 < -q ^ 3 + 15 * q ^ 2 + 13 * q + 1 := by
        have hp : 0 < q ^ 2 * (15 - q) := by positivity
        nlinarith only [hp, hqgt]
      have hid :
          -(q ^ 4 - 16 * q ^ 3 + 2 * q ^ 2 + 12 * q - 7) =
            8 + (q - 1) * (-q ^ 3 + 15 * q ^ 2 + 13 * q + 1) := by ring
      have hp : 0 < (q - 1) * (-q ^ 3 + 15 * q ^ 2 + 13 * q + 1) :=
        mul_pos (sub_pos.mpr hqgt) hfac
      nlinarith only [hid, hp]
  exact (not_lt_of_ge hpoly) hpolyNeg

/-- Strict normalized five-variable endpoint for the block chamber. -/
private lemma three_negative_excess_one_strict
    {x0 x1 x3 x4 x5 : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx3 : 0 ≤ x3)
    (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)
    (h35 : 2 + x4 ≤ (1 + x3) * (1 + x5))
    (h40 : 2 + x5 ≤ (1 + x4) * (1 + x0))
    (h51 : 2 + x0 ≤ (1 + x5) * (1 + x1)) :
    3 < x0 + x1 + x3 + x4 + x5 := by
  by_contra hnot
  have hsum : x0 + x1 + x3 + x4 + x5 ≤ 3 := le_of_not_gt hnot
  let A : ℝ := x1 + x3
  let q : ℝ := x5
  let R : ℝ := x0 + x4
  have hA : 2 + R ≤ (1 + q) * A + 2 * q := by
    simp only [A, q, R]
    nlinarith only [h35, h51]
  have hcap : 4 * (1 + q) ≤ 4 * R + R ^ 2 := by
    have hsquare := sq_nonneg (x0 - x4)
    simp only [q, R]
    nlinarith only [h40, hsquare]
  have hqR : q + R ≤ 3 := by
    simp only [q, R]
    linarith only [hsum, hx1, hx3]
  have hG := block_G_pos hx5 (add_nonneg hx0 hx4) hqR hcap
  have hexcess : 0 ≤ (1 + q) * A + 2 * q - 2 - R := by
    linarith only [hA]
  have hpositive :
      0 < (q ^ 2 + q * R + 2 * R - 4 * q - 1) +
        ((1 + q) * A + 2 * q - 2 - R) := by
    linarith only [hG, hexcess]
  have hnonpos : (1 + q) * (A + q + R - 3) ≤ 0 := by
    have hinside : A + q + R - 3 ≤ 0 := by
      simp only [A, q, R]
      linarith only [hsum]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hinside
  have hid :
      (q ^ 2 + q * R + 2 * R - 4 * q - 1) +
          ((1 + q) * A + 2 * q - 2 - R) =
        (1 + q) * (A + q + R - 3) := by ring
  nlinarith only [hpositive, hnonpos, hid]

/-- Homogeneous strict endpoint. -/
private lemma three_negative_excess_strict
    {m x0 x1 x3 x4 x5 : ℝ} (hm : 0 < m)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx3 : 0 ≤ x3)
    (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)
    (h35 : 2 * m ^ 2 + m * x4 ≤ (m + x3) * (m + x5))
    (h40 : 2 * m ^ 2 + m * x5 ≤ (m + x4) * (m + x0))
    (h51 : 2 * m ^ 2 + m * x0 ≤ (m + x5) * (m + x1)) :
    3 * m < x0 + x1 + x3 + x4 + x5 := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hsquare : 0 ≤ (1 / m) ^ 2 := sq_nonneg _
  have h35n : 2 + x4 / m ≤ (1 + x3 / m) * (1 + x5 / m) := by
    calc
      2 + x4 / m = (2 * m ^ 2 + m * x4) * (1 / m) ^ 2 := by
        field_simp [hmne]
      _ ≤ ((m + x3) * (m + x5)) * (1 / m) ^ 2 :=
        mul_le_mul_of_nonneg_right h35 hsquare
      _ = (1 + x3 / m) * (1 + x5 / m) := by
        field_simp [hmne]
  have h40n : 2 + x5 / m ≤ (1 + x4 / m) * (1 + x0 / m) := by
    calc
      2 + x5 / m = (2 * m ^ 2 + m * x5) * (1 / m) ^ 2 := by
        field_simp [hmne]
      _ ≤ ((m + x4) * (m + x0)) * (1 / m) ^ 2 :=
        mul_le_mul_of_nonneg_right h40 hsquare
      _ = (1 + x4 / m) * (1 + x0 / m) := by
        field_simp [hmne]
  have h51n : 2 + x0 / m ≤ (1 + x5 / m) * (1 + x1 / m) := by
    calc
      2 + x0 / m = (2 * m ^ 2 + m * x0) * (1 / m) ^ 2 := by
        field_simp [hmne]
      _ ≤ ((m + x5) * (m + x1)) * (1 / m) ^ 2 :=
        mul_le_mul_of_nonneg_right h51 hsquare
      _ = (1 + x5 / m) * (1 + x1 / m) := by
        field_simp [hmne]
  have hnorm := three_negative_excess_one_strict
    (div_nonneg hx0 hm.le) (div_nonneg hx1 hm.le)
    (div_nonneg hx3 hm.le) (div_nonneg hx4 hm.le)
    (div_nonneg hx5 hm.le) h35n h40n h51n
  have hscaled := mul_lt_mul_of_pos_left hnorm hm
  calc
    3 * m = m * 3 := by ring
    _ < m * (x0 / m + x1 / m + x3 / m + x4 / m + x5 / m) := hscaled
    _ = x0 + x1 + x3 + x4 + x5 := by
      field_simp [hmne]

/-- A nonalternating all-positive-`d` chamber is strict. -/
theorem h6_consecutive_array_bound_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc3 : c 3 ≤ -m) (hc4 : c 4 ≤ -m) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hanonneg : ∀ i, 0 ≤ a i := fun i => le_trans hm.le (ha i)
  have hdnonneg : ∀ i, 0 ≤ d i := fun i => le_trans hm.le (hd i)
  have hdd (i j : Fin 6) : m * m ≤ d i * d j := by
    calc
      m * m ≤ m * d j := mul_le_mul_of_nonneg_left (hd j) hm.le
      _ ≤ d i * d j := mul_le_mul_of_nonneg_right (hd i) (hdnonneg j)
  have negative_product (i j k : Fin 6) (hc : c i ≤ -m)
      (hr : d i * d (i + 1) = a i * a j + c i * a k) :
      m ^ 2 + m * a k ≤ a i * a j := by
    have hca : c i * a k ≤ (-m) * a k :=
      mul_le_mul_of_nonneg_right hc (hanonneg k)
    have hupper : d i * d (i + 1) ≤ a i * a j - m * a k := by
      calc
        d i * d (i + 1) = a i * a j + c i * a k := hr
        _ ≤ a i * a j + (-m) * a k := add_le_add_right hca _
        _ = a i * a j - m * a k := by ring
    nlinarith only [hdd i (i + 1), hupper]
  have hp35 : m ^ 2 + m * a 4 ≤ a 3 * a 5 := by
    simpa using negative_product 3 5 4 hc3 (by simpa using hrel 3)
  have hp40 : m ^ 2 + m * a 5 ≤ a 4 * a 0 := by
    simpa using negative_product 4 0 5 hc4 (by simpa using hrel 4)
  have hp51 : m ^ 2 + m * a 0 ≤ a 5 * a 1 := by
    simpa using negative_product 5 1 0 hc5 (by simpa using hrel 5)
  have hx0 : 0 ≤ a 0 - m := sub_nonneg.mpr (ha 0)
  have hx1 : 0 ≤ a 1 - m := sub_nonneg.mpr (ha 1)
  have hx2 : 0 ≤ a 2 - m := sub_nonneg.mpr (ha 2)
  have hx3 : 0 ≤ a 3 - m := sub_nonneg.mpr (ha 3)
  have hx4 : 0 ≤ a 4 - m := sub_nonneg.mpr (ha 4)
  have hx5 : 0 ≤ a 5 - m := sub_nonneg.mpr (ha 5)
  have h35 :
      2 * m ^ 2 + m * (a 4 - m) ≤
        (m + (a 3 - m)) * (m + (a 5 - m)) := by
    nlinarith only [hp35]
  have h40 :
      2 * m ^ 2 + m * (a 5 - m) ≤
        (m + (a 4 - m)) * (m + (a 0 - m)) := by
    nlinarith only [hp40]
  have h51 :
      2 * m ^ 2 + m * (a 0 - m) ≤
        (m + (a 5 - m)) * (m + (a 1 - m)) := by
    nlinarith only [hp51]
  have hexcess := three_negative_excess_strict hm
    hx0 hx1 hx3 hx4 hx5 h35 h40 h51
  nlinarith only [hexcess, hx2]

end HeilbronnChallenge.N7Upper
