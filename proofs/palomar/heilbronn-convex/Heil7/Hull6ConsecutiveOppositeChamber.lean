import Heil7.Hull6BracketRoute

/-!
# The consecutive-opposite-sign hull-six chamber

This file closes the second chamber with all six two-step radial brackets
positive.  Up to cyclic rotation and reversal, the three opposite brackets
`b 0 3`, `b 1 4`, `b 2 5` are all positive; skew-symmetry makes the next
three orientations all negative.

Only the three GP identities carrying those negative signs are needed.  They
give three product inequalities in the boundary-sector excesses.  A small
polynomial lemma then shows that the total excess is at least `3m`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The canonical block-sign chamber.  Its cyclic/reflected images cover all
non-alternating opposite sign patterns when every two-step bracket is
positive. -/
def H6ConsecutiveOppositeChamber (b : Fin 6 → Fin 6 → ℝ) : Prop :=
  0 < b 0 2 ∧ 0 < b 1 3 ∧ 0 < b 2 4 ∧
  0 < b 3 5 ∧ 0 < b 4 0 ∧ 0 < b 5 1 ∧
  0 < b 0 3 ∧ 0 < b 1 4 ∧ 0 < b 2 5

/-- The only two-variable polynomial fact needed in the block chamber. -/
private lemma block_G_nonneg
    {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hcap : 4 * (1 + q) ≤ 4 * R + R ^ 2) :
    0 ≤ q ^ 2 + q * R + 2 * R - 4 * q - 1 := by
  by_cases hlarge : 4 ≤ R
  · have hterm : 0 ≤ (R - 4) * q :=
      mul_nonneg (sub_nonneg.mpr hlarge) hq
    nlinarith only [sq_nonneg q, hterm, hlarge]
  by_cases hmid : (3 : ℝ) / 2 ≤ R
  · have hR4 : R ≤ 4 := le_of_not_ge hlarge
    have hp : 0 ≤ (2 * R - 3) * (29 - 2 * R) := by
      apply mul_nonneg <;> linarith
    have hid :
        16 * (q ^ 2 + q * R + 2 * R - 4 * q - 1) =
          (4 * q + 2 * R - 8) ^ 2 + 7 +
            (2 * R - 3) * (29 - 2 * R) := by ring
    nlinarith only [hid, sq_nonneg (4 * q + 2 * R - 8), hp]
  · have hRmid : R ≤ (3 : ℝ) / 2 := le_of_lt (lt_of_not_ge hmid)
    let Q : ℝ := R + R ^ 2 / 4 - 1
    have hqQ : q ≤ Q := by
      dsimp [Q]
      nlinarith only [hcap]
    have hQ : 0 ≤ Q := hq.trans hqQ
    have hcurve : 0 ≤ R * ((3 : ℝ) / 2 - R) :=
      mul_nonneg hR (sub_nonneg.mpr hRmid)
    have hsecond : q + Q + R - 4 ≤ 0 := by
      dsimp [Q] at hqQ ⊢
      nlinarith only [hqQ, hcurve, hRmid]
    have hfirst : q - Q ≤ 0 := sub_nonpos.mpr hqQ
    have hdiffprod : 0 ≤ (q - Q) * (q + Q + R - 4) :=
      mul_nonneg_of_nonpos_of_nonpos hfirst hsecond
    have hdiff :
        0 ≤ (q ^ 2 + q * R + 2 * R - 4 * q - 1) -
          (Q ^ 2 + Q * R + 2 * R - 4 * Q - 1) := by
      calc
        (q ^ 2 + q * R + 2 * R - 4 * q - 1) -
            (Q ^ 2 + Q * R + 2 * R - 4 * Q - 1) =
          (q - Q) * (q + Q + R - 4) := by ring
        _ ≥ 0 := hdiffprod
    let f : ℝ := R ^ 3 + 8 * R ^ 2 - 24 * R + 16
    have hf : 0 ≤ f := by
      by_cases hR1 : R ≤ 1
      · have hp12 : 0 ≤ (1 - R) * (2 - R) := by
          apply mul_nonneg <;> linarith
        have hcube : 0 ≤ R ^ 3 := by positivity
        have hidf : f = R ^ 3 + 8 * (1 - R) * (2 - R) := by
          simp only [f]
          ring
        rw [hidf]
        nlinarith only [hcube, hp12]
      · have ht : 0 ≤ R - 1 := by linarith
        have hcube : 0 ≤ (R - 1) ^ 3 := by positivity
        have hidf :
            44 * f = 44 * (R - 1) ^ 3 +
              (22 * (R - 1) - 5) ^ 2 + 19 := by
          simp only [f]
          ring
        nlinarith only [hidf, hcube, sq_nonneg (22 * (R - 1) - 5)]
    have hQeval :
        16 * (Q ^ 2 + Q * R + 2 * R - 4 * Q - 1) =
          (R + 4) * f := by
      simp only [Q, f]
      ring
    have hQG : 0 ≤ Q ^ 2 + Q * R + 2 * R - 4 * Q - 1 := by
      have hp : 0 ≤ (R + 4) * f := mul_nonneg (by linarith) hf
      nlinarith only [hQeval, hp]
    nlinarith only [hdiff, hQG]

/-- Normalized five-variable consequence of the three negative GP rows. -/
private lemma three_negative_excess_one
    {x0 x1 x3 x4 x5 : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx3 : 0 ≤ x3)
    (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)
    (h35 : 2 + x4 ≤ (1 + x3) * (1 + x5))
    (h40 : 2 + x5 ≤ (1 + x4) * (1 + x0))
    (h51 : 2 + x0 ≤ (1 + x5) * (1 + x1)) :
    3 ≤ x0 + x1 + x3 + x4 + x5 := by
  let A := x1 + x3
  let q := x5
  let R := x0 + x4
  have hA : 2 + R ≤ (1 + q) * A + 2 * q := by
    simp only [A, q, R]
    nlinarith only [h35, h51]
  have hcap : 4 * (1 + q) ≤ 4 * R + R ^ 2 := by
    have hsquare := sq_nonneg (x0 - x4)
    simp only [q, R]
    nlinarith only [h40, hsquare]
  have hG := block_G_nonneg hx5 (add_nonneg hx0 hx4) hcap
  have hprod : 0 ≤ (1 + q) * (A + q + R - 3) := by
    have hexcess : 0 ≤ (1 + q) * A + 2 * q - 2 - R := by
      linarith only [hA]
    calc
      0 ≤ q ^ 2 + q * R + 2 * R - 4 * q - 1 := hG
      _ ≤ (q ^ 2 + q * R + 2 * R - 4 * q - 1) +
          ((1 + q) * A + 2 * q - 2 - R) :=
        le_add_of_nonneg_right hexcess
      _ = (1 + q) * (A + q + R - 3) := by ring
  have hsum : 3 ≤ A + q + R := by
    by_contra hnot
    have hlt : A + q + R < 3 := lt_of_not_ge hnot
    have hneg : (1 + q) * (A + q + R - 3) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hlt)
    linarith
  simpa only [A, q, R, add_assoc, add_left_comm, add_comm] using hsum

/-- Homogeneous form of `three_negative_excess_one`. -/
private lemma three_negative_excess
    {m x0 x1 x3 x4 x5 : ℝ} (hm : 0 < m)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx3 : 0 ≤ x3)
    (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)
    (h35 : 2 * m ^ 2 + m * x4 ≤ (m + x3) * (m + x5))
    (h40 : 2 * m ^ 2 + m * x5 ≤ (m + x4) * (m + x0))
    (h51 : 2 * m ^ 2 + m * x0 ≤ (m + x5) * (m + x1)) :
    3 * m ≤ x0 + x1 + x3 + x4 + x5 := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hsquare : 0 ≤ (1 / m) ^ 2 := sq_nonneg _
  have h35n :
      2 + x4 / m ≤ (1 + x3 / m) * (1 + x5 / m) := by
    calc
      2 + x4 / m = (2 * m ^ 2 + m * x4) * (1 / m) ^ 2 := by
        field_simp [hmne]
        <;> ring
      _ ≤ ((m + x3) * (m + x5)) * (1 / m) ^ 2 :=
        mul_le_mul_of_nonneg_right h35 hsquare
      _ = (1 + x3 / m) * (1 + x5 / m) := by
        field_simp [hmne]
        <;> ring
  have h40n :
      2 + x5 / m ≤ (1 + x4 / m) * (1 + x0 / m) := by
    calc
      2 + x5 / m = (2 * m ^ 2 + m * x5) * (1 / m) ^ 2 := by
        field_simp [hmne]
        <;> ring
      _ ≤ ((m + x4) * (m + x0)) * (1 / m) ^ 2 :=
        mul_le_mul_of_nonneg_right h40 hsquare
      _ = (1 + x4 / m) * (1 + x0 / m) := by
        field_simp [hmne]
        <;> ring
  have h51n :
      2 + x0 / m ≤ (1 + x5 / m) * (1 + x1 / m) := by
    calc
      2 + x0 / m = (2 * m ^ 2 + m * x0) * (1 / m) ^ 2 := by
        field_simp [hmne]
        <;> ring
      _ ≤ ((m + x5) * (m + x1)) * (1 / m) ^ 2 :=
        mul_le_mul_of_nonneg_right h51 hsquare
      _ = (1 + x5 / m) * (1 + x1 / m) := by
        field_simp [hmne]
        <;> ring
  have hnorm := three_negative_excess_one
    (div_nonneg hx0 hm.le) (div_nonneg hx1 hm.le)
    (div_nonneg hx3 hm.le) (div_nonneg hx4 hm.le)
    (div_nonneg hx5 hm.le) h35n h40n h51n
  have hscaled := mul_le_mul_of_nonneg_left hnorm hm.le
  calc
    3 * m = m * 3 := by ring
    _ ≤ m * (x0 / m + x1 / m + x3 / m + x4 / m + x5 / m) := hscaled
    _ = x0 + x1 + x3 + x4 + x5 := by
      field_simp [hmne]
      <;> ring

/-- Three consecutive negative opposite brackets already force the sharp
boundary-sector bound, provided all six two-step brackets are positive. -/
private theorem consecutive_scalar
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc3 : c 3 ≤ -m) (hc4 : c 4 ≤ -m) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
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
        _ ≤ a i * a j + (-m) * a k := by
          simpa only [add_comm] using add_le_add_right hca (a i * a j)
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
  have hexcess := three_negative_excess hm hx0 hx1 hx3 hx4 hx5 h35 h40 h51
  nlinarith only [hexcess, hx2]

/-- Array-level form of the consecutive-opposite chamber bound.  The final
dispatcher applies this statement to cyclic shifts of its three arrays. -/
theorem h6_consecutive_array_bound
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc3 : c 3 ≤ -m) (hc4 : c 4 ≤ -m) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 :=
  consecutive_scalar m a d c hm ha hd hc3 hc4 hc5 hrel

/-- Sharp bound in the canonical all-two-step-positive block chamber. -/
theorem h6_consecutive_opposite_chamber_bound
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6ConsecutiveOppositeChamber b) :
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 := by
  rcases hchamber with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hc0pos, hc1pos, hc2pos⟩
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have ha : ∀ i, m ≤ a i := by
    intro i
    have hp := hedge i
    have hn : i ≠ i + 1 := by fin_cases i <;> decide
    have hf := hradial i (i + 1) hn
    rw [abs_of_pos hp] at hf
    exact hf
  have hdpos : ∀ i, 0 < d i := by
    intro i
    fin_cases i
    · simpa [d] using hd0
    · simpa [d] using hd1
    · simpa [d] using hd2
    · simpa [d] using hd3
    · simpa [d] using hd4
    · simpa [d] using hd5
  have hd : ∀ i, m ≤ d i := by
    intro i
    have hn : i ≠ i + 2 := by fin_cases i <;> decide
    have hf := hradial i (i + 2) hn
    rw [abs_of_pos (hdpos i)] at hf
    exact hf
  have hc3 : c 3 ≤ -m := by
    have hsym := hskew 3 0
    have hf := hradial 0 3 (by decide)
    rw [abs_of_pos hc0pos] at hf
    change b 3 0 ≤ -m
    linarith
  have hc4 : c 4 ≤ -m := by
    have hsym := hskew 4 1
    have hf := hradial 1 4 (by decide)
    rw [abs_of_pos hc1pos] at hf
    change b 4 1 ≤ -m
    linarith
  have hc5 : c 5 ≤ -m := by
    have hsym := hskew 5 2
    have hf := hradial 2 5 (by decide)
    rw [abs_of_pos hc2pos] at hf
    change b 5 2 ≤ -m
    linarith
  have hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1) := by
    intro i
    fin_cases i
    · have hp := hgp 0 1 2 3
      change b 0 2 * b 1 3 = b 0 1 * b 2 3 + b 0 3 * b 1 2
      linarith
    · have hp := hgp 1 2 3 4
      change b 1 3 * b 2 4 = b 1 2 * b 3 4 + b 1 4 * b 2 3
      linarith
    · have hp := hgp 2 3 4 5
      change b 2 4 * b 3 5 = b 2 3 * b 4 5 + b 2 5 * b 3 4
      linarith
    · have hp := hgp 3 4 5 0
      change b 3 5 * b 4 0 = b 3 4 * b 5 0 + b 3 0 * b 4 5
      linarith
    · have hp := hgp 4 5 0 1
      change b 4 0 * b 5 1 = b 4 5 * b 0 1 + b 4 1 * b 5 0
      linarith
    · have hp := hgp 5 0 1 2
      change b 5 1 * b 0 2 = b 5 0 * b 1 2 + b 5 2 * b 0 1
      linarith
  have hbound := consecutive_scalar m a d c hm ha hd hc3 hc4 hc5 hrel
  simpa [a] using hbound

end HeilbronnChallenge.N7Upper
