import Heil7.Hull6BracketRoute

/-!
# Finite sign reduction for the hull-six bracket core

Put

* `a i = b i (i+1)`,
* `d i = b i (i+2)`, and
* `c i = b i (i+3)`.

This file contains only the finite sign dispatcher.  It reduces the scalar
hexagon theorem to the two opposite-sign orbits when all `d i` are positive,
the orbit with one negative `d i`, and the orbit with two consecutive negative
`d i`.  No angular or winding-number formalization is needed: GP rules out
antipodal pairs of sign transitions.  The two alternating hull-triangle rows
rule out five or six negative `d i`, while the remaining four-negative orbit
already gives the stronger boundary bound `10m`.

The four callback hypotheses are the deliberately narrow seam for the chamber
proofs.  This module does not assert any of those nonlinear chamber bounds.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- All six cyclic two-step brackets are positive. -/
def H6DAllPositive (d : Fin 6 → ℝ) : Prop :=
  0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧
  0 < d 3 ∧ 0 < d 4 ∧ 0 < d 5

/-- Exactly one cyclic two-step bracket is negative. -/
def H6DOneNegative (d : Fin 6 → ℝ) : Prop :=
  (d 0 < 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ d 1 < 0 ∧ 0 < d 2 ∧ 0 < d 3 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ d 2 < 0 ∧ 0 < d 3 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ d 3 < 0 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 ∧ d 4 < 0 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 ∧ 0 < d 4 ∧ d 5 < 0)

/-- Exactly two cyclically consecutive two-step brackets are negative. -/
def H6DTwoConsecutiveNegative (d : Fin 6 → ℝ) : Prop :=
  (d 0 < 0 ∧ d 1 < 0 ∧ 0 < d 2 ∧ 0 < d 3 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ 0 < d 3 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ d 2 < 0 ∧ d 3 < 0 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ d 3 < 0 ∧ d 4 < 0 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 ∧ 0 < d 4 ∧ d 5 < 0)

/-- The alternating orbit of the three unoriented opposite-ray brackets.
Skew-symmetry supplies the signs at indices `3,4,5`. -/
def H6CAlternating (c : Fin 6 → ℝ) : Prop :=
  (0 < c 0 ∧ c 1 < 0 ∧ 0 < c 2) ∨
  (c 0 < 0 ∧ 0 < c 1 ∧ c 2 < 0)

/-- The other opposite-ray orbit: three positive signs followed cyclically by
three negative signs.  The six displayed cases are its possible rotations,
recorded using `c 0,c 1,c 2`; skew supplies `c 3,c 4,c 5`. -/
def H6CBlock (c : Fin 6 → ℝ) : Prop :=
  (0 < c 0 ∧ 0 < c 1 ∧ 0 < c 2) ∨
  (0 < c 0 ∧ 0 < c 1 ∧ c 2 < 0) ∨
  (0 < c 0 ∧ c 1 < 0 ∧ c 2 < 0) ∨
  (c 0 < 0 ∧ c 1 < 0 ∧ c 2 < 0) ∨
  (c 0 < 0 ∧ c 1 < 0 ∧ 0 < c 2) ∨
  (c 0 < 0 ∧ 0 < c 1 ∧ 0 < c 2)

private def H6DFourNegative (d : Fin 6 → ℝ) : Prop :=
  (0 < d 0 ∧ 0 < d 1 ∧ d 2 < 0 ∧ d 3 < 0 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ d 3 < 0 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ d 1 < 0 ∧ 0 < d 2 ∧ 0 < d 3 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ 0 < d 3 ∧ 0 < d 4 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ d 3 < 0 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ d 3 < 0 ∧ d 4 < 0 ∧ 0 < d 5)

private def SignChange (x y : ℝ) : Prop :=
  (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)

private lemma strictSignCases (x : ℝ) (h : x < 0 ∨ 0 < x) :
    (x < 0 ∧ ¬ 0 < x) ∨ (0 < x ∧ ¬ x < 0) := by
  rcases h with hneg | hpos
  · exact Or.inl ⟨hneg, not_lt_of_ge hneg.le⟩
  · exact Or.inr ⟨hpos, not_lt_of_ge hpos.le⟩

private lemma h6_d_sign_shape
    (d : Fin 6 → ℝ)
    (h0 : d 0 < 0 ∨ 0 < d 0) (h1 : d 1 < 0 ∨ 0 < d 1)
    (h2 : d 2 < 0 ∨ 0 < d 2) (h3 : d 3 < 0 ∨ 0 < d 3)
    (h4 : d 4 < 0 ∨ 0 < d 4) (h5 : d 5 < 0 ∨ 0 < d 5)
    (heven : 0 < d 0 ∨ 0 < d 2 ∨ 0 < d 4)
    (hodd : 0 < d 1 ∨ 0 < d 3 ∨ 0 < d 5)
    (h03 : SignChange (d 0) (d 1) → ¬ SignChange (d 3) (d 4))
    (h14 : SignChange (d 1) (d 2) → ¬ SignChange (d 4) (d 5))
    (h25 : SignChange (d 2) (d 3) → ¬ SignChange (d 5) (d 0)) :
    H6DAllPositive d ∨ H6DOneNegative d ∨
      H6DTwoConsecutiveNegative d ∨ H6DFourNegative d := by
  unfold H6DAllPositive H6DOneNegative
    H6DTwoConsecutiveNegative H6DFourNegative
  simp only [SignChange] at h03 h14 h25
  rcases strictSignCases (d 0) h0 with h0 | h0 <;>
    rcases strictSignCases (d 1) h1 with h1 | h1 <;>
      rcases strictSignCases (d 2) h2 with h2 | h2 <;>
        rcases strictSignCases (d 3) h3 with h3 | h3 <;>
          rcases strictSignCases (d 4) h4 with h4 | h4 <;>
            rcases strictSignCases (d 5) h5 with h5 | h5 <;>
              simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2] at h03 h14 h25 heven hodd ⊢

private lemma h6_c_sign_shape
    (c : Fin 6 → ℝ)
    (h0 : c 0 < 0 ∨ 0 < c 0) (h1 : c 1 < 0 ∨ 0 < c 1)
    (h2 : c 2 < 0 ∨ 0 < c 2) :
    H6CAlternating c ∨ H6CBlock c := by
  unfold H6CAlternating H6CBlock
  rcases strictSignCases (c 0) h0 with h0 | h0 <;>
    rcases strictSignCases (c 1) h1 with h1 | h1 <;>
      rcases strictSignCases (c 2) h2 with h2 | h2 <;>
        simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

private lemma c_neg_of_signChange
    {a0 a1 a2 x y c : ℝ}
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hchange : SignChange x y)
    (hgp : x * y = a0 * a2 + c * a1) :
    c < 0 := by
  have hxy : x * y < 0 := by
    rcases hchange with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact mul_neg_of_neg_of_pos hx hy
    · exact mul_neg_of_pos_of_neg hx hy
  have haa : 0 < a0 * a2 := mul_pos ha0 ha2
  have hca : c * a1 < 0 := by nlinarith only [hgp, hxy, haa]
  by_contra hn
  have hc : 0 ≤ c := le_of_not_gt hn
  exact (not_lt_of_ge (mul_nonneg hc ha1.le)) hca

private lemma three_mul_le_of_outer
    {m a d c : ℝ} (hd : d ≤ -m) (hc : m ≤ c)
    (hout : m ≤ a + d - c) :
    3 * m ≤ a := by
  linarith

/-- Finite dispatcher for the signs occurring in `H6BracketCore`.

The all-positive branch is split into the alternating and block orbits of the
opposite brackets.  The other callbacks receive all cyclic rotations at once.
Every sign pattern not covered by a callback is either inconsistent with the
two alternating hull-triangle floors, inconsistent with GP/skew, or already
forces the stronger estimate `10m`. -/
theorem h6_sign_reduction
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (hhull : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hallAlt :
      H6DAllPositive (fun i => b i (i + 2)) →
      H6CAlternating (fun i => b i (i + 3)) →
      9 * m ≤ b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0)
    (hallBlock :
      H6DAllPositive (fun i => b i (i + 2)) →
      H6CBlock (fun i => b i (i + 3)) →
      9 * m ≤ b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0)
    (hone :
      H6DOneNegative (fun i => b i (i + 2)) →
      9 * m ≤ b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0)
    (htwo :
      H6DTwoConsecutiveNegative (fun i => b i (i + 2)) →
      9 * m ≤ b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0) :
    9 * m ≤ b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 := by
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have haPos : ∀ i, 0 < a i := by
    intro i
    exact hedge i
  have ha : ∀ i, m ≤ a i := by
    intro i
    have hf := hradial i (i + 1) (by fin_cases i <;> decide)
    rw [abs_of_pos (haPos i)] at hf
    exact hf
  have hdne : ∀ i, d i ≠ 0 := by
    intro i hz
    have hf := hradial i (i + 2) (by fin_cases i <;> decide)
    change m ≤ |d i| at hf
    rw [hz, abs_zero] at hf
    linarith
  have hcne : ∀ i, c i ≠ 0 := by
    intro i hz
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    change m ≤ |c i| at hf
    rw [hz, abs_zero] at hf
    linarith
  have hcopp : ∀ i : Fin 6, c (i + 3) = -c i := by
    intro i
    fin_cases i
    · change b 3 0 = -b 0 3
      exact hskew 3 0
    · change b 4 1 = -b 1 4
      exact hskew 4 1
    · change b 5 2 = -b 2 5
      exact hskew 5 2
    · change b 0 3 = -b 3 0
      exact hskew 0 3
    · change b 1 4 = -b 4 1
      exact hskew 1 4
    · change b 2 5 = -b 5 2
      exact hskew 2 5
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
  have htransition : ∀ i : Fin 6,
      SignChange (d i) (d (i + 1)) → c i < 0 := by
    intro i hchange
    exact c_neg_of_signChange (haPos i) (haPos (i + 1))
      (haPos (i + 2)) hchange (hrel i)
  have hnoOpp : ∀ i : Fin 6,
      ¬ (SignChange (d i) (d (i + 1)) ∧
        SignChange (d (i + 3)) (d (i + 4))) := by
    intro i hboth
    have hci := htransition i hboth.1
    have hcj := htransition (i + 3) (by
      simpa [add_assoc] using hboth.2)
    have hop := hcopp i
    linarith
  have hP : ∀ i : Fin 6, m ≤ a i + d (i + 1) - c i := by
    intro i
    fin_cases i
    · change m ≤ b 0 1 + b 1 3 - b 0 3
      exact hhull 0 1 3 (by decide) (by decide)
    · change m ≤ b 1 2 + b 2 4 - b 1 4
      exact hhull 1 2 4 (by decide) (by decide)
    · change m ≤ b 2 3 + b 3 5 - b 2 5
      exact hhull 2 3 5 (by decide) (by decide)
    · have hh := hhull 0 3 4 (by decide) (by decide)
      have hs0 := hskew 3 0
      have hs1 := hskew 4 0
      change m ≤ b 3 4 + b 4 0 - b 3 0
      linarith
    · have hh := hhull 1 4 5 (by decide) (by decide)
      have hs0 := hskew 4 1
      have hs1 := hskew 5 1
      change m ≤ b 4 5 + b 5 1 - b 4 1
      linarith
    · have hh := hhull 0 2 5 (by decide) (by decide)
      have hs0 := hskew 5 0
      have hs1 := hskew 5 2
      change m ≤ b 5 0 + b 0 2 - b 5 2
      linarith
  have hQ : ∀ i : Fin 6, m ≤ d i + a (i + 2) - c i := by
    intro i
    fin_cases i
    · change m ≤ b 0 2 + b 2 3 - b 0 3
      exact hhull 0 2 3 (by decide) (by decide)
    · change m ≤ b 1 3 + b 3 4 - b 1 4
      exact hhull 1 3 4 (by decide) (by decide)
    · change m ≤ b 2 4 + b 4 5 - b 2 5
      exact hhull 2 4 5 (by decide) (by decide)
    · have hh := hhull 0 3 5 (by decide) (by decide)
      have hs0 := hskew 3 0
      have hs1 := hskew 5 0
      change m ≤ b 3 5 + b 5 0 - b 3 0
      linarith
    · have hh := hhull 0 1 4 (by decide) (by decide)
      have hs0 := hskew 4 0
      have hs1 := hskew 4 1
      change m ≤ b 4 0 + b 0 1 - b 4 1
      linarith
    · have hh := hhull 1 2 5 (by decide) (by decide)
      have hs0 := hskew 5 1
      have hs1 := hskew 5 2
      change m ≤ b 5 1 + b 1 2 - b 5 2
      linarith
  have hEven : m ≤ d 0 + d 2 + d 4 := by
    have hh := hhull 0 2 4 (by decide) (by decide)
    have hs := hskew 4 0
    change m ≤ b 0 2 + b 2 4 + b 4 0
    linarith
  have hOdd : m ≤ d 1 + d 3 + d 5 := by
    have hh := hhull 1 3 5 (by decide) (by decide)
    have hs := hskew 5 1
    change m ≤ b 1 3 + b 3 5 + b 5 1
    linarith
  have hd0s := lt_or_gt_of_ne (hdne 0)
  have hd1s := lt_or_gt_of_ne (hdne 1)
  have hd2s := lt_or_gt_of_ne (hdne 2)
  have hd3s := lt_or_gt_of_ne (hdne 3)
  have hd4s := lt_or_gt_of_ne (hdne 4)
  have hd5s := lt_or_gt_of_ne (hdne 5)
  have hevenSome : 0 < d 0 ∨ 0 < d 2 ∨ 0 < d 4 := by
    by_contra hn
    push_neg at hn
    linarith
  have hoddSome : 0 < d 1 ∨ 0 < d 3 ∨ 0 < d 5 := by
    by_contra hn
    push_neg at hn
    linarith
  have hno03 := hnoOpp 0
  have hno14 := hnoOpp 1
  have hno25 := hnoOpp 2
  norm_num at hno03 hno14 hno25
  have hshape :
      H6DAllPositive d ∨ H6DOneNegative d ∨
      H6DTwoConsecutiveNegative d ∨ H6DFourNegative d :=
    h6_d_sign_shape d hd0s hd1s hd2s hd3s hd4s hd5s
      hevenSome hoddSome hno03 hno14 hno25
  rcases hshape with hall | honeCase | htwoCase | hfour
  · have hc0s := lt_or_gt_of_ne (hcne 0)
    have hc1s := lt_or_gt_of_ne (hcne 1)
    have hc2s := lt_or_gt_of_ne (hcne 2)
    have hcshape : H6CAlternating c ∨ H6CBlock c :=
      h6_c_sign_shape c hc0s hc1s hc2s
    rcases hcshape with halt | hblock
    · apply hallAlt
      · simpa [d] using hall
      · simpa [c] using halt
    · apply hallBlock
      · simpa [d] using hall
      · simpa [c] using hblock
  · apply hone
    simpa [d] using honeCase
  · apply htwo
    simpa [d] using htwoCase
  · have hdNegFloor : ∀ i, d i < 0 → d i ≤ -m := by
      intro i hdi
      have hf := hradial i (i + 2) (by fin_cases i <;> decide)
      rw [abs_of_neg hdi] at hf
      linarith
    have hcPosFloor : ∀ i, 0 < c i → m ≤ c i := by
      intro i hci
      have hf := hradial i (i + 3) (by fin_cases i <;> decide)
      rwa [abs_of_pos hci] at hf
    have hbig : ∀ i : Fin 6,
        d i < 0 → d (i + 1) < 0 → 0 < c i →
        3 * m ≤ a i ∧ 3 * m ≤ a (i + 2) := by
      intro i hdi hdj hci
      constructor
      · exact three_mul_le_of_outer (hdNegFloor (i + 1) hdj)
          (hcPosFloor i hci) (hP i)
      · exact three_mul_le_of_outer (hdNegFloor i hdi)
          (hcPosFloor i hci) (by simpa [add_comm] using hQ i)
    have hten : ∀ i : Fin 6,
        3 * m ≤ a i → 3 * m ≤ a (i + 2) →
        10 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
      intro i hi hj
      have ha0 := ha 0
      have ha1 := ha 1
      have ha2 := ha 2
      have ha3 := ha 3
      have ha4 := ha 4
      have ha5 := ha 5
      fin_cases i
      · change 3 * m ≤ a 0 at hi
        change 3 * m ≤ a 2 at hj
        linarith only [hi, hj, ha0, ha1, ha2, ha3, ha4, ha5]
      · change 3 * m ≤ a 1 at hi
        change 3 * m ≤ a 3 at hj
        linarith only [hi, hj, ha0, ha1, ha2, ha3, ha4, ha5]
      · change 3 * m ≤ a 2 at hi
        change 3 * m ≤ a 4 at hj
        linarith only [hi, hj, ha0, ha1, ha2, ha3, ha4, ha5]
      · change 3 * m ≤ a 3 at hi
        change 3 * m ≤ a 5 at hj
        linarith only [hi, hj, ha0, ha1, ha2, ha3, ha4, ha5]
      · change 3 * m ≤ a 4 at hi
        change 3 * m ≤ a 0 at hj
        linarith only [hi, hj, ha0, ha1, ha2, ha3, ha4, ha5]
      · change 3 * m ≤ a 5 at hi
        change 3 * m ≤ a 1 at hj
        linarith only [hi, hj, ha0, ha1, ha2, ha3, ha4, ha5]
    rcases hfour with hfour | hfour | hfour | hfour | hfour | hfour
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc5 := htransition 5 (Or.inl ⟨hd5, hd0⟩)
      have hop := hcopp 2
      change c 5 = -c 2 at hop
      have hb := hbig 2 hd2 hd3 (by linarith only [hop, hc5])
      have ht := hten 2 hb.1 hb.2
      simpa [a] using (show 9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by
        linarith)
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc0 := htransition 0 (Or.inl ⟨hd0, hd1⟩)
      have hop := hcopp 3
      change c 0 = -c 3 at hop
      have hb := hbig 3 hd3 hd4 (by linarith only [hop, hc0])
      have ht := hten 3 hb.1 hb.2
      simpa [a] using (show 9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by
        linarith)
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc1 := htransition 1 (Or.inl ⟨hd1, hd2⟩)
      have hop := hcopp 4
      change c 1 = -c 4 at hop
      have hb := hbig 4 hd4 hd5 (by linarith only [hop, hc1])
      have ht := hten 4 hb.1 hb.2
      simpa [a] using (show 9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by
        linarith)
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc2 := htransition 2 (Or.inl ⟨hd2, hd3⟩)
      have hop := hcopp 5
      change c 2 = -c 5 at hop
      have hb := hbig 5 hd5 hd0 (by linarith only [hop, hc2])
      have ht := hten 5 hb.1 hb.2
      simpa [a] using (show 9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by
        linarith)
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc3 := htransition 3 (Or.inl ⟨hd3, hd4⟩)
      have hop := hcopp 0
      change c 3 = -c 0 at hop
      have hb := hbig 0 hd0 hd1 (by linarith only [hop, hc3])
      have ht := hten 0 hb.1 hb.2
      simpa [a] using (show 9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by
        linarith)
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc4 := htransition 4 (Or.inl ⟨hd4, hd5⟩)
      have hop := hcopp 1
      change c 4 = -c 1 at hop
      have hb := hbig 1 hd1 hd2 (by linarith only [hop, hc4])
      have ht := hten 1 hb.1 hb.2
      simpa [a] using (show 9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by
        linarith)

end HeilbronnChallenge.N7Upper
