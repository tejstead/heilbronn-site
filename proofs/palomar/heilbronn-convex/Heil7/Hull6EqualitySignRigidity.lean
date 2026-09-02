import Heil7.Hull6SignReduction
import Heil7.Hull6ConsecutiveOppositeStrict
import Heil7.Hull6TwoNegativeChamber
import Heil7.Hull6OneNegativeChamberStrict

/-!
# Equality sign rigidity for the hull-six bracket core

Equality in the sharp `9m` fan bound can occur only in the tight sign orbit:
all cyclic two-step brackets are positive and the three unoriented opposite
brackets alternate in sign.  The proof first exposes the finite sign split
hidden inside `h6_sign_reduction`, then uses strict versions of the three
non-tight chamber bounds.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The five outcomes of the finite hull-six sign calculation.  The final
outcome is the elementary four-negative branch, which already costs `10m`. -/
def H6EqualitySignCases
    (m : ℝ) (a d c : Fin 6 → ℝ) : Prop :=
  (H6DAllPositive d ∧ H6CAlternating c) ∨
  (H6DAllPositive d ∧ H6CBlock c) ∨
  H6DOneNegative d ∨
  H6DTwoConsecutiveNegative d ∨
  10 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5

private def H6EqDFourNegative (d : Fin 6 → ℝ) : Prop :=
  (0 < d 0 ∧ 0 < d 1 ∧ d 2 < 0 ∧ d 3 < 0 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ d 3 < 0 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ d 1 < 0 ∧ 0 < d 2 ∧ 0 < d 3 ∧ d 4 < 0 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ 0 < d 3 ∧ 0 < d 4 ∧ d 5 < 0) ∨
  (d 0 < 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ d 3 < 0 ∧ 0 < d 4 ∧ 0 < d 5) ∨
  (0 < d 0 ∧ d 1 < 0 ∧ d 2 < 0 ∧ d 3 < 0 ∧ d 4 < 0 ∧ 0 < d 5)

private def H6EqSignChange (x y : ℝ) : Prop :=
  (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)

private lemma h6Eq_c_neg_of_signChange
    {a0 a1 a2 x y c : ℝ}
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hchange : H6EqSignChange x y)
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

private lemma h6Eq_three_mul_le
    {m a d c : ℝ} (hd : d ≤ -m) (hc : m ≤ c)
    (hout : m ≤ a + d - c) :
    3 * m ≤ a := by
  linarith

private lemma h6Eq_strictSignCases (x : ℝ) (h : x < 0 ∨ 0 < x) :
    (x < 0 ∧ ¬ 0 < x) ∨ (0 < x ∧ ¬ x < 0) := by
  rcases h with hneg | hpos
  · exact Or.inl ⟨hneg, not_lt_of_ge hneg.le⟩
  · exact Or.inr ⟨hpos, not_lt_of_ge hpos.le⟩

private lemma h6Eq_d_sign_shape
    (d : Fin 6 → ℝ)
    (h0 : d 0 < 0 ∨ 0 < d 0) (h1 : d 1 < 0 ∨ 0 < d 1)
    (h2 : d 2 < 0 ∨ 0 < d 2) (h3 : d 3 < 0 ∨ 0 < d 3)
    (h4 : d 4 < 0 ∨ 0 < d 4) (h5 : d 5 < 0 ∨ 0 < d 5)
    (heven : 0 < d 0 ∨ 0 < d 2 ∨ 0 < d 4)
    (hodd : 0 < d 1 ∨ 0 < d 3 ∨ 0 < d 5)
    (h03 : ¬ (H6EqSignChange (d 0) (d 1) ∧
      H6EqSignChange (d 3) (d 4)))
    (h14 : ¬ (H6EqSignChange (d 1) (d 2) ∧
      H6EqSignChange (d 4) (d 5)))
    (h25 : ¬ (H6EqSignChange (d 2) (d 3) ∧
      H6EqSignChange (d 5) (d 0))) :
    H6DAllPositive d ∨ H6DOneNegative d ∨
      H6DTwoConsecutiveNegative d ∨ H6EqDFourNegative d := by
  unfold H6DAllPositive H6DOneNegative
    H6DTwoConsecutiveNegative H6EqDFourNegative
  simp only [H6EqSignChange] at h03 h14 h25
  rcases h6Eq_strictSignCases (d 0) h0 with h0 | h0 <;>
    rcases h6Eq_strictSignCases (d 1) h1 with h1 | h1 <;>
      rcases h6Eq_strictSignCases (d 2) h2 with h2 | h2 <;>
        rcases h6Eq_strictSignCases (d 3) h3 with h3 | h3 <;>
          rcases h6Eq_strictSignCases (d 4) h4 with h4 | h4 <;>
            rcases h6Eq_strictSignCases (d 5) h5 with h5 | h5 <;>
              simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2,
                h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]
                at h03 h14 h25 heven hodd ⊢

private lemma h6Eq_c_sign_shape
    (c : Fin 6 → ℝ)
    (h0 : c 0 < 0 ∨ 0 < c 0) (h1 : c 1 < 0 ∨ 0 < c 1)
    (h2 : c 2 < 0 ∨ 0 < c 2) :
    H6CAlternating c ∨ H6CBlock c := by
  unfold H6CAlternating H6CBlock
  rcases h6Eq_strictSignCases (c 0) h0 with h0 | h0 <;>
    rcases h6Eq_strictSignCases (c 1) h1 with h1 | h1 <;>
      rcases h6Eq_strictSignCases (c 2) h2 with h2 | h2 <;>
        simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- Array-level finite sign classification.  It is independent of the
nonlinear chamber estimates and is useful specifically because it exposes
the branch that the bound-only dispatcher deliberately hides. -/
theorem h6_array_sign_cases
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (haPos : ∀ i, 0 < a i)
    (ha : ∀ i, m ≤ a i)
    (hdne : ∀ i, d i ≠ 0)
    (hcne : ∀ i, c i ≠ 0)
    (hdNegFloor : ∀ i, d i < 0 → d i ≤ -m)
    (hcPosFloor : ∀ i, 0 < c i → m ≤ c i)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hP : ∀ i : Fin 6, m ≤ a i + d (i + 1) - c i)
    (hQ : ∀ i : Fin 6, m ≤ d i + a (i + 2) - c i)
    (hEven : m ≤ d 0 + d 2 + d 4)
    (hOdd : m ≤ d 1 + d 3 + d 5) :
    H6EqualitySignCases m a d c := by
  have htransition : ∀ i : Fin 6,
      H6EqSignChange (d i) (d (i + 1)) → c i < 0 := by
    intro i hchange
    exact h6Eq_c_neg_of_signChange (haPos i) (haPos (i + 1))
      (haPos (i + 2)) hchange (hrel i)
  have hnoOpp : ∀ i : Fin 6,
      ¬ (H6EqSignChange (d i) (d (i + 1)) ∧
        H6EqSignChange (d (i + 3)) (d (i + 4))) := by
    intro i hboth
    have hci := htransition i hboth.1
    have hcj := htransition (i + 3) (by
      simpa [add_assoc] using hboth.2)
    have hop := hcopp i
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
  change ¬ (H6EqSignChange (d 0) (d 1) ∧
    H6EqSignChange (d 3) (d 4)) at hno03
  have hno14 := hnoOpp 1
  change ¬ (H6EqSignChange (d 1) (d 2) ∧
    H6EqSignChange (d 4) (d 5)) at hno14
  have hno25 := hnoOpp 2
  change ¬ (H6EqSignChange (d 2) (d 3) ∧
    H6EqSignChange (d 5) (d 0)) at hno25
  have hshape :
      H6DAllPositive d ∨ H6DOneNegative d ∨
      H6DTwoConsecutiveNegative d ∨ H6EqDFourNegative d :=
    h6Eq_d_sign_shape d hd0s hd1s hd2s hd3s hd4s hd5s
      hevenSome hoddSome hno03 hno14 hno25
  rcases hshape with hall | hone | htwo | hfour
  · have hc0s := lt_or_gt_of_ne (hcne 0)
    have hc1s := lt_or_gt_of_ne (hcne 1)
    have hc2s := lt_or_gt_of_ne (hcne 2)
    have hcshape : H6CAlternating c ∨ H6CBlock c :=
      h6Eq_c_sign_shape c hc0s hc1s hc2s
    rcases hcshape with halt | hblock
    · exact Or.inl ⟨hall, halt⟩
    · exact Or.inr (Or.inl ⟨hall, hblock⟩)
  · exact Or.inr (Or.inr (Or.inl hone))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htwo)))
  · have hbig : ∀ i : Fin 6,
        d i < 0 → d (i + 1) < 0 → 0 < c i →
        3 * m ≤ a i ∧ 3 * m ≤ a (i + 2) := by
      intro i hdi hdj hci
      constructor
      · exact h6Eq_three_mul_le (hdNegFloor (i + 1) hdj)
          (hcPosFloor i hci) (hP i)
      · exact h6Eq_three_mul_le (hdNegFloor i hdi)
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
      have hb := hbig 2 hd2 hd3 (by linarith)
      exact Or.inr (Or.inr (Or.inr (Or.inr (hten 2 hb.1 hb.2))))
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc0 := htransition 0 (Or.inl ⟨hd0, hd1⟩)
      have hop := hcopp 3
      change c 0 = -c 3 at hop
      have hb := hbig 3 hd3 hd4 (by linarith)
      exact Or.inr (Or.inr (Or.inr (Or.inr (hten 3 hb.1 hb.2))))
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc1 := htransition 1 (Or.inl ⟨hd1, hd2⟩)
      have hop := hcopp 4
      change c 1 = -c 4 at hop
      have hb := hbig 4 hd4 hd5 (by linarith)
      exact Or.inr (Or.inr (Or.inr (Or.inr (hten 4 hb.1 hb.2))))
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc2 := htransition 2 (Or.inl ⟨hd2, hd3⟩)
      have hop := hcopp 5
      change c 2 = -c 5 at hop
      have hb := hbig 5 hd5 hd0 (by linarith)
      exact Or.inr (Or.inr (Or.inr (Or.inr (hten 5 hb.1 hb.2))))
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc3 := htransition 3 (Or.inl ⟨hd3, hd4⟩)
      have hop := hcopp 0
      change c 3 = -c 0 at hop
      have hb := hbig 0 hd0 hd1 (by linarith)
      exact Or.inr (Or.inr (Or.inr (Or.inr (hten 0 hb.1 hb.2))))
    · rcases hfour with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hc4 := htransition 4 (Or.inl ⟨hd4, hd5⟩)
      have hop := hcopp 1
      change c 4 = -c 1 at hop
      have hb := hbig 1 hd1 hd2 (by linarith)
      exact Or.inr (Or.inr (Or.inr (Or.inr (hten 1 hb.1 hb.2))))

private def h6EqShiftArray (r : Fin 6) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => x (r + i)

private lemma h6EqShiftArray_sum (r : Fin 6) (a : Fin 6 → ℝ) :
    h6EqShiftArray r a 0 + h6EqShiftArray r a 1 +
        h6EqShiftArray r a 2 + h6EqShiftArray r a 3 +
        h6EqShiftArray r a 4 + h6EqShiftArray r a 5 =
      a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  fin_cases r
  · change a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = _
    ring
  · change a 1 + a 2 + a 3 + a 4 + a 5 + a 0 = _
    ring
  · change a 2 + a 3 + a 4 + a 5 + a 0 + a 1 = _
    ring
  · change a 3 + a 4 + a 5 + a 0 + a 1 + a 2 = _
    ring
  · change a 4 + a 5 + a 0 + a 1 + a 2 + a 3 = _
    ring
  · change a 5 + a 0 + a 1 + a 2 + a 3 + a 4 = _
    ring

private lemma h6EqShiftArray_rel
    (r : Fin 6) (a d c : Fin 6 → ℝ)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    ∀ i : Fin 6,
      h6EqShiftArray r d i * h6EqShiftArray r d (i + 1) =
        h6EqShiftArray r a i * h6EqShiftArray r a (i + 2) +
          h6EqShiftArray r c i * h6EqShiftArray r a (i + 1) := by
  intro i
  simpa only [h6EqShiftArray, add_assoc] using hrel (r + i)

private lemma h6EqShiftArray_cap
    (r : Fin 6) (m : ℝ) (a d : Fin 6 → ℝ)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m) :
    ∀ i : Fin 6,
      h6EqShiftArray r d i ≤
        h6EqShiftArray r a i + h6EqShiftArray r a (i + 1) - m := by
  intro i
  simpa only [h6EqShiftArray, add_assoc] using hcap (r + i)

private lemma h6EqShiftArray_opp
    (r : Fin 6) (c : Fin 6 → ℝ)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i) :
    ∀ i : Fin 6,
      h6EqShiftArray r c (i + 3) = -h6EqShiftArray r c i := by
  intro i
  simpa only [h6EqShiftArray, add_assoc] using hcopp (r + i)

private theorem h6Eq_block_shifted_strict
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i) (hd : ∀ i, m ≤ d i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hc3 : c (r + 3) ≤ -m) (hc4 : c (r + 4) ≤ -m)
    (hc5 : c (r + 5) ≤ -m) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hb := h6_consecutive_array_bound_strict m
    (h6EqShiftArray r a) (h6EqShiftArray r d) (h6EqShiftArray r c) hm
    (fun i => ha (r + i)) (fun i => hd (r + i))
    (by simpa [h6EqShiftArray] using hc3)
    (by simpa [h6EqShiftArray] using hc4)
    (by simpa [h6EqShiftArray] using hc5)
    (h6EqShiftArray_rel r a d c hrel)
  calc
    9 * m < h6EqShiftArray r a 0 + h6EqShiftArray r a 1 +
        h6EqShiftArray r a 2 + h6EqShiftArray r a 3 +
        h6EqShiftArray r a 4 + h6EqShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6EqShiftArray_sum r a

private theorem h6Eq_one_shifted_strict
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hd0 : d r ≤ -m)
    (hd1 : m ≤ d (r + 1)) (hd2 : m ≤ d (r + 2))
    (hd3 : m ≤ d (r + 3)) (hd4 : m ≤ d (r + 4))
    (hd5 : m ≤ d (r + 5)) (hc1abs : m ≤ |c (r + 1)|) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hcapS := h6EqShiftArray_cap r m a d hcap
  have hcoppS := h6EqShiftArray_opp r c hcopp
  have hb := h6_one_negative_array_bound_any_c1_strict m
    (h6EqShiftArray r a) (h6EqShiftArray r d) (h6EqShiftArray r c) hm
    (fun i => ha (r + i))
    (by simpa [h6EqShiftArray] using hd0)
    (by simpa [h6EqShiftArray] using hd1)
    (by simpa [h6EqShiftArray] using hd2)
    (by simpa [h6EqShiftArray] using hd3)
    (by simpa [h6EqShiftArray] using hd4)
    (by simpa [h6EqShiftArray] using hd5)
    (by simpa [h6EqShiftArray] using hc1abs)
    (hcapS 1) (hcapS 2) (hcapS 3) (hcapS 4) (hcapS 5)
    (hcoppS 0) (hcoppS 1) (hcoppS 2)
    (h6EqShiftArray_rel r a d c hrel)
  calc
    9 * m < h6EqShiftArray r a 0 + h6EqShiftArray r a 1 +
        h6EqShiftArray r a 2 + h6EqShiftArray r a 3 +
        h6EqShiftArray r a 4 + h6EqShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6EqShiftArray_sum r a

private theorem h6Eq_two_shifted_strict
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hd0 : d r ≤ -m) (hd1 : d (r + 1) ≤ -m)
    (hd2 : m ≤ d (r + 2)) (hd3 : m ≤ d (r + 3))
    (hd4 : m ≤ d (r + 4)) (hd5 : m ≤ d (r + 5)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hcapS := h6EqShiftArray_cap r m a d hcap
  have hcoppS := h6EqShiftArray_opp r c hcopp
  have hb := h6_two_negative_array_bound_strict m
    (h6EqShiftArray r a) (h6EqShiftArray r d) (h6EqShiftArray r c) hm
    (fun i => ha (r + i))
    (by simpa [h6EqShiftArray] using hd0)
    (by simpa [h6EqShiftArray] using hd1)
    (by simpa [h6EqShiftArray] using hd2)
    (by simpa [h6EqShiftArray] using hd3)
    (by simpa [h6EqShiftArray] using hd4)
    (by simpa [h6EqShiftArray] using hd5)
    (hcapS 2) (hcapS 3) (hcapS 4) (hcapS 5)
    (hcoppS 1) (hcoppS 2)
    (h6EqShiftArray_rel r a d c hrel)
  calc
    9 * m < h6EqShiftArray r a 0 + h6EqShiftArray r a 1 +
        h6EqShiftArray r a 2 + h6EqShiftArray r a 3 +
        h6EqShiftArray r a 4 + h6EqShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6EqShiftArray_sum r a

private theorem h6Eq_block_orbit_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i) (hd : ∀ i, m ≤ d i)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hcNegFloor : ∀ i, c i < 0 → c i ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hblock : H6CBlock c) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hc03 : c 3 = -c 0 := by simpa using hcopp 0
  have hc14 : c 4 = -c 1 := by simpa using hcopp 1
  have hc25 : c 5 = -c 2 := by simpa using hcopp 2
  rcases hblock with hcase | hcase | hcase | hcase | hcase | hcase
  · rcases hcase with ⟨hc0, hc1, hc2⟩
    exact h6Eq_block_shifted_strict m a d c 0 hm ha hd hrel
      (hcNegFloor 3 (by linarith)) (hcNegFloor 4 (by linarith))
      (hcNegFloor 5 (by linarith))
  · rcases hcase with ⟨hc0, hc1, hc2⟩
    exact h6Eq_block_shifted_strict m a d c 5 hm ha hd hrel
      (by simpa using hcNegFloor 2 hc2)
      (by simpa using hcNegFloor 3 (by linarith))
      (by simpa using hcNegFloor 4 (by linarith))
  · rcases hcase with ⟨hc0, hc1, hc2⟩
    exact h6Eq_block_shifted_strict m a d c 4 hm ha hd hrel
      (by simpa using hcNegFloor 1 hc1)
      (by simpa using hcNegFloor 2 hc2)
      (by simpa using hcNegFloor 3 (by linarith))
  · rcases hcase with ⟨hc0, hc1, hc2⟩
    exact h6Eq_block_shifted_strict m a d c 3 hm ha hd hrel
      (by simpa using hcNegFloor 0 hc0)
      (by simpa using hcNegFloor 1 hc1)
      (by simpa using hcNegFloor 2 hc2)
  · rcases hcase with ⟨hc0, hc1, hc2⟩
    exact h6Eq_block_shifted_strict m a d c 2 hm ha hd hrel
      (by simpa using hcNegFloor 5 (by linarith))
      (by simpa using hcNegFloor 0 hc0)
      (by simpa using hcNegFloor 1 hc1)
  · rcases hcase with ⟨hc0, hc1, hc2⟩
    exact h6Eq_block_shifted_strict m a d c 1 hm ha hd hrel
      (by simpa using hcNegFloor 4 (by linarith))
      (by simpa using hcNegFloor 5 (by linarith))
      (by simpa using hcNegFloor 0 hc0)

private theorem h6Eq_one_orbit_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hdPosFloor : ∀ i, 0 < d i → m ≤ d i)
    (hdNegFloor : ∀ i, d i < 0 → d i ≤ -m)
    (hcAbs : ∀ i, m ≤ |c i|)
    (hone : H6DOneNegative d) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  rcases hone with hcase | hcase | hcase | hcase | hcase | hcase
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_one_shifted_strict m a d c 0 hm ha hcap hcopp hrel
      (hdNegFloor 0 hd0) (hdPosFloor 1 hd1) (hdPosFloor 2 hd2)
      (hdPosFloor 3 hd3) (hdPosFloor 4 hd4) (hdPosFloor 5 hd5) (hcAbs 1)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_one_shifted_strict m a d c 1 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 1 hd1) (by simpa using hdPosFloor 2 hd2)
      (by simpa using hdPosFloor 3 hd3) (by simpa using hdPosFloor 4 hd4)
      (by simpa using hdPosFloor 5 hd5) (by simpa using hdPosFloor 0 hd0)
      (by simpa using hcAbs 2)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_one_shifted_strict m a d c 2 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 2 hd2) (by simpa using hdPosFloor 3 hd3)
      (by simpa using hdPosFloor 4 hd4) (by simpa using hdPosFloor 5 hd5)
      (by simpa using hdPosFloor 0 hd0) (by simpa using hdPosFloor 1 hd1)
      (by simpa using hcAbs 3)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_one_shifted_strict m a d c 3 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 3 hd3) (by simpa using hdPosFloor 4 hd4)
      (by simpa using hdPosFloor 5 hd5) (by simpa using hdPosFloor 0 hd0)
      (by simpa using hdPosFloor 1 hd1) (by simpa using hdPosFloor 2 hd2)
      (by simpa using hcAbs 4)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_one_shifted_strict m a d c 4 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 4 hd4) (by simpa using hdPosFloor 5 hd5)
      (by simpa using hdPosFloor 0 hd0) (by simpa using hdPosFloor 1 hd1)
      (by simpa using hdPosFloor 2 hd2) (by simpa using hdPosFloor 3 hd3)
      (by simpa using hcAbs 5)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_one_shifted_strict m a d c 5 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 5 hd5) (by simpa using hdPosFloor 0 hd0)
      (by simpa using hdPosFloor 1 hd1) (by simpa using hdPosFloor 2 hd2)
      (by simpa using hdPosFloor 3 hd3) (by simpa using hdPosFloor 4 hd4)
      (by simpa using hcAbs 0)

private theorem h6Eq_two_orbit_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hdPosFloor : ∀ i, 0 < d i → m ≤ d i)
    (hdNegFloor : ∀ i, d i < 0 → d i ≤ -m)
    (htwo : H6DTwoConsecutiveNegative d) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  rcases htwo with hcase | hcase | hcase | hcase | hcase | hcase
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_two_shifted_strict m a d c 0 hm ha hcap hcopp hrel
      (hdNegFloor 0 hd0) (hdNegFloor 1 hd1)
      (hdPosFloor 2 hd2) (hdPosFloor 3 hd3)
      (hdPosFloor 4 hd4) (hdPosFloor 5 hd5)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_two_shifted_strict m a d c 1 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 1 hd1) (by simpa using hdNegFloor 2 hd2)
      (by simpa using hdPosFloor 3 hd3) (by simpa using hdPosFloor 4 hd4)
      (by simpa using hdPosFloor 5 hd5) (by simpa using hdPosFloor 0 hd0)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_two_shifted_strict m a d c 2 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 2 hd2) (by simpa using hdNegFloor 3 hd3)
      (by simpa using hdPosFloor 4 hd4) (by simpa using hdPosFloor 5 hd5)
      (by simpa using hdPosFloor 0 hd0) (by simpa using hdPosFloor 1 hd1)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_two_shifted_strict m a d c 3 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 3 hd3) (by simpa using hdNegFloor 4 hd4)
      (by simpa using hdPosFloor 5 hd5) (by simpa using hdPosFloor 0 hd0)
      (by simpa using hdPosFloor 1 hd1) (by simpa using hdPosFloor 2 hd2)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_two_shifted_strict m a d c 4 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 4 hd4) (by simpa using hdNegFloor 5 hd5)
      (by simpa using hdPosFloor 0 hd0) (by simpa using hdPosFloor 1 hd1)
      (by simpa using hdPosFloor 2 hd2) (by simpa using hdPosFloor 3 hd3)
  · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    exact h6Eq_two_shifted_strict m a d c 5 hm ha hcap hcopp hrel
      (by simpa using hdNegFloor 5 hd5) (by simpa using hdNegFloor 0 hd0)
      (by simpa using hdPosFloor 1 hd1) (by simpa using hdPosFloor 2 hd2)
      (by simpa using hdPosFloor 3 hd3) (by simpa using hdPosFloor 4 hd4)

/-- Equality in the full hull-six bracket core forces the unique tight sign
orbit.  In particular every non-tight chamber is separated from equality by
a strict inequality. -/
theorem h6_bracket_equality_signs
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (hhull : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (heq : b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 = 9 * m) :
    H6DAllPositive (fun i => b i (i + 2)) ∧
      H6CAlternating (fun i => b i (i + 3)) := by
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
  have hdPosFloor : ∀ i, 0 < d i → m ≤ d i := by
    intro i hi
    have hf := hradial i (i + 2) (by fin_cases i <;> decide)
    change m ≤ |d i| at hf
    rwa [abs_of_pos hi] at hf
  have hdNegFloor : ∀ i, d i < 0 → d i ≤ -m := by
    intro i hi
    have hf := hradial i (i + 2) (by fin_cases i <;> decide)
    change m ≤ |d i| at hf
    rw [abs_of_neg hi] at hf
    linarith
  have hcNegFloor : ∀ i, c i < 0 → c i ≤ -m := by
    intro i hi
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    change m ≤ |c i| at hf
    rw [abs_of_neg hi] at hf
    linarith
  have hcPosFloor : ∀ i, 0 < c i → m ≤ c i := by
    intro i hi
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    change m ≤ |c i| at hf
    rwa [abs_of_pos hi] at hf
  have hcAbs : ∀ i, m ≤ |c i| := by
    intro i
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    simpa [c] using hf
  have hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m := by
    intro i
    fin_cases i
    · have ho := hhull 0 1 2 (by decide) (by decide)
      change b 0 2 ≤ b 0 1 + b 1 2 - m
      linarith
    · have ho := hhull 1 2 3 (by decide) (by decide)
      change b 1 3 ≤ b 1 2 + b 2 3 - m
      linarith
    · have ho := hhull 2 3 4 (by decide) (by decide)
      change b 2 4 ≤ b 2 3 + b 3 4 - m
      linarith
    · have ho := hhull 3 4 5 (by decide) (by decide)
      change b 3 5 ≤ b 3 4 + b 4 5 - m
      linarith
    · have ho := hhull 0 4 5 (by decide) (by decide)
      have hs40 := hskew 4 0
      have hs50 := hskew 5 0
      change b 4 0 ≤ b 4 5 + b 5 0 - m
      linarith
    · have ho := hhull 0 1 5 (by decide) (by decide)
      have hs51 := hskew 5 1
      have hs50 := hskew 5 0
      change b 5 1 ≤ b 5 0 + b 0 1 - m
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
  have hcases := h6_array_sign_cases m a d c hm haPos ha hdne hcne
    hdNegFloor hcPosFloor hcopp hrel hP hQ hEven hOdd
  have hsumEq : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 9 * m := by
    simpa [a] using heq
  unfold H6EqualitySignCases at hcases
  rcases hcases with halt | hblock | hone | htwo | hten
  · exact ⟨by simpa [d] using halt.1, by simpa [c] using halt.2⟩
  · have hdFloor : ∀ i, m ≤ d i := by
      intro i
      rcases hblock.1 with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      fin_cases i
      · exact hdPosFloor 0 hd0
      · exact hdPosFloor 1 hd1
      · exact hdPosFloor 2 hd2
      · exact hdPosFloor 3 hd3
      · exact hdPosFloor 4 hd4
      · exact hdPosFloor 5 hd5
    have hstrict := h6Eq_block_orbit_strict m a d c hm ha hdFloor hcopp
      hcNegFloor hrel hblock.2
    exfalso
    linarith only [hstrict, hsumEq]
  · have hstrict := h6Eq_one_orbit_strict m a d c hm ha hcap hcopp hrel
      hdPosFloor hdNegFloor hcAbs hone
    exfalso
    linarith only [hstrict, hsumEq]
  · have hstrict := h6Eq_two_orbit_strict m a d c hm ha hcap hcopp hrel
      hdPosFloor hdNegFloor htwo
    exfalso
    linarith only [hstrict, hsumEq]
  · exfalso
    linarith only [hten, hsumEq, hm]

end HeilbronnChallenge.N7Upper
