import Heil7.Hull7ContinuantScalar

/-!
# Strict form of the hull-seven continuant bound

The centered endpoint calculation in `Hull7ContinuantScalar` leaves a gap of
at least two.  Consequently the borderline fan sum `9` is impossible: the
continuant hypotheses imply a strict inequality, not merely the weak bound
needed by the canonical challenge theorem.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The normalized continuant packet excludes equality at fan sum nine. -/
theorem nine_lt_fanSum_of_hullSeven_continuant
    (a b c d e p16 q2 q3 q4 q5 r14 r15 r25 r26 r36 : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hp16 : 1 ≤ p16)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5)
    (hr14 : 0 ≤ r14) (hr15 : 0 ≤ r15)
    (hr25 : 0 ≤ r25) (hr26 : 0 ≤ r26) (hr36 : 0 ≤ r36)
    (hear2 : q2 ≤ a + b - 1) (hear3 : q3 ≤ b + c - 1)
    (hear4 : q4 ≤ c + d - 1) (hear5 : q5 ≤ d + e - 1)
    (h14 : b * r14 = q2 * q3 - a * c)
    (h15 : c * r15 = r14 * q4 - q2 * d)
    (h16 : d * p16 = r15 * q5 - r14 * e)
    (h25 : c * r25 = q3 * q4 - b * d)
    (h26 : d * r26 = r25 * q5 - q3 * e)
    (h36 : d * r36 = q4 * q5 - c * e) :
    9 < a + b + c + d + e := by
  let Q2 : ℝ := a + b - 1
  let Q3 : ℝ := b + c - 1
  let Q4 : ℝ := c + d - 1
  let Q5 : ℝ := d + e - 1
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; linarith
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; linarith
  have hQ4 : 0 ≤ Q4 := by dsimp [Q4]; linarith
  have hQ5 : 0 ≤ Q5 := by dsimp [Q5]; linarith
  have hmono := hullSevenContinuantNumerator_mono
    a b c d e q2 q3 q4 q5 Q2 Q3 Q4 Q5 r14 r15 r25 r26 r36
    (by linarith) (by linarith) (by linarith)
    hq2 hq3 hq4 hq5 hQ2 hQ3 hQ4 hQ5
    hr14 hr15 hr25 hr26 hr36
    (by simpa [Q2] using hear2) (by simpa [Q3] using hear3)
    (by simpa [Q4] using hear4) (by simpa [Q5] using hear5)
    h14 h15 h25 h26 h36
  have hcont := hullSeven_continuant_identity
    a b c d e q2 q3 q4 q5 r14 r15 p16 h14 h15 h16
  have hdennonneg : 0 ≤ b * c * d := by positivity
  have hpLower : b * c * d ≤ b * c * d * p16 := by
    nlinarith [mul_nonneg hdennonneg (sub_nonneg.mpr hp16)]
  have hbase :
      b * c * d ≤ hullSevenMaximalContinuantNumerator a b c d e := by
    dsimp [Q2, Q3, Q4, Q5] at hmono
    rw [← hcont] at hmono
    exact hpLower.trans hmono
  by_contra hn
  have hsum : a + b + c + d + e ≤ 9 := le_of_not_gt hn
  have hstrict :=
    hullSeven_maximalContinuant_lt_denominator ha hb hc hd he hsum
  exact (not_lt_of_ge hbase) hstrict

/-- Homogeneous strict form.  Positivity of `m` is essential when rescaling
the strict normalized inequality. -/
theorem nine_mul_lt_fanSum_of_hullSeven_continuant
    (m a b c d e p16 q2 q3 q4 q5 r14 r15 r25 r26 r36 : ℝ)
    (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hd : m ≤ d) (he : m ≤ e) (hp16 : m ≤ p16)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5)
    (hr14 : 0 ≤ r14) (hr15 : 0 ≤ r15)
    (hr25 : 0 ≤ r25) (hr26 : 0 ≤ r26) (hr36 : 0 ≤ r36)
    (hear2 : q2 ≤ a + b - m) (hear3 : q3 ≤ b + c - m)
    (hear4 : q4 ≤ c + d - m) (hear5 : q5 ≤ d + e - m)
    (h14 : b * r14 = q2 * q3 - a * c)
    (h15 : c * r15 = r14 * q4 - q2 * d)
    (h16 : d * p16 = r15 * q5 - r14 * e)
    (h25 : c * r25 = q3 * q4 - b * d)
    (h26 : d * r26 = r25 * q5 - q3 * e)
    (h36 : d * r36 = q4 * q5 - c * e) :
    9 * m < a + b + c + d + e := by
  have hm0 : 0 ≤ m := hm.le
  have hn := nine_lt_fanSum_of_hullSeven_continuant
    (a / m) (b / m) (c / m) (d / m) (e / m) (p16 / m)
    (q2 / m) (q3 / m) (q4 / m) (q5 / m)
    (r14 / m) (r15 / m) (r25 / m) (r26 / m) (r36 / m)
    (by apply (le_div_iff₀ hm).2; simpa using ha)
    (by apply (le_div_iff₀ hm).2; simpa using hb)
    (by apply (le_div_iff₀ hm).2; simpa using hc)
    (by apply (le_div_iff₀ hm).2; simpa using hd)
    (by apply (le_div_iff₀ hm).2; simpa using he)
    (by apply (le_div_iff₀ hm).2; simpa using hp16)
    (div_nonneg hq2 hm0) (div_nonneg hq3 hm0)
    (div_nonneg hq4 hm0) (div_nonneg hq5 hm0)
    (div_nonneg hr14 hm0) (div_nonneg hr15 hm0)
    (div_nonneg hr25 hm0) (div_nonneg hr26 hm0) (div_nonneg hr36 hm0)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q2 ≤ a + b - m := hear2
        _ = (a / m + b / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q3 ≤ b + c - m := hear3
        _ = (b / m + c / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q4 ≤ c + d - m := hear4
        _ = (c / m + d / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q5 ≤ d + e - m := hear5
        _ = (d / m + e / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      calc
        b / m * (r14 / m) = (b * r14) / m ^ 2 := by ring
        _ = (q2 * q3 - a * c) / m ^ 2 := by rw [h14]
        _ = q2 / m * (q3 / m) - a / m * (c / m) := by ring)
    (by
      calc
        c / m * (r15 / m) = (c * r15) / m ^ 2 := by ring
        _ = (r14 * q4 - q2 * d) / m ^ 2 := by rw [h15]
        _ = r14 / m * (q4 / m) - q2 / m * (d / m) := by ring)
    (by
      calc
        d / m * (p16 / m) = (d * p16) / m ^ 2 := by ring
        _ = (r15 * q5 - r14 * e) / m ^ 2 := by rw [h16]
        _ = r15 / m * (q5 / m) - r14 / m * (e / m) := by ring)
    (by
      calc
        c / m * (r25 / m) = (c * r25) / m ^ 2 := by ring
        _ = (q3 * q4 - b * d) / m ^ 2 := by rw [h25]
        _ = q3 / m * (q4 / m) - b / m * (d / m) := by ring)
    (by
      calc
        d / m * (r26 / m) = (d * r26) / m ^ 2 := by ring
        _ = (r25 * q5 - q3 * e) / m ^ 2 := by rw [h26]
        _ = r25 / m * (q5 / m) - q3 / m * (e / m) := by ring)
    (by
      calc
        d / m * (r36 / m) = (d * r36) / m ^ 2 := by ring
        _ = (q4 * q5 - c * e) / m ^ 2 := by rw [h36]
        _ = q4 / m * (q5 / m) - c / m * (e / m) := by ring)
  have hscaled := mul_lt_mul_of_pos_right hn hm
  calc
    9 * m < (a / m + b / m + c / m + d / m + e / m) * m := hscaled
    _ = a + b + c + d + e := by
      field_simp [hm.ne']
      <;> ring

end HeilbronnChallenge.N7Upper
