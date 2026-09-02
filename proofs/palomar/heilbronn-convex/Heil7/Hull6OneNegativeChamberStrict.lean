import Heil7.Hull6OneNegativeChamber
import Heil7.Hull6OneNegativeScalarStrict

/-!
# Strictness of the one-negative hull-six chamber

The production bound only needs a weak `9m` conclusion.  Equality
classification needs the strict form recorded here.  The positive-`c 1`
branch uses the same homogeneous P/I/K extraction as the production proof;
the other branch is its array-level reflection.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- A one-negative chamber in the positive-`c 1` frame cannot attain `9m`. -/
theorem h6_one_negative_array_bound_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m)
    (hd1 : m ≤ d 1) (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hc1 : m ≤ c 1)
    (hcap1 : d 1 ≤ a 1 + a 2 - m)
    (hcap2 : d 2 ≤ a 2 + a 3 - m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hcopp0 : c 3 = -c 0) (hcopp1 : c 4 = -c 1)
    (hcopp2 : c 5 = -c 2)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  let p := (a 0 - m) / m
  let q := (a 1 - m) / m
  let r := (a 2 - m) / m
  let s := (a 3 - m) / m
  let t := (a 4 - m) / m
  have hmne : m ≠ 0 := ne_of_gt hm
  have hp : 0 ≤ p := by
    simpa [p] using div_nonneg (sub_nonneg.mpr (ha 0)) hm.le
  have hq : 0 ≤ q := by
    simpa [q] using div_nonneg (sub_nonneg.mpr (ha 1)) hm.le
  have hr : 0 ≤ r := by
    simpa [r] using div_nonneg (sub_nonneg.mpr (ha 2)) hm.le
  have hs : 0 ≤ s := by
    simpa [s] using div_nonneg (sub_nonneg.mpr (ha 3)) hm.le
  have ht : 0 ≤ t := by
    simpa [t] using div_nonneg (sub_nonneg.mpr (ha 4)) hm.le
  rcases h6_one_negative_PIK_homogeneous m a d c hm ha
      hd0 hd1 hd2 hd3 hd4 hd5 hcap1 hcap2 hcap3
      hcopp0 hcopp1 hcopp2 hc1 hrel with ⟨hPh, hIh, hKh⟩
  have hscale2 : 0 ≤ (1 / m) ^ 2 := by positivity
  have hscale3 : 0 ≤ (1 / m) ^ 3 := by positivity
  have hscale4 : 0 ≤ (1 / m) ^ 4 := by positivity
  have hPscaled := mul_le_mul_of_nonneg_right hPh hscale2
  have hIscaled := mul_le_mul_of_nonneg_right hIh hscale3
  have hKscaled := mul_le_mul_of_nonneg_right hKh hscale4
  have hP : 1 ≤ r * (1 + q + r + s) := by
    calc
      1 = m ^ 2 * (1 / m) ^ 2 := by
        field_simp [hmne]
        <;> ring
      _ ≤ ((a 2 - m) *
          (m + (a 1 - m) + (a 2 - m) + (a 3 - m))) *
          (1 / m) ^ 2 := hPscaled
      _ = r * (1 + q + r + s) := by
        simp only [p, q, r, s, t]
        field_simp [hmne]
        <;> ring
  have hI :
      (1 + s) * (2 + q) ≤
        (1 + p) * s * (2 + r + s + t) := by
    calc
      (1 + s) * (2 + q) =
          (m * (m + (a 3 - m)) * (2 * m + (a 1 - m))) *
            (1 / m) ^ 3 := by
        simp only [p, q, r, s, t]
        field_simp [hmne]
        <;> ring
      _ ≤ ((m + (a 0 - m)) * (a 3 - m) *
          (2 * m + (a 2 - m) + (a 3 - m) + (a 4 - m))) *
            (1 / m) ^ 3 := hIscaled
      _ = (1 + p) * s * (2 + r + s + t) := by
        simp only [p, q, r, s, t]
        field_simp [hmne]
        <;> ring
  have hK :
      (1 + s) * (1 + q) +
          (1 + t) * (2 + p + r + p * r) ≤
        (p + t + p * t) * (1 + s + t) * (1 + q) := by
    calc
      (1 + s) * (1 + q) +
          (1 + t) * (2 + p + r + p * r) =
        (m ^ 2 * (m + (a 3 - m)) * (m + (a 1 - m)) +
            m * (m + (a 4 - m)) *
              (2 * m ^ 2 + m * ((a 0 - m) + (a 2 - m)) +
                (a 0 - m) * (a 2 - m))) * (1 / m) ^ 4 := by
          simp only [p, q, r, s, t]
          field_simp [hmne]
          <;> ring
      _ ≤ ((m * ((a 0 - m) + (a 4 - m)) +
            (a 0 - m) * (a 4 - m)) *
          (m + (a 3 - m) + (a 4 - m)) * (m + (a 1 - m))) *
            (1 / m) ^ 4 := hKscaled
      _ = (p + t + p * t) * (1 + s + t) * (1 + q) := by
        simp only [p, q, r, s, t]
        field_simp [hmne]
        <;> ring
  have hnorm := h6OneNegativePIK_strict hp hq hr hs ht hP hI hK
  have hscaled := mul_lt_mul_of_pos_left hnorm hm
  have heq :
      m * (p + q + r + s + t) =
        (a 0 - m) + (a 1 - m) + (a 2 - m) +
          (a 3 - m) + (a 4 - m) := by
    simp only [p, q, r, s, t]
    field_simp [hmne]
    <;> ring
  nlinarith only [hscaled, heq, ha 5]

/-- Strict reflected one-negative bound in the negative-`c 1` frame. -/
theorem h6_one_negative_array_bound_neg_c1_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m)
    (hd1 : m ≤ d 1) (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hc1neg : c 1 ≤ -m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hcap4 : d 4 ≤ a 4 + a 5 - m)
    (hcap5 : d 5 ≤ a 5 + a 0 - m)
    (hcopp0 : c 3 = -c 0) (hcopp1 : c 4 = -c 1)
    (hcopp2 : c 5 = -c 2)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  let ar : Fin 6 → ℝ := ![a 1, a 0, a 5, a 4, a 3, a 2]
  let dr : Fin 6 → ℝ := ![d 0, d 5, d 4, d 3, d 2, d 1]
  let cr : Fin 6 → ℝ := ![c 5, c 4, c 3, c 2, c 1, c 0]
  have har : ∀ i, m ≤ ar i := by
    intro i
    fin_cases i
    · simpa [ar] using ha 1
    · simpa [ar] using ha 0
    · simpa [ar] using ha 5
    · simpa [ar] using ha 4
    · simpa [ar] using ha 3
    · simpa [ar] using ha 2
  have hdr0 : dr 0 ≤ -m := by simpa [dr] using hd0
  have hdr1 : m ≤ dr 1 := by simpa [dr] using hd5
  have hdr2 : m ≤ dr 2 := by simpa [dr] using hd4
  have hdr3 : m ≤ dr 3 := by simpa [dr] using hd3
  have hdr4 : m ≤ dr 4 := by simpa [dr] using hd2
  have hdr5 : m ≤ dr 5 := by simpa [dr] using hd1
  have hcr1 : m ≤ cr 1 := by
    simp [cr]
    rw [hcopp1]
    linarith only [hc1neg]
  have hrcap1 : dr 1 ≤ ar 1 + ar 2 - m := by
    simpa [dr, ar, add_comm] using hcap5
  have hrcap2 : dr 2 ≤ ar 2 + ar 3 - m := by
    simpa [dr, ar, add_comm] using hcap4
  have hrcap3 : dr 3 ≤ ar 3 + ar 4 - m := by
    simpa [dr, ar, add_comm] using hcap3
  have hcropp0 : cr 3 = -cr 0 := by
    simp [cr]
    linarith only [hcopp2]
  have hcropp1 : cr 4 = -cr 1 := by
    simp [cr]
    linarith only [hcopp1]
  have hcropp2 : cr 5 = -cr 2 := by
    simp [cr]
    linarith only [hcopp0]
  have hrrel : ∀ i : Fin 6,
      dr i * dr (i + 1) = ar i * ar (i + 2) + cr i * ar (i + 1) := by
    intro i
    fin_cases i
    · simpa [dr, ar, cr, mul_comm] using hrel 5
    · simpa [dr, ar, cr, mul_comm] using hrel 4
    · simpa [dr, ar, cr, mul_comm] using hrel 3
    · simpa [dr, ar, cr, mul_comm] using hrel 2
    · simpa [dr, ar, cr, mul_comm] using hrel 1
    · simpa [dr, ar, cr, mul_comm] using hrel 0
  have hbound := h6_one_negative_array_bound_strict m ar dr cr hm har
    hdr0 hdr1 hdr2 hdr3 hdr4 hdr5 hcr1
    hrcap1 hrcap2 hrcap3 hcropp0 hcropp1 hcropp2 hrrel
  dsimp [ar] at hbound
  nlinarith only [hbound]

/-- Strict one-negative bound without choosing the sign of `c 1`. -/
theorem h6_one_negative_array_bound_any_c1_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m)
    (hd1 : m ≤ d 1) (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hc1abs : m ≤ |c 1|)
    (hcap1 : d 1 ≤ a 1 + a 2 - m)
    (hcap2 : d 2 ≤ a 2 + a 3 - m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hcap4 : d 4 ≤ a 4 + a 5 - m)
    (hcap5 : d 5 ≤ a 5 + a 0 - m)
    (hcopp0 : c 3 = -c 0) (hcopp1 : c 4 = -c 1)
    (hcopp2 : c 5 = -c 2)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  by_cases hc1n : 0 ≤ c 1
  · have hc1 : m ≤ c 1 := by simpa [abs_of_nonneg hc1n] using hc1abs
    exact h6_one_negative_array_bound_strict m a d c hm ha
      hd0 hd1 hd2 hd3 hd4 hd5 hc1 hcap1 hcap2 hcap3
      hcopp0 hcopp1 hcopp2 hrel
  · have hc1lt : c 1 < 0 := lt_of_not_ge hc1n
    have hc1neg : c 1 ≤ -m := by
      rw [abs_of_neg hc1lt] at hc1abs
      linarith only [hc1abs]
    exact h6_one_negative_array_bound_neg_c1_strict m a d c hm ha
      hd0 hd1 hd2 hd3 hd4 hd5 hc1neg hcap3 hcap4 hcap5
      hcopp0 hcopp1 hcopp2 hrel

end HeilbronnChallenge.N7Upper
