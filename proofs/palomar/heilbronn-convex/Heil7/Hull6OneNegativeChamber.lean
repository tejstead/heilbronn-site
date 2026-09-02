import Heil7.Hull6BracketRoute
import Heil7.Hull6OneNegativeScalar

/-!
# The canonical one-negative hull-six chamber

Write `a i = b i (i+1)`, `d i = b i (i+2)`, and `c i = b i (i+3)`.
This file treats the canonical chamber `d 0 < 0`, `d 1,...,d 5 > 0` in
the branch `c 1 > 0`.  The geometric input is first reduced to three
normalized polynomial inequalities (`P`, `I`, and `K`); the exact scalar
certificate in `Hull6OneNegativeScalar` then forces boundary excess at least
`3m`.

The public array theorem is deliberately independent of rotations and
reflections.  The sign dispatcher can transport an arbitrary one-negative
chamber to this canonical positive-`c 1` frame.  A bracket-level callback seam
at the end records exactly what remains for the negative-`c 1` reflection.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The canonical cyclic two-step chamber, before splitting the sign of
`b 1 4`. -/
def H6OneNegativeChamber (b : Fin 6 → Fin 6 → ℝ) : Prop :=
  b 0 2 < 0 ∧
  0 < b 1 3 ∧ 0 < b 2 4 ∧ 0 < b 3 5 ∧
  0 < b 4 0 ∧ 0 < b 5 1

/-- Homogeneous `P`, `I`, and `K` extracted from the canonical array data.

Only the first three positive ear caps are used.  The identities
`c 3 = -c 0`, `c 4 = -c 1`, and `c 5 = -c 2` are the three instances of
skew-symmetry for opposite brackets. -/
theorem h6_one_negative_PIK_homogeneous
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m)
    (hd1 : m ≤ d 1) (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hcap1 : d 1 ≤ a 1 + a 2 - m)
    (hcap2 : d 2 ≤ a 2 + a 3 - m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hc3 : c 3 = -c 0) (hc4 : c 4 = -c 1) (hc5 : c 5 = -c 2)
    (hc1 : m ≤ c 1)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    let p := a 0 - m
    let q := a 1 - m
    let r := a 2 - m
    let s := a 3 - m
    let t := a 4 - m
    m ^ 2 ≤ r * (m + q + r + s) ∧
    m * (m + s) * (2 * m + q) ≤
      (m + p) * s * (2 * m + r + s + t) ∧
    m ^ 2 * (m + s) * (m + q) +
        m * (m + t) * (2 * m ^ 2 + m * (p + r) + p * r) ≤
      (m * (p + t) + p * t) * (m + s + t) * (m + q) := by
  dsimp only
  have ha0n : 0 ≤ a 0 := le_trans hm.le (ha 0)
  have ha1n : 0 ≤ a 1 := le_trans hm.le (ha 1)
  have ha2n : 0 ≤ a 2 := le_trans hm.le (ha 2)
  have ha3n : 0 ≤ a 3 := le_trans hm.le (ha 3)
  have ha4n : 0 ≤ a 4 := le_trans hm.le (ha 4)
  have ha5n : 0 ≤ a 5 := le_trans hm.le (ha 5)
  have hd1n : 0 ≤ d 1 := le_trans hm.le hd1
  have hd2n : 0 ≤ d 2 := le_trans hm.le hd2
  have hd3n : 0 ≤ d 3 := le_trans hm.le hd3
  have hd4n : 0 ≤ d 4 := le_trans hm.le hd4
  have hd5n : 0 ≤ d 5 := le_trans hm.le hd5
  have hD1 : 0 ≤ a 1 + a 2 - m := hd1n.trans hcap1
  have hD2 : 0 ≤ a 2 + a 3 - m := hd2n.trans hcap2
  have hD3 : 0 ≤ a 3 + a 4 - m := hd3n.trans hcap3
  have hq0 : m ≤ -d 0 := by linarith only [hd0]

  have hcap12 :
      d 1 * d 2 ≤ (a 1 + a 2 - m) * (a 2 + a 3 - m) :=
    mul_le_mul hcap1 hcap2 hd2n hD1
  have hc1a2 : m * a 2 ≤ c 1 * a 2 :=
    mul_le_mul_of_nonneg_right hc1 ha2n
  have hrow1 : d 1 * d 2 = a 1 * a 3 + c 1 * a 2 := by
    simpa using hrel 1
  have hPlower :
      a 1 * a 3 + m * a 2 ≤ d 1 * d 2 := by
    calc
      a 1 * a 3 + m * a 2 ≤ a 1 * a 3 + c 1 * a 2 :=
        add_le_add_right hc1a2 (a 1 * a 3)
      _ = d 1 * d 2 := hrow1.symm
  have hP :
      m ^ 2 ≤ (a 2 - m) *
        (m + (a 1 - m) + (a 2 - m) + (a 3 - m)) := by
    nlinarith only [hPlower, hcap12]

  have hqd5 : m ^ 2 ≤ (-d 0) * d 5 := by
    calc
      m ^ 2 = m * m := by ring
      _ ≤ m * d 5 := mul_le_mul_of_nonneg_left hd5 hm.le
      _ ≤ (-d 0) * d 5 := mul_le_mul_of_nonneg_right hq0 hd5n
  have ha5a1 : m * a 1 ≤ a 5 * a 1 :=
    mul_le_mul_of_nonneg_right (ha 5) ha1n
  have hrow5 : d 5 * d 0 = a 5 * a 1 + c 5 * a 0 := by
    simpa using hrel 5
  have heF : c 2 * a 0 = a 5 * a 1 + (-d 0) * d 5 := by
    rw [hc5] at hrow5
    nlinarith only [hrow5]
  have hFa0 : m * (a 1 + m) ≤ c 2 * a 0 := by
    rw [heF]
    nlinarith only [ha5a1, hqd5]
  have hcap23 :
      d 2 * d 3 ≤ (a 2 + a 3 - m) * (a 3 + a 4 - m) :=
    mul_le_mul hcap2 hcap3 hd3n hD2
  have hrow2 : d 2 * d 3 = a 2 * a 4 + c 2 * a 3 := by
    simpa using hrel 2
  have hc2a3 :
      c 2 * a 3 ≤ (a 3 - m) *
        (2 * m + (a 2 - m) + (a 3 - m) + (a 4 - m)) := by
    nlinarith only [hrow2, hcap23]
  have hFa0a3 : m * (a 1 + m) * a 3 ≤ (c 2 * a 0) * a 3 :=
    mul_le_mul_of_nonneg_right hFa0 ha3n
  have hc2a3a0 : (c 2 * a 3) * a 0 ≤
      ((a 3 - m) *
        (2 * m + (a 2 - m) + (a 3 - m) + (a 4 - m))) * a 0 :=
    mul_le_mul_of_nonneg_right hc2a3 ha0n
  have hI :
      m * (m + (a 3 - m)) * (2 * m + (a 1 - m)) ≤
        (m + (a 0 - m)) * (a 3 - m) *
          (2 * m + (a 2 - m) + (a 3 - m) + (a 4 - m)) := by
    nlinarith only [hFa0a3, hc2a3a0]

  have hc4le : c 4 ≤ -m := by linarith only [hc4, hc1]
  have hc4a5 : c 4 * a 5 ≤ (-m) * a 5 :=
    mul_le_mul_of_nonneg_right hc4le ha5n
  have hma5 : (-m) * a 5 ≤ (-m) * m :=
    mul_le_mul_of_nonpos_left (ha 5) (by linarith only [hm])
  have hrow4 : d 4 * d 5 = a 4 * a 0 + c 4 * a 5 := by
    simpa using hrel 4
  have hd45upper : d 4 * d 5 ≤ a 4 * a 0 - m ^ 2 := by
    calc
      d 4 * d 5 = a 4 * a 0 + c 4 * a 5 := hrow4
      _ ≤ a 4 * a 0 + (-m) * a 5 :=
        add_le_add_right hc4a5 (a 4 * a 0)
      _ ≤ a 4 * a 0 + (-m) * m := add_le_add_right hma5 (a 4 * a 0)
      _ = a 4 * a 0 - m ^ 2 := by ring
  have hmd4 : m * d 4 ≤ d 4 * d 5 :=
    by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd5 hd4n
  have hU : m * d 4 ≤ a 0 * a 4 - m ^ 2 := by
    calc
      m * d 4 ≤ d 4 * d 5 := hmd4
      _ ≤ a 4 * a 0 - m ^ 2 := hd45upper
      _ = a 0 * a 4 - m ^ 2 := by ring
  have hma3 : m * a 3 ≤ a 3 * a 5 := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (ha 5) ha3n
  have hrow3 : d 3 * d 4 = a 3 * a 5 + c 3 * a 4 := by
    simpa using hrel 3
  have hrow3lower : m * a 3 + c 3 * a 4 ≤ d 3 * d 4 := by
    calc
      m * a 3 + c 3 * a 4 ≤ a 3 * a 5 + c 3 * a 4 :=
        add_le_add_left hma3 (c 3 * a 4)
      _ = d 3 * d 4 := hrow3.symm
  have hcap3scaled : d 3 * (m * d 4) ≤
      (a 3 + a 4 - m) * (m * d 4) :=
    mul_le_mul_of_nonneg_right hcap3 (mul_nonneg hm.le hd4n)
  have hUscaled : (a 3 + a 4 - m) * (m * d 4) ≤
      (a 3 + a 4 - m) * (a 0 * a 4 - m ^ 2) :=
    mul_le_mul_of_nonneg_left hU hD3
  have hCupper :
      m * (m * a 3 + c 3 * a 4) ≤
        (a 3 + a 4 - m) * (a 0 * a 4 - m ^ 2) := by
    calc
      m * (m * a 3 + c 3 * a 4) ≤ m * (d 3 * d 4) :=
        mul_le_mul_of_nonneg_left hrow3lower hm.le
      _ = d 3 * (m * d 4) := by ring
      _ ≤ (a 3 + a 4 - m) * (m * d 4) := hcap3scaled
      _ ≤ (a 3 + a 4 - m) * (a 0 * a 4 - m ^ 2) := hUscaled
  have hqd1 : m ^ 2 ≤ (-d 0) * d 1 := by
    calc
      m ^ 2 = m * m := by ring
      _ ≤ m * d 1 := mul_le_mul_of_nonneg_left hd1 hm.le
      _ ≤ (-d 0) * d 1 := mul_le_mul_of_nonneg_right hq0 hd1n
  have hrow0 : d 0 * d 1 = a 0 * a 2 + c 0 * a 1 := by
    simpa using hrel 0
  have heC : c 3 * a 1 = a 0 * a 2 + (-d 0) * d 1 := by
    rw [hc3]
    nlinarith only [hrow0]
  have hCa1 : a 0 * a 2 + m ^ 2 ≤ c 3 * a 1 := by
    rw [heC]
    exact add_le_add_right hqd1 (a 0 * a 2)
  have hCa1scaled :
      (m * a 4) * (a 0 * a 2 + m ^ 2) ≤
        (m * a 4) * (c 3 * a 1) :=
    mul_le_mul_of_nonneg_left hCa1 (mul_nonneg hm.le ha4n)
  have hKraw :
      m ^ 2 * a 3 * a 1 + m * a 4 * (a 0 * a 2 + m ^ 2) ≤
        (a 0 * a 4 - m ^ 2) * (a 3 + a 4 - m) * a 1 := by
    have hmul := mul_le_mul_of_nonneg_right hCupper ha1n
    nlinarith only [hmul, hCa1scaled]
  have hK :
      m ^ 2 * (m + (a 3 - m)) * (m + (a 1 - m)) +
          m * (m + (a 4 - m)) *
            (2 * m ^ 2 + m * ((a 0 - m) + (a 2 - m)) +
              (a 0 - m) * (a 2 - m)) ≤
        (m * ((a 0 - m) + (a 4 - m)) +
            (a 0 - m) * (a 4 - m)) *
          (m + (a 3 - m) + (a 4 - m)) * (m + (a 1 - m)) := by
    nlinarith only [hKraw]
  exact ⟨hP, hI, hK⟩

/-- The canonical one-negative array bound in the positive-`c 1` frame.

The positive two-step floors make this a direct target for cyclic sign
dispatchers.  The proof uses precisely `hc1`, the first three positive ear
caps, the opposite identities, and the six consecutive Pluecker rows. -/
theorem h6_one_negative_array_bound
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
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
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
  rcases h6_one_negative_PIK_homogeneous m a d c hm ha hd0 hd1 hd2 hd3 hd4 hd5
      hcap1 hcap2 hcap3 hcopp0 hcopp1 hcopp2 hc1 hrel with
    ⟨hPh, hIh, hKh⟩
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
  have hnorm := h6OneNegativePIK hp hq hr hs ht hP hI hK
  have hscaled := mul_le_mul_of_nonneg_left hnorm hm.le
  have hfive :
      8 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 := by
    have heq :
        m * (p + q + r + s + t) =
          (a 0 - m) + (a 1 - m) + (a 2 - m) +
            (a 3 - m) + (a 4 - m) := by
      simp only [p, q, r, s, t]
      field_simp [hmne]
      <;> ring
    nlinarith only [hscaled, heq]
  nlinarith only [hfive, ha 5]

/-- The same canonical array bound in the negative-`c 1` branch.

This is the reflection `i ↦ 2-i`, already expressed at array level.  It sends
`a` to `[a1,a0,a5,a4,a3,a2]`, `d` to `[d0,d5,d4,d3,d2,d1]`, and `c` to
`[c5,c4,c3,c2,c1,c0]`.  Thus no sorted outer-triangle statement has to be
transported here. -/
theorem h6_one_negative_array_bound_neg_c1
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
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
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
  have hbound := h6_one_negative_array_bound m ar dr cr hm har
    hdr0 hdr1 hdr2 hdr3 hdr4 hdr5 hcr1
    hrcap1 hrcap2 hrcap3 hcropp0 hcropp1 hcropp2 hrrel
  dsimp [ar] at hbound
  nlinarith only [hbound]

/-- Canonical one-negative array bound without choosing the sign of `c 1`.

This is the preferred dispatcher seam: all five ear caps are available before
reflection, while the only opposite-bracket magnitude needed is the radial
floor for `c 1`. -/
theorem h6_one_negative_array_bound_any_c1
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
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  by_cases hc1n : 0 ≤ c 1
  · have hc1 : m ≤ c 1 := by simpa [abs_of_nonneg hc1n] using hc1abs
    exact h6_one_negative_array_bound m a d c hm ha hd0 hd1 hd2 hd3 hd4 hd5
      hc1 hcap1 hcap2 hcap3 hcopp0 hcopp1 hcopp2 hrel
  · have hc1lt : c 1 < 0 := lt_of_not_ge hc1n
    have hc1neg : c 1 ≤ -m := by
      rw [abs_of_neg hc1lt] at hc1abs
      linarith only [hc1abs]
    exact h6_one_negative_array_bound_neg_c1 m a d c hm ha
      hd0 hd1 hd2 hd3 hd4 hd5 hc1neg
      hcap3 hcap4 hcap5 hcopp0 hcopp1 hcopp2 hrel

/-! ## Bracket adapters -/

/-- Complete bracket-level bound for the canonical one-negative chamber.
The sign of `c 1` is split and reflected by the array theorem above. -/
theorem h6_one_negative_chamber_bound
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (houter : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6OneNegativeChamber b) :
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 := by
  rcases hchamber with ⟨hd0neg, hd1pos, hd2pos, hd3pos, hd4pos, hd5pos⟩
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have ha : ∀ i, m ≤ a i := by
    intro i
    have hf := hradial i (i + 1) (by fin_cases i <;> decide)
    rw [abs_of_pos (hedge i)] at hf
    exact hf
  have hd0 : d 0 ≤ -m := by
    have hf := hradial 0 2 (by decide)
    rw [abs_of_neg hd0neg] at hf
    change b 0 2 ≤ -m
    linarith
  have hd1 : m ≤ d 1 := by simpa [d, abs_of_pos hd1pos] using hradial 1 3 (by decide)
  have hd2 : m ≤ d 2 := by simpa [d, abs_of_pos hd2pos] using hradial 2 4 (by decide)
  have hd3 : m ≤ d 3 := by simpa [d, abs_of_pos hd3pos] using hradial 3 5 (by decide)
  have hd4 : m ≤ d 4 := by simpa [d, abs_of_pos hd4pos] using hradial 4 0 (by decide)
  have hd5 : m ≤ d 5 := by simpa [d, abs_of_pos hd5pos] using hradial 5 1 (by decide)
  have hc1abs : m ≤ |c 1| := by
    simpa [c] using hradial 1 4 (by decide)
  have hcap1 : d 1 ≤ a 1 + a 2 - m := by
    have ho := houter 1 2 3 (by decide) (by decide)
    change b 1 3 ≤ b 1 2 + b 2 3 - m
    linarith
  have hcap2 : d 2 ≤ a 2 + a 3 - m := by
    have ho := houter 2 3 4 (by decide) (by decide)
    change b 2 4 ≤ b 2 3 + b 3 4 - m
    linarith
  have hcap3 : d 3 ≤ a 3 + a 4 - m := by
    have ho := houter 3 4 5 (by decide) (by decide)
    change b 3 5 ≤ b 3 4 + b 4 5 - m
    linarith
  have hcap4 : d 4 ≤ a 4 + a 5 - m := by
    have ho := houter 0 4 5 (by decide) (by decide)
    have hs04 := hskew 0 4
    have hs05 := hskew 0 5
    change b 4 0 ≤ b 4 5 + b 5 0 - m
    linarith
  have hcap5 : d 5 ≤ a 5 + a 0 - m := by
    have ho := houter 0 1 5 (by decide) (by decide)
    have hs15 := hskew 1 5
    have hs05 := hskew 0 5
    change b 5 1 ≤ b 5 0 + b 0 1 - m
    linarith
  have hcopp0 : c 3 = -c 0 := by change b 3 0 = -b 0 3; exact hskew 3 0
  have hcopp1 : c 4 = -c 1 := by change b 4 1 = -b 1 4; exact hskew 4 1
  have hcopp2 : c 5 = -c 2 := by change b 5 2 = -b 2 5; exact hskew 5 2
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
  have hbound := h6_one_negative_array_bound_any_c1 m a d c hm ha
    hd0 hd1 hd2 hd3 hd4 hd5 hc1abs
    hcap1 hcap2 hcap3 hcap4 hcap5 hcopp0 hcopp1 hcopp2 hrel
  simpa [a] using hbound

/-- Compatibility name for callers that have already split `c 1 > 0`. -/
theorem h6_one_negative_c1_positive_bound
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (houter : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6OneNegativeChamber b)
    (_hc1pos : 0 < b 1 4) :
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 :=
  h6_one_negative_chamber_bound m b hm hskew hgp hradial houter hedge hchamber

/-- Canonical callback seam: only the reflected negative-`c 1` branch remains.
The finite dispatcher may supply that branch after transporting brackets. -/
theorem h6_one_negative_chamber_bound_of_negative_branch
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (houter : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6OneNegativeChamber b)
    (_hnegative : b 1 4 < 0 →
      9 * m ≤ b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0) :
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 := by
  exact h6_one_negative_chamber_bound m b hm hskew hgp hradial
    houter hedge hchamber

end HeilbronnChallenge.N7Upper
