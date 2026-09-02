import Heilbronn8.HullSixL14Bound

/-!
# The scalar core of the `1 + 5` hull-six chamber

This file isolates the one-dimensional inequalities which arise after a line
through the two non-hull points separates one hull vertex from the other five.
Nothing in this file asserts that a geometric configuration supplies the data
below.  In particular, the eventual geometric adapter must supply the four
`P`-fan areas on the five-vertex block, the five negative line-level
magnitudes, the three lower-hull ear inequalities, the endpoint ordering, and
the ordered pair of lower-hull edges crossed by the rays from the isolated
vertex through `P` and `Q`.

The point of keeping that boundary explicit is that the proof below is a
small reusable real-algebra argument.  It contains no generated certificate
bank.  The main conclusion is that the scalar crossing parameter is at least
`5 / 4` whenever the four fan areas have sum below `17 / 2`.
-/

namespace Heilbronn8

set_option maxHeartbeats 1000000

/-- Scalar data attached to a `1 + 5` line split.

Let `P,Q` be the two interior points, let `U` be the isolated hull vertex,
and write `L₁,...,L₅` for the five vertices on the other side of the
oriented line `PQ`.  Then `aᵢ` are the four normalized `P`-fan areas
`[P,Lᵢ,Lᵢ₊₁]`, while `bᵢ` are the normalized positive magnitudes
`-[P,Q,Lᵢ]` of the five negative line levels.  The corresponding `Q`-fan
areas are
`cᵢ = aᵢ + bᵢ₊₁ - bᵢ`
by the base-change identity.  All these determinants have been divided by
the common lower triangle-area bound, so their floors are one.

The three `ear` fields are exactly the scalar forms of the three consecutive
lower-hull triangle floors. -/
structure HullSixOneFiveData where
  a₁ : ℝ
  a₂ : ℝ
  a₃ : ℝ
  a₄ : ℝ
  b₁ : ℝ
  b₂ : ℝ
  b₃ : ℝ
  b₄ : ℝ
  b₅ : ℝ
  ha₁ : 1 ≤ a₁
  ha₂ : 1 ≤ a₂
  ha₃ : 1 ≤ a₃
  ha₄ : 1 ≤ a₄
  hb₁ : 1 ≤ b₁
  hb₂ : 1 ≤ b₂
  hb₃ : 1 ≤ b₃
  hb₄ : 1 ≤ b₄
  hb₅ : 1 ≤ b₅
  hc₁ : (1 : ℝ) ≤ a₁ + b₂ - b₁
  hc₂ : (1 : ℝ) ≤ a₂ + b₃ - b₂
  hc₃ : (1 : ℝ) ≤ a₃ + b₄ - b₃
  hc₄ : (1 : ℝ) ≤ a₄ + b₅ - b₄
  ear₂ : b₂ ≤ a₁ * (b₂ - b₃) + a₂ * (b₂ - b₁)
  ear₃ : b₃ ≤ a₂ * (b₃ - b₄) + a₃ * (b₃ - b₂)
  ear₄ : b₄ ≤ a₃ * (b₄ - b₅) + a₄ * (b₄ - b₃)

namespace HullSixOneFiveData

def area (D : HullSixOneFiveData) : ℝ := D.a₁ + D.a₂ + D.a₃ + D.a₄

def aAt (D : HullSixOneFiveData) : Fin 4 → ℝ :=
  ![D.a₁, D.a₂, D.a₃, D.a₄]

def bAt (D : HullSixOneFiveData) : Fin 5 → ℝ :=
  ![D.b₁, D.b₂, D.b₃, D.b₄, D.b₅]

def dAt (D : HullSixOneFiveData) : Fin 4 → ℝ :=
  ![D.b₁ - D.b₂, D.b₂ - D.b₃, D.b₃ - D.b₄, D.b₄ - D.b₅]

def cAt (D : HullSixOneFiveData) : Fin 4 → ℝ :=
  ![D.a₁ + D.b₂ - D.b₁, D.a₂ + D.b₃ - D.b₂,
    D.a₃ + D.b₄ - D.b₃, D.a₄ + D.b₅ - D.b₄]

def adjacentSum (D : HullSixOneFiveData) : Fin 4 → ℝ :=
  ![D.b₁ + D.b₂, D.b₂ + D.b₃, D.b₃ + D.b₄, D.b₄ + D.b₅]

/-- The `a`-ratio on an edge is strictly larger than `4 / 5`. -/
def AHigh (D : HullSixOneFiveData) (i : Fin 4) : Prop :=
  4 * D.adjacentSum i < 5 * D.aAt i

/-- The `c`-ratio on an edge is strictly larger than `4 / 5`. -/
def CHigh (D : HullSixOneFiveData) (i : Fin 4) : Prop :=
  4 * D.adjacentSum i < 5 * D.cAt i

def DiagonalHigh (D : HullSixOneFiveData) (i : Fin 4) : Prop :=
  D.AHigh i ∧ D.CHigh i

@[simp] lemma cAt_eq_aAt_sub_dAt (D : HullSixOneFiveData) (i : Fin 4) :
    D.cAt i = D.aAt i - D.dAt i := by
  fin_cases i <;> simp [cAt, aAt, dAt] <;> ring

private lemma haAt_pos (D : HullSixOneFiveData) (i : Fin 4) :
    0 < D.aAt i := by
  fin_cases i <;> simp [aAt] <;> linarith [D.ha₁, D.ha₂, D.ha₃, D.ha₄]

private lemma hcAt_one (D : HullSixOneFiveData) (i : Fin 4) :
    1 ≤ D.cAt i := by
  fin_cases i
  · simpa [cAt] using D.hc₁
  · simpa [cAt] using D.hc₂
  · simpa [cAt] using D.hc₃
  · simpa [cAt] using D.hc₄

private lemma adjacentSum_pos (D : HullSixOneFiveData) (i : Fin 4) :
    0 < D.adjacentSum i := by
  fin_cases i <;> simp [adjacentSum] <;>
    linarith [D.hb₁, D.hb₂, D.hb₃, D.hb₄, D.hb₅]

private lemma d₁_pos_forces_d₂_pos (D : HullSixOneFiveData)
    (h : 0 < D.b₁ - D.b₂) : 0 < D.b₂ - D.b₃ := by
  by_contra hn
  have hd₂ : D.b₂ - D.b₃ ≤ 0 := le_of_not_gt hn
  have hleft : D.a₁ * (D.b₂ - D.b₃) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₁]) hd₂
  have hright : 0 < D.a₂ * (D.b₁ - D.b₂) :=
    mul_pos (by linarith [D.ha₂]) h
  nlinarith [D.ear₂, D.hb₂]

private lemma d₂_pos_forces_d₃_pos (D : HullSixOneFiveData)
    (h : 0 < D.b₂ - D.b₃) : 0 < D.b₃ - D.b₄ := by
  by_contra hn
  have hd₃ : D.b₃ - D.b₄ ≤ 0 := le_of_not_gt hn
  have hleft : D.a₂ * (D.b₃ - D.b₄) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₂]) hd₃
  have hright : 0 < D.a₃ * (D.b₂ - D.b₃) :=
    mul_pos (by linarith [D.ha₃]) h
  nlinarith [D.ear₃, D.hb₃]

private lemma d₃_pos_forces_d₄_pos (D : HullSixOneFiveData)
    (h : 0 < D.b₃ - D.b₄) : 0 < D.b₄ - D.b₅ := by
  by_contra hn
  have hd₄ : D.b₄ - D.b₅ ≤ 0 := le_of_not_gt hn
  have hleft : D.a₃ * (D.b₄ - D.b₅) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₃]) hd₄
  have hright : 0 < D.a₄ * (D.b₃ - D.b₄) :=
    mul_pos (by linarith [D.ha₄]) h
  nlinarith [D.ear₄, D.hb₄]

/-- The ear inequalities make positivity of `dᵢ = bᵢ - bᵢ₊₁`
propagate to the right.  This is the division-free content of strict
monotonicity of `dᵢ / aᵢ`. -/
theorem dAt_pos_of_le (D : HullSixOneFiveData) (k l : Fin 4)
    (hkl : k ≤ l) (hk : 0 < D.dAt k) : 0 < D.dAt l := by
  have h12 := D.d₁_pos_forces_d₂_pos
  have h23 := D.d₂_pos_forces_d₃_pos
  have h34 := D.d₃_pos_forces_d₄_pos
  have hkl_val : k.val ≤ l.val := hkl
  fin_cases k
  · have hd₁ : 0 < D.b₁ - D.b₂ := by simpa [dAt] using hk
    fin_cases l
    · simpa [dAt] using hd₁
    · simpa [dAt] using h12 hd₁
    · simpa [dAt] using h23 (h12 hd₁)
    · simpa [dAt] using h34 (h23 (h12 hd₁))
  · have hd₂ : 0 < D.b₂ - D.b₃ := by simpa [dAt] using hk
    fin_cases l
    · norm_num at hkl_val
    · simpa [dAt] using hd₂
    · simpa [dAt] using h23 hd₂
    · simpa [dAt] using h34 (h23 hd₂)
  · have hd₃ : 0 < D.b₃ - D.b₄ := by simpa [dAt] using hk
    fin_cases l
    · norm_num at hkl_val
    · norm_num at hkl_val
    · simpa [dAt] using hd₃
    · simpa [dAt] using h34 hd₃
  · have hd₄ : 0 < D.b₄ - D.b₅ := by simpa [dAt] using hk
    fin_cases l
    · norm_num at hkl_val
    · norm_num at hkl_val
    · norm_num at hkl_val
    · simpa [dAt] using hd₄

/-- Ten ordered transition pairs reduce to four shared-diagonal cases. -/
theorem transitionPair_to_diagonal (D : HullSixOneFiveData)
    (k l : Fin 4) (hkl : k ≤ l)
    (hk : D.AHigh k) (hl : D.CHigh l) :
    ∃ i : Fin 4, D.DiagonalHigh i := by
  by_cases hdk : D.dAt k ≤ 0
  · refine ⟨k, hk, ?_⟩
    rw [CHigh, D.cAt_eq_aAt_sub_dAt]
    rw [AHigh] at hk
    nlinarith
  · have hdkpos : 0 < D.dAt k := lt_of_not_ge hdk
    have hdlpos := D.dAt_pos_of_le k l hkl hdkpos
    refine ⟨l, ?_, hl⟩
    rw [AHigh]
    rw [CHigh, D.cAt_eq_aAt_sub_dAt] at hl
    nlinarith

/-! ## Small rational inequalities used by the peak cases -/

private lemma ratio_pair_ge_two {x : ℝ} (hx : 0 < x) :
    2 ≤ x + 1 / x := by
  have hnonneg : 0 ≤ (x - 1) ^ 2 / x := div_nonneg (sq_nonneg _) (le_of_lt hx)
  have hid : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
    field_simp [ne_of_gt hx] <;> ring
  linarith

private lemma six_ratio_terms_ge_six {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    6 ≤ p + 1 / p + q + 1 / q + p / q + q / p := by
  have hp' := ratio_pair_ge_two hp
  have hq' := ratio_pair_ge_two hq
  have hpq : 2 ≤ p / q + q / p := by
    have hpqpos : 0 < p / q := div_pos hp hq
    have h := ratio_pair_ge_two hpqpos
    have hid : 1 / (p / q) = q / p := by
      field_simp [ne_of_gt hp, ne_of_gt hq]
    simpa [hid] using h
  linarith

/-- If the peak occurs no later than `b₂`, the four fan areas already sum to
at least ten. -/
theorem area_ge_ten_of_d₂_nonneg (D : HullSixOneFiveData)
    (hd₂ : 0 ≤ D.b₂ - D.b₃) : 10 ≤ D.area := by
  have hd₃ : 0 < D.b₃ - D.b₄ := by
    by_contra hn
    have hle : D.b₃ - D.b₄ ≤ 0 := le_of_not_gt hn
    have h0 : D.a₂ * (D.b₃ - D.b₄) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₂]) hle
    have h1 : 0 ≤ D.a₃ * (D.b₂ - D.b₃) :=
      mul_nonneg (by linarith [D.ha₃]) hd₂
    nlinarith [D.ear₃, D.hb₃]
  have hd₄ := D.d₃_pos_forces_d₄_pos hd₃
  let p := D.b₃ - D.b₄
  let q := D.b₄ - D.b₅
  have hp : 0 < p := hd₃
  have hq : 0 < q := hd₄
  have hb₃ : 1 + p + q ≤ D.b₃ := by
    dsimp [p, q]
    linarith [D.hb₅]
  have hc₄ : 1 + q ≤ D.a₄ := by
    dsimp [q]
    linarith [D.hc₄]
  have ha₂mul : 1 + p + q ≤ D.a₂ * p := by
    dsimp [p]
    have hdrop : 0 ≤ D.a₃ * (D.b₂ - D.b₃) :=
      mul_nonneg (by linarith [D.ha₃]) hd₂
    nlinarith [D.ear₃, hb₃]
  have hu₂ : 1 / p + q / p ≤ D.a₂ - 1 := by
    rw [show 1 / p + q / p = (1 + q) / p by
      field_simp [ne_of_gt hp] <;> ring]
    exact (div_le_iff₀ hp).2 (by nlinarith [ha₂mul])
  have ha₃mul : 1 + q + p * (1 + q) ≤ D.a₃ * q := by
    dsimp [p, q] at hc₄ ⊢
    have hpa₄ : (D.b₃ - D.b₄) * (1 + (D.b₄ - D.b₅)) ≤
        (D.b₃ - D.b₄) * D.a₄ :=
      mul_le_mul_of_nonneg_left hc₄ (le_of_lt hd₃)
    nlinarith only [D.ear₄, D.hb₅, hpa₄]
  have hu₃ : 1 / q + p / q + p ≤ D.a₃ - 1 := by
    rw [show 1 / q + p / q + p = (1 + p + p * q) / q by
      field_simp [ne_of_gt hq] <;> ring]
    exact (div_le_iff₀ hq).2 (by nlinarith [ha₃mul])
  have hrat := six_ratio_terms_ge_six hp hq
  dsimp [area]
  nlinarith [D.ha₁, hu₂, hu₃, hc₄]

private lemma d₄_neg_forces_d₃_neg (D : HullSixOneFiveData)
    (hd₄ : D.b₄ - D.b₅ < 0) : D.b₃ - D.b₄ < 0 := by
  by_contra hn
  have hd₃ : 0 ≤ D.b₃ - D.b₄ := le_of_not_gt hn
  have h0 : D.a₃ * (D.b₄ - D.b₅) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₃]) (le_of_lt hd₄)
  have h1 : 0 ≤ D.a₄ * (D.b₃ - D.b₄) :=
    mul_nonneg (by linarith [D.ha₄]) hd₃
  nlinarith [D.ear₄, D.hb₄]

private lemma d₃_neg_forces_d₂_neg (D : HullSixOneFiveData)
    (hd₃ : D.b₃ - D.b₄ < 0) : D.b₂ - D.b₃ < 0 := by
  by_contra hn
  have hd₂ : 0 ≤ D.b₂ - D.b₃ := le_of_not_gt hn
  have h0 : D.a₂ * (D.b₃ - D.b₄) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₂]) (le_of_lt hd₃)
  have h1 : 0 ≤ D.a₃ * (D.b₂ - D.b₃) :=
    mul_nonneg (by linarith [D.ha₃]) hd₂
  nlinarith [D.ear₃, D.hb₃]

private lemma d₂_neg_forces_d₁_neg (D : HullSixOneFiveData)
    (hd₂ : D.b₂ - D.b₃ < 0) : D.b₁ - D.b₂ < 0 := by
  by_contra hn
  have hd₁ : 0 ≤ D.b₁ - D.b₂ := le_of_not_gt hn
  have h0 : D.a₁ * (D.b₂ - D.b₃) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₁]) (le_of_lt hd₂)
  have h1 : 0 ≤ D.a₂ * (D.b₁ - D.b₂) :=
    mul_nonneg (by linarith [D.ha₂]) hd₁
  nlinarith [D.ear₂, D.hb₂]

/-- If the peak occurs at `b₅`, the four fan areas also sum to at least ten. -/
theorem area_ge_ten_of_d₄_neg (D : HullSixOneFiveData)
    (hd₄ : D.b₄ - D.b₅ < 0) : 10 ≤ D.area := by
  have hd₃ := D.d₄_neg_forces_d₃_neg hd₄
  have hd₂ := D.d₃_neg_forces_d₂_neg hd₃
  have hd₁ := D.d₂_neg_forces_d₁_neg hd₂
  let y₁ := D.b₂ - D.b₁
  let y₂ := D.b₃ - D.b₂
  let y₃ := D.b₄ - D.b₃
  let p := y₂ / y₁
  let q := y₃ / y₁
  have hy₁ : 0 < y₁ := by dsimp [y₁]; linarith
  have hy₂ : 0 < y₂ := by dsimp [y₂]; linarith
  have hy₃ : 0 < y₃ := by dsimp [y₃]; linarith
  have hp : 0 < p := div_pos hy₂ hy₁
  have hq : 0 < q := div_pos hy₃ hy₁
  have hp_id : p * y₁ = y₂ := by
    dsimp [p]
    field_simp [ne_of_gt hy₁]
  have hq_id : q * y₁ = y₃ := by
    dsimp [q]
    field_simp [ne_of_gt hy₁]
  have ha₂ : 1 + p ≤ D.a₂ := by
    have hmul : (1 + p) * y₁ ≤ D.a₂ * y₁ := by
      dsimp [y₁, y₂] at hp_id ⊢
      nlinarith [D.ear₂, D.hb₁, D.ha₁]
    exact (mul_le_mul_iff_of_pos_right hy₁).mp hmul
  have ha₃ : 1 + q + q / p + 1 / p ≤ D.a₃ := by
    have hmul : (1 + q + q / p + 1 / p) * y₂ ≤ D.a₃ * y₂ := by
      have hratioMul : (1 + q + q / p + 1 / p) * y₂ =
          y₂ + q * y₂ + y₃ + y₁ := by
        dsimp [p, q]
        field_simp [ne_of_gt hy₁, ne_of_gt hy₂] <;> ring
      have hpqcross : p * y₃ = q * y₂ := by
        dsimp [p, q]
        field_simp [ne_of_gt hy₁] <;> ring
      have ha₂scaled : (1 + p) * y₃ ≤ D.a₂ * y₃ :=
        mul_le_mul_of_nonneg_right ha₂ (le_of_lt hy₃)
      have hb₃lower : 1 + y₁ + y₂ ≤ D.b₃ := by
        dsimp [y₁, y₂]
        linarith [D.hb₁]
      have hear : D.b₃ ≤ D.a₃ * y₂ - D.a₂ * y₃ := by
        dsimp [y₂, y₃]
        nlinarith [D.ear₃]
      rw [hratioMul]
      nlinarith [hpqcross, ha₂scaled, hb₃lower, hear]
    exact (mul_le_mul_iff_of_pos_right hy₂).mp hmul
  have ha₄ : 1 + 1 / q + p / q ≤ D.a₄ := by
    have hmul : (1 + 1 / q + p / q) * y₃ ≤ D.a₄ * y₃ := by
      have hratioMul : (1 + 1 / q + p / q) * y₃ = y₃ + y₁ + y₂ := by
        dsimp [p, q]
        field_simp [ne_of_gt hy₁, ne_of_gt hy₃] <;> ring
      have hdrop : 0 ≤ D.a₃ * (D.b₅ - D.b₄) :=
        mul_nonneg (by linarith [D.ha₃]) (by linarith [hd₄])
      have hb₄lower : 1 + y₁ + y₂ + y₃ ≤ D.b₄ := by
        dsimp [y₁, y₂, y₃]
        linarith [D.hb₁]
      rw [hratioMul]
      dsimp [y₃]
      nlinarith [D.ear₄, hdrop, hb₄lower]
    exact (mul_le_mul_iff_of_pos_right hy₃).mp hmul
  have hrat := six_ratio_terms_ge_six hp hq
  dsimp [area]
  nlinarith [D.ha₁, ha₂, ha₃, ha₄]

/-! ## The remaining noncentral peak -/

private lemma cubic_reciprocal_ge_nine_halves {v : ℝ} (hv : 0 < v) :
    9 / 2 ≤ 2 * v + 2 / v + 1 / v ^ 2 := by
  have hP : 0 ≤ 4 * v ^ 3 - 9 * v ^ 2 + 4 * v + 2 := by
    by_cases hquarter : v ≤ 1 / 4
    · have hv2 : v ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
      have hv3 : 0 ≤ v ^ 3 := pow_nonneg (le_of_lt hv) 3
      nlinarith
    · have hquarter' : 1 / 4 ≤ v := le_of_not_ge hquarter
      by_cases hthree : v ≤ 3 / 2
      · rw [show 4 * v ^ 3 - 9 * v ^ 2 + 4 * v + 2 =
            (v - 1) ^ 2 * (4 * v - 1) + (3 - 2 * v) by ring]
        exact add_nonneg
          (mul_nonneg (sq_nonneg _) (by linarith [hquarter']))
          (by linarith [hthree])
      · have hthree' : 3 / 2 ≤ v := le_of_not_ge hthree
        have hquad : 0 ≤ 4 * v ^ 2 - 3 * v - 1 / 2 := by
          rw [show 4 * v ^ 2 - 3 * v - 1 / 2 =
            (v - 3 / 2) * (4 * v + 3) + 4 by ring]
          exact add_nonneg
            (mul_nonneg (by linarith [hthree']) (by linarith [hv]))
            (by norm_num)
        rw [show 4 * v ^ 3 - 9 * v ^ 2 + 4 * v + 2 =
          (v - 3 / 2) * (4 * v ^ 2 - 3 * v - 1 / 2) + 5 / 4 by ring]
        exact add_nonneg (mul_nonneg (by linarith [hthree']) hquad) (by norm_num)
  by_contra hn
  have hneg : 2 * v + 2 / v + 1 / v ^ 2 - 9 / 2 < 0 := by linarith
  have hv2 : 0 < v ^ 2 := by nlinarith [mul_pos hv hv]
  have hmul :
      (2 * v + 2 / v + 1 / v ^ 2 - 9 / 2) * (2 * v ^ 2) < 0 :=
    mul_neg_of_neg_of_pos hneg (by positivity)
  have hid :
      (2 * v + 2 / v + 1 / v ^ 2 - 9 / 2) * (2 * v ^ 2) =
        4 * v ^ 3 - 9 * v ^ 2 + 4 * v + 2 := by
    field_simp [ne_of_gt hv] <;> ring
  rw [hid] at hmul
  linarith

private lemma yz_fraction_ge_nine_halves
    {y z : ℝ} (hy : 0 < y) (hz : 0 ≤ z) (hyz : 1 < y * z) :
    9 / 2 ≤ y + z + (y + 1) / (y * z - 1) := by
  let v := Real.sqrt (y * z - 1)
  have hv : 0 < v := Real.sqrt_pos.2 (sub_pos.2 hyz)
  have hv2 : v ^ 2 = y * z - 1 := by
    dsimp [v]
    exact Real.sq_sqrt (sub_nonneg.2 (le_of_lt hyz))
  have hv2pos : 0 < v ^ 2 := by nlinarith [mul_pos hv hv]
  have hamgm : 2 * v + 2 / v ≤ y + z + y / v ^ 2 := by
    by_contra hn
    have hneg : y + z + y / v ^ 2 - (2 * v + 2 / v) < 0 := by linarith
    have hfac : 0 < y * v ^ 2 := mul_pos hy hv2pos
    have hmul : (y + z + y / v ^ 2 - (2 * v + 2 / v)) *
        (y * v ^ 2) < 0 := mul_neg_of_neg_of_pos hneg hfac
    have hid : (y + z + y / v ^ 2 - (2 * v + 2 / v)) *
        (y * v ^ 2) = (v ^ 2 + 1) * (y - v) ^ 2 := by
      field_simp [ne_of_gt hv]
      nlinarith [hv2]
    rw [hid] at hmul
    have hrhs : 0 ≤ (v ^ 2 + 1) * (y - v) ^ 2 :=
      mul_nonneg (by nlinarith [sq_nonneg v]) (sq_nonneg _)
    linarith
  have hrec := cubic_reciprocal_ge_nine_halves hv
  have hden : y * z - 1 = v ^ 2 := by linarith [hv2]
  rw [hden]
  rw [show (y + 1) / v ^ 2 = y / v ^ 2 + 1 / v ^ 2 by ring]
  nlinarith

/-- If the peak is at `b₄`, the fan-area target `17 / 2` already follows. -/
theorem area_ge_seventeen_halves_of_peak_b₄ (D : HullSixOneFiveData)
    (hd₃ : D.b₃ - D.b₄ < 0) (hd₄ : 0 ≤ D.b₄ - D.b₅) :
    17 / 2 ≤ D.area := by
  have hd₂ := D.d₃_neg_forces_d₂_neg hd₃
  have hd₁ := D.d₂_neg_forces_d₁_neg hd₂
  let y₁ := D.b₂ - D.b₁
  let y₂ := D.b₃ - D.b₂
  let y₃ := D.b₄ - D.b₃
  let X := D.b₄ - D.b₅
  let h := D.b₁ / y₁
  let p := y₂ / y₁
  let r := y₃ / y₁
  let S₀ := 1 + h + p
  let x₀ := D.a₃
  let u₄ := D.a₄ - 1
  have hy₁ : 0 < y₁ := by dsimp [y₁]; linarith
  have hy₂ : 0 < y₂ := by dsimp [y₂]; linarith
  have hy₃ : 0 < y₃ := by dsimp [y₃]; linarith
  have hX : 0 ≤ X := by simpa [X] using hd₄
  have hh : 0 < h := div_pos (by linarith [D.hb₁]) hy₁
  have hp : 0 < p := div_pos hy₂ hy₁
  have hr : 0 < r := div_pos hy₃ hy₁
  have hS : 1 < S₀ := by dsimp [S₀]; linarith [hh, hp]
  have hx₀ : 1 ≤ x₀ := by simpa [x₀] using D.ha₃
  have hu₄ : 0 ≤ u₄ := by dsimp [u₄]; linarith [D.ha₄]
  have hXcap : X ≤ u₄ := by
    dsimp [X, u₄]
    linarith [D.hc₄]
  have hinv : 1 / y₁ ≤ h := by
    dsimp [h]
    apply (div_le_div_iff_of_pos_right hy₁).2
    linarith [D.hb₁]
  have ha₂ : S₀ ≤ D.a₂ := by
    rw [show S₀ = (y₁ + D.b₁ + y₂) / y₁ by
      dsimp [S₀, h, p]
      field_simp [ne_of_gt hy₁] <;> ring]
    apply (div_le_iff₀ hy₁).2
    dsimp [y₁, y₂]
    nlinarith [D.ear₂, D.ha₁]
  have hx₀p : S₀ * (1 + r) ≤ x₀ * p := by
    have hp_id : p * y₁ = y₂ := by
      dsimp [p]
      field_simp [ne_of_gt hy₁]
    have hr_id : r * y₁ = y₃ := by
      dsimp [r]
      field_simp [ne_of_gt hy₁]
    have hS_id : S₀ * y₁ = D.b₃ := by
      dsimp [S₀, h, p]
      field_simp [ne_of_gt hy₁]
      dsimp [y₁, y₂]
      ring
    have hscaled : S₀ * y₃ ≤ D.a₂ * y₃ :=
      mul_le_mul_of_nonneg_right ha₂ (le_of_lt hy₃)
    have hear : D.b₃ ≤ x₀ * y₂ - D.a₂ * y₃ := by
      dsimp [x₀, y₂, y₃]
      nlinarith [D.ear₃]
    apply (mul_le_mul_iff_of_pos_right hy₁).mp
    nlinarith [hp_id, hr_id, hS_id, hscaled, hear]
  have hu₄support : S₀ ≤ u₄ * (x₀ * h + r) := by
    have hXY : x₀ * X / y₁ ≤ x₀ * u₄ * h := by
      have hx₀nonneg : 0 ≤ x₀ := by linarith [hx₀]
      have h0 : x₀ * X ≤ x₀ * u₄ :=
        mul_le_mul_of_nonneg_left hXcap hx₀nonneg
      have hx₀u₄nonneg : 0 ≤ x₀ * u₄ := mul_nonneg hx₀nonneg hu₄
      have h1 : (x₀ * u₄) * (1 / y₁) ≤ (x₀ * u₄) * h :=
        mul_le_mul_of_nonneg_left hinv hx₀u₄nonneg
      calc
        x₀ * X / y₁ = (x₀ * X) * (1 / y₁) := by
          simp [div_eq_mul_inv]
        _ ≤ (x₀ * u₄) * (1 / y₁) :=
          mul_le_mul_of_nonneg_right h0 (le_of_lt (one_div_pos.mpr hy₁))
        _ ≤ (x₀ * u₄) * h := h1
    have hear : S₀ ≤ x₀ * X / y₁ + u₄ * r := by
      rw [show x₀ * X / y₁ + u₄ * r =
          (x₀ * X + u₄ * y₃) / y₁ by
        dsimp [r]
        field_simp [ne_of_gt hy₁] <;> ring]
      apply (le_div_iff₀ hy₁).2
      have hS_id : S₀ * y₁ = D.b₃ := by
        dsimp [S₀, h, p]
        field_simp [ne_of_gt hy₁]
        dsimp [y₁, y₂]
        ring
      have hear' : D.b₃ ≤ x₀ * X + u₄ * y₃ := by
        dsimp [x₀, X, u₄, y₃]
        nlinarith [D.ear₄]
      nlinarith [hS_id, hear']
    nlinarith [hear, hXY]
  let y := S₀ - 1
  let z := x₀ - 1
  have hy : 0 < y := by dsimp [y]; linarith [hS]
  have hz : 0 ≤ z := by dsimp [z]; linarith [hx₀]
  have hden : x₀ * h + r ≤ y * z - 1 := by
    dsimp [y, z]
    have hSdef : S₀ = 1 + h + p := rfl
    have hhr : 0 ≤ h * r := mul_nonneg (le_of_lt hh) (le_of_lt hr)
    have hpr : 0 ≤ p * r := mul_nonneg (le_of_lt hp) (le_of_lt hr)
    nlinarith [hx₀p]
  have hbasepos : 0 < x₀ * h + r := by
    have hx₀pos : 0 < x₀ := by linarith [hx₀]
    have := mul_pos hx₀pos hh
    linarith [hr]
  have hdenpos : 0 < y * z - 1 := lt_of_lt_of_le hbasepos hden
  have hfrac : (y + 1) / (y * z - 1) ≤ u₄ := by
    apply (div_le_iff₀ hdenpos).2
    have hmul := mul_le_mul_of_nonneg_left hden hu₄
    dsimp [y]
    nlinarith [hu₄support, hmul]
  have halg := yz_fraction_ge_nine_halves hy hz (by linarith [hdenpos])
  dsimp [y, z, S₀, x₀, u₄] at halg hfrac ha₂
  dsimp [area]
  nlinarith only [D.ha₁, ha₂, hfrac, halg]

/-! ## A compact endpoint branch using `HullSixL14Bound` -/

private lemma middle_b_lower
    {a b L M R : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hear : M ≤ a * (M - R) + b * (M - L)) :
    (a + b) / (a + b - 1) ≤ M := by
  have hab : 1 < a + b := by linarith
  have hupper : M ≤ (a + b) * (M - 1) := by
    have h0 : M - R ≤ M - 1 := by linarith
    have h1 : M - L ≤ M - 1 := by linarith
    have ha0 : 0 ≤ a := by linarith [ha]
    have hb0 : 0 ≤ b := by linarith [hb]
    have h0' : a * (M - R) ≤ a * (M - 1) :=
      mul_le_mul_of_nonneg_left h0 ha0
    have h1' : b * (M - L) ≤ b * (M - 1) :=
      mul_le_mul_of_nonneg_left h1 hb0
    nlinarith [hear, h0', h1']
  apply (div_le_iff₀ (by linarith : 0 < a + b - 1)).2
  nlinarith [hupper]

/-- The low-last-area endpoint contradiction.  This is the exact seam where
the independent `L14` supporting-plane theorem is used. -/
theorem farLeft_of_last_cap (D : HullSixOneFiveData)
    (hfar : D.AHigh 0) (hcap : D.a₄ ≤ 13 / 8) :
    17 / 2 < D.area := by
  have ha₁p : 0 < D.a₁ := by linarith [D.ha₁]
  have ha₂p : 0 < D.a₂ := by linarith [D.ha₂]
  have ha₃p : 0 < D.a₃ := by linarith [D.ha₃]
  have ha₄p : 0 < D.a₄ := by linarith [D.ha₄]
  have hb₂lo := middle_b_lower D.ha₁ D.ha₂ D.hb₁ D.hb₃ D.ear₂
  have hb₃lo := middle_b_lower D.ha₂ D.ha₃ D.hb₂ D.hb₄ D.ear₃
  have hb₄lo := middle_b_lower D.ha₃ D.ha₄ D.hb₃ D.hb₅ D.ear₄
  by_contra hn
  have hsum : D.area ≤ 17 / 2 := le_of_not_gt hn
  have hL14 := hullSix_L14_ge_nine_fourths D.a₁ D.a₂ D.a₃ D.a₄
    D.ha₁ D.ha₂ D.ha₃ D.ha₄ (by simpa [area] using hsum) hcap
  have hi₂ : hullSixPairTerm D.a₁ D.a₂ ≤
      D.b₂ / (D.a₁ * D.a₂) := by
    rw [hullSixPairTerm]
    rw [show (D.a₁ + D.a₂) / (D.a₁ * D.a₂ * (D.a₁ + D.a₂ - 1)) =
        ((D.a₁ + D.a₂) / (D.a₁ + D.a₂ - 1)) / (D.a₁ * D.a₂) by
      field_simp [ne_of_gt ha₁p, ne_of_gt ha₂p,
        ne_of_gt (show 0 < D.a₁ + D.a₂ - 1 by linarith [D.ha₁, D.ha₂])] <;> ring]
    exact (div_le_div_iff_of_pos_right (mul_pos ha₁p ha₂p)).2 hb₂lo
  have hi₃ : hullSixPairTerm D.a₂ D.a₃ ≤
      D.b₃ / (D.a₂ * D.a₃) := by
    rw [hullSixPairTerm]
    rw [show (D.a₂ + D.a₃) / (D.a₂ * D.a₃ * (D.a₂ + D.a₃ - 1)) =
        ((D.a₂ + D.a₃) / (D.a₂ + D.a₃ - 1)) / (D.a₂ * D.a₃) by
      field_simp [ne_of_gt ha₂p, ne_of_gt ha₃p,
        ne_of_gt (show 0 < D.a₂ + D.a₃ - 1 by linarith [D.ha₂, D.ha₃])] <;> ring]
    exact (div_le_div_iff_of_pos_right (mul_pos ha₂p ha₃p)).2 hb₃lo
  have hi₄ : hullSixPairTerm D.a₃ D.a₄ ≤
      D.b₄ / (D.a₃ * D.a₄) := by
    rw [hullSixPairTerm]
    rw [show (D.a₃ + D.a₄) / (D.a₃ * D.a₄ * (D.a₃ + D.a₄ - 1)) =
        ((D.a₃ + D.a₄) / (D.a₃ + D.a₄ - 1)) / (D.a₃ * D.a₄) by
      field_simp [ne_of_gt ha₃p, ne_of_gt ha₄p,
        ne_of_gt (show 0 < D.a₃ + D.a₄ - 1 by linarith [D.ha₃, D.ha₄])] <;> ring]
    exact (div_le_div_iff_of_pos_right (mul_pos ha₃p ha₄p)).2 hb₄lo
  have hinc₂ : D.b₂ / (D.a₁ * D.a₂) ≤
      (D.b₂ - D.b₃) / D.a₂ - (D.b₁ - D.b₂) / D.a₁ := by
    rw [show (D.b₂ - D.b₃) / D.a₂ - (D.b₁ - D.b₂) / D.a₁ =
        (D.a₁ * (D.b₂ - D.b₃) + D.a₂ * (D.b₂ - D.b₁)) /
          (D.a₁ * D.a₂) by
      field_simp [ne_of_gt ha₁p, ne_of_gt ha₂p] <;> ring]
    exact (div_le_div_iff_of_pos_right (mul_pos ha₁p ha₂p)).2 D.ear₂
  have hinc₃ : D.b₃ / (D.a₂ * D.a₃) ≤
      (D.b₃ - D.b₄) / D.a₃ - (D.b₂ - D.b₃) / D.a₂ := by
    rw [show (D.b₃ - D.b₄) / D.a₃ - (D.b₂ - D.b₃) / D.a₂ =
        (D.a₂ * (D.b₃ - D.b₄) + D.a₃ * (D.b₃ - D.b₂)) /
          (D.a₂ * D.a₃) by
      field_simp [ne_of_gt ha₂p, ne_of_gt ha₃p] <;> ring]
    exact (div_le_div_iff_of_pos_right (mul_pos ha₂p ha₃p)).2 D.ear₃
  have hinc₄ : D.b₄ / (D.a₃ * D.a₄) ≤
      (D.b₄ - D.b₅) / D.a₄ - (D.b₃ - D.b₄) / D.a₃ := by
    rw [show (D.b₄ - D.b₅) / D.a₄ - (D.b₃ - D.b₄) / D.a₃ =
        (D.a₃ * (D.b₄ - D.b₅) + D.a₄ * (D.b₄ - D.b₃)) /
          (D.a₃ * D.a₄) by
      field_simp [ne_of_gt ha₃p, ne_of_gt ha₄p] <;> ring]
    exact (div_le_div_iff_of_pos_right (mul_pos ha₃p ha₄p)).2 D.ear₄
  have hleft : 2 / D.a₁ - 5 / 4 < (D.b₁ - D.b₂) / D.a₁ := by
    simp [AHigh, adjacentSum, aAt] at hfar
    rw [show 2 / D.a₁ - 5 / 4 = (2 - 5 * D.a₁ / 4) / D.a₁ by
      field_simp [ne_of_gt ha₁p] <;> ring]
    exact (div_lt_div_iff_of_pos_right ha₁p).2 (by nlinarith [D.hb₁, hfar])
  have hright : (D.b₄ - D.b₅) / D.a₄ ≤ 1 - 1 / D.a₄ := by
    rw [show 1 - 1 / D.a₄ = (D.a₄ - 1) / D.a₄ by
      field_simp [ne_of_gt ha₄p] <;> ring]
    exact (div_le_div_iff_of_pos_right ha₄p).2 (by linarith [D.hc₄])
  nlinarith [hL14, hi₂, hi₃, hi₄, hinc₂, hinc₃, hinc₄, hleft, hright]

/-! ## The cap-free endpoint transfer -/

private lemma farEndpoint_R_nonneg (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    let t := x + y + z
    let B := 5 * x ^ 2 + 4 * x * y + 4 * x * z + 13 * y * z +
      4 * z ^ 2
    let L := 10 * x + 4 * y + 12 * z
    let C := 69 / 2 * x * y * z - 3 * y ^ 2 * z - 3 * y * z ^ 2
    0 ≤ 2 / 9 * t * B + 4 / 81 * t ^ 2 * L - C := by
  dsimp
  let R := 2 / 9 * (x + y + z) *
      (5 * x ^ 2 + 4 * x * y + 4 * x * z + 13 * y * z + 4 * z ^ 2) +
    4 / 81 * (x + y + z) ^ 2 * (10 * x + 4 * y + 12 * z) -
    (69 / 2 * x * y * z - 3 * y ^ 2 * z - 3 * y * z ^ 2)
  let X := 7 * x / 6
  let Y := 29 * y / 50
  let Z := 9 * z / 8
  have hid : R - 203 / 2592 * x * y * z =
      y / (4 * (86 / 27)) *
        ((2 * (86 / 27) * x - (1019 / 100) * z) ^ 2 +
          (2944493 / 21870000) * z ^ 2) +
      z / (4 * (290 / 81)) *
        ((2 * (290 / 81) * x - (248 / 25) * y) ^ 2 +
          (297256 / 4100625) * y ^ 2) +
      x / (4 * (16 / 9)) *
        ((2 * (16 / 9) * y - (99 / 20) * z) ^ 2 +
          (23071 / 291600) * z ^ 2) +
      11 / 648 * x ^ 3 + 24491 / 10125000 * y ^ 3 +
      797 / 13824 * z ^ 3 +
      (X + Y + Z) / 2 * ((X - Y) ^ 2 + (Y - Z) ^ 2 + (Z - X) ^ 2) := by
    dsimp [R, X, Y, Z]
    ring
  have hrhs : 0 ≤
      y / (4 * (86 / 27)) *
        ((2 * (86 / 27) * x - (1019 / 100) * z) ^ 2 +
          (2944493 / 21870000) * z ^ 2) +
      z / (4 * (290 / 81)) *
        ((2 * (290 / 81) * x - (248 / 25) * y) ^ 2 +
          (297256 / 4100625) * y ^ 2) +
      x / (4 * (16 / 9)) *
        ((2 * (16 / 9) * y - (99 / 20) * z) ^ 2 +
          (23071 / 291600) * z ^ 2) +
      11 / 648 * x ^ 3 + 24491 / 10125000 * y ^ 3 +
      797 / 13824 * z ^ 3 +
      (X + Y + Z) / 2 * ((X - Y) ^ 2 + (Y - Z) ^ 2 + (Z - X) ^ 2) := by
    dsimp [X, Y, Z]
    positivity
  change 0 ≤ R
  have hcx : 0 ≤ 203 / 2592 * x * y * z := by positivity
  have hcxR : 203 / 2592 * x * y * z ≤ R := by
    apply sub_nonneg.mp
    rw [hid]
    exact hrhs
  exact hcx.trans hcxR

/-- The purely polynomial half of the far-endpoint argument.  Keeping it in
its own declaration gives the transfer elimination and the SOS closure
separate heartbeat budgets. -/
private lemma farEndpoint_sum_ge_of_poly_pos
    (p q r s : ℝ)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hPpos : 0 <
      (((r - 1) * (q + r + s - 1)) * (p + q - 1) -
          p * r * (r + s - 1)) * (5 * p - 4) -
        4 * q * ((r - 1) * (q + r + s - 1)) - 4 * p * q * r) :
    17 / 2 ≤ p + q + r + s := by
  by_contra harea
  have hsum : p + q + r + s < 17 / 2 := lt_of_not_ge harea
  let x := p - 1
  let y := q - 1
  let z := r - 1
  let w := s - 1
  let tau := x + y + z + w
  let t := x + y + z
  let BB := 5 * x ^ 2 + 4 * x * y + 4 * x * z + 13 * y * z + 4 * z ^ 2
  let LL := 10 * x + 4 * y + 12 * z
  let C := 69 / 2 * x * y * z - 3 * y ^ 2 * z - 3 * y * z ^ 2
  let P :=
    (((r - 1) * (q + r + s - 1)) * (p + q - 1) -
        p * r * (r + s - 1)) * (5 * p - 4) -
      4 * q * ((r - 1) * (q + r + s - 1)) - 4 * p * q * r
  have hPpos' : 0 < P := by simpa [P] using hPpos
  have hx : 0 ≤ x := by dsimp [x]; linarith [hp1]
  have hy : 0 ≤ y := by dsimp [y]; linarith [hq1]
  have hz : 0 ≤ z := by dsimp [z]; linarith [hr1]
  have hw : 0 ≤ w := by dsimp [w]; linarith [hs1]
  have htau : tau < 9 / 2 := by
    dsimp [tau, x, y, z, w]
    linarith [hsum]
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htbound : t < 9 / 2 := by
    dsimp [t]
    dsimp [tau] at htau
    linarith only [htau, hw]
  have hBB : 0 ≤ BB := by dsimp [BB]; positivity
  have hLL : 0 ≤ LL := by dsimp [LL]; positivity
  have hR := farEndpoint_R_nonneg x y z hx hy hz
  change 0 ≤ 2 / 9 * t * BB + 4 / 81 * t ^ 2 * LL - C at hR
  have hCBL : C ≤ BB + LL := by
    have htB : 2 / 9 * t * BB ≤ BB := by
      have hfactor : 2 / 9 * t ≤ 1 := by linarith [htbound]
      have := mul_le_mul_of_nonneg_right hfactor hBB
      simpa [mul_assoc] using this
    have ht2 : t ^ 2 ≤ (9 / 2 : ℝ) ^ 2 := by
      nlinarith only [ht, htbound]
    have htL : 4 / 81 * t ^ 2 * LL ≤ LL := by
      have hfactor : 4 / 81 * t ^ 2 ≤ 1 := by nlinarith only [ht2]
      have := mul_le_mul_of_nonneg_right hfactor hLL
      simpa [mul_assoc] using this
    linarith only [hR, htB, htL]
  have hPbound : P ≤ C - BB - LL - 5 := by
    have hxyz : 0 ≤ x * y * z := by positivity
    have hlead := mul_le_mul_of_nonneg_left
      (show 5 * tau + 12 ≤ 69 / 2 by linarith [htau]) hxyz
    have hPexpand : P =
        x * y * z * (5 * tau + 12) - 3 * y * z * (y + z + w) -
        5 * x ^ 2 * w - 5 * x ^ 2 - 4 * x * y - 4 * x * z -
        6 * x * w - 13 * y * z - 4 * z ^ 2 - 4 * z * w -
        10 * x - 4 * y - 12 * z - w - 5 := by
      dsimp [P, x, y, z, w, tau]
      ring
    rw [hPexpand]
    dsimp [C, BB, LL]
    have h0 : 0 ≤ 3 * y * z * w := by positivity
    have h1 : 0 ≤ 5 * x ^ 2 * w := by positivity
    have h2 : 0 ≤ 6 * x * w := by positivity
    have h3 : 0 ≤ 4 * z * w := by positivity
    nlinarith only [hlead, h0, h1, h2, h3, hw]
  linarith only [hPpos', hPbound, hCBL]

/-- A denominator-free transfer theorem closes the complementary endpoint
branch.  It only uses the `a`-ratio at the first edge; no `c`-ratio is needed. -/
private theorem farLeft_transfer (D : HullSixOneFiveData)
    (hfar : D.AHigh 0) : 17 / 2 ≤ D.area := by
  let p := D.a₁
  let q := D.a₂
  let r := D.a₃
  let s := D.a₄
  let B₁ := D.b₁
  let B₂ := D.b₂
  let B₃ := D.b₃
  let B₄ := D.b₄
  let B₅ := D.b₅
  let M := (r - 1) * (q + r + s - 1)
  let N := M * (p + q - 1) - p * r * (r + s - 1)
  let P := N * (5 * p - 4) - 4 * q * M - 4 * p * q * r
  have hp : 0 < p := by dsimp [p]; linarith [D.ha₁]
  have hq : 0 < q := by dsimp [q]; linarith [D.ha₂]
  have hr : 0 < r := by dsimp [r]; linarith [D.ha₃]
  have hs : 0 < s := by dsimp [s]; linarith [D.ha₄]
  have hp1 : 1 ≤ p := by simpa [p] using D.ha₁
  have hq1 : 1 ≤ q := by simpa [q] using D.ha₂
  have hr1 : 1 ≤ r := by simpa [r] using D.ha₃
  have hs1 : 1 ≤ s := by simpa [s] using D.ha₄
  have hB₁ : 1 ≤ B₁ := by simpa [B₁] using D.hb₁
  have hB₂ : 1 ≤ B₂ := by simpa [B₂] using D.hb₂
  have hB₅ : 1 ≤ B₅ := by simpa [B₅] using D.hb₅
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by linarith [hr1]) (by linarith [hq1, hr1, hs1])
  have hI₂ : p * B₃ ≤ (p + q - 1) * B₂ - q * B₁ := by
    dsimp [p, q, B₁, B₂, B₃]
    nlinarith only [D.ear₂]
  have hI₃ : q * B₄ ≤ (q + r - 1) * B₃ - r * B₂ := by
    dsimp [q, r, B₂, B₃, B₄]
    nlinarith only [D.ear₃]
  have hI₄ : r * B₅ ≤ (r + s - 1) * B₄ - s * B₃ := by
    dsimp [r, s, B₃, B₄, B₅]
    nlinarith only [D.ear₄]
  have hD : 0 ≤ r + s - 1 := by linarith [hr1, hs1]
  have h43 : q * r * B₅ ≤ M * B₃ - r * (r + s - 1) * B₂ := by
    calc
      q * r * B₅ = q * (r * B₅) := by ring
      _ ≤ q * ((r + s - 1) * B₄ - s * B₃) :=
        mul_le_mul_of_nonneg_left hI₄ (le_of_lt hq)
      _ = (r + s - 1) * (q * B₄) - q * s * B₃ := by ring
      _ ≤ (r + s - 1) * ((q + r - 1) * B₃ - r * B₂) -
          q * s * B₃ :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hI₃ hD) _
      _ = M * B₃ - r * (r + s - 1) * B₂ := by
        dsimp [M]
        ring
  have helim : p * q * r * B₅ ≤ N * B₂ - q * M * B₁ := by
    calc
      p * q * r * B₅ = p * (q * r * B₅) := by ring
      _ ≤ p * (M * B₃ - r * (r + s - 1) * B₂) :=
        mul_le_mul_of_nonneg_left h43 (le_of_lt hp)
      _ = M * (p * B₃) - p * r * (r + s - 1) * B₂ := by ring
      _ ≤ M * ((p + q - 1) * B₂ - q * B₁) -
          p * r * (r + s - 1) * B₂ :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hI₂ hM) _
      _ = N * B₂ - q * M * B₁ := by
        dsimp [N]
        ring
  have hN : 0 < N := by
    by_contra hn
    have hNle : N ≤ 0 := le_of_not_gt hn
    have hNB : N * B₂ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hNle (by linarith [hB₂])
    have hqMB : 0 ≤ q * M * B₁ := by positivity
    have hpqrB : 0 < p * q * r * B₅ := by positivity
    nlinarith only [helim, hNB, hqMB, hpqrB]
  have hfar' : 4 * B₂ < 5 * p - 4 * B₁ := by
    simp [AHigh, adjacentSum, aAt] at hfar
    dsimp [p, B₁, B₂]
    linarith
  have hfarN := mul_lt_mul_of_pos_left hfar' hN
  have hB₁extra : 0 ≤ B₁ - 1 := by linarith
  have hB₅extra : 0 ≤ B₅ - 1 := by linarith
  have hPpos : 0 < P := by
    dsimp [P]
    have h0 : 0 ≤ N * (B₁ - 1) := mul_nonneg (le_of_lt hN) hB₁extra
    have h1 : 0 ≤ q * M * (B₁ - 1) := by positivity
    have h2 : 0 ≤ p * q * r * (B₅ - 1) := by positivity
    nlinarith only [helim, hfarN, h0, h1, h2]
  have hsum := farEndpoint_sum_ge_of_poly_pos p q r s hp1 hq1 hr1 hs1 (by
    simpa [P, N, M] using hPpos)
  simpa [area, p, q, r, s] using hsum

/-- The complete far-left endpoint theorem.  The small last-area branch is
dispatched by `L14`; the transfer identity closes the remaining branch. -/
theorem farLeft (D : HullSixOneFiveData) (hfar : D.AHigh 0) :
    17 / 2 ≤ D.area := by
  by_cases hcap : D.a₄ ≤ 13 / 8
  · exact le_of_lt (D.farLeft_of_last_cap hfar hcap)
  · exact D.farLeft_transfer hfar

/-! ## The central peak, fourth diagonal -/

private lemma central_rational_lower {r : ℝ} (hr : 3 < r) :
    9 / 2 < r - 7 / 5 + 9 * r / (5 * (r - 1) * (r - 3)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hr3 : 0 < r - 3 := by linarith
  have hP : 0 < 10 * r ^ 3 - 99 * r ^ 2 + 284 * r - 177 := by
    let t := r - 9 / 2
    have ht : -3 / 2 < t := by dsimp [t]; linarith
    by_cases ht0 : 0 ≤ t
    · have hform : 10 * r ^ 3 - 99 * r ^ 2 + 284 * r - 177 =
          10 * t ^ 3 + 36 * t ^ 2 + t / 2 + 15 / 2 := by
        dsimp [t]
        ring
      rw [hform]
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht0 3
      nlinarith only [ht0, ht2, ht3]
    · have htneg : t < 0 := lt_of_not_ge ht0
      have hform : 10 * r ^ 3 - 99 * r ^ 2 + 284 * r - 177 =
          t ^ 2 * (36 + 10 * t) + (t + 15) / 2 := by
        dsimp [t]
        ring
      rw [hform]
      have hcoef : 0 < 36 + 10 * t := by linarith
      have hfirst : 0 ≤ t ^ 2 * (36 + 10 * t) :=
        mul_nonneg (sq_nonneg t) (le_of_lt hcoef)
      have hsecond : 0 < (t + 15) / 2 := by linarith
      exact add_pos_of_nonneg_of_pos hfirst hsecond
  by_contra hn
  have hnonpos :
      r - 7 / 5 + 9 * r / (5 * (r - 1) * (r - 3)) - 9 / 2 ≤ 0 :=
    by linarith
  have hden : 0 < 10 * (r - 1) * (r - 3) := by positivity
  have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hden)
  have hid :
      (r - 7 / 5 + 9 * r / (5 * (r - 1) * (r - 3)) - 9 / 2) *
          (10 * (r - 1) * (r - 3)) =
        10 * r ^ 3 - 99 * r ^ 2 + 284 * r - 177 := by
    field_simp [ne_of_gt hr1, ne_of_gt hr3] <;> ring
  rw [hid] at hmul
  linarith

/-- Normalized central-peak lemma for the fourth `c`-ratio.

Here `h = 1 / b₃`; `X,Y` are the two left gaps divided by `b₃`, and
`Z,W` are the two right gaps.  The conclusion says that the excess of the
four fan areas over their unit floors is strictly greater than `9 / 2`.
The hypotheses are written in exactly the form supplied by the geometric
normalization. -/
theorem centralFourth_normalized
    (h x y z w X Y Z W : ℝ)
    (hh : 0 < h)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W)
    (hleft : X + Y ≤ 1 - h) (hright : Z + W ≤ 1 - h)
    (hear₁ : 1 ≤ (1 + y) * X - x * Y)
    (hear₂ : 1 ≤ (1 + y) * Z + (1 + z) * Y)
    (hear₃ : 1 ≤ (1 + z) * W - w * Z)
    (hratio : 4 * (2 - 2 * Z - W) < 5 * (h * (1 + w) - W)) :
    9 / 2 < x + y + z + w := by
  let p := 1 + y
  let q := 1 + z
  let r := p + q
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hxY : 0 ≤ x * Y := mul_nonneg hx hY
  have hwZ : 0 ≤ w * Z := mul_nonneg hw hZ
  have hpX : 1 ≤ p * X := by
    dsimp [p]
    linarith only [hear₁, hxY]
  have hqW : 1 ≤ q * W := by
    dsimp [q]
    linarith only [hear₃, hwZ]
  have hcrossProduct : 1 ≤ (p * W) * (q * X) := by
    have hpX0 : 0 ≤ p * X := by linarith [hpX]
    have hprod := mul_le_mul hpX hqW (by norm_num : (0 : ℝ) ≤ 1) hpX0
    nlinarith
  have hcrossSum : 2 ≤ p * W + q * X := by
    have hsnonneg : 0 ≤ p * W + q * X := by positivity
    have hsq := sq_nonneg (p * W - q * X)
    nlinarith [hcrossProduct]
  have hwidth : 3 ≤ (1 - h) * r := by
    have hZcap : Z ≤ 1 - h - W := by linarith
    have hYcap : Y ≤ 1 - h - X := by linarith
    have h0 : p * Z ≤ p * (1 - h - W) :=
      mul_le_mul_of_nonneg_left hZcap (le_of_lt hp)
    have h1 : q * Y ≤ q * (1 - h - X) :=
      mul_le_mul_of_nonneg_left hYcap (le_of_lt hq)
    dsimp [r]
    nlinarith only [h0, h1, hcrossSum, hear₂]
  have hr3 : 3 < r := by
    have hhr : 0 < h * r := mul_pos hh hrpos
    nlinarith [hwidth]
  have hD4 : 2 * h + W ≤ 2 - 2 * Z - W := by nlinarith [hright]
  have hratio' : 9 * W < h * (5 * w - 3) := by nlinarith [hratio, hD4]
  have hWlower : 1 / q ≤ W := by
    apply (div_le_iff₀ hq).2
    linarith only [hear₃, hwZ]
  have hwlower : 3 / 5 + 9 / (5 * h * q) < w := by
    have hhq : 0 < 5 * h * q := by positivity
    have h9 : 9 / q ≤ 9 * W := by
      simpa [div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left hWlower (by norm_num : (0 : ℝ) ≤ 9))
    have h9' : 9 < h * q * (5 * w - 3) := by
      have h9strict : 9 / q < h * (5 * w - 3) :=
        lt_of_le_of_lt h9 hratio'
      have h9cleared : 9 < h * (5 * w - 3) * q :=
        (div_lt_iff₀ hq).mp h9strict
      simpa [mul_assoc, mul_comm, mul_left_comm] using h9cleared
    rw [show 3 / 5 + 9 / (5 * h * q) =
        (3 * h * q + 9) / (5 * h * q) by
      field_simp [ne_of_gt hh, ne_of_gt hq] <;> ring]
    exact (div_lt_iff₀ hhq).2 (by nlinarith [h9'])
  have hrecip : r / ((r - 1) * (r - 3)) ≤ 1 / (h * q) := by
    have hr1 : 0 < r - 1 := by linarith
    have hrm : 0 < r - 3 := by linarith
    have hhbound : h * r ≤ r - 3 := by nlinarith [hwidth]
    have hqbound : q ≤ r - 1 := by dsimp [r, p]; linarith
    have h0 := mul_le_mul_of_nonneg_right hhbound (le_of_lt hq)
    have h1 := mul_le_mul_of_nonneg_right hqbound (by linarith : 0 ≤ r - 3)
    apply (div_le_div_iff₀ (mul_pos hr1 hrm) (mul_pos hh hq)).2
    nlinarith [h0, h1]
  have hbase := central_rational_lower hr3
  have hscaled := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 9 / 5)
  have hr1 : 0 < r - 1 := by linarith [hr3]
  have hrm : 0 < r - 3 := by linarith [hr3]
  have hscaled' :
      9 * r / (5 * (r - 1) * (r - 3)) ≤ 9 / (5 * h * q) := by
    calc
      9 * r / (5 * (r - 1) * (r - 3)) =
          (9 / 5) * (r / ((r - 1) * (r - 3))) := by
            field_simp [ne_of_gt hr1, ne_of_gt hrm] <;> ring
      _ ≤ (9 / 5) * (1 / (h * q)) := hscaled
      _ = 9 / (5 * h * q) := by
        field_simp [ne_of_gt hh, ne_of_gt hq] <;> ring
  have hwlower' :
      3 / 5 + 9 * r / (5 * (r - 1) * (r - 3)) < w :=
    calc
      3 / 5 + 9 * r / (5 * (r - 1) * (r - 3)) ≤
          3 / 5 + 9 / (5 * h * q) := by
            simpa [add_comm] using add_le_add_left hscaled' (3 / 5)
      _ < w := hwlower
  have hsumlower :
      r - 7 / 5 + 9 * r / (5 * (r - 1) * (r - 3)) <
        x + y + z + w := by
    dsimp [r, p, q] at hwlower' ⊢
    linarith only [hx, hwlower']
  exact lt_trans hbase hsumlower

/-- In unnormalized scalar data, a central peak and a high fourth `c`-ratio
force the fan-area target. -/
theorem centralFourth (D : HullSixOneFiveData)
    (hd₂ : D.b₂ - D.b₃ ≤ 0) (hd₃ : 0 ≤ D.b₃ - D.b₄)
    (hhigh : D.CHigh 3) : 17 / 2 < D.area := by
  have hd₁ : D.b₁ - D.b₂ < 0 := by
    by_contra hn
    have hd₁' : 0 ≤ D.b₁ - D.b₂ := le_of_not_gt hn
    have h0 : D.a₁ * (D.b₂ - D.b₃) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₁]) hd₂
    have h1 : 0 ≤ D.a₂ * (D.b₁ - D.b₂) :=
      mul_nonneg (by linarith [D.ha₂]) hd₁'
    nlinarith [D.ear₂, D.hb₂]
  have hd₄ : 0 < D.b₄ - D.b₅ := by
    by_contra hn
    have hd₄' : D.b₄ - D.b₅ ≤ 0 := le_of_not_gt hn
    have h0 : D.a₃ * (D.b₄ - D.b₅) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₃]) hd₄'
    have h1 : 0 ≤ D.a₄ * (D.b₃ - D.b₄) :=
      mul_nonneg (by linarith [D.ha₄]) hd₃
    nlinarith [D.ear₄, D.hb₄]
  let B := D.b₃
  let h := 1 / B
  let x := D.a₁ - 1
  let y := D.a₂ - 1
  let z := D.a₃ - 1
  let w := D.a₄ - 1
  let X := (D.b₂ - D.b₁) / B
  let Y := (D.b₃ - D.b₂) / B
  let Z := (D.b₃ - D.b₄) / B
  let W := (D.b₄ - D.b₅) / B
  have hB : 0 < B := by dsimp [B]; linarith [D.hb₃]
  have hh : 0 < h := one_div_pos.2 hB
  have hx : 0 ≤ x := by dsimp [x]; linarith [D.ha₁]
  have hy : 0 ≤ y := by dsimp [y]; linarith [D.ha₂]
  have hz : 0 ≤ z := by dsimp [z]; linarith [D.ha₃]
  have hw : 0 ≤ w := by dsimp [w]; linarith [D.ha₄]
  have hX : 0 ≤ X := by
    dsimp [X]
    exact div_nonneg (by linarith [hd₁]) (le_of_lt hB)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact div_nonneg (by linarith [hd₂]) (le_of_lt hB)
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    exact div_nonneg hd₃ (le_of_lt hB)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact div_nonneg (le_of_lt hd₄) (le_of_lt hB)
  have hleft : X + Y ≤ 1 - h := by
    rw [show X + Y = (D.b₃ - D.b₁) / B by
      dsimp [X, Y]
      ring]
    rw [show 1 - h = (B - 1) / B by
      dsimp [h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2 (by dsimp [B]; linarith [D.hb₁])
  have hright : Z + W ≤ 1 - h := by
    rw [show Z + W = (D.b₃ - D.b₅) / B by
      dsimp [Z, W]
      ring]
    rw [show 1 - h = (B - 1) / B by
      dsimp [h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2 (by dsimp [B]; linarith [D.hb₅])
  have hear₁ : 1 ≤ (1 + y) * X - x * Y := by
    rw [show (1 + y) * X - x * Y =
        (D.a₂ * (D.b₂ - D.b₁) - (D.a₁ - 1) * (D.b₃ - D.b₂)) / B by
      dsimp [x, y, X, Y]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    dsimp [B]
    nlinarith [D.ear₂]
  have hear₂ : 1 ≤ (1 + y) * Z + (1 + z) * Y := by
    rw [show (1 + y) * Z + (1 + z) * Y =
        (D.a₂ * (D.b₃ - D.b₄) + D.a₃ * (D.b₃ - D.b₂)) / B by
      dsimp [y, z, Y, Z]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    simpa [B] using D.ear₃
  have hear₃ : 1 ≤ (1 + z) * W - w * Z := by
    rw [show (1 + z) * W - w * Z =
        (D.a₃ * (D.b₄ - D.b₅) - (D.a₄ - 1) * (D.b₃ - D.b₄)) / B by
      dsimp [z, w, Z, W]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    dsimp [B]
    nlinarith [D.ear₄]
  have hratio : 4 * (2 - 2 * Z - W) < 5 * (h * (1 + w) - W) := by
    simp [CHigh, adjacentSum, cAt] at hhigh
    rw [show 2 - 2 * Z - W = (D.b₄ + D.b₅) / B by
      dsimp [Z, W]
      field_simp [ne_of_gt hB] <;> ring]
    rw [show h * (1 + w) - W =
        (D.a₄ + D.b₅ - D.b₄) / B by
      dsimp [h, w, W]
      field_simp [ne_of_gt hB] <;> ring]
    calc
      4 * ((D.b₄ + D.b₅) / B) = (4 * (D.b₄ + D.b₅)) / B := by ring
      _ < (5 * (D.a₄ + D.b₅ - D.b₄)) / B :=
        (div_lt_div_iff_of_pos_right hB).2 (by simpa using hhigh)
      _ = 5 * ((D.a₄ + D.b₅ - D.b₄) / B) := by ring
  have hsum := centralFourth_normalized h x y z w X Y Z W hh hx hy hz hw
    hX hY hZ hW hleft hright hear₁ hear₂ hear₃ hratio
  dsimp [x, y, z, w] at hsum
  dsimp [area]
  linarith only [hsum]

/-! The central second-diagonal certificate is deliberately exposed as a
small normalized theorem below.  It is the only bulky algebraic identity in
the one-plus-five route. -/

private lemma centralDiagTwo_P_pos {t : ℝ} (ht : 0 ≤ t) (htmax : t < 29 / 10) :
    0 < 720750 * t ^ 3 - 512275 * t ^ 2 + 69360 * t + 110592 := by
  by_cases ht04 : t ≤ 2 / 5
  · have ht2 : t ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by nlinarith
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
    nlinarith
  · let u := t - 2 / 5
    have hu : 0 ≤ u := by dsimp [u]; linarith
    rw [show 720750 * t ^ 3 - 512275 * t ^ 2 + 69360 * t + 110592 =
      720750 * u ^ 3 + 352625 * u ^ 2 + 5500 * u + 102500 by
      dsimp [u]
      ring]
    positivity

/-- Exact normalized bound for the central second `a`-ratio. -/
theorem centralSecond_normalized
    (h x y z w X Y Z W : ℝ)
    (hh : 0 < h)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W)
    (hleft : X + Y ≤ 1 - h) (hright : Z + W ≤ 1 - h)
    (hear₁ : 1 ≤ (1 + y) * X - x * Y)
    (hear₂ : 1 ≤ (1 + y) * Z + (1 + z) * Y)
    (hear₃ : 1 ≤ (1 + z) * W - w * Z)
    (hWcap : W ≤ w * h)
    (hsum : x + y + z + w ≤ 9 / 2) :
    5 * h * (1 + y) ≤ 4 * (2 - Y) := by
  let a := 1 + y
  let b := 1 + z
  let U := a * h
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hwpos : 0 < w := by
    by_contra hn
    have hwle : w ≤ 0 := le_of_not_gt hn
    have hwh : w * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hwle (le_of_lt hh)
    have hWzero : W = 0 := by nlinarith
    nlinarith [hear₃]
  have hI1 : U + (a + x) * Y ≤ y := by
    have hXcap : X ≤ 1 - h - Y := by linarith
    have hm : a * X ≤ a * (1 - h - Y) :=
      mul_le_mul_of_nonneg_left hXcap (le_of_lt ha)
    dsimp [U, a]
    nlinarith only [hear₁, hm]
  have hmidW : w * (1 - b * Y) ≤ a * w * Z := by
    have hm : w ≤ w * ((1 + y) * Z + (1 + z) * Y) :=
      by
        simpa using mul_le_mul_of_nonneg_left hear₂ (le_of_lt hwpos)
    dsimp [a, b] at hm ⊢
    nlinarith only [hm]
  have hI2 : b * U - b * (b + w) * Y ≤ a * z - b - w := by
    have hwid : a * b * (Z + W) ≤ a * b * (1 - h) :=
      mul_le_mul_of_nonneg_left hright
        (mul_nonneg (le_of_lt ha) (le_of_lt hb))
    have hm : b ≤ b * ((1 + y) * Z + (1 + z) * Y) :=
      by
        simpa using mul_le_mul_of_nonneg_left hear₂ (le_of_lt hb)
    have hl : a ≤ a * ((1 + z) * W - w * Z) :=
      by
        simpa using mul_le_mul_of_nonneg_left hear₃ (le_of_lt ha)
    dsimp [U, a, b] at hwid hm hl hmidW ⊢
    nlinarith only [hwid, hm, hl, hmidW]
  have hI3 : 1 + a / w ≤ b * U + b * Y := by
    have hlast : 1 / w ≤ b * h - Z := by
      apply (div_le_iff₀ hwpos).2
      have hbW : b * W ≤ b * (w * h) :=
        mul_le_mul_of_nonneg_left hWcap (le_of_lt hb)
      dsimp [b] at hbW ⊢
      nlinarith only [hear₃, hbW]
    have hlastA : a * (1 / w) ≤ a * (b * h - Z) :=
      mul_le_mul_of_nonneg_left hlast (le_of_lt ha)
    calc
      1 + a / w = 1 + a * (1 / w) := by ring
      _ ≤ ((1 + y) * Z + (1 + z) * Y) + a * (b * h - Z) :=
        add_le_add hear₂ hlastA
      _ = b * U + b * Y := by
        dsimp [U, a, b]
        ring
  let D := b + w + 1 + a / w - a * z
  let T := b * (b + w + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hDupper : D ≤ T * Y := by
    dsimp [D, T]
    nlinarith only [hI2, hI3]
  by_cases hylow : y ≤ 8 / 5
  · have hcoeff : 4 / 5 ≤ a + x := by dsimp [a]; linarith
    have hYmul := mul_le_mul_of_nonneg_right hcoeff hY
    dsimp [U, a] at hI1 hYmul ⊢
    nlinarith only [hI1, hYmul, hylow]
  · have hylow' : 8 / 5 < y := lt_of_not_ge hylow
    have hzpos : 0 < z := by
      by_contra hn
      have hz0 : z = 0 := le_antisymm (le_of_not_gt hn) hz
      have hwZ : 0 ≤ w * Z := mul_nonneg hw hZ
      rw [hz0] at hear₃
      nlinarith only [hear₃, hright, hwZ, hZ, hh]
    let t := y - 8 / 5
    let L := 29 / 10 - t - w
    have ht : 0 < t := by dsimp [t]; linarith
    have htmax : t < 29 / 10 := by dsimp [t]; nlinarith [hsum, hwpos, hz]
    have hL : 0 < L := by
      dsimp [L, t]
      nlinarith only [hsum, hx, hzpos]
    have hzL : z ≤ L := by dsimp [L, t]; nlinarith [hsum, hx]
    let Phi : ℝ → ℝ := fun zz =>
      w * (2 + zz + w) * (9 / 5 - t * zz) +
        (t + 9 / 5) * (t + 13 / 5) * (1 - w * zz)
    have hPhi0 : 0 < Phi 0 := by
      have hw2 : 0 < 2 + w := by linarith only [hwpos]
      have ht9 : 0 < t + 9 / 5 := by linarith only [ht]
      have ht13 : 0 < t + 13 / 5 := by linarith only [ht]
      have hfirst : 0 < w * (2 + w) * (9 / 5) := by positivity
      have hsecond : 0 < (t + 9 / 5) * (t + 13 / 5) := by positivity
      dsimp [Phi]
      nlinarith only [hfirst, hsecond]
    let Aq := 4650 * t + 2340
    let Bq := 4650 * t ^ 2 - 12045 * t - 2376
    let Cq := 500 * t ^ 2 + 2200 * t + 2340
    let Qt := Aq * w ^ 2 + Bq * w + Cq
    have hAq : 0 < Aq := by dsimp [Aq]; nlinarith
    have hPt := centralDiagTwo_P_pos (le_of_lt ht) htmax
    have hQidentity : 4 * Aq * Qt = (2 * Aq * w + Bq) ^ 2 +
        3 * (49 - 10 * t) *
          (720750 * t ^ 3 - 512275 * t ^ 2 + 69360 * t + 110592) := by
      dsimp [Aq, Bq, Cq, Qt]
      ring
    have hQt : 0 < Qt := by
      have h49 : 0 < 49 - 10 * t := by linarith [htmax]
      have hrhs : 0 < (2 * Aq * w + Bq) ^ 2 +
          3 * (49 - 10 * t) *
            (720750 * t ^ 3 - 512275 * t ^ 2 + 69360 * t + 110592) := by
        positivity
      by_contra hn
      have hQtle : Qt ≤ 0 := le_of_not_gt hn
      have hleftNonpos : 4 * Aq * Qt ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hQtle
      rw [hQidentity] at hleftNonpos
      linarith only [hrhs, hleftNonpos]
    have hPhiL : 0 < Phi L := by
      have hid : 500 * Phi L = Qt := by
        dsimp [Phi, L, Aq, Bq, Cq, Qt]
        ring
      nlinarith only [hid, hQt]
    have hinterp : L * Phi z = (L - z) * Phi 0 + z * Phi L +
        t * w * L * z * (L - z) := by
      dsimp [Phi, L]
      ring
    have hPhi : 0 < Phi z := by
      have hLz : 0 ≤ L - z := by linarith
      have hmain : 0 < (L - z) * Phi 0 + z * Phi L := by
        by_cases hz0 : z = 0
        · subst z
          simpa using mul_pos hL hPhi0
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have hzterm : 0 < z * Phi L := mul_pos hzpos hPhiL
          have hother : 0 ≤ (L - z) * Phi 0 :=
            mul_nonneg hLz (le_of_lt hPhi0)
          linarith only [hzterm, hother]
      have hextra : 0 ≤ t * w * L * z * (L - z) := by positivity
      have hLPhi : 0 < L * Phi z := by
        rw [hinterp]
        exact add_pos_of_pos_of_nonneg hmain hextra
      by_contra hn
      have hnonpos :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hL) (le_of_not_gt hn)
      exact (not_lt_of_ge hnonpos) hLPhi
    let G := (y + 1 / 5) * D - (y - 8 / 5) * T
    have hGap : w * G = Phi z := by
      dsimp [G, D, T, Phi, a, b, t]
      field_simp [ne_of_gt hwpos] <;> ring
    have hG : 0 < G := by
      have := (mul_pos_iff.mp (by rw [hGap]; exact hPhi))
      rcases this with h | h
      · exact h.2
      · linarith only [hwpos, h.1]
    have hG' : 0 < (y + 1 / 5) * D - (y - 8 / 5) * T := by
      simpa only [G] using hG
    have hDpos : 0 < D := by
      have hTterm : 0 ≤ (y - 8 / 5) * T :=
        mul_nonneg (by linarith) (le_of_lt hT)
      have hprodD : 0 < (y + 1 / 5) * D := by
        linarith only [hG', hTterm]
      rcases mul_pos_iff.mp hprodD with hpos | hneg
      · exact hpos.2
      · linarith only [hylow', hneg.1]
    have hcoef : 0 < x + y + 1 / 5 := by linarith [hx, hylow']
    have hsubDirect : (x + y + 1 / 5) * D ≤
        (x + y + 1 / 5) * (T * Y) :=
      mul_le_mul_of_nonneg_left hDupper (le_of_lt hcoef)
    have hstrong : (y - 8 / 5) * T ≤ (x + y + 1 / 5) * D := by
      have hxD : 0 ≤ x * D := mul_nonneg hx (le_of_lt hDpos)
      nlinarith only [hG', hxD]
    have htarget : U + 4 / 5 * Y ≤ 8 / 5 := by
      by_contra hn
      have hbad : 8 / 5 < U + 4 / 5 * Y := lt_of_not_ge hn
      have hI1' : U + 4 / 5 * Y ≤ y - (x + y + 1 / 5) * Y := by
        dsimp [a] at hI1
        nlinarith only [hI1]
      have htyT : (y - 8 / 5) * T ≤ (x + y + 1 / 5) * Y * T := by
        calc
          (y - 8 / 5) * T ≤ (x + y + 1 / 5) * D := hstrong
          _ ≤ (x + y + 1 / 5) * Y * T := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using hsubDirect
      have hty : y - 8 / 5 ≤ (x + y + 1 / 5) * Y := by
        exact (mul_le_mul_iff_of_pos_right hT).mp
          (by simpa [mul_assoc] using htyT)
      linarith only [hbad, hI1', hty]
    dsimp [U, a] at htarget ⊢
    nlinarith only [htarget]

/-- The normalized second-diagonal result applied to scalar data. -/
theorem centralSecond_not_AHigh (D : HullSixOneFiveData)
    (hd₂ : D.b₂ - D.b₃ ≤ 0) (hd₃ : 0 ≤ D.b₃ - D.b₄)
    (harea : D.area ≤ 17 / 2) : ¬ D.AHigh 1 := by
  intro hhigh
  have hd₁ : D.b₁ - D.b₂ < 0 := by
    by_contra hn
    have hd₁' : 0 ≤ D.b₁ - D.b₂ := le_of_not_gt hn
    have h0 : D.a₁ * (D.b₂ - D.b₃) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₁]) hd₂
    have h1 : 0 ≤ D.a₂ * (D.b₁ - D.b₂) :=
      mul_nonneg (by linarith [D.ha₂]) hd₁'
    nlinarith [D.ear₂, D.hb₂]
  have hd₄ : 0 < D.b₄ - D.b₅ := by
    by_contra hn
    have hd₄' : D.b₄ - D.b₅ ≤ 0 := le_of_not_gt hn
    have h0 : D.a₃ * (D.b₄ - D.b₅) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₃]) hd₄'
    have h1 : 0 ≤ D.a₄ * (D.b₃ - D.b₄) :=
      mul_nonneg (by linarith [D.ha₄]) hd₃
    nlinarith [D.ear₄, D.hb₄]
  let B := D.b₃
  let h := 1 / B
  let x := D.a₁ - 1
  let y := D.a₂ - 1
  let z := D.a₃ - 1
  let w := D.a₄ - 1
  let X := (D.b₂ - D.b₁) / B
  let Y := (D.b₃ - D.b₂) / B
  let Z := (D.b₃ - D.b₄) / B
  let W := (D.b₄ - D.b₅) / B
  have hB : 0 < B := by dsimp [B]; linarith [D.hb₃]
  have hh : 0 < h := one_div_pos.2 hB
  have hx : 0 ≤ x := by dsimp [x]; linarith [D.ha₁]
  have hy : 0 ≤ y := by dsimp [y]; linarith [D.ha₂]
  have hz : 0 ≤ z := by dsimp [z]; linarith [D.ha₃]
  have hw : 0 ≤ w := by dsimp [w]; linarith [D.ha₄]
  have hX : 0 ≤ X := by
    dsimp [X]
    exact div_nonneg (by linarith [hd₁]) (le_of_lt hB)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact div_nonneg (by linarith [hd₂]) (le_of_lt hB)
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    exact div_nonneg hd₃ (le_of_lt hB)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact div_nonneg (le_of_lt hd₄) (le_of_lt hB)
  have hleft : X + Y ≤ 1 - h := by
    rw [show X + Y = (D.b₃ - D.b₁) / B by
      dsimp [X, Y]
      ring]
    rw [show 1 - h = (B - 1) / B by
      dsimp [h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2 (by dsimp [B]; linarith [D.hb₁])
  have hright : Z + W ≤ 1 - h := by
    rw [show Z + W = (D.b₃ - D.b₅) / B by
      dsimp [Z, W]
      ring]
    rw [show 1 - h = (B - 1) / B by
      dsimp [h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2 (by dsimp [B]; linarith [D.hb₅])
  have hear₁ : 1 ≤ (1 + y) * X - x * Y := by
    rw [show (1 + y) * X - x * Y =
        (D.a₂ * (D.b₂ - D.b₁) - (D.a₁ - 1) * (D.b₃ - D.b₂)) / B by
      dsimp [x, y, X, Y]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    dsimp [B]
    nlinarith [D.ear₂]
  have hear₂ : 1 ≤ (1 + y) * Z + (1 + z) * Y := by
    rw [show (1 + y) * Z + (1 + z) * Y =
        (D.a₂ * (D.b₃ - D.b₄) + D.a₃ * (D.b₃ - D.b₂)) / B by
      dsimp [y, z, Y, Z]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    simpa [B] using D.ear₃
  have hear₃ : 1 ≤ (1 + z) * W - w * Z := by
    rw [show (1 + z) * W - w * Z =
        (D.a₃ * (D.b₄ - D.b₅) - (D.a₄ - 1) * (D.b₃ - D.b₄)) / B by
      dsimp [z, w, Z, W]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    dsimp [B]
    nlinarith [D.ear₄]
  have hWcap : W ≤ w * h := by
    rw [show W = (D.b₄ - D.b₅) / B by rfl]
    rw [show w * h = (D.a₄ - 1) / B by
      dsimp [w, h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2 (by linarith [D.hc₄])
  have hsum : x + y + z + w ≤ 9 / 2 := by
    dsimp [x, y, z, w]
    dsimp [area] at harea
    linarith only [harea]
  have hbound := centralSecond_normalized h x y z w X Y Z W hh hx hy hz hw
    hX hY hZ hW hleft hright hear₁ hear₂ hear₃ hWcap hsum
  simp [AHigh, adjacentSum, aAt] at hhigh
  have hbound' : 5 * D.a₂ ≤ 4 * (D.b₂ + D.b₃) := by
    have hid0 : 5 * h * (1 + y) = (5 * D.a₂) / B := by
      dsimp [h, y]
      field_simp [ne_of_gt hB] <;> ring
    have hid1 : 4 * (2 - Y) = (4 * (D.b₂ + D.b₃)) / B := by
      have hBne : B ≠ 0 := ne_of_gt hB
      change 4 * (2 - (B - D.b₂) / B) = (4 * (D.b₂ + B)) / B
      field_simp [hBne] <;> ring
    rw [hid0, hid1] at hbound
    exact (div_le_div_iff_of_pos_right hB).mp hbound
  nlinarith

/-! ## Reversal and the complete scalar transition closure -/

/-- Reverse the lower chain and exchange the two interior base points. -/
def reverse (D : HullSixOneFiveData) : HullSixOneFiveData where
  a₁ := D.a₄ + D.b₅ - D.b₄
  a₂ := D.a₃ + D.b₄ - D.b₃
  a₃ := D.a₂ + D.b₃ - D.b₂
  a₄ := D.a₁ + D.b₂ - D.b₁
  b₁ := D.b₅
  b₂ := D.b₄
  b₃ := D.b₃
  b₄ := D.b₂
  b₅ := D.b₁
  ha₁ := D.hc₄
  ha₂ := D.hc₃
  ha₃ := D.hc₂
  ha₄ := D.hc₁
  hb₁ := D.hb₅
  hb₂ := D.hb₄
  hb₃ := D.hb₃
  hb₄ := D.hb₂
  hb₅ := D.hb₁
  hc₁ := by linarith [D.ha₄]
  hc₂ := by linarith [D.ha₃]
  hc₃ := by linarith [D.ha₂]
  hc₄ := by linarith [D.ha₁]
  ear₂ := by nlinarith [D.ear₄]
  ear₃ := by nlinarith [D.ear₃]
  ear₄ := by nlinarith [D.ear₂]

@[simp] theorem reverse_area (D : HullSixOneFiveData) :
    D.reverse.area = D.area + D.b₅ - D.b₁ := by
  simp [reverse, area]
  ring

private theorem diagonal_impossible_central
    (D : HullSixOneFiveData)
    (horder : D.b₅ ≤ D.b₁)
    (hd₂ : D.b₂ - D.b₃ ≤ 0) (hd₃ : 0 ≤ D.b₃ - D.b₄)
    (harea : D.area < 17 / 2)
    (i : Fin 4) : ¬ D.DiagonalHigh i := by
  intro hi
  fin_cases i
  · have := D.farLeft hi.1
    linarith
  · exact (D.centralSecond_not_AHigh hd₂ hd₃ (le_of_lt harea)) hi.1
  · let R := D.reverse
    have hRarea : R.area < 17 / 2 := by
      have hrev : R.area = D.area + D.b₅ - D.b₁ := by
        simpa only [R] using (reverse_area D)
      rw [hrev]
      linarith only [harea, horder]
    have hRd₂ : R.b₂ - R.b₃ ≤ 0 := by dsimp [R, reverse]; linarith
    have hRd₃ : 0 ≤ R.b₃ - R.b₄ := by dsimp [R, reverse]; linarith
    have hRA : R.AHigh 1 := by
      have hci := hi.2
      simp [CHigh, adjacentSum, cAt] at hci
      simp [AHigh, adjacentSum, aAt, R, reverse]
      linarith [hci]
    exact (R.centralSecond_not_AHigh hRd₂ hRd₃ (le_of_lt hRarea)) hRA
  · have := D.centralFourth hd₂ hd₃ hi.2
    linarith

/-- Below `17 / 2`, no shared diagonal can have both ratios above `4 / 5`.
The endpoint order is the one harmless WLOG choice required by the scalar
normalization. -/
theorem noDiagonalHigh_below (D : HullSixOneFiveData)
    (horder : D.b₅ ≤ D.b₁) (harea : D.area < 17 / 2)
    (i : Fin 4) : ¬ D.DiagonalHigh i := by
  by_cases hd₂ : 0 ≤ D.b₂ - D.b₃
  · have hten := D.area_ge_ten_of_d₂_nonneg hd₂
    intro
    linarith
  · have hd₂' : D.b₂ - D.b₃ < 0 := lt_of_not_ge hd₂
    by_cases hd₃ : 0 ≤ D.b₃ - D.b₄
    · exact D.diagonal_impossible_central horder (le_of_lt hd₂') hd₃ harea i
    · have hd₃' : D.b₃ - D.b₄ < 0 := lt_of_not_ge hd₃
      by_cases hd₄ : 0 ≤ D.b₄ - D.b₅
      · have hlarge := D.area_ge_seventeen_halves_of_peak_b₄ hd₃' hd₄
        intro
        linarith
      · have hd₄' : D.b₄ - D.b₅ < 0 := lt_of_not_ge hd₄
        have hten := D.area_ge_ten_of_d₄_neg hd₄'
        intro
        linarith

/-- The ten ordered transition pairs are all excluded below `17 / 2`. -/
theorem noOrderedHighPair_below (D : HullSixOneFiveData)
    (horder : D.b₅ ≤ D.b₁) (harea : D.area < 17 / 2)
    (k l : Fin 4) (hkl : k ≤ l) :
    ¬ (D.AHigh k ∧ D.CHigh l) := by
  rintro ⟨hk, hl⟩
  rcases D.transitionPair_to_diagonal k l hkl hk hl with ⟨i, hi⟩
  exact D.noDiagonalHigh_below horder harea i hi

/-- Final scalar crossing lemma.

The geometric adapter supplies `mₖ ≤ u aₖ` and `mₗ ≤ u cₗ` for the two
ordered lower-hull edges hit by the rays from the isolated vertex through the
two interior points.  The scalar proof then forces `u ≥ 5 / 4`. -/
theorem crossingParameter_ge_five_fourths (D : HullSixOneFiveData)
    (horder : D.b₅ ≤ D.b₁) (harea : D.area < 17 / 2)
    (k l : Fin 4) (hkl : k ≤ l)
    (u : ℝ)
    (hcrossA : D.adjacentSum k ≤ u * D.aAt k)
    (hcrossC : D.adjacentSum l ≤ u * D.cAt l) :
    5 / 4 ≤ u := by
  have hnot := D.noOrderedHighPair_below horder harea k l hkl
  by_cases hk : D.AHigh k
  · have hl : ¬ D.CHigh l := by
      intro hl
      exact hnot ⟨hk, hl⟩
    rw [CHigh] at hl
    have hcpos : 0 < D.cAt l := by linarith [D.hcAt_one l]
    have hratio : 5 * D.cAt l ≤ 4 * D.adjacentSum l := le_of_not_gt hl
    have hscaled := mul_le_mul_of_nonneg_left hcrossC (by norm_num : (0 : ℝ) ≤ 4)
    by_contra hu
    have hult : u < 5 / 4 := lt_of_not_ge hu
    have hmul : u * D.cAt l < 5 / 4 * D.cAt l :=
      mul_lt_mul_of_pos_right hult hcpos
    nlinarith
  · rw [AHigh] at hk
    have hap : 0 < D.aAt k := D.haAt_pos k
    have hratio : 5 * D.aAt k ≤ 4 * D.adjacentSum k := le_of_not_gt hk
    have hscaled := mul_le_mul_of_nonneg_left hcrossA (by norm_num : (0 : ℝ) ≤ 4)
    by_contra hu
    have hult : u < 5 / 4 := lt_of_not_ge hu
    have hmul : u * D.aAt k < 5 / 4 * D.aAt k :=
      mul_lt_mul_of_pos_right hult hap
    nlinarith

end HullSixOneFiveData

end Heilbronn8
