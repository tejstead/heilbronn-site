import Heil7.Hull6BracketRoute

/-!
# The two-consecutive-negative hull-six chamber

Write `a i = b i (i+1)` and `d i = b i (i+2)`.  This file treats the
canonical chamber in which `d 0,d 1` are negative and the other four
two-step brackets are positive.

Two pairs of Pluecker identities eliminate opposite three-step brackets.
After the four consecutive outer-triangle floors cap `d 2,...,d 5`, the
result is a pair of cubic inequalities in the six boundary-sector excesses.
Their product forces total excess strictly greater than `3m`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The canonical two-consecutive-negative chamber. -/
def H6TwoNegativeChamber (b : Fin 6 → Fin 6 → ℝ) : Prop :=
  b 0 2 < 0 ∧ b 1 3 < 0 ∧
  0 < b 2 4 ∧ 0 < b 3 5 ∧ 0 < b 4 0 ∧ 0 < b 5 1

/-- The normalized polynomial endpoint of the two-negative argument. -/
private lemma two_negative_excess_one
    {x0 x1 x2 x3 x4 x5 : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)
    (h3 :
      (1 + x3) * (1 + (1 + x5) * (1 + x1)) ≤
        (1 + x0) * x3 * (2 + x2 + x3 + x4))
    (h5 :
      (1 + x5) * (1 + (1 + x1) * (1 + x3)) ≤
        (1 + x2) * x5 * (2 + x4 + x5 + x0)) :
    3 < x0 + x1 + x2 + x3 + x4 + x5 := by
  by_contra hnot
  have hsum : x0 + x1 + x2 + x3 + x4 + x5 ≤ 3 :=
    le_of_not_gt hnot
  let p := x0 + x2
  let u := x3 + x5
  let v := x3 * x5
  let A := 2 + x2 + x3 + x4
  let B := 2 + x4 + x5 + x0
  let P := (1 + x0) * (1 + x2)
  let R := (1 + x3) * (2 + x3) * (1 + x5) * (2 + x5)
  let D := (u + 2) * (u + 4)
  let L := P * v * A * B
  let N := u * (2 + p) * (10 - p - u)
  have hp : 0 ≤ p := by
    simp only [p]
    positivity
  have hu : 0 ≤ u := by
    simp only [u]
    positivity
  have hv : 0 ≤ v := by
    simp only [v]
    positivity
  have hpu : p + u + x4 ≤ 3 := by
    simp only [p, u]
    linarith only [hsum, hx1]
  have hu3 : u ≤ 3 := by linarith only [hpu, hp, hx4]
  have hA : 0 < A := by
    simp only [A]
    positivity
  have hB : 0 < B := by
    simp only [B]
    positivity
  have hP : 0 < P := by
    simp only [P]
    positivity
  have hR : 0 < R := by
    simp only [R]
    positivity
  have hD : 0 < D := by
    simp only [D]
    positivity
  have h3weak :
      (1 + x3) * (2 + x5) ≤ (1 + x0) * x3 * A := by
    have hinside : 2 + x5 ≤ 1 + (1 + x5) * (1 + x1) := by
      have hp0 : 0 ≤ (1 + x5) * x1 := by positivity
      nlinarith only [hp0]
    calc
      (1 + x3) * (2 + x5) ≤
          (1 + x3) * (1 + (1 + x5) * (1 + x1)) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ ≤ (1 + x0) * x3 * A := by
        simpa only [A] using h3
  have h5weak :
      (1 + x5) * (2 + x3) ≤ (1 + x2) * x5 * B := by
    have hinside : 2 + x3 ≤ 1 + (1 + x1) * (1 + x3) := by
      have hp0 : 0 ≤ x1 * (1 + x3) := by positivity
      nlinarith only [hp0]
    calc
      (1 + x5) * (2 + x3) ≤
          (1 + x5) * (1 + (1 + x1) * (1 + x3)) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ ≤ (1 + x2) * x5 * B := by
        simpa only [B] using h5
  have hlower : R ≤ L := by
    have hmul := mul_le_mul h3weak h5weak (by positivity) (by positivity)
    calc
      R = ((1 + x3) * (2 + x5)) * ((1 + x5) * (2 + x3)) := by
        simp only [R]
        ring
      _ ≤ ((1 + x0) * x3 * A) * ((1 + x2) * x5 * B) := hmul
      _ = L := by
        simp only [L, P, v]
        ring
  have hPbound : 4 * P ≤ (2 + p) ^ 2 := by
    have hs := sq_nonneg (x0 - x2)
    simp only [P, p]
    nlinarith only [hs]
  have hAB0 : 4 * (A * B) ≤ (A + B) ^ 2 := by
    nlinarith only [sq_nonneg (A - B)]
  have hABsum : A + B ≤ 10 - p - u := by
    simp only [A, B, p, u]
    linarith only [hpu]
  have hT : 0 ≤ 10 - p - u := by
    linarith only [hpu, hx4]
  have hABsq : (A + B) ^ 2 ≤ (10 - p - u) ^ 2 := by
    have hmul := mul_le_mul hABsum hABsum
      (add_nonneg hA.le hB.le) hT
    simpa only [pow_two] using hmul
  have hABbound : 4 * (A * B) ≤ (10 - p - u) ^ 2 :=
    hAB0.trans hABsq
  have hfourv : 4 * v ≤ u ^ 2 := by
    simp only [u, v]
    nlinarith only [sq_nonneg (x3 - x5)]
  have hu_sq : u ^ 2 ≤ 9 := by
    have hp0 : 0 ≤ u * (3 - u) :=
      mul_nonneg hu (sub_nonneg.mpr hu3)
    nlinarith only [hp0, hu3]
  have huv4 : 4 * (u ^ 2 * v) ≤ u ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hfourv (sq_nonneg u)
    nlinarith only [hmul]
  have hu4 : u ^ 4 ≤ 9 * u ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hu_sq (sq_nonneg u)
    nlinarith only [hmul]
  have hcoarse : 9 * u ^ 2 ≤ 32 * (u + 1) * (u + 2) := by
    nlinarith only [sq_nonneg u, hu]
  have hsecond : 0 ≤ 8 * (u + 1) * (u + 2) - u ^ 2 * v := by
    nlinarith only [huv4, hu4, hcoarse]
  have hfirst : 0 ≤ u ^ 2 - 4 * v := by
    linarith only [hfourv]
  have hfactor :
      0 ≤ (u ^ 2 - 4 * v) *
        (8 * (u + 1) * (u + 2) - u ^ 2 * v) :=
    mul_nonneg hfirst hsecond
  have hsymid :
      4 * u ^ 2 * R - D ^ 2 * v =
        (u ^ 2 - 4 * v) *
          (8 * (u + 1) * (u + 2) - u ^ 2 * v) := by
    simp only [R, D, u, v]
    ring
  have hvbound : D ^ 2 * v ≤ 4 * u ^ 2 * R := by
    nlinarith only [hfactor, hsymid]
  have hPAB := mul_le_mul hPbound hABbound (by positivity) (by positivity)
  have hall := mul_le_mul hPAB hvbound (by positivity) (by positivity)
  have hcombined : 16 * D ^ 2 * L ≤ 4 * N ^ 2 * R := by
    calc
      16 * D ^ 2 * L =
          (4 * P) * (4 * (A * B)) * (D ^ 2 * v) := by
        simp only [L]
        ring
      _ ≤ (2 + p) ^ 2 * (10 - p - u) ^ 2 *
          (4 * u ^ 2 * R) := hall
      _ = 4 * N ^ 2 * R := by
        simp only [N]
        ring
  have hupper : 4 * D ^ 2 * L ≤ N ^ 2 * R := by
    have hscaled : 4 * (4 * D ^ 2 * L) ≤ 4 * (N ^ 2 * R) := by
      convert hcombined using 1 <;> ring
    have hfour : (0 : ℝ) < 4 := by norm_num
    exact le_of_mul_le_mul_left hscaled hfour
  have ht : 0 ≤ 3 - p - u := by linarith only [hpu, hx4]
  have h5p : 0 ≤ 5 - p := by linarith only [hpu, hu, hx4]
  have hfront : (2 + p) * (10 - p - u) ≤ 7 * (5 - u) := by
    have hp0 : 0 ≤ (3 - p - u) * (5 - p) := mul_nonneg ht h5p
    nlinarith only [hp0]
  have hNupper : N ≤ 7 * u * (5 - u) := by
    have hmul := mul_le_mul_of_nonneg_left hfront hu
    calc
      N = u * ((2 + p) * (10 - p - u)) := by
        simp only [N]
        ring
      _ ≤ u * (7 * (5 - u)) := hmul
      _ = 7 * u * (5 - u) := by ring
  have hquad : 7 * u * (5 - u) < 2 * D := by
    have hsos : 0 < (18 * u - 23) ^ 2 + 47 := by positivity
    have hid :
        36 * (2 * (u + 2) * (u + 4) - 7 * u * (5 - u)) =
          (18 * u - 23) ^ 2 + 47 := by ring
    simp only [D]
    nlinarith only [hsos, hid]
  have hNlt : N < 2 * D := hNupper.trans_lt hquad
  have hN : 0 ≤ N := by
    simp only [N]
    have hlast : 0 ≤ 10 - p - u := hT
    positivity
  have hdiff : 0 < 2 * D - N := sub_pos.mpr hNlt
  have hsumDN : 0 < 2 * D + N := by positivity
  have hprodDN := mul_pos hdiff hsumDN
  have hNsq : N ^ 2 < 4 * D ^ 2 := by
    nlinarith only [hprodDN]
  have hstrict : N ^ 2 * R < 4 * D ^ 2 * R :=
    mul_lt_mul_of_pos_right hNsq hR
  have hlower_scaled : 4 * D ^ 2 * R ≤ 4 * D ^ 2 * L :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  linarith only [hlower_scaled, hupper, hstrict]

/-- Homogeneous form of `two_negative_excess_one`. -/
private lemma two_negative_excess
    {m x0 x1 x2 x3 x4 x5 : ℝ} (hm : 0 < m)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5)
    (h3 :
      (m + x3) * (m ^ 2 + (m + x5) * (m + x1)) ≤
        (m + x0) * x3 * (2 * m + x2 + x3 + x4))
    (h5 :
      (m + x5) * (m ^ 2 + (m + x1) * (m + x3)) ≤
        (m + x2) * x5 * (2 * m + x4 + x5 + x0)) :
    3 * m < x0 + x1 + x2 + x3 + x4 + x5 := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hscale : 0 ≤ (1 / m) ^ 3 := by positivity
  have h3n :
      (1 + x3 / m) * (1 + (1 + x5 / m) * (1 + x1 / m)) ≤
        (1 + x0 / m) * (x3 / m) *
          (2 + x2 / m + x3 / m + x4 / m) := by
    calc
      (1 + x3 / m) * (1 + (1 + x5 / m) * (1 + x1 / m)) =
          ((m + x3) * (m ^ 2 + (m + x5) * (m + x1))) *
            (1 / m) ^ 3 := by
        field_simp [hmne]
      _ ≤ ((m + x0) * x3 * (2 * m + x2 + x3 + x4)) *
          (1 / m) ^ 3 := mul_le_mul_of_nonneg_right h3 hscale
      _ = (1 + x0 / m) * (x3 / m) *
          (2 + x2 / m + x3 / m + x4 / m) := by
        field_simp [hmne]
  have h5n :
      (1 + x5 / m) * (1 + (1 + x1 / m) * (1 + x3 / m)) ≤
        (1 + x2 / m) * (x5 / m) *
          (2 + x4 / m + x5 / m + x0 / m) := by
    calc
      (1 + x5 / m) * (1 + (1 + x1 / m) * (1 + x3 / m)) =
          ((m + x5) * (m ^ 2 + (m + x1) * (m + x3))) *
            (1 / m) ^ 3 := by
        field_simp [hmne]
      _ ≤ ((m + x2) * x5 * (2 * m + x4 + x5 + x0)) *
          (1 / m) ^ 3 := mul_le_mul_of_nonneg_right h5 hscale
      _ = (1 + x2 / m) * (x5 / m) *
          (2 + x4 / m + x5 / m + x0 / m) := by
        field_simp [hmne]
  have hnorm := two_negative_excess_one
    (div_nonneg hx0 hm.le) (div_nonneg hx1 hm.le)
    (div_nonneg hx2 hm.le) (div_nonneg hx3 hm.le)
    (div_nonneg hx4 hm.le) (div_nonneg hx5 hm.le) h3n h5n
  have hscaled := mul_lt_mul_of_pos_left hnorm hm
  calc
    3 * m = m * 3 := by ring
    _ < m * (x0 / m + x1 / m + x2 / m + x3 / m + x4 / m + x5 / m) :=
      hscaled
    _ = x0 + x1 + x2 + x3 + x4 + x5 := by
      field_simp [hmne]

/-- Scalar form after the sign and outer-floor data have been extracted. -/
private theorem two_negative_scalar
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m) (hd1 : d 1 ≤ -m)
    (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hcap2 : d 2 ≤ a 2 + a 3 - m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hcap4 : d 4 ≤ a 4 + a 5 - m)
    (hcap5 : d 5 ≤ a 5 + a 0 - m)
    (hc4 : c 4 = -c 1) (hc5 : c 5 = -c 2)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hanonneg : ∀ i, 0 ≤ a i := fun i => le_trans hm.le (ha i)
  have hd2n : 0 ≤ d 2 := le_trans hm.le hd2
  have hd3n : 0 ≤ d 3 := le_trans hm.le hd3
  have hd4n : 0 ≤ d 4 := le_trans hm.le hd4
  have hd5n : 0 ≤ d 5 := le_trans hm.le hd5
  have hD2 : 0 ≤ a 2 + a 3 - m := hd2n.trans hcap2
  have hD3 : 0 ≤ a 3 + a 4 - m := hd3n.trans hcap3
  have hD4 : 0 ≤ a 4 + a 5 - m := hd4n.trans hcap4
  have hD5 : 0 ≤ a 5 + a 0 - m := hd5n.trans hcap5
  have hcap23 :
      d 2 * d 3 ≤ (a 2 + a 3 - m) * (a 3 + a 4 - m) :=
    mul_le_mul hcap2 hcap3 hd3n hD2
  have hcap45 :
      d 4 * d 5 ≤ (a 4 + a 5 - m) * (a 5 + a 0 - m) :=
    mul_le_mul hcap4 hcap5 hd5n hD4
  have hq : m ≤ -d 0 := by linarith only [hd0]
  have hr : m ≤ -d 1 := by linarith only [hd1]
  have hqd5 : m ^ 2 ≤ (-d 0) * d 5 := by
    calc
      m ^ 2 = m * m := by ring
      _ ≤ m * d 5 := mul_le_mul_of_nonneg_left hd5 hm.le
      _ ≤ (-d 0) * d 5 := mul_le_mul_of_nonneg_right hq hd5n
  have hrd2 : m ^ 2 ≤ (-d 1) * d 2 := by
    calc
      m ^ 2 = m * m := by ring
      _ ≤ m * d 2 := mul_le_mul_of_nonneg_left hd2 hm.le
      _ ≤ (-d 1) * d 2 := mul_le_mul_of_nonneg_right hr hd2n
  have hr2 : d 2 * d 3 = a 2 * a 4 + c 2 * a 3 := by
    simpa using hrel 2
  have hr5 : d 5 * d 0 = a 5 * a 1 + c 5 * a 0 := by
    simpa using hrel 5
  have he3 : d 2 * d 3 - a 2 * a 4 = c 2 * a 3 := by
    nlinarith only [hr2]
  have he0 : c 2 * a 0 = (-d 0) * d 5 + a 5 * a 1 := by
    rw [hc5] at hr5
    nlinarith only [hr5]
  have hexact3 :
      a 0 * (d 2 * d 3 - a 2 * a 4) =
        a 3 * ((-d 0) * d 5 + a 5 * a 1) := by
    calc
      a 0 * (d 2 * d 3 - a 2 * a 4) = a 0 * (c 2 * a 3) := by
        rw [he3]
      _ = a 3 * (c 2 * a 0) := by ring
      _ = a 3 * ((-d 0) * d 5 + a 5 * a 1) := by rw [he0]
  have hraw3 :
      a 3 * (m ^ 2 + a 5 * a 1) ≤
        a 0 * ((a 2 + a 3 - m) * (a 3 + a 4 - m) - a 2 * a 4) := by
    calc
      a 3 * (m ^ 2 + a 5 * a 1) ≤
          a 3 * ((-d 0) * d 5 + a 5 * a 1) := by
        apply mul_le_mul_of_nonneg_left _ (hanonneg 3)
        exact add_le_add_left hqd5 _
      _ = a 0 * (d 2 * d 3 - a 2 * a 4) := hexact3.symm
      _ ≤ a 0 *
          ((a 2 + a 3 - m) * (a 3 + a 4 - m) - a 2 * a 4) := by
        apply mul_le_mul_of_nonneg_left _ (hanonneg 0)
        exact sub_le_sub_right hcap23 _
  have hr1 : d 1 * d 2 = a 1 * a 3 + c 1 * a 2 := by
    simpa using hrel 1
  have hr4 : d 4 * d 5 = a 4 * a 0 + c 4 * a 5 := by
    simpa using hrel 4
  have hf2 : (-c 1) * a 2 = (-d 1) * d 2 + a 1 * a 3 := by
    nlinarith only [hr1]
  have hf5 : (-c 1) * a 5 = d 4 * d 5 - a 4 * a 0 := by
    rw [hc4] at hr4
    nlinarith only [hr4]
  have hexact5 :
      a 2 * (d 4 * d 5 - a 4 * a 0) =
        a 5 * ((-d 1) * d 2 + a 1 * a 3) := by
    calc
      a 2 * (d 4 * d 5 - a 4 * a 0) = a 2 * ((-c 1) * a 5) := by
        rw [hf5]
      _ = a 5 * ((-c 1) * a 2) := by ring
      _ = a 5 * ((-d 1) * d 2 + a 1 * a 3) := by rw [hf2]
  have hraw5 :
      a 5 * (m ^ 2 + a 1 * a 3) ≤
        a 2 * ((a 4 + a 5 - m) * (a 5 + a 0 - m) - a 4 * a 0) := by
    calc
      a 5 * (m ^ 2 + a 1 * a 3) ≤
          a 5 * ((-d 1) * d 2 + a 1 * a 3) := by
        apply mul_le_mul_of_nonneg_left _ (hanonneg 5)
        exact add_le_add_left hrd2 _
      _ = a 2 * (d 4 * d 5 - a 4 * a 0) := hexact5.symm
      _ ≤ a 2 *
          ((a 4 + a 5 - m) * (a 5 + a 0 - m) - a 4 * a 0) := by
        apply mul_le_mul_of_nonneg_left _ (hanonneg 2)
        exact sub_le_sub_right hcap45 _
  have hx0 : 0 ≤ a 0 - m := sub_nonneg.mpr (ha 0)
  have hx1 : 0 ≤ a 1 - m := sub_nonneg.mpr (ha 1)
  have hx2 : 0 ≤ a 2 - m := sub_nonneg.mpr (ha 2)
  have hx3 : 0 ≤ a 3 - m := sub_nonneg.mpr (ha 3)
  have hx4 : 0 ≤ a 4 - m := sub_nonneg.mpr (ha 4)
  have hx5 : 0 ≤ a 5 - m := sub_nonneg.mpr (ha 5)
  have h3 :
      (m + (a 3 - m)) *
          (m ^ 2 + (m + (a 5 - m)) * (m + (a 1 - m))) ≤
        (m + (a 0 - m)) * (a 3 - m) *
          (2 * m + (a 2 - m) + (a 3 - m) + (a 4 - m)) := by
    convert hraw3 using 1 <;> ring
  have h5 :
      (m + (a 5 - m)) *
          (m ^ 2 + (m + (a 1 - m)) * (m + (a 3 - m))) ≤
        (m + (a 2 - m)) * (a 5 - m) *
          (2 * m + (a 4 - m) + (a 5 - m) + (a 0 - m)) := by
    convert hraw5 using 1 <;> ring
  have hexcess := two_negative_excess hm hx0 hx1 hx2 hx3 hx4 hx5 h3 h5
  nlinarith only [hexcess]

/-- Array-level form of the two-consecutive-negative chamber bound.  Its
cyclic cap hypotheses make relabeling independent of the numeric order used
by the original outer-triangle predicate. -/
theorem h6_two_negative_array_bound
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m) (hd1 : d 1 ≤ -m)
    (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hcap2 : d 2 ≤ a 2 + a 3 - m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hcap4 : d 4 ≤ a 4 + a 5 - m)
    (hcap5 : d 5 ≤ a 5 + a 0 - m)
    (hc4 : c 4 = -c 1) (hc5 : c 5 = -c 2)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  exact (two_negative_scalar m a d c hm ha hd0 hd1 hd2 hd3 hd4 hd5
    hcap2 hcap3 hcap4 hcap5 hc4 hc5 hrel).le

/-- Strict array-level form used when classifying equality in the hull-six
bound.  Thus no chamber with two consecutive negative two-step brackets can
attain the constant `9`. -/
theorem h6_two_negative_array_bound_strict
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd0 : d 0 ≤ -m) (hd1 : d 1 ≤ -m)
    (hd2 : m ≤ d 2) (hd3 : m ≤ d 3)
    (hd4 : m ≤ d 4) (hd5 : m ≤ d 5)
    (hcap2 : d 2 ≤ a 2 + a 3 - m)
    (hcap3 : d 3 ≤ a 3 + a 4 - m)
    (hcap4 : d 4 ≤ a 4 + a 5 - m)
    (hcap5 : d 5 ≤ a 5 + a 0 - m)
    (hc4 : c 4 = -c 1) (hc5 : c 5 = -c 2)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m < a 0 + a 1 + a 2 + a 3 + a 4 + a 5 :=
  two_negative_scalar m a d c hm ha hd0 hd1 hd2 hd3 hd4 hd5
    hcap2 hcap3 hcap4 hcap5 hc4 hc5 hrel

/-- The sharp hull-six bound in the canonical chamber with exactly the first
two two-step brackets negative.  In fact the proof gives a strict bound. -/
theorem h6_two_negative_chamber_bound
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (houter : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6TwoNegativeChamber b) :
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 := by
  rcases hchamber with ⟨hd0neg, hd1neg, hd2pos, hd3pos, hd4pos, hd5pos⟩
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
  have hd0 : d 0 ≤ -m := by
    have hf := hradial 0 2 (by decide)
    rw [abs_of_neg hd0neg] at hf
    change b 0 2 ≤ -m
    linarith
  have hd1 : d 1 ≤ -m := by
    have hf := hradial 1 3 (by decide)
    rw [abs_of_neg hd1neg] at hf
    change b 1 3 ≤ -m
    linarith
  have hd2 : m ≤ d 2 := by
    have hf := hradial 2 4 (by decide)
    rw [abs_of_pos hd2pos] at hf
    change m ≤ b 2 4
    exact hf
  have hd3 : m ≤ d 3 := by
    have hf := hradial 3 5 (by decide)
    rw [abs_of_pos hd3pos] at hf
    change m ≤ b 3 5
    exact hf
  have hd4 : m ≤ d 4 := by
    have hf := hradial 4 0 (by decide)
    rw [abs_of_pos hd4pos] at hf
    change m ≤ b 4 0
    exact hf
  have hd5 : m ≤ d 5 := by
    have hf := hradial 5 1 (by decide)
    rw [abs_of_pos hd5pos] at hf
    change m ≤ b 5 1
    exact hf
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
  have hc4 : c 4 = -c 1 := by
    change b 4 1 = -b 1 4
    exact hskew 4 1
  have hc5 : c 5 = -c 2 := by
    change b 5 2 = -b 2 5
    exact hskew 5 2
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
  have hstrict := two_negative_scalar m a d c hm ha hd0 hd1 hd2 hd3 hd4 hd5
    hcap2 hcap3 hcap4 hcap5 hc4 hc5 hrel
  have hbound := hstrict.le
  simpa [a] using hbound

end HeilbronnChallenge.N7Upper
