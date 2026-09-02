import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Height-max certificate for the `q = 222/223/233` hull-six branches

This is the final scalar family in the `p = 011` q-blind chamber.  Here
`Y01` is positive, so its signed floor is an upper bound rather than one of
the lower bounds used in the other scalar modules.  The proof packages the
result as a max of two upper-chain estimates and a max of two lower-chain
estimates.

The lower-chain max is made unconditional by an explicit full-hull input:
the oriented ear `L0,L1,L2` has normalized area at least one.  This avoids
any hidden height-order assumption.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Heilbronn8

open scoped BigOperators

/-! ## Two finite weighted certificates used by the height theorem -/

/-- The nineteen-copy sum used when the auxiliary coefficient `M` is negative. -/
noncomputable def hullSixThreeThreeQ233NineteenSum
    (a b c d : ℝ) : ℝ :=
  a + a / d + b / d + c / b + d / b + 1 / b +
    d / (b * c) + d / c + 2 * d / a

noncomputable def hullSixThreeThreeQ233NineteenTerm
    (a b c d : ℝ) : Fin 9 → ℝ :=
  ![a, a / d, b / d, c / b, d / b, 1 / b,
    d / (b * c), d / c, 2 * d / a]

def hullSixThreeThreeQ233NineteenWeight : Fin 9 → ℕ :=
  ![2, 2, 5, 2, 1, 1, 1, 1, 4]

noncomputable def hullSixThreeThreeQ233NineteenConstant : ℝ :=
  1 / ((2 : ℝ) ^ 10 * (5 : ℝ) ^ 5)

theorem hullSixThreeThreeQ233_nineteenWeight_pos
    (i : Fin 9) : 0 < hullSixThreeThreeQ233NineteenWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ233NineteenWeight]

theorem hullSixThreeThreeQ233_nineteenWeight_sum :
    ∑ i, hullSixThreeThreeQ233NineteenWeight i = 19 := by
  norm_num [hullSixThreeThreeQ233NineteenWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ233_nineteenTerm_nonneg
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (i : Fin 9) :
    0 ≤ hullSixThreeThreeQ233NineteenTerm a b c d i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ233NineteenTerm] <;>
    positivity

theorem hullSixThreeThreeQ233_nineteenTerm_sum
    (a b c d : ℝ) :
    ∑ i, hullSixThreeThreeQ233NineteenTerm a b c d i =
      hullSixThreeThreeQ233NineteenSum a b c d := by
  simp [hullSixThreeThreeQ233NineteenTerm,
    hullSixThreeThreeQ233NineteenSum, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeQ233_nineteenTerm_product
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (∏ i,
        (hullSixThreeThreeQ233NineteenTerm a b c d i /
          (hullSixThreeThreeQ233NineteenWeight i : ℝ)) ^
            hullSixThreeThreeQ233NineteenWeight i) =
      hullSixThreeThreeQ233NineteenConstant := by
  simp [hullSixThreeThreeQ233NineteenTerm,
    hullSixThreeThreeQ233NineteenWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ233NineteenConstant]
  field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
  <;> ring

theorem hullSixThreeThreeQ233_nineteenConstant_pos :
    0 < hullSixThreeThreeQ233NineteenConstant := by
  unfold hullSixThreeThreeQ233NineteenConstant
  positivity

theorem hullSixThreeThreeQ233_nineteen_root_gap :
    (17 : ℝ) / 2 <
      19 * hullSixThreeThreeQ233NineteenConstant ^ ((19 : ℝ)⁻¹) := by
  have hpow :
      ((17 : ℝ) / 38) ^ 19 < hullSixThreeThreeQ233NineteenConstant := by
    norm_num [hullSixThreeThreeQ233NineteenConstant]
  have hpowRpow :
      ((17 : ℝ) / 38) ^ (19 : ℝ) <
        hullSixThreeThreeQ233NineteenConstant := by
    change ((17 : ℝ) / 38) ^ ((19 : ℕ) : ℝ) <
      hullSixThreeThreeQ233NineteenConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (17 : ℝ) / 38 <
        hullSixThreeThreeQ233NineteenConstant ^ ((19 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ233_nineteenConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeQ233_nineteen_gt
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (17 : ℝ) / 2 < hullSixThreeThreeQ233NineteenSum a b c d := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ233NineteenWeight
    (hullSixThreeThreeQ233NineteenTerm a b c d)
    hullSixThreeThreeQ233_nineteenWeight_pos
    (hullSixThreeThreeQ233_nineteenTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt hd))
  rw [hullSixThreeThreeQ233_nineteenWeight_sum,
    hullSixThreeThreeQ233_nineteenTerm_product ha hb hc hd] at hamgm
  rw [← hullSixThreeThreeQ233_nineteenTerm_sum a b c d]
  exact hullSixThreeThreeQ233_nineteen_root_gap.trans_le hamgm

/-- The ten-term, thirty-eight-copy sum used in the asymmetric endpoint. -/
noncomputable def hullSixThreeThreeQ233AsymSum
    (b x y : ℝ) : ℝ :=
  x + y + b + x / (b * y) + x ^ 2 / (b * y) + 3 / b +
    2 * x / b + y / b + 1 / (b * x) + 2 * y / (b * x)

noncomputable def hullSixThreeThreeQ233AsymTerm
    (b x y : ℝ) : Fin 10 → ℝ :=
  ![x, y, b, x / (b * y), x ^ 2 / (b * y), 3 / b,
    2 * x / b, y / b, 1 / (b * x), 2 * y / (b * x)]

def hullSixThreeThreeQ233AsymWeight : Fin 10 → ℕ :=
  ![1, 1, 18, 3, 1, 5, 1, 1, 5, 2]

noncomputable def hullSixThreeThreeQ233AsymConstant : ℝ :=
  1 / ((5 : ℝ) ^ 10 * (18 : ℝ) ^ 17)

theorem hullSixThreeThreeQ233_asymWeight_pos
    (i : Fin 10) : 0 < hullSixThreeThreeQ233AsymWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ233AsymWeight]

theorem hullSixThreeThreeQ233_asymWeight_sum :
    ∑ i, hullSixThreeThreeQ233AsymWeight i = 38 := by
  norm_num [hullSixThreeThreeQ233AsymWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ233_asymTerm_nonneg
    {b x y : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (i : Fin 10) :
    0 ≤ hullSixThreeThreeQ233AsymTerm b x y i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ233AsymTerm] <;>
    positivity

theorem hullSixThreeThreeQ233_asymTerm_sum
    (b x y : ℝ) :
    ∑ i, hullSixThreeThreeQ233AsymTerm b x y i =
      hullSixThreeThreeQ233AsymSum b x y := by
  simp [hullSixThreeThreeQ233AsymTerm, hullSixThreeThreeQ233AsymSum,
    Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeQ233_asymTerm_product
    {b x y : ℝ} (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    (∏ i,
        (hullSixThreeThreeQ233AsymTerm b x y i /
          (hullSixThreeThreeQ233AsymWeight i : ℝ)) ^
            hullSixThreeThreeQ233AsymWeight i) =
      hullSixThreeThreeQ233AsymConstant := by
  simp [hullSixThreeThreeQ233AsymTerm,
    hullSixThreeThreeQ233AsymWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ233AsymConstant]
  field_simp [hb.ne', hx.ne', hy.ne']
  <;> ring

theorem hullSixThreeThreeQ233_asymConstant_pos :
    0 < hullSixThreeThreeQ233AsymConstant := by
  unfold hullSixThreeThreeQ233AsymConstant
  positivity

theorem hullSixThreeThreeQ233_asym_root_gap :
    (13 : ℝ) / 2 <
      38 * hullSixThreeThreeQ233AsymConstant ^ ((38 : ℝ)⁻¹) := by
  have hpow :
      ((13 : ℝ) / 76) ^ 38 < hullSixThreeThreeQ233AsymConstant := by
    norm_num [hullSixThreeThreeQ233AsymConstant]
  have hpowRpow :
      ((13 : ℝ) / 76) ^ (38 : ℝ) <
        hullSixThreeThreeQ233AsymConstant := by
    change ((13 : ℝ) / 76) ^ ((38 : ℕ) : ℝ) <
      hullSixThreeThreeQ233AsymConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (13 : ℝ) / 76 <
        hullSixThreeThreeQ233AsymConstant ^ ((38 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ233_asymConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeQ233_asym_gt
    {b x y : ℝ} (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    (13 : ℝ) / 2 < hullSixThreeThreeQ233AsymSum b x y := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ233AsymWeight
    (hullSixThreeThreeQ233AsymTerm b x y)
    hullSixThreeThreeQ233_asymWeight_pos
    (hullSixThreeThreeQ233_asymTerm_nonneg
      (le_of_lt hb) (le_of_lt hx) (le_of_lt hy))
  rw [hullSixThreeThreeQ233_asymWeight_sum,
    hullSixThreeThreeQ233_asymTerm_product hb hx hy] at hamgm
  rw [← hullSixThreeThreeQ233_asymTerm_sum b x y]
  exact hullSixThreeThreeQ233_asym_root_gap.trans_le hamgm

/-! ## The nonpositive-boundary endpoint -/

noncomputable def hullSixThreeThreeQ233FourTerm
    (a b c p k : ℝ) : Fin 4 → ℝ :=
  ![b / 2, a / (2 * p * b), c / b, p * k * b / c]

def hullSixThreeThreeQ233FourWeight : Fin 4 → ℕ :=
  ![1, 1, 1, 1]

theorem hullSixThreeThreeQ233_fourWeight_pos
    (i : Fin 4) : 0 < hullSixThreeThreeQ233FourWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ233FourWeight]

theorem hullSixThreeThreeQ233_fourTerm_nonneg
    {a b c p k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hk : 0 ≤ k) (i : Fin 4) :
    0 ≤ hullSixThreeThreeQ233FourTerm a b c p k i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ233FourTerm] <;>
    positivity

theorem hullSixThreeThreeQ233_fourTerm_product
    {a b c p k : ℝ} (hb : 0 < b) (hc : 0 < c) (hp : 0 < p) :
    ∏ i, hullSixThreeThreeQ233FourTerm a b c p k i = a * k / 4 := by
  simp [hullSixThreeThreeQ233FourTerm, Fin.prod_univ_succ]
  field_simp [hb.ne', hc.ne', hp.ne']
  <;> ring

theorem hullSixThreeThreeQ233_four_gt
    {a b c p k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hp : 0 < p) (hk : 0 < k)
    (hak : (29 : ℝ) / 5 < a * k) :
    (21 : ℝ) / 5 < ∑ i, hullSixThreeThreeQ233FourTerm a b c p k i := by
  have hprod : 0 < a * k / 4 := by positivity
  have hpow : ((21 : ℝ) / 20) ^ 4 < a * k / 4 := by
    have : ((21 : ℝ) / 20) ^ 4 < (29 : ℝ) / 20 := by norm_num
    nlinarith
  have hpowRpow :
      ((21 : ℝ) / 20) ^ (4 : ℝ) < a * k / 4 := by
    change ((21 : ℝ) / 20) ^ ((4 : ℕ) : ℝ) < a * k / 4
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (21 : ℝ) / 20 < (a * k / 4) ^ ((4 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hprod) (by norm_num)]
    exact hpowRpow
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ233FourWeight
    (hullSixThreeThreeQ233FourTerm a b c p k)
    hullSixThreeThreeQ233_fourWeight_pos
    (hullSixThreeThreeQ233_fourTerm_nonneg
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt hp) (le_of_lt hk))
  have hweight : ∑ i, hullSixThreeThreeQ233FourWeight i = 4 := by
    norm_num [hullSixThreeThreeQ233FourWeight, Fin.sum_univ_succ]
  rw [hweight] at hamgm
  have hscaledProduct :
      (∏ i,
          (hullSixThreeThreeQ233FourTerm a b c p k i /
            (hullSixThreeThreeQ233FourWeight i : ℝ)) ^
              hullSixThreeThreeQ233FourWeight i) = a * k / 4 := by
    simpa [hullSixThreeThreeQ233FourWeight, Fin.prod_univ_succ] using
      (hullSixThreeThreeQ233_fourTerm_product (a := a) (k := k) hb hc hp)
  rw [hscaledProduct] at hamgm
  nlinarith

/--
When the shifted endpoint numerator is nonpositive, the average of the two
upper estimates plus `Q0` is already strictly larger than `13/2`.
-/
theorem hullSixThreeThreeQ233_nonpos_height
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hN : e * (a + 1) - f * (a - 1) ≤ 0) :
    (13 : ℝ) / 2 <
      (((a + b) / d + (c + d) / b - 1) +
        (b - a + (c + d) / b)) / 2 +
          (a + f - 2 + d * f *
            (1 / (b * d) + 1 / (b * c) + 1 / (c * e))) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have haStrict : 1 < a := by
    by_contra h
    have hae : a = 1 := by linarith
    rw [hae] at hN
    nlinarith

  let k : ℝ := f / e
  let p : ℝ := d / b
  have hk : 0 < k := by dsimp [k]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hkBoundary : a + 1 ≤ k * (a - 1) := by
    dsimp [k]
    have hscale := mul_le_mul_of_nonneg_left hN (le_of_lt (one_div_pos.mpr he))
    have hid :
        (1 / e) * (e * (a + 1) - f * (a - 1)) =
          (a + 1) - (f / e) * (a - 1) := by
      field_simp [he.ne']
      <;> ring
    rw [hid] at hscale
    linarith
  have hkLeF : k ≤ f := by
    dsimp [k]
    have hmul := mul_le_mul_of_nonneg_left he1 (le_of_lt (div_pos hf he))
    calc
      f / e = (f / e) * 1 := by ring
      _ ≤ (f / e) * e := hmul
      _ = f := by field_simp [he.ne']

  have hPpoly : 0 < 10 * p ^ 2 - 14 * p + 5 := by
    nlinarith [sq_nonneg (10 * p - 7)]
  have hpBound : (7 : ℝ) / 5 < p + 1 / (2 * p) := by
    have hq : 0 < (10 * p ^ 2 - 14 * p + 5) / (10 * p) := by
      positivity
    have hid :
        (10 * p ^ 2 - 14 * p + 5) / (10 * p) =
          p + 1 / (2 * p) - 7 / 5 := by
      field_simp [hp.ne']
      <;> ring
    rw [hid] at hq
    linarith

  have hApoly : 0 < 5 * a ^ 2 - 29 * a + 44 := by
    nlinarith [sq_nonneg (10 * a - 29)]
  have hkFrac : (a + 1) / (a - 1) ≤ k := by
    apply (div_le_iff₀ (sub_pos.mpr haStrict)).2
    nlinarith
  have hakHalf : (17 : ℝ) / 5 < k + a / 2 := by
    have hq :
        (17 : ℝ) / 5 < (a + 1) / (a - 1) + a / 2 := by
      have hpos : 0 < (5 * a ^ 2 - 29 * a + 44) / (10 * (a - 1)) := by
        positivity
      have hid :
          (5 * a ^ 2 - 29 * a + 44) / (10 * (a - 1)) =
            (a + 1) / (a - 1) + a / 2 - 17 / 5 := by
        field_simp [ne_of_gt (sub_pos.mpr haStrict)]
        <;> ring
      rw [hid] at hpos
      linarith
    linarith

  have hAKpoly : 0 < 5 * a ^ 2 - 24 * a + 29 := by
    nlinarith [sq_nonneg (5 * a - 12)]
  have hakBoundary : (29 : ℝ) / 5 < a * ((a + 1) / (a - 1)) := by
    have hq :
        0 < (5 * a ^ 2 - 24 * a + 29) / (5 * (a - 1)) := by
      positivity
    have hid :
        (5 * a ^ 2 - 24 * a + 29) / (5 * (a - 1)) =
          a * ((a + 1) / (a - 1)) - 29 / 5 := by
      field_simp [ne_of_gt (sub_pos.mpr haStrict)]
      <;> ring
    rw [hid] at hq
    linarith
  have hak : (29 : ℝ) / 5 < a * k := by
    have hmul := mul_le_mul_of_nonneg_left hkFrac (le_of_lt ha)
    nlinarith

  have hFour := hullSixThreeThreeQ233_four_gt ha hb hc hp hk hak
  let L : ℝ :=
    (a + b) / 2 + (a + b) / (2 * d) + (c + d) / b +
      f + f / b + d * f / (b * c) + d * f / (c * e)
  let R : ℝ :=
    a / 2 + k + p + 1 / (2 * p) + b / 2 +
      a / (2 * p * b) + c / b + p * k * b / c
  have hLminusR : 0 ≤ L - R := by
    have hfk : 0 ≤ f - k := sub_nonneg.mpr hkLeF
    have hexact : L - R = f - k + f / b + d * f / (b * c) := by
      dsimp [L, R, p, k]
      field_simp [hb.ne', hc.ne', he.ne', hd.ne']
      <;> ring
    rw [hexact]
    positivity
  have hRgt : 9 < R := by
    have hFour' :
        (21 : ℝ) / 5 <
          b / 2 + a / (2 * p * b) + c / b + p * k * b / c := by
      convert hFour using 1 <;>
        simp [hullSixThreeThreeQ233FourTerm, Fin.sum_univ_succ] <;>
        ring
    dsimp [R]
    nlinarith [hpBound, hakHalf, hFour']
  have hLgt : 9 < L := by linarith
  have hEndpointIdentity :
      (((a + b) / d + (c + d) / b - 1) +
        (b - a + (c + d) / b)) / 2 +
          (a + f - 2 + d * f *
            (1 / (b * d) + 1 / (b * c) + 1 / (c * e))) =
        L - 5 / 2 := by
    dsimp [L]
    field_simp [hb.ne', hc.ne', hd.ne', he.ne']
    <;> ring
  rw [hEndpointIdentity]
  linarith

/-! ## The two `f = 1` endpoints -/

theorem hullSixThreeThreeQ233_mNeg_height
    {a b c d e : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e)
    (hM : 1 / c - 1 + 1 / a < 0) :
    (13 : ℝ) / 2 <
      ((a + b) / d + (c + d) / b - 1) +
        (a - 1 + d + d / a + 1 / b + d / (b * c) +
          (d / e) * (1 / c - 1 + 1 / a)) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hInvE : 1 / e ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left he1 (by positivity : 0 ≤ (1 : ℝ) / e)
    calc
      1 / e = (1 / e) * 1 := by ring
      _ ≤ (1 / e) * e := hmul
      _ = 1 := by field_simp [he.ne']
  have hMscale :
      d * (1 / c - 1 + 1 / a) ≤
        (d / e) * (1 / c - 1 + 1 / a) := by
    have hfirst : d * (1 / e - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (by linarith)
    have hnonneg :
        0 ≤ d * (1 / e - 1) * (1 / c - 1 + 1 / a) := by
      exact mul_nonneg_of_nonpos_of_nonpos hfirst (le_of_lt hM)
    have hid :
        (d / e) * (1 / c - 1 + 1 / a) -
            d * (1 / c - 1 + 1 / a) =
          d * (1 / e - 1) * (1 / c - 1 + 1 / a) := by ring
    linarith
  have h19 := hullSixThreeThreeQ233_nineteen_gt ha hb hc hd
  have hid :
      ((a + b) / d + (c + d) / b - 1) +
          (a - 1 + d + d / a + 1 / b + d / (b * c) +
            d * (1 / c - 1 + 1 / a)) + 2 =
        hullSixThreeThreeQ233NineteenSum a b c d := by
    dsimp [hullSixThreeThreeQ233NineteenSum]
    field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
    <;> ring
  have hEndpoint :
      (17 : ℝ) / 2 <
        ((a + b) / d + (c + d) / b - 1) +
          (a - 1 + d + d / a + 1 / b + d / (b * c) +
            d * (1 / c - 1 + 1 / a)) + 2 := by
    rw [hid]
    exact h19
  linarith

/--
The asymmetric `M >= 0` endpoint.  The rational substitution below turns
the endpoint into the ten-term thirty-eight-copy sum.
-/
theorem hullSixThreeThreeQ233_asym_height
    {a b c d : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hd1 : 1 ≤ d)
    (hM : 0 ≤ 1 / c - 1 + 1 / a)
    (hL : 1 / d + a / (b * d) + a / (b * c) ≤ 1) :
    (13 : ℝ) / 2 <
      (b - a + (c + d) / b) +
        (a - 1 + 1 / b + d / (b * c) + d + d / a) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  let x : ℝ := a / b
  let v : ℝ := x / c
  let u : ℝ := (1 + x) / d
  have hx : 0 < x := by dsimp [x]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hUV : u + v ≤ 1 := by
    have hid :
        u + v = 1 / d + a / (b * d) + a / (b * c) := by
      dsimp [u, v, x]
      field_simp [hb.ne', hc.ne', hd.ne']
      <;> ring
    rw [hid]
    exact hL
  have hOneMinusV : 0 < 1 - v := by linarith
  let A : ℝ := (1 + x) / (1 - v)
  let r0 : ℝ := A - 1
  let y : ℝ := r0 - x
  have hA : 0 < A := by dsimp [A]; positivity
  have hAleD : A ≤ d := by
    apply (div_le_iff₀ hOneMinusV).2
    have huLe : (1 + x) / d ≤ 1 - v := by
      dsimp [u] at hUV
      linarith
    simpa [mul_comm] using (div_le_iff₀ hd).1 huLe
  have hMscaled : (a - 1) / b ≤ v := by
    have hscale := mul_nonneg (le_of_lt hx) hM
    have hid :
        x * (1 / c - 1 + 1 / a) = v - (a - 1) / b := by
      dsimp [x, v]
      field_simp [ha.ne', hb.ne', hc.ne']
      <;> ring
    rw [hid] at hscale
    linarith
  have hyIdentity : y = A * x / c := by
    have hAden : A * (1 - v) = 1 + x := by
      dsimp [A]
      field_simp [ne_of_gt hOneMinusV]
    have hvx : x / c = v := by rfl
    calc
      y = A - 1 - x := by rfl
      _ = A * v := by nlinarith [hAden]
      _ = A * x / c := by rw [← hvx]; ring
  have hy : 0 < y := by rw [hyIdentity]; positivity
  have hAexpand : A = 1 + x + y := by
    dsimp [y, r0]
    ring

  let coeff : ℝ := 1 / b + 1 / (b * c) + 1 + 1 / a
  have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hdScaled : A * coeff ≤ d * coeff :=
    mul_le_mul_of_nonneg_right hAleD hcoeff
  let E0 : ℝ :=
    r0 + b + A * r0 / (b * y) + (2 * A - 1) / (b * x)
  have hEndpointLower :
      E0 ≤
        (b - a + (c + d) / b) +
          (a - 1 + 1 / b + d / (b * c) + d + d / a) := by
    have hRawIdentity :
        (b - a + (c + d) / b) +
            (a - 1 + 1 / b + d / (b * c) + d + d / a) =
          b - 1 + c / b + 1 / b + d * coeff := by
      dsimp [coeff]
      ring
    rw [hRawIdentity]
    have hBoundaryIdentity :
        b - 1 + c / b + 1 / b + A * coeff = E0 := by
      dsimp [E0, coeff, r0]
      have hax : a = b * x := by
        dsimp [x]
        field_simp [hb.ne']
      have hyCross : c * y = A * x := by
        rw [hyIdentity]
        field_simp [hc.ne']
      have hyCross' := hyCross
      rw [hAexpand] at hyCross'
      rw [hax]
      field_simp [hb.ne', hc.ne', hx.ne', hy.ne']
      rw [hAexpand]
      linear_combination (c * x - y) * hyCross'
    rw [← hBoundaryIdentity]
    linarith
  have hEexpand : E0 = hullSixThreeThreeQ233AsymSum b x y := by
    dsimp [E0, r0, hullSixThreeThreeQ233AsymSum]
    rw [hAexpand]
    field_simp [hb.ne', hx.ne', hy.ne']
    <;> ring
  have hAsym := hullSixThreeThreeQ233_asym_gt hb hx hy
  rw [← hEexpand] at hAsym
  exact hAsym.trans_le hEndpointLower

/-! ## The height-max theorem -/

/--
The scalar height theorem behind all three positive-`Y01` cuts.  The single
reciprocal inequality is exactly the rescaled positive-`Y01` floor.  The two
maxima retain whichever upper- and lower-chain endpoint is stronger.
-/
theorem hullSixThreeThreeQ233_heightMax
    {a b c d e f : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hI :
      e / d + a * e / (b * d) + a * e / (b * c) + a / c ≤
        a + e - 1) :
    (13 : ℝ) / 2 <
      max ((a + b) / d + (c + d) / b - 1)
          (b - a + (c + d) / b) +
        max
          (a + f - 2 + d * f *
            (1 / (b * d) + 1 / (b * c) + 1 / (c * e)))
          ((a + f - 2 + d * f *
              (1 / (b * d) + 1 / (b * c) + 1 / (c * e))) +
            d * f * ((a * e - a * f + e + f) / (a * e * f))) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1

  let PA : ℝ := (a + b) / d + (c + d) / b - 1
  let PB : ℝ := b - a + (c + d) / b
  let A0 : ℝ := 1 / (b * d) + 1 / (b * c) + 1 / (c * e)
  let Q0 : ℝ → ℝ := fun g => a + g - 2 + d * g * A0
  let z0 : ℝ → ℝ := fun g => (a * e - a * g + e + g) / (a * e * g)
  let Qr : ℝ → ℝ := fun g => Q0 g + d * g * z0 g
  let N : ℝ := e * (a + 1) - f * (a - 1)
  let K : ℝ :=
    1 + 1 / b + d / (b * c) + d / (c * e) + d / (a * e) - d / e
  let M : ℝ := 1 / c - 1 + 1 / a
  change (13 : ℝ) / 2 < max PA PB + max (Q0 f) (Qr f)

  have hPaverage : (PA + PB) / 2 ≤ max PA PB := by
    have hleft := le_max_left PA PB
    have hright := le_max_right PA PB
    linarith

  by_cases hNle : N ≤ 0
  · have hbase := hullSixThreeThreeQ233_nonpos_height
      ha1 hb1 hc1 hd1 he1 hf1 (by simpa [N] using hNle)
    have hbase' : (13 : ℝ) / 2 < (PA + PB) / 2 + Q0 f := by
      simpa [PA, PB, Q0, A0] using hbase
    exact hbase'.trans_le
      (add_le_add hPaverage (le_max_left (Q0 f) (Qr f)))

  · have hN : 0 < N := lt_of_not_ge hNle
    by_cases hKneg : K < 0
    · have haStrict : 1 < a := by
        by_contra hnot
        have haEq : a = 1 := by linarith
        have hKpos : 0 < K := by
          have hid : K = 1 + 1 / b + d / (b * c) + d / (c * e) := by
            dsimp [K]
            rw [haEq]
            field_simp [hb.ne', hc.ne', he.ne']
            <;> ring
          rw [hid]
          positivity
        linarith
      let fs : ℝ := e * (a + 1) / (a - 1)
      have hfs : 0 < fs := by dsimp [fs]; positivity
      have hratio : 1 < (a + 1) / (a - 1) := by
        apply (lt_div_iff₀ (sub_pos.mpr haStrict)).2
        linarith
      have hfs1 : 1 ≤ fs := by
        have hmul :=
          mul_le_mul_of_nonneg_right he1
            (le_of_lt (lt_trans zero_lt_one hratio))
        have hratioLe : (a + 1) / (a - 1) ≤ fs := by
          dsimp [fs]
          calc
            (a + 1) / (a - 1) =
                1 * ((a + 1) / (a - 1)) := by ring
            _ ≤ e * ((a + 1) / (a - 1)) := hmul
            _ = e * (a + 1) / (a - 1) := by ring
        linarith
      have hfLe : f ≤ fs := by
        dsimp [fs]
        apply (le_div_iff₀ (sub_pos.mpr haStrict)).2
        dsimp [N] at hN
        linarith
      have hNfs : e * (a + 1) - fs * (a - 1) = 0 := by
        dsimp [fs]
        field_simp [ne_of_gt (sub_pos.mpr haStrict)]
        <;> ring
      have hboundary := hullSixThreeThreeQ233_nonpos_height
        ha1 hb1 hc1 hd1 he1 hfs1 (le_of_eq hNfs)
      have hboundary' : (13 : ℝ) / 2 < (PA + PB) / 2 + Q0 fs := by
        simpa [PA, PB, Q0, A0] using hboundary
      have hzBoundary : z0 fs = 0 := by
        have hnum : a * e - a * fs + e + fs = 0 := by
          nlinarith [hNfs]
        dsimp [z0]
        rw [hnum]
        simp
      have hQrBoundary : Qr fs = Q0 fs := by
        change Q0 fs + d * fs * z0 fs = Q0 fs
        rw [hzBoundary]
        ring
      have hQrDiff : Qr f - Qr fs = (f - fs) * K := by
        dsimp [Qr, Q0, z0, A0, K]
        field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne', hfs.ne']
        <;> ring
      have hQrMono : Qr fs ≤ Qr f := by
        have hprod : 0 ≤ (f - fs) * K :=
          mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfLe) hKneg.le
        linarith
      have hlower : Q0 fs ≤ max (Q0 f) (Qr f) := by
        rw [← hQrBoundary]
        exact hQrMono.trans (le_max_right (Q0 f) (Qr f))
      exact hboundary'.trans_le (add_le_add hPaverage hlower)

    · have hK : 0 ≤ K := le_of_not_gt hKneg
      have hQrDiffOne : Qr f - Qr 1 = (f - 1) * K := by
        dsimp [Qr, Q0, z0, A0, K]
        field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne', hf.ne']
        <;> ring
      have hQrOneLe : Qr 1 ≤ Qr f := by
        have hprod : 0 ≤ (f - 1) * K :=
          mul_nonneg (sub_nonneg.mpr hf1) hK
        linarith
      have hQrOneForm :
          Qr 1 =
            a - 1 + d + d / a + 1 / b + d / (b * c) + (d / e) * M := by
        dsimp [Qr, Q0, z0, A0, M]
        field_simp [ha.ne', hb.ne', hc.ne', hd.ne', he.ne']
        <;> ring

      by_cases hMneg : M < 0
      · have hm := hullSixThreeThreeQ233_mNeg_height
          ha1 hb1 hc1 hd1 he1 (by simpa [M] using hMneg)
        have hm' : (13 : ℝ) / 2 < PA + Qr 1 := by
          rw [hQrOneForm]
          simpa [PA, M] using hm
        exact hm'.trans_le
          (add_le_add
            (le_max_left PA PB)
            (hQrOneLe.trans (le_max_right (Q0 f) (Qr f))))

      · have hM : 0 ≤ M := le_of_not_gt hMneg
        let L0 : ℝ := 1 / d + a / (b * d) + a / (b * c)
        have hIidentity :
            e * (L0 - 1) + a * M =
              (e / d + a * e / (b * d) + a * e / (b * c) + a / c) -
                (a + e - 1) := by
          dsimp [L0, M]
          field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
          <;> ring
        have hLnonpos : e * (L0 - 1) ≤ 0 := by
          have htotal : e * (L0 - 1) + a * M ≤ 0 := by
            rw [hIidentity]
            linarith
          have hAM : 0 ≤ a * M := mul_nonneg (le_of_lt ha) hM
          linarith
        have hL : L0 ≤ 1 := by
          by_contra hnot
          have hstrict : 0 < L0 - 1 := by linarith
          have := mul_pos he hstrict
          linarith
        let Qinf : ℝ := a - 1 + 1 / b + d / (b * c) + d + d / a
        have hQinfLeOne : Qinf ≤ Qr 1 := by
          have hscale : 0 ≤ (d / e) * M := by positivity
          rw [hQrOneForm]
          dsimp [Qinf]
          linarith
        have hasym := hullSixThreeThreeQ233_asym_height
          ha1 hb1 hc1 hd1 (by simpa [M] using hM) (by simpa [L0] using hL)
        have hasym' : (13 : ℝ) / 2 < PB + Qinf := by
          simpa [PB, Qinf] using hasym
        exact hasym'.trans_le
          (add_le_add
            (le_max_right PA PB)
            (hQinfLeOne.trans
              (hQrOneLe.trans (le_max_right (Q0 f) (Qr f)))))

/-! ## Raw consecutive-area certificate -/

/--
The geometry-facing scalar certificate for the positive-`Y01` family.

The five gap variables are the consecutive slope gaps
`r,s,t,w,z`.  Thus the six consecutive area summands are
```
ab(r+s),  bc t,  cd(s+t),  de(s+t+w),  ef z,  af(r+s+t+w+z).
```
The last hypothesis is the normalized lower hull-ear floor.  Keeping it
explicit is what makes both lower-chain endpoints valid without a height
ordering case split.
-/
theorem hullSixThreeThreeQ233_scalar
    {a b c d e f r s t w z : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hX00 : 1 ≤ a * d * r)
    (hX10 : 1 ≤ b * d * s)
    (hu1 : 1 ≤ b * c * t)
    (hX21 : 1 ≤ c * e * w)
    (hl1 : 1 ≤ e * f * z)
    (hUpper01q : 1 ≤ a * b * (r + s) + a - b)
    (hY01pos : 1 ≤ a + e - a * e * (r + s + t + w))
    (hY02neg : 1 ≤ a * f * (r + s + t + w + z) - a - f)
    (hLowerEar :
      1 ≤ d * e * (s + t + w) + e * f * z -
        d * f * (s + t + w + z)) :
    (25 : ℝ) / 2 <
      a * b * (r + s) + b * c * t + c * d * (s + t) +
        d * e * (s + t + w) + e * f * z +
          a * f * (r + s + t + w + z) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1

  let U : ℝ := a * b * (r + s)
  let T : ℝ := b * c * t
  let E : ℝ := c * d * (s + t)
  let L : ℝ := d * e * (s + t + w)
  let Z : ℝ := e * f * z
  let F : ℝ := a * f * (r + s + t + w + z)
  let R : ℝ := U + T + E - 2
  let S : ℝ := L + Z + F - 4
  let PA : ℝ := (a + b) / d + (c + d) / b - 1
  let PB : ℝ := b - a + (c + d) / b
  let A0 : ℝ := 1 / (b * d) + 1 / (b * c) + 1 / (c * e)
  let Q0 : ℝ := a + f - 2 + d * f * A0
  let z0 : ℝ := (a * e - a * f + e + f) / (a * e * f)
  let Qr : ℝ := Q0 + d * f * z0

  have hr : 1 / (a * d) ≤ r := by
    apply (div_le_iff₀ (mul_pos ha hd)).2
    nlinarith [hX00]
  have hs : 1 / (b * d) ≤ s := by
    apply (div_le_iff₀ (mul_pos hb hd)).2
    nlinarith [hX10]
  have ht : 1 / (b * c) ≤ t := by
    apply (div_le_iff₀ (mul_pos hb hc)).2
    nlinarith [hu1]
  have hw : 1 / (c * e) ≤ w := by
    apply (div_le_iff₀ (mul_pos hc he)).2
    nlinarith [hX21]
  have hz : 1 / (e * f) ≤ z := by
    apply (div_le_iff₀ (mul_pos he hf)).2
    nlinarith [hl1]
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hz

  /- The positive `Y01` floor gives the reciprocal height inequality. -/
  have hYupper :
      a * e * (r + s + t + w) ≤ a + e - 1 := by
    linarith
  have hIr : e / d ≤ a * e * r := by
    have hscale :=
      mul_le_mul_of_nonneg_left hX00 (le_of_lt (div_pos he hd))
    calc
      e / d = (e / d) * 1 := by ring
      _ ≤ (e / d) * (a * d * r) := hscale
      _ = a * e * r := by field_simp [hd.ne']
  have hIs : a * e / (b * d) ≤ a * e * s := by
    have hcoef : 0 ≤ a * e / (b * d) := by positivity
    have hscale := mul_le_mul_of_nonneg_left hX10 hcoef
    calc
      a * e / (b * d) = (a * e / (b * d)) * 1 := by ring
      _ ≤ (a * e / (b * d)) * (b * d * s) := hscale
      _ = a * e * s := by field_simp [hb.ne', hd.ne']
  have hIt : a * e / (b * c) ≤ a * e * t := by
    have hcoef : 0 ≤ a * e / (b * c) := by positivity
    have hscale := mul_le_mul_of_nonneg_left hu1 hcoef
    calc
      a * e / (b * c) = (a * e / (b * c)) * 1 := by ring
      _ ≤ (a * e / (b * c)) * (b * c * t) := hscale
      _ = a * e * t := by field_simp [hb.ne', hc.ne']
  have hIw : a / c ≤ a * e * w := by
    have hscale :=
      mul_le_mul_of_nonneg_left hX21 (le_of_lt (div_pos ha hc))
    calc
      a / c = (a / c) * 1 := by ring
      _ ≤ (a / c) * (c * e * w) := hscale
      _ = a * e * w := by field_simp [hc.ne']
  have hI :
      e / d + a * e / (b * d) + a * e / (b * c) + a / c ≤
        a + e - 1 := by
    nlinarith [hIr, hIs, hIt, hIw, hYupper]

  /- Two independent upper-chain lower bounds. -/
  have hUr : b / d ≤ a * b * r := by
    have hscale :=
      mul_le_mul_of_nonneg_left hX00 (le_of_lt (div_pos hb hd))
    calc
      b / d = (b / d) * 1 := by ring
      _ ≤ (b / d) * (a * d * r) := hscale
      _ = a * b * r := by field_simp [hd.ne']
  have hUs : a / d ≤ a * b * s := by
    have hscale :=
      mul_le_mul_of_nonneg_left hX10 (le_of_lt (div_pos ha hd))
    calc
      a / d = (a / d) * 1 := by ring
      _ ≤ (a / d) * (b * d * s) := hscale
      _ = a * b * s := by field_simp [hd.ne']
  have hUfirst : (a + b) / d ≤ U := by
    calc
      (a + b) / d = b / d + a / d := by ring
      _ ≤ a * b * r + a * b * s := add_le_add hUr hUs
      _ = U := by dsimp [U]; ring
  have hTone : 1 ≤ T := by simpa [T] using hu1
  have hEs : c / b ≤ c * d * s := by
    have hscale :=
      mul_le_mul_of_nonneg_left hX10 (le_of_lt (div_pos hc hb))
    calc
      c / b = (c / b) * 1 := by ring
      _ ≤ (c / b) * (b * d * s) := hscale
      _ = c * d * s := by field_simp [hb.ne']
  have hEt : d / b ≤ c * d * t := by
    have hscale :=
      mul_le_mul_of_nonneg_left hu1 (le_of_lt (div_pos hd hb))
    calc
      d / b = (d / b) * 1 := by ring
      _ ≤ (d / b) * (b * c * t) := hscale
      _ = c * d * t := by field_simp [hb.ne']
  have hEfirst : (c + d) / b ≤ E := by
    calc
      (c + d) / b = c / b + d / b := by ring
      _ ≤ c * d * s + c * d * t := add_le_add hEs hEt
      _ = E := by dsimp [E]; ring
  have hRPA : PA ≤ R := by
    dsimp [PA, R]
    linarith [hUfirst, hTone, hEfirst]
  have hUsecond : b - a + 1 ≤ U := by
    dsimp [U]
    linarith [hUpper01q]
  have hRPB : PB ≤ R := by
    dsimp [PB, R]
    linarith [hUsecond, hTone, hEfirst]

  /- The lower ear plus `-Y02` controls the whole lower chain. -/
  have hEar :
      1 + d * f * (s + t + w + z) ≤ L + Z := by
    dsimp [L, Z]
    linarith [hLowerEar]
  have hFlower : a + f + 1 ≤ F := by
    dsimp [F]
    linarith [hY02neg]
  have hSraw :
      a + f - 2 + d * f * (s + t + w + z) ≤ S := by
    dsimp [S]
    linarith [hEar, hFlower]
  have hA0 : A0 ≤ s + t + w := by
    dsimp [A0]
    linarith [hs, ht, hw]
  have hQ0 : Q0 ≤ S := by
    have hsum : A0 ≤ s + t + w + z := by linarith [hA0, hzpos]
    have hscaled := mul_le_mul_of_nonneg_left hsum (mul_nonneg hd.le hf.le)
    dsimp [Q0]
    linarith [hSraw, hscaled]

  /- Trading the positive-`Y01` upper bound against `-Y02` gives `z0`. -/
  have hYscaled := mul_le_mul_of_nonneg_left hYupper (le_of_lt hf)
  have hFscaled := mul_le_mul_of_nonneg_left hFlower (le_of_lt he)
  have hzNumerator :
      a * e - a * f + e + f ≤ a * e * f * z := by
    dsimp [F] at hFscaled
    nlinarith [hYscaled, hFscaled]
  have hz0 : z0 ≤ z := by
    dsimp [z0]
    apply (div_le_iff₀ (mul_pos (mul_pos ha he) hf)).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hzNumerator
  have hQr : Qr ≤ S := by
    have hsum : A0 + z0 ≤ s + t + w + z := by linarith [hA0, hz0]
    have hscaled := mul_le_mul_of_nonneg_left hsum (mul_nonneg hd.le hf.le)
    have hid : Qr = a + f - 2 + d * f * (A0 + z0) := by
      dsimp [Qr, Q0]
      ring
    rw [hid]
    linarith [hSraw, hscaled]

  have hheight := hullSixThreeThreeQ233_heightMax
    ha1 hb1 hc1 hd1 he1 hf1 hI
  have hheight' : (13 : ℝ) / 2 < max PA PB + max Q0 Qr := by
    simpa [PA, PB, Q0, Qr, A0, z0] using hheight
  have hmaxP : max PA PB ≤ R := max_le hRPA hRPB
  have hmaxQ : max Q0 Qr ≤ S := max_le hQ0 hQr
  have hRS : (13 : ℝ) / 2 < R + S :=
    hheight'.trans_le (add_le_add hmaxP hmaxQ)
  dsimp [R, S, U, T, E, L, Z, F] at hRS
  nlinarith

end Heilbronn8
