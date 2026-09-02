import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Compact scalar closure for the residual `MRRR / LLLM` table

This is the complement-rotation-fixed residual table called
`HullSixTwoFourCuts.strictCounterexample` by the finite census.  The proof
does not use that finite symmetry.  The two height orientations are derived
separately, in the `P` and `Q` fans, and reduce to the same eleven-term
Laurent inequality.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

noncomputable def hullSixTwoFour_p03Laurent
    (b c r f : ℝ) : ℝ :=
  f + b / 2 + 1 / (2 * c) + b / (2 * c) +
    1 / (2 * f) + b / (2 * f) + c / b + r / b +
      f / b + b / r + c / r

noncomputable def hullSixTwoFour_p03Term
    (b c r f : ℝ) : Fin 11 → ℝ :=
  ![f, b / 2, 1 / (2 * c), b / (2 * c),
    1 / (2 * f), b / (2 * f), c / b, r / b,
    f / b, b / r, c / r]

def hullSixTwoFour_p03Weight : Fin 11 → ℕ :=
  ![4, 3, 3, 4, 4, 4, 4, 8, 4, 5, 3]

noncomputable def hullSixTwoFour_p03Constant : ℝ :=
  1 / (2 ^ 90 * 3 ^ 9 * 5 ^ 5)

theorem hullSixTwoFour_p03Weight_pos
    (i : Fin 11) : 0 < hullSixTwoFour_p03Weight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_p03Weight]

theorem hullSixTwoFour_p03Weight_sum :
    ∑ i, hullSixTwoFour_p03Weight i = 46 := by
  norm_num [hullSixTwoFour_p03Weight, Fin.sum_univ_succ]

theorem hullSixTwoFour_p03Term_nonneg
    {b c r f : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hf : 0 ≤ f) (i : Fin 11) :
    0 ≤ hullSixTwoFour_p03Term b c r f i := by
  fin_cases i <;> simp [hullSixTwoFour_p03Term] <;> positivity

theorem hullSixTwoFour_p03Term_sum
    (b c r f : ℝ) :
    ∑ i, hullSixTwoFour_p03Term b c r f i =
      hullSixTwoFour_p03Laurent b c r f := by
  simp [hullSixTwoFour_p03Term, hullSixTwoFour_p03Laurent,
    Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_p03Term_product
    {b c r f : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r) (hf : 0 < f) :
    (∏ i,
        (hullSixTwoFour_p03Term b c r f i /
          (hullSixTwoFour_p03Weight i : ℝ)) ^
            hullSixTwoFour_p03Weight i) =
      hullSixTwoFour_p03Constant := by
  simp [hullSixTwoFour_p03Term, hullSixTwoFour_p03Weight,
    Fin.prod_univ_succ, hullSixTwoFour_p03Constant]
  field_simp [hb.ne', hc.ne', hr.ne', hf.ne'] <;> ring

theorem hullSixTwoFour_p03Constant_pos :
    0 < hullSixTwoFour_p03Constant := by
  norm_num [hullSixTwoFour_p03Constant]

theorem hullSixTwoFour_p03_root_gap :
    (8 : ℝ) <
      46 * hullSixTwoFour_p03Constant ^ ((46 : ℝ)⁻¹) := by
  have hpow : ((4 : ℝ) / 23) ^ 46 <
      hullSixTwoFour_p03Constant := by
    norm_num [hullSixTwoFour_p03Constant]
  have hpowRpow : ((4 : ℝ) / 23) ^ (46 : ℝ) <
      hullSixTwoFour_p03Constant := by
    change ((4 : ℝ) / 23) ^ ((46 : ℕ) : ℝ) <
      hullSixTwoFour_p03Constant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (4 : ℝ) / 23 <
      hullSixTwoFour_p03Constant ^ ((46 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_p03Constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_p03_laurent_gt
    {b c r f : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r) (hf : 0 < f) :
    (8 : ℝ) < hullSixTwoFour_p03Laurent b c r f := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_p03Weight (hullSixTwoFour_p03Term b c r f)
    hullSixTwoFour_p03Weight_pos
    (hullSixTwoFour_p03Term_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt hr) (le_of_lt hf))
  rw [hullSixTwoFour_p03Weight_sum,
    hullSixTwoFour_p03Term_product hb hc hr hf,
    hullSixTwoFour_p03Term_sum b c r f] at hamgm
  exact hullSixTwoFour_p03_root_gap.trans_le hamgm

/-! ## The orientation `d ≤ e`, in the `P` fan -/

theorem hullSixTwoFour_p03_e_ge_d_scalar
    {a b c d e f A Ap C E0 E1 E2 F X11 X12 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hE01 : 1 ≤ E0) (hE11 : 1 ≤ E1)
    (hde : d ≤ e) (hAp : Ap = A + a - b)
    (hcA : a + b ≤ c * A) (hfAp : a + b ≤ f * Ap)
    (hbE2 : e + f ≤ b * E2) (hF : a + f + 1 ≤ F)
    (hEar : d ≤ (d - c) * E1 - (e - d) * E0)
    (hRec : b * E1 = e * X11 - d * X12)
    (hX12 : 1 ≤ X12) (hHull : 1 ≤ C + E0 - X11) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hE00 : 0 ≤ E0 := le_trans zero_le_one hE01
  have hE10 : 0 ≤ E1 := le_trans zero_le_one hE11
  let r := d - c
  have hr : 0 < r := by
    dsimp [r]
    by_contra hnot
    have hdc : d - c ≤ 0 := le_of_not_gt hnot
    have hfirst : (d - c) * E1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdc hE10
    have hsecond : 0 ≤ (e - d) * E0 :=
      mul_nonneg (sub_nonneg.mpr hde) hE00
    nlinarith
  have hE : e ≤ r * E1 := by
    have hmul : e - d ≤ (e - d) * E0 := by
      have := mul_le_mul_of_nonneg_left hE01 (sub_nonneg.mpr hde)
      simpa using this
    dsimp [r]
    nlinarith [hEar]
  have hE1Lower : e / r ≤ E1 := by
    apply (div_le_iff₀ hr).2
    simpa [mul_comm] using hE

  have hX12Mul : d ≤ d * X12 := by
    simpa using mul_le_mul_of_nonneg_left hX12 (le_of_lt hd)
  have hRecLower : b * E1 + d ≤ e * X11 := by
    linarith [hRec, hX12Mul]
  have hXUpper : X11 ≤ C + E0 - 1 := by linarith
  have heX : e * X11 ≤ e * (C + E0 - 1) :=
    mul_le_mul_of_nonneg_left hXUpper (le_of_lt he)
  have hbE : b * (e / r) ≤ b * E1 :=
    mul_le_mul_of_nonneg_left hE1Lower (le_of_lt hb)
  have hRaw : b * (e / r) + d ≤ e * (C + E0 - 1) := by
    linarith
  have hShape : b * (e / r) + d = e * (b / r + d / e) := by
    field_simp [hr.ne', he.ne'] <;> ring
  have hCE : 1 + b / r + d / e ≤ C + E0 := by
    rw [hShape] at hRaw
    have hdiv := le_of_mul_le_mul_left hRaw he
    linarith

  have hALeft : (a + b) / c ≤ A := by
    apply (div_le_iff₀ hc).2
    simpa [mul_comm] using hcA
  have hARight : (a + b) / f - a + b ≤ A := by
    have hdiv : (a + b) / f ≤ Ap := by
      apply (div_le_iff₀ hf).2
      simpa [mul_comm] using hfAp
    rw [hAp] at hdiv
    linarith
  have hAavg :
      ((a + b) / c + ((a + b) / f - a + b)) / 2 ≤ A := by
    linarith
  have hAavg' :
      a / (2 * c) + b / (2 * c) + a / (2 * f) + b / (2 * f) -
          a / 2 + b / 2 ≤ A := by
    calc
      a / (2 * c) + b / (2 * c) + a / (2 * f) + b / (2 * f) -
            a / 2 + b / 2 =
          ((a + b) / c + ((a + b) / f - a + b)) / 2 := by
            field_simp [hc.ne', hf.ne']
            ring
      _ ≤ A := hAavg
  have hE2Lower : (e + f) / b ≤ E2 := by
    apply (div_le_iff₀ hb).2
    simpa [mul_comm] using hbE2
  have hE2Lower' : e / b + f / b ≤ E2 := by
    calc
      e / b + f / b = (e + f) / b := by ring
      _ ≤ E2 := hE2Lower

  have haHalf : (1 : ℝ) / 2 ≤ a / 2 := by linarith
  have haC : 1 / (2 * c) ≤ a / (2 * c) := by
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * c)).2
    exact ha1
  have haF : 1 / (2 * f) ≤ a / (2 * f) := by
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * f)).2
    exact ha1
  have heB : c / b + r / b ≤ e / b := by
    have hcr : c + r ≤ e := by dsimp [r]; linarith
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hb).2 hcr
  have hReciprocal : 2 ≤ d / e + e / d := by
    field_simp [hd.ne', he.ne']
    nlinarith [sq_nonneg (d - e)]
  have heR : e / d + c / r ≤ e / r := by
    have hshape : e / r - (e / d + c / r) =
        c * (e - d) / (r * d) := by
      field_simp [hr.ne', hd.ne']
      dsimp [r]
      ring
    have hnonneg : 0 ≤ c * (e - d) / (r * d) := by positivity
    linarith

  have hLower : (9 : ℝ) / 2 +
      hullSixTwoFour_p03Laurent b c r f ≤
        A + C + E0 + E1 + E2 + F := by
    dsimp [hullSixTwoFour_p03Laurent]
    linarith [hAavg', hCE, hE1Lower, hE2Lower', hF,
      haHalf, haC, haF, heB, hReciprocal, heR]
  have hStrict : (25 : ℝ) / 2 < (9 : ℝ) / 2 +
      hullSixTwoFour_p03Laurent b c r f := by
    have h := add_lt_add_left
      (hullSixTwoFour_p03_laurent_gt hb hc hr hf) ((9 : ℝ) / 2)
    norm_num at h ⊢
    simpa [add_comm] using h
  exact hStrict.trans_le hLower

/-! ## The orientation `e ≤ d`, in the `Q` fan -/

theorem hullSixTwoFour_p03_e_le_d_scalar
    {a b c d e f A Ap Cp x y z Fp J1 J2 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hed : e ≤ d) (hA : A = Ap - a + b)
    (hfAp : a + b ≤ f * Ap) (hcA : a + b ≤ c * A)
    (hCp : b + c + 1 ≤ Cp) (hax : c + d ≤ a * x)
    (hEar : e ≤ (e - d) * z - (f - e) * y)
    (hRec : a * y = d * J2 - e * J1)
    (hJ1 : 1 ≤ J1) (hHull : 1 ≤ -J2 + z + Fp) :
    (25 : ℝ) / 2 < Ap + Cp + x + y + z + Fp := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hy0 : 0 ≤ y := le_trans zero_le_one hy1
  have hz0 : 0 ≤ z := le_trans zero_le_one hz1
  let s := e - f
  have hs : 0 < s := by
    dsimp [s]
    by_contra hnot
    have hef : e - f ≤ 0 := le_of_not_gt hnot
    have hfirst : (e - f) * y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hef hy0
    have hsecond : 0 ≤ (d - e) * z :=
      mul_nonneg (sub_nonneg.mpr hed) hz0
    nlinarith [hEar]
  have hY : d ≤ s * y := by
    have hmul : d - e ≤ (d - e) * z := by
      have := mul_le_mul_of_nonneg_left hz1 (sub_nonneg.mpr hed)
      simpa using this
    dsimp [s]
    nlinarith [hEar]
  have hyLower : d / s ≤ y := by
    apply (div_le_iff₀ hs).2
    simpa [mul_comm] using hY

  have heJ : e ≤ e * J1 := by
    simpa using mul_le_mul_of_nonneg_left hJ1 (le_of_lt he)
  have hRecUpper : a * y + e ≤ d * J2 := by
    linarith [hRec, heJ]
  have hJ2Upper : J2 ≤ z + Fp - 1 := by linarith
  have hdJ : d * J2 ≤ d * (z + Fp - 1) :=
    mul_le_mul_of_nonneg_left hJ2Upper (le_of_lt hd)
  have haY : a * (d / s) ≤ a * y :=
    mul_le_mul_of_nonneg_left hyLower (le_of_lt ha)
  have hRaw : a * (d / s) + e ≤ d * (z + Fp - 1) := by
    linarith
  have hShape : a * (d / s) + e = d * (a / s + e / d) := by
    field_simp [hs.ne', hd.ne'] <;> ring
  have hZF : 1 + a / s + e / d ≤ z + Fp := by
    rw [hShape] at hRaw
    have hdiv := le_of_mul_le_mul_left hRaw hd
    linarith

  have hApLeft : (a + b) / f ≤ Ap := by
    apply (div_le_iff₀ hf).2
    simpa [mul_comm] using hfAp
  have hApRight : (a + b) / c + a - b ≤ Ap := by
    have hdiv : (a + b) / c ≤ A := by
      apply (div_le_iff₀ hc).2
      simpa [mul_comm] using hcA
    rw [hA] at hdiv
    linarith
  have hApAvg :
      ((a + b) / f + ((a + b) / c + a - b)) / 2 ≤ Ap := by
    linarith
  have hApAvg' :
      a / (2 * f) + b / (2 * f) + a / (2 * c) + b / (2 * c) +
          a / 2 - b / 2 ≤ Ap := by
    calc
      a / (2 * f) + b / (2 * f) + a / (2 * c) + b / (2 * c) +
            a / 2 - b / 2 =
          ((a + b) / f + ((a + b) / c + a - b)) / 2 := by
            field_simp [hc.ne', hf.ne']
            ring
      _ ≤ Ap := hApAvg
  have hxLower : (c + d) / a ≤ x := by
    apply (div_le_iff₀ ha).2
    simpa [mul_comm] using hax
  have hxLower' : c / a + d / a ≤ x := by
    calc
      c / a + d / a = (c + d) / a := by ring
      _ ≤ x := hxLower

  have hbHalf : (1 : ℝ) / 2 ≤ b / 2 := by linarith
  have hbF : 1 / (2 * f) ≤ b / (2 * f) := by
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * f)).2
    exact hb1
  have hbC : 1 / (2 * c) ≤ b / (2 * c) := by
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * c)).2
    exact hb1
  have hdA : f / a + s / a ≤ d / a := by
    have hfs : f + s ≤ d := by dsimp [s]; linarith
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right ha).2 hfs
  have hReciprocal : 2 ≤ e / d + d / e := by
    field_simp [hd.ne', he.ne']
    nlinarith [sq_nonneg (d - e)]
  have hdS : d / e + f / s ≤ d / s := by
    have hshape : d / s - (d / e + f / s) =
        f * (d - e) / (s * e) := by
      field_simp [hs.ne', he.ne']
      dsimp [s]
      ring
    have hnonneg : 0 ≤ f * (d - e) / (s * e) := by positivity
    linarith

  have hLower : (9 : ℝ) / 2 +
      hullSixTwoFour_p03Laurent a f s c ≤
        Ap + Cp + x + y + z + Fp := by
    dsimp [hullSixTwoFour_p03Laurent]
    linarith [hApAvg', hCp, hxLower', hyLower, hZF,
      hbHalf, hbF, hbC, hdA, hReciprocal, hdS]
  have hStrict : (25 : ℝ) / 2 < (9 : ℝ) / 2 +
      hullSixTwoFour_p03Laurent a f s c := by
    have h := add_lt_add_left
      (hullSixTwoFour_p03_laurent_gt ha hf hs hc) ((9 : ℝ) / 2)
    norm_num at h ⊢
    simpa [add_comm] using h
  exact hStrict.trans_le hLower

end Heilbronn8.Survivors.Join
