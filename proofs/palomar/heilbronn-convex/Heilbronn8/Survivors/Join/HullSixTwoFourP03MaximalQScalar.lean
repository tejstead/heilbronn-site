import Heilbronn8.Survivors.Join.HullSixTwoFourP03Y13PosLeScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourStrictCounterexampleAMGM

/-!
# Scalar closures for the `p = (0,3)` maximal-`q` frontier

The positive endpoint branch reuses the two q-blind scalar closures already
available for the two height orders.  This file supplies the two negative
endpoint closures.  Their geometric input is summarized by the strengthened
far transition `b * e + e * f + e + f <= b * E2`; no additional `Q`-chord
sign is present in either API.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.Survivors.Join

open scoped BigOperators

/-! ## Negative endpoint, height order `d <= e` -/

noncomputable def hullSixTwoFour_p03Y13NegHighLaurent
    (b c r : ℝ) : ℝ :=
  r + b / c + b / r + c / r + 2 * c / b + 2 * r / b + 1 / b

noncomputable def hullSixTwoFour_p03Y13NegHighTerm
    (b c r : ℝ) : Fin 7 → ℝ :=
  ![r, b / c, b / r, c / r, 2 * c / b, 2 * r / b, 1 / b]

def hullSixTwoFour_p03Y13NegHighWeight : Fin 7 → ℕ :=
  ![1, 2, 1, 1, 1, 1, 1]

theorem hullSixTwoFour_p03Y13NegHighWeight_pos
    (i : Fin 7) : 0 < hullSixTwoFour_p03Y13NegHighWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_p03Y13NegHighWeight]

theorem hullSixTwoFour_p03Y13NegHighWeight_sum :
    ∑ i, hullSixTwoFour_p03Y13NegHighWeight i = 8 := by
  norm_num [hullSixTwoFour_p03Y13NegHighWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_p03Y13NegHighTerm_nonneg
    {b c r : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (i : Fin 7) :
    0 ≤ hullSixTwoFour_p03Y13NegHighTerm b c r i := by
  fin_cases i <;> simp [hullSixTwoFour_p03Y13NegHighTerm] <;> positivity

theorem hullSixTwoFour_p03Y13NegHighTerm_sum
    (b c r : ℝ) :
    ∑ i, hullSixTwoFour_p03Y13NegHighTerm b c r i =
      hullSixTwoFour_p03Y13NegHighLaurent b c r := by
  simp [hullSixTwoFour_p03Y13NegHighTerm,
    hullSixTwoFour_p03Y13NegHighLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_p03Y13NegHighTerm_product
    {b c r : ℝ} (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    (∏ i,
        (hullSixTwoFour_p03Y13NegHighTerm b c r i /
          (hullSixTwoFour_p03Y13NegHighWeight i : ℝ)) ^
            hullSixTwoFour_p03Y13NegHighWeight i) = 1 := by
  simp [hullSixTwoFour_p03Y13NegHighTerm,
    hullSixTwoFour_p03Y13NegHighWeight, Fin.prod_univ_succ]
  field_simp [hb.ne', hc.ne', hr.ne'] <;> ring

theorem hullSixTwoFour_p03Y13NegHigh_laurent_ge
    {b c r : ℝ} (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    (8 : ℝ) ≤ hullSixTwoFour_p03Y13NegHighLaurent b c r := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_p03Y13NegHighWeight
    (hullSixTwoFour_p03Y13NegHighTerm b c r)
    hullSixTwoFour_p03Y13NegHighWeight_pos
    (hullSixTwoFour_p03Y13NegHighTerm_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt hr))
  rw [hullSixTwoFour_p03Y13NegHighWeight_sum,
    hullSixTwoFour_p03Y13NegHighTerm_product hb hc hr,
    hullSixTwoFour_p03Y13NegHighTerm_sum b c r] at hamgm
  norm_num at hamgm ⊢
  exact hamgm

/-- Negative-endpoint scalar closure in the height order `d <= e`. -/
theorem hullSixTwoFour_p03Y13Neg_d_le_e_scalar
    {a b c d e f A C E0 E1 E2 F X11 X12 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hE01 : 1 ≤ E0) (hE11 : 1 ≤ E1)
    (hde : d ≤ e) (hcA : a + b ≤ c * A)
    (hbE2Strong : b * e + e * f + e + f ≤ b * E2)
    (hF : a + f + 1 ≤ F)
    (hEar : d ≤ (d - c) * E1 - (e - d) * E0)
    (hRec : b * E1 = e * X11 - d * X12)
    (hX12 : 1 ≤ X12) (hHull : 1 ≤ C + E0 - X11) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hE00 : 0 ≤ E0 := le_trans zero_le_one hE01
  have hE10 : 0 ≤ E1 := le_trans zero_le_one hE11
  let r : ℝ := d - c
  have hr : 0 < r := by
    dsimp [r]
    by_contra hnot
    have hdc : d - c ≤ 0 := le_of_not_gt hnot
    have hfirst : (d - c) * E1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdc hE10
    have hsecond : 0 ≤ (e - d) * E0 :=
      mul_nonneg (sub_nonneg.mpr hde) hE00
    nlinarith
  have hEarReduced : e ≤ r * E1 := by
    have hmul : e - d ≤ (e - d) * E0 := by
      simpa using mul_le_mul_of_nonneg_left hE01 (sub_nonneg.mpr hde)
    dsimp [r]
    nlinarith [hEar]
  have hE1Lower : e / r ≤ E1 :=
    (div_le_iff₀ hr).2 (by simpa [mul_comm] using hEarReduced)

  have hdX12 : d ≤ d * X12 := by
    simpa using mul_le_mul_of_nonneg_left hX12 (le_of_lt hd)
  have hRecLower : b * E1 + d ≤ e * X11 := by
    linarith [hRec, hdX12]
  have hX11Upper : X11 ≤ C + E0 - 1 := by linarith [hHull]
  have heX11 : e * X11 ≤ e * (C + E0 - 1) :=
    mul_le_mul_of_nonneg_left hX11Upper (le_of_lt he)
  have hbE : b * (e / r) ≤ b * E1 :=
    mul_le_mul_of_nonneg_left hE1Lower (le_of_lt hb)
  have hRawCentral : b * (e / r) + d ≤ e * (C + E0 - 1) := by
    linarith
  have hCentralShape :
      b * (e / r) + d = e * (b / r + d / e) := by
    field_simp [hr.ne', he.ne'] <;> ring
  have hCentral : 1 + b / r + d / e ≤ C + E0 := by
    rw [hCentralShape] at hRawCentral
    have hdiv := le_of_mul_le_mul_left hRawCentral he
    linarith

  have hALower : (a + b) / c ≤ A :=
    (div_le_iff₀ hc).2 (by simpa [mul_comm] using hcA)
  have hE2Lower : e + (e * f + e + f) / b ≤ E2 := by
    have hdiv : (b * e + e * f + e + f) / b ≤ E2 :=
      (div_le_iff₀ hb).2 (by simpa [mul_comm] using hbE2Strong)
    convert hdiv using 1 <;> field_simp [hb.ne'] <;> ring
  have hRaw :
      a + f + e + 2 + (a + b) / c + (b + e) / r + d / e +
          (e * f + e + f) / b ≤
        A + C + E0 + E1 + E2 + F := by
    rw [show (b + e) / r = b / r + e / r by ring]
    nlinarith [hALower, hCentral, hE1Lower, hE2Lower, hF]

  have hecr : c + r ≤ e := by dsimp [r]; linarith
  have hAc : (1 + b) / c ≤ (a + b) / c :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  have hAc' : 1 / c + b / c ≤ (a + b) / c := by
    calc
      1 / c + b / c = (1 + b) / c := by ring
      _ ≤ (a + b) / c := hAc
  have hbr : (b + c + r) / r ≤ (b + e) / r :=
    (div_le_div_iff_of_pos_right hr).2 (by linarith)
  have hbr' : b / r + c / r + 1 ≤ (b + e) / r := by
    calc
      b / r + c / r + 1 = (b + c + r) / r := by
        field_simp [hr.ne']
      _ ≤ (b + e) / r := hbr
  have hef : e ≤ e * f := by
    simpa using mul_le_mul_of_nonneg_left hf1 (le_of_lt he)
  have hfarNum : 2 * c + 2 * r + 1 ≤ e * f + e + f := by
    nlinarith [hecr, hef]
  have hfar : (2 * c + 2 * r + 1) / b ≤
      (e * f + e + f) / b :=
    (div_le_div_iff_of_pos_right hb).2 hfarNum
  have hfar' : 2 * c / b + 2 * r / b + 1 / b ≤
      (e * f + e + f) / b := by
    calc
      2 * c / b + 2 * r / b + 1 / b =
          (2 * c + 2 * r + 1) / b := by ring
      _ ≤ (e * f + e + f) / b := hfar
  have hdRatio : 0 ≤ d / e := by positivity
  have hLower :
      5 + c + 1 / c +
          hullSixTwoFour_p03Y13NegHighLaurent b c r ≤
        A + C + E0 + E1 + E2 + F := by
    dsimp [hullSixTwoFour_p03Y13NegHighLaurent]
    nlinarith [hRaw, hAc', hbr', hfar', hdRatio]
  have hLaurent := hullSixTwoFour_p03Y13NegHigh_laurent_ge hb hc hr
  have hcNonneg : 0 ≤ c + 1 / c := by positivity
  nlinarith

/-! ## Negative endpoint, height order `e <= d` -/

noncomputable def hullSixTwoFour_p03Y13NegLowLaurent
    (b f s : ℝ) : ℝ :=
  s / f + 3 * f / b + 2 * s / b + b / s + f / s

noncomputable def hullSixTwoFour_p03Y13NegLowTerm
    (b f s : ℝ) : Fin 5 → ℝ :=
  ![s / f, 3 * f / b, 2 * s / b, b / s, f / s]

def hullSixTwoFour_p03Y13NegLowWeight : Fin 5 → ℕ :=
  ![2, 1, 1, 2, 1]

noncomputable def hullSixTwoFour_p03Y13NegLowConstant : ℝ :=
  3 / 8

theorem hullSixTwoFour_p03Y13NegLowWeight_pos
    (i : Fin 5) : 0 < hullSixTwoFour_p03Y13NegLowWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFour_p03Y13NegLowWeight]

theorem hullSixTwoFour_p03Y13NegLowWeight_sum :
    ∑ i, hullSixTwoFour_p03Y13NegLowWeight i = 7 := by
  norm_num [hullSixTwoFour_p03Y13NegLowWeight, Fin.sum_univ_succ]

theorem hullSixTwoFour_p03Y13NegLowTerm_nonneg
    {b f s : ℝ} (hb : 0 ≤ b) (hf : 0 ≤ f) (hs : 0 ≤ s)
    (i : Fin 5) :
    0 ≤ hullSixTwoFour_p03Y13NegLowTerm b f s i := by
  fin_cases i <;> simp [hullSixTwoFour_p03Y13NegLowTerm] <;> positivity

theorem hullSixTwoFour_p03Y13NegLowTerm_sum
    (b f s : ℝ) :
    ∑ i, hullSixTwoFour_p03Y13NegLowTerm b f s i =
      hullSixTwoFour_p03Y13NegLowLaurent b f s := by
  simp [hullSixTwoFour_p03Y13NegLowTerm,
    hullSixTwoFour_p03Y13NegLowLaurent, Fin.sum_univ_succ] <;> ring

theorem hullSixTwoFour_p03Y13NegLowTerm_product
    {b f s : ℝ} (hb : 0 < b) (hf : 0 < f) (hs : 0 < s) :
    (∏ i,
        (hullSixTwoFour_p03Y13NegLowTerm b f s i /
          (hullSixTwoFour_p03Y13NegLowWeight i : ℝ)) ^
            hullSixTwoFour_p03Y13NegLowWeight i) =
      hullSixTwoFour_p03Y13NegLowConstant := by
  simp [hullSixTwoFour_p03Y13NegLowTerm,
    hullSixTwoFour_p03Y13NegLowWeight, Fin.prod_univ_succ,
    hullSixTwoFour_p03Y13NegLowConstant]
  field_simp [hb.ne', hf.ne', hs.ne'] <;> ring

theorem hullSixTwoFour_p03Y13NegLowConstant_pos :
    0 < hullSixTwoFour_p03Y13NegLowConstant := by
  norm_num [hullSixTwoFour_p03Y13NegLowConstant]

theorem hullSixTwoFour_p03Y13NegLow_root_gap :
    (9 : ℝ) / 2 <
      7 * hullSixTwoFour_p03Y13NegLowConstant ^ ((7 : ℝ)⁻¹) := by
  have hpow : ((9 : ℝ) / 14) ^ 7 <
      hullSixTwoFour_p03Y13NegLowConstant := by
    norm_num [hullSixTwoFour_p03Y13NegLowConstant]
  have hpowRpow : ((9 : ℝ) / 14) ^ (7 : ℝ) <
      hullSixTwoFour_p03Y13NegLowConstant := by
    change ((9 : ℝ) / 14) ^ ((7 : ℕ) : ℝ) <
      hullSixTwoFour_p03Y13NegLowConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (9 : ℝ) / 14 <
      hullSixTwoFour_p03Y13NegLowConstant ^ ((7 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFour_p03Y13NegLowConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFour_p03Y13NegLow_laurent_gt
    {b f s : ℝ} (hb : 0 < b) (hf : 0 < f) (hs : 0 < s) :
    (9 : ℝ) / 2 < hullSixTwoFour_p03Y13NegLowLaurent b f s := by
  have hamgm := Heilbronn8.scalar_weighted_amgm_nat
    hullSixTwoFour_p03Y13NegLowWeight
    (hullSixTwoFour_p03Y13NegLowTerm b f s)
    hullSixTwoFour_p03Y13NegLowWeight_pos
    (hullSixTwoFour_p03Y13NegLowTerm_nonneg
      (le_of_lt hb) (le_of_lt hf) (le_of_lt hs))
  rw [hullSixTwoFour_p03Y13NegLowWeight_sum,
    hullSixTwoFour_p03Y13NegLowTerm_product hb hf hs,
    hullSixTwoFour_p03Y13NegLowTerm_sum b f s] at hamgm
  exact hullSixTwoFour_p03Y13NegLow_root_gap.trans_le hamgm

/-- Negative-endpoint scalar closure in the height order `e <= d`. -/
theorem hullSixTwoFour_p03Y13Neg_e_le_d_scalar
    {a b d e f A C E0 E1 E2 F X11 X12 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hd1 : 1 ≤ d)
    (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A) (hE11 : 1 ≤ E1) (hE21 : 1 ≤ E2)
    (hed : e ≤ d)
    (hbE2Strong : b * e + e * f + e + f ≤ b * E2)
    (hF : a + f + 1 ≤ F)
    (hEar : e ≤ (e - f) * E1 + (e - d) * E2)
    (hRec : b * E1 = e * X11 - d * X12)
    (hX12 : 1 ≤ X12) (hHull : 1 ≤ C + E0 - X11) :
    (25 : ℝ) / 2 < A + C + E0 + E1 + E2 + F := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hE10 : 0 ≤ E1 := le_trans zero_le_one hE11
  have hE20 : 0 ≤ E2 := le_trans zero_le_one hE21
  let s : ℝ := e - f
  have hs : 0 < s := by
    dsimp [s]
    by_contra hnot
    have hef : e - f ≤ 0 := le_of_not_gt hnot
    have hfirst : (e - f) * E1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hef hE10
    have hsecond : (e - d) * E2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hed) hE20
    nlinarith
  have hEarReduced : e ≤ s * E1 := by
    have hsecond : (e - d) * E2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hed) hE20
    dsimp [s]
    nlinarith [hEar]
  have hE1Lower : e / s ≤ E1 :=
    (div_le_iff₀ hs).2 (by simpa [mul_comm] using hEarReduced)

  have hdX12 : d ≤ d * X12 := by
    simpa using mul_le_mul_of_nonneg_left hX12 (le_of_lt hd)
  have hX11Upper : X11 ≤ C + E0 - 1 := by linarith [hHull]
  have heX11 : e * X11 ≤ e * (C + E0 - 1) :=
    mul_le_mul_of_nonneg_left hX11Upper (le_of_lt he)
  have hCentral0 : b * E1 + 2 * e ≤ e * (C + E0) := by
    nlinarith [hRec, hdX12, heX11, hed]
  have hbe : b * e ≤ b * (s * E1) :=
    mul_le_mul_of_nonneg_left hEarReduced (le_of_lt hb)
  have hCentralScaled : e * (b + 2 * s) ≤ e * (s * (C + E0)) := by
    calc
      e * (b + 2 * s) = b * e + 2 * s * e := by ring
      _ ≤ b * (s * E1) + 2 * s * e := by linarith
      _ = s * (b * E1 + 2 * e) := by ring
      _ ≤ s * (e * (C + E0)) :=
        mul_le_mul_of_nonneg_left hCentral0 (le_of_lt hs)
      _ = e * (s * (C + E0)) := by ring
  have hCentralScaled' : b + 2 * s ≤ s * (C + E0) :=
    le_of_mul_le_mul_left hCentralScaled he
  have hCentral : 2 + b / s ≤ C + E0 := by
    have hdiv : (2 * s + b) / s ≤ C + E0 :=
      (div_le_iff₀ hs).2 (by
        simpa [add_comm, mul_comm] using hCentralScaled')
    convert hdiv using 1 <;> field_simp [hs.ne'] <;> ring

  have hE2Lower : e + (e * f + e + f) / b ≤ E2 := by
    have hdiv : (b * e + e * f + e + f) / b ≤ E2 :=
      (div_le_iff₀ hb).2 (by simpa [mul_comm] using hbE2Strong)
    convert hdiv using 1 <;> field_simp [hb.ne'] <;> ring
  have hRaw :
      a + f + e + 4 + (b + e) / s + (e * f + e + f) / b ≤
        A + C + E0 + E1 + E2 + F := by
    rw [show (b + e) / s = b / s + e / s by ring]
    nlinarith [hA1, hCentral, hE1Lower, hE2Lower, hF]

  have hSF : s / f ≤ s := by
    exact (div_le_iff₀ hf).2 (by
      have hmul : s ≤ s * f := by
        simpa using mul_le_mul_of_nonneg_left hf1 (le_of_lt hs)
      simpa [mul_comm] using hmul)
  have hStrongNum : 3 * f + 2 * s ≤ e * f + e + f := by
    have heq : e = f + s := by dsimp [s]; ring
    rw [heq]
    have hmul : 0 ≤ (f - 1) * (f + s) := by positivity
    nlinarith
  have hStrongFrac : (3 * f + 2 * s) / b ≤
      (e * f + e + f) / b :=
    (div_le_div_iff_of_pos_right hb).2 hStrongNum
  have hStrongFrac' : 3 * f / b + 2 * s / b ≤
      (e * f + e + f) / b := by
    calc
      3 * f / b + 2 * s / b = (3 * f + 2 * s) / b := by ring
      _ ≤ (e * f + e + f) / b := hStrongFrac
  have hRatioShape : (b + e) / s = b / s + f / s + 1 := by
    rw [show e = f + s by dsimp [s]; ring]
    field_simp [hs.ne']
    ring
  have hBase : 8 + s / f ≤ a + 2 * f + s + 5 := by
    nlinarith
  have hLower :
      8 + hullSixTwoFour_p03Y13NegLowLaurent b f s ≤
        A + C + E0 + E1 + E2 + F := by
    dsimp [hullSixTwoFour_p03Y13NegLowLaurent]
    have heq : e = f + s := by dsimp [s]; ring
    nlinarith [hRaw, hStrongFrac', hRatioShape, hBase, heq]
  have hLaurent := hullSixTwoFour_p03Y13NegLow_laurent_gt hb hf hs
  nlinarith

end Heilbronn8.Survivors.Join
