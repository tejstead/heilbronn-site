import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the shifted-right q-blind `q = 33` chamber

The exact table adapter supplies a shifted first lower edge
`1 <= x + c - d`, three separated transition bounds, and the two lower
hull ears.  The ears force a common height floor.  After the substitutions

```text
s = 1 / (y - 1),       v = x + c - (1 + s),
```

the remaining analytic kernel is bounded by one square-root estimate, a
three-term AM--GM inequality, and two explicit rational SOS certificates.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

open scoped BigOperators

/-! ## A small three-term AM--GM seam -/

private def hullSixTwoFourQ33AMGMWeight : Fin 3 → ℕ :=
  ![1, 1, 1]

private noncomputable def hullSixTwoFourQ33AMGMTerm
    (u v w : ℝ) : Fin 3 → ℝ :=
  ![u, v, w]

private theorem hullSixTwoFourQ33_amgmWeight_pos
    (i : Fin 3) : 0 < hullSixTwoFourQ33AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixTwoFourQ33AMGMWeight]

private theorem hullSixTwoFourQ33_amgmWeight_sum :
    ∑ i, hullSixTwoFourQ33AMGMWeight i = 3 := by
  norm_num [hullSixTwoFourQ33AMGMWeight, Fin.sum_univ_succ]

private theorem hullSixTwoFourQ33_amgmTerm_nonneg
    {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (i : Fin 3) :
    0 ≤ hullSixTwoFourQ33AMGMTerm u v w i := by
  fin_cases i <;>
    simp [hullSixTwoFourQ33AMGMTerm, hu, hv, hw]

private theorem hullSixTwoFourQ33_amgmTerm_sum
    (u v w : ℝ) :
    ∑ i, hullSixTwoFourQ33AMGMTerm u v w i = u + v + w := by
  simp [hullSixTwoFourQ33AMGMTerm, Fin.sum_univ_succ] <;> ring

private theorem hullSixTwoFourQ33_amgmTerm_product
    (u v w : ℝ) :
    (∏ i,
        (hullSixTwoFourQ33AMGMTerm u v w i /
          (hullSixTwoFourQ33AMGMWeight i : ℝ)) ^
            hullSixTwoFourQ33AMGMWeight i) =
      u * v * w := by
  simp [hullSixTwoFourQ33AMGMTerm, hullSixTwoFourQ33AMGMWeight,
    Fin.prod_univ_succ] <;> ring

private theorem hullSixTwoFourQ33_three_term_amgm
    {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hprod : u * v * w = 1) :
    (3 : ℝ) ≤ u + v + w := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourQ33AMGMWeight
    (hullSixTwoFourQ33AMGMTerm u v w)
    hullSixTwoFourQ33_amgmWeight_pos
    (hullSixTwoFourQ33_amgmTerm_nonneg hu hv hw)
  rw [hullSixTwoFourQ33_amgmWeight_sum,
    hullSixTwoFourQ33_amgmTerm_product, hprod] at hamgm
  norm_num at hamgm
  rw [hullSixTwoFourQ33_amgmTerm_sum] at hamgm
  exact hamgm

/-! ## The two rational pieces of the analytic kernel -/

private theorem hullSixTwoFourQ33_sqrt_rational_lower
    {s : ℝ} (hs : 0 < s) :
    60 * (s + 2) / (9 * s + 43) ≤
      2 * Real.sqrt (s + 2) := by
  have hs2 : 0 ≤ s + 2 := by linarith
  have hden : 0 < 9 * s + 43 := by linarith
  have hsqrtSq : (Real.sqrt (s + 2)) ^ 2 = s + 2 :=
    Real.sq_sqrt hs2
  have hlinear :
      30 * Real.sqrt (s + 2) ≤ 9 * s + 43 := by
    apply (sq_le_sq₀ (by positivity) (le_of_lt hden)).mp
    nlinarith [sq_nonneg (9 * s - 7)]
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Real.sqrt_nonneg (s + 2)))
  apply (div_le_iff₀ hden).2
  nlinarith

private theorem hullSixTwoFourQ33_reciprocal_lower
    {s v : ℝ} (hs : 0 < s) (hv : 0 < v) :
    (25 : ℝ) / 32 - 125 * s / 1152 - 625 * v / 2304 ≤
      1 / (v * (v + s)) := by
  let U : ℝ := 5 * v / 8
  let W : ℝ := 5 * (v + s) / 12
  let T : ℝ := 1 / (U * W)
  have hvs : 0 < v + s := by linarith
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hT : 0 ≤ T := by
    dsimp [T, U, W]
    positivity
  have hprod : U * W * T = 1 := by
    dsimp [T, U, W]
    field_simp [hv.ne', hvs.ne'] <;> ring
  have hamgm := hullSixTwoFourQ33_three_term_amgm hU hW hT hprod
  have hgap : 0 ≤ U + W + T - 3 := by linarith
  have hscaled : 0 ≤ ((25 : ℝ) / 96) * (U + W + T - 3) :=
    mul_nonneg (by norm_num) hgap
  have hidentity :
      ((25 : ℝ) / 96) * (U + W + T - 3) =
        1 / (v * (v + s)) -
          ((25 : ℝ) / 32 - 125 * s / 1152 -
            625 * v / 2304) := by
    dsimp [T, U, W]
    field_simp [hv.ne', hvs.ne'] <;> ring
  rw [hidentity] at hscaled
  linarith

private noncomputable def hullSixTwoFourQ33SPoly (s : ℝ) : ℝ :=
  1155375 * s ^ 3 + 7285169 * s ^ 2 - 14271012 * s + 6192000

private noncomputable def hullSixTwoFourQ33VPoly (v : ℝ) : ℝ :=
  209875 * v ^ 2 - 695232 * v + 576000

private theorem hullSixTwoFourQ33_sPoly_pos
    {s : ℝ} (hs : 0 < s) :
    0 < hullSixTwoFourQ33SPoly s := by
  have hfactor : 0 < 1155375 * s + 9179984 := by positivity
  have hproduct :
      0 ≤ (50 * s - 41) ^ 2 * (1155375 * s + 9179984) :=
    mul_nonneg (sq_nonneg _) (le_of_lt hfactor)
  have htail : 0 < 18219025 * s + 48446896 := by positivity
  have hidentity :
      2500 * hullSixTwoFourQ33SPoly s =
        (50 * s - 41) ^ 2 * (1155375 * s + 9179984) +
          18219025 * s + 48446896 := by
    unfold hullSixTwoFourQ33SPoly
    ring
  nlinarith

private theorem hullSixTwoFourQ33_vPoly_pos
    (v : ℝ) :
    0 < hullSixTwoFourQ33VPoly v := by
  have hsq : 0 ≤ (209875 * v - 347616) ^ 2 := sq_nonneg _
  have hidentity :
      209875 * hullSixTwoFourQ33VPoly v =
        (209875 * v - 347616) ^ 2 + 51116544 := by
    unfold hullSixTwoFourQ33VPoly
    ring
  nlinarith

private theorem hullSixTwoFourQ33_sPart_gt
    {s : ℝ} (hs : 0 < s) :
    (21219 : ℝ) / 4000 <
      s + 1 / s + 60 * (s + 2) / (9 * s + 43) -
        125 * s / 1152 := by
  have hlinear : 0 < 9 * s + 43 := by linarith
  have hden : 0 < 144000 * s * (9 * s + 43) := by positivity
  have hidentity :
      s + 1 / s + 60 * (s + 2) / (9 * s + 43) -
            125 * s / 1152 - (21219 : ℝ) / 4000 =
        hullSixTwoFourQ33SPoly s /
          (144000 * s * (9 * s + 43)) := by
    unfold hullSixTwoFourQ33SPoly
    field_simp [hs.ne', hlinear.ne'] <;> ring
  have hpositive :
      0 < hullSixTwoFourQ33SPoly s /
        (144000 * s * (9 * s + 43)) :=
    div_pos (hullSixTwoFourQ33_sPoly_pos hs) hden
  nlinarith

private theorem hullSixTwoFourQ33_vPart_gt
    {v : ℝ} (hv : 0 < v) :
    (1207 : ℝ) / 500 <
      v + 2 / v - 625 * v / 2304 := by
  have hden : 0 < 288000 * v := by positivity
  have hidentity :
      v + 2 / v - 625 * v / 2304 - (1207 : ℝ) / 500 =
        hullSixTwoFourQ33VPoly v / (288000 * v) := by
    unfold hullSixTwoFourQ33VPoly
    field_simp [hv.ne'] <;> ring
  have hpositive :
      0 < hullSixTwoFourQ33VPoly v / (288000 * v) :=
    div_pos (hullSixTwoFourQ33_vPoly_pos v) hden
  nlinarith

private theorem hullSixTwoFourQ33_kernel
    {s v : ℝ} (hs : 0 < s) (hv1 : 1 ≤ v) :
    (21 : ℝ) / 2 <
      2 + s + 1 / s + v + 2 * Real.sqrt (s + 2) +
        2 / v + 1 / (v * (v + s)) := by
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  have hsqrt := hullSixTwoFourQ33_sqrt_rational_lower hs
  have hreciprocal := hullSixTwoFourQ33_reciprocal_lower hs hv
  have hsPart := hullSixTwoFourQ33_sPart_gt hs
  have hvPart := hullSixTwoFourQ33_vPart_gt hv
  have hconstant :
      (21 : ℝ) / 2 =
        2 + (25 : ℝ) / 32 + (21219 : ℝ) / 4000 +
          (1207 : ℝ) / 500 := by
    norm_num
  rw [hconstant]
  nlinarith

/-! ## Ear and transition reductions -/

private theorem hullSixTwoFourQ33_ears_height_floor
    {c d e f x y z : ℝ}
    (hc1 : 1 ≤ c) (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    1 < y ∧ y / (y - 1) ≤ d ∧ y / (y - 1) ≤ e := by
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hy : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  by_cases hde : d ≤ e
  · have hnonneg : 0 ≤ (e - d) * x :=
      mul_nonneg (sub_nonneg.mpr hde) (le_of_lt hx)
    have hdrop : d ≤ (d - c) * y := by nlinarith
    have hcd : c < d := by
      by_contra hnot
      have hgap : d - c ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hmul : (d - c) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hgap (le_of_lt hy)
      nlinarith
    have hdgt : 1 < d := lt_of_le_of_lt hc1 hcd
    have hcompare : (d - c) * y ≤ (d - 1) * y :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hy)
    have hdy : d ≤ (d - 1) * y := hdrop.trans hcompare
    have hygt : 1 < y := by
      by_contra hnot
      have hyle : y ≤ 1 := le_of_not_gt hnot
      have hmul : (d - 1) * y ≤ (d - 1) * 1 :=
        mul_le_mul_of_nonneg_left hyle (by linarith)
      nlinarith
    have hratio : y / (y - 1) ≤ d := by
      apply (div_le_iff₀ (sub_pos.mpr hygt)).2
      nlinarith
    exact ⟨hygt, hratio, hratio.trans hde⟩
  · have hed : e < d := lt_of_not_ge hde
    have hnegative : (e - d) * z < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hed) hz
    have heStrict : e < (e - f) * y := by nlinarith
    have hef : f < e := by
      by_contra hnot
      have hgap : e - f ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hmul : (e - f) * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hgap (le_of_lt hy)
      nlinarith
    have hegt : 1 < e := lt_of_le_of_lt hf1 hef
    have hcompare : (e - f) * y ≤ (e - 1) * y :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hy)
    have hey : e < (e - 1) * y := heStrict.trans_le hcompare
    have hygt : 1 < y := by
      by_contra hnot
      have hyle : y ≤ 1 := le_of_not_gt hnot
      have hmul : (e - 1) * y ≤ (e - 1) * 1 :=
        mul_le_mul_of_nonneg_left hyle (by linarith)
      nlinarith
    have hratio : y / (y - 1) < e := by
      apply (div_lt_iff₀ (sub_pos.mpr hygt)).2
      nlinarith
    exact ⟨hygt, le_of_lt (hratio.trans hed), le_of_lt hratio⟩

private theorem hullSixTwoFourQ33_two_sqrt_le_add
    {s r z : ℝ} (hs : 0 < s) (hr : 0 < r) (hz : 0 < z)
    (hprod : s + 2 ≤ r * z) :
    2 * Real.sqrt (s + 2) ≤ r + z := by
  have hs2 : 0 ≤ s + 2 := by linarith
  have hsqrtSq : (Real.sqrt (s + 2)) ^ 2 = s + 2 :=
    Real.sq_sqrt hs2
  have hamgmScaled :
      2 * Real.sqrt (s + 2) * r ≤ r ^ 2 + (s + 2) := by
    nlinarith [sq_nonneg (r - Real.sqrt (s + 2))]
  have hamgm :
      2 * Real.sqrt (s + 2) ≤ r + (s + 2) / r := by
    calc
      2 * Real.sqrt (s + 2) =
          (2 * Real.sqrt (s + 2) * r) / r := by
            field_simp [hr.ne']
      _ ≤ (r ^ 2 + (s + 2)) / r :=
        div_le_div_of_nonneg_right hamgmScaled (le_of_lt hr)
      _ = r + (s + 2) / r := by
        field_simp [hr.ne'] <;> ring
  have hquotient : (s + 2) / r ≤ z :=
    (div_le_iff₀ hr).2 (by simpa [mul_comm] using hprod)
  linarith

private theorem hullSixTwoFourQ33_A_lower
    {a b c d x A s v : ℝ}
    (ha0 : 0 ≤ a) (hc : 0 < c) (hx1 : 1 ≤ x)
    (hs : 0 < s) (hv1 : 1 ≤ v)
    (hvShape : v = x + c - (1 + s))
    (hdFloor : 1 + s ≤ d)
    (hw1 : 1 ≤ x + c - d)
    (hAtransition : a + b ≤ c * A)
    (hxTransition : c + d ≤ b * (x + c - d)) :
    (a + (1 + (1 + 2 * s) / v)) / (v + s) ≤ A := by
  let w : ℝ := x + c - d
  let C₀ : ℝ := v + s
  let K : ℝ := 1 + (1 + 2 * s) / v
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  have hw : 0 < w := lt_of_lt_of_le zero_lt_one (by simpa [w] using hw1)
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    linarith
  have hwv : w ≤ v := by
    dsimp [w]
    nlinarith
  have hC₀Shape : C₀ = x + c - 1 := by
    dsimp [C₀]
    nlinarith
  have hcC₀ : c ≤ C₀ := by nlinarith
  have hbLower : (c + d) / w ≤ b := by
    apply (div_le_iff₀ hw).2
    simpa [w] using hxTransition
  have hALower : (a + b) / c ≤ A := by
    exact (div_le_iff₀ hc).2
      (by simpa [mul_comm] using hAtransition)
  have hKShape : K = (v + 1 + 2 * s) / v := by
    dsimp [K]
    field_simp [hv.ne'] <;> ring
  have hfactor : 0 ≤ c * (v + 1 + 2 * s) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hwv hfactor
  have hKFirst : K * c * w ≤ c * (v + 1 + 2 * s) := by
    rw [hKShape]
    rw [show ((v + 1 + 2 * s) / v) * c * w =
      ((v + 1 + 2 * s) * c * w) / v by ring]
    apply (div_le_iff₀ hv).2
    nlinarith
  have hgap : 0 ≤ (1 + s) * (C₀ - c) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hcC₀)
  have hfirstIdentity :
      (c + 1 + s) * C₀ - c * (v + 1 + 2 * s) =
        (1 + s) * (C₀ - c) := by
    dsimp [C₀]
    ring
  have hKSecond :
      c * (v + 1 + 2 * s) ≤ (c + d) * C₀ := by
    have hleft : c * (v + 1 + 2 * s) ≤ (c + 1 + s) * C₀ := by
      nlinarith
    have hright : (c + 1 + s) * C₀ ≤ (c + d) * C₀ :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hC₀)
    exact hleft.trans hright
  have hKCross : K * (c * w) ≤ (c + d) * C₀ := by
    nlinarith [hKFirst, hKSecond]
  have hKDiv : K / C₀ ≤ (c + d) / (c * w) :=
    (div_le_div_iff₀ hC₀ (mul_pos hc hw)).2 hKCross
  have haDiv : a / C₀ ≤ a / c := by
    exact (div_le_div_iff₀ hC₀ hc).2
      (mul_le_mul_of_nonneg_left hcC₀ ha0)
  have hcombined :
      (a + K) / C₀ ≤ (a + (c + d) / w) / c := by
    have hsum := add_le_add haDiv hKDiv
    calc
      (a + K) / C₀ = a / C₀ + K / C₀ := by ring
      _ ≤ a / c + (c + d) / (c * w) := hsum
      _ = (a + (c + d) / w) / c := by
        field_simp [hc.ne', hw.ne'] <;> ring
  have hmiddle : (a + (c + d) / w) / c ≤ (a + b) / c :=
    div_le_div_of_nonneg_right (add_le_add_right hbLower a) (le_of_lt hc)
  have hresult : (a + K) / C₀ ≤ A :=
    hcombined.trans (hmiddle.trans hALower)
  simpa [K, C₀] using hresult

/-! ## Raw shifted-right scalar endpoint -/

theorem hullSixTwoFourQ33ShiftedRight_scalar
    {a b c d e f A Cfan x y z Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hCfan1 : 1 ≤ Cfan)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hFp1 : 1 ≤ Fp)
    (hxP1 : 1 ≤ x + c - d)
    (hAtransition : a + b ≤ c * A)
    (hxTransition : c + d ≤ b * (x + c - d))
    (hzTransition : e + f ≤ a * z)
    (hEar0 : d ≤ (d - c) * y - (e - d) * x)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    (25 : ℝ) / 2 <
      A + Cfan + x + y + z + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hheights := hullSixTwoFourQ33_ears_height_floor
    hc1 hd1 he1 hf1 hx1 hy1 hz1 hEar0 hEar1
  have hygt : 1 < y := hheights.1
  have hdRatio : y / (y - 1) ≤ d := hheights.2.1
  have heRatio : y / (y - 1) ≤ e := hheights.2.2

  let s : ℝ := 1 / (y - 1)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hyShape : y = 1 + 1 / s := by
    dsimp [s]
    field_simp [(sub_pos.mpr hygt).ne'] <;> ring
  have hDShape : y / (y - 1) = 1 + s := by
    dsimp [s]
    field_simp [(sub_pos.mpr hygt).ne'] <;> ring
  have hdFloor : 1 + s ≤ d := by
    rw [← hDShape]
    exact hdRatio
  have heFloor : 1 + s ≤ e := by
    rw [← hDShape]
    exact heRatio

  let v : ℝ := x + c - (1 + s)
  have hv1 : 1 ≤ v := by
    dsimp [v]
    nlinarith
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  let C₀ : ℝ := v + s
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    linarith
  let r : ℝ := max 1 ((s + 2) / z)
  let K : ℝ := 1 + (1 + 2 * s) / v

  have hsum : s + 2 ≤ e + f := by nlinarith
  have hratio : (s + 2) / z ≤ a := by
    apply (div_le_iff₀ hz).2
    nlinarith
  have hra : r ≤ a := by
    dsimp [r]
    exact max_le ha1 hratio
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact le_max_left 1 ((s + 2) / z)
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrz : s + 2 ≤ r * z := by
    exact (div_le_iff₀ hz).1 (by
      dsimp [r]
      exact le_max_right 1 ((s + 2) / z))

  have hALower : (a + K) / C₀ ≤ A := by
    have h := hullSixTwoFourQ33_A_lower
      (le_of_lt ha) hc hx1 hs hv1 (by rfl) hdFloor hxP1
      hAtransition hxTransition
    simpa [K, C₀] using h
  have hfrac : (r + K) / C₀ ≤ A := by
    have hnum : r + K ≤ a + K := add_le_add_left hra K
    have hdiv : (r + K) / C₀ ≤ (a + K) / C₀ :=
      div_le_div_of_nonneg_right hnum (le_of_lt hC₀)
    exact hdiv.trans hALower
  have hbase : 2 + s + 1 / s + v = x + y + c := by
    dsimp [v]
    rw [hyShape]
    ring
  have hraw :
      2 + s + 1 / s + v + z + r + (r + K) / C₀ ≤
        A + x + y + z + a + c := by
    nlinarith

  have hsqrt := hullSixTwoFourQ33_two_sqrt_le_add hs hr hz hrz
  have htailIdentity :
      (1 + K) / C₀ = 2 / v + 1 / (v * (v + s)) := by
    dsimp [K, C₀]
    field_simp [hv.ne', (show 0 < v + s by linarith).ne'] <;> ring
  have htail :
      2 / v + 1 / (v * (v + s)) ≤ (r + K) / C₀ := by
    rw [← htailIdentity]
    exact div_le_div_of_nonneg_right
      (add_le_add_left hr1 K) (le_of_lt hC₀)
  have hkernelLower :
      2 + s + 1 / s + v + 2 * Real.sqrt (s + 2) +
          2 / v + 1 / (v * (v + s)) ≤
        A + x + y + z + a + c := by
    nlinarith
  have hkernel := hullSixTwoFourQ33_kernel hs hv1
  have hcore : (21 : ℝ) / 2 < A + x + y + z + a + c :=
    hkernel.trans_le hkernelLower
  nlinarith

end Heilbronn8
