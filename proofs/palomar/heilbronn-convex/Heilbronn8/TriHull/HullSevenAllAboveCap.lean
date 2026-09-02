import Heilbronn8.TriHull.HullSevenTransferProducer

/-!
# Closure of the hull-seven all-above-cap branch

This is the recurrence-free `rho/x/j` argument promised by
`HullSevenTransferProducer`.  Put `x=s+u`, `j=s*u`, and

`g rho = 2 * (rho^2 - 1 + (rho+1) * sqrt (rho^2+1))`.

The cap identity and radial lower bound imply `g rho <= x`; the interval
condition implies `q-1 >= 4/x`.  Below the sharp radius the resulting
reciprocal radial expression is antitone, while above it the already-proved
central radial expression is monotone.
-/

namespace Heilbronn8.TriHull

noncomputable def hullSevenAllAboveSumLower (r : ℝ) : ℝ :=
  2 * (r ^ 2 - 1 + (r + 1) * Real.sqrt (r ^ 2 + 1))

noncomputable def hullSevenAllAboveRadial (r : ℝ) : ℝ :=
  6 + 1 / r ^ 2 + hullSevenAllAboveSumLower r +
    4 / hullSevenAllAboveSumLower r

private lemma hullSevenAllAboveSumLower_pos {r : ℝ} (hr : 0 < r) :
    0 < hullSevenAllAboveSumLower r := by
  have hs0 := Real.sqrt_nonneg (r ^ 2 + 1)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ r ^ 2 + 1)
  have hsqrtOne : 1 < Real.sqrt (r ^ 2 + 1) := by
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hsqrtOne
    (add_pos hr (by norm_num : (0 : ℝ) < 1))
  unfold hullSevenAllAboveSumLower
  nlinarith

private lemma hullSevenAllAboveSumLower_mono {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    hullSevenAllAboveSumLower x ≤ hullSevenAllAboveSumLower y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hsquares : x ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx hy)]
  have hsqrt : Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt (y ^ 2 + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hprod :
      (x + 1) * Real.sqrt (x ^ 2 + 1) ≤
        (y + 1) * Real.sqrt (y ^ 2 + 1) := by
    exact mul_le_mul (by linarith) hsqrt (Real.sqrt_nonneg _) (by linarith)
  unfold hullSevenAllAboveSumLower
  nlinarith

private lemma hullSevenAllAboveSumLower_at_reciprocalRoot :
    hullSevenAllAboveSumLower (1 / hullSevenCoreRoot) =
      2 * hullSevenCoreRoot := by
  have hid := hullSevenCoreRoot_radical_identity
  unfold hullSevenAllAboveSumLower
  rw [hid]
  ring

private lemma hullSevenAllAbove_sum_lower {H : ℝ}
    (data : HullSevenAllAboveCapData H) :
    hullSevenAllAboveSumLower data.rho ≤ data.s + data.u := by
  let r := data.rho
  let x := data.s + data.u
  let j := data.s * data.u
  let y := Real.sqrt (r ^ 2 + 1)
  have hr : 0 < r := by simpa [r] using data.rho_pos
  have hx : 0 < x := by
    dsimp [x]
    exact add_pos data.s_pos data.u_pos
  have hj : 0 < j := by
    dsimp [j]
    exact mul_pos data.s_pos data.u_pos
  have hy0 : 0 ≤ y := by dsimp [y]; exact Real.sqrt_nonneg _
  have hy2 : y ^ 2 = r ^ 2 + 1 := by
    dsimp [y]
    exact Real.sq_sqrt (by positivity)
  have hjx : 4 * j ≤ x ^ 2 := by
    dsimp [x, j]
    nlinarith [sq_nonneg (data.s - data.u)]
  have hcapExpanded :
      j + (1 - r ^ 2) * x =
        (1 + r ^ 2) * data.q - 1 + 3 * r ^ 2 := by
    dsimp [r, x, j]
    nlinarith [data.cap_identity]
  have hradialScaled :
      (1 + r ^ 2) * (1 + 2 * r) ≤
        (1 + r ^ 2) * data.q := by
    exact mul_le_mul_of_nonneg_left data.radial_q (by positivity)
  have hradial :
      2 * r * (r + 1) ^ 2 ≤ j + (1 - r ^ 2) * x := by
    nlinarith [hcapExpanded, hradialScaled]
  have hquad :
      0 ≤ x ^ 2 + 4 * (1 - r ^ 2) * x -
        8 * r * (r + 1) ^ 2 := by
    nlinarith [hjx, hradial]
  let g := 2 * (r ^ 2 - 1 + (r + 1) * y)
  let h := 2 * (r ^ 2 - 1 - (r + 1) * y)
  have hfactor :
      x ^ 2 + 4 * (1 - r ^ 2) * x - 8 * r * (r + 1) ^ 2 =
        (x - g) * (x - h) := by
    dsimp [g, h]
    nlinarith [hy2]
  have hyr : r < y := by nlinarith [hy0, hy2]
  have hhneg : h < 0 := by
    have hr1 : 0 < r + 1 := add_pos hr (by norm_num : (0 : ℝ) < 1)
    have hyr' : 0 < y - r := sub_pos.mpr hyr
    have hprod : 0 < (r + 1) * (y - r) := mul_pos hr1 hyr'
    dsimp [h]
    nlinarith only [hprod, hr]
  have hxh : 0 < x - h := by linarith
  have hxg : g ≤ x := by
    by_contra hnot
    have hneg : (x - g) * (x - h) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hnot)) hxh
    rw [← hfactor] at hneg
    exact (not_lt_of_ge hquad) hneg
  simpa [hullSevenAllAboveSumLower, r, y, g, x] using hxg

/-- The selector actually supplies a strict radial inequality.  Retaining it
makes the lower bound on `s+u` strict as well. -/
private lemma hullSevenAllAbove_sum_lower_strict {H : ℝ}
    (data : HullSevenAllAboveCapData H) :
    hullSevenAllAboveSumLower data.rho < data.s + data.u := by
  let r := data.rho
  let x := data.s + data.u
  let j := data.s * data.u
  let y := Real.sqrt (r ^ 2 + 1)
  have hr : 0 < r := by simpa [r] using data.rho_pos
  have hx : 0 < x := by
    dsimp [x]
    exact add_pos data.s_pos data.u_pos
  have hj : 0 < j := by
    dsimp [j]
    exact mul_pos data.s_pos data.u_pos
  have hy0 : 0 ≤ y := by dsimp [y]; exact Real.sqrt_nonneg _
  have hy2 : y ^ 2 = r ^ 2 + 1 := by
    dsimp [y]
    exact Real.sq_sqrt (by positivity)
  have hjx : 4 * j ≤ x ^ 2 := by
    dsimp [x, j]
    nlinarith [sq_nonneg (data.s - data.u)]
  have hcapExpanded :
      j + (1 - r ^ 2) * x =
        (1 + r ^ 2) * data.q - 1 + 3 * r ^ 2 := by
    dsimp [r, x, j]
    nlinarith [data.cap_identity]
  have hradialScaled :
      (1 + r ^ 2) * (1 + 2 * r) <
        (1 + r ^ 2) * data.q := by
    exact mul_lt_mul_of_pos_left
      (by simpa [r] using data.radial_q_strict) (by positivity)
  have hradial :
      2 * r * (r + 1) ^ 2 < j + (1 - r ^ 2) * x := by
    nlinarith [hcapExpanded, hradialScaled]
  have hquad :
      0 < x ^ 2 + 4 * (1 - r ^ 2) * x -
        8 * r * (r + 1) ^ 2 := by
    nlinarith [hjx, hradial]
  let g := 2 * (r ^ 2 - 1 + (r + 1) * y)
  let h := 2 * (r ^ 2 - 1 - (r + 1) * y)
  have hfactor :
      x ^ 2 + 4 * (1 - r ^ 2) * x - 8 * r * (r + 1) ^ 2 =
        (x - g) * (x - h) := by
    dsimp [g, h]
    nlinarith [hy2]
  have hyr : r < y := by nlinarith [hy0, hy2]
  have hhneg : h < 0 := by
    have hr1 : 0 < r + 1 := add_pos hr (by norm_num : (0 : ℝ) < 1)
    have hyr' : 0 < y - r := sub_pos.mpr hyr
    have hprod : 0 < (r + 1) * (y - r) := mul_pos hr1 hyr'
    dsimp [h]
    nlinarith only [hprod, hr]
  have hxh : 0 < x - h := by linarith
  have hxg : g < x := by
    rw [hfactor] at hquad
    by_contra hnot
    have hnonpos : x - g ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have : (x - g) * (x - h) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hxh.le
    linarith
  simpa [hullSevenAllAboveSumLower, r, y, g, x] using hxg

private lemma hullSevenAllAbove_interval_area {H : ℝ}
    (data : HullSevenAllAboveCapData H) :
    6 + 1 / data.rho ^ 2 + (data.s + data.u) +
        4 / (data.s + data.u) ≤ H := by
  have hs : 0 < data.s := data.s_pos
  have hu : 0 < data.u := data.u_pos
  have hsum : 0 < data.s + data.u := add_pos hs hu
  have hprod : 0 < data.s * data.u := mul_pos hs hu
  have hfour :
      4 / (data.s + data.u) ≤
        1 / data.s + 1 / data.u := by
    have hsq := sq_nonneg (data.s - data.u)
    have hid :
        1 / data.s + 1 / data.u =
          (data.s + data.u) / (data.s * data.u) := by
      field_simp [hs.ne', hu.ne']
      ring
    rw [hid]
    apply (div_le_div_iff₀ hsum hprod).2
    nlinarith
  have hq : 1 + 4 / (data.s + data.u) ≤ data.q := by
    linarith [hfour, data.interval]
  linarith [data.area]

private lemma hullSevenAllAboveSumLower_two_at_three_fifths :
    (2 : ℝ) ≤ hullSevenAllAboveSumLower (3 / 5) := by
  have hs0 := Real.sqrt_nonneg (((3 / 5 : ℝ) ^ 2) + 1)
  have hs2 :
      (Real.sqrt (((3 / 5 : ℝ) ^ 2) + 1)) ^ 2 =
        ((3 / 5 : ℝ) ^ 2) + 1 :=
    Real.sq_sqrt (by positivity)
  unfold hullSevenAllAboveSumLower
  nlinarith

private lemma reciprocalRoot_lt_seven_tenths :
    1 / hullSevenCoreRoot < (7 / 10 : ℝ) := by
  have hroot : (147 / 100 : ℝ) ≤ hullSevenCoreRoot :=
    hullSevenCoreRoot_mem.1
  have hroot0 : 0 < hullSevenCoreRoot := hullSevenCoreRoot_pos
  apply (div_lt_iff₀ hroot0).2
  nlinarith

private lemma hullSevenAllAboveSumLower_lipschitz {x y : ℝ}
    (hx : (3 / 5 : ℝ) ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 7 / 10) :
    hullSevenAllAboveSumLower y - hullSevenAllAboveSumLower x ≤
      8 * (y - x) := by
  let sx := Real.sqrt (x ^ 2 + 1)
  let sy := Real.sqrt (y ^ 2 + 1)
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hsx0 : 0 ≤ sx := by dsimp [sx]; exact Real.sqrt_nonneg _
  have hsy0 : 0 ≤ sy := by dsimp [sy]; exact Real.sqrt_nonneg _
  have hsx2 : sx ^ 2 = x ^ 2 + 1 := by
    dsimp [sx]
    exact Real.sq_sqrt (by positivity)
  have hsy2 : sy ^ 2 = y ^ 2 + 1 := by
    dsimp [sy]
    exact Real.sq_sqrt (by positivity)
  have hsqrt : sx ≤ sy := by
    dsimp [sx, sy]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx0 hy0)]
  have hsx1 : 1 ≤ sx := by nlinarith
  have hsy1 : 1 ≤ sy := by nlinarith
  have hsyUpper : sy ≤ 5 / 4 := by
    have hy2 : y ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by
      exact (sq_le_sq₀ hy0 (by norm_num : (0 : ℝ) ≤ 7 / 10)).2 hy
    nlinarith only [hsy0, hsy2, hy2]
  have hdiffIdentity :
      (sy - sx) * (sy + sx) = (y - x) * (y + x) := by
    nlinarith [hsx2, hsy2]
  have hsumUpper : y + x ≤ 7 / 5 := by linarith
  have hdiffUpper : sy - sx ≤ (7 / 10) * (y - x) := by
    have hdiff0 : 0 ≤ sy - sx := sub_nonneg.mpr hsqrt
    have hleft := mul_le_mul_of_nonneg_left
      (show (2 : ℝ) ≤ sy + sx by linarith) hdiff0
    have hright := mul_le_mul_of_nonneg_left hsumUpper
      (sub_nonneg.mpr hxy)
    nlinarith [hdiffIdentity]
  have hdiff :
      hullSevenAllAboveSumLower y - hullSevenAllAboveSumLower x =
        2 * (y ^ 2 - x ^ 2) +
          2 * ((y - x) * sy + (x + 1) * (sy - sx)) := by
    unfold hullSevenAllAboveSumLower
    dsimp [sx, sy]
    ring
  have hsquareDiff : y ^ 2 - x ^ 2 ≤ (7 / 5) * (y - x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
      (sub_nonneg.mpr hsumUpper)]
  have hfirst := mul_le_mul_of_nonneg_left hsyUpper
    (sub_nonneg.mpr hxy)
  have hx1 : x + 1 ≤ 17 / 10 := by linarith
  have hsecond :
      (sy - sx) * (x + 1) ≤
        ((7 / 10 : ℝ) * (y - x)) * (17 / 10) := by
    calc
      (sy - sx) * (x + 1) ≤
          ((7 / 10 : ℝ) * (y - x)) * (x + 1) :=
        mul_le_mul_of_nonneg_right hdiffUpper (by linarith)
      _ ≤ ((7 / 10 : ℝ) * (y - x)) * (17 / 10) :=
        mul_le_mul_of_nonneg_left hx1
          (mul_nonneg (by norm_num) (sub_nonneg.mpr hxy))
  rw [hdiff]
  nlinarith

private lemma hullSevenAllAboveRadial_antitone_to_root {x y : ℝ}
    (hx : (3 / 5 : ℝ) ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1 / hullSevenCoreRoot) :
    hullSevenAllAboveRadial y ≤ hullSevenAllAboveRadial x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hySeven : y ≤ 7 / 10 :=
    le_trans hy (le_of_lt reciprocalRoot_lt_seven_tenths)
  let gx := hullSevenAllAboveSumLower x
  let gy := hullSevenAllAboveSumLower y
  have hgx2 : 2 ≤ gx := by
    dsimp [gx]
    exact le_trans hullSevenAllAboveSumLower_two_at_three_fifths
      (hullSevenAllAboveSumLower_mono (by norm_num) hx)
  have hgxy : gx ≤ gy := by
    dsimp [gx, gy]
    exact hullSevenAllAboveSumLower_mono hx0.le hxy
  have hgy3 : gy ≤ 3 := by
    have hmono := hullSevenAllAboveSumLower_mono hy0.le hy
    rw [hullSevenAllAboveSumLower_at_reciprocalRoot] at hmono
    have hrootUpper : hullSevenCoreRoot ≤ 3 / 2 :=
      hullSevenCoreRoot_mem.2
    dsimp [gy]
    linarith
  have hgx0 : 0 < gx := lt_of_lt_of_le (by norm_num) hgx2
  have hgy0 : 0 < gy := lt_of_lt_of_le hgx0 hgxy
  have hgdif : gy - gx ≤ 8 * (y - x) := by
    dsimp [gx, gy]
    exact hullSevenAllAboveSumLower_lipschitz hx hxy hySeven
  have hfactorUpper : 1 - 4 / (gx * gy) ≤ 5 / 9 := by
    have hprod : gx * gy ≤ 9 := by nlinarith [hgxy]
    have hprod0 : 0 < gx * gy := mul_pos hgx0 hgy0
    have hfrac : (4 / 9 : ℝ) ≤ 4 / (gx * gy) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 9) hprod0).2
      nlinarith
    linarith
  have hfactor0 : 0 ≤ 1 - 4 / (gx * gy) := by
    have hprod : 4 ≤ gx * gy := by nlinarith
    have hprod0 : 0 < gx * gy := mul_pos hgx0 hgy0
    have hfrac : 4 / (gx * gy) ≤ 1 := by
      apply (div_le_iff₀ hprod0).2
      simpa using hprod
    linarith
  have hcorrection :
      (gy - gx) * (1 - 4 / (gx * gy)) ≤
        (40 / 9 : ℝ) * (y - x) := by
    have hdiff0 : 0 ≤ gy - gx := sub_nonneg.mpr hgxy
    have hmul := mul_le_mul hgdif hfactorUpper hfactor0
      (by positivity : 0 ≤ 8 * (y - x))
    nlinarith
  have hxySquare : x ^ 2 * y ^ 2 ≤ (2401 / 10000 : ℝ) := by
    have hxSeven : x ≤ 7 / 10 := le_trans hxy hySeven
    have hx2 : x ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by
      exact (sq_le_sq₀ hx0.le (by norm_num : (0 : ℝ) ≤ 7 / 10)).2
        hxSeven
    have hy2 : y ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by
      exact (sq_le_sq₀ hy0.le (by norm_num : (0 : ℝ) ≤ 7 / 10)).2
        hySeven
    calc
      x ^ 2 * y ^ 2 ≤ (7 / 10 : ℝ) ^ 2 * y ^ 2 :=
        mul_le_mul_of_nonneg_right hx2 (sq_nonneg y)
      _ ≤ (7 / 10 : ℝ) ^ 2 * (7 / 10 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hy2 (sq_nonneg (7 / 10 : ℝ))
      _ = 2401 / 10000 := by norm_num
  have hsumLower : (6 / 5 : ℝ) ≤ x + y := by linarith
  have hcoefficient :
      (24 / 5 : ℝ) * (x ^ 2 * y ^ 2) ≤ x + y := by
    nlinarith [hxySquare]
  have hinvIdentity :
      1 / x ^ 2 - 1 / y ^ 2 =
        (y - x) * (x + y) / (x ^ 2 * y ^ 2) := by
    field_simp [hx0.ne', hy0.ne']
    ring
  have hden : 0 < x ^ 2 * y ^ 2 := by positivity
  have hinvLower :
      (24 / 5 : ℝ) * (y - x) ≤ 1 / x ^ 2 - 1 / y ^ 2 := by
    rw [hinvIdentity]
    apply (le_div_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hcoefficient
      (sub_nonneg.mpr hxy)
    nlinarith
  have hradialIdentity :
      hullSevenAllAboveRadial x - hullSevenAllAboveRadial y =
        (1 / x ^ 2 - 1 / y ^ 2) -
          (gy - gx) * (1 - 4 / (gx * gy)) := by
    change (6 + 1 / x ^ 2 + gx + 4 / gx) -
        (6 + 1 / y ^ 2 + gy + 4 / gy) = _
    field_simp [hx0.ne', hy0.ne', hgx0.ne', hgy0.ne']
    ring
  rw [← sub_nonneg, hradialIdentity]
  nlinarith [hinvLower, hcorrection]

private lemma hullSevenAllAboveRadial_at_reciprocalRoot :
    hullSevenAllAboveRadial (1 / hullSevenCoreRoot) =
      hullSevenSharpH := by
  have hroot0 := hullSevenCoreRoot_pos
  unfold hullSevenAllAboveRadial
  rw [hullSevenAllAboveSumLower_at_reciprocalRoot]
  unfold hullSevenSharpH
  field_simp [hroot0.ne']
  ring

/-- The recurrence-free all-above-cap scalar branch is closed. -/
theorem hullSevenAllAboveCapClosure_proved :
    HullSevenAllAboveCapClosure := by
  intro H data
  have hr := data.rho_pos
  have hsum := hullSevenAllAbove_sum_lower data
  have hintervalArea := hullSevenAllAbove_interval_area data
  by_cases hsmall : data.rho ≤ 3 / 5
  · have hsu : 4 ≤
        (data.s + data.u) + 4 / (data.s + data.u) := by
      have hsum0 : 0 < data.s + data.u :=
        add_pos data.s_pos data.u_pos
      rw [show (data.s + data.u) + 4 / (data.s + data.u) =
          ((data.s + data.u) ^ 2 + 4) / (data.s + data.u) by
        field_simp [hsum0.ne']]
      apply (le_div_iff₀ hsum0).2
      nlinarith [sq_nonneg (data.s + data.u - 2)]
    have hrSquare : data.rho ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by
      exact (sq_le_sq₀ hr.le (by norm_num : (0 : ℝ) ≤ 3 / 5)).2
        hsmall
    have hinv : (25 / 9 : ℝ) ≤ 1 / data.rho ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr)).2
      nlinarith
    have hH : (115 / 9 : ℝ) ≤ H := by
      linarith [hintervalArea]
    have hv : (79 / 1000 : ℝ) < v8 := v8_gt
    have hmul := mul_le_mul_of_nonneg_left hH v8_pos.le
    nlinarith
  · have hlarge : (3 / 5 : ℝ) ≤ data.rho :=
      le_of_not_ge hsmall
    let r0 := 1 / hullSevenCoreRoot
    by_cases hright : r0 ≤ data.rho
    · have hcentral : hullSevenRadialCentral data.rho ≤ H := by
        have hq := data.radial_q
        unfold hullSevenAllAboveSumLower at hsum
        unfold hullSevenRadialCentral
        linarith only [hsum, hq, data.area]
      have hr0lo : (2 / 3 : ℝ) ≤ r0 := by
        dsimp [r0]
        exact hullSevenReciprocalRoot_mem.1
      have hmono := hullSevenRadialCentral_monotone hr0lo hright
      have hsharp : hullSevenSharpH ≤ H := by
        rw [show hullSevenRadialCentral r0 = hullSevenSharpH by
          dsimp [r0]
          exact hullSevenRadialCentral_at_reciprocalRoot] at hmono
        exact le_trans hmono hcentral
      have hmul := mul_le_mul_of_nonneg_left hsharp v8_pos.le
      rw [v8_mul_hullSevenSharpH] at hmul
      exact hmul
    · have hrle : data.rho ≤ r0 := le_of_not_ge hright
      have hg2 : 2 ≤ hullSevenAllAboveSumLower data.rho :=
        le_trans hullSevenAllAboveSumLower_two_at_three_fifths
          (hullSevenAllAboveSumLower_mono (by norm_num) hlarge)
      have hx2 : 2 ≤ data.s + data.u := le_trans hg2 hsum
      have hg0 : 0 < hullSevenAllAboveSumLower data.rho :=
        lt_of_lt_of_le (by norm_num) hg2
      have hx0 : 0 < data.s + data.u := lt_of_lt_of_le (by norm_num) hx2
      have hmonoReciprocal :
          hullSevenAllAboveSumLower data.rho +
              4 / hullSevenAllAboveSumLower data.rho ≤
            (data.s + data.u) + 4 / (data.s + data.u) := by
        have hid :
            ((data.s + data.u) + 4 / (data.s + data.u)) -
                (hullSevenAllAboveSumLower data.rho +
                  4 / hullSevenAllAboveSumLower data.rho) =
              ((data.s + data.u) -
                  hullSevenAllAboveSumLower data.rho) *
                (1 - 4 / ((data.s + data.u) *
                  hullSevenAllAboveSumLower data.rho)) := by
          field_simp [hx0.ne', hg0.ne']
          ring
        have hprod : 4 ≤ (data.s + data.u) *
            hullSevenAllAboveSumLower data.rho := by nlinarith
        have hfactor : 0 ≤ 1 - 4 / ((data.s + data.u) *
            hullSevenAllAboveSumLower data.rho) := by
          have hp : 0 < (data.s + data.u) *
              hullSevenAllAboveSumLower data.rho := mul_pos hx0 hg0
          have hfrac : 4 / ((data.s + data.u) *
              hullSevenAllAboveSumLower data.rho) ≤ 1 := by
            apply (div_le_iff₀ hp).2
            simpa using hprod
          linarith only [hfrac]
        rw [← sub_nonneg, hid]
        exact mul_nonneg (sub_nonneg.mpr hsum) hfactor
      have hradial : hullSevenAllAboveRadial data.rho ≤ H := by
        unfold hullSevenAllAboveRadial
        linarith [hintervalArea, hmonoReciprocal]
      have hanti := hullSevenAllAboveRadial_antitone_to_root
        hlarge hrle (le_rfl : r0 ≤ r0)
      have hsharp : hullSevenSharpH ≤ H := by
        rw [show hullSevenAllAboveRadial r0 = hullSevenSharpH by
          dsimp [r0]
          exact hullSevenAllAboveRadial_at_reciprocalRoot] at hanti
        exact le_trans hanti hradial
      have hmul := mul_le_mul_of_nonneg_left hsharp v8_pos.le
      rw [v8_mul_hullSevenSharpH] at hmul
      exact hmul

/-- The all-above selector outcome is strictly separated from the sharp
boundary. -/
theorem HullSevenAllAboveCapData.not_v8_boundary {H : ℝ}
    (data : HullSevenAllAboveCapData H)
    (hupper : v8 * H ≤ 1) : False := by
  have hHle : H ≤ hullSevenSharpH := by
    have hmul : v8 * H ≤ v8 * hullSevenSharpH := by
      rw [v8_mul_hullSevenSharpH]
      exact hupper
    nlinarith [v8_pos]
  have hr := data.rho_pos
  have hsum := hullSevenAllAbove_sum_lower data
  have hsumStrict := hullSevenAllAbove_sum_lower_strict data
  have hintervalArea := hullSevenAllAbove_interval_area data
  by_cases hsmall : data.rho ≤ 3 / 5
  · have hsu : 4 ≤
        (data.s + data.u) + 4 / (data.s + data.u) := by
      have hsum0 : 0 < data.s + data.u := add_pos data.s_pos data.u_pos
      rw [show (data.s + data.u) + 4 / (data.s + data.u) =
          ((data.s + data.u) ^ 2 + 4) / (data.s + data.u) by
        field_simp [hsum0.ne']]
      apply (le_div_iff₀ hsum0).2
      nlinarith [sq_nonneg (data.s + data.u - 2)]
    have hrSquare : data.rho ^ 2 ≤ (3 / 5 : ℝ) ^ 2 :=
      (sq_le_sq₀ hr.le (by norm_num)).2 hsmall
    have hinv : (25 / 9 : ℝ) ≤ 1 / data.rho ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr)).2
      nlinarith
    have hH : (115 / 9 : ℝ) ≤ H := by
      linarith [hintervalArea]
    have hmul := mul_le_mul_of_nonneg_left hH v8_pos.le
    nlinarith [v8_gt]
  · have hlarge : (3 / 5 : ℝ) ≤ data.rho := le_of_not_ge hsmall
    let r0 := 1 / hullSevenCoreRoot
    by_cases hright : r0 ≤ data.rho
    · have hcentralStrict : hullSevenRadialCentral data.rho < H := by
        unfold hullSevenAllAboveSumLower at hsum
        unfold hullSevenRadialCentral
        linarith only [hsum, data.radial_q_strict, data.area]
      have hr0lo : (2 / 3 : ℝ) ≤ r0 := by
        dsimp [r0]
        exact hullSevenReciprocalRoot_mem.1
      have hmono := hullSevenRadialCentral_monotone hr0lo hright
      have hsharpLe : hullSevenSharpH ≤
          hullSevenRadialCentral data.rho := by
        rw [← hullSevenRadialCentral_at_reciprocalRoot]
        simpa [r0] using hmono
      linarith
    · have hrle : data.rho ≤ r0 := le_of_not_ge hright
      have hg2 : 2 ≤ hullSevenAllAboveSumLower data.rho :=
        le_trans hullSevenAllAboveSumLower_two_at_three_fifths
          (hullSevenAllAboveSumLower_mono (by norm_num) hlarge)
      have hg0 : 0 < hullSevenAllAboveSumLower data.rho :=
        lt_of_lt_of_le (by norm_num) hg2
      have hx0 : 0 < data.s + data.u := add_pos data.s_pos data.u_pos
      have hmonoReciprocalStrict :
          hullSevenAllAboveSumLower data.rho +
              4 / hullSevenAllAboveSumLower data.rho <
            (data.s + data.u) + 4 / (data.s + data.u) := by
        let g := hullSevenAllAboveSumLower data.rho
        let x := data.s + data.u
        have hg2' : 2 ≤ g := by simpa [g] using hg2
        have hgx : g < x := by simpa [g, x] using hsumStrict
        have hprod : 4 < x * g := by
          have hxg : g * g < x * g := mul_lt_mul_of_pos_right hgx hg0
          nlinarith [sq_nonneg (g - 2)]
        have hfactor : 0 < 1 - 4 / (x * g) := by
          have hxg0 : 0 < x * g := mul_pos hx0 hg0
          have : 4 / (x * g) < 1 := by
            apply (div_lt_iff₀ hxg0).2
            simpa using hprod
          linarith
        have hid :
            ((data.s + data.u) + 4 / (data.s + data.u)) -
                (hullSevenAllAboveSumLower data.rho +
                  4 / hullSevenAllAboveSumLower data.rho) =
              ((data.s + data.u) -
                  hullSevenAllAboveSumLower data.rho) *
                (1 - 4 / ((data.s + data.u) *
                  hullSevenAllAboveSumLower data.rho)) := by
          field_simp [hx0.ne', hg0.ne']
          ring
        rw [← sub_pos, hid]
        exact mul_pos (sub_pos.mpr hsumStrict)
          (by simpa [x, g] using hfactor)
      have hradialStrict : hullSevenAllAboveRadial data.rho < H := by
        unfold hullSevenAllAboveRadial
        linarith [hintervalArea, hmonoReciprocalStrict]
      have hanti := hullSevenAllAboveRadial_antitone_to_root
        hlarge hrle (le_rfl : r0 ≤ r0)
      have hsharpLe : hullSevenSharpH ≤
          hullSevenAllAboveRadial data.rho := by
        rw [← hullSevenAllAboveRadial_at_reciprocalRoot]
        simpa [r0] using hanti
      linarith

end Heilbronn8.TriHull
