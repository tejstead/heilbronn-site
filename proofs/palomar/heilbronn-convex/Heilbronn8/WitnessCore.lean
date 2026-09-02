import Heilbronn8.Defs
import Heilbronn8.V8

namespace Heilbronn8

noncomputable def cw : ℝ :=
  (217330 * v8 ^ 4 - 206886 * v8 ^ 3 + 70519 * v8 ^ 2 -
    10079 * v8 + 485) / 47

noncomputable def dw : ℝ :=
  (1077380 * v8 ^ 4 - 997156 * v8 ^ 3 + 339636 * v8 ^ 2 -
    49222 * v8 + 2319) / 47

noncomputable def ew : ℝ :=
  (227630 * v8 ^ 4 - 129966 * v8 ^ 3 + 20883 * v8 ^ 2 +
    164 * v8 - 97) / 47

noncomputable def fw : ℝ :=
  2 * (321360 * v8 ^ 4 - 291692 * v8 ^ 3 + 99299 * v8 ^ 2 -
    14532 * v8 + 698) / 47

noncomputable def gw : ℝ :=
  -(538690 * v8 ^ 4 - 498578 * v8 ^ 3 + 169818 * v8 ^ 2 -
    24611 * v8 + 1136) / 47

noncomputable def w : Fin 8 → ℝ × ℝ :=
  ![((0 : ℝ), (1 : ℝ)), (-1, cw), (1, cw), (-dw, ew),
    (dw, ew), (0, 0), (-fw, gw), (fw, gw)]

lemma vP :
    2060 * v8 ^ 5 - 2332 * v8 ^ 4 + 1064 * v8 ^ 3 -
      240 * v8 ^ 2 + 26 * v8 - 1 = 0 := by
  simpa [P] using v8_root

/--
Simultaneous tight-bracket bounds for the four monomials used by every
generated interval certificate.
-/
lemma v8_pow_bounds :
    (80000139329466 / 10 ^ 15 : ℝ) ≤ v8 ∧
    v8 ≤ (80000139329467 / 10 ^ 15 : ℝ) ∧
    (80000139329466 / 10 ^ 15 : ℝ) ^ 2 ≤ v8 ^ 2 ∧
    v8 ^ 2 ≤ (80000139329467 / 10 ^ 15 : ℝ) ^ 2 ∧
    (80000139329466 / 10 ^ 15 : ℝ) ^ 3 ≤ v8 ^ 3 ∧
    v8 ^ 3 ≤ (80000139329467 / 10 ^ 15 : ℝ) ^ 3 ∧
    (80000139329466 / 10 ^ 15 : ℝ) ^ 4 ≤ v8 ^ 4 ∧
    v8 ^ 4 ≤ (80000139329467 / 10 ^ 15 : ℝ) ^ 4 := by
  have h1l := v8_lb.le
  have h1u := v8_ub.le
  have h2l :
      (80000139329466 / 10 ^ 15 : ℝ) ^ 2 ≤ v8 ^ 2 := by
    nlinarith
  have h2u :
      v8 ^ 2 ≤ (80000139329467 / 10 ^ 15 : ℝ) ^ 2 := by
    nlinarith
  have h3l :
      (80000139329466 / 10 ^ 15 : ℝ) ^ 3 ≤ v8 ^ 3 := by
    nlinarith [
      mul_nonneg (sub_nonneg.mpr h2l) (sub_nonneg.mpr h1l)]
  have h3u :
      v8 ^ 3 ≤ (80000139329467 / 10 ^ 15 : ℝ) ^ 3 := by
    nlinarith [
      mul_nonneg (sub_nonneg.mpr h2u) (sub_nonneg.mpr h1u)]
  have h4l :
      (80000139329466 / 10 ^ 15 : ℝ) ^ 4 ≤ v8 ^ 4 := by
    nlinarith [
      mul_nonneg (sub_nonneg.mpr h3l) (sub_nonneg.mpr h1l)]
  have h4u :
      v8 ^ 4 ≤ (80000139329467 / 10 ^ 15 : ℝ) ^ 4 := by
    nlinarith [
      mul_nonneg (sub_nonneg.mpr h3u) (sub_nonneg.mpr h1u)]
  exact ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩

noncomputable def H2w : ℝ := H2 w

lemma H2w_reduce : H2w = ((-2618 / 47) + (69202 / 47) * v8 + (-518292 / 47) * v8 ^ 2 + (1608172 / 47) * v8 ^ 3 + (-1804560 / 47) * v8 ^ 4 : ℝ) := by
  simp [H2w, H2, hullCycle, w, sig, cw, dw, ew, fw, gw]
  linear_combination ((-10555668 / 2209) + (177941502 / 2209) * v8 + (-859541680 / 2209) * v8 ^ 2 + (1268980600 / 2209) * v8 ^ 3 : ℝ) * vP

lemma H2w_reduced_pos : 0 < ((-2618 / 47) + (69202 / 47) * v8 + (-518292 / 47) * v8 ^ 2 + (1608172 / 47) * v8 ^ 3 + (-1804560 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma H2w_pos : 0 < H2w := by
  rw [H2w_reduce]
  exact H2w_reduced_pos

lemma v8H2w_pos : 0 < v8 * H2w :=
  mul_pos v8_pos H2w_pos

lemma sig_w_012 : sig (w 0) (w 1) (w 2) = v8 * H2w := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma sig_w_013 : sig (w 0) (w 1) (w 3) = v8 * H2w := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-1022490 / 2209) + (28788027 / 2209) * v8 + (-262671240 / 2209) * v8 ^ 2 + (973205270 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_014 : sig (w 0) (w 1) (w 4) - v8 * H2w = ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((1104834 / 2209) + (-7676691 / 2209) * v8 + (-93211764 / 2209) * v8 ^ 2 + (745878090 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_014_poly_pos : 0 < ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_015 : sig (w 0) (w 1) (w 5) - v8 * H2w = ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_015_poly_pos : 0 < ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_016 : sig (w 0) (w 1) (w 6) - v8 * H2w = ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-623668 / 2209) + (21226861 / 2209) * v8 + (-227276834 / 2209) * v8 ^ 2 + (927348640 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_016_poly_pos : 0 < ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_017 : sig (w 0) (w 1) (w 7) - v8 * H2w = ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((706012 / 2209) + (-115525 / 2209) * v8 + (-128606170 / 2209) * v8 ^ 2 + (791734720 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_017_poly_pos : 0 < ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_023 : -sig (w 0) (w 2) (w 3) - v8 * H2w = ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((1104834 / 2209) + (-7676691 / 2209) * v8 + (-93211764 / 2209) * v8 ^ 2 + (745878090 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_023_poly_pos : 0 < ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma sig_w_024 : sig (w 0) (w 2) (w 4) = -(v8 * H2w) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((1022490 / 2209) + (-28788027 / 2209) * v8 + (262671240 / 2209) * v8 ^ 2 + (-973205270 / 2209) * v8 ^ 3 + (1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_025 : -sig (w 0) (w 2) (w 5) - v8 * H2w = ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_025_poly_pos : 0 < ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_026 : -sig (w 0) (w 2) (w 6) - v8 * H2w = ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((706012 / 2209) + (-115525 / 2209) * v8 + (-128606170 / 2209) * v8 ^ 2 + (791734720 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_026_poly_pos : 0 < ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_027 : -sig (w 0) (w 2) (w 7) - v8 * H2w = ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-623668 / 2209) + (21226861 / 2209) * v8 + (-227276834 / 2209) * v8 ^ 2 + (927348640 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_027_poly_pos : 0 < ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_034 : sig (w 0) (w 3) (w 4) - v8 * H2w = ((4638 / 47) + (-98444 / 47) * v8 + (679272 / 47) * v8 ^ 2 + (-1994312 / 47) * v8 ^ 3 + (2154760 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-449886 / 2209) + (9045286 / 2209) * v8 + (-91165146 / 2209) * v8 ^ 2 + (621440700 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_034_poly_pos : 0 < ((4638 / 47) + (-98444 / 47) * v8 + (679272 / 47) * v8 ^ 2 + (-1994312 / 47) * v8 ^ 3 + (2154760 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_035 : sig (w 0) (w 3) (w 5) - v8 * H2w = ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_035_poly_pos : 0 < ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_036 : sig (w 0) (w 3) (w 6) - v8 * H2w = ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2498972 / 2209) + (55400299 / 2209) * v8 + (-405134568 / 2209) * v8 ^ 2 + (1212297110 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_036_poly_pos : 0 < ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_037 : sig (w 0) (w 3) (w 7) - v8 * H2w = ((1071 / 47) + (-20008 / 47) * v8 + (145186 / 47) * v8 ^ 2 + (-476460 / 47) * v8 ^ 3 + (597400 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2894064 / 2209) + (53963277 / 2209) * v8 + (-355903984 / 2209) * v8 ^ 2 + (1070255990 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_037_poly_pos : 0 < ((1071 / 47) + (-20008 / 47) * v8 + (145186 / 47) * v8 ^ 2 + (-476460 / 47) * v8 ^ 3 + (597400 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_045 : -sig (w 0) (w 4) (w 5) - v8 * H2w = ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_045_poly_pos : 0 < ((3195 / 47) + (-69380 / 47) * v8 + (480674 / 47) * v8 ^ 2 + (-1410928 / 47) * v8 ^ 3 + (1512040 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_046 : -sig (w 0) (w 4) (w 6) - v8 * H2w = ((1071 / 47) + (-20008 / 47) * v8 + (145186 / 47) * v8 ^ 2 + (-476460 / 47) * v8 ^ 3 + (597400 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2894064 / 2209) + (53963277 / 2209) * v8 + (-355903984 / 2209) * v8 ^ 2 + (1070255990 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_046_poly_pos : 0 < ((1071 / 47) + (-20008 / 47) * v8 + (145186 / 47) * v8 ^ 2 + (-476460 / 47) * v8 ^ 3 + (597400 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_047 : -sig (w 0) (w 4) (w 7) - v8 * H2w = ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2498972 / 2209) + (55400299 / 2209) * v8 + (-405134568 / 2209) * v8 ^ 2 + (1212297110 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_047_poly_pos : 0 < ((923 / 47) + (-20158 / 47) * v8 + (141038 / 47) * v8 ^ 2 + (-413772 / 47) * v8 ^ 3 + (434660 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_056 : -sig (w 0) (w 5) (w 6) - v8 * H2w = ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_056_poly_pos : 0 < ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_057 : sig (w 0) (w 5) (w 7) - v8 * H2w = ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_057_poly_pos : 0 < ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_067 : sig (w 0) (w 6) (w 7) - v8 * H2w = ((-84 / 47) + (8728 / 47) * v8 + (-95178 / 47) * v8 ^ 2 + (366856 / 47) * v8 ^ 3 + (-500580 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-3306884 / 2209) + (62343190 / 2209) * v8 + (-413637574 / 2209) * v8 ^ 2 + (1195684240 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_067_poly_pos : 0 < ((-84 / 47) + (8728 / 47) * v8 + (-95178 / 47) * v8 ^ 2 + (366856 / 47) * v8 ^ 3 + (-500580 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_123 : -sig (w 1) (w 2) (w 3) - v8 * H2w = ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_123_poly_pos : 0 < ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_124 : -sig (w 1) (w 2) (w 4) - v8 * H2w = ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_124_poly_pos : 0 < ((2040 / 47) + (-40644 / 47) * v8 + (240310 / 47) * v8 ^ 2 + (-567612 / 47) * v8 ^ 3 + (414060 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_125 : -sig (w 1) (w 2) (w 5) - v8 * H2w = ((1846 / 47) + (-40316 / 47) * v8 + (282076 / 47) * v8 ^ 2 + (-827544 / 47) * v8 ^ 3 + (869320 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_125_poly_pos : 0 < ((1846 / 47) + (-40316 / 47) * v8 + (282076 / 47) * v8 ^ 2 + (-827544 / 47) * v8 ^ 3 + (869320 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_126 : -sig (w 1) (w 2) (w 6) - v8 * H2w = ((4118 / 47) + (-89538 / 47) * v8 + (621712 / 47) * v8 ^ 2 + (-1824700 / 47) * v8 ^ 3 + (1946700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_126_poly_pos : 0 < ((4118 / 47) + (-89538 / 47) * v8 + (621712 / 47) * v8 ^ 2 + (-1824700 / 47) * v8 ^ 3 + (1946700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_127 : -sig (w 1) (w 2) (w 7) - v8 * H2w = ((4118 / 47) + (-89538 / 47) * v8 + (621712 / 47) * v8 ^ 2 + (-1824700 / 47) * v8 ^ 3 + (1946700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((876 / 47) + (10555668 / 2209) * v8 + (-177941502 / 2209) * v8 ^ 2 + (859541680 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_127_poly_pos : 0 < ((4118 / 47) + (-89538 / 47) * v8 + (621712 / 47) * v8 ^ 2 + (-1824700 / 47) * v8 ^ 3 + (1946700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_134 : sig (w 1) (w 3) (w 4) - v8 * H2w = ((2598 / 47) + (-57800 / 47) * v8 + (438962 / 47) * v8 ^ 2 + (-1426700 / 47) * v8 ^ 3 + (1740700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2577210 / 2209) + (45510004 / 2209) * v8 + (-260624622 / 2209) * v8 ^ 2 + (848767880 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_134_poly_pos : 0 < ((2598 / 47) + (-57800 / 47) * v8 + (438962 / 47) * v8 ^ 2 + (-1426700 / 47) * v8 ^ 3 + (1740700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_135 : sig (w 1) (w 3) (w 5) - v8 * H2w = ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-1022490 / 2209) + (28788027 / 2209) * v8 + (-262671240 / 2209) * v8 ^ 2 + (973205270 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_135_poly_pos : 0 < ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma sig_w_136 : sig (w 1) (w 3) (w 6) = v8 * H2w := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2897794 / 2209) + (62961465 / 2209) * v8 + (-440528974 / 2209) * v8 ^ 2 + (1258153740 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_137 : sig (w 1) (w 3) (w 7) - v8 * H2w = ((-2124 / 47) + (49372 / 47) * v8 + (-335488 / 47) * v8 ^ 2 + (934468 / 47) * v8 ^ 3 + (-914640 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4622566 / 2209) + (82866829 / 2209) * v8 + (-489969054 / 2209) * v8 ^ 2 + (1251726540 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_137_poly_pos : 0 < ((-2124 / 47) + (49372 / 47) * v8 + (-335488 / 47) * v8 ^ 2 + (934468 / 47) * v8 ^ 3 + (-914640 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_145 : -sig (w 1) (w 4) (w 5) - v8 * H2w = ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-1022490 / 2209) + (28788027 / 2209) * v8 + (-262671240 / 2209) * v8 ^ 2 + (973205270 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_145_poly_pos : 0 < ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_146 : -sig (w 1) (w 4) (w 6) - v8 * H2w = ((-46 / 47) + (478 / 47) * v8 + (45914 / 47) * v8 ^ 2 + (-322620 / 47) * v8 ^ 3 + (618000 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4622566 / 2209) + (82866829 / 2209) * v8 + (-489969054 / 2209) * v8 ^ 2 + (1251726540 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_146_poly_pos : 0 < ((-46 / 47) + (478 / 47) * v8 + (45914 / 47) * v8 ^ 2 + (-322620 / 47) * v8 ^ 3 + (618000 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2l, h3u, h4l]

lemma gap_w_147 : -sig (w 1) (w 4) (w 7) - v8 * H2w = ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2897794 / 2209) + (62961465 / 2209) * v8 + (-440528974 / 2209) * v8 ^ 2 + (1258153740 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_147_poly_pos : 0 < ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_156 : -sig (w 1) (w 5) (w 6) - v8 * H2w = ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-623668 / 2209) + (21226861 / 2209) * v8 + (-227276834 / 2209) * v8 ^ 2 + (927348640 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_156_poly_pos : 0 < ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma sig_w_157 : sig (w 1) (w 5) (w 7) = v8 * H2w := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-623668 / 2209) + (21226861 / 2209) * v8 + (-227276834 / 2209) * v8 ^ 2 + (927348640 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_167 : sig (w 1) (w 6) (w 7) - v8 * H2w = ((-2356 / 47) + (57950 / 47) * v8 + (-434814 / 47) * v8 ^ 2 + (1364012 / 47) * v8 ^ 3 + (-1577960 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4636564 / 2209) + (83685576 / 2209) * v8 + (-512308238 / 2209) * v8 ^ 2 + (1331298160 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_167_poly_pos : 0 < ((-2356 / 47) + (57950 / 47) * v8 + (-434814 / 47) * v8 ^ 2 + (1364012 / 47) * v8 ^ 3 + (-1577960 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_234 : sig (w 2) (w 3) (w 4) - v8 * H2w = ((2598 / 47) + (-57800 / 47) * v8 + (438962 / 47) * v8 ^ 2 + (-1426700 / 47) * v8 ^ 3 + (1740700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2577210 / 2209) + (45510004 / 2209) * v8 + (-260624622 / 2209) * v8 ^ 2 + (848767880 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_234_poly_pos : 0 < ((2598 / 47) + (-57800 / 47) * v8 + (438962 / 47) * v8 ^ 2 + (-1426700 / 47) * v8 ^ 3 + (1740700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_235 : sig (w 2) (w 3) (w 5) - v8 * H2w = ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-1022490 / 2209) + (28788027 / 2209) * v8 + (-262671240 / 2209) * v8 ^ 2 + (973205270 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_235_poly_pos : 0 < ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_236 : sig (w 2) (w 3) (w 6) - v8 * H2w = ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2897794 / 2209) + (62961465 / 2209) * v8 + (-440528974 / 2209) * v8 ^ 2 + (1258153740 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_236_poly_pos : 0 < ((2078 / 47) + (-48894 / 47) * v8 + (381402 / 47) * v8 ^ 2 + (-1257088 / 47) * v8 ^ 3 + (1532640 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_237 : sig (w 2) (w 3) (w 7) - v8 * H2w = ((-46 / 47) + (478 / 47) * v8 + (45914 / 47) * v8 ^ 2 + (-322620 / 47) * v8 ^ 3 + (618000 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4622566 / 2209) + (82866829 / 2209) * v8 + (-489969054 / 2209) * v8 ^ 2 + (1251726540 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_237_poly_pos : 0 < ((-46 / 47) + (478 / 47) * v8 + (45914 / 47) * v8 ^ 2 + (-322620 / 47) * v8 ^ 3 + (618000 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2l, h3u, h4l]

lemma gap_w_245 : -sig (w 2) (w 4) (w 5) - v8 * H2w = ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-1022490 / 2209) + (28788027 / 2209) * v8 + (-262671240 / 2209) * v8 ^ 2 + (973205270 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_245_poly_pos : 0 < ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_246 : -sig (w 2) (w 4) (w 6) - v8 * H2w = ((-2124 / 47) + (49372 / 47) * v8 + (-335488 / 47) * v8 ^ 2 + (934468 / 47) * v8 ^ 3 + (-914640 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4622566 / 2209) + (82866829 / 2209) * v8 + (-489969054 / 2209) * v8 ^ 2 + (1251726540 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_246_poly_pos : 0 < ((-2124 / 47) + (49372 / 47) * v8 + (-335488 / 47) * v8 ^ 2 + (934468 / 47) * v8 ^ 3 + (-914640 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma sig_w_247 : sig (w 2) (w 4) (w 7) = -(v8 * H2w) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((2897794 / 2209) + (-62961465 / 2209) * v8 + (440528974 / 2209) * v8 ^ 2 + (-1258153740 / 2209) * v8 ^ 3 + (1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma sig_w_256 : sig (w 2) (w 5) (w 6) = -(v8 * H2w) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((623668 / 2209) + (-21226861 / 2209) * v8 + (227276834 / 2209) * v8 ^ 2 + (-927348640 / 2209) * v8 ^ 3 + (1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_257 : sig (w 2) (w 5) (w 7) - v8 * H2w = ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-623668 / 2209) + (21226861 / 2209) * v8 + (-227276834 / 2209) * v8 ^ 2 + (927348640 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_257_poly_pos : 0 < ((2272 / 47) + (-49222 / 47) * v8 + (339636 / 47) * v8 ^ 2 + (-997156 / 47) * v8 ^ 3 + (1077380 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma gap_w_267 : sig (w 2) (w 6) (w 7) - v8 * H2w = ((-2356 / 47) + (57950 / 47) * v8 + (-434814 / 47) * v8 ^ 2 + (1364012 / 47) * v8 ^ 3 + (-1577960 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4636564 / 2209) + (83685576 / 2209) * v8 + (-512308238 / 2209) * v8 ^ 2 + (1331298160 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_267_poly_pos : 0 < ((-2356 / 47) + (57950 / 47) * v8 + (-434814 / 47) * v8 ^ 2 + (1364012 / 47) * v8 ^ 3 + (-1577960 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma sig_w_345 : sig (w 3) (w 4) (w 5) = v8 * H2w := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-449886 / 2209) + (9045286 / 2209) * v8 + (-91165146 / 2209) * v8 ^ 2 + (621440700 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_346 : -sig (w 3) (w 4) (w 6) - v8 * H2w = ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4943150 / 2209) + (100318290 / 2209) * v8 + (-669873406 / 2209) * v8 ^ 2 + (1661112400 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_346_poly_pos : 0 < ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_347 : -sig (w 3) (w 4) (w 7) - v8 * H2w = ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-4943150 / 2209) + (100318290 / 2209) * v8 + (-669873406 / 2209) * v8 ^ 2 + (1661112400 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_347_poly_pos : 0 < ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma sig_w_356 : sig (w 3) (w 5) (w 6) = -(v8 * H2w) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((2498972 / 2209) + (-55400299 / 2209) * v8 + (405134568 / 2209) * v8 ^ 2 + (-1212297110 / 2209) * v8 ^ 3 + (1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_357 : -sig (w 3) (w 5) (w 7) - v8 * H2w = ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2894064 / 2209) + (53963277 / 2209) * v8 + (-355903984 / 2209) * v8 ^ 2 + (1070255990 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_357_poly_pos : 0 < ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_367 : sig (w 3) (w 6) (w 7) - v8 * H2w = ((-232 / 47) + (8578 / 47) * v8 + (-99326 / 47) * v8 ^ 2 + (429544 / 47) * v8 ^ 3 + (-663320 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2911792 / 2209) + (63780212 / 2209) * v8 + (-462868158 / 2209) * v8 ^ 2 + (1337725360 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_367_poly_pos : 0 < ((-232 / 47) + (8578 / 47) * v8 + (-99326 / 47) * v8 ^ 2 + (429544 / 47) * v8 ^ 3 + (-663320 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_456 : sig (w 4) (w 5) (w 6) - v8 * H2w = ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2894064 / 2209) + (53963277 / 2209) * v8 + (-355903984 / 2209) * v8 ^ 2 + (1070255990 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_456_poly_pos : 0 < ((-2644 / 47) + (58278 / 47) * v8 + (-393048 / 47) * v8 ^ 2 + (1104080 / 47) * v8 ^ 3 + (-1122700 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma sig_w_457 : sig (w 4) (w 5) (w 7) = v8 * H2w := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2498972 / 2209) + (55400299 / 2209) * v8 + (-405134568 / 2209) * v8 ^ 2 + (1212297110 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_467 : sig (w 4) (w 6) (w 7) - v8 * H2w = ((-232 / 47) + (8578 / 47) * v8 + (-99326 / 47) * v8 ^ 2 + (429544 / 47) * v8 ^ 3 + (-663320 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-2911792 / 2209) + (63780212 / 2209) * v8 + (-462868158 / 2209) * v8 ^ 2 + (1337725360 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_467_poly_pos : 0 < ((-232 / 47) + (8578 / 47) * v8 + (-99326 / 47) * v8 ^ 2 + (429544 / 47) * v8 ^ 3 + (-663320 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma gap_w_567 : sig (w 5) (w 6) (w 7) - v8 * H2w = ((-2876 / 47) + (66856 / 47) * v8 + (-492374 / 47) * v8 ^ 2 + (1533624 / 47) * v8 ^ 3 + (-1786020 / 47) * v8 ^ 4 : ℝ) := by
  simp [w, H2w, H2, hullCycle, sig, cw, dw, ew, fw, gw]
  linear_combination ((-3306884 / 2209) + (62343190 / 2209) * v8 + (-413637574 / 2209) * v8 ^ 2 + (1195684240 / 2209) * v8 ^ 3 + (-1268980600 / 2209) * v8 ^ 4 : ℝ) * vP

lemma gap_w_567_poly_pos : 0 < ((-2876 / 47) + (66856 / 47) * v8 + (-492374 / 47) * v8 ^ 2 + (1533624 / 47) * v8 ^ 3 + (-1786020 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]


end Heilbronn8
