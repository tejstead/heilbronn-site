import Heilbronn8.TriHull.HullSevenType2ProductScalar

/-!
# Kernel certificate for the hull-seven type-2 two-variable closer

The checker is the deterministic reconstruction documented by
`proofs/convex-n8/h7_type2_2d_exact_generator.py`, SHA256
`6c0c4424903356cc5b5d038da39e6dfebf8956cf0d4f73b6f51e26802ed8e446`.
The durable 20-bit certificate generator beside it has SHA256
`5e4280ea48a41d8ea9b763f766f1eeeb26b62f630e50a7127b1fcc398ba06a58`.

The lower branch closes 2,123 nodes at depth at most 25.  The upper branch
closes 1,839 nodes at depth at most 22.  Both facts below use ordinary kernel
`decide`; no native evaluator or external certificate is trusted.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull
namespace HullSevenType2TwoVar

set_option maxRecDepth 1000000 in
theorem lower_root_checked : check .lower 26 lowerRoot = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem upper_root_checked : check .upper 26 upperRoot = true := by
  decide +kernel

private lemma lower_root_positive : lowerRoot.Positive := by
  norm_num [lowerRoot, Box.Positive]

private lemma upper_root_positive : upperRoot.Positive := by
  norm_num [upperRoot, Box.Positive]

private lemma reciprocal_domain {x d : ℝ} (hx : 1 ≤ x)
    (hprod : 1 < x * d) : 1 / x < d := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  apply (div_lt_iff₀ hxpos).2
  nlinarith [hprod]

private lemma term_nonneg {x d y : ℝ} (hx : 1 ≤ x)
    (hprod : 1 < x * d) (hy : 0 ≤ y) :
    0 ≤ y * (1 + 1 / d) := by
  have hd := reciprocal_domain hx hprod
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hdpos : 0 < d := (one_div_pos.mpr hxpos).trans hd
  exact mul_nonneg hy (by positivity)

private lemma root_rad_upper {x d y t : ℝ} (hx : 1 ≤ x)
    (hprod : 1 < x * d) (hy : 0 ≤ y) (ht : 0 ≤ t)
    (hle : y * (1 + 1 / d) + 2 * t ≤ 19 / 2) :
    t ^ 2 ≤ 361 / 16 := by
  have hterm := term_nonneg hx hprod hy
  have htupper : t ≤ 19 / 4 := by nlinarith
  nlinarith [sq_nonneg (t - 19 / 4)]

private lemma lower_two_x_le_rad {x d : ℝ} (hx : 1 ≤ x)
    (hdom : 1 / x < d) : 2 * x ≤ radValue .lower x d := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hdpos : 0 < d := (one_div_pos.mpr hxpos).trans hdom
  have hxdiv : 0 ≤ x / d := by positivity
  let first : ℝ := 2 * x + d + x / d
  have hfirst0 : 0 ≤ first := by dsimp [first]; positivity
  have htwo : 2 * x ≤ first := by
    dsimp [first]
    linarith [hdpos.le, hxdiv]
  have hgrow : first ≤ first * (d + 1) := by
    have hm : 0 ≤ first * d := mul_nonneg hfirst0 hdpos.le
    nlinarith
  simpa [radValue, first] using htwo.trans hgrow

private lemma upper_d_sq_le_rad {x d : ℝ} (hx : 1 ≤ x)
    (hdom : 1 / x < d) : d ^ 2 ≤ radValue .upper x d := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hdpos : 0 < d := (one_div_pos.mpr hxpos).trans hdom
  have hq : d ^ 2 ≤ d * (2 * x + d) := by
    nlinarith [mul_nonneg hdpos.le hxpos.le]
  let first : ℝ := d * (2 * x + d) + x
  have hfirst0 : 0 ≤ first := by dsimp [first]; positivity
  have hdfirst : d ^ 2 ≤ first := by dsimp [first]; linarith
  have hinv0 : 0 ≤ 1 / x := by positivity
  have hgrow : first ≤ first * (1 + 1 / x) := by
    have hm : 0 ≤ first * (1 / x) := mul_nonneg hfirst0 hinv0
    nlinarith
  simpa [radValue, first] using hdfirst.trans hgrow

/-- The lower (`d <= X`) branch of the exact two-variable type-2 closer.
The variables `y` and `t` may be any nonnegative square roots of the displayed
rational functions; no choice of `Real.sqrt` is built into the interface. -/
theorem hullSeven_type2_twoVar_lower_gt
    {x d y t : ℝ}
    (hx : 1 ≤ x)
    (hprod : 1 < x * d)
    (horder : d ≤ x)
    (hy : 0 ≤ y)
    (ht : 0 ≤ t)
    (hysq : y ^ 2 = ySqValue x d)
    (htsq : t ^ 2 = radValue .lower x d) :
    19 / 2 < y * (1 + 1 / d) + 2 * t := by
  have hdom := reciprocal_domain hx hprod
  by_contra hn
  have hle : y * (1 + 1 / d) + 2 * t ≤ 19 / 2 := le_of_not_gt hn
  have hrad : radValue .lower x d ≤ 361 / 16 := by
    rw [← htsq]
    exact root_rad_upper hx hprod hy ht hle
  have hxupper : x ≤ 361 / 32 := by
    have htwo := lower_two_x_le_rad hx hdom
    linarith
  have hdlo : (32 : ℝ) / 361 ≤ d := by
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have hinv : 1 / (361 / 32 : ℝ) ≤ 1 / x :=
      one_div_le_one_div_of_le hxpos hxupper
    norm_num at hinv ⊢
    exact hinv.trans (by simpa only [one_div] using hdom.le)
  have hcontains : lowerRoot.Contains x d := by
    norm_num [lowerRoot, Box.Contains]
    exact ⟨hx, hxupper, hdlo, horder.trans hxupper⟩
  have hfeasible : Feasible .lower lowerRoot x d y t :=
    { contains := hcontains
      x_floor := hx
      domain := hdom
      order := horder
      y_nonneg := hy
      t_nonneg := ht
      y_sq := hysq
      t_sq := htsq }
  exact (not_le_of_gt
    (check_sound lower_root_positive lower_root_checked hfeasible)) hle

/-- The upper (`X <= d`) branch of the exact two-variable type-2 closer. -/
theorem hullSeven_type2_twoVar_upper_gt
    {x d y t : ℝ}
    (hx : 1 ≤ x)
    (hprod : 1 < x * d)
    (horder : x ≤ d)
    (hy : 0 ≤ y)
    (ht : 0 ≤ t)
    (hysq : y ^ 2 = ySqValue x d)
    (htsq : t ^ 2 = radValue .upper x d) :
    19 / 2 < y * (1 + 1 / d) + 2 * t := by
  have hdom := reciprocal_domain hx hprod
  by_contra hn
  have hle : y * (1 + 1 / d) + 2 * t ≤ 19 / 2 := le_of_not_gt hn
  have hrad : radValue .upper x d ≤ 361 / 16 := by
    rw [← htsq]
    exact root_rad_upper hx hprod hy ht hle
  have hdupper : d ≤ 19 / 4 := by
    have hdsq := upper_d_sq_le_rad hx hdom
    have hdpos : 0 < d := (one_div_pos.mpr
      (lt_of_lt_of_le (by norm_num) hx)).trans hdom
    nlinarith [sq_nonneg (d - 19 / 4)]
  have hcontains : upperRoot.Contains x d := by
    norm_num [upperRoot, Box.Contains]
    exact ⟨hx, horder.trans hdupper, hx.trans horder, hdupper⟩
  have hfeasible : Feasible .upper upperRoot x d y t :=
    { contains := hcontains
      x_floor := hx
      domain := hdom
      order := horder
      y_nonneg := hy
      t_nonneg := ht
      y_sq := hysq
      t_sq := htsq }
  exact (not_le_of_gt
    (check_sound upper_root_positive upper_root_checked hfeasible)) hle

end HullSevenType2TwoVar

/-- The single numerical capability consumed by the compact product-ear
reduction. -/
theorem hullSevenType2TwoVarBound_checked : HullSevenType2TwoVarBound :=
  ⟨HullSevenType2TwoVar.hullSeven_type2_twoVar_lower_gt,
    HullSevenType2TwoVar.hullSeven_type2_twoVar_upper_gt⟩

end Heilbronn8.TriHull
