import Heilbronn8.TriHull.HullSevenTightCore

/-!
# Broad scalar core for the hull-seven transfer

The geometric transfer does not in general reach the two-parameter fan in
`HullSevenTightCore`: its middle-ear surrogate still has two outer-ear
slacks.  This file records the correct four-parameter scalar seam.

The fan is

`1, s+1, t+1, w+1, u+1, 1, G`.

The proof uses two one-variable radial lower bounds.  This module deliberately
contains no coordinate-box hypothesis; the C24 retained records carry sign
paths, not spatial boxes.
-/

namespace Heilbronn8.TriHull

/-- The outer-product radial lower bound. -/
noncomputable def hullSevenRadialOuter (r : ℝ) : ℝ :=
  6 + 2 * r + 2 / r + 1 / r ^ 2

/-- The shifted-central-chord radial lower bound. -/
noncomputable def hullSevenRadialCentral (r : ℝ) : ℝ :=
  4 + 2 * r + 2 * r ^ 2 + 1 / r ^ 2 +
    2 * (r + 1) * Real.sqrt (r ^ 2 + 1)

/-- The sharp hull-seven denominator, written in the form used by the broad
core. -/
noncomputable def hullSevenSharpH : ℝ :=
  6 + hullSevenCoreRoot ^ 2 + 2 * hullSevenCoreRoot +
    2 / hullSevenCoreRoot

lemma hullSevenCoreRoot_pos : 0 < hullSevenCoreRoot := by
  linarith [hullSevenCoreRoot_mem.1]

lemma hullSevenReciprocalRoot_mem :
    (2 / 3 : ℝ) ≤ 1 / hullSevenCoreRoot ∧
      1 / hullSevenCoreRoot ≤ 1 := by
  have hs0 := hullSevenCoreRoot_pos
  have hs1 : 1 ≤ hullSevenCoreRoot := by
    linarith [hullSevenCoreRoot_mem.1]
  constructor
  · apply (le_div_iff₀ hs0).2
    nlinarith [hullSevenCoreRoot_mem.2]
  · apply (div_le_iff₀ hs0).2
    simpa using hs1

lemma hullSevenRadialOuter_at_reciprocalRoot :
    hullSevenRadialOuter (1 / hullSevenCoreRoot) = hullSevenSharpH := by
  have hs0 := hullSevenCoreRoot_pos
  unfold hullSevenRadialOuter hullSevenSharpH
  field_simp [hs0.ne']
  ring

/-- The radical identity at the sharp root.  It is just the quintic root
equation after clearing the fourth power of the denominator. -/
lemma hullSevenCoreRoot_radical_identity :
    (1 / hullSevenCoreRoot + 1) *
        Real.sqrt ((1 / hullSevenCoreRoot) ^ 2 + 1) =
      hullSevenCoreRoot + 1 - (1 / hullSevenCoreRoot) ^ 2 := by
  let s := hullSevenCoreRoot
  have hs0 : 0 < s := by
    dsimp [s]
    exact hullSevenCoreRoot_pos
  have hs1 : 1 ≤ s := by
    dsimp [s]
    linarith [hullSevenCoreRoot_mem.1]
  have hpoly :
      (s ^ 3 + s ^ 2 - 1) ^ 2 = (s + 1) ^ 2 * (s ^ 2 + 1) := by
    have hid :
        (s ^ 3 + s ^ 2 - 1) ^ 2 - (s + 1) ^ 2 * (s ^ 2 + 1) =
          s * hullSevenCoreQ s := by
      unfold hullSevenCoreQ
      ring
    have hQ : hullSevenCoreQ s = 0 := by
      dsimp [s]
      exact hullSevenCoreRoot_eq_zero
    rw [hQ, mul_zero] at hid
    linarith
  have hsqrtSq :
      (Real.sqrt ((1 / s) ^ 2 + 1)) ^ 2 = (1 / s) ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  have heqSq :
      ((1 / s + 1) * Real.sqrt ((1 / s) ^ 2 + 1)) ^ 2 =
        (s + 1 - (1 / s) ^ 2) ^ 2 := by
    rw [mul_pow, hsqrtSq]
    field_simp [hs0.ne']
    nlinarith [hpoly]
  have hleft :
      0 ≤ (1 / s + 1) * Real.sqrt ((1 / s) ^ 2 + 1) := by
    positivity
  have hinv : (1 / s) ^ 2 ≤ 1 := by
    have hdiv : 1 / s ≤ 1 := by
      apply (div_le_iff₀ hs0).2
      simpa using hs1
    have hdiv0 : 0 ≤ 1 / s := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiv)
      (by nlinarith : 0 ≤ 1 + 1 / s)]
  have hright : 0 ≤ s + 1 - (1 / s) ^ 2 := by
    nlinarith
  dsimp [s] at heqSq hleft hright ⊢
  nlinarith

lemma hullSevenRadialCentral_at_reciprocalRoot :
    hullSevenRadialCentral (1 / hullSevenCoreRoot) = hullSevenSharpH := by
  have hs0 := hullSevenCoreRoot_pos
  have hradical :
      2 * (1 / hullSevenCoreRoot + 1) *
          Real.sqrt ((1 / hullSevenCoreRoot) ^ 2 + 1) =
        2 * (hullSevenCoreRoot + 1 -
          (1 / hullSevenCoreRoot) ^ 2) := by
    calc
      2 * (1 / hullSevenCoreRoot + 1) *
          Real.sqrt ((1 / hullSevenCoreRoot) ^ 2 + 1) =
          2 * ((1 / hullSevenCoreRoot + 1) *
            Real.sqrt ((1 / hullSevenCoreRoot) ^ 2 + 1)) := by ring
      _ = 2 * (hullSevenCoreRoot + 1 -
          (1 / hullSevenCoreRoot) ^ 2) := by
        rw [hullSevenCoreRoot_radical_identity]
  unfold hullSevenRadialCentral hullSevenSharpH
  rw [hradical]
  field_simp [hs0.ne']
  ring

lemma v8_mul_hullSevenSharpH : v8 * hullSevenSharpH = 1 := by
  simpa [hullSevenSharpH] using hullSevenCoreRoot_v8_phi

/-- The outer radial bound decreases up to radius one.  This proof is kept
algebraic so that the broad core does not need a differentiability API. -/
lemma hullSevenRadialOuter_antitone {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    hullSevenRadialOuter y ≤ hullSevenRadialOuter x := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hxy0 : 0 < x * y := mul_pos hx hy0
  have hx1 : x ≤ 1 := le_trans hxy hy
  have hprodLe : x * y ≤ 1 := by
    have hmul : x * y ≤ x := by
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy)]
    exact le_trans hmul hx1
  have hinv : 1 ≤ 1 / (x * y) := by
    apply (le_div_iff₀ hxy0).2
    simpa using hprodLe
  have hbracket :
      0 ≤ -2 + 2 / (x * y) + (x + y) / (x ^ 2 * y ^ 2) := by
    have hlast : 0 ≤ (x + y) / (x ^ 2 * y ^ 2) := by positivity
    have htwice : 2 ≤ 2 / (x * y) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [htwice, hlast]
  have hid :
      hullSevenRadialOuter x - hullSevenRadialOuter y =
        (y - x) *
          (-2 + 2 / (x * y) + (x + y) / (x ^ 2 * y ^ 2)) := by
    unfold hullSevenRadialOuter
    field_simp [hx.ne', hy0.ne']
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hxy) hbracket

/-- The central radial bound increases from radius `2/3` onward.  The small
`6/5` square-root estimate leaves a rational margin `19/60`, avoiding the
larger second-derivative calculation. -/
lemma hullSevenRadialCentral_monotone {x y : ℝ}
    (hx : (2 / 3 : ℝ) ≤ x) (hxy : x ≤ y) :
    hullSevenRadialCentral x ≤ hullSevenRadialCentral y := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hsum0 : 0 ≤ x + y := by positivity
  have hsquares : x ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hsum0]
  have hsqrt :
      Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt (y ^ 2 + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hySquare : (4 / 9 : ℝ) ≤ y ^ 2 := by
    have hplus : 0 ≤ y + 2 / 3 := by positivity
    nlinarith [mul_nonneg (by linarith : 0 ≤ y - 2 / 3) hplus]
  have hrootSquare :
      (Real.sqrt (y ^ 2 + 1)) ^ 2 = y ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  have hrootLower : (6 / 5 : ℝ) ≤ Real.sqrt (y ^ 2 + 1) := by
    have hroot0 := Real.sqrt_nonneg (y ^ 2 + 1)
    nlinarith
  have hrootProduct :
      (6 / 5 : ℝ) * (y - x) ≤
        (y + 1) * Real.sqrt (y ^ 2 + 1) -
          (x + 1) * Real.sqrt (x ^ 2 + 1) := by
    have hid :
        (y + 1) * Real.sqrt (y ^ 2 + 1) -
            (x + 1) * Real.sqrt (x ^ 2 + 1) =
          (y - x) * Real.sqrt (y ^ 2 + 1) +
            (x + 1) *
              (Real.sqrt (y ^ 2 + 1) - Real.sqrt (x ^ 2 + 1)) := by
      ring
    rw [hid]
    have hfirst := mul_le_mul_of_nonneg_left hrootLower
      (sub_nonneg.mpr hxy)
    have hsecond :
        0 ≤ (x + 1) *
          (Real.sqrt (y ^ 2 + 1) - Real.sqrt (x ^ 2 + 1)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hsqrt)
    linarith
  have hpoly : 4 * (x + y) ≤ 27 * x ^ 2 * y ^ 2 := by
    let a := x - 2 / 3
    let b := y - 2 / 3
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hb : 0 ≤ b := by dsimp [b]; linarith
    have hid :
        27 * x ^ 2 * y ^ 2 - 4 * (x + y) =
          12 * a + 12 * b + 12 * a ^ 2 + 12 * b ^ 2 +
            48 * a * b + 36 * a ^ 2 * b + 36 * a * b ^ 2 +
              27 * a ^ 2 * b ^ 2 := by
      dsimp [a, b]
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hden : 0 < x ^ 2 * y ^ 2 := by positivity
  have hcoefficient :
      (x + y) / (x ^ 2 * y ^ 2) ≤ 27 / 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith [hpoly]
  have hcoefficientMul := mul_le_mul_of_nonneg_left hcoefficient
    (sub_nonneg.mpr hxy)
  have hreciprocal :
      1 / y ^ 2 - 1 / x ^ 2 =
        -(y - x) * ((x + y) / (x ^ 2 * y ^ 2)) := by
    field_simp [hx0.ne', hy0.ne']
    ring
  have hdiff :
      hullSevenRadialCentral y - hullSevenRadialCentral x =
        2 * (y - x) + 2 * (y ^ 2 - x ^ 2) +
          (1 / y ^ 2 - 1 / x ^ 2) +
            2 * ((y + 1) * Real.sqrt (y ^ 2 + 1) -
              (x + 1) * Real.sqrt (x ^ 2 + 1)) := by
    unfold hullSevenRadialCentral
    ring
  rw [← sub_nonneg, hdiff, hreciprocal]
  have hsum : (4 / 3 : ℝ) ≤ x + y := by linarith
  nlinarith

/-- If both radial estimates are available, their lower envelope is the sharp
hull-seven value. -/
theorem hullSeven_v8_of_radial_bounds {H r : ℝ}
    (hr : 0 < r)
    (houter : hullSevenRadialOuter r ≤ H)
    (hcentral : hullSevenRadialCentral r ≤ H) :
    1 ≤ v8 * H := by
  let r0 := 1 / hullSevenCoreRoot
  have hr0pos : 0 < r0 := by
    dsimp [r0]
    exact one_div_pos.mpr hullSevenCoreRoot_pos
  have hr0lo : (2 / 3 : ℝ) ≤ r0 := by
    dsimp [r0]
    exact hullSevenReciprocalRoot_mem.1
  have hr0hi : r0 ≤ 1 := by
    dsimp [r0]
    exact hullSevenReciprocalRoot_mem.2
  have hsharp : hullSevenSharpH ≤ H := by
    by_cases hleft : r ≤ r0
    · have hradial : hullSevenRadialOuter r0 ≤ hullSevenRadialOuter r :=
        hullSevenRadialOuter_antitone hr hleft hr0hi
      rw [show hullSevenRadialOuter r0 = hullSevenSharpH by
        dsimp [r0]
        exact hullSevenRadialOuter_at_reciprocalRoot] at hradial
      exact le_trans hradial houter
    · have hright : r0 ≤ r := le_of_not_ge hleft
      have hradial :
          hullSevenRadialCentral r0 ≤ hullSevenRadialCentral r :=
        hullSevenRadialCentral_monotone hr0lo hright
      rw [show hullSevenRadialCentral r0 = hullSevenSharpH by
        dsimp [r0]
        exact hullSevenRadialCentral_at_reciprocalRoot] at hradial
      exact le_trans hradial hcentral
  have hmul := mul_le_mul_of_nonneg_left hsharp v8_pos.le
  rw [v8_mul_hullSevenSharpH] at hmul
  exact hmul

/-- Positivity of the two shifted central factors follows from the product
floor.  The negative-negative alternative would have product below `z^2`,
while the right side is strictly above `z^2`. -/
lemma hullSeven_shifted_factors_pos {s t w u : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hw : 0 < w) (hu : 0 < u)
    (hcentral :
      (t + 1) * (w + 1) * (t * w + 1) ≤
        (s + 1 - t * w) * (u + 1 - t * w)) :
    0 < s + 1 - t * w ∧ 0 < u + 1 - t * w := by
  let z := t * w
  let a := s + 1 - z
  let b := u + 1 - z
  have hz : 0 < z := by dsimp [z]; positivity
  have hab : 0 < a * b := by
    dsimp [a, b, z] at hcentral ⊢
    exact lt_of_lt_of_le (by positivity) hcentral
  rcases (mul_pos_iff.mp hab) with hpos | hneg
  · simpa [a, b] using hpos
  · rcases hneg with ⟨haNeg, hbNeg⟩
    exfalso
    have haZ : -a < z := by dsimp [a]; linarith
    have hbZ : -b < z := by dsimp [b]; linarith
    have hnegB : 0 < -b := neg_pos.mpr hbNeg
    have hsmall : (-a) * (-b) < z * z :=
      mul_lt_mul haZ (le_of_lt hbZ) hnegB hz.le
    have hzLeft : z < (t + 1) * (w + 1) := by
      dsimp [z]
      nlinarith
    have hzRight : z < z + 1 := by linarith
    have hfactorNonneg : 0 ≤ (t + 1) * (w + 1) := by positivity
    have hlarge : z * z < (t + 1) * (w + 1) * (z + 1) := by
      exact mul_lt_mul hzLeft (le_of_lt hzRight) hz hfactorNonneg
    have habEq : a * b = (-a) * (-b) := by ring
    have hcentral' :
        (t + 1) * (w + 1) * (z + 1) ≤ a * b := by
      simpa [a, b, z] using hcentral
    rw [habEq] at hcentral'
    linarith

set_option maxHeartbeats 800000 in
/-- Correct four-parameter scalar seam for the hull-seven transfer.

Unlike the narrower tight core, this theorem permits the two outer-ear
slacks `s*t-1` and `u*w-1`. -/
theorem hullSeven_broad_core_v8 {s t w u G : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hw : 0 < w) (hu : 0 < u)
    (hst : 1 ≤ s * t) (huw : 1 ≤ u * w)
    (hG : 1 / (t * w) ≤ G)
    (hcentral :
      (t + 1) * (w + 1) * (t * w + 1) ≤
        (s + 1 - t * w) * (u + 1 - t * w)) :
    1 ≤ v8 * (6 + s + t + w + u + G) := by
  let z := t * w
  let r := Real.sqrt z
  have hz : 0 < z := by dsimp [z]; positivity
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hz
  have hrsq : r ^ 2 = z := by
    dsimp [r]
    exact Real.sq_sqrt hz.le
  have hrsq' : r ^ 2 = t * w := by simpa [z] using hrsq
  have htw : 2 * r ≤ t + w := by
    nlinarith [sq_nonneg (t - w), hrsq']
  have hsInv : 1 / t ≤ s := by
    apply (div_le_iff₀ ht).2
    simpa using hst
  have huInv : 1 / w ≤ u := by
    apply (div_le_iff₀ hw).2
    simpa using huw
  have hinvIdentity : 1 / t + 1 / w = (t + w) / r ^ 2 := by
    field_simp [ht.ne', hw.ne', hr.ne']
    nlinarith [hrsq']
  have hinvLower : 2 / r ≤ 1 / t + 1 / w := by
    rw [hinvIdentity]
    apply (div_le_div_iff₀ hr (sq_pos_of_pos hr)).2
    have hm := mul_nonneg (sub_nonneg.mpr htw) hr.le
    nlinarith [hrsq', hm]
  have hsu : 2 / r ≤ s + u :=
    le_trans hinvLower (add_le_add hsInv huInv)
  have hGr : 1 / r ^ 2 ≤ G := by
    rw [hrsq]
    simpa [z] using hG
  have houter :
      hullSevenRadialOuter r ≤ 6 + s + t + w + u + G := by
    unfold hullSevenRadialOuter
    linarith

  obtain ⟨ha, hb⟩ :=
    hullSeven_shifted_factors_pos hs ht hw hu hcentral
  let a := s + 1 - z
  let b := u + 1 - z
  have ha' : 0 < a := by simpa [a, z] using ha
  have hb' : 0 < b := by simpa [b, z] using hb
  have htwFactor : (r + 1) ^ 2 ≤ (t + 1) * (w + 1) := by
    nlinarith [hrsq']
  have hfactorBound :
      (r + 1) ^ 2 * (r ^ 2 + 1) ≤ a * b := by
    calc
      (r + 1) ^ 2 * (r ^ 2 + 1) ≤
          (t + 1) * (w + 1) * (r ^ 2 + 1) := by
        exact mul_le_mul_of_nonneg_right htwFactor (by positivity)
      _ = (t + 1) * (w + 1) * (z + 1) := by rw [hrsq]
      _ ≤ a * b := by simpa [a, b, z] using hcentral
  have habSquare : 4 * a * b ≤ (a + b) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hsqrtSq :
      (Real.sqrt (r ^ 2 + 1)) ^ 2 = r ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  have htargetSquare :
      (2 * (r + 1) * Real.sqrt (r ^ 2 + 1)) ^ 2 ≤
        (a + b) ^ 2 := by
    calc
      (2 * (r + 1) * Real.sqrt (r ^ 2 + 1)) ^ 2 =
          4 * (r + 1) ^ 2 * (r ^ 2 + 1) := by
        rw [mul_pow, mul_pow, hsqrtSq]
        ring
      _ ≤ 4 * (a * b) := by nlinarith [hfactorBound]
      _ ≤ (a + b) ^ 2 := by nlinarith [habSquare]
  have htargetPos :
      0 ≤ 2 * (r + 1) * Real.sqrt (r ^ 2 + 1) := by positivity
  have habSumPos : 0 ≤ a + b := by linarith
  have hshifted :
      2 * (r + 1) * Real.sqrt (r ^ 2 + 1) ≤ a + b := by
    exact (sq_le_sq₀ htargetPos habSumPos).1 htargetSquare
  have hsuCentral :
      2 * z - 2 + 2 * (r + 1) * Real.sqrt (r ^ 2 + 1) ≤ s + u := by
    dsimp [a, b] at hshifted
    linarith
  have hsuCentral' :
      2 * r ^ 2 - 2 + 2 * (r + 1) * Real.sqrt (r ^ 2 + 1) ≤ s + u := by
    rw [← hrsq] at hsuCentral
    exact hsuCentral
  have hcentralBound :
      hullSevenRadialCentral r ≤ 6 + s + t + w + u + G := by
    unfold hullSevenRadialCentral
    linarith [hsuCentral', htw, hGr]
  exact hullSeven_v8_of_radial_bounds hr houter hcentralBound

/-- Exact geometric-transfer payload required by the broad scalar theorem.
This replaces the too-strong two-variable transfer seam: the producer may
retain both outer-ear slacks. -/
structure HullSevenBroadTransferData (H : ℝ) where
  s : ℝ
  t : ℝ
  w : ℝ
  u : ℝ
  G : ℝ
  s_pos : 0 < s
  t_pos : 0 < t
  w_pos : 0 < w
  u_pos : 0 < u
  left_outer : 1 ≤ s * t
  right_outer : 1 ≤ u * w
  closing : 1 / (t * w) ≤ G
  central :
    (t + 1) * (w + 1) * (t * w + 1) ≤
      (s + 1 - t * w) * (u + 1 - t * w)
  area : 6 + s + t + w + u + G ≤ H

/-- Correct continuation theorem for a future recurrence/geometry producer. -/
theorem hullSeven_v8_of_broad_transfer {H : ℝ}
    (data : HullSevenBroadTransferData H) :
    1 ≤ v8 * H := by
  have hcore := hullSeven_broad_core_v8 data.s_pos data.t_pos data.w_pos
    data.u_pos data.left_outer data.right_outer data.closing data.central
  have hmul := mul_le_mul_of_nonneg_left data.area v8_pos.le
  linarith

end Heilbronn8.TriHull
