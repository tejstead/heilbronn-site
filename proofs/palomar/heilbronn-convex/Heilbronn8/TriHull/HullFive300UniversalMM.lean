import Heilbronn8.TriHull.HullFive300UniversalME

set_option maxHeartbeats 0

/-!
# Rational closure of the double-negative outer-cross orbit

This file closes the remaining `++--` outer orbit in the adjacent central
chart.  The two local parameters have positive orientation, while `AXR` and
`BQD` have negative orientation.  After eliminating the original fan
coordinates, the central variables are

* `r = AQR - 2`, `q = BQR - 2`;
* `C = c - 2`, `F = f - 2`, `n = -CQR - 2`;
* `X = BXC - 2`, `Y = CDA - 2`;
* `W = g + p + Q - Delta`.

The proof is entirely rational.  First we prove the sharp `C = F = 0`
estimate.  For `W <= 25 / 4`, a cleared two-variable polynomial shows that
positive `C,F` cannot lower the estimate.  For `W >= 25 / 4`, the two ear
rows themselves contradict a total below eleven.
-/

namespace Heilbronn8.TriHull

/-- The two-variable compression estimate used in the small-`W` branch. -/
lemma hullFive300_mm_compression
    {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F) :
    F * (41 / 8 + C) / (4 + F) + C * (41 / 8 + F) / (4 + C) ≤
      (33 / 25 : ℝ) * (C + F) := by
  let u : ℝ := C + F
  let v : ℝ := C * F
  let den : ℝ := (4 + C) * (4 + F)
  let L : ℝ :=
    (31 / 50 : ℝ) * u + (132 / 25 : ℝ) * u ^ 2 +
      v * ((8 / 25 : ℝ) * u - 73 / 4)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hC4 : 0 < 4 + C := by linarith
  have hF4 : 0 < 4 + F := by linarith
  have hden : 0 < den := by dsimp [den]; positivity
  have huv : 4 * v ≤ u ^ 2 := by
    dsimp [u, v]
    nlinarith [sq_nonneg (C - F)]
  have hclear :
      (((33 / 25 : ℝ) * (C + F) -
          (F * (41 / 8 + C) / (4 + F) +
            C * (41 / 8 + F) / (4 + C))) * den) = L := by
    dsimp [den, L, u, v]
    field_simp [ne_of_gt hC4, ne_of_gt hF4] <;> ring
  have hL400a :
      400 * L =
        248 * u + 2112 * u ^ 2 + 4 * v * (32 * u - 1825) := by
    dsimp [L]
    ring
  have hL400b :
      400 * L =
        (248 * u + 287 * u ^ 2 + 32 * u ^ 3) +
          (u ^ 2 - 4 * v) * (1825 - 32 * u) := by
    dsimp [L]
    ring
  have hL : 0 ≤ L := by
    by_cases hq : 0 ≤ 32 * u - 1825
    · have hqv : 0 ≤ 4 * v * (32 * u - 1825) :=
        mul_nonneg (mul_nonneg (by norm_num) hv) hq
      have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
      nlinarith [hL400a]
    · have hq' : 0 ≤ 1825 - 32 * u := by linarith
      have hdisc : 0 ≤ u ^ 2 - 4 * v := by linarith
      have hprod : 0 ≤ (u ^ 2 - 4 * v) * (1825 - 32 * u) :=
        mul_nonneg hdisc hq'
      have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
      have hu3 : 0 ≤ u ^ 3 := by
        rw [show u ^ 3 = u ^ 2 * u by ring]
        exact mul_nonneg hu2 hu
      nlinarith [hL400b]
  by_contra hnot
  have hneg :
      (33 / 25 : ℝ) * (C + F) -
          (F * (41 / 8 + C) / (4 + F) +
            C * (41 / 8 + F) / (4 + C)) < 0 := by
    linarith
  have hprodneg :
      (((33 / 25 : ℝ) * (C + F) -
          (F * (41 / 8 + C) / (4 + F) +
            C * (41 / 8 + F) / (4 + C))) * den) < 0 :=
    mul_neg_of_neg_of_pos hneg hden
  nlinarith [hclear]

/-- Sharp rational estimate for the transformed system when `c=f=2`. -/
lemma hullFive300_mm_base
    {W r q : ℝ}
    (hW : 0 < W) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hWr : 4 ≤ W + r) (hWq : 4 ≤ W + q)
    (hshape : 4 + r * q ≤ (r + q) * (W + r + q - 2)) :
    11 ≤ W + (r + q) - 2 + (12 + 4 * (r + q) + r * q) / W +
      2 * W / (4 + r) + 2 * W / (4 + q) := by
  let s : ℝ := r + q
  let p : ℝ := r * q
  let D : ℝ := 16 + 4 * s + p
  let K : ℝ := 12 + 4 * s + p
  let C0 : ℝ := s * (W + s - 2) - 4 - p
  let J : ℝ := W + s - 2 + K / W + 2 * W * (8 + s) / D
  let G : ℝ :=
    (32 + 6 * s + p) * W ^ 2 + D * (s - 13) * W + D * K
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hr4 : 0 < 4 + r := by linarith
  have hq4 : 0 < 4 + q := by linarith
  have hDfactor : D = (4 + r) * (4 + q) := by
    dsimp [D, s, p]
    ring
  have hD : 0 < D := by rw [hDfactor]; positivity
  have hC0 : 0 ≤ C0 := by
    dsimp [C0, s, p]
    linarith
  have hEarCombine :
      2 * W / (4 + r) + 2 * W / (4 + q) =
        2 * W * (8 + s) / D := by
    rw [hDfactor]
    dsimp [s]
    field_simp [ne_of_gt hr4, ne_of_gt hq4] <;> ring
  have hClear : W * D * (J - 11) = G := by
    dsimp [J, G]
    field_simp [ne_of_gt hW, ne_of_gt hD] <;> ring

  have hG : 0 ≤ G := by
    by_cases hW4 : 4 ≤ W
    · let H0 : ℝ := (32 + 6 * s + p) * (W + 4) + D * (s - 13)
      have hsSquare : 4 * p ≤ s ^ 2 := by
        dsimp [s, p]
        nlinarith [sq_nonneg (r - q)]
      have hGid :
          G = 32 * C0 + p * (p + 12 * s + 24) +
            (W - 4) * (H0 - 32 * s) := by
        dsimp [G, C0, H0, D, K]
        ring
      have hHid :
          H0 - 32 * s =
            (4 * s ^ 2 - 20 * s + 48 + p * (s - 5)) +
              (32 + 6 * s + p) * (W - 4) := by
        dsimp [H0, D]
        ring
      have hcore : 0 ≤ 4 * s ^ 2 - 20 * s + 48 + p * (s - 5) := by
        by_cases hs5 : 5 ≤ s
        · have hsp : 0 ≤ p * (s - 5) :=
            mul_nonneg hp (sub_nonneg.mpr hs5)
          have hss : 0 ≤ 4 * s * (s - 5) :=
            mul_nonneg (mul_nonneg (by norm_num) hs) (sub_nonneg.mpr hs5)
          nlinarith
        · have hs5' : s ≤ 5 := le_of_not_ge hs5
          have hps : -5 * p ≤ p * (s - 5) := by
            nlinarith [mul_nonneg hp hs]
          have hquad : 0 ≤ 11 * s ^ 2 - 80 * s + 192 := by
            nlinarith [sq_nonneg (11 * s - 40)]
          nlinarith
      have hcoef : 0 ≤ 32 + 6 * s + p := by linarith
      have htail : 0 ≤ (32 + 6 * s + p) * (W - 4) :=
        mul_nonneg hcoef (sub_nonneg.mpr hW4)
      have hH0 : 0 ≤ H0 - 32 * s := by nlinarith [hHid]
      have hlast : 0 ≤ (W - 4) * (H0 - 32 * s) :=
        mul_nonneg (sub_nonneg.mpr hW4) hH0
      have hpterm : 0 ≤ p * (p + 12 * s + 24) := by positivity
      nlinarith [hGid]
    · have hW4' : W ≤ 4 := le_of_not_ge hW4
      let l : ℝ := 4 - W
      let t : ℝ := s - l
      let h : ℝ := p - l * t
      let B0 : ℝ :=
        8 * t ^ 2 + 15 * l * t + 44 * t + 52 * l + 2 * l ^ 2 - 48
      have hl : 0 ≤ l := by dsimp [l]; linarith
      have hrl : l ≤ r := by dsimp [l]; linarith [hWr]
      have hql : l ≤ q := by dsimp [l]; linarith [hWq]
      have ht : l ≤ t := by dsimp [t, s]; linarith
      have ht0 : 0 ≤ t := le_trans hl ht
      have hhId : h = (r - l) * (q - l) := by
        dsimp [h, t, s, p]
        ring
      have hh : 0 ≤ h := by
        rw [hhId]
        exact mul_nonneg (sub_nonneg.mpr hrl) (sub_nonneg.mpr hql)
      have hC0h : C0 + h = t ^ 2 + 2 * t + 2 * l - 4 := by
        dsimp [C0, h, t, l, s, p]
        ring
      have htl : 1 ≤ t + l := by
        by_contra hnot
        have hlt : t + l < 1 := lt_of_not_ge hnot
        have ht1 : t < 1 := by linarith
        have htSq : t ^ 2 ≤ t := by
          have hprod := mul_nonneg ht0 (by linarith : 0 ≤ 1 - t)
          nlinarith
        nlinarith [hC0h]
      have hBid :
          B0 = 8 * (C0 + h) + 15 * l * t + 28 * t + 36 * l +
            2 * l ^ 2 - 16 := by
        dsimp [B0]
        rw [hC0h]
        ring
      have hrem : 12 ≤ 28 * t + 36 * l - 16 := by nlinarith
      have hB0 : 0 ≤ B0 := by
        have hltprod : 0 ≤ l * t := mul_nonneg hl ht0
        nlinarith [hBid, mul_nonneg hl hl]
      have hGid :
          G = 32 * C0 + h ^ 2 + h * (l * t + 12 * t + 17 * l + 24) +
            l * B0 := by
        dsimp [G, C0, h, t, l, B0, D, K, s, p]
        ring
      have hhterm : 0 ≤ h * (l * t + 12 * t + 17 * l + 24) := by
        have : 0 ≤ l * t + 12 * t + 17 * l + 24 := by positivity
        exact mul_nonneg hh this
      have hlB : 0 ≤ l * B0 := mul_nonneg hl hB0
      nlinarith [hGid, sq_nonneg h]

  change 11 ≤ W + s - 2 + K / W +
    2 * W / (4 + r) + 2 * W / (4 + q)
  have htoJ :
      W + s - 2 + K / W + 2 * W / (4 + r) + 2 * W / (4 + q) = J := by
    dsimp [J]
    linarith [hEarCombine]
  rw [htoJ]
  by_contra hnot
  have hJneg : J - 11 < 0 := by linarith
  have hWD : 0 < W * D := mul_pos hW hD
  have hneg : W * D * (J - 11) < 0 := mul_neg_of_pos_of_neg hWD hJneg
  nlinarith [hClear]

/-- Complete transformed closure of the double-negative outer-cross orbit. -/
theorem hullFive300_mm_transformed_scalar
    {W r q C F n X Y : ℝ}
    (hW : 0 < W)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hn : 0 ≤ n) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hWr : 4 ≤ W + r) (hWq : 4 ≤ W + q)
    (hshape : 4 + r * q ≤ (r + q) * (W + r + q - 2))
    (hNrow : (2 + n) * W =
      (2 + r) * (4 + q + C) + (2 + q) * (2 + F))
    (hEarX : 2 * W - (2 + C) * F ≤ X * (4 + r + F))
    (hEarY : 2 * W - (2 + F) * C ≤ Y * (4 + q + C)) :
    11 ≤ W + r + q + C + F + n + X + Y := by
  let s : ℝ := r + q
  let u : ℝ := C + F
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hbase := hullFive300_mm_base hW hr hq hWr hWq hshape
  by_cases hsmall : W ≤ 25 / 4
  · let A0 : ℝ := 4 + r
    let B0 : ℝ := 4 + q
    let DX : ℝ :=
      F * (2 * W + A0 * (2 + C)) / (A0 * (A0 + F))
    let DY : ℝ :=
      C * (2 * W + B0 * (2 + F)) / (B0 * (B0 + C))
    have hA0 : 0 < A0 := by dsimp [A0]; linarith
    have hB0 : 0 < B0 := by dsimp [B0]; linarith
    have hA0F : 0 < A0 + F := by dsimp [A0]; linarith
    have hB0C : 0 < B0 + C := by dsimp [B0]; linarith
    have h4F : 0 < 4 + F := by linarith
    have h4C : 0 < 4 + C := by linarith
    have hXraw : 2 * W / A0 - DX ≤ X := by
      have hraw : (2 * W - (2 + C) * F) / (A0 + F) ≤ X := by
        apply (div_le_iff₀ hA0F).2
        dsimp [A0] at *
        nlinarith
      have hid :
          2 * W / A0 - DX = (2 * W - (2 + C) * F) / (A0 + F) := by
        dsimp [DX]
        field_simp [ne_of_gt hA0, ne_of_gt hA0F] <;> ring
      rw [hid]
      exact hraw
    have hYraw : 2 * W / B0 - DY ≤ Y := by
      have hraw : (2 * W - (2 + F) * C) / (B0 + C) ≤ Y := by
        apply (div_le_iff₀ hB0C).2
        dsimp [B0] at *
        nlinarith
      have hid :
          2 * W / B0 - DY = (2 * W - (2 + F) * C) / (B0 + C) := by
        dsimp [DY]
        field_simp [ne_of_gt hB0, ne_of_gt hB0C] <;> ring
      rw [hid]
      exact hraw
    have hWA : 2 * W / A0 ≤ 25 / 8 := by
      apply (div_le_iff₀ hA0).2
      dsimp [A0]
      nlinarith
    have hWB : 2 * W / B0 ≤ 25 / 8 := by
      apply (div_le_iff₀ hB0).2
      dsimp [B0]
      nlinarith
    have hDXid : DX = F * (2 * W / A0 + 2 + C) / (A0 + F) := by
      dsimp [DX]
      field_simp [ne_of_gt hA0, ne_of_gt hA0F] <;> ring
    have hDYid : DY = C * (2 * W / B0 + 2 + F) / (B0 + C) := by
      dsimp [DY]
      field_simp [ne_of_gt hB0, ne_of_gt hB0C] <;> ring
    have hDX : DX ≤ F * (41 / 8 + C) / (4 + F) := by
      rw [hDXid]
      have hnum0 : 0 ≤ F * (2 * W / A0 + 2 + C) := by positivity
      have hnum :
          F * (2 * W / A0 + 2 + C) ≤ F * (41 / 8 + C) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hF
      have hfirst :
          F * (2 * W / A0 + 2 + C) / (A0 + F) ≤
            F * (41 / 8 + C) / (A0 + F) :=
        (div_le_div_iff_of_pos_right hA0F).2 hnum
      have hnum1 : 0 ≤ F * (41 / 8 + C) := by positivity
      have hsecond :
          F * (41 / 8 + C) / (A0 + F) ≤
            F * (41 / 8 + C) / (4 + F) := by
        apply (div_le_div_iff₀ hA0F h4F).2
        have hden : 4 + F ≤ A0 + F := by dsimp [A0]; linarith
        exact mul_le_mul_of_nonneg_left hden hnum1
      exact hfirst.trans hsecond
    have hDY : DY ≤ C * (41 / 8 + F) / (4 + C) := by
      rw [hDYid]
      have hnum :
          C * (2 * W / B0 + 2 + F) ≤ C * (41 / 8 + F) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hC
      have hfirst :
          C * (2 * W / B0 + 2 + F) / (B0 + C) ≤
            C * (41 / 8 + F) / (B0 + C) :=
        (div_le_div_iff_of_pos_right hB0C).2 hnum
      have hnum1 : 0 ≤ C * (41 / 8 + F) := by positivity
      have hsecond :
          C * (41 / 8 + F) / (B0 + C) ≤
            C * (41 / 8 + F) / (4 + C) := by
        apply (div_le_div_iff₀ hB0C h4C).2
        have hden : 4 + C ≤ B0 + C := by dsimp [B0]; linarith
        exact mul_le_mul_of_nonneg_left hden hnum1
      exact hfirst.trans hsecond
    have hcompress := hullFive300_mm_compression hC hF
    have hDXY : DX + DY ≤ (33 / 25 : ℝ) * u := by
      dsimp [u]
      linarith
    have hLamC : (33 / 25 : ℝ) ≤ 1 + (2 + r) / W := by
      have hratio : (8 / 25 : ℝ) ≤ (2 + r) / W := by
        apply (le_div_iff₀ hW).2
        nlinarith [hsmall]
      nlinarith
    have hLamF : (33 / 25 : ℝ) ≤ 1 + (2 + q) / W := by
      have hratio : (8 / 25 : ℝ) ≤ (2 + q) / W := by
        apply (le_div_iff₀ hW).2
        nlinarith [hsmall]
      nlinarith
    have hcost :
        (33 / 25 : ℝ) * u ≤
          (1 + (2 + r) / W) * C + (1 + (2 + q) / W) * F := by
      have hCmul := mul_le_mul_of_nonneg_right hLamC hC
      have hFmul := mul_le_mul_of_nonneg_right hLamF hF
      dsimp [u]
      nlinarith
    have hnDiv :
        n = (12 + 4 * (r + q) + r * q) / W - 2 +
          (2 + r) * C / W + (2 + q) * F / W := by
      field_simp [ne_of_gt hW]
      nlinarith [hNrow]
    dsimp [A0, B0] at hXraw hYraw
    have htail :
        2 * W / (4 + r) + 2 * W / (4 + q) ≤
          (1 + (2 + r) / W) * C +
            (1 + (2 + q) / W) * F + X + Y := by
      nlinarith [hXraw, hYraw, hDXY, hcost]
    have hbase' :
        11 ≤
          (W + (r + q) - 2 +
            (12 + 4 * (r + q) + r * q) / W) +
          (2 * W / (4 + r) + 2 * W / (4 + q)) := by
      nlinarith [hbase]
    calc
      11 ≤
          (W + (r + q) - 2 +
            (12 + 4 * (r + q) + r * q) / W) +
          (2 * W / (4 + r) + 2 * W / (4 + q)) := hbase'
      _ ≤
          (W + (r + q) - 2 +
            (12 + 4 * (r + q) + r * q) / W) +
          ((1 + (2 + r) / W) * C +
            (1 + (2 + q) / W) * F + X + Y) := by
        nlinarith [htail]
      _ = W + r + q + C + F + n + X + Y := by
        rw [hnDiv]
        ring
  · have hlarge : 25 / 4 < W := lt_of_not_ge hsmall
    by_contra hnot
    have htotal : W + r + q + C + F + n + X + Y < 11 :=
      lt_of_not_ge hnot
    let d : ℝ := 11 - W
    let V : ℝ := X + Y
    have hV : 0 ≤ V := by dsimp [V]; linarith
    have hd : 0 < d := by dsimp [d]; linarith
    have hbudget : s + u + V < d := by
      dsimp [s, u, V, d]
      linarith
    have hEarSum :
        4 * W ≤ 4 * V + r * X + q * Y + F * X + C * Y +
          2 * u + 2 * C * F := by
      dsimp [V, u]
      nlinarith [hEarX, hEarY]
    have hrs : r * X + q * Y ≤ s * V := by
      have hcross : 0 ≤ r * Y + q * X := by positivity
      dsimp [s, V]
      nlinarith
    have hCFV : F * X + C * Y ≤ u * V := by
      have hcross : 0 ≤ C * X + F * Y := by positivity
      dsimp [u, V]
      nlinarith
    have hCF : 4 * C * F ≤ u ^ 2 := by
      dsimp [u]
      nlinarith [sq_nonneg (C - F)]
    have hmaster0 :
        4 * W ≤ V * (4 + s + u) + 2 * u + u ^ 2 / 2 := by
      nlinarith [hEarSum, hrs, hCFV, hCF]
    have hsCap : s ≤ d - u - V := by linarith [hbudget]
    have hsScaled := mul_le_mul_of_nonneg_right hsCap hV
    have huCap : u ≤ d - V := by linarith [hbudget]
    have hfactor : 0 ≤ (d - V - u) * (4 + d - V + u) := by
      exact mul_nonneg (by linarith) (by linarith)
    have hmaster :
        4 * W ≤ 2 * d + d ^ 2 / 2 + 2 * V - V ^ 2 / 2 := by
      nlinarith [hmaster0, hsScaled, hfactor]
    by_cases hd2 : 2 ≤ d
    · have hW9 : W ≤ 9 := by dsimp [d] at hd2; linarith
      have hVmax : 2 * V - V ^ 2 / 2 ≤ 2 := by
        nlinarith [sq_nonneg (V - 2)]
      have hquadProd :
          (W - 25 / 4) * (W + 25 / 4 - 34) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have hquad : (W ^ 2 - 34 * W + 169) / 2 ≤ -71 / 32 := by
        nlinarith [hquadProd]
      dsimp [d] at hmaster
      nlinarith
    · have hd2' : d ≤ 2 := le_of_not_ge hd2
      have hVd : V ≤ d := by linarith [hbudget]
      have hfactor2 : 0 ≤ (d - V) * (4 - d - V) := by
        exact mul_nonneg (sub_nonneg.mpr hVd) (by linarith)
      have hVmax :
          2 * V - V ^ 2 / 2 ≤ 2 * d - d ^ 2 / 2 := by
        nlinarith [hfactor2]
      have hW9 : 9 ≤ W := by dsimp [d] at hd2'; linarith
      dsimp [d] at hmaster
      nlinarith

end Heilbronn8.TriHull
