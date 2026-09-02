import Mathlib

/-!
# Compact scalar endpoints for hull-five `1 + 1 + 1`

These two lemmas are the purely scalar end of the two reanchored geometry
packets.  Their hypotheses are the seven hull-area floors, the two pentagon
sum identities, the two ear estimates, and the appropriate central
determinant certificate.  No retained key or computational certificate is
used here.
-/

namespace Heilbronn8.TriHull

set_option maxHeartbeats 1000000

/-- The scalar endpoint for the reanchored `UZ` packet. -/
theorem hullFive111_uz_hull_sum_gt
    {T U V E W Z F : ℝ}
    (hT : 3 ≤ T)
    (hU : 3 ≤ U)
    (hV : 3 ≤ V)
    (hE : 3 ≤ E)
    (hW : 3 ≤ W)
    (hZ : 3 ≤ Z)
    (hF : 3 ≤ F)
    (right_sum : U + V = T + E)
    (left_sum : W + Z = T + F)
    (rightEar : T + 2 ≤ (U - 2) * (E - 1))
    (leftEar : T + 2 ≤ (Z - 2) * (F - 1))
    (central :
      V * W + W * (T + U) + T * V + Z * (T + U) ≤
        T * V * W) :
    (25 : ℝ) / 2 < T + E + F := by
  by_contra hn
  have hsmall : T + E + F ≤ (25 : ℝ) / 2 :=
    le_of_not_gt hn

  let K : ℝ := T + 2
  let x : ℝ := E - 1
  let y : ℝ := F - 1
  let p : ℝ := U - 2
  let q : ℝ := Z - 2
  let r : ℝ := x + y
  let d : ℝ := (25 : ℝ) / 2 - K

  have hK : 5 ≤ K := by
    dsimp [K]
    linarith only [hT]
  have hKpos : 0 < K := by linarith only [hK]
  have hx : 2 ≤ x := by
    dsimp [x]
    linarith only [hE]
  have hy : 2 ≤ y := by
    dsimp [y]
    linarith only [hF]
  have hxpos : 0 < x := by linarith only [hx]
  have hypos : 0 < y := by linarith only [hy]
  have hp : 1 ≤ p := by
    dsimp [p]
    linarith only [hU]
  have hq : 1 ≤ q := by
    dsimp [q]
    linarith only [hZ]
  have hpq_nonneg : 0 ≤ p + q := by linarith only [hp, hq]
  have hr : 4 ≤ r := by
    dsimp [r]
    linarith only [hx, hy]
  have hrpos : 0 < r := by linarith only [hr]
  have hrd : r ≤ d := by
    dsimp [r, d, x, y, K]
    linarith only [hsmall]
  have hdpos : 0 < d := lt_of_lt_of_le hrpos hrd

  have rightEar' : K ≤ p * x := by
    simpa [K, p, x] using rightEar
  have leftEar' : K ≤ q * y := by
    simpa [K, q, y] using leftEar

  have rightEar_y : K * y ≤ (p * x) * y :=
    mul_le_mul_of_nonneg_right rightEar' hypos.le
  have leftEar_x : K * x ≤ (q * y) * x :=
    mul_le_mul_of_nonneg_right leftEar' hxpos.le

  have hKr : K * r ≤ x * y * (p + q) := by
    dsimp [r]
    nlinarith only [rightEar_y, leftEar_x]

  have hxy : 4 * x * y ≤ r ^ 2 := by
    dsimp [r]
    nlinarith only [sq_nonneg (x - y)]

  have hxy_scaled :
      (4 * x * y) * (p + q) ≤ r ^ 2 * (p + q) :=
    mul_le_mul_of_nonneg_right hxy hpq_nonneg

  have hcancel_scaled :
      r * (4 * K) ≤ r * (r * (p + q)) := by
    nlinarith only [hKr, hxy_scaled]

  have hfourK : 4 * K ≤ r * (p + q) :=
    le_of_mul_le_mul_left hcancel_scaled hrpos

  have hrd_scaled : r * (p + q) ≤ d * (p + q) :=
    mul_le_mul_of_nonneg_right hrd hpq_nonneg
  have hfourKd : 4 * K ≤ d * (p + q) :=
    hfourK.trans hrd_scaled

  have hgap : (K - (5 : ℝ) / 2) * d < 4 * K := by
    dsimp [d]
    nlinarith only [sq_nonneg (K - (11 : ℝ) / 2)]

  have hgap_scaled :
      (K - (5 : ℝ) / 2) * d < (p + q) * d := by
    nlinarith only [hgap, hfourKd]

  have hpq_lower : K - (5 : ℝ) / 2 < p + q := by
    by_contra hnot
    have hpq_upper : p + q ≤ K - (5 : ℝ) / 2 :=
      le_of_not_gt hnot
    have hmul :=
      mul_le_mul_of_nonneg_right hpq_upper hdpos.le
    nlinarith only [hgap_scaled, hmul]

  have sum_identity :
      V + W = 2 * K + r - 6 - (p + q) := by
    dsimp [K, r, x, y, p, q]
    linarith only [right_sum, left_sum]

  have hr_upper : r ≤ (25 : ℝ) / 2 - K := by
    simpa [d] using hrd

  have hVW_sum : V + W ≤ 9 := by
    rw [sum_identity]
    nlinarith only [hpq_lower, hr_upper]

  let A : ℝ := T - 1
  have hApos : 0 < A := by
    dsimp [A]
    linarith only [hT]

  have central_group :
      W * (T + U) + Z * (T + U) =
        (T + F) * (T + U) := by
    calc
      W * (T + U) + Z * (T + U) =
          (W + Z) * (T + U) := by ring
      _ = (T + F) * (T + U) := by rw [left_sum]

  have central_rearranged :
      (T + F) * (T + U) ≤ A * V * W - T * V := by
    dsimp [A]
    nlinarith only [central, central_group]

  have hTU_nonneg : 0 ≤ T + U := by linarith only [hT, hU]
  have hT3_nonneg : 0 ≤ T + 3 := by linarith only [hT]
  have hFpart : 0 ≤ (F - 3) * (T + U) :=
    mul_nonneg (sub_nonneg.mpr hF) hTU_nonneg
  have hUpart : 0 ≤ (T + 3) * (U - 3) :=
    mul_nonneg hT3_nonneg (sub_nonneg.mpr hU)

  have hcentral_floor :
      (T + 3) ^ 2 ≤ (T + F) * (T + U) := by
    nlinarith only [hFpart, hUpart]

  have hG :
      (T + 3) ^ 2 ≤ A * V * W - T * V :=
    hcentral_floor.trans central_rearranged

  have hW_upper : W ≤ 9 - V := by
    linarith only [hVW_sum]
  have hAV_nonneg : 0 ≤ A * V :=
    mul_nonneg hApos.le (by linarith only [hV])
  have hW_scaled :
      (A * V) * W ≤ (A * V) * (9 - V) :=
    mul_le_mul_of_nonneg_left hW_upper hAV_nonneg

  have hG_upper :
      A * V * W - T * V ≤
        A * V * (9 - V) - T * V := by
    nlinarith only [hW_scaled]

  have hQ :
      (T + 3) ^ 2 ≤
        A * V * (9 - V) - T * V :=
    hG.trans hG_upper

  have hfourA : 0 ≤ 4 * A :=
    mul_nonneg (by norm_num) hApos.le
  have hQ_scaled :
      4 * A * (T + 3) ^ 2 ≤
        4 * A * (A * V * (9 - V) - T * V) :=
    mul_le_mul_of_nonneg_left hQ hfourA

  have hcomplete_square :
      4 * A * (A * V * (9 - V) - T * V) ≤
        (9 * A - T) ^ 2 := by
    nlinarith only [sq_nonneg (2 * A * V - (9 * A - T))]

  have himpossible :
      4 * A * (T + 3) ^ 2 ≤ (9 * A - T) ^ 2 :=
    hQ_scaled.trans hcomplete_square

  have hcubic_nonneg :
      0 ≤ (3 * T - 13) ^ 2 * (3 * T - 7) :=
    mul_nonneg (sq_nonneg (3 * T - 13)) (by linarith only [hT])

  have hstrict :
      (9 * A - T) ^ 2 < 4 * A * (T + 3) ^ 2 := by
    dsimp [A]
    nlinarith only [hcubic_nonneg]

  exact (not_lt_of_ge himpossible) hstrict

/-- The scalar endpoint for the reanchored `VZ` packet. -/
theorem hullFive111_vz_hull_sum_gt
    {T U V E W Z F : ℝ}
    (hT : 3 ≤ T)
    (hU : 3 ≤ U)
    (hV : 3 ≤ V)
    (hE : 3 ≤ E)
    (hW : 3 ≤ W)
    (hZ : 3 ≤ Z)
    (hF : 3 ≤ F)
    (right_sum : U + V = T + E)
    (left_sum : W + Z = T + F)
    (rightEar : T + 2 ≤ (V - 2) * (E - 1))
    (leftEar : T + 2 ≤ (Z - 2) * (F - 1))
    (central :
      W * (T + V) + U * (2 * T + F) ≤ T * U * W) :
    (25 : ℝ) / 2 < T + E + F := by
  by_contra hn
  have hsmall : T + E + F ≤ (25 : ℝ) / 2 :=
    le_of_not_gt hn

  let K : ℝ := T + 2
  let x : ℝ := E - 1
  let y : ℝ := F - 1
  let D : ℝ → ℝ := fun r => r ^ 2 + (K - 3) * r - K
  let g : ℝ → ℝ := fun r => K * (r + 1) / D r
  let ell : ℝ → ℝ := fun r =>
    2 - (K + 6) * (r - 3) / (2 * K)

  have hK : 5 ≤ K := by
    dsimp [K]
    linarith only [hT]
  have hKpos : 0 < K := by linarith only [hK]
  have hKupper : K ≤ (17 : ℝ) / 2 := by
    dsimp [K]
    linarith only [hsmall, hE, hF]
  have hx : 2 ≤ x := by
    dsimp [x]
    linarith only [hE]
  have hy : 2 ≤ y := by
    dsimp [y]
    linarith only [hF]
  have hxpos : 0 < x := by linarith only [hx]
  have hypos : 0 < y := by linarith only [hy]
  have hUpos : 0 < U := by linarith only [hU]
  have hWpos : 0 < W := by linarith only [hW]

  have rightEar' : K ≤ (V - 2) * x := by
    simpa [K, x] using rightEar
  have leftEar' : K ≤ (Z - 2) * y := by
    simpa [K, y] using leftEar
  have right_sum' : U + V = K + x - 1 := by
    dsimp [K, x]
    linarith only [right_sum]
  have left_sum' : W + Z = K + y - 1 := by
    dsimp [K, y]
    linarith only [left_sum]
  have right_sum_x : (U + V) * x = (K + x - 1) * x :=
    congrArg (fun s : ℝ => s * x) right_sum'
  have left_sum_y : (W + Z) * y = (K + y - 1) * y :=
    congrArg (fun s : ℝ => s * y) left_sum'

  have hUx : U * x ≤ D x := by
    dsimp [D]
    nlinarith only [rightEar', right_sum_x]
  have hWy : W * y ≤ D y := by
    dsimp [D]
    nlinarith only [leftEar', left_sum_y]
  have hDxpos : 0 < D x := by
    have hprod : 0 < U * x := mul_pos hUpos hxpos
    exact lt_of_lt_of_le hprod hUx
  have hDypos : 0 < D y := by
    have hprod : 0 < W * y := mul_pos hWpos hypos
    exact lt_of_lt_of_le hprod hWy

  have hKx : K * (x + 1) ≤ (T + V) * x := by
    dsimp [K] at rightEar' ⊢
    nlinarith only [rightEar']
  have hKy : K * (y + 1) ≤ (T + Z) * y := by
    dsimp [K] at leftEar' ⊢
    nlinarith only [leftEar']
  have hTVnonneg : 0 ≤ T + V := by linarith only [hT, hV]
  have hTZnonneg : 0 ≤ T + Z := by linarith only [hT, hZ]

  have hcross_x :
      K * (x + 1) * U ≤ (T + V) * D x := by
    calc
      K * (x + 1) * U ≤ ((T + V) * x) * U :=
        mul_le_mul_of_nonneg_right hKx hUpos.le
      _ = (T + V) * (U * x) := by ring
      _ ≤ (T + V) * D x :=
        mul_le_mul_of_nonneg_left hUx hTVnonneg
  have hcross_y :
      K * (y + 1) * W ≤ (T + Z) * D y := by
    calc
      K * (y + 1) * W ≤ ((T + Z) * y) * W :=
        mul_le_mul_of_nonneg_right hKy hWpos.le
      _ = (T + Z) * (W * y) := by ring
      _ ≤ (T + Z) * D y :=
        mul_le_mul_of_nonneg_left hWy hTZnonneg

  have hgx : g x ≤ (T + V) / U := by
    dsimp only [g]
    exact (div_le_div_iff₀ hDxpos hUpos).2 hcross_x
  have hgy : g y ≤ (T + Z) / W := by
    dsimp only [g]
    exact (div_le_div_iff₀ hDypos hWpos).2 hcross_y

  have htwo : 2 * T + F = W + (T + Z) := by
    linarith only [left_sum]
  have central' :
      W * (T + V) + U * (T + Z) ≤ (K - 3) * U * W := by
    rw [htwo] at central
    dsimp [K]
    nlinarith only [central]
  have hratio_mul :
      ((T + V) / U + (T + Z) / W) * (U * W) =
        W * (T + V) + U * (T + Z) := by
    field_simp [ne_of_gt hUpos, ne_of_gt hWpos]
    <;> ring
  have hcentral_scaled :
      ((T + V) / U + (T + Z) / W) * (U * W) ≤
        (K - 3) * (U * W) := by
    rw [hratio_mul]
    simpa [mul_assoc] using central'
  have hcentral_ratio :
      (T + V) / U + (T + Z) / W ≤ K - 3 := by
    exact le_of_mul_le_mul_right hcentral_scaled (mul_pos hUpos hWpos)
  have hgsum : g x + g y ≤ K - 3 := by
    linarith only [hgx, hgy, hcentral_ratio]

  have tangent :
      ∀ r : ℝ, 2 ≤ r → 0 < D r → ell r ≤ g r := by
    intro r hr hDr
    have hrpos : 0 < r := by linarith only [hr]
    have hcoeff : 0 ≤ K ^ 2 + K * r + 2 * K + 6 * r := by
      positivity
    have hnum :
        0 ≤ (r - 3) ^ 2 * (K ^ 2 + K * r + 2 * K + 6 * r) :=
      mul_nonneg (sq_nonneg (r - 3)) hcoeff
    have hden : 0 < 2 * K * D r := by
      exact mul_pos (mul_pos (by norm_num) hKpos) hDr
    have hid :
        g r - ell r =
          (r - 3) ^ 2 * (K ^ 2 + K * r + 2 * K + 6 * r) /
            (2 * K * D r) := by
      dsimp only [g, ell]
      field_simp [ne_of_gt hKpos, ne_of_gt hDr]
      dsimp [D]
      ring
    have hquot :
        0 ≤
          (r - 3) ^ 2 * (K ^ 2 + K * r + 2 * K + 6 * r) /
            (2 * K * D r) :=
      div_nonneg hnum hden.le
    linarith only [hid, hquot]

  have htx : ell x ≤ g x := tangent x hx hDxpos
  have hty : ell y ≤ g y := tangent y hy hDypos

  have hxy_upper : x + y ≤ (25 : ℝ) / 2 - K := by
    dsimp [x, y, K]
    linarith only [hsmall]
  have hslope_nonneg : 0 ≤ K + 6 := by linarith only [hK]
  have hslope_bound :
      (K + 6) * (x + y - 6) ≤
        (K + 6) * ((25 : ℝ) / 2 - K - 6) := by
    exact mul_le_mul_of_nonneg_left (by linarith only [hxy_upper]) hslope_nonneg
  have hcap_product :
      0 ≤ (K - 5) * ((17 : ℝ) / 2 - K) :=
    mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hKupper)
  have hendpoint_pos : 0 < -2 * K ^ 2 + 27 * K - 78 := by
    nlinarith only [hcap_product]
  have hrhs_pos :
      0 < 2 * K * (7 - K) - (K + 6) * (x + y - 6) := by
    nlinarith only [hslope_bound, hendpoint_pos]
  have hell_mul :
      (ell x + ell y - (K - 3)) * (2 * K) =
        2 * K * (7 - K) - (K + 6) * (x + y - 6) := by
    dsimp only [ell]
    field_simp [ne_of_gt hKpos]
    ring
  have hscaled_pos :
      0 < (ell x + ell y - (K - 3)) * (2 * K) := by
    rw [hell_mul]
    exact hrhs_pos
  have htwoKpos : 0 < 2 * K := mul_pos (by norm_num) hKpos
  have hdiff_pos : 0 < ell x + ell y - (K - 3) := by
    rcases (mul_pos_iff.mp hscaled_pos) with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hneg.2, htwoKpos]
  have hell : K - 3 < ell x + ell y := by
    linarith only [hdiff_pos]

  linarith only [htx, hty, hgsum, hell]

end Heilbronn8.TriHull
