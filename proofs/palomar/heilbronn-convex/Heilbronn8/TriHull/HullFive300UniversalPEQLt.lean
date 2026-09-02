import Heilbronn8.TriHull.HullFive300UniversalME

set_option maxHeartbeats 0

/-!
# The `Q < Delta` branch of the positive-endpoint orbit

This file is a standalone scalar closure.  It uses the central Pluecker row,
the common hard-side estimate, and the seven-atom budget.  The sign of `DQR`
is irrelevant in this branch.
-/

namespace Heilbronn8.TriHull

/-- The `Q < Delta` branch is incompatible with the hard-side inequalities
and a seven-atom total below `21`.  The auxiliary variable `R` denotes the
quantity called `beta + V` in the geometric reduction. -/
lemma hullFive300_pe_q_lt_delta_impossible
    {a b c d e f g Delta Q R : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hDelta : 2 ≤ Delta)
    (hT : a + b + c + d + e + f + g < 21)
    (hcentral : (a + b + c) * Delta = a * d + b * Q)
    (hQlt : Q < Delta)
    (hP : 60 < 13 * b * e - 8 * b - 30 * e)
    (hcommon : 2 * b ≤ (Delta - 2) * R)
    (hRupper : R < 19 - a - g) :
    False := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have he0 : 0 < e := by linarith
  have hDelta0 : 0 < Delta := by linarith
  have hDeltaNonneg : 0 ≤ Delta := hDelta0.le

  have hcentral' :
      a * (d - Delta) = b * (Delta - Q) + c * Delta := by
    nlinarith [hcentral]
  have hbGap : 0 < b * (Delta - Q) :=
    mul_pos hb0 (sub_pos.mpr hQlt)
  have hcDelta : 2 * Delta ≤ c * Delta := by
    have hprod : 0 ≤ (c - 2) * Delta :=
      mul_nonneg (sub_nonneg.mpr hc) hDeltaNonneg
    nlinarith
  have hEarClear : 2 * Delta < a * (d - Delta) := by
    rw [hcentral']
    nlinarith

  have hR17 : R < 17 - a := by linarith
  have hProductPos : 0 < (Delta - 2) * R := by
    have htwob : 0 < 2 * b := by positivity
    exact lt_of_lt_of_le htwob hcommon
  have hDeltaNe : Delta ≠ 2 := by
    intro hEq
    subst Delta
    norm_num at hProductPos
  have hDelta2 : 2 < Delta :=
    lt_of_le_of_ne hDelta (Ne.symm hDeltaNe)
  have hHard17 : 2 * b < (Delta - 2) * (17 - a) := by
    have hmul : (Delta - 2) * R < (Delta - 2) * (17 - a) :=
      mul_lt_mul_of_pos_left hR17 (by linarith)
    exact lt_of_le_of_lt hcommon hmul
  have h17a15 : 17 - a ≤ 15 := by linarith
  have hmul15 :
      (Delta - 2) * (17 - a) ≤ (Delta - 2) * 15 := by
    exact mul_le_mul_of_nonneg_left h17a15 (by linarith)
  have hHard15 : 2 * b < 15 * (Delta - 2) := by
    nlinarith [lt_of_lt_of_le hHard17 hmul15]
  have hDeltaLower : 2 + 2 * (b / 15) < Delta := by
    nlinarith [hHard15]

  have hEarDiv : 2 * Delta / a < d - Delta := by
    apply (div_lt_iff₀ ha0).2
    nlinarith [hEarClear]
  have hdDelta : Delta * (1 + 2 / a) < d := by
    have hid : Delta * (1 + 2 / a) = Delta + 2 * Delta / a := by
      field_simp [ne_of_gt ha0]
      <;> ring
    rw [hid]
    linarith

  let u : ℝ := b / 15
  let q : ℝ := 1 + u / 2 - u ^ 2 / 8
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hSum : a + b + d + e < 15 := by linarith
  have hb9 : b < 9 := by linarith
  have hu3 : u < 3 / 5 := by
    dsimp [u]
    norm_num
    linarith
  have h8u : 0 ≤ 8 - u := by linarith
  have hqSquareIdentity :
      (1 + u) - q ^ 2 = u ^ 3 * (8 - u) / 64 := by
    dsimp [q]
    ring
  have huCube : 0 ≤ u ^ 3 := by positivity
  have hqSquare : q ^ 2 ≤ 1 + u := by
    have hprod : 0 ≤ u ^ 3 * (8 - u) :=
      mul_nonneg huCube h8u
    nlinarith [hqSquareIdentity]
  have hFactor : 0 < 1 + 2 / a := by positivity
  have hDeltaU : 2 * (1 + u) < Delta := by
    dsimp [u]
    linarith [hDeltaLower]
  have hdU : 2 * (1 + u) * (1 + 2 / a) < d := by
    have hmul :
        2 * (1 + u) * (1 + 2 / a) <
          Delta * (1 + 2 / a) :=
      mul_lt_mul_of_pos_right hDeltaU hFactor
    exact lt_trans hmul hdDelta
  have hdUExpanded : 2 * (1 + u) + 4 * (1 + u) / a < d := by
    have hid :
        2 * (1 + u) * (1 + 2 / a) =
          2 * (1 + u) + 4 * (1 + u) / a := by
      field_simp [ne_of_gt ha0]
      <;> ring
    rw [← hid]
    exact hdU

  have hAMIdentity :
      a + 4 * (1 + u) / a - 4 * q =
        ((a - 2 * q) ^ 2 + 4 * ((1 + u) - q ^ 2)) / a := by
    field_simp [ne_of_gt ha0]
    <;> ring
  have hAM : 4 * q ≤ a + 4 * (1 + u) / a := by
    have hnum :
        0 ≤ (a - 2 * q) ^ 2 + 4 * ((1 + u) - q ^ 2) := by
      have hfour : 0 ≤ 4 * ((1 + u) - q ^ 2) := by positivity
      exact add_nonneg (sq_nonneg (a - 2 * q)) hfour
    have hquot :
        0 ≤ ((a - 2 * q) ^ 2 + 4 * ((1 + u) - q ^ 2)) / a :=
      div_nonneg hnum ha0.le
    rw [← hAMIdentity] at hquot
    linarith
  have hNecessary : b + e + 2 * (1 + u) + 4 * q < 15 := by
    have hwithD :
        a + b + e + 2 * (1 + u) + 4 * (1 + u) / a < 15 := by
      linarith [hSum, hdUExpanded]
    linarith [hAM]
  have heUpper : e + 19 * b / 15 - b ^ 2 / 450 < 9 := by
    dsimp [u, q] at hNecessary
    nlinarith [hNecessary]

  have hPclear : 8 * b + 60 < e * (13 * b - 30) := by
    nlinarith [hP]
  have hDenPos : 0 < 13 * b - 30 := by
    by_contra hnot
    have hnonpos : 13 * b - 30 ≤ 0 := le_of_not_gt hnot
    have hmul : e * (13 * b - 30) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos he0.le hnonpos
    nlinarith [hPclear]
  have heLower : (8 * b + 60) / (13 * b - 30) < e := by
    exact (div_lt_iff₀ hDenPos).2 hPclear

  let N : ℝ :=
    -13 * b ^ 3 + 7440 * b ^ 2 - 66150 * b + 148500
  have hNpos : 0 < N := by
    by_cases hb5 : b ≤ 5
    · let K : ℝ := 7375 * b ^ 2 - 66150 * b + 148500
      have hNK : K ≤ N := by
        have hprod : 0 ≤ 13 * b ^ 2 * (5 - b) := by positivity
        dsimp [N, K]
        nlinarith
      have hKSos :
          4 * 7375 * K = (14750 * b - 66150) ^ 2 + 4927500 := by
        dsimp [K]
        ring
      have hKpos : 0 < K := by
        nlinarith [sq_nonneg (14750 * b - 66150), hKSos]
      linarith
    · have hb5' : 5 < b := lt_of_not_ge hb5
      let t : ℝ := b - 5
      have ht0 : 0 < t := by dsimp [t]; linarith
      have ht4 : t < 4 := by dsimp [t]; linarith
      have hNshift :
          N = -13 * t ^ 3 + 7245 * t ^ 2 + 7275 * t + 2125 := by
        dsimp [N, t]
        ring
      have hdrop :
          7193 * t ^ 2 + 7275 * t + 2125 < N := by
        have hprod : 0 < 13 * t ^ 2 * (4 - t) := by positivity
        rw [hNshift]
        nlinarith
      have hbase : 0 < 7193 * t ^ 2 + 7275 * t + 2125 := by positivity
      linarith

  let qUpper : ℝ := 9 - 19 * b / 15 + b ^ 2 / 450
  have hDifference :
      (8 * b + 60) / (13 * b - 30) - qUpper =
        N / (450 * (13 * b - 30)) := by
    have hDenNe : 13 * b - 30 ≠ 0 := ne_of_gt hDenPos
    have hrewrite :
        (8 * b + 60) / (13 * b - 30) - qUpper =
          ((8 * b + 60) - qUpper * (13 * b - 30)) /
            (13 * b - 30) := by
      apply (eq_div_iff hDenNe).2
      rw [sub_mul, div_mul_cancel₀ _ hDenNe]
    rw [hrewrite]
    rw [show (8 * b + 60) - qUpper * (13 * b - 30) = N / 450 by
      dsimp [qUpper, N]
      ring]
    rw [div_div]
  have hBigDen : 0 < 450 * (13 * b - 30) := by positivity
  have hDifferencePos :
      0 < (8 * b + 60) / (13 * b - 30) - qUpper := by
    rw [hDifference]
    exact div_pos hNpos hBigDen
  have heBelowQ : e < qUpper := by
    dsimp [qUpper]
    linarith [heUpper]
  linarith [heLower, hDifferencePos, heBelowQ]

end Heilbronn8.TriHull
