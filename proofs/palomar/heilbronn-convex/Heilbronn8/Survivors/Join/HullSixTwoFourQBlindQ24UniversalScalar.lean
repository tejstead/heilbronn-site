import Mathlib

/-!
# A universal scalar closer for the q-blind `q = 24` chamber

The exact `MMRR / LMMM` table leaves a particularly small packet.  Three
consecutive unprimed lower-fan areas, the primed top edge, and the two lower
hull ears force a strict `21 / 2` lower bound.  The final estimate uses the
rational constant `181 / 128`; no algebraic approximation theorem is needed.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- The rational two-variable SOS used after the lower-ear elimination. -/
private lemma hullSixTwoFourQ24_rational_sos
    {D r : ℝ} (hD : 0 < D) :
    (181 / 128 : ℝ) * (1 + r) ≤
      D + (1 + r ^ 2) / D := by
  have hk : 0 ≤ 2 - (181 / 128 : ℝ) ^ 2 := by norm_num
  have hnum :
      0 ≤
        (D - (181 / 128 : ℝ) * (1 + r) / 2) ^ 2 +
          (1 - r) ^ 2 / 2 +
            (2 - (181 / 128 : ℝ) ^ 2) * (1 + r) ^ 2 / 4 := by
    have h0 :
        0 ≤ (2 - (181 / 128 : ℝ) ^ 2) * (1 + r) ^ 2 :=
      mul_nonneg hk (sq_nonneg (1 + r))
    exact add_nonneg
      (add_nonneg (sq_nonneg _)
        (div_nonneg (sq_nonneg _) (by norm_num)))
      (div_nonneg h0 (by norm_num))
  have hid :
      D + (1 + r ^ 2) / D - (181 / 128 : ℝ) * (1 + r) =
        ((D - (181 / 128 : ℝ) * (1 + r) / 2) ^ 2 +
          (1 - r) ^ 2 / 2 +
            (2 - (181 / 128 : ℝ) ^ 2) * (1 + r) ^ 2 / 4) / D := by
    field_simp [hD.ne'] <;> ring
  rw [← sub_nonneg, hid]
  exact div_nonneg hnum hD.le

/-- The one-variable rational endpoint. -/
private lemma hullSixTwoFourQ24_rational_bracket
    {s : ℝ} (hs1 : 1 ≤ s) :
    (17 : ℝ) / 2 ≤
      s ^ 2 + 2 / s ^ 2 +
        (181 / 128 : ℝ) * (s + 2 + 1 / s) := by
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hk0 : 0 ≤ (181 / 128 : ℝ) := by norm_num
  have hcoef : 0 ≤ 2 - (181 / 128 : ℝ) ^ 2 := by norm_num
  have hid :
      s ^ 2 + 2 / s ^ 2 +
          (181 / 128 : ℝ) * (s + 2 + 1 / s) =
        6 * (181 / 128 : ℝ) +
          (s ^ 2 - (181 / 128 : ℝ)) ^ 2 / s ^ 2 +
          (181 / 128 : ℝ) * (s - 1) ^ 2 / s +
          (2 - (181 / 128 : ℝ) ^ 2) / s ^ 2 := by
    field_simp [hs.ne'] <;> ring
  rw [hid]
  have hfirst :
      0 ≤ (s ^ 2 - (181 / 128 : ℝ)) ^ 2 / s ^ 2 :=
    div_nonneg (sq_nonneg _) hs2.le
  have hsecond :
      0 ≤ (181 / 128 : ℝ) * (s - 1) ^ 2 / s :=
    div_nonneg (mul_nonneg hk0 (sq_nonneg _)) hs.le
  have hthird :
      0 ≤ (2 - (181 / 128 : ℝ) ^ 2) / s ^ 2 :=
    div_nonneg hcoef hs2.le
  by_cases hsmall : s ≤ (9 : ℝ) / 8
  · have hmon :
        0 ≤ ((9 : ℝ) / 8 - s) * (s + 5 / 4) :=
      mul_nonneg (sub_nonneg.mpr hsmall) (by positivity)
    have hpoly : s ^ 2 + s / 8 ≤ (45 : ℝ) / 32 := by
      nlinarith
    have hgap :
        s / 8 ≤ (181 / 128 : ℝ) - s ^ 2 := by
      nlinarith
    have hgapSum :
        0 ≤ ((181 / 128 : ℝ) - s ^ 2) + s / 8 := by
      nlinarith
    have hgapProd :
        0 ≤
          (((181 / 128 : ℝ) - s ^ 2) - s / 8) *
            (((181 / 128 : ℝ) - s ^ 2) + s / 8) :=
      mul_nonneg (sub_nonneg.mpr hgap) hgapSum
    have hgapSq :
        (s / 8) ^ 2 ≤
          ((181 / 128 : ℝ) - s ^ 2) ^ 2 := by
      nlinarith
    have hone :
        (1 : ℝ) / 64 ≤
          (s ^ 2 - (181 / 128 : ℝ)) ^ 2 / s ^ 2 := by
      apply (le_div_iff₀ hs2).2
      nlinarith
    norm_num at hone ⊢
    nlinarith
  · have hlarge : (9 : ℝ) / 8 ≤ s := le_of_not_ge hsmall
    have hleft : 0 ≤ 8 * s - 9 := by nlinarith
    have hright : 0 ≤ 9 * s - 8 := by nlinarith
    have hprod : 0 ≤ (8 * s - 9) * (9 * s - 8) :=
      mul_nonneg hleft hright
    have hquad : s ≤ 72 * (s - 1) ^ 2 := by
      nlinarith
    have hfrac : (1 : ℝ) / 72 ≤ (s - 1) ^ 2 / s := by
      apply (le_div_iff₀ hs).2
      nlinarith
    have hfrac0 : 0 ≤ (s - 1) ^ 2 / s :=
      div_nonneg (sq_nonneg _) hs.le
    have hk : (9 : ℝ) / 8 ≤ 181 / 128 := by norm_num
    have hone :
        (1 : ℝ) / 64 ≤
          (181 / 128 : ℝ) * (s - 1) ^ 2 / s := by
      calc
        (1 : ℝ) / 64 = (9 / 8 : ℝ) * (1 / 72) := by norm_num
        _ ≤ (9 / 8 : ℝ) * ((s - 1) ^ 2 / s) :=
          mul_le_mul_of_nonneg_left hfrac (by norm_num)
        _ ≤ (181 / 128 : ℝ) * ((s - 1) ^ 2 / s) :=
          mul_le_mul_of_nonneg_right hk hfrac0
        _ = (181 / 128 : ℝ) * (s - 1) ^ 2 / s := by ring
    norm_num at hone ⊢
    nlinarith

/-- Universal scalar closure for the exact q-blind `q = 24` packet. -/
theorem hullSixTwoFourQBlindQ24Universal_scalar
    {b d e f Ap E0 E1 E2 : ℝ}
    (hb1 : 1 ≤ b) (hd1 : 1 ≤ d)
    (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hAp1 : 1 ≤ Ap)
    (hE01 : 1 ≤ E0) (hE11 : 1 ≤ E1) (hE21 : 1 ≤ E2)
    (hQ : 1 ≤ E2 - e + f)
    (hEar0 : d ≤ (d - e) * E0 + (d - 1) * E1)
    (hEar1 : e ≤ (e - f) * E1 + (e - d) * E2)
    (hApTransition : 1 + b ≤ f * Ap)
    (hE0Transition : 1 + d ≤ b * E0) :
    (21 : ℝ) / 2 < Ap + b + f + E0 + E1 + E2 := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hAp : 0 < Ap := lt_of_lt_of_le zero_lt_one hAp1
  have hE1 : 0 < E1 := lt_of_lt_of_le zero_lt_one hE11
  let P : ℝ := d - 1
  let D : ℝ := E1 - 1
  let E : ℝ := E2 - 1
  have hP0 : 0 ≤ P := by dsimp [P]; linarith
  have hD0 : 0 ≤ D := by dsimp [D]; linarith
  have hE0 : 0 ≤ E := by dsimp [E]; linarith
  have hPDbase : 1 + (e - d) * E0 ≤ P * D := by
    dsimp [P, D]
    nlinarith [hEar0]
  have hPD : 1 ≤ P * D := by
    by_cases hde : d ≤ e
    · have hcoef : 0 ≤ e - d := sub_nonneg.mpr hde
      have hmul : e - d ≤ (e - d) * E0 := by
        simpa using mul_le_mul_of_nonneg_left hE01 hcoef
      nlinarith
    · have hed : e < d := lt_of_not_ge hde
      have hneg : (e - d) * E2 ≤ e - d := by
        simpa using mul_le_mul_of_nonpos_left hE21
          (sub_nonpos.mpr (le_of_lt hed))
      have hdBound : d ≤ (e - f) * E1 := by
        nlinarith [hEar1, hneg]
      have hef : 0 < e - f := by
        by_contra hnot
        have hnonpos : e - f ≤ 0 := le_of_not_gt hnot
        have hmul : (e - f) * E1 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hnonpos hE1.le
        nlinarith
      have hgap : e - f < P := by
        dsimp [P]
        linarith
      have hstrict : (e - f) * E1 < P * E1 :=
        mul_lt_mul_of_pos_right hgap hE1
      have hshape : P * E1 = P * D + P := by
        dsimp [D]
        ring
      rw [hshape] at hstrict
      dsimp [P] at hstrict
      nlinarith
  have hP : 0 < P := by
    by_contra hnot
    have hnonpos : P ≤ 0 := le_of_not_gt hnot
    have hmul : P * D ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hD0
    nlinarith
  have hD : 0 < D := by
    by_contra hnot
    have hnonpos : D ≤ 0 := le_of_not_gt hnot
    have hmul : P * D ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hP0 hnonpos
    nlinarith
  have hGap : e - d ≤ P * D - 1 := by
    by_cases hde : d ≤ e
    · have hcoef : 0 ≤ e - d := sub_nonneg.mpr hde
      have hmul : e - d ≤ (e - d) * E0 := by
        simpa using mul_le_mul_of_nonneg_left hE01 hcoef
      nlinarith
    · have hed : e < d := lt_of_not_ge hde
      nlinarith
  have hEF : e - f ≤ E := by
    dsimp [E]
    linarith [hQ]
  have hEarRearranged :
      d ≤ (e - f) * (D + 1) + (e - d) * E := by
    dsimp [D, E]
    nlinarith [hEar1]
  have hfirst : (e - f) * (D + 1) ≤ E * (D + 1) :=
    mul_le_mul_of_nonneg_right hEF (by linarith [hD0])
  have hsecond : (e - d) * E ≤ (P * D - 1) * E :=
    mul_le_mul_of_nonneg_right hGap hE0
  have hfactor :
      E * (D + 1) + (P * D - 1) * E = d * (D * E) := by
    dsimp [P]
    ring
  have hdDE : d ≤ d * (D * E) := by
    rw [← hfactor]
    exact hEarRearranged.trans (add_le_add hfirst hsecond)
  have hDE : 1 ≤ D * E := by
    by_contra hnot
    have hlt : D * E < 1 := lt_of_not_ge hnot
    have hmul : d * (D * E) < d * 1 :=
      mul_lt_mul_of_pos_left hlt hd
    nlinarith
  have hInvP : 1 / D ≤ P := by
    exact (div_le_iff₀ hD).2 (by simpa [mul_comm] using hPD)
  have hInvE : 1 / D ≤ E := by
    exact (div_le_iff₀ hD).2 (by simpa [mul_comm] using hDE)
  have hE0Lower : (1 + d) / b ≤ E0 := by
    exact (div_le_iff₀ hb).2
      (by simpa [mul_comm] using hE0Transition)
  have hNumer : 2 + 1 / D ≤ 1 + d := by
    dsimp [P] at hInvP
    linarith
  have hE0Fine : 2 / b + 1 / (b * D) ≤ E0 := by
    calc
      2 / b + 1 / (b * D) = (2 + 1 / D) / b := by
        field_simp [hb.ne', hD.ne'] <;> ring
      _ ≤ (1 + d) / b :=
        (div_le_div_iff_of_pos_right hb).2 hNumer
      _ ≤ E0 := hE0Lower
  have hEdges :
      2 + D + (1 + 1 / b) / D + 2 / b ≤ E0 + E1 + E2 := by
    have hshape :
        2 + D + (1 + 1 / b) / D + 2 / b =
          (2 / b + 1 / (b * D)) + (D + 1) + (1 / D + 1) := by
      field_simp [hb.ne', hD.ne'] <;> ring
    rw [hshape]
    have hE1shape : E1 = D + 1 := by dsimp [D]; ring
    have hE2shape : E2 = E + 1 := by dsimp [E]; ring
    rw [hE1shape, hE2shape]
    linarith
  let s : ℝ := Real.sqrt b
  let r : ℝ := 1 / s
  let k : ℝ := 181 / 128
  have hk : 0 < k := by
    dsimp [k]
    norm_num
  have hs2 : s ^ 2 = b := by
    dsimp [s]
    exact Real.sq_sqrt hb.le
  have hs1 : 1 ≤ s := by
    dsimp [s]
    simpa using Real.sqrt_le_sqrt hb1
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hr2 : r ^ 2 = 1 / b := by
    dsimp only [r]
    rw [div_pow, one_pow, hs2]
  have hDSOS0 := hullSixTwoFourQ24_rational_sos (D := D) (r := r) hD
  have hDSOS : k * (1 + r) ≤ D + (1 + 1 / b) / D := by
    simpa [k, hr2] using hDSOS0
  have hAMGM : 4 * (Ap * f) ≤ (Ap + f) ^ 2 := by
    nlinarith [sq_nonneg (Ap - f)]
  have hprod : 1 + b ≤ Ap * f := by
    simpa [mul_comm] using hApTransition
  have hsumSq : 4 * (1 + b) ≤ (Ap + f) ^ 2 := by
    nlinarith
  have hsPair : 2 * (s + 1) ^ 2 ≤ 4 * (1 + b) := by
    nlinarith [sq_nonneg (s - 1)]
  have hk2 : k ^ 2 < 2 := by
    dsimp [k]
    norm_num
  have hsplus : 0 < (s + 1) ^ 2 :=
    sq_pos_of_pos (by linarith [hs])
  have hksq0 := mul_lt_mul_of_pos_right hk2 hsplus
  have hksq : (k * (s + 1)) ^ 2 < 2 * (s + 1) ^ 2 := by
    simpa [mul_pow] using hksq0
  have htopSq : (k * (s + 1)) ^ 2 < (Ap + f) ^ 2 :=
    hksq.trans_le (hsPair.trans hsumSq)
  have htop : k * (s + 1) < Ap + f := by
    apply (sq_lt_sq₀
      (mul_nonneg hk.le (by linarith [hs]))
      (add_nonneg hAp.le hf.le)).mp
    exact htopSq
  have hLower1 :
      (Ap + f) + b +
          (2 + D + (1 + 1 / b) / D + 2 / b) ≤
        Ap + b + f + E0 + E1 + E2 := by
    nlinarith
  have hLower2 :
      k * (s + 1) + b + 2 + k * (1 + r) + 2 / b <
        Ap + b + f + E0 + E1 + E2 := by
    nlinarith
  have hshape :
      k * (s + 1) + b + 2 + k * (1 + r) + 2 / b =
        2 + s ^ 2 + 2 / s ^ 2 + k * (s + 2 + 1 / s) := by
    dsimp only [r]
    rw [← hs2]
    field_simp [hs.ne'] <;> ring
  rw [hshape] at hLower2
  have hBracket := hullSixTwoFourQ24_rational_bracket (s := s) hs1
  nlinarith

end Heilbronn8
