import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the `p = 111`, negative-`Y22` frontier

This file is geometry-free.  It uses only two endpoint `Q`-fan floors,
the positive first `X` column, the negative `Y22` floor, four hull-triangle
floors, and three exact determinant identities.  No other `Y` sign and no
geometric symmetry enter the argument.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

private theorem p111_five_term_amgm
    {x0 x1 x2 x3 x4 : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4) :
    5 * (x0 * x1 * x2 * x3 * x4) ^ ((5 : ℝ)⁻¹) ≤
      x0 + x1 + x2 + x3 + x4 := by
  let weight : Fin 5 → ℕ := ![1, 1, 1, 1, 1]
  let term : Fin 5 → ℝ := ![x0, x1, x2, x3, x4]
  have hweight : ∀ i, 0 < weight i := by
    intro i
    fin_cases i <;> norm_num [weight]
  have hterm : ∀ i, 0 ≤ term i := by
    intro i
    fin_cases i <;> simp [term, hx0, hx1, hx2, hx3, hx4]
  have hamgm := scalar_weighted_amgm_nat weight term hweight hterm
  simpa [weight, term, Fin.sum_univ_succ, Fin.prod_univ_succ,
    add_assoc, mul_assoc] using hamgm

private theorem p111_first_amgm
    {u k : ℝ} (hu : 0 < u) (hk : 0 < k) :
    (11 : ℝ) / 2 < u + k + u / k + 3 / u := by
  have hproduct :
      u * k * (u / k) * (3 / (2 * u)) * (3 / (2 * u)) =
        (9 : ℝ) / 4 := by
    field_simp [hu.ne', hk.ne'] <;> ring
  have hamgm := p111_five_term_amgm
    (le_of_lt hu) (le_of_lt hk) (by positivity : 0 ≤ u / k)
    (by positivity : 0 ≤ 3 / (2 * u))
    (by positivity : 0 ≤ 3 / (2 * u))
  rw [hproduct] at hamgm
  have hpow : ((11 : ℝ) / 10) ^ 5 < (9 : ℝ) / 4 := by
    norm_num
  have hpowRpow :
      ((11 : ℝ) / 10) ^ (5 : ℝ) < (9 : ℝ) / 4 := by
    change ((11 : ℝ) / 10) ^ ((5 : ℕ) : ℝ) < (9 : ℝ) / 4
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (11 : ℝ) / 10 < ((9 : ℝ) / 4) ^ ((5 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (by norm_num : (0 : ℝ) ≤ 9 / 4) (by norm_num)]
    exact hpowRpow
  calc
    (11 : ℝ) / 2 = 5 * ((11 : ℝ) / 10) := by norm_num
    _ < 5 * ((9 : ℝ) / 4) ^ ((5 : ℝ)⁻¹) :=
      mul_lt_mul_of_pos_left hroot (by norm_num)
    _ ≤ u + k + u / k + 3 / (2 * u) + 3 / (2 * u) := hamgm
    _ = u + k + u / k + 3 / u := by
      field_simp [hu.ne'] <;> ring

private theorem p111_second_amgm
    {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    (11 : ℝ) / 2 < p + t + 2 / p + 4 / (p * t) := by
  have hproduct :
      (p / 2) * (p / 2) * t * (2 / p) * (4 / (p * t)) =
        (2 : ℝ) := by
    field_simp [hp.ne', ht.ne'] <;> ring
  have hamgm := p111_five_term_amgm
    (by positivity : 0 ≤ p / 2) (by positivity : 0 ≤ p / 2)
    (le_of_lt ht) (by positivity : 0 ≤ 2 / p)
    (by positivity : 0 ≤ 4 / (p * t))
  rw [hproduct] at hamgm
  have hpow : ((11 : ℝ) / 10) ^ 5 < (2 : ℝ) := by
    norm_num
  have hpowRpow : ((11 : ℝ) / 10) ^ (5 : ℝ) < (2 : ℝ) := by
    change ((11 : ℝ) / 10) ^ ((5 : ℕ) : ℝ) < (2 : ℝ)
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (11 : ℝ) / 10 < (2 : ℝ) ^ ((5 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)]
    exact hpowRpow
  nlinarith

private theorem p111_six_reciprocal
    {u : ℝ} (hu : 0 < u) :
    (9 : ℝ) / 2 < u + 6 / u := by
  have hpoly : 0 < u ^ 2 - (9 : ℝ) / 2 * u + 6 := by
    nlinarith [sq_nonneg (u - (9 : ℝ) / 4)]
  have hid :
      u + 6 / u - (9 : ℝ) / 2 =
        (u ^ 2 - (9 : ℝ) / 2 * u + 6) / u := by
    field_simp [hu.ne'] <;> ring
  have hdiff : 0 < u + 6 / u - (9 : ℝ) / 2 := by
    rw [hid]
    exact div_pos hpoly hu
  exact sub_pos.mp hdiff

private theorem p111_large_tau
    {p t : ℝ} (hp1 : 1 ≤ p) (ht2 : 2 ≤ t) :
    7 ≤ t + 4 / (t + 2) + p + (t + 6) / (t * p) := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) ht2
  have htp : 0 < t * p := mul_pos ht hp
  have ht2p : 0 < t + 2 := by linarith
  let K : ℝ := 7 - t - 4 / (t + 2)
  let c : ℝ := (t + 6) / t
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcp : c / p = (t + 6) / (t * p) := by
    dsimp [c]
    field_simp [hp.ne', ht.ne'] <;> ring
  by_cases hK : K ≤ 0
  · have hpair : 0 ≤ p + c / p := by positivity
    dsimp [K] at hK
    rw [← hcp]
    linarith
  · have hKpos : 0 < K := lt_of_not_ge hK
    have ht7 : t < 7 := by
      have hfrac : 0 < 4 / (t + 2) := by positivity
      dsimp [K] at hKpos
      linarith
    have hC : t ^ 3 - 6 * t ^ 2 - 27 * t - 24 < 0 := by
      by_cases ht6 : t ≤ 6
      · have hlead : t ^ 2 * (t - 6) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t)
            (sub_nonpos.mpr ht6)
        nlinarith
      · have h6t : 6 < t := lt_of_not_ge ht6
        have htSq : t ^ 2 < 49 := by
          have hfac : 0 < (7 - t) * (7 + t) :=
            mul_pos (sub_pos.mpr ht7) (by linarith)
          nlinarith
        have hgap : t - 6 < 1 := by linarith
        have hleadLt : t ^ 2 * (t - 6) < 49 := by
          have hsqPos : 0 < t ^ 2 := sq_pos_of_pos ht
          have hsmall : t ^ 2 * (t - 6) < t ^ 2 :=
            by
              simpa only [mul_one] using
                (mul_lt_mul_of_pos_left hgap hsqPos)
          exact hsmall.trans htSq
        nlinarith
    have hid :
        4 * c - K ^ 2 =
          -((t - 2) ^ 2) *
              (t ^ 3 - 6 * t ^ 2 - 27 * t - 24) /
            (t * (t + 2) ^ 2) := by
      dsimp [c, K]
      field_simp [ht.ne', ht2p.ne'] <;> ring
    have hden : 0 < t * (t + 2) ^ 2 := by positivity
    have hnum :
        0 ≤ -((t - 2) ^ 2) *
          (t ^ 3 - 6 * t ^ 2 - 27 * t - 24) := by
      have hmul :=
        mul_nonneg (sq_nonneg (t - 2)) (le_of_lt (neg_pos.mpr hC))
      nlinarith
    have hdisc : 0 ≤ 4 * c - K ^ 2 := by
      rw [hid]
      exact div_nonneg hnum (le_of_lt hden)
    have hquad : 0 ≤ p ^ 2 - K * p + c := by
      nlinarith [sq_nonneg (2 * p - K)]
    have hpair : K ≤ p + c / p := by
      have hpairId :
          p + c / p - K = (p ^ 2 - K * p + c) / p := by
        field_simp [hp.ne'] <;> ring
      have hdiff : 0 ≤ p + c / p - K := by
        rw [hpairId]
        exact div_nonneg hquad (le_of_lt hp)
      exact sub_nonneg.mp hdiff
    dsimp [K] at hpair
    rw [← hcp]
    linarith

/--
Geometry-free closure for the normalized `p = 111`, `Y22 <= -1` branch.

`L02` is the `P,L0,L2` determinant.  The four hull assumptions are the
triangles `015`, `012`, `123`, and `345`, respectively.
-/
theorem hullSixThreeThreeP111Y22Neg_scalar
    {u0 u1 u2 v0 v2 A0 A1 A2 A3 A4 A5
      X00 X10 X12 X22 L02 : ℝ}
    (hu01 : 1 ≤ u0) (hu11 : 1 ≤ u1) (hu21 : 1 ≤ u2)
    (hv01 : 1 ≤ v0) (hv21 : 1 ≤ v2)
    (hA01 : 1 ≤ A0) (hA11 : 1 ≤ A1) (hA21 : 1 ≤ A2)
    (hA31 : 1 ≤ A3) (hA41 : 1 ≤ A4) (hA51 : 1 ≤ A5)
    (hB0 : 1 ≤ A0 + u0 - u1)
    (hB5 : 1 ≤ A5 - u0 - v2)
    (hX00 : 1 ≤ X00) (hX10 : 1 ≤ X10)
    (hY22 : X22 + u2 + v2 ≤ -1)
    (hColumn0 : v0 * A0 = u0 * X10 - u1 * X00)
    (hColumn2 : u2 * (-X12) - u1 * (-X22) = v2 * A1)
    (hL02Identity : u2 * L02 = v2 * A2 + v0 * (-X22))
    (hHull015 : 1 ≤ A0 + A5 + X12)
    (hHull012 : u1 ≤ A0 * (u1 - u2) + A1 * (u1 - u0))
    (hHull123 : 1 ≤ A1 + A2 - X10)
    (hHull345 : 1 ≤ A3 + A4 - L02) :
    (25 : ℝ) / 2 < A0 + A1 + A2 + A3 + A4 + A5 := by
  have hu0 : 0 < u0 := lt_of_lt_of_le zero_lt_one hu01
  have hu1 : 0 < u1 := lt_of_lt_of_le zero_lt_one hu11
  have hu2 : 0 < u2 := lt_of_lt_of_le zero_lt_one hu21
  have hv0 : 0 < v0 := lt_of_lt_of_le zero_lt_one hv01
  have hv2 : 0 < v2 := lt_of_lt_of_le zero_lt_one hv21
  have hA0 : 0 < A0 := lt_of_lt_of_le zero_lt_one hA01
  have hA1 : 0 < A1 := lt_of_lt_of_le zero_lt_one hA11
  have hA2 : 0 < A2 := lt_of_lt_of_le zero_lt_one hA21

  let sigma : ℝ := A1 + A2 - 1
  have hsigma1 : 1 ≤ sigma := by
    dsimp [sigma]
    linarith
  have hsigma : 0 < sigma := lt_of_lt_of_le zero_lt_one hsigma1
  have hMfloor : u2 + 2 ≤ -X22 := by linarith
  have hM : 0 < -X22 := by linarith

  have hNIdentity :
      -X12 = (u1 * (-X22) + v2 * A1) / u2 := by
    apply (eq_div_iff hu2.ne').2
    nlinarith [hColumn2]
  have hWrapLower :
      (u1 * (-X22) + v2 * A1) / u2 + 1 ≤ A0 + A5 := by
    calc
      (u1 * (-X22) + v2 * A1) / u2 + 1 = -X12 + 1 := by
        rw [hNIdentity]
      _ ≤ A0 + A5 := by linarith
  have hL02 :
      L02 = (v2 * A2 + v0 * (-X22)) / u2 := by
    apply (eq_div_iff hu2.ne').2
    nlinarith [hL02Identity]
  have hMiddleLower :
      (v2 * A2 + v0 * (-X22)) / u2 + 1 ≤ A3 + A4 := by
    calc
      (v2 * A2 + v0 * (-X22)) / u2 + 1 = L02 + 1 := by
        rw [hL02]
      _ ≤ A3 + A4 := by linarith
  have hFracJoin :
      (u1 * (-X22) + v2 * A1) / u2 +
          (v2 * A2 + v0 * (-X22)) / u2 =
        ((u1 + v0) * (-X22) + v2 * (A1 + A2)) / u2 := by
    ring
  have hCore :
      2 + (A1 + A2) +
          ((u1 + v0) * (-X22) + v2 * (A1 + A2)) / u2 ≤
        A0 + A1 + A2 + A3 + A4 + A5 := by
    nlinarith [hWrapLower, hMiddleLower, hFracJoin]

  have hLeftProduct :
      (u1 + 1) * (u2 + 2) ≤ (u1 + v0) * (-X22) := by
    exact mul_le_mul (by linarith) hMfloor (by positivity) (by positivity)
  have hSnonneg : 0 ≤ A1 + A2 := by positivity
  have hFanProduct : A1 + A2 ≤ v2 * (A1 + A2) := by
    simpa [one_mul] using
      (mul_le_mul_of_nonneg_right hv21 hSnonneg)
  have hNumerator :
      (u1 + 1) * (u2 + 2) + (A1 + A2) ≤
        (u1 + v0) * (-X22) + v2 * (A1 + A2) := by
    linarith
  have hFraction :
      ((u1 + 1) * (u2 + 2) + (A1 + A2)) / u2 ≤
        ((u1 + v0) * (-X22) + v2 * (A1 + A2)) / u2 :=
    (div_le_div_iff_of_pos_right hu2).2 hNumerator
  have hFIdentity :
      2 + (A1 + A2) +
          ((u1 + 1) * (u2 + 2) + (A1 + A2)) / u2 =
        4 + u1 + sigma + (2 * u1 + sigma + 3) / u2 := by
    dsimp [sigma]
    field_simp [hu2.ne'] <;> ring
  have hF :
      4 + u1 + sigma + (2 * u1 + sigma + 3) / u2 ≤
        A0 + A1 + A2 + A3 + A4 + A5 := by
    rw [← hFIdentity]
    nlinarith [hCore, hFraction]

  have hX10Upper : X10 ≤ sigma := by
    dsimp [sigma]
    linarith
  have hqX10 : u0 * X10 ≤ u0 * sigma :=
    mul_le_mul_of_nonneg_left hX10Upper (le_of_lt hu0)
  have hA0Scale : A0 ≤ v0 * A0 := by
    simpa [one_mul] using
      (mul_le_mul_of_nonneg_right hv01 (le_of_lt hA0))
  have hX00Scale : u1 ≤ u1 * X00 := by
    simpa [mul_one] using
      (mul_le_mul_of_nonneg_left hX00 (le_of_lt hu1))
  have hqSigma : A0 + u1 ≤ u0 * sigma := by
    nlinarith [hColumn0, hqX10, hA0Scale, hX00Scale]
  have hA1Upper : A1 ≤ sigma := by
    dsimp [sigma]
    linarith

  by_cases hq : u1 ≤ u0
  · have hSecondNonpos : A1 * (u1 - u0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA1)
        (sub_nonpos.mpr hq)
    have hEarMain : u1 ≤ A0 * (u1 - u2) := by
      nlinarith [hHull012]
    have hu21 : u2 < u1 := by
      by_contra hnot
      have hgap : u1 - u2 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
      have hnonpos : A0 * (u1 - u2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA0) hgap
      linarith
    have hk : 0 < u1 - u2 := sub_pos.mpr hu21
    have hA0Lower : u1 / (u1 - u2) ≤ A0 := by
      exact (div_le_iff₀ hk).2 (by simpa [mul_comm] using hEarMain)

    have hA5Lower : u0 + 2 ≤ A5 := by linarith
    have hA2Product : 1 ≤ v2 * A2 := by
      simpa [one_mul] using
        (mul_le_mul hv21 hA21 zero_le_one (le_of_lt hv2))
    have hMProduct : u2 + 2 ≤ v0 * (-X22) := by
      simpa [one_mul] using
        (mul_le_mul hv01 hMfloor (by positivity) (le_of_lt hv0))
    have hL02Strong : 1 + 3 / u2 ≤ L02 := by
      have hnum : u2 + 3 ≤ v2 * A2 + v0 * (-X22) := by linarith
      have hdiv := (div_le_div_iff_of_pos_right hu2).2 hnum
      rw [hL02]
      calc
        1 + 3 / u2 = (u2 + 3) / u2 := by
          field_simp [hu2.ne'] <;> ring
        _ ≤ (v2 * A2 + v0 * (-X22)) / u2 := hdiv
    have hA34Lower : 2 + 3 / u2 ≤ A3 + A4 := by
      linarith [hHull345, hL02Strong]
    have hAlternative :
        5 + u0 + A0 + A1 + 3 / u2 ≤
          A0 + A1 + A2 + A3 + A4 + A5 := by
      linarith
    have hFinalLower :
        6 + u1 + u1 / (u1 - u2) + 3 / u2 ≤
          A0 + A1 + A2 + A3 + A4 + A5 := by
      nlinarith [hAlternative, hA0Lower]
    have hamgm := p111_first_amgm hu2 hk
    have hid :
        6 + u1 + u1 / (u1 - u2) + 3 / u2 =
          7 + (u2 + (u1 - u2) + u2 / (u1 - u2) + 3 / u2) := by
      field_simp [hu2.ne', hk.ne'] <;> ring
    rw [hid] at hFinalLower
    nlinarith
  · have hqu : u0 < u1 := lt_of_not_ge hq
    have hdelta : 0 < u1 - u0 := sub_pos.mpr hqu
    have hA0Delta : 1 + (u1 - u0) ≤ A0 := by linarith
    let R : ℝ := u1 * (sigma - 1) - 1
    let D : ℝ := R + sigma + 1
    let T : ℝ := u1 + sigma
    have hdeltaBound : (u1 - u0) * (sigma + 1) ≤ R := by
      dsimp [R]
      nlinarith [hqSigma, hA0Delta]
    have hdeltaProduct : 0 < (u1 - u0) * (sigma + 1) := by
      exact mul_pos hdelta (by linarith)
    have hR : 0 < R := lt_of_lt_of_le hdeltaProduct hdeltaBound
    have hD : 0 < D := by dsimp [D]; linarith
    have hT : 0 < T := by dsimp [T]; positivity

    have close_of_reduction (hReduction : u2 * D ≤ R * T) :
        (25 : ℝ) / 2 < A0 + A1 + A2 + A3 + A4 + A5 := by
      let N : ℝ := 2 * u1 + sigma + 3
      let G : ℝ := 4 + u1 + sigma + N * D / (R * T)
      have hRT : 0 < R * T := mul_pos hR hT
      have hReciprocal : D / (R * T) ≤ 1 / u2 := by
        exact (div_le_div_iff₀ hRT hu2).2
          (by simpa [mul_comm] using hReduction)
      have hN : 0 ≤ N := by dsimp [N]; positivity
      have hNReciprocal : N * (D / (R * T)) ≤ N * (1 / u2) :=
        mul_le_mul_of_nonneg_left hReciprocal hN
      dsimp [N] at hNReciprocal
      have hGleF :
          G ≤ 4 + u1 + sigma + (2 * u1 + sigma + 3) / u2 := by
        dsimp [G, N]
        have hleft :
            (2 * u1 + sigma + 3) * D / (R * T) =
              (2 * u1 + sigma + 3) * (D / (R * T)) := by ring
        have hright :
            (2 * u1 + sigma + 3) / u2 =
              (2 * u1 + sigma + 3) * (1 / u2) := by ring
        rw [hleft, hright]
        simpa [add_comm] using
          add_le_add_left hNReciprocal (4 + u1 + sigma)
      have hGleH : G ≤ A0 + A1 + A2 + A3 + A4 + A5 :=
        hGleF.trans hF

      let tau : ℝ := sigma - 1
      have hTau : 0 < tau := by
        by_contra hnot
        have htNonpos : tau ≤ 0 := le_of_not_gt hnot
        have hprod : u1 * tau ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu1) htNonpos
        dsimp [R, tau] at hR hprod
        nlinarith
      have hUTau : 0 < u1 * tau := mul_pos hu1 hTau
      have hRIdentity : R = u1 * tau - 1 := by
        dsimp [R, tau]
      have hTIdentity : T = u1 + tau + 1 := by
        dsimp [T, tau]
        ring
      let a : ℝ := (u1 + 3) / T
      let b : ℝ := (tau + 2) / R
      let c : ℝ := 1 / u1 + 2 / (u1 * tau)
      have ha : 0 < a := by dsimp [a]; positivity
      have hc : 0 < c := by dsimp [c]; positivity
      have hRlt : R < u1 * tau := by rw [hRIdentity]; linarith
      have hbRaw :
          (tau + 2) / (u1 * tau) < (tau + 2) / R := by
        apply (div_lt_div_iff₀ hUTau hR).2
        exact mul_lt_mul_of_pos_left hRlt (by linarith)
      have hcIdentity : c = (tau + 2) / (u1 * tau) := by
        dsimp [c]
        field_simp [hu1.ne', hTau.ne'] <;> ring
      have hcb : c < b := by
        calc
          c = (tau + 2) / (u1 * tau) := hcIdentity
          _ < (tau + 2) / R := hbRaw
          _ = b := by rfl
      have hGIdentity : G = 5 + T + a + b + a * b := by
        dsimp only [G, N, a, b, D]
        field_simp [hR.ne', hT.ne']
        rw [hRIdentity, hTIdentity]
        dsimp [tau]
        ring
      have hcbScaled : (1 + a) * c < (1 + a) * b :=
        mul_lt_mul_of_pos_left hcb (by linarith)
      have hBaseStrict :
          6 + u1 + tau + a + (1 + a) * c < G := by
        rw [hGIdentity]
        nlinarith [hTIdentity, hcbScaled]

      by_cases ht2 : tau ≤ 2
      · have ha1 : 1 ≤ a := by
          dsimp [a]
          apply (le_div_iff₀ hT).2
          nlinarith [hTIdentity]
        have hTwoC : 2 * c ≤ (1 + a) * c :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hc)
        have hcTwice :
            2 * c = 2 / u1 + 4 / (u1 * tau) := by
          dsimp [c]
          ring
        have hSimpleStrict :
            7 + u1 + tau + 2 / u1 + 4 / (u1 * tau) < G := by
          nlinarith [hBaseStrict, hTwoC, hcTwice]
        have hamgm := p111_second_amgm hu1 hTau
        nlinarith
      · have ht2' : 2 ≤ tau := le_of_lt (lt_of_not_ge ht2)
        have ht2pos : 0 < tau + 2 := by linarith
        have haLower : 4 / (tau + 2) ≤ a := by
          dsimp [a]
          apply (div_le_div_iff₀ ht2pos hT).2
          have hprod : 0 ≤ (tau - 2) * (u1 - 1) :=
            mul_nonneg (sub_nonneg.mpr ht2') (sub_nonneg.mpr hu11)
          nlinarith [hTIdentity]
        have hOnePlus :
            (1 + 4 / (tau + 2)) * c ≤ (1 + a) * c :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hc)
        have hTailIdentity :
            4 / (tau + 2) + (tau + 6) / (tau * u1) =
              4 / (tau + 2) + (1 + 4 / (tau + 2)) * c := by
          rw [hcIdentity]
          field_simp [hu1.ne', hTau.ne', ht2pos.ne'] <;> ring
        have hTailTerms :
            4 / (tau + 2) + (tau + 6) / (tau * u1) ≤
              a + (1 + a) * c := by
          rw [hTailIdentity]
          linarith
        have hLargeStrict :
            6 + tau + 4 / (tau + 2) + u1 +
                (tau + 6) / (tau * u1) < G := by
          nlinarith [hBaseStrict, hTailTerms]
        have hLarge := p111_large_tau hu11 ht2'
        nlinarith

    by_cases hpu : u1 ≤ u2
    · have hAterm :
          A0 * (u1 - u2) ≤
            (1 + (u1 - u0)) * (u1 - u2) :=
        mul_le_mul_of_nonpos_right hA0Delta (sub_nonpos.mpr hpu)
      have hBterm :
          A1 * (u1 - u0) ≤ sigma * (u1 - u0) :=
        mul_le_mul_of_nonneg_right hA1Upper (le_of_lt hdelta)
      have hUdelta :
          u2 ≤ (u1 - u0) * (u1 + sigma - u2) := by
        nlinarith [hHull012, hAterm, hBterm]
      have hfactor : 0 < u1 + sigma - u2 := by
        by_contra hnot
        have hnonpos : u1 + sigma - u2 ≤ 0 := le_of_not_gt hnot
        have hprod : (u1 - u0) * (u1 + sigma - u2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdelta) hnonpos
        linarith
      have hfirst := mul_le_mul_of_nonneg_right hUdelta
        (show 0 ≤ sigma + 1 by linarith)
      have hsecond := mul_le_mul_of_nonneg_right hdeltaBound
        (le_of_lt hfactor)
      apply close_of_reduction
      dsimp [D, T]
      nlinarith [hfirst, hsecond]
    · have hup : u2 < u1 := lt_of_not_ge hpu
      have hk : 0 < u1 - u2 := sub_pos.mpr hup
      by_cases hk1 : 1 ≤ u1 - u2
      · have hNumeratorCoarse :
            2 * u2 + 6 ≤ 2 * u1 + sigma + 3 := by
          nlinarith
        have hDivCoarse :
            2 + 6 / u2 ≤ (2 * u1 + sigma + 3) / u2 := by
          have hdiv := (div_le_div_iff_of_pos_right hu2).2 hNumeratorCoarse
          calc
            2 + 6 / u2 = (2 * u2 + 6) / u2 := by
              field_simp [hu2.ne'] <;> ring
            _ ≤ (2 * u1 + sigma + 3) / u2 := hdiv
        have hCoarse :
            8 + u2 + 6 / u2 ≤
              4 + u1 + sigma + (2 * u1 + sigma + 3) / u2 := by
          linarith
        have hpair := p111_six_reciprocal hu2
        nlinarith [hF]
      · have hklt : u1 - u2 < 1 := lt_of_not_ge hk1
        have hA0Upper : A0 ≤ u0 * sigma - u1 := by
          linarith [hqSigma]
        have hAterm :
            (u1 - u2) * A0 ≤
              (u1 - u2) * (u0 * sigma - u1) :=
          mul_le_mul_of_nonneg_left hA0Upper (le_of_lt hk)
        have hBterm :
            A1 * (u1 - u0) ≤ sigma * (u1 - u0) :=
          mul_le_mul_of_nonneg_right hA1Upper (le_of_lt hdelta)
        have hPbound :
            u1 ≤
              (u1 - u2) * u1 * (sigma - 1) +
                sigma * (u1 - u0) * (1 - (u1 - u2)) := by
          have hid :
              (u1 - u2) * (u0 * sigma - u1) +
                  sigma * (u1 - u0) =
                (u1 - u2) * u1 * (sigma - 1) +
                  sigma * (u1 - u0) * (1 - (u1 - u2)) := by
            ring
          rw [← hid]
          nlinarith [hHull012, hAterm, hBterm]
        have hfirst := mul_le_mul_of_nonneg_right hPbound
          (show 0 ≤ sigma + 1 by linarith)
        have hscale : 0 ≤ sigma * (1 - (u1 - u2)) :=
          mul_nonneg (le_of_lt hsigma) (sub_nonneg.mpr (le_of_lt hklt))
        have hsecond := mul_le_mul_of_nonneg_left hdeltaBound hscale
        apply close_of_reduction
        dsimp [D, T, R] at hfirst hsecond ⊢
        nlinarith [hfirst, hsecond]

end Heilbronn8
