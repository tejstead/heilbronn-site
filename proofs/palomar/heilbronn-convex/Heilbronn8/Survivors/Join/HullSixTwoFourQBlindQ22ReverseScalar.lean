import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ22ReverseCertificate

/-!
# Reverse-height scalar closure for the q-blind q22 chamber

This file treats the missing `e < d` half of the coincident q22 packet.
The long polynomial work is isolated in the accompanying certificate module;
the proof here records only the normalized geometric reduction and the two
elementary final square arguments.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

open HullSixTwoFourQ22Reverse

theorem hullSixTwoFourQ22Reverse_scalar
    {a b c d e f A C E0 y z Fp : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hA1 : 1 ≤ A) (hC1 : 1 ≤ C) (hE01 : 1 ≤ E0)
    (hy1 : 1 ≤ y) (hz1 : 1 ≤ z) (hFp1 : 1 ≤ Fp)
    (hed : e < d)
    (hAtransition : a + b ≤ c * A)
    (hE0transition : c + d ≤ b * E0)
    (hytransition : d + e ≤ a * y)
    (hEar0 :
      d ≤ (y + d - e) * (d - c) + (d - e) * E0)
    (hEar1 : e ≤ (e - d) * z - (f - e) * y) :
    (25 : ℝ) / 2 < A + C + E0 + y + z + Fp + a + d := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hE0 : 0 < E0 := lt_of_lt_of_le zero_lt_one hE01
  have hy : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hFp : 0 < Fp := lt_of_lt_of_le zero_lt_one hFp1
  have hp : 0 < d - e := sub_pos.mpr hed
  have hdgt : 1 < d := lt_of_le_of_lt he1 hed

  have hpz : d - e ≤ (d - e) * z := by
    simpa using mul_le_mul_of_nonneg_left hz1 (le_of_lt hp)
  have hdy : d ≤ (e - f) * y := by
    nlinarith [hEar1, hpz]
  have hef : f < e := by
    by_contra hnot
    have hgap : e - f ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have hmul : (e - f) * y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hgap (le_of_lt hy)
    nlinarith
  have her : 0 < e - f := sub_pos.mpr hef

  by_cases hdc : d ≤ c
  · have hfirst : (y + d - e) * (d - c) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by nlinarith)
        (sub_nonpos.mpr hdc)
    have hE : d ≤ (d - e) * E0 := by
      nlinarith [hEar0, hfirst]
    have hrsum : (d - e) + (e - f) ≤ d - 1 := by
      linarith
    have hEy : d * y ≤ ((d - e) * E0) * y :=
      mul_le_mul_of_nonneg_right hE (le_of_lt hy)
    have hdyE : d * E0 ≤ ((e - f) * y) * E0 :=
      mul_le_mul_of_nonneg_right hdy (le_of_lt hE0)
    have hprod0 :
        d * (E0 + y) ≤ ((d - e) + (e - f)) * E0 * y := by
      nlinarith [hEy, hdyE]
    have hprod1 :
        ((d - e) + (e - f)) * E0 * y ≤ (d - 1) * E0 * y := by
      have hnonneg : 0 ≤ E0 * y := mul_nonneg (le_of_lt hE0) (le_of_lt hy)
      have hmul := mul_le_mul_of_nonneg_right hrsum hnonneg
      nlinarith
    have hprod : d * (E0 + y) ≤ (d - 1) * E0 * y :=
      hprod0.trans hprod1
    have hsq : 4 * E0 * y ≤ (E0 + y) ^ 2 := by
      nlinarith [sq_nonneg (E0 - y)]
    have hstep :
        4 * d * (E0 + y) ≤ (d - 1) * (E0 + y) ^ 2 := by
      have hleft : 4 * d * (E0 + y) ≤ 4 * ((d - 1) * E0 * y) := by
        nlinarith [hprod]
      have hright :
          4 * ((d - 1) * E0 * y) ≤ (d - 1) * (E0 + y) ^ 2 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr (le_of_lt hdgt))
      exact hleft.trans hright
    have hsumpos : 0 < E0 + y := add_pos hE0 hy
    have hstep' :
        (E0 + y) * (4 * d) ≤ (E0 + y) * ((d - 1) * (E0 + y)) := by
      nlinarith [hstep]
    have hrec : 4 * d ≤ (d - 1) * (E0 + y) :=
      by
        by_contra hnot
        have hlt : (d - 1) * (E0 + y) < 4 * d := lt_of_not_ge hnot
        have hmul := mul_lt_mul_of_pos_left hlt hsumpos
        exact (not_lt_of_ge hstep') hmul
    have hfactor : 0 ≤ (d - 1) * (d + E0 + y - 9) := by
      nlinarith [hrec, sq_nonneg (d - 3)]
    have hheight : 9 ≤ d + E0 + y := by
      by_contra hnot
      have hneg : d + E0 + y - 9 < 0 := by linarith
      have := mul_neg_of_pos_of_neg (sub_pos.mpr hdgt) hneg
      exact (not_lt_of_ge hfactor) this
    nlinarith
  · have hcd : c < d := lt_of_not_ge hdc
    have hygt : 1 < y := by
      by_contra hnot
      have hyle : y ≤ 1 := le_of_not_gt hnot
      have hry : (e - f) * y ≤ e - f := by
        simpa using mul_le_mul_of_nonneg_left hyle (le_of_lt her)
      nlinarith
    have hdiv : d / y ≤ e - f := by
      exact (div_le_iff₀ hy).2 (by simpa [mul_comm] using hdy)

    let q : ℝ := y - 1
    let h : ℝ := d - 1 - d / y
    have hq : 0 < q := by dsimp [q]; linarith
    have hph : d - e ≤ h := by
      dsimp [h]
      nlinarith
    have hh : 0 < h := lt_of_lt_of_le hp hph
    have hdOf : d = dOf q h := by
      dsimp [dOf, q, h]
      field_simp [hy.ne', sub_ne_zero.mpr (ne_of_gt hygt)]
      ring
    have ha0Identity : a0Q q h = (2 * d - h) / y := by
      dsimp [a0Q, q, h]
      field_simp [hy.ne', sub_ne_zero.mpr (ne_of_gt hygt)]
      ring
    have hayLower : 2 * d - h ≤ a * y := by
      nlinarith [hytransition, hph]
    have ha0 : a0Q q h ≤ a := by
      rw [ha0Identity]
      exact (div_le_iff₀ hy).2 (by simpa [mul_comm] using hayLower)

    by_contra hnot
    have hHle :
        A + C + E0 + y + z + Fp + a + d ≤ (25 : ℝ) / 2 :=
      le_of_not_gt hnot
    let B : ℝ := a + y + d
    let M : ℝ := (17 : ℝ) / 2 - B
    have hB : B ≤ (15 : ℝ) / 2 := by
      dsimp [B]
      nlinarith
    have hM1 : 1 ≤ M := by
      dsimp [M]
      linarith
    have hE0M : E0 ≤ M := by
      dsimp [M, B]
      nlinarith
    have hq9 : q < (9 : ℝ) / 2 := by
      dsimp [q, B] at hB ⊢
      nlinarith
    have hMcap : M ≤ (13 : ℝ) / 2 - q - d := by
      dsimp [M, B, q]
      linarith

    let T : ℝ := TQ q h
    let D : ℝ := DQ q h d M
    let U : ℝ := UQ q h d M
    have hTIdentity : T = y + h := by
      dsimp [T, TQ, q]
      ring
    have hD : 0 < D := by
      dsimp [D, DQ]
      have hhd : 0 < h / d := div_pos hh hd
      have hterm : 0 < (h / d) * M := mul_pos hhd (lt_of_lt_of_le zero_lt_one hM1)
      nlinarith
    have hU : (9 : ℝ) / 8 < U := by
      dsimp [U]
      exact u_gt_nine_eighths hq hq9 hh hdOf hMcap hD

    have hcoef : 0 ≤ (d - c) + E0 := by
      positivity
    have hreplace :
        (y + d - e) * (d - c) + (d - e) * E0 ≤
          (y + h) * (d - c) + h * E0 := by
      have hmul := mul_le_mul_of_nonneg_right hph hcoef
      nlinarith
    have hEarUpper : d ≤ (y + h) * (d - c) + h * E0 :=
      hEar0.trans hreplace
    have hTcE : T * c ≤ d * (T - 1 + (h / d) * E0) := by
      have hid : d * (T - 1 + (h / d) * E0) = T * d - d + h * E0 := by
        field_simp [hd.ne']
      rw [hid, hTIdentity]
      nlinarith [hEarUpper]
    have hinner : T - 1 + (h / d) * E0 ≤ D := by
      dsimp [D, DQ]
      have hhd0 : 0 ≤ h / d := le_of_lt (div_pos hh hd)
      have hmul := mul_le_mul_of_nonneg_left hE0M hhd0
      nlinarith
    have hTc : T * c ≤ d * D := by
      have hmul := mul_le_mul_of_nonneg_left hinner (le_of_lt hd)
      exact hTcE.trans hmul

    let u : ℝ := d / c
    let t : ℝ := b / c
    have hu : 0 < u := by dsimp [u]; positivity
    have ht : 0 < t := by dsimp [t]; positivity
    have hUu : U ≤ u := by
      have hquot : T / D ≤ d / c := (div_le_div_iff₀ hD hc).2 hTc
      simpa [U, UQ, u] using hquot

    have hALower : (a + b) / c ≤ A :=
      (div_le_iff₀ hc).2 (by simpa [mul_comm] using hAtransition)
    have hE0Lower : (c + d) / b ≤ E0 :=
      (div_le_iff₀ hb).2 (by simpa [mul_comm] using hE0transition)
    have htransitionIdentity :
        (a + b) / c + (c + d) / b =
          (a / d) * u + t + (1 + u) / t := by
      dsimp [u, t]
      field_simp [hb.ne', hc.ne', hd.ne']
    have hAE :
        (a / d) * u + t + (1 + u) / t ≤ A + E0 := by
      rw [← htransitionIdentity]
      linarith

    by_cases hUhigh : (5 : ℝ) / 4 ≤ U
    · have huHigh : (5 : ℝ) / 4 ≤ u := hUhigh.trans hUu
      have hpair : 3 ≤ t + (1 + u) / t := by
        have hid : t + (1 + u) / t = (t ^ 2 + (1 + u)) / t := by
          field_simp [ht.ne']
        rw [hid]
        apply (le_div_iff₀ ht).2
        nlinarith [sq_nonneg (t - (3 : ℝ) / 2)]
      have hCore :
          (13 : ℝ) / 2 < B + (a / d) * U := by
        have hBcore : a + (q + 1) + d ≤ (15 : ℝ) / 2 := by
          simpa [B, q] using hB
        have hDcore :
            0 < DQ q h d
              ((17 : ℝ) / 2 - (a + (q + 1) + d)) := by
          simpa [D, M, B, q] using hD
        have hraw := core_gt_thirteen_halves
          hq hq9 hh hdOf ha1 ha0 hBcore hDcore
        simpa [B, q, U, M] using hraw
      have hratio : 0 < a / d := div_pos ha hd
      have hCoreU : B + (a / d) * U ≤ B + (a / d) * u := by
        simpa [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_left hUu (le_of_lt hratio)) B
      dsimp [B] at hCore hCoreU
      nlinarith
    · have hUlow : U < (5 : ℝ) / 4 := lt_of_not_ge hUhigh
      have hTD : T < (5 : ℝ) / 4 * D := by
        dsimp [U, UQ] at hUlow
        exact (div_lt_iff₀ hD).mp hUlow
      have hRactual :
          0 < T + 5 * (h / d) * M - 5 := by
        dsimp [D, DQ] at hTD
        nlinarith

      have ha0SIdentity : a0S y d = a0Q q h := by
        rw [ha0Identity]
        dsimp [a0S, h]
        field_simp [hy.ne']
        ring
      have ha0S : a0S y d ≤ a := by
        rw [ha0SIdentity]
        exact ha0
      let aStar : ℝ := max 1 (a0S y d)
      have haStar1 : 1 ≤ aStar := by
        exact le_max_left 1 (a0S y d)
      have haStarA : aStar ≤ a := by
        exact max_le ha1 ha0S
      have hMS : M ≤ MS aStar y d := by
        dsimp [M, B, MS]
        linarith
      have hMS1 : 1 ≤ MS aStar y d := hM1.trans hMS
      have hTS : TS y d = T := by
        rw [hTIdentity]
        dsimp [TS, h]
        field_simp [hy.ne']
        ring
      have hkS : kS y d = h / d := by
        dsimp [kS, h]
        field_simp [hy.ne', hd.ne']
        ring
      have hRStar :
          0 ≤ TS y d + 5 * kS y d * MS aStar y d - 5 := by
        have hk0 : 0 ≤ 5 * (h / d) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hMS hk0
        rw [hTS, hkS]
        nlinarith
      have hdS : y / (y - 1) < d := by
        apply (div_lt_iff₀ (sub_pos.mpr hygt)).2
        have hyh : 0 < y * h := mul_pos hy hh
        dsimp [h] at hyh
        field_simp [hy.ne'] at hyh
        nlinarith
      have hPhi :
          (53 : ℝ) / 8 ≤
            aStar + y + d + (9 / 8) * (aStar / d) := by
        by_cases ha01 : a0S y d ≤ 1
        · have hstar : aStar = 1 := max_eq_left ha01
          have hMS1' : 1 ≤ MS 1 y d := by simpa [hstar] using hMS1
          have hRStar' :
              0 ≤ TS y d + 5 * kS y d * MS 1 y d - 5 := by
            simpa [hstar] using hRStar
          have hlow := low_phi_one hygt hdS ha01 hMS1' hRStar'
          simpa [hstar] using hlow
        · have ha01' : 1 < a0S y d := lt_of_not_ge ha01
          have hstar : aStar = a0S y d :=
            max_eq_right (le_of_lt ha01')
          have hMSa : 1 ≤ MS (a0S y d) y d := by
            simpa [hstar] using hMS1
          have hRStar' :
              0 ≤ TS y d + 5 * kS y d * MS (a0S y d) y d - 5 := by
            simpa [hstar] using hRStar
          have hlow := low_phi_a0 hygt hdS ha01' hMSa hRStar'
          simpa [hstar] using hlow
      have haStar : 0 < aStar := lt_of_lt_of_le zero_lt_one haStar1
      have hratioStar : 0 < aStar / d := div_pos haStar hd
      have hratioLe : aStar / d ≤ a / d := by
        exact (div_le_div_iff_of_pos_right hd).2 haStarA
      have hUStrict :
          (9 / 8) * (aStar / d) < U * (aStar / d) :=
        mul_lt_mul_of_pos_right hU hratioStar
      have hUpos : 0 < U := lt_trans (by norm_num) hU
      have hUCompare : U * (aStar / d) ≤ U * (a / d) :=
        mul_le_mul_of_nonneg_left hratioLe (le_of_lt hUpos)
      have hActualPhi :
          (53 : ℝ) / 8 < B + (a / d) * U := by
        dsimp [B]
        nlinarith

      have huLow : (9 : ℝ) / 8 < u := hU.trans_le hUu
      let v : ℝ := (1 + u) / t
      have hv : 0 < v := by
        dsimp [v]
        positivity
      have htv : t * v = 1 + u := by
        dsimp [v]
        field_simp [ht.ne']
      have hsquare : 4 * t * v ≤ (t + v) ^ 2 := by
        nlinarith [sq_nonneg (t - v)]
      have hprodStrict : (17 : ℝ) / 2 < 4 * t * v := by
        nlinarith [htv, huLow]
      have hpairLow : (23 : ℝ) / 8 < t + (1 + u) / t := by
        change (23 : ℝ) / 8 < t + v
        by_contra hnotPair
        have hle : t + v ≤ (23 : ℝ) / 8 := le_of_not_gt hnotPair
        have hleft : 0 ≤ (23 : ℝ) / 8 - (t + v) := by linarith
        have hright : 0 ≤ (23 : ℝ) / 8 + (t + v) := by positivity
        have hfac := mul_nonneg hleft hright
        nlinarith
      have hratio : 0 ≤ a / d := le_of_lt (div_pos ha hd)
      have hBaseU : B + (a / d) * U ≤ B + (a / d) * u :=
        by
          simpa [add_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_left hUu hratio) B
      dsimp [B] at hActualPhi
      dsimp [B] at hBaseU
      nlinarith

end Heilbronn8
