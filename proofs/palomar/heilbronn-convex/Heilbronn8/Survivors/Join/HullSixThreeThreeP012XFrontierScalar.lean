import Mathlib.Analysis.MeanInequalities

/-!
# Scalar closure for the maximal-q `p = 012` X-frontier

This module is geometry-free.  Five positive floor multipliers encode the
successive merged-slope determinants in the order
`U0,L0,U1,L1,U2,L2`.  The strengthened wrap floor is then reduced to the
unit-floor chamber.  Its scale parameter disappears through one exact
two-variable AM--GM identity.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Heilbronn8

private lemma p012_two_sqrt_mul_le_add {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  rw [Real.sqrt_mul hx]
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]

/-! ## The one-variable analytic remainder -/

private lemma p012_sqrt_quotient_bound {A : ℝ} (hA : 0 < A) :
    9 / 2 ≤ A + 2 * Real.sqrt (1 + 3 * A) / A := by
  let q := Real.sqrt (1 + 3 * A)
  have hrad : 0 ≤ 1 + 3 * A := by positivity
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = 1 + 3 * A := by
    simpa [q] using Real.sq_sqrt hrad
  have hq1 : 1 < q := by
    apply (sq_lt_sq₀ (by norm_num) hq0).mp
    nlinarith
  have hpoly :
      0 ≤ 2 * q ^ 4 - 31 * q ^ 2 + 36 * q + 29 := by
    by_cases htwo : q ≤ 2
    · have hquad : q ^ 2 ≤ 3 * q - 2 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr hq1.le) (sub_nonpos.mpr htwo)]
      have hfactor :
          0 ≤ (q - 2) ^ 2 * (q ^ 2 + 4 * q + 12) := by
        exact mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg q])
      have hquartic : 32 * q - 48 ≤ q ^ 4 := by
        nlinarith [hfactor]
      nlinarith
    · have htwo' : 2 < q := lt_of_not_ge htwo
      by_cases hfive : q ≤ 5 / 2
      · let h := q - 2
        have hh : 0 ≤ h := by dsimp [h]; linarith
        have hsos :
            0 < 2 * h ^ 4 + 16 * h ^ 3 +
                17 * (h - 12 / 17) ^ 2 + 9 / 17 := by
          have h3 : 0 ≤ h ^ 3 := by positivity
          have h4 : 0 ≤ h ^ 4 := by positivity
          nlinarith [sq_nonneg (h - 12 / 17)]
        dsimp [h] at hsos
        nlinarith
      · have hfive' : 5 / 2 < q := lt_of_not_ge hfive
        let h := q - 5 / 2
        have hh : 0 < h := by dsimp [h]; linarith
        have hsos :
            0 < 2 * h ^ 4 + 20 * h ^ 3 + 44 * h ^ 2 +
                6 * h + 27 / 8 := by positivity
        dsimp [h] at hsos
        nlinarith
  have hcleared : 9 * A ≤ 2 * A ^ 2 + 4 * q := by
    nlinarith [hpoly]
  have hmul :
      (9 / 2) * A ≤
        (A + 2 * Real.sqrt (1 + 3 * A) / A) * A := by
    dsimp [q] at hcleared
    rw [add_mul, div_mul_cancel₀ _ hA.ne']
    nlinarith [hcleared]
  exact le_of_mul_le_mul_right hmul hA

private lemma p012_cubic_sqrt_gt {A : ℝ} (hA : 0 < A) :
    5 * A < 2 * (A + 1) * Real.sqrt (A + 1) := by
  have hA1 : 0 ≤ A + 1 := by positivity
  have hsqrt : (Real.sqrt (A + 1)) ^ 2 = A + 1 :=
    Real.sq_sqrt hA1
  have hfactor : 0 ≤ (A - 2) ^ 2 * (4 * A + 1) := by positivity
  have hcubic : 27 * A ^ 2 ≤ 4 * (A + 1) ^ 3 := by
    nlinarith [hfactor]
  apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
  nlinarith [sq_pos_of_pos hA]

/-! ## Exact scale cancellation in the unit-floor chamber -/

private lemma p012_interior_key
    {p h B : ℝ} (hp : 0 < p) (hh : 0 < h) (hB : 0 < B) :
    let A := p + h + p * h
    let U := (1 + h + p * h) / p
    let V := p * (1 + 1 / h + 1 / (p * h))
    let S := Real.sqrt (1 + 3 * A)
    19 / 2 <
      A + U * B + V / B + (2 * S - B - 1 / B) / A := by
  dsimp
  let A := p + h + p * h
  let U := (1 + h + p * h) / p
  let V := p * (1 + 1 / h + 1 / (p * h))
  let S := Real.sqrt (1 + 3 * A)
  let T := Real.sqrt (A + 1)
  let alpha := U - 1 / A
  let beta := V - 1 / A
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 0 < A + 1 := by positivity
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hTSq : T ^ 2 = A + 1 := by
    simpa [T] using Real.sq_sqrt hA1.le
  have hAlphaId :
      A * U - 1 = (A + 1) * h * (1 + p) / p := by
    dsimp [A, U]
    field_simp [hp.ne', hh.ne'] <;> ring
  have hBetaId :
      A * V - 1 = (A + 1) * p * (1 + h) / h := by
    dsimp [A, V]
    field_simp [hp.ne', hh.ne'] <;> ring
  have hAlpha : 0 < alpha := by
    have : 0 < A * U - 1 := by rw [hAlphaId]; positivity
    have hid : alpha = (A * U - 1) / A := by
      dsimp [alpha]
      field_simp [hA.ne'] <;> ring
    rw [hid]
    exact div_pos this hA
  have hBeta : 0 < beta := by
    have : 0 < A * V - 1 := by rw [hBetaId]; positivity
    have hid : beta = (A * V - 1) / A := by
      dsimp [beta]
      field_simp [hA.ne'] <;> ring
    rw [hid]
    positivity
  have hprod : alpha * beta = (A + 1) ^ 3 / A ^ 2 := by
    dsimp [alpha, beta]
    rw [show (U - 1 / A) = (A * U - 1) / A by
      field_simp [hA.ne'] <;> ring]
    rw [show (V - 1 / A) = (A * V - 1) / A by
      field_simp [hA.ne'] <;> ring]
    rw [hAlphaId, hBetaId]
    have hAh : (1 + p) * (1 + h) = A + 1 := by
      dsimp [A]
      ring
    field_simp [hp.ne', hh.ne', hA.ne']
    nlinarith
  let X := alpha * B
  let Y := beta / B
  let L := (A + 1) * T / A
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hXY : X * Y = L ^ 2 := by
    calc
      X * Y = alpha * beta := by
        dsimp [X, Y]
        field_simp [hB.ne'] <;> ring
      _ = (A + 1) ^ 3 / A ^ 2 := hprod
      _ = (A + 1) ^ 2 * T ^ 2 / A ^ 2 := by
        rw [hTSq]
        ring
      _ = ((A + 1) * T) ^ 2 / A ^ 2 := by ring
      _ = L ^ 2 := by
        dsimp [L]
        rw [div_pow]
  have hpair : 2 * L ≤ X + Y := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg (X - Y)]
  have hquot := p012_sqrt_quotient_bound hA
  have hcubic := p012_cubic_sqrt_gt hA
  have hcubicDiv : 5 < 2 * (A + 1) * T / A := by
    apply (lt_div_iff₀ hA).2
    simpa [T, mul_assoc, mul_comm, mul_left_comm] using hcubic
  have hrearrange :
      A + U * B + V / B + (2 * S - B - 1 / B) / A =
        (A + 2 * S / A) + (X + Y) := by
    dsimp [X, Y, alpha, beta]
    field_simp [hA.ne', hB.ne'] <;> ring
  rw [hrearrange]
  dsimp [S] at hquot ⊢
  dsimp [L] at hpair
  have hfiveXY : 5 < X + Y := by
    calc
      5 < 2 * (A + 1) * T / A := hcubicDiv
      _ = 2 * ((A + 1) * T / A) := by ring
      _ ≤ X + Y := hpair
  calc
    (19 : ℝ) / 2 = 9 / 2 + 5 := by norm_num
    _ < (A + 2 * Real.sqrt (1 + 3 * A) / A) + (X + Y) :=
      add_lt_add_of_le_of_lt hquot hfiveXY

private lemma p012_unit_floor_gt
    {r s t u v : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hu : 0 < u) (hv : 0 < v)
    (hwrap : 3 ≤
      1 / (u * v) + r / (u * v) + r / v + r * s / v + r * s) :
    19 / 2 <
      s * t +
      (r * s * t + 1 / s + 1 / (s * t * u)) +
      (t * u + u / s + 1 / (s * t)) +
      (s * t * u + u + 1 / (t * u * v)) +
      1 / (t * u) := by
  let x := s * t
  let y := s * t * u
  let z := t * u
  let w := r * s * t
  let k := 1 / (t * u * v)
  let A := z / y + z / x + y / x
  let B := x * z / y
  let q := B * k
  let rr := w / B
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hrr : 0 < rr := by dsimp [rr]; positivity
  have hwrap' : 3 ≤ q + rr + A * q * rr := by
    have hid :
        q + rr + A * q * rr =
          1 / (u * v) + r / (u * v) + r / v + r * s / v + r * s := by
      dsimp [q, rr, A, B, x, y, z, w, k]
      field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
    rw [hid]
    exact hwrap
  let Q := 1 + A * q
  let RR := 1 + A * rr
  let S := Real.sqrt (1 + 3 * A)
  have hrad : 0 ≤ 1 + 3 * A := by positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hSSq : S ^ 2 = 1 + 3 * A := by
    simpa [S] using Real.sq_sqrt hrad
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hRR : 0 < RR := by dsimp [RR]; positivity
  have hprod : S ^ 2 ≤ Q * RR := by
    dsimp [Q, RR]
    nlinarith
  let X := B * RR
  let Y := Q / B
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hXY : X * Y = Q * RR := by
    dsimp [X, Y]
    field_simp [hB.ne'] <;> ring
  have hpair : 2 * S ≤ X + Y := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [hprod, hXY, sq_nonneg (X - Y)]
  have hcost :
      (2 * S - B - 1 / B) / A ≤ B * rr + q / B := by
    have hid :
        X + Y - B - 1 / B = A * (B * rr + q / B) := by
      dsimp [X, Y, Q, RR]
      field_simp [hB.ne'] <;> ring
    apply (div_le_iff₀ hA).2
    nlinarith
  let p := z / y
  let h := y / x
  have hp : 0 < p := by dsimp [p]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hAid : A = p + h + p * h := by
    dsimp [A, p, h]
    field_simp [hx.ne', hy.ne', hz.ne'] <;> ring
  have hKid :
      x + 1 / x + y + 1 / y + z + 1 / z + A =
        A + ((1 + h + p * h) / p) * B +
          (p * (1 + 1 / h + 1 / (p * h))) / B := by
    dsimp [A, B, p, h]
    field_simp [hx.ne', hy.ne', hz.ne'] <;> ring
  have hinterior := p012_interior_key hp hh hB
  rw [← hAid] at hinterior
  have hbase :
      19 / 2 <
        x + 1 / x + y + 1 / y + z + 1 / z + A +
          B * rr + q / B := by
    rw [hKid]
    exact lt_of_lt_of_le hinterior (by nlinarith [hcost])
  have hR :
      s * t +
        (r * s * t + 1 / s + 1 / (s * t * u)) +
        (t * u + u / s + 1 / (s * t)) +
        (s * t * u + u + 1 / (t * u * v)) +
        1 / (t * u) =
      x + 1 / x + y + 1 / y + z + 1 / z + A +
        B * rr + q / B := by
    dsimp [x, y, z, w, k, A, B, q, rr]
    field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
  rw [hR]
  exact hbase

/-! ## Excess floors: the cheapest added wrap is an endpoint -/

private lemma p012_center_not_below_both
    {q0 q2 q4 x : ℝ}
    (hq0 : 0 < q0) (hq2 : 0 < q2) (hq4 : 0 < q4) (hx : 0 < x)
    (hsum : q0 + q4 < 3) :
    ¬ (x + 1 / (q0 * q4) + 1 / (q0 * q2 * q4 * x) < q4 * x ∧
      x + 1 / (q0 * q4) + 1 / (q0 * q2 * q4 * x) <
        1 / (q2 * q4 * x)) := by
  rintro ⟨hleft, hright⟩
  have hden : 0 < q0 * q2 * q4 * x := by positivity
  have hdenR : 0 < q2 * q4 * x := by positivity
  have hthird :
      1 / (q0 * q2 * q4 * x) < (q4 - 1) * x := by
    have hmid : 0 < 1 / (q0 * q4) := by positivity
    nlinarith
  have hA :
      1 < (q0 * q2 * q4 * x ^ 2) * (q4 - 1) := by
    calc
      1 < (q4 - 1) * x * (q0 * q2 * q4 * x) :=
        (div_lt_iff₀ hden).mp hthird
      _ = (q0 * q2 * q4 * x ^ 2) * (q4 - 1) := by ring
  have hshort :
      x + 1 / (q0 * q2 * q4 * x) < 1 / (q2 * q4 * x) := by
    have hmid : 0 < 1 / (q0 * q4) := by positivity
    linarith
  have hB : q0 * q2 * q4 * x ^ 2 < q0 - 1 := by
    have hmul := mul_lt_mul_of_pos_right hshort hden
    have hleft :
        (x + 1 / (q0 * q2 * q4 * x)) * (q0 * q2 * q4 * x) =
          q0 * q2 * q4 * x ^ 2 + 1 := by
      field_simp [hq0.ne', hq2.ne', hq4.ne', hx.ne'] <;> ring
    have hright :
        (1 / (q2 * q4 * x)) * (q0 * q2 * q4 * x) = q0 := by
      field_simp [hq0.ne', hq2.ne', hq4.ne', hx.ne'] <;> ring
    rw [hleft, hright] at hmul
    nlinarith
  have hM : 0 < q0 * q2 * q4 * x ^ 2 := by positivity
  have hq4one : 0 < q4 - 1 := by nlinarith
  have hprod : 1 < (q0 - 1) * (q4 - 1) := by
    have hm := mul_lt_mul_of_pos_right hB hq4one
    nlinarith
  have hq0one : 0 < q0 - 1 := by
    have := mul_pos_iff.mp (lt_trans zero_lt_one hprod)
    rcases this with h | h
    · exact h.1
    · have hsmall : 0 < q4 * (1 - q0) :=
        mul_pos hq4 (sub_pos.mpr (by linarith [h.1]))
      nlinarith [hsmall]
  have hfour : 4 < q0 + q4 := by
    nlinarith [sq_nonneg ((q0 - 1) - (q4 - 1))]
  linarith

private lemma p012_ratio_core
    {r s t u v x0 x1 x2 x3 x4 : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hu : 0 < u) (hv : 0 < v)
    (hx0 : 1 ≤ x0) (hx1 : 1 ≤ x1) (hx2 : 1 ≤ x2)
    (hx3 : 1 ≤ x3) (hx4 : 1 ≤ x4)
    (hwrap : 3 ≤
      (1 / (u * v)) * x0 + (r / (u * v)) * x1 +
      (r / v) * x2 + (r * s / v) * x3 + (r * s) * x4) :
    19 / 2 <
      (s * t) * x0 +
      (r * s * t + 1 / s + 1 / (s * t * u)) * x1 +
      (t * u + u / s + 1 / (s * t)) * x2 +
      (s * t * u + u + 1 / (t * u * v)) * x3 +
      (1 / (t * u)) * x4 := by
  let q0 := 1 / (u * v)
  let q1 := r / (u * v)
  let q2 := r / v
  let q3 := r * s / v
  let q4 := r * s
  let L0 := s * t
  let L1 := r * s * t + 1 / s + 1 / (s * t * u)
  let L2 := t * u + u / s + 1 / (s * t)
  let L3 := s * t * u + u + 1 / (t * u * v)
  let L4 := 1 / (t * u)
  let F0 := q0 + q1 + q2 + q3 + q4
  let R0 := L0 + L1 + L2 + L3 + L4
  have hq0 : 0 < q0 := by dsimp [q0]; positivity
  have hq1 : 0 < q1 := by dsimp [q1]; positivity
  have hq2 : 0 < q2 := by dsimp [q2]; positivity
  have hq3 : 0 < q3 := by dsimp [q3]; positivity
  have hq4 : 0 < q4 := by dsimp [q4]; positivity
  have hL0 : 0 < L0 := by dsimp [L0]; positivity
  have hL1 : 0 < L1 := by dsimp [L1]; positivity
  have hL2 : 0 < L2 := by dsimp [L2]; positivity
  have hL3 : 0 < L3 := by dsimp [L3]; positivity
  have hL4 : 0 < L4 := by dsimp [L4]; positivity
  by_cases hbase : 3 ≤ F0
  · have hunit := p012_unit_floor_gt hr hs ht hu hv (by
      simpa [F0, q0, q1, q2, q3, q4] using hbase)
    have hmono :
        R0 ≤ L0 * x0 + L1 * x1 + L2 * x2 + L3 * x3 + L4 * x4 := by
      have h0 := mul_le_mul_of_nonneg_left hx0 hL0.le
      have h1 := mul_le_mul_of_nonneg_left hx1 hL1.le
      have h2 := mul_le_mul_of_nonneg_left hx2 hL2.le
      have h3 := mul_le_mul_of_nonneg_left hx3 hL3.le
      have h4 := mul_le_mul_of_nonneg_left hx4 hL4.le
      dsimp [R0]
      nlinarith
    dsimp [L0, L1, L2, L3, L4] at hmono ⊢
    nlinarith
  · have hF0 : F0 < 3 := lt_of_not_ge hbase
    let rho0 := L0 / q0
    let rho2 := L2 / q2
    let rho4 := L4 / q4
    have hrho0 : 0 < rho0 := by dsimp [rho0]; positivity
    have hrho2 : 0 < rho2 := by dsimp [rho2]; positivity
    have hrho4 : 0 < rho4 := by dsimp [rho4]; positivity
    have hsum04 : q0 + q4 < 3 := by
      dsimp [F0] at hF0
      nlinarith
    let xx := t / q1
    have hxx : 0 < xx := by dsimp [xx]; positivity
    have hrho0id : rho0 = q4 * xx := by
      dsimp [rho0, L0, q0, q4, xx, q1]
      field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
    have hrho4id : rho4 = 1 / (q2 * q4 * xx) := by
      dsimp [rho4, L4, q4, q2, xx, q1]
      field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
    have hrho2id :
        rho2 = xx + 1 / (q0 * q4) + 1 / (q0 * q2 * q4 * xx) := by
      dsimp [rho2, L2, q2, xx, q1, q0, q4]
      field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
    have hcenter : ¬ (rho2 < rho0 ∧ rho2 < rho4) := by
      rw [hrho0id, hrho4id, hrho2id]
      exact p012_center_not_below_both hq0 hq2 hq4 hxx hsum04
    by_cases hend : rho0 ≤ rho4
    · have h02 : rho0 ≤ rho2 := by
        by_contra h
        exact hcenter ⟨lt_of_not_ge h, lt_of_lt_of_le (lt_of_not_ge h) hend⟩
      have h01 : rho0 ≤ L1 / q1 := by
        apply (le_div_iff₀ hq1).2
        have hid : rho0 * q1 = r * s * t := by
          dsimp [rho0, L0, q0, q1]
          field_simp [hu.ne', hv.ne'] <;> ring
        rw [hid]
        dsimp [L1]
        have hp1 : 0 ≤ 1 / s := by positivity
        have hp2 : 0 ≤ 1 / (s * t * u) := by positivity
        linarith
      have h03 : rho0 ≤ L3 / q3 := by
        have h43 : rho4 ≤ L3 / q3 := by
          apply (le_div_iff₀ hq3).2
          have hid : rho4 * q3 = 1 / (t * u * v) := by
            dsimp [rho4, L4, q4, q3]
            field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
          rw [hid]
          dsimp [L3]
          have hp1 : 0 ≤ s * t * u := by positivity
          have hp2 : 0 ≤ u := hu.le
          linarith
        exact hend.trans h43
      have h0i : ∀ i : Fin 5,
          rho0 * (![q0, q1, q2, q3, q4] i) ≤
            (![L0, L1, L2, L3, L4] i) := by
        intro i
        fin_cases i
        · dsimp [rho0]
          exact (div_mul_cancel₀ L0 hq0.ne').le
        · exact (le_div_iff₀ hq1).mp h01
        · exact (le_div_iff₀ hq2).mp h02
        · exact (le_div_iff₀ hq3).mp h03
        · exact (le_div_iff₀ hq4).mp hend
      let extra : Fin 5 → ℝ := ![x0 - 1, x1 - 1, x2 - 1, x3 - 1, x4 - 1]
      have hextra : ∀ i, 0 ≤ extra i := by
        intro i; fin_cases i <;> simp [extra] <;> linarith
      have hcost :
          rho0 * (3 - F0) ≤
            L0 * (x0 - 1) + L1 * (x1 - 1) + L2 * (x2 - 1) +
              L3 * (x3 - 1) + L4 * (x4 - 1) := by
        have hwextra : 3 - F0 ≤
            q0 * (x0 - 1) + q1 * (x1 - 1) + q2 * (x2 - 1) +
              q3 * (x3 - 1) + q4 * (x4 - 1) := by
          dsimp [F0, q0, q1, q2, q3, q4] at hwrap ⊢
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left hwextra hrho0.le
        have hterm (i : Fin 5) :=
          mul_le_mul_of_nonneg_right (h0i i) (hextra i)
        have h0 := hterm 0
        have h1 := hterm 1
        have h2 := hterm 2
        have h3 := hterm 3
        have h4 := hterm 4
        norm_num at h0 h1 h2 h3 h4
        calc
          rho0 * (3 - F0) ≤
              rho0 * (q0 * (x0 - 1) + q1 * (x1 - 1) + q2 * (x2 - 1) +
                q3 * (x3 - 1) + q4 * (x4 - 1)) := hmul
          _ = rho0 * q0 * (x0 - 1) + rho0 * q1 * (x1 - 1) +
                rho0 * q2 * (x2 - 1) + rho0 * q3 * (x3 - 1) +
                rho0 * q4 * (x4 - 1) := by ring
          _ ≤ L0 * (x0 - 1) + L1 * (x1 - 1) + L2 * (x2 - 1) +
                L3 * (x3 - 1) + L4 * (x4 - 1) :=
            add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4
      let C := 1 / (u * v) + 1 / v + s / v + s
      let r' := (3 - q0) / C
      have hC : 0 < C := by dsimp [C]; positivity
      have hr' : 0 < r' := by
        dsimp [r']
        apply div_pos
        · dsimp [F0] at hF0
          nlinarith
        · exact hC
      have hFaff : F0 = q0 + r * C := by
        dsimp [F0, q0, q1, q2, q3, q4, C]
        field_simp [hu.ne', hv.ne'] <;> ring
      have hrr' : r < r' := by
        apply (lt_div_iff₀ hC).2
        rw [hFaff] at hF0
        nlinarith
      have hunitWrap : 3 ≤
          1 / (u * v) + r' / (u * v) + r' / v +
            r' * s / v + r' * s := by
        have hid :
            1 / (u * v) + r' / (u * v) + r' / v +
                r' * s / v + r' * s = q0 + r' * C := by
          dsimp [q0, C]
          field_simp [hu.ne', hv.ne'] <;> ring
        rw [hid]
        dsimp [r']
        rw [div_mul_cancel₀ (3 - q0) hC.ne']
        linarith
      have hnew := p012_unit_floor_gt hr' hs ht hu hv hunitWrap
      have hslope : s * t < rho0 * C := by
        have hq0C : q0 < C := by
          dsimp [q0, C]
          have h1 : 0 < 1 / v := by positivity
          have h2 : 0 < s / v := by positivity
          linarith [hs]
        calc
          s * t = L0 := rfl
          _ = rho0 * q0 := by
            dsimp [rho0]
            exact (div_mul_cancel₀ L0 hq0.ne').symm
          _ < rho0 * C := mul_lt_mul_of_pos_left hq0C hrho0
      have hcompare :
          R0 + s * t * (r' - r) ≤ R0 + rho0 * (3 - F0) := by
        have hdeficit : 3 - F0 = C * (r' - r) := by
          rw [hFaff]
          dsimp [r']
          field_simp [hC.ne'] <;> ring
        rw [hdeficit]
        have := mul_le_mul_of_nonneg_right hslope.le (sub_nonneg.mpr hrr'.le)
        nlinarith
      have hRnew :
          s * t +
            (r' * s * t + 1 / s + 1 / (s * t * u)) +
            (t * u + u / s + 1 / (s * t)) +
            (s * t * u + u + 1 / (t * u * v)) +
            1 / (t * u) = R0 + s * t * (r' - r) := by
        dsimp [R0, L0, L1, L2, L3, L4]
        ring
      rw [hRnew] at hnew
      dsimp [R0, L0, L1, L2, L3, L4] at hcost hcompare ⊢
      nlinarith
    · have hend' : rho4 < rho0 := lt_of_not_ge hend
      have h42 : rho4 ≤ rho2 := by
        by_contra h
        exact hcenter ⟨lt_trans (lt_of_not_ge h) hend', lt_of_not_ge h⟩
      have h41 : rho4 ≤ L1 / q1 := by
        have h01 : rho0 ≤ L1 / q1 := by
          apply (le_div_iff₀ hq1).2
          have hid : rho0 * q1 = r * s * t := by
            dsimp [rho0, L0, q0, q1]
            field_simp [hu.ne', hv.ne'] <;> ring
          rw [hid]
          dsimp [L1]
          have hp1 : 0 ≤ 1 / s := by positivity
          have hp2 : 0 ≤ 1 / (s * t * u) := by positivity
          linarith
        exact hend'.le.trans h01
      have h43 : rho4 ≤ L3 / q3 := by
        apply (le_div_iff₀ hq3).2
        have hid : rho4 * q3 = 1 / (t * u * v) := by
          dsimp [rho4, L4, q4, q3]
          field_simp [hr.ne', hs.ne', ht.ne', hu.ne', hv.ne'] <;> ring
        rw [hid]
        dsimp [L3]
        have hp1 : 0 ≤ s * t * u := by positivity
        have hp2 : 0 ≤ u := hu.le
        linarith
      have h4i : ∀ i : Fin 5,
          rho4 * (![q0, q1, q2, q3, q4] i) ≤
            (![L0, L1, L2, L3, L4] i) := by
        intro i
        fin_cases i
        · exact (le_div_iff₀ hq0).mp hend'.le
        · exact (le_div_iff₀ hq1).mp h41
        · exact (le_div_iff₀ hq2).mp h42
        · exact (le_div_iff₀ hq3).mp h43
        · dsimp [rho4]
          exact (div_mul_cancel₀ L4 hq4.ne').le
      let extra : Fin 5 → ℝ := ![x0 - 1, x1 - 1, x2 - 1, x3 - 1, x4 - 1]
      have hextra : ∀ i, 0 ≤ extra i := by
        intro i; fin_cases i <;> simp [extra] <;> linarith
      have hcost :
          rho4 * (3 - F0) ≤
            L0 * (x0 - 1) + L1 * (x1 - 1) + L2 * (x2 - 1) +
              L3 * (x3 - 1) + L4 * (x4 - 1) := by
        have hwextra : 3 - F0 ≤
            q0 * (x0 - 1) + q1 * (x1 - 1) + q2 * (x2 - 1) +
              q3 * (x3 - 1) + q4 * (x4 - 1) := by
          dsimp [F0, q0, q1, q2, q3, q4] at hwrap ⊢
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left hwextra hrho4.le
        have hterm (i : Fin 5) :=
          mul_le_mul_of_nonneg_right (h4i i) (hextra i)
        have h0 := hterm 0
        have h1 := hterm 1
        have h2 := hterm 2
        have h3 := hterm 3
        have h4 := hterm 4
        norm_num at h0 h1 h2 h3 h4
        calc
          rho4 * (3 - F0) ≤
              rho4 * (q0 * (x0 - 1) + q1 * (x1 - 1) + q2 * (x2 - 1) +
                q3 * (x3 - 1) + q4 * (x4 - 1)) := hmul
          _ = rho4 * q0 * (x0 - 1) + rho4 * q1 * (x1 - 1) +
                rho4 * q2 * (x2 - 1) + rho4 * q3 * (x3 - 1) +
                rho4 * q4 * (x4 - 1) := by ring
          _ ≤ L0 * (x0 - 1) + L1 * (x1 - 1) + L2 * (x2 - 1) +
                L3 * (x3 - 1) + L4 * (x4 - 1) :=
            add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4
      let zeta := 1 / v
      let C := 1 / u + r / u + r + r * s
      let zeta' := (3 - q4) / C
      have hzeta : 0 < zeta := by dsimp [zeta]; positivity
      have hC : 0 < C := by dsimp [C]; positivity
      have hzeta' : 0 < zeta' := by
        dsimp [zeta']
        apply div_pos
        · dsimp [F0] at hF0
          nlinarith
        · exact hC
      have hFaff : F0 = q4 + zeta * C := by
        dsimp [F0, q0, q1, q2, q3, q4, zeta, C]
        field_simp [hu.ne', hv.ne'] <;> ring
      have hzz' : zeta < zeta' := by
        apply (lt_div_iff₀ hC).2
        rw [hFaff] at hF0
        nlinarith
      let v' := 1 / zeta'
      have hv' : 0 < v' := by dsimp [v']; positivity
      have hv'id : 1 / v' = zeta' := by
        dsimp [v']
        field_simp [hzeta'.ne']
      have hunitWrap : 3 ≤
          1 / (u * v') + r / (u * v') + r / v' +
            r * s / v' + r * s := by
        have hid :
            1 / (u * v') + r / (u * v') + r / v' +
                r * s / v' + r * s = q4 + zeta' * C := by
          rw [← hv'id]
          dsimp [q4, C]
          field_simp [hu.ne', hv'.ne'] <;> ring
        rw [hid]
        dsimp [zeta']
        rw [div_mul_cancel₀ (3 - q4) hC.ne']
        linarith
      have hnew := p012_unit_floor_gt hr hs ht hu hv' hunitWrap
      have hslope : 1 / (t * u) < rho4 * C := by
        have hq4C : q4 < C := by
          dsimp [q4, C]
          have h1 : 0 < 1 / u := by positivity
          have h2 : 0 < r / u := by positivity
          linarith [hr]
        calc
          1 / (t * u) = L4 := rfl
          _ = rho4 * q4 := by
            dsimp [rho4]
            exact (div_mul_cancel₀ L4 hq4.ne').symm
          _ < rho4 * C := mul_lt_mul_of_pos_left hq4C hrho4
      have hdeficit : 3 - F0 = C * (zeta' - zeta) := by
        rw [hFaff]
        dsimp [zeta']
        field_simp [hC.ne'] <;> ring
      have hcompare :
          R0 + (1 / (t * u)) * (zeta' - zeta) ≤
            R0 + rho4 * (3 - F0) := by
        rw [hdeficit]
        have := mul_le_mul_of_nonneg_right hslope.le (sub_nonneg.mpr hzz'.le)
        nlinarith
      have hRnew :
          s * t +
            (r * s * t + 1 / s + 1 / (s * t * u)) +
            (t * u + u / s + 1 / (s * t)) +
            (s * t * u + u + 1 / (t * u * v')) +
            1 / (t * u) =
          R0 + (1 / (t * u)) * (zeta' - zeta) := by
        have hnewRecip : 1 / (t * u * v') = (1 / (t * u)) * zeta' := by
          rw [← hv'id]
          field_simp [ht.ne', hu.ne', hv'.ne'] <;> ring
        rw [hnewRecip]
        dsimp [R0, L0, L1, L2, L3, L4, zeta]
        field_simp [ht.ne', hu.ne', hv.ne'] <;> ring
      rw [hRnew] at hnew
      dsimp [R0, L0, L1, L2, L3, L4] at hcost hcompare ⊢
      nlinarith

/-! ## Public division-free scalar API -/

/-- Five adjacent determinant floors and the strengthened wrap force
normalized hull area above `25/2`. -/
theorem hullSixThreeThree_p012_scalar
    {a b c d e f g1 g2 g3 g4 g5 A B C D E F H : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hg1 : 0 < g1) (hg2 : 0 < g2) (hg3 : 0 < g3)
    (hg4 : 0 < g4) (hg5 : 0 < g5)
    (h1 : 1 ≤ a * d * g1)
    (h2 : 1 ≤ b * d * g2)
    (h3 : 1 ≤ b * e * g3)
    (h4 : 1 ≤ c * e * g4)
    (h5 : 1 ≤ c * f * g5)
    (hA : a * b * (g1 + g2) ≤ A)
    (hB : b * c * (g3 + g4) ≤ B)
    (hC : c * d * (g2 + g3 + g4) ≤ C)
    (hD : d * e * (g2 + g3) ≤ D)
    (hE : e * f * (g4 + g5) ≤ E)
    (hF : a * f * (g1 + g2 + g3 + g4 + g5) ≤ F)
    (hwrap : 3 ≤ a * f * (g1 + g2 + g3 + g4 + g5))
    (hH : A + B + C + D + E + F ≤ H) :
    25 / 2 < H := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hf0 : 0 < f := lt_of_lt_of_le zero_lt_one hf
  let r := a / b
  let s := b / c
  let t := c / d
  let u := d / e
  let v := e / f
  let x0 := a * d * g1
  let x1 := b * d * g2
  let x2 := b * e * g3
  let x3 := c * e * g4
  let x4 := c * f * g5
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hwrap' : 3 ≤
      (1 / (u * v)) * x0 + (r / (u * v)) * x1 +
      (r / v) * x2 + (r * s / v) * x3 + (r * s) * x4 := by
    have hid :
        (1 / (u * v)) * x0 + (r / (u * v)) * x1 +
            (r / v) * x2 + (r * s / v) * x3 + (r * s) * x4 =
          a * f * (g1 + g2 + g3 + g4 + g5) := by
      dsimp [r, s, t, u, v, x0, x1, x2, x3, x4]
      field_simp [ha0.ne', hb0.ne', hc0.ne', hd0.ne', he0.ne', hf0.ne']
      <;> ring
    rw [hid]
    exact hwrap
  have hratio := p012_ratio_core hr hs ht hu hv
    (by simpa [x0] using h1) (by simpa [x1] using h2)
    (by simpa [x2] using h3) (by simpa [x3] using h4)
    (by simpa [x4] using h5) hwrap'
  have hRidentity :
      (s * t) * x0 +
        (r * s * t + 1 / s + 1 / (s * t * u)) * x1 +
        (t * u + u / s + 1 / (s * t)) * x2 +
        (s * t * u + u + 1 / (t * u * v)) * x3 +
        (1 / (t * u)) * x4 =
      a * b * (g1 + g2) + b * c * (g3 + g4) +
        c * d * (g2 + g3 + g4) + d * e * (g2 + g3) +
        e * f * (g4 + g5) := by
    dsimp [r, s, t, u, v, x0, x1, x2, x3, x4]
    field_simp [ha0.ne', hb0.ne', hc0.ne', hd0.ne', he0.ne', hf0.ne']
    <;> ring
  rw [hRidentity] at hratio
  nlinarith

end Heilbronn8
