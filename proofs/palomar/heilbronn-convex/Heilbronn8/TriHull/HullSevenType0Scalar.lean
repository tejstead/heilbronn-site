import Heilbronn8.TriHull.HullSevenType1Scalar

/-!
# Compact scalar closure for the c-positive hull-seven type 0 chamber

The type 0 sign packet has

```text
c=d15, h=d16, G=-d06, n=d05, l=d04, m=d26,
L=d14, R=d25.
```

The four endpoint rows used below are

```text
L*R=A*D+c*q
l*c=a*D+n*L
c*m=A*z+h*R
a*z=n*h+G*c.
```

Together with the two endpoint caps they give a pair of reduced endpoint
inequalities.  The final scalar argument is rational and uses only those two
inequalities and the interval part of the endpoint high point.
-/

namespace Heilbronn8.TriHull

set_option maxHeartbeats 800000

/-! ## Scalar closer -/

/-- The exact reduced payload used by the type 0 scalar proof. -/
structure HullSevenType0ScalarData (H : ℝ) where
  a : ℝ
  z : ℝ
  s : ℝ
  u : ℝ
  r : ℝ
  a_ge : 1 ≤ a
  z_ge : 1 ≤ z
  s_pos : 0 < s
  u_pos : 0 < u
  r_gt : (107 : ℝ) / 50 < r
  interval : s + u ≤ r * s * u
  left_endpoint :
    (a * z - 1) * (a + s) ≥
      (s + 1) + a * (1 + (r + 1) / (u + 1))
  right_endpoint :
    (a * z - 1) * (z + u) ≥
      (u + 1) + z * (1 + (r + 1) / (s + 1))
  area : a + z + s + u + r + 5 ≤ H

/-- The reduced type 0 inequalities force the required strict total. -/
theorem hullSevenType0_reduced_gt
    {H : ℝ} (X : HullSevenType0ScalarData H) :
    (15 : ℝ) / 2 < X.a + X.z + X.s + X.u + X.r := by
  let x := X.a + X.z
  let y := X.s + X.u
  let k := X.a * X.z - 2
  let P := X.a / (X.u + 1)
  let Q := X.z / (X.s + 1)
  let rho := P + Q
  have ha0 : 0 < X.a := lt_of_lt_of_le (by norm_num) X.a_ge
  have hz0 : 0 < X.z := lt_of_lt_of_le (by norm_num) X.z_ge
  have hs0 : 0 < X.s := X.s_pos
  have hu0 : 0 < X.u := X.u_pos
  have hr0 : 0 < X.r := lt_trans (by norm_num) X.r_gt
  have hrTwo : 2 < X.r := lt_trans (by norm_num) X.r_gt
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hsu0 : 0 < X.s * X.u := mul_pos hs0 hu0
  have hsuAmgm : 4 * (X.s * X.u) ≤ y ^ 2 := by
    dsimp [y]
    nlinarith [sq_nonneg (X.s - X.u)]
  have hintervalScaled := mul_le_mul_of_nonneg_right X.interval hy0.le
  have hry : 4 ≤ X.r * y := by
    apply (mul_le_mul_iff_of_pos_left hsu0).mp
    calc
      (X.s * X.u) * 4 = 4 * (X.s * X.u) := by ring
      _ ≤ y ^ 2 := hsuAmgm
      _ ≤ (X.r * X.s * X.u) * y := by
        simpa [pow_two, y] using hintervalScaled
      _ = (X.s * X.u) * (X.r * y) := by ring
  have hrySum : 4 < X.r + y := by
    by_contra hnot
    have hsum : X.r + y ≤ 4 := le_of_not_gt hnot
    have hm := mul_le_mul_of_nonneg_left hsum hr0.le
    have hsquare : 0 < (X.r - 2) ^ 2 := sq_pos_of_pos (sub_pos.mpr hrTwo)
    nlinarith [hry, hm]
  by_contra hnot
  have htotal : x + y + X.r ≤ (15 : ℝ) / 2 := by
    simpa [x, y, add_assoc, add_left_comm, add_comm] using le_of_not_gt hnot
  have hxUpper : x < (7 : ℝ) / 2 := by linarith
  have hazAmgm : 4 * (X.a * X.z) ≤ x ^ 2 := by
    dsimp [x]
    nlinarith [sq_nonneg (X.a - X.z)]
  have hxUpperProduct :
      0 < ((7 : ℝ) / 2 - x) * ((7 : ℝ) / 2 + x) := by
    exact mul_pos (sub_pos.mpr hxUpper) (by positivity)
  have hazUpper : X.a * X.z < (49 : ℝ) / 16 := by
    nlinarith [hazAmgm, hxUpperProduct]
  have hleft :
      1 + X.a * (X.r + 1) / (X.u + 1) ≤
        k * (X.a + X.s) := by
    have h := X.left_endpoint
    have hlhs :
        (X.s + 1) + X.a * (1 + (X.r + 1) / (X.u + 1)) =
          (1 + X.a * (X.r + 1) / (X.u + 1)) + (X.a + X.s) := by
      ring
    have hrhs :
        (X.a * X.z - 1) * (X.a + X.s) =
          (X.a * X.z - 2) * (X.a + X.s) + (X.a + X.s) := by
      ring
    rw [hlhs, hrhs] at h
    dsimp [k]
    linarith
  have hright :
      1 + X.z * (X.r + 1) / (X.s + 1) ≤
        k * (X.z + X.u) := by
    have h := X.right_endpoint
    have hlhs :
        (X.u + 1) + X.z * (1 + (X.r + 1) / (X.s + 1)) =
          (1 + X.z * (X.r + 1) / (X.s + 1)) + (X.z + X.u) := by
      ring
    have hrhs :
        (X.a * X.z - 1) * (X.z + X.u) =
          (X.a * X.z - 2) * (X.z + X.u) + (X.z + X.u) := by
      ring
    rw [hlhs, hrhs] at h
    dsimp [k]
    linarith
  have hendpoint : 2 + (X.r + 1) * rho ≤ k * (x + y) := by
    calc
      2 + (X.r + 1) * rho =
          (1 + X.a * (X.r + 1) / (X.u + 1)) +
            (1 + X.z * (X.r + 1) / (X.s + 1)) := by
              dsimp [rho, P, Q]
              ring
      _ ≤ k * (X.a + X.s) + k * (X.z + X.u) :=
        add_le_add hleft hright
      _ = k * (x + y) := by
        dsimp [x, y]
        ring
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hrho0 : 0 < rho := by dsimp [rho]; positivity
  have hxy0 : 0 < x + y := add_pos hx0 hy0
  have hk0 : 0 < k := by
    by_contra hnot
    have hkNonpos : k ≤ 0 := le_of_not_gt hnot
    have hm := mul_nonpos_of_nonpos_of_nonneg hkNonpos hxy0.le
    have hrhs : 0 < 2 + (X.r + 1) * rho := by positivity
    linarith
  have hazLower : 2 < X.a * X.z := by
    dsimp [k] at hk0
    linarith
  have hxLower : (14 : ℝ) / 5 < x := by
    by_contra hnot
    have hxLe : x ≤ (14 : ℝ) / 5 := le_of_not_gt hnot
    have hfactor :
        0 ≤ ((14 : ℝ) / 5 - x) * ((14 : ℝ) / 5 + x) :=
      mul_nonneg (sub_nonneg.mpr hxLe) (by positivity)
    nlinarith [hazAmgm, hfactor]
  have hyUpper : y < (64 : ℝ) / 25 := by
    linarith [X.r_gt]
  let M := (X.s + 1) * (X.u + 1)
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hMAmgm : 4 * M ≤ (y + 2) ^ 2 := by
    dsimp [M, y]
    nlinarith [sq_nonneg (X.s - X.u)]
  have hyShift : y + 2 < (114 : ℝ) / 25 := by linarith
  have hyShiftFactor :
      0 < ((114 : ℝ) / 25 - (y + 2)) *
        ((114 : ℝ) / 25 + (y + 2)) := by
    exact mul_pos (sub_pos.mpr hyShift) (by positivity)
  have hMSquare : (y + 2) ^ 2 < 21 := by
    nlinarith [hyShiftFactor]
  have hMUpper : M < (21 : ℝ) / 4 := by
    nlinarith [hMAmgm, hMSquare]
  have hPQIdentity : P * Q = (X.a * X.z) / M := by
    dsimp [P, Q, M]
    field_simp [ne_of_gt (by positivity : 0 < X.s + 1),
      ne_of_gt (by positivity : 0 < X.u + 1)]
  have hPQ : (8 : ℝ) / 21 < P * Q := by
    rw [hPQIdentity]
    apply (lt_div_iff₀ hM0).2
    have hscaled : ((8 : ℝ) / 21) * M < 2 := by
      nlinarith [hMUpper]
    linarith
  have hrhoSquare : 4 * (P * Q) ≤ rho ^ 2 := by
    dsimp [rho]
    nlinarith [sq_nonneg (P - Q)]
  have hrho : (6 : ℝ) / 5 < rho := by
    by_contra hnot
    have hrhoLe : rho ≤ (6 : ℝ) / 5 := le_of_not_gt hnot
    have hfactor :
        0 ≤ ((6 : ℝ) / 5 - rho) * ((6 : ℝ) / 5 + rho) :=
      mul_nonneg (sub_nonneg.mpr hrhoLe) (by positivity)
    nlinarith [hPQ, hrhoSquare, hfactor]
  have hkUpper : k < (17 : ℝ) / 16 := by
    dsimp [k]
    linarith
  have hxyUpper : x + y < (134 : ℝ) / 25 := by
    linarith [X.r_gt]
  have hleftFinal : k * (x + y) < (1139 : ℝ) / 200 := by
    calc
      k * (x + y) < ((17 : ℝ) / 16) * (x + y) :=
        mul_lt_mul_of_pos_right hkUpper hxy0
      _ < ((17 : ℝ) / 16) * ((134 : ℝ) / 25) :=
        mul_lt_mul_of_pos_left hxyUpper (by norm_num)
      _ = (1139 : ℝ) / 200 := by norm_num
  have hq : (157 : ℝ) / 50 < X.r + 1 := by linarith [X.r_gt]
  have hqR :
      ((157 : ℝ) / 50) * ((6 : ℝ) / 5) <
        (X.r + 1) * rho :=
    mul_lt_mul hq hrho.le (by norm_num) (by linarith [hq])
  have hrightFinal : (721 : ℝ) / 125 < 2 + (X.r + 1) * rho := by
    nlinarith [hqR]
  have hgap : (1139 : ℝ) / 200 < (721 : ℝ) / 125 := by norm_num
  linarith

/-- The compact scalar type 0 area bound. -/
theorem hullSevenType0_area_gt
    {H : ℝ} (X : HullSevenType0ScalarData H) : (25 : ℝ) / 2 < H := by
  have hmain := hullSevenType0_reduced_gt X
  linarith [X.area]

/-! ## Determinant and cap adapter -/

/-- Exact determinant, floor, ear, and cap packet for the type 0 chamber. -/
structure HullSevenType0ChordInput (H : ℝ) where
  a : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  z : ℝ
  G : ℝ
  p : ℝ
  q : ℝ
  rChord : ℝ
  L : ℝ
  R : ℝ
  c : ℝ
  l : ℝ
  m : ℝ
  n : ℝ
  h : ℝ
  a_ge : 1 ≤ a
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  C_ge : 1 ≤ C
  D_ge : 1 ≤ D
  z_ge : 1 ≤ z
  G_ge : 1 ≤ G
  p_ge : 1 ≤ p
  q_ge : 1 ≤ q
  rChord_ge : 1 ≤ rChord
  L_ge : 1 ≤ L
  R_ge : 1 ≤ R
  c_ge : 1 ≤ c
  l_ge : 1 ≤ l
  m_ge : 1 ≤ m
  n_ge : 1 ≤ n
  h_ge : 1 ≤ h
  p_ear : p ≤ A + B - 1
  q_ear : q ≤ B + C - 1
  r_ear : rChord ≤ C + D - 1
  plucker_L : B * L = q * p - A * C
  plucker_R : C * R = q * rChord - D * B
  left_cap : A * l + a * q ≤ L * (a + A - 1)
  right_cap : D * m + z * q ≤ R * (z + D - 1)
  plucker_central : L * R = A * D + c * q
  plucker_leftFar : l * c = a * D + n * L
  plucker_rightFar : c * m = A * z + h * R
  plucker_endpoint : a * z = n * h + G * c
  area : a + A + B + C + D + z + G ≤ H

/-- Forget everything except the endpoint high-point packet. -/
def HullSevenType0ChordInput.toEndpointHighPointInput
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    HullSevenEndpointHighPointInput where
  a0 := X.a
  A := X.A
  B := X.B
  C := X.C
  D := X.D
  a5 := X.z
  p := X.p
  q := X.q
  r := X.rChord
  L := X.L
  R := X.R
  l := X.l
  m := X.m
  a0_ge := X.a_ge
  A_ge := X.A_ge
  B_ge := X.B_ge
  C_ge := X.C_ge
  D_ge := X.D_ge
  a5_ge := X.z_ge
  p_ge := X.p_ge
  q_ge := X.q_ge
  r_ge := X.rChord_ge
  L_ge := X.L_ge
  R_ge := X.R_ge
  l_ge := X.l_ge
  m_ge := X.m_ge
  p_ear := X.p_ear
  q_ear := X.q_ear
  r_ear := X.r_ear
  L_rec := X.plucker_L
  R_rec := X.plucker_R
  left_endpoint := X.left_cap
  right_endpoint := X.right_cap

/-- A recurrence, its ear cap, and its endpoint cap force the endpoint chord
lower bound used by the type 0 cancellation. -/
private lemma hullSevenType0_endpoint_lower
    {a A B C p q L l : ℝ}
    (ha : 1 ≤ a) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hpEar : p ≤ A + B - 1)
    (hrec : B * L = q * p - A * C)
    (hcap : A * l + a * q ≤ L * (a + A - 1)) :
    1 + q / A ≤ L := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hupper : B * L ≤ q * (A + B - 1) - A * C := by
    have hm := mul_le_mul_of_nonneg_left hpEar hq0.le
    nlinarith [hrec]
  have hAl : A ≤ A * l := by
    nlinarith [mul_nonneg (le_trans (by norm_num) hA)
      (sub_nonneg.mpr hl)]
  have horiginal : A + a * q ≤ L * (a + A - 1) :=
    le_trans (by linarith) hcap
  have hear : 0 ≤ (L - q) + L * (A - 1) - A := by
    by_contra hnot
    have hfail : (L - q) + L * (A - 1) - A < 0 := lt_of_not_ge hnot
    have horiginal' :
        0 ≤ a * (L - q) + L * (A - 1) - A := by
      nlinarith [horiginal]
    have hsplit :
        a * (L - q) + L * (A - 1) - A =
          ((L - q) + L * (A - 1) - A) + (a - 1) * (L - q) := by
      ring
    have hprod : 0 < (a - 1) * (L - q) := by
      rw [hsplit] at horiginal'
      linarith
    have hLq : q < L := by
      rcases (mul_pos_iff.mp hprod) with hpos | hneg
      · exact sub_pos.mp hpos.2
      · exfalso
        linarith [ha, hneg.1]
    have hqB : q * B < L * B := mul_lt_mul_of_pos_right hLq hB0
    have hbig : A * C < q * (A - 1) := by
      nlinarith [hqB, hupper]
    have hAC : A ≤ A * C := by
      nlinarith [mul_nonneg (le_trans (by norm_num) hA)
        (sub_nonneg.mpr hC)]
    have hqA : q * A < L * A := mul_lt_mul_of_pos_right hLq hA0
    have hsmall : q * (A - 1) < A := by
      nlinarith [hqA, hfail]
    linarith
  have hdiv : q / A ≤ L - 1 := by
    apply (div_le_iff₀ hA0).2
    nlinarith [hear]
  linarith

/-- The endpoint packet and the positive central row produce ThresholdData. -/
private theorem HullSevenType0ChordInput.toThresholdData
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    HullSevenType1ThresholdData X.A X.D X.q := by
  let Y := X.toEndpointHighPointInput
  let P := hullSeven_endpointHighPoint Y
  have ht : 0 < P.t := P.t_pos
  have hw : 0 < P.w := P.w_pos
  have hAgt : 1 < X.A := by
    by_contra hnot
    have hA : X.A - 1 ≤ 0 := by linarith
    have hm : (X.A - 1) * P.t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hA ht.le
    have hout : 1 ≤ (X.A - 1) * P.t := by
      simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using
        P.left_outer
    linarith
  have hDgt : 1 < X.D := by
    by_contra hnot
    have hD : X.D - 1 ≤ 0 := by linarith
    have hm : (X.D - 1) * P.w ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hD hw.le
    have hout : 1 ≤ (X.D - 1) * P.w := by
      simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using
        P.right_outer
    linarith
  have hs : 0 < X.A - 1 := sub_pos.mpr hAgt
  have hu : 0 < X.D - 1 := sub_pos.mpr hDgt
  have htLower : 1 / (X.A - 1) ≤ P.t := by
    apply (div_le_iff₀ hs).2
    have hout : 1 ≤ (X.A - 1) * P.t := by
      simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using
        P.left_outer
    simpa [mul_comm] using hout
  have hwLower : 1 / (X.D - 1) ≤ P.w := by
    apply (div_le_iff₀ hu).2
    have hout : 1 ≤ (X.D - 1) * P.w := by
      simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using
        P.right_outer
    simpa [mul_comm] using hout
  have hsum : P.t + P.w = X.q - 1 := by
    simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using P.sum_eq
  have hintervalDiv :
      1 / (X.A - 1) + 1 / (X.D - 1) ≤ X.q - 1 := by linarith
  have hinterval :
      (X.A - 1) + (X.D - 1) ≤
        (X.q - 1) * (X.A - 1) * (X.D - 1) := by
    have hsu : 0 < (X.A - 1) * (X.D - 1) := mul_pos hs hu
    have hm := mul_le_mul_of_nonneg_right hintervalDiv hsu.le
    have hid :
        (1 / (X.A - 1) + 1 / (X.D - 1)) *
            ((X.A - 1) * (X.D - 1)) =
          (X.A - 1) + (X.D - 1) := by
      field_simp [hs.ne', hu.ne']
      ring
    rw [hid] at hm
    simpa [mul_assoc] using hm
  have hq0 : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hKLR : X.A * X.D + X.q ≤ X.L * X.R := by
    have hcq := mul_le_mul_of_nonneg_right X.c_ge hq0.le
    nlinarith [X.plucker_central]
  have hleft : X.L * (1 + P.t) ≤ P.t * (X.A + X.q) := by
    simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using
      P.left_scaled
  have hright : X.R * (1 + P.w) ≤ P.w * (X.D + X.q) := by
    simpa [Y, HullSevenType0ChordInput.toEndpointHighPointInput] using
      P.right_scaled
  have hKscaled := mul_le_mul_of_nonneg_right hKLR
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + P.t)
      (by positivity : (0 : ℝ) ≤ 1 + P.w))
  have hsurrogate :
      (X.L * (1 + P.t)) * (X.R * (1 + P.w)) ≤
        (P.t * (X.A + X.q)) * (P.w * (X.D + X.q)) := by
    exact mul_le_mul hleft hright
      (mul_nonneg (le_trans (by norm_num) X.R_ge) (by positivity))
      (mul_nonneg ht.le (by positivity))
  have hKproduct :
      (X.A * X.D + X.q) * ((1 + P.t) * (1 + P.w)) ≤
        P.t * P.w * ((X.A + X.q) * (X.D + X.q)) := by
    calc
      (X.A * X.D + X.q) * ((1 + P.t) * (1 + P.w))
          ≤ (X.L * X.R) * ((1 + P.t) * (1 + P.w)) := hKscaled
      _ = (X.L * (1 + P.t)) * (X.R * (1 + P.w)) := by ring
      _ ≤ (P.t * (X.A + X.q)) * (P.w * (X.D + X.q)) := hsurrogate
      _ = P.t * P.w * ((X.A + X.q) * (X.D + X.q)) := by ring
  have hM :
      (X.A + X.q) * (X.D + X.q) =
        (X.A * X.D + X.q) + X.q * (X.A + X.D + X.q - 1) := by ring
  have hmain :
      (X.A * X.D + X.q) * (1 + P.t + P.w) ≤
        P.t * P.w * X.q * (X.A + X.D + X.q - 1) := by
    nlinarith [hKproduct, hM]
  have htw : 4 * P.t * P.w ≤ (P.t + P.w) ^ 2 := by
    nlinarith [sq_nonneg (P.t - P.w)]
  have hS0 : 0 ≤ X.A + X.D + X.q - 1 := by
    nlinarith [X.A_ge, X.D_ge, X.q_ge]
  have htwScaled := mul_le_mul_of_nonneg_right htw
    (mul_nonneg hq0.le hS0)
  have hmainScaled := mul_le_mul_of_nonneg_left hmain
    (by norm_num : (0 : ℝ) ≤ 4)
  have hqsum : 1 + P.t + P.w = X.q := by linarith [hsum]
  have hPplusScaled :
      4 * (X.A * X.D + X.q) * X.q ≤
        (X.q - 1) ^ 2 * X.q * (X.A + X.D + X.q - 1) := by
    calc
      4 * (X.A * X.D + X.q) * X.q =
          4 * ((X.A * X.D + X.q) * (1 + P.t + P.w)) := by
            rw [hqsum]
            ring
      _ ≤ 4 * (P.t * P.w * X.q * (X.A + X.D + X.q - 1)) :=
        hmainScaled
      _ ≤ (P.t + P.w) ^ 2 * X.q * (X.A + X.D + X.q - 1) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using htwScaled
      _ = (X.q - 1) ^ 2 * X.q * (X.A + X.D + X.q - 1) := by
        rw [hsum]
  have hPplus :
      4 * (X.A * X.D + X.q) ≤
        (X.q - 1) ^ 2 * (X.A + X.D + X.q - 1) := by
    apply (mul_le_mul_iff_of_pos_right hq0).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hPplusScaled
  exact
    { A_gt := hAgt
      D_gt := hDgt
      interval := hinterval
      pplus := hPplus }

/-- Cancellation of the left endpoint cap against the positive central row. -/
theorem HullSevenType0ChordInput.leftEndpointCancel
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    X.A * X.n + X.a * X.R ≤ X.c * (X.a + X.A - 1) := by
  have hc0 : 0 ≤ X.c := le_trans (by norm_num) X.c_ge
  have hm := mul_le_mul_of_nonneg_left X.left_cap hc0
  have hcq : X.c * X.q = X.L * X.R - X.A * X.D := by
    nlinarith [X.plucker_central]
  have hid :
      X.c * (X.A * X.l + X.a * X.q) =
        X.L * (X.A * X.n + X.a * X.R) := by
    calc
      X.c * (X.A * X.l + X.a * X.q) =
          X.A * (X.l * X.c) + X.a * (X.c * X.q) := by ring
      _ = X.A * (X.a * X.D + X.n * X.L) +
          X.a * (X.L * X.R - X.A * X.D) := by
        rw [X.plucker_leftFar, hcq]
      _ = X.L * (X.A * X.n + X.a * X.R) := by ring
  rw [hid] at hm
  have hm' :
      X.L * (X.A * X.n + X.a * X.R) ≤
        X.L * (X.c * (X.a + X.A - 1)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  exact (mul_le_mul_iff_of_pos_left
    (lt_of_lt_of_le (by norm_num) X.L_ge)).mp hm'

/-- Cancellation of the right endpoint cap against the positive central row. -/
theorem HullSevenType0ChordInput.rightEndpointCancel
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    X.D * X.h + X.z * X.L ≤ X.c * (X.z + X.D - 1) := by
  have hc0 : 0 ≤ X.c := le_trans (by norm_num) X.c_ge
  have hm := mul_le_mul_of_nonneg_left X.right_cap hc0
  have hcq : X.c * X.q = X.L * X.R - X.A * X.D := by
    nlinarith [X.plucker_central]
  have hid :
      X.c * (X.D * X.m + X.z * X.q) =
        X.R * (X.D * X.h + X.z * X.L) := by
    calc
      X.c * (X.D * X.m + X.z * X.q) =
          X.D * (X.c * X.m) + X.z * (X.c * X.q) := by ring
      _ = X.D * (X.A * X.z + X.h * X.R) +
          X.z * (X.L * X.R - X.A * X.D) := by
        rw [X.plucker_rightFar, hcq]
      _ = X.R * (X.D * X.h + X.z * X.L) := by ring
  rw [hid] at hm
  have hm' :
      X.R * (X.D * X.h + X.z * X.L) ≤
        X.R * (X.c * (X.z + X.D - 1)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  exact (mul_le_mul_iff_of_pos_left
    (lt_of_lt_of_le (by norm_num) X.R_ge)).mp hm'

/-- The endpoint identity bounds the central chord magnitude by `a*z-1`. -/
theorem HullSevenType0ChordInput.c_le
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    X.c ≤ X.a * X.z - 1 := by
  have hnh : 1 ≤ X.n * X.h := by
    calc
      1 ≤ X.h := X.h_ge
      _ ≤ X.n * X.h := by
        simpa using mul_le_mul_of_nonneg_right X.n_ge
          (le_trans (by norm_num) X.h_ge)
  have hc0 : 0 ≤ X.c := le_trans (by norm_num) X.c_ge
  have hGc : X.c ≤ X.G * X.c := by
    have hm := mul_le_mul_of_nonneg_right X.G_ge hc0
    simpa using hm
  nlinarith [X.plucker_endpoint]

/-- The determinant and cap packet supplies the reduced left endpoint. -/
theorem HullSevenType0ChordInput.leftEndpointReduced
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    X.A + X.a * (1 + X.q / X.D) ≤
      (X.a * X.z - 1) * (X.a + X.A - 1) := by
  have hfactor : 0 ≤ X.a + X.A - 1 := by
    nlinarith [X.a_ge, X.A_ge]
  have hcScaled := mul_le_mul_of_nonneg_right X.c_le hfactor
  have hAn : X.A ≤ X.A * X.n := by
    nlinarith [mul_nonneg (le_trans (by norm_num) X.A_ge)
      (sub_nonneg.mpr X.n_ge)]
  have hRlower : 1 + X.q / X.D ≤ X.R :=
    hullSevenType0_endpoint_lower X.z_ge X.D_ge X.C_ge X.B_ge X.q_ge
      X.m_ge (by linarith [X.r_ear]) X.plucker_R X.right_cap
  have haR := mul_le_mul_of_nonneg_left hRlower
    (le_trans (by norm_num) X.a_ge)
  nlinarith [X.leftEndpointCancel, hcScaled, hAn, haR]

/-- The determinant and cap packet supplies the reduced right endpoint. -/
theorem HullSevenType0ChordInput.rightEndpointReduced
    {H : ℝ} (X : HullSevenType0ChordInput H) :
    X.D + X.z * (1 + X.q / X.A) ≤
      (X.a * X.z - 1) * (X.z + X.D - 1) := by
  have hfactor : 0 ≤ X.z + X.D - 1 := by
    nlinarith [X.z_ge, X.D_ge]
  have hcScaled := mul_le_mul_of_nonneg_right X.c_le hfactor
  have hDh : X.D ≤ X.D * X.h := by
    nlinarith [mul_nonneg (le_trans (by norm_num) X.D_ge)
      (sub_nonneg.mpr X.h_ge)]
  have hLlower : 1 + X.q / X.A ≤ X.L :=
    hullSevenType0_endpoint_lower X.a_ge X.A_ge X.B_ge X.C_ge X.q_ge
      X.l_ge X.p_ear X.plucker_L X.left_cap
  have hzL := mul_le_mul_of_nonneg_left hLlower
    (le_trans (by norm_num) X.z_ge)
  nlinarith [X.rightEndpointCancel, hcScaled, hDh, hzL]

/-- The complete determinant packet supplies the scalar payload. -/
noncomputable def HullSevenType0ChordInput.toScalarData
    {H : ℝ} (X : HullSevenType0ChordInput H) : HullSevenType0ScalarData H :=
  let T := X.toThresholdData
  { a := X.a
    z := X.z
    s := X.A - 1
    u := X.D - 1
    r := X.q - 1
    a_ge := X.a_ge
    z_ge := X.z_ge
    s_pos := sub_pos.mpr T.A_gt
    u_pos := sub_pos.mpr T.D_gt
    r_gt := by
      have hq := hullSevenType1_q_gt_157_div_50 T
      linarith
    interval := by
      simpa [mul_assoc] using T.interval
    left_endpoint := by
      simpa [sub_eq_add_neg, add_assoc] using X.leftEndpointReduced
    right_endpoint := by
      simpa [sub_eq_add_neg, add_assoc] using X.rightEndpointReduced
    area := by
      nlinarith [X.area, X.G_ge, X.q_ear] }

/-- End-to-end strict area bound from the type 0 determinant packet. -/
theorem hullSevenType0_area_gt_of_chord
    {H : ℝ} (X : HullSevenType0ChordInput H) : (25 : ℝ) / 2 < H :=
  hullSevenType0_area_gt X.toScalarData

/-- Direct sharp-constant consequence for the type 0 dispatcher. -/
theorem hullSeven_v8_of_type0_scalar
    {H : ℝ} (X : HullSevenType0ChordInput H) : 1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 < H := hullSevenType0_area_gt_of_chord X
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

end Heilbronn8.TriHull
