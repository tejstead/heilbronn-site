import Mathlib

/-!
# Scalar core of the convex-octagon ear bound

This module isolates the two algebraic moves in the sharp elementary proof.
It deliberately has no generated data and no geometric adapter.

For a strict convex octagon, retain the four even vertices and call the
doubled corner areas of their central quadrilateral `q i`.  If the doubled
areas of the four intervening cap ears are `c i`, put

```text
d i = q i - q (i-1),
N i u = q i * q (i+1) + u * d i.
```

The opposite-sum identity for a quadrilateral says

```text
q i + q (i+2) = q (i-1) + q (i+1),
```

and therefore `d i < q i` and `d i < q (i+1)`.  The first theorem below
shows, without differentiation or division, that lowering one cap from
`u >= m` to the ear floor `m` can only increase the relevant product ratio.

After all four caps have been lowered, write

```text
q0 = t+a, q2 = t-a, q1 = t+b, q3 = t-b.
```

The second theorem is the positive polynomial identity controlling each
opposite pair.  It is used once with `(alpha,beta)=(a,b)` and once with
`(alpha,beta)=(b,-a)`; the latter is why the odd-pair square is `(a-b)^2`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- Positivity of a cyclic numerator is preserved when its cap is lowered. -/
theorem octagon_lowered_numerator_pos
    {m q qnext d u : ℝ}
    (hm : 0 < m) (hq : 0 < q) (hqnext : 0 < qnext)
    (hu : m ≤ u) (hNu : 0 < q * qnext + u * d) :
    0 < q * qnext + m * d := by
  by_cases hd : 0 ≤ d
  · exact add_pos_of_pos_of_nonneg (mul_pos hq hqnext)
      (mul_nonneg hm.le hd)
  · have hd' : d < 0 := lt_of_not_ge hd
    have hstep : (u - m) * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu) hd'.le
    nlinarith

/--
Division-free one-coordinate cap-lowering inequality.

`q` and `qnext` are adjacent central-corner areas, `d` is their cyclic
difference numerator, and `left`, `right` are the neighboring cap areas.
The two strict bounds on `d` are precisely what follows from positivity and
the opposite-sum identity of the central quadrilateral.
-/
theorem octagon_cap_lower_cross
    {m q qnext d left right u : ℝ}
    (hm : 0 < m) (hq : 0 < q) (hqnext : 0 < qnext)
    (hu : m ≤ u) (hleft : m ≤ left) (hright : m ≤ right)
    (hdq : d < q) (hdqnext : d < qnext)
    (hNu : 0 < q * qnext + u * d) :
    (q * qnext + u * d) ^ 2 *
          (m * q + left * m) * (m * qnext + right * m) ≤
      (q * qnext + m * d) ^ 2 *
          (m * q + left * u) * (m * qnext + right * u) := by
  let Nu : ℝ := q * qnext + u * d
  let Nm : ℝ := q * qnext + m * d
  let Dlu : ℝ := m * q + left * u
  let Dlm : ℝ := m * q + left * m
  let Dru : ℝ := m * qnext + right * u
  let Drm : ℝ := m * qnext + right * m
  have hmdLeft : m * d ≤ left * qnext := by
    have hmd : m * d < m * qnext :=
      mul_lt_mul_of_pos_left hdqnext hm
    have hmleft : m * qnext ≤ left * qnext :=
      mul_le_mul_of_nonneg_right hleft hqnext.le
    exact le_trans hmd.le hmleft
  have hmdRight : m * d ≤ right * q := by
    have hmd : m * d < m * q := mul_lt_mul_of_pos_left hdq hm
    have hmright : m * q ≤ right * q :=
      mul_le_mul_of_nonneg_right hright hq.le
    exact le_trans hmd.le hmright
  have hNm : 0 < Nm := by
    by_cases hd : 0 ≤ d
    · dsimp [Nm]
      exact add_pos_of_pos_of_nonneg (mul_pos hq hqnext)
        (mul_nonneg hm.le hd)
    · have hd' : d < 0 := lt_of_not_ge hd
      have hstep : (u - m) * d ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu) hd'.le
      have hid :
          (q * qnext + u * d) - (q * qnext + m * d) = (u - m) * d := by
        ring
      change 0 < q * qnext + m * d
      nlinarith
  have hDlm : 0 < Dlm := by
    dsimp [Dlm]
    have hmq : 0 < m * q := mul_pos hm hq
    have hlm : 0 ≤ left * m :=
      mul_nonneg (le_trans hm.le hleft) hm.le
    linarith
  have hDlu : 0 < Dlu := by
    dsimp [Dlu]
    have hmq : 0 < m * q := mul_pos hm hq
    have hlu : 0 ≤ left * u :=
      mul_nonneg (le_trans hm.le hleft) (le_trans hm.le hu)
    linarith
  have hDrm : 0 < Drm := by
    dsimp [Drm]
    have hmq : 0 < m * qnext := mul_pos hm hqnext
    have hrm : 0 ≤ right * m :=
      mul_nonneg (le_trans hm.le hright) hm.le
    linarith
  have hDru : 0 < Dru := by
    dsimp [Dru]
    have hmq : 0 < m * qnext := mul_pos hm hqnext
    have hru : 0 ≤ right * u :=
      mul_nonneg (le_trans hm.le hright) (le_trans hm.le hu)
    linarith
  have hleftCross : Nu * Dlm ≤ Nm * Dlu := by
    have hid : Nm * Dlu - Nu * Dlm =
        (u - m) * q * (left * qnext - m * d) := by
      dsimp [Nu, Nm, Dlu, Dlm]
      ring
    have hnonneg :
        0 ≤ (u - m) * q * (left * qnext - m * d) :=
      mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hu) hq.le)
        (sub_nonneg.mpr hmdLeft)
    linarith
  have hrightCross : Nu * Drm ≤ Nm * Dru := by
    have hid : Nm * Dru - Nu * Drm =
        (u - m) * qnext * (right * q - m * d) := by
      dsimp [Nu, Nm, Dru, Drm]
      ring
    have hnonneg :
        0 ≤ (u - m) * qnext * (right * q - m * d) :=
      mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hu) hqnext.le)
        (sub_nonneg.mpr hmdRight)
    linarith
  have hmul := mul_le_mul hleftCross hrightCross
    (mul_nonneg hNu.le hDrm.le) (mul_nonneg hNm.le hDlu.le)
  dsimp [Nu, Nm, Dlu, Dlm, Dru, Drm] at hmul ⊢
  nlinarith

/--
Ratio form of `octagon_cap_lower_cross`, with arbitrary unchanged numerator
and denominator factors.  This is the form used four times in succession in
the octagon scalar closure.
-/
theorem octagon_cap_lower_ratio
    {m q qnext d left right u commonN commonD : ℝ}
    (hm : 0 < m) (hq : 0 < q) (hqnext : 0 < qnext)
    (hu : m ≤ u) (hleft : m ≤ left) (hright : m ≤ right)
    (hdq : d < q) (hdqnext : d < qnext)
    (hNu : 0 < q * qnext + u * d) (hcommonD : 0 < commonD) :
    ((q * qnext + u * d) * commonN) ^ 2 /
          ((m * q + left * u) * (m * qnext + right * u) * commonD) ≤
      ((q * qnext + m * d) * commonN) ^ 2 /
          ((m * q + left * m) * (m * qnext + right * m) * commonD) := by
  have hcross := octagon_cap_lower_cross hm hq hqnext hu hleft hright
    hdq hdqnext hNu
  have hcurrent :
      0 < (m * q + left * u) * (m * qnext + right * u) * commonD := by
    have hleftPos : 0 < m * q + left * u := by
      have : 0 ≤ left * u :=
        mul_nonneg (le_trans hm.le hleft) (le_trans hm.le hu)
      nlinarith [mul_pos hm hq]
    have hrightPos : 0 < m * qnext + right * u := by
      have : 0 ≤ right * u :=
        mul_nonneg (le_trans hm.le hright) (le_trans hm.le hu)
      nlinarith [mul_pos hm hqnext]
    positivity
  have hlowered :
      0 < (m * q + left * m) * (m * qnext + right * m) * commonD := by
    have hleftPos : 0 < m * q + left * m := by
      have : 0 ≤ left * m :=
        mul_nonneg (le_trans hm.le hleft) hm.le
      nlinarith [mul_pos hm hq]
    have hrightPos : 0 < m * qnext + right * m := by
      have : 0 ≤ right * m :=
        mul_nonneg (le_trans hm.le hright) hm.le
      nlinarith [mul_pos hm hqnext]
    positivity
  apply (div_le_div_iff₀ hcurrent hlowered).2
  have hscale : 0 ≤ commonN ^ 2 * commonD :=
    mul_nonneg (sq_nonneg commonN) hcommonD.le
  have hscaled := mul_le_mul_of_nonneg_right hcross hscale
  nlinarith

/--
Positive polynomial identity for one opposite pair after every cap has been
lowered to `m`.

The two rational pair factors have numerators

```text
t^2 + alpha*beta ± (t+m)*(alpha+beta)
```

and common-denominator product `t^2-beta^2`.  This cross-multiplied form is
the one intended for the geometric proof.
-/
theorem octagon_opposite_pair_cross
    {m t alpha beta : ℝ}
    (hm : 0 < m) (ht : 0 < t)
    (hbetaLo : -t < beta) (hbetaHi : beta < t) :
    let plus := t ^ 2 + alpha * beta + (t + m) * (alpha + beta)
    let minus := t ^ 2 + alpha * beta - (t + m) * (alpha + beta)
    plus * minus * (t + m) ^ 2 ≤
      t ^ 2 * ((t + m) ^ 2 - alpha ^ 2) * (t ^ 2 - beta ^ 2) := by
  dsimp
  have htb : 0 ≤ t ^ 2 - beta ^ 2 := by
    have hminus : 0 ≤ t - beta := le_of_lt (sub_pos.mpr hbetaHi)
    have hplus : 0 ≤ t + beta := le_of_lt (by linarith)
    nlinarith [mul_nonneg hminus hplus]
  have hcore :
      0 ≤ (t + m) ^ 2 * (alpha + beta) ^ 2 +
        alpha ^ 2 * (t ^ 2 - beta ^ 2) := by
    positivity
  have hfactor :
      0 ≤ m * (m + 2 * t) *
        ((t + m) ^ 2 * (alpha + beta) ^ 2 +
          alpha ^ 2 * (t ^ 2 - beta ^ 2)) := by
    positivity
  have hid :
      t ^ 2 * ((t + m) ^ 2 - alpha ^ 2) * (t ^ 2 - beta ^ 2) -
          (t ^ 2 + alpha * beta + (t + m) * (alpha + beta)) *
            (t ^ 2 + alpha * beta - (t + m) * (alpha + beta)) *
            (t + m) ^ 2 =
        m * (m + 2 * t) *
          ((t + m) ^ 2 * (alpha + beta) ^ 2 +
            alpha ^ 2 * (t ^ 2 - beta ^ 2)) := by
    ring
  linarith

/-- The even opposite pair uses `(alpha,beta)=(a,b)`. -/
theorem octagon_even_pair_cross
    {m t a b : ℝ}
    (hm : 0 < m) (ht : 0 < t) (hbLo : -t < b) (hbHi : b < t) :
    let plus := t ^ 2 + a * b + (t + m) * (a + b)
    let minus := t ^ 2 + a * b - (t + m) * (a + b)
    plus * minus * (t + m) ^ 2 ≤
      t ^ 2 * ((t + m) ^ 2 - a ^ 2) * (t ^ 2 - b ^ 2) := by
  exact octagon_opposite_pair_cross hm ht hbLo hbHi

/--
The odd opposite pair uses `(alpha,beta)=(b,-a)`, giving the corrected
square `(a-b)^2` after expansion.
-/
theorem octagon_odd_pair_cross
    {m t a b : ℝ}
    (hm : 0 < m) (ht : 0 < t) (haLo : -t < a) (haHi : a < t) :
    let plus := t ^ 2 - a * b + (t + m) * (b - a)
    let minus := t ^ 2 - a * b - (t + m) * (b - a)
    plus * minus * (t + m) ^ 2 ≤
      t ^ 2 * ((t + m) ^ 2 - b ^ 2) * (t ^ 2 - a ^ 2) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using
    (octagon_opposite_pair_cross (m := m) (t := t)
      (alpha := b) (beta := -a) hm ht (by linarith) (by linarith))

/--
The two opposite-pair identities turn the equal-cap product floor into the
sharp scalar inequality `4*m*(t+m) <= t^2`.

The hypothesis is written in the completely cross-multiplied form produced
by the four cap-lowering steps.  `ePlus,eMinus` are the even-pair numerators;
`oPlus,oMinus` are the odd-pair numerators.
-/
theorem octagon_pair_product_forces_sharp
    {m t a b : ℝ}
    (hm : 0 < m) (ht : 0 < t)
    (haLo : -t < a) (haHi : a < t)
    (hbLo : -t < b) (hbHi : b < t)
    (hePlusPos :
      0 < t ^ 2 + a * b + (t + m) * (a + b))
    (heMinusPos :
      0 < t ^ 2 + a * b - (t + m) * (a + b))
    (hoPlusPos :
      0 < t ^ 2 - a * b + (t + m) * (b - a))
    (hoMinusPos :
      0 < t ^ 2 - a * b - (t + m) * (b - a))
    (hmaster :
      256 * m ^ 4 * ((t + m) ^ 2 - a ^ 2) * ((t + m) ^ 2 - b ^ 2) *
          (t ^ 2 - a ^ 2) ^ 2 * (t ^ 2 - b ^ 2) ^ 2 ≤
        ((t ^ 2 + a * b + (t + m) * (a + b)) *
          (t ^ 2 + a * b - (t + m) * (a + b)) *
          (t ^ 2 - a * b + (t + m) * (b - a)) *
          (t ^ 2 - a * b - (t + m) * (b - a))) ^ 2) :
    4 * m * (t + m) ≤ t ^ 2 := by
  let T : ℝ := t + m
  let A : ℝ := T ^ 2 - a ^ 2
  let B : ℝ := T ^ 2 - b ^ 2
  let U : ℝ := t ^ 2 - a ^ 2
  let V : ℝ := t ^ 2 - b ^ 2
  let ePlus : ℝ := t ^ 2 + a * b + T * (a + b)
  let eMinus : ℝ := t ^ 2 + a * b - T * (a + b)
  let oPlus : ℝ := t ^ 2 - a * b + T * (b - a)
  let oMinus : ℝ := t ^ 2 - a * b - T * (b - a)
  have hT : 0 < T := by dsimp [T]; linarith
  have hA : 0 < A := by
    have hfac : A = (T - a) * (T + a) := by dsimp [A]; ring
    rw [hfac]
    exact mul_pos (by dsimp [T]; linarith) (by dsimp [T]; linarith)
  have hB : 0 < B := by
    have hfac : B = (T - b) * (T + b) := by dsimp [B]; ring
    rw [hfac]
    exact mul_pos (by dsimp [T]; linarith) (by dsimp [T]; linarith)
  have hU : 0 < U := by
    have hfac : U = (t - a) * (t + a) := by dsimp [U]; ring
    rw [hfac]
    exact mul_pos (sub_pos.mpr haHi) (by linarith)
  have hV : 0 < V := by
    have hfac : V = (t - b) * (t + b) := by dsimp [V]; ring
    rw [hfac]
    exact mul_pos (sub_pos.mpr hbHi) (by linarith)
  have hePlus : 0 < ePlus := by
    simpa [ePlus, T] using hePlusPos
  have heMinus : 0 < eMinus := by
    simpa [eMinus, T] using heMinusPos
  have hoPlus : 0 < oPlus := by
    simpa [oPlus, T] using hoPlusPos
  have hoMinus : 0 < oMinus := by
    simpa [oMinus, T] using hoMinusPos
  have hEvenRaw := octagon_even_pair_cross (m := m) (t := t)
    (a := a) (b := b) hm ht hbLo hbHi
  have hOddRaw := octagon_odd_pair_cross (m := m) (t := t)
    (a := a) (b := b) hm ht haLo haHi
  have hEven : ePlus * eMinus * T ^ 2 ≤ t ^ 2 * A * V := by
    simpa [T, A, V, ePlus, eMinus] using hEvenRaw
  have hOdd : oPlus * oMinus * T ^ 2 ≤ t ^ 2 * B * U := by
    simpa [T, B, U, oPlus, oMinus] using hOddRaw
  have hpairMulRaw := mul_le_mul hEven hOdd
    (mul_nonneg (mul_nonneg hoPlus.le hoMinus.le) (sq_nonneg T))
    (mul_nonneg (mul_nonneg (sq_nonneg t) hA.le) hV.le)
  have hpair :
      (ePlus * eMinus * oPlus * oMinus) * T ^ 4 ≤
        t ^ 4 * A * B * U * V := by
    calc
      (ePlus * eMinus * oPlus * oMinus) * T ^ 4 =
          (ePlus * eMinus * T ^ 2) * (oPlus * oMinus * T ^ 2) := by ring
      _ ≤ (t ^ 2 * A * V) * (t ^ 2 * B * U) := hpairMulRaw
      _ = t ^ 4 * A * B * U * V := by ring
  have hpairLeft :
      0 ≤ (ePlus * eMinus * oPlus * oMinus) * T ^ 4 := by positivity
  have hpairRight : 0 ≤ t ^ 4 * A * B * U * V := by positivity
  have hpairSqRaw := mul_le_mul hpair hpair hpairLeft hpairRight
  have hpairSq :
      (ePlus * eMinus * oPlus * oMinus) ^ 2 * T ^ 8 ≤
        t ^ 8 * A ^ 2 * B ^ 2 * U ^ 2 * V ^ 2 := by
    calc
      (ePlus * eMinus * oPlus * oMinus) ^ 2 * T ^ 8 =
          ((ePlus * eMinus * oPlus * oMinus) * T ^ 4) *
            ((ePlus * eMinus * oPlus * oMinus) * T ^ 4) := by ring
      _ ≤ (t ^ 4 * A * B * U * V) * (t ^ 4 * A * B * U * V) :=
        hpairSqRaw
      _ = t ^ 8 * A ^ 2 * B ^ 2 * U ^ 2 * V ^ 2 := by ring
  have hmaster' :
      256 * m ^ 4 * A * B * U ^ 2 * V ^ 2 ≤
        (ePlus * eMinus * oPlus * oMinus) ^ 2 := by
    simpa [T, A, B, U, V, ePlus, eMinus, oPlus, oMinus] using hmaster
  have hmasterT := mul_le_mul_of_nonneg_right hmaster' (by positivity : 0 ≤ T ^ 8)
  have hcombined :
      256 * m ^ 4 * A * B * U ^ 2 * V ^ 2 * T ^ 8 ≤
        t ^ 8 * A ^ 2 * B ^ 2 * U ^ 2 * V ^ 2 :=
    le_trans hmasterT hpairSq
  let K : ℝ := A * B * U ^ 2 * V ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hcancelInput : K * (256 * m ^ 4 * T ^ 8) ≤
      K * (t ^ 8 * A * B) := by
    dsimp [K]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hcombined
  have hfirst : 256 * m ^ 4 * T ^ 8 ≤ t ^ 8 * A * B :=
    le_of_mul_le_mul_left hcancelInput hK
  have hAB : A * B ≤ T ^ 4 := by
    have hAle : A ≤ T ^ 2 := by
      dsimp [A]
      exact sub_le_self _ (sq_nonneg a)
    have hBle : B ≤ T ^ 2 := by
      dsimp [B]
      exact sub_le_self _ (sq_nonneg b)
    have hmul := mul_le_mul hAle hBle hB.le (sq_nonneg T)
    calc
      A * B ≤ T ^ 2 * T ^ 2 := hmul
      _ = T ^ 4 := by ring
  have hABscaled : t ^ 8 * A * B ≤ t ^ 8 * T ^ 4 := by
    calc
      t ^ 8 * A * B = t ^ 8 * (A * B) := by ring
      _ ≤ t ^ 8 * T ^ 4 :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
  have hsecond : 256 * m ^ 4 * T ^ 8 ≤ t ^ 8 * T ^ 4 :=
    le_trans hfirst hABscaled
  have hT4 : 0 < T ^ 4 := by positivity
  have hpolyInput : T ^ 4 * (256 * m ^ 4 * T ^ 4) ≤ T ^ 4 * t ^ 8 := by
    convert hsecond using 1 <;> ring
  have hpoly : 256 * m ^ 4 * T ^ 4 ≤ t ^ 8 :=
    le_of_mul_le_mul_left hpolyInput hT4
  by_contra hnot
  have hlt : t ^ 2 < 4 * m * T := lt_of_not_ge hnot
  have hleftPos : 0 < t ^ 2 := sq_pos_of_pos ht
  have hrightPos : 0 < 4 * m * T := by positivity
  have hsq1raw := mul_lt_mul hlt hlt.le hleftPos hrightPos.le
  have hsq1 : (t ^ 2) ^ 2 < (4 * m * T) ^ 2 := by
    simpa only [pow_two] using hsq1raw
  have hsq1Left : 0 < (t ^ 2) ^ 2 := by positivity
  have hsq1Right : 0 < (4 * m * T) ^ 2 := by positivity
  have hsq2raw := mul_lt_mul hsq1 hsq1.le hsq1Left hsq1Right.le
  have hsq2 : t ^ 8 < 256 * m ^ 4 * T ^ 4 := by
    have hleft : ((t ^ 2) ^ 2) * ((t ^ 2) ^ 2) = t ^ 8 := by
      ring
    have hright : ((4 * m * T) ^ 2) * ((4 * m * T) ^ 2) =
        256 * m ^ 4 * T ^ 4 := by
      ring
    rw [hleft, hright] at hsq2raw
    exact hsq2raw
  exact (not_lt_of_ge hpoly) hsq2

/--
Equal-cap endpoint in the original four central-corner variables.

The displayed product inequality is exactly what remains after the four
coordinatewise cap-lowering applications.  The four positivity hypotheses
are inherited while lowering because each affected cyclic factor either
increases, or stays positive throughout the lowering interval.
-/
theorem hullEight_octagon_scalar_of_floor_product
    {m q0 q1 q2 q3 : ℝ}
    (hm : 0 < m)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hq2 : 0 < q2) (hq3 : 0 < q3)
    (hqsum : q0 + q2 = q1 + q3)
    (hN0 : 0 < q0 * q1 + m * (q0 - q3))
    (hN1 : 0 < q1 * q2 + m * (q1 - q0))
    (hN2 : 0 < q2 * q3 + m * (q2 - q1))
    (hN3 : 0 < q3 * q0 + m * (q3 - q2))
    (hproduct :
      256 * m ^ 4 * (q0 + m) * (q1 + m) * (q2 + m) * (q3 + m) *
          (q0 * q1 * q2 * q3) ^ 2 ≤
        ((q0 * q1 + m * (q0 - q3)) *
          (q1 * q2 + m * (q1 - q0)) *
          (q2 * q3 + m * (q2 - q1)) *
          (q3 * q0 + m * (q3 - q2))) ^ 2) :
    17 * m ≤ 2 * (q0 + q2) := by
  let t : ℝ := (q0 + q2) / 2
  let a : ℝ := (q0 - q2) / 2
  let b : ℝ := (q1 - q3) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hq0c : q0 = t + a := by dsimp [t, a]; ring
  have hq2c : q2 = t - a := by dsimp [t, a]; ring
  have htalt : t = (q1 + q3) / 2 := by dsimp [t]; linarith
  have hq1c : q1 = t + b := by dsimp [b]; rw [htalt]; ring
  have hq3c : q3 = t - b := by dsimp [b]; rw [htalt]; ring
  have haLo : -t < a := by dsimp [t, a]; linarith
  have haHi : a < t := by dsimp [t, a]; linarith
  have hbLo : -t < b := by dsimp [t, b]; linarith
  have hbHi : b < t := by dsimp [t, b]; linarith
  have hCaps :
      (q0 + m) * (q1 + m) * (q2 + m) * (q3 + m) =
        (((t + m) ^ 2 - a ^ 2) * ((t + m) ^ 2 - b ^ 2)) := by
    rw [hq0c, hq1c, hq2c, hq3c]
    ring
  have hQ :
      q0 * q1 * q2 * q3 =
        (t ^ 2 - a ^ 2) * (t ^ 2 - b ^ 2) := by
    rw [hq0c, hq1c, hq2c, hq3c]
    ring
  have hN0Eq :
      q0 * q1 + m * (q0 - q3) =
        t ^ 2 + a * b + (t + m) * (a + b) := by
    rw [hq0c, hq1c, hq3c]
    ring
  have hN1Eq :
      q1 * q2 + m * (q1 - q0) =
        t ^ 2 - a * b + (t + m) * (b - a) := by
    rw [hq1c, hq2c, hq0c]
    ring
  have hN2Eq :
      q2 * q3 + m * (q2 - q1) =
        t ^ 2 + a * b - (t + m) * (a + b) := by
    rw [hq2c, hq3c, hq1c]
    ring
  have hN3Eq :
      q3 * q0 + m * (q3 - q2) =
        t ^ 2 - a * b - (t + m) * (b - a) := by
    rw [hq3c, hq0c, hq2c]
    ring
  have hePlus :
      0 < t ^ 2 + a * b + (t + m) * (a + b) := by
    calc
      0 < q0 * q1 + m * (q0 - q3) := hN0
      _ = t ^ 2 + a * b + (t + m) * (a + b) := hN0Eq
  have heMinus :
      0 < t ^ 2 + a * b - (t + m) * (a + b) := by
    calc
      0 < q2 * q3 + m * (q2 - q1) := hN2
      _ = t ^ 2 + a * b - (t + m) * (a + b) := hN2Eq
  have hoPlus :
      0 < t ^ 2 - a * b + (t + m) * (b - a) := by
    calc
      0 < q1 * q2 + m * (q1 - q0) := hN1
      _ = t ^ 2 - a * b + (t + m) * (b - a) := hN1Eq
  have hoMinus :
      0 < t ^ 2 - a * b - (t + m) * (b - a) := by
    calc
      0 < q3 * q0 + m * (q3 - q2) := hN3
      _ = t ^ 2 - a * b - (t + m) * (b - a) := hN3Eq
  have hmaster :
      256 * m ^ 4 * ((t + m) ^ 2 - a ^ 2) *
          ((t + m) ^ 2 - b ^ 2) *
          (t ^ 2 - a ^ 2) ^ 2 * (t ^ 2 - b ^ 2) ^ 2 ≤
        ((t ^ 2 + a * b + (t + m) * (a + b)) *
          (t ^ 2 + a * b - (t + m) * (a + b)) *
          (t ^ 2 - a * b + (t + m) * (b - a)) *
          (t ^ 2 - a * b - (t + m) * (b - a))) ^ 2 := by
    have hpGrouped :
        256 * m ^ 4 *
              ((q0 + m) * (q1 + m) * (q2 + m) * (q3 + m)) *
              (q0 * q1 * q2 * q3) ^ 2 ≤
            ((q0 * q1 + m * (q0 - q3)) *
              (q1 * q2 + m * (q1 - q0)) *
              (q2 * q3 + m * (q2 - q1)) *
              (q3 * q0 + m * (q3 - q2))) ^ 2 := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct
    rw [hCaps, hQ, hN0Eq, hN1Eq, hN2Eq, hN3Eq] at hpGrouped
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpGrouped
  have hsharp := octagon_pair_product_forces_sharp hm ht haLo haHi hbLo hbHi
    hePlus heMinus hoPlus hoMinus hmaster
  by_contra hnot
  have htarget : 4 * t < 17 * m := by
    have : 2 * (q0 + q2) < 17 * m := lt_of_not_ge hnot
    dsimp [t]
    linarith
  have ht16 : t < 16 * m := by linarith
  have hmulT : 4 * t ^ 2 < 17 * m * t := by
    have := mul_lt_mul_of_pos_right htarget ht
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using this
  have hmulM : m * t < 16 * m ^ 2 := by
    have := mul_lt_mul_of_pos_left ht16 hm
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using this
  have hbelow : t ^ 2 < 4 * m * (t + m) := by nlinarith
  exact (not_lt_of_ge hsharp) hbelow

/--
Main scalar interface for the octagon adapter.

`N0,...,N3` are the four positive cyclic factors before cap lowering and
`D0,...,D3` are the four joint-ear product factors.  The adapter obtains the
single displayed product premise from four Pluecker identities and four
instances of `(x-y)^2 >= 0`.  This theorem lowers all caps to `m`, invokes
the opposite-pair endpoint, and returns the rational central-area bound.
-/
theorem hullEight_octagon_scalar_of_product
    {m q0 q1 q2 q3 c0 c1 c2 c3 : ℝ}
    (hm : 0 < m)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hq2 : 0 < q2) (hq3 : 0 < q3)
    (hc0 : m ≤ c0) (hc1 : m ≤ c1)
    (hc2 : m ≤ c2) (hc3 : m ≤ c3)
    (hqsum : q0 + q2 = q1 + q3)
    (hN0 : 0 < q0 * q1 + c0 * (q0 - q3))
    (hN1 : 0 < q1 * q2 + c1 * (q1 - q0))
    (hN2 : 0 < q2 * q3 + c2 * (q2 - q1))
    (hN3 : 0 < q3 * q0 + c3 * (q3 - q2))
    (hproduct :
      256 * (m * q0 + c3 * c0) * (m * q1 + c0 * c1) *
          (m * q2 + c1 * c2) * (m * q3 + c2 * c3) *
          (q0 * q1 * q2 * q3) ^ 2 ≤
        ((q0 * q1 + c0 * (q0 - q3)) *
          (q1 * q2 + c1 * (q1 - q0)) *
          (q2 * q3 + c2 * (q2 - q1)) *
          (q3 * q0 + c3 * (q3 - q2))) ^ 2) :
    17 * m ≤ 2 * (q0 + q2) := by
  let N0 : ℝ → ℝ := fun u ↦ q0 * q1 + u * (q0 - q3)
  let N1 : ℝ → ℝ := fun u ↦ q1 * q2 + u * (q1 - q0)
  let N2 : ℝ → ℝ := fun u ↦ q2 * q3 + u * (q2 - q1)
  let N3 : ℝ → ℝ := fun u ↦ q3 * q0 + u * (q3 - q2)
  let D0 : ℝ → ℝ → ℝ := fun left cap ↦ m * q0 + left * cap
  let D1 : ℝ → ℝ → ℝ := fun left cap ↦ m * q1 + left * cap
  let D2 : ℝ → ℝ → ℝ := fun left cap ↦ m * q2 + left * cap
  let D3 : ℝ → ℝ → ℝ := fun left cap ↦ m * q3 + left * cap
  have hc0p : 0 < c0 := lt_of_lt_of_le hm hc0
  have hc1p : 0 < c1 := lt_of_lt_of_le hm hc1
  have hc2p : 0 < c2 := lt_of_lt_of_le hm hc2
  have hc3p : 0 < c3 := lt_of_lt_of_le hm hc3
  have hd0q0 : q0 - q3 < q0 := by linarith
  have hd0q1 : q0 - q3 < q1 := by linarith
  have hd1q1 : q1 - q0 < q1 := by linarith
  have hd1q2 : q1 - q0 < q2 := by linarith
  have hd2q2 : q2 - q1 < q2 := by linarith
  have hd2q3 : q2 - q1 < q3 := by linarith
  have hd3q3 : q3 - q2 < q3 := by linarith
  have hd3q0 : q3 - q2 < q0 := by linarith
  have hN0m : 0 < N0 m := by
    apply octagon_lowered_numerator_pos hm hq0 hq1 hc0
    simpa [N0] using hN0
  have hN1m : 0 < N1 m := by
    apply octagon_lowered_numerator_pos hm hq1 hq2 hc1
    simpa [N1] using hN1
  have hN2m : 0 < N2 m := by
    apply octagon_lowered_numerator_pos hm hq2 hq3 hc2
    simpa [N2] using hN2
  have hN3m : 0 < N3 m := by
    apply octagon_lowered_numerator_pos hm hq3 hq0 hc3
    simpa [N3] using hN3
  have hD0cc : 0 < D0 c3 c0 := by dsimp [D0]; positivity
  have hD1cc : 0 < D1 c0 c1 := by dsimp [D1]; positivity
  have hD2cc : 0 < D2 c1 c2 := by dsimp [D2]; positivity
  have hD3cc : 0 < D3 c2 c3 := by dsimp [D3]; positivity
  let F0 : ℝ :=
    (N0 c0 * N1 c1 * N2 c2 * N3 c3) ^ 2 /
      (D0 c3 c0 * D1 c0 c1 * D2 c1 c2 * D3 c2 c3)
  let F1 : ℝ :=
    (N0 m * N1 c1 * N2 c2 * N3 c3) ^ 2 /
      (D0 c3 m * D1 m c1 * D2 c1 c2 * D3 c2 c3)
  let F2 : ℝ :=
    (N0 m * N1 m * N2 c2 * N3 c3) ^ 2 /
      (D0 c3 m * D1 m m * D2 m c2 * D3 c2 c3)
  let F3 : ℝ :=
    (N0 m * N1 m * N2 m * N3 c3) ^ 2 /
      (D0 c3 m * D1 m m * D2 m m * D3 m c3)
  let F4 : ℝ :=
    (N0 m * N1 m * N2 m * N3 m) ^ 2 /
      (D0 m m * D1 m m * D2 m m * D3 m m)
  have hF01 : F0 ≤ F1 := by
    have hcommonD : 0 < D2 c1 c2 * D3 c2 c3 := mul_pos hD2cc hD3cc
    have hraw := octagon_cap_lower_ratio
      (m := m) (q := q0) (qnext := q1) (d := q0 - q3)
      (left := c3) (right := c1) (u := c0)
      (commonN := N1 c1 * N2 c2 * N3 c3)
      (commonD := D2 c1 c2 * D3 c2 c3)
      hm hq0 hq1 hc0 hc3 hc1 hd0q0 hd0q1 hN0 hcommonD
    dsimp [F0, F1, N0, N1, N2, N3, D0, D1, D2, D3] at hraw ⊢
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
  have hD0c3m : 0 < D0 c3 m := by dsimp [D0]; positivity
  have hD3c2c3 : 0 < D3 c2 c3 := hD3cc
  have hF12 : F1 ≤ F2 := by
    have hcommonD : 0 < D0 c3 m * D3 c2 c3 := mul_pos hD0c3m hD3c2c3
    have hraw := octagon_cap_lower_ratio
      (m := m) (q := q1) (qnext := q2) (d := q1 - q0)
      (left := m) (right := c2) (u := c1)
      (commonN := N0 m * N2 c2 * N3 c3)
      (commonD := D0 c3 m * D3 c2 c3)
      hm hq1 hq2 hc1 le_rfl hc2 hd1q1 hd1q2 hN1 hcommonD
    dsimp [F1, F2, N0, N1, N2, N3, D0, D1, D2, D3] at hraw ⊢
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
  have hD1mm : 0 < D1 m m := by dsimp [D1]; positivity
  have hF23 : F2 ≤ F3 := by
    have hcommonD : 0 < D0 c3 m * D1 m m := mul_pos hD0c3m hD1mm
    have hraw := octagon_cap_lower_ratio
      (m := m) (q := q2) (qnext := q3) (d := q2 - q1)
      (left := m) (right := c3) (u := c2)
      (commonN := N0 m * N1 m * N3 c3)
      (commonD := D0 c3 m * D1 m m)
      hm hq2 hq3 hc2 le_rfl hc3 hd2q2 hd2q3 hN2 hcommonD
    dsimp [F2, F3, N0, N1, N2, N3, D0, D1, D2, D3] at hraw ⊢
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
  have hD1mm' : 0 < D1 m m := hD1mm
  have hD2mm : 0 < D2 m m := by dsimp [D2]; positivity
  have hF34 : F3 ≤ F4 := by
    have hcommonD : 0 < D1 m m * D2 m m := mul_pos hD1mm' hD2mm
    have hraw := octagon_cap_lower_ratio
      (m := m) (q := q3) (qnext := q0) (d := q3 - q2)
      (left := m) (right := m) (u := c3)
      (commonN := N0 m * N1 m * N2 m)
      (commonD := D1 m m * D2 m m)
      hm hq3 hq0 hc3 le_rfl le_rfl hd3q3 hd3q0 hN3 hcommonD
    dsimp [F3, F4, N0, N1, N2, N3, D0, D1, D2, D3] at hraw ⊢
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
  have hFmono : F0 ≤ F4 := le_trans (le_trans (le_trans hF01 hF12) hF23) hF34
  have hDcurrent :
      0 < D0 c3 c0 * D1 c0 c1 * D2 c1 c2 * D3 c2 c3 := by positivity
  have hF0lower : 256 * (q0 * q1 * q2 * q3) ^ 2 ≤ F0 := by
    apply (le_div_iff₀ hDcurrent).2
    dsimp [F0, N0, N1, N2, N3, D0, D1, D2, D3]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct
  have hF4lower : 256 * (q0 * q1 * q2 * q3) ^ 2 ≤ F4 :=
    le_trans hF0lower hFmono
  have hDfloor :
      0 < D0 m m * D1 m m * D2 m m * D3 m m := by positivity
  have hfloorCross :
      256 * (q0 * q1 * q2 * q3) ^ 2 *
          (D0 m m * D1 m m * D2 m m * D3 m m) ≤
        (N0 m * N1 m * N2 m * N3 m) ^ 2 := by
    exact (le_div_iff₀ hDfloor).mp (by simpa [F4] using hF4lower)
  have hfloorProduct :
      256 * m ^ 4 * (q0 + m) * (q1 + m) * (q2 + m) * (q3 + m) *
          (q0 * q1 * q2 * q3) ^ 2 ≤
        ((q0 * q1 + m * (q0 - q3)) *
          (q1 * q2 + m * (q1 - q0)) *
          (q2 * q3 + m * (q2 - q1)) *
          (q3 * q0 + m * (q3 - q2))) ^ 2 := by
    dsimp [N0, N1, N2, N3, D0, D1, D2, D3] at hfloorCross
    have hden :
        (m * q0 + m * m) * (m * q1 + m * m) *
            (m * q2 + m * m) * (m * q3 + m * m) =
          m ^ 4 * (q0 + m) * (q1 + m) * (q2 + m) * (q3 + m) := by
      ring
    rw [hden] at hfloorCross
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hfloorCross
  exact hullEight_octagon_scalar_of_floor_product hm hq0 hq1 hq2 hq3 hqsum
    hN0m hN1m hN2m hN3m hfloorProduct

/--
The rational target `17/4` lies strictly below the sharp scalar threshold.
This is the final numerical step used after writing the central area as
`Q=2*t` and using the four cap floors.
-/
theorem octagon_rational_target_below_sharp
    {m t : ℝ} (hm : 0 < m) (ht : 0 < t)
    (htarget : 4 * t < 17 * m) :
    t ^ 2 < 4 * m * (t + m) := by
  have ht16 : t < 16 * m := by nlinarith
  have hmulT : 4 * t ^ 2 < 17 * m * t := by
    have := mul_lt_mul_of_pos_right htarget ht
    nlinarith
  have hmulM : m * t < 16 * m ^ 2 := by
    have := mul_lt_mul_of_pos_left ht16 hm
    nlinarith
  nlinarith

end Heilbronn8
