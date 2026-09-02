import Mathlib

/-!
# A rational continuant closer for seven cyclic ears

This file contains the scalar core of a direct hull-seven ear argument.  Write

`a = [012]`, `b = [023]`, `c = [034]`, `d = [045]`, `e = [056]`

for the five triangles in the fan based at vertex zero, and put

`q2 = [013]`, `q3 = [024]`, `q4 = [035]`, `q5 = [046]`.

The three left Pluecker recurrences express `[016]` as the continuant below.
If every cyclic ear is at least one, the four `q` variables are bounded above
by `a+b-1`, ..., `d+e-1`.  Positivity of the remaining minors makes the
continuant monotone under those four replacements.  Two exact endpoint-push
identities then reduce the assertion to a polynomial on a three-simplex.

No geometric claim is made here.  In particular, the separate geometric
adapter must show that the five fan triangles inherit the common cyclic-ear
floor and must provide the displayed Pluecker rows.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Numerator of the length-four Pluecker continuant from `1` to `6`. -/
def hullSevenContinuantNumerator
    (a b c d e q2 q3 q4 q5 : ℝ) : ℝ :=
  q2 * q3 * q4 * q5 - a * c * q4 * q5 - b * d * q2 * q5 -
    c * e * q2 * q3 + a * c ^ 2 * e

/-- The continuant after replacing each two-step minor by its ear-floor cap. -/
def hullSevenMaximalContinuantNumerator (a b c d e : ℝ) : ℝ :=
  hullSevenContinuantNumerator a b c d e
    (a + b - 1) (b + c - 1) (c + d - 1) (d + e - 1)

/-- Three consecutive Pluecker recurrences give the closed continuant formula.
The intended minors are `r14 = [014]`, `r15 = [015]`, and `p16 = [016]`. -/
lemma hullSeven_continuant_identity
    (a b c d e q2 q3 q4 q5 r14 r15 p16 : ℝ)
    (h14 : b * r14 = q2 * q3 - a * c)
    (h15 : c * r15 = r14 * q4 - q2 * d)
    (h16 : d * p16 = r15 * q5 - r14 * e) :
    b * c * d * p16 =
      hullSevenContinuantNumerator a b c d e q2 q3 q4 q5 := by
  calc
    b * c * d * p16 = b * c * (d * p16) := by ring
    _ = b * c * (r15 * q5 - r14 * e) := by rw [h16]
    _ = b * (c * r15) * q5 - c * (b * r14) * e := by ring
    _ = b * (r14 * q4 - q2 * d) * q5 -
        c * (q2 * q3 - a * c) * e := by rw [h15, h14]
    _ = (b * r14) * q4 * q5 - b * d * q2 * q5 -
        c * e * q2 * q3 + a * c ^ 2 * e := by ring
    _ = hullSevenContinuantNumerator a b c d e q2 q3 q4 q5 := by
      rw [h14]
      unfold hullSevenContinuantNumerator
      ring

/-- Monotonicity of the continuant in all four two-step minors.

The replacements are deliberately made in the order `q5,q4,q3,q2`.  At each
step the corresponding coefficient is an actual or intermediate positive
minor.  The right-hand recurrences use `r25 = [025]`, `r26 = [026]`, and
`r36 = [036]`. -/
lemma hullSevenContinuantNumerator_mono
    (a b c d e q2 q3 q4 q5 Q2 Q3 Q4 Q5
      r14 r15 r25 r26 r36 : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4)
    (hq5 : 0 ≤ q5)
    (hQ2 : 0 ≤ Q2) (hQ3 : 0 ≤ Q3) (hQ4 : 0 ≤ Q4)
    (hQ5 : 0 ≤ Q5)
    (hr14 : 0 ≤ r14) (hr15 : 0 ≤ r15)
    (hr25 : 0 ≤ r25) (hr26 : 0 ≤ r26) (hr36 : 0 ≤ r36)
    (h2 : q2 ≤ Q2) (h3 : q3 ≤ Q3)
    (h4 : q4 ≤ Q4) (h5 : q5 ≤ Q5)
    (h14 : b * r14 = q2 * q3 - a * c)
    (h15 : c * r15 = r14 * q4 - q2 * d)
    (h25 : c * r25 = q3 * q4 - b * d)
    (h26 : d * r26 = r25 * q5 - q3 * e)
    (h36 : d * r36 = q4 * q5 - c * e) :
    hullSevenContinuantNumerator a b c d e q2 q3 q4 q5 ≤
      hullSevenContinuantNumerator a b c d e Q2 Q3 Q4 Q5 := by
  have hcoef5id :
      q2 * q3 * q4 - a * c * q4 - b * d * q2 = b * c * r15 := by
    calc
      q2 * q3 * q4 - a * c * q4 - b * d * q2 =
          (q2 * q3 - a * c) * q4 - b * q2 * d := by ring
      _ = (b * r14) * q4 - b * q2 * d := by rw [← h14]
      _ = b * (r14 * q4 - q2 * d) := by ring
      _ = b * (c * r15) := by rw [← h15]
      _ = b * c * r15 := by ring
  have hcoef5 :
      0 ≤ q2 * q3 * q4 - a * c * q4 - b * d * q2 := by
    rw [hcoef5id]
    exact mul_nonneg (mul_nonneg hb hc) hr15
  have hstep5id :
      hullSevenContinuantNumerator a b c d e q2 q3 q4 Q5 -
          hullSevenContinuantNumerator a b c d e q2 q3 q4 q5 =
        (Q5 - q5) *
          (q2 * q3 * q4 - a * c * q4 - b * d * q2) := by
    unfold hullSevenContinuantNumerator
    ring
  have hstep5 :
      hullSevenContinuantNumerator a b c d e q2 q3 q4 q5 ≤
        hullSevenContinuantNumerator a b c d e q2 q3 q4 Q5 := by
    apply sub_nonneg.mp
    rw [hstep5id]
    exact mul_nonneg (sub_nonneg.mpr h5) hcoef5

  have hcoef4id :
      (q2 * q3 - a * c) * Q5 = b * r14 * Q5 := by rw [← h14]
  have hcoef4 : 0 ≤ (q2 * q3 - a * c) * Q5 := by
    rw [hcoef4id]
    positivity
  have hstep4id :
      hullSevenContinuantNumerator a b c d e q2 q3 Q4 Q5 -
          hullSevenContinuantNumerator a b c d e q2 q3 q4 Q5 =
        (Q4 - q4) * (q2 * q3 - a * c) * Q5 := by
    unfold hullSevenContinuantNumerator
    ring
  have hstep4 :
      hullSevenContinuantNumerator a b c d e q2 q3 q4 Q5 ≤
        hullSevenContinuantNumerator a b c d e q2 q3 Q4 Q5 := by
    apply sub_nonneg.mp
    rw [hstep4id]
    simpa [mul_assoc] using mul_nonneg (sub_nonneg.mpr h4) hcoef4

  have hbase36 : 0 ≤ q4 * q5 - c * e := by
    rw [← h36]
    exact mul_nonneg hd hr36
  have hprod45 : q4 * q5 ≤ Q4 * Q5 := by
    calc
      q4 * q5 ≤ Q4 * q5 := mul_le_mul_of_nonneg_right h4 hq5
      _ ≤ Q4 * Q5 := mul_le_mul_of_nonneg_left h5 hQ4
  have hQ45 : 0 ≤ Q4 * Q5 - c * e :=
    sub_nonneg.mpr ((sub_nonneg.mp hbase36).trans hprod45)
  have hcoef3 : 0 ≤ q2 * (Q4 * Q5 - c * e) :=
    mul_nonneg hq2 hQ45
  have hstep3id :
      hullSevenContinuantNumerator a b c d e q2 Q3 Q4 Q5 -
          hullSevenContinuantNumerator a b c d e q2 q3 Q4 Q5 =
        (Q3 - q3) * q2 * (Q4 * Q5 - c * e) := by
    unfold hullSevenContinuantNumerator
    ring
  have hstep3 :
      hullSevenContinuantNumerator a b c d e q2 q3 Q4 Q5 ≤
        hullSevenContinuantNumerator a b c d e q2 Q3 Q4 Q5 := by
    apply sub_nonneg.mp
    rw [hstep3id]
    simpa [mul_assoc] using mul_nonneg (sub_nonneg.mpr h3) hcoef3

  have hcoef2baseid :
      q3 * q4 * q5 - b * d * q5 - c * e * q3 = c * d * r26 := by
    calc
      q3 * q4 * q5 - b * d * q5 - c * e * q3 =
          (q3 * q4 - b * d) * q5 - c * q3 * e := by ring
      _ = (c * r25) * q5 - c * q3 * e := by rw [← h25]
      _ = c * (r25 * q5 - q3 * e) := by ring
      _ = c * (d * r26) := by rw [← h26]
      _ = c * d * r26 := by ring
  have hcoef2base :
      0 ≤ q3 * q4 * q5 - b * d * q5 - c * e * q3 := by
    rw [hcoef2baseid]
    exact mul_nonneg (mul_nonneg hc hd) hr26
  have hcoef2a :
      0 ≤ q3 * Q4 * q5 - b * d * q5 - c * e * q3 := by
    calc
      0 ≤ q3 * q4 * q5 - b * d * q5 - c * e * q3 := hcoef2base
      _ ≤ q3 * Q4 * q5 - b * d * q5 - c * e * q3 := by
        apply sub_nonneg.mp
        have hid :
            (q3 * Q4 * q5 - b * d * q5 - c * e * q3) -
                (q3 * q4 * q5 - b * d * q5 - c * e * q3) =
              q3 * (Q4 - q4) * q5 := by ring
        rw [hid]
        exact mul_nonneg (mul_nonneg hq3 (sub_nonneg.mpr h4)) hq5
  have hQ4q5 : 0 ≤ Q4 * q5 - c * e := by
    apply sub_nonneg.mpr
    exact (sub_nonneg.mp hbase36).trans
      (mul_le_mul_of_nonneg_right h4 hq5)
  have hcoef2b :
      0 ≤ Q3 * Q4 * q5 - b * d * q5 - c * e * Q3 := by
    calc
      0 ≤ q3 * Q4 * q5 - b * d * q5 - c * e * q3 := hcoef2a
      _ ≤ Q3 * Q4 * q5 - b * d * q5 - c * e * Q3 := by
        apply sub_nonneg.mp
        have hid :
            (Q3 * Q4 * q5 - b * d * q5 - c * e * Q3) -
                (q3 * Q4 * q5 - b * d * q5 - c * e * q3) =
              (Q3 - q3) * (Q4 * q5 - c * e) := by ring
        rw [hid]
        exact mul_nonneg (sub_nonneg.mpr h3) hQ4q5
  have hbase25 : 0 ≤ q3 * q4 - b * d := by
    rw [← h25]
    exact mul_nonneg hc hr25
  have hQ34 : 0 ≤ Q3 * Q4 - b * d := by
    apply sub_nonneg.mpr
    have hprod34 : q3 * q4 ≤ Q3 * Q4 := by
      calc
        q3 * q4 ≤ Q3 * q4 := mul_le_mul_of_nonneg_right h3 hq4
        _ ≤ Q3 * Q4 := mul_le_mul_of_nonneg_left h4 hQ3
    exact (sub_nonneg.mp hbase25).trans hprod34
  have hcoef2 :
      0 ≤ Q3 * Q4 * Q5 - b * d * Q5 - c * e * Q3 := by
    calc
      0 ≤ Q3 * Q4 * q5 - b * d * q5 - c * e * Q3 := hcoef2b
      _ ≤ Q3 * Q4 * Q5 - b * d * Q5 - c * e * Q3 := by
        apply sub_nonneg.mp
        have hid :
            (Q3 * Q4 * Q5 - b * d * Q5 - c * e * Q3) -
                (Q3 * Q4 * q5 - b * d * q5 - c * e * Q3) =
              (Q5 - q5) * (Q3 * Q4 - b * d) := by ring
        rw [hid]
        exact mul_nonneg (sub_nonneg.mpr h5) hQ34
  have hstep2id :
      hullSevenContinuantNumerator a b c d e Q2 Q3 Q4 Q5 -
          hullSevenContinuantNumerator a b c d e q2 Q3 Q4 Q5 =
        (Q2 - q2) *
          (Q3 * Q4 * Q5 - b * d * Q5 - c * e * Q3) := by
    unfold hullSevenContinuantNumerator
    ring
  have hstep2 :
      hullSevenContinuantNumerator a b c d e q2 Q3 Q4 Q5 ≤
        hullSevenContinuantNumerator a b c d e Q2 Q3 Q4 Q5 := by
    apply sub_nonneg.mp
    rw [hstep2id]
    exact mul_nonneg (sub_nonneg.mpr h2) hcoef2
  exact hstep5.trans (hstep4.trans (hstep3.trans hstep2))

/-- Manifestly nonnegative factor in the endpoint-push identities. -/
def hullSevenEndpointPushFactor (A B C D E : ℝ) : ℝ :=
  4 + 2 * E + 2 * D + 4 * C + 2 * B + 2 * A +
    C * E + C * D + C ^ 2 + B * E + B * D + B * C +
    A * E + A * D + A * C

lemma hullSevenEndpointPushFactor_nonneg
    {A B C D E : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) :
    0 ≤ hullSevenEndpointPushFactor A B C D E := by
  unfold hullSevenEndpointPushFactor
  positivity

/-- Move all excess in the left endpoint fan triangle into its neighbour. -/
lemma hullSeven_endpoint_push_left_identity (a b c d e : ℝ) :
    b * hullSevenMaximalContinuantNumerator 1 (a + b - 1) c d e -
        (a + b - 1) * hullSevenMaximalContinuantNumerator a b c d e =
      (a - 1) * (d - 1) *
        hullSevenEndpointPushFactor
          (a - 1) (b - 1) (c - 1) (d - 1) (e - 1) := by
  unfold hullSevenMaximalContinuantNumerator hullSevenContinuantNumerator
    hullSevenEndpointPushFactor
  ring

/-- Reversed endpoint push on the right. -/
lemma hullSeven_endpoint_push_right_identity (a b c d e : ℝ) :
    d * hullSevenMaximalContinuantNumerator a b c (d + e - 1) 1 -
        (d + e - 1) * hullSevenMaximalContinuantNumerator a b c d e =
      (e - 1) * (b - 1) *
        hullSevenEndpointPushFactor
          (e - 1) (d - 1) (c - 1) (b - 1) (a - 1) := by
  unfold hullSevenMaximalContinuantNumerator hullSevenContinuantNumerator
    hullSevenEndpointPushFactor
  ring

/-- Exact centered form of the final denominator-minus-numerator gap. -/
lemma hullSeven_centered_continuant_gap_identity (x y z : ℝ) :
    (1 + x) * (1 + y) * (1 + z) -
        hullSevenMaximalContinuantNumerator 1 (1 + x) (1 + y) (1 + z) 1 =
      2 + 3 * x + y + 3 * z + x ^ 2 + z ^ 2 + x * y + x * z + y * z -
        x * y * z * (3 + x + y + z) := by
  unfold hullSevenMaximalContinuantNumerator hullSevenContinuantNumerator
  ring

/-- The centered gap is at least two on the simplex `x+y+z ≤ 4`. -/
lemma two_le_hullSeven_centered_continuant_gap
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z ≤ 4) :
    2 ≤ 2 + 3 * x + y + 3 * z + x ^ 2 + z ^ 2 +
      x * y + x * z + y * z - x * y * z * (3 + x + y + z) := by
  let u : ℝ := x + z
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huy : u + y ≤ 4 := by dsimp [u]; linarith
  have hfourxz : 4 * (x * z) ≤ u ^ 2 := by
    have hsquare := sq_nonneg (x - z)
    dsimp [u]
    nlinarith
  have hfactor : 0 ≤ 1 + y * (3 + u + y) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hfourxz hfactor
  have hreduce :
      12 * u + 4 * y + 3 * u ^ 2 + 4 * u * y -
          u ^ 2 * y * (3 + u + y) ≤
        4 * ((2 + 3 * x + y + 3 * z + x ^ 2 + z ^ 2 +
          x * y + x * z + y * z - x * y * z *
            (3 + x + y + z)) - 2) := by
    dsimp [u] at hscaled ⊢
    nlinarith
  have hslack : 0 ≤ 4 - u - y := by linarith
  have hdrop := mul_nonneg (mul_nonneg (sq_nonneg u) hy) hslack
  have hreduce' :
      12 * u + 4 * y + 3 * u ^ 2 + 4 * u * y - 7 * u ^ 2 * y ≤
        12 * u + 4 * y + 3 * u ^ 2 + 4 * u * y -
          u ^ 2 * y * (3 + u + y) := by
    nlinarith
  let k : ℝ := 4 + 4 * u - 7 * u ^ 2
  have hmain : 0 ≤ 12 * u + 3 * u ^ 2 + y * k := by
    by_cases hk : 0 ≤ k
    · exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) hu)
          (mul_nonneg (by norm_num) (sq_nonneg u)))
        (mul_nonneg hy hk)
    · have hk' : k < 0 := lt_of_not_ge hk
      have hyu : y ≤ 4 - u := by linarith
      have hmul : (4 - u) * k ≤ y * k :=
        mul_le_mul_of_nonpos_right hyu hk'.le
      have hpoly : 0 ≤ 7 * u ^ 3 - 29 * u ^ 2 + 24 * u + 16 := by
        by_cases hu2 : u ≤ 2
        · let r : ℝ := 2 - u
          have hr : 0 ≤ r := by dsimp [r]; linarith
          have hr2 : r ≤ 2 := by dsimp [r]; linarith
          have hquad := mul_nonneg hr (sub_nonneg.mpr hr2)
          have hcubic : 0 ≤ 7 * r ^ 2 * (2 - r) :=
            mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r))
              (sub_nonneg.mpr hr2)
          have hid :
              7 * u ^ 3 - 29 * u ^ 2 + 24 * u + 16 =
                4 + 8 * r + 13 * r ^ 2 - 7 * r ^ 3 := by
            dsimp [r]
            ring
          rw [hid]
          nlinarith
        · have hu2' : 2 < u := lt_of_not_ge hu2
          let r : ℝ := u - 2
          have hr : 0 ≤ r := by dsimp [r]; linarith
          have hsquare := sq_nonneg (13 * r - 4)
          have hcubic := mul_nonneg (sq_nonneg r) hr
          have hid :
              7 * u ^ 3 - 29 * u ^ 2 + 24 * u + 16 =
                4 - 8 * r + 13 * r ^ 2 + 7 * r ^ 3 := by
            dsimp [r]
            ring
          rw [hid]
          nlinarith
      have hidmain :
          12 * u + 3 * u ^ 2 + (4 - u) * k =
            7 * u ^ 3 - 29 * u ^ 2 + 24 * u + 16 := by
        dsimp [k]
        ring
      nlinarith
  have hmain' :
      0 ≤ 12 * u + 4 * y + 3 * u ^ 2 + 4 * u * y - 7 * u ^ 2 * y := by
    dsimp [k] at hmain
    nlinarith
  nlinarith

/-- At the maximal two-step minors, five fan triangles of sum at most nine
leave a strict continuant deficit. -/
lemma hullSeven_maximalContinuant_lt_denominator
    {a b c d e : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (hsum : a + b + c + d + e ≤ 9) :
    hullSevenMaximalContinuantNumerator a b c d e < b * c * d := by
  let B : ℝ := a + b - 1
  let D : ℝ := d + e - 1
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hleftFactor :
      0 ≤ hullSevenEndpointPushFactor
        (a - 1) (b - 1) (c - 1) (d - 1) (e - 1) :=
    hullSevenEndpointPushFactor_nonneg
      (sub_nonneg.mpr ha) (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)
      (sub_nonneg.mpr hd) (sub_nonneg.mpr he)
  have hleftCross :
      B * hullSevenMaximalContinuantNumerator a b c d e ≤
        b * hullSevenMaximalContinuantNumerator 1 B c d e := by
    have hid := hullSeven_endpoint_push_left_identity a b c d e
    dsimp [B]
    nlinarith [mul_nonneg
      (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hd)) hleftFactor]
  have hrightFactor :
      0 ≤ hullSevenEndpointPushFactor
        (e - 1) (d - 1) (c - 1) (B - 1) (1 - 1) :=
    hullSevenEndpointPushFactor_nonneg
      (sub_nonneg.mpr he) (sub_nonneg.mpr hd) (sub_nonneg.mpr hc)
      (sub_nonneg.mpr hB) (by norm_num)
  have hrightCross :
      D * hullSevenMaximalContinuantNumerator 1 B c d e ≤
        d * hullSevenMaximalContinuantNumerator 1 B c D 1 := by
    have hid := hullSeven_endpoint_push_right_identity 1 B c d e
    dsimp [D]
    nlinarith [mul_nonneg
      (mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hB)) hrightFactor]
  let x : ℝ := B - 1
  let y : ℝ := c - 1
  let z : ℝ := D - 1
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hxyz : x + y + z ≤ 4 := by dsimp [x, y, z, B, D]; linarith
  have hgap := two_le_hullSeven_centered_continuant_gap hx hy hz hxyz
  have hidgap := hullSeven_centered_continuant_gap_identity x y z
  have hfinal :
      hullSevenMaximalContinuantNumerator 1 B c D 1 < B * c * D := by
    have hBx : B = 1 + x := by dsimp [x]; ring
    have hcy : c = 1 + y := by dsimp [y]; ring
    have hDz : D = 1 + z := by dsimp [z]; ring
    rw [hBx, hcy, hDz]
    nlinarith
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  by_contra hn
  have hden : b * c * d ≤ hullSevenMaximalContinuantNumerator a b c d e :=
    le_of_not_gt hn
  have hleftMul :
      b * (B * c * d) ≤
        b * hullSevenMaximalContinuantNumerator 1 B c d e := by
    calc
      b * (B * c * d) = B * (b * c * d) := by ring
      _ ≤ B * hullSevenMaximalContinuantNumerator a b c d e :=
        mul_le_mul_of_nonneg_left hden hBpos.le
      _ ≤ b * hullSevenMaximalContinuantNumerator 1 B c d e := hleftCross
  have hleftDen :
      B * c * d ≤ hullSevenMaximalContinuantNumerator 1 B c d e :=
    le_of_mul_le_mul_left hleftMul hbpos
  have hrightMul :
      d * (B * c * D) ≤
        d * hullSevenMaximalContinuantNumerator 1 B c D 1 := by
    calc
      d * (B * c * D) = D * (B * c * d) := by ring
      _ ≤ D * hullSevenMaximalContinuantNumerator 1 B c d e :=
        mul_le_mul_of_nonneg_left hleftDen hDpos.le
      _ ≤ d * hullSevenMaximalContinuantNumerator 1 B c D 1 := hrightCross
  have hrightDen :
      B * c * D ≤ hullSevenMaximalContinuantNumerator 1 B c D 1 :=
    le_of_mul_le_mul_left hrightMul hdpos
  linarith

/-- Complete normalized scalar packet for the direct fan-minor proof.

All hypotheses have immediate geometric meanings as positive triangle minors,
Pluecker rows, and the four cyclic-ear lower bounds. -/
theorem nine_le_fanSum_of_hullSeven_continuant
    (a b c d e p16 q2 q3 q4 q5 r14 r15 r25 r26 r36 : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hp16 : 1 ≤ p16)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5)
    (hr14 : 0 ≤ r14) (hr15 : 0 ≤ r15)
    (hr25 : 0 ≤ r25) (hr26 : 0 ≤ r26) (hr36 : 0 ≤ r36)
    (hear2 : q2 ≤ a + b - 1) (hear3 : q3 ≤ b + c - 1)
    (hear4 : q4 ≤ c + d - 1) (hear5 : q5 ≤ d + e - 1)
    (h14 : b * r14 = q2 * q3 - a * c)
    (h15 : c * r15 = r14 * q4 - q2 * d)
    (h16 : d * p16 = r15 * q5 - r14 * e)
    (h25 : c * r25 = q3 * q4 - b * d)
    (h26 : d * r26 = r25 * q5 - q3 * e)
    (h36 : d * r36 = q4 * q5 - c * e) :
    9 ≤ a + b + c + d + e := by
  let Q2 : ℝ := a + b - 1
  let Q3 : ℝ := b + c - 1
  let Q4 : ℝ := c + d - 1
  let Q5 : ℝ := d + e - 1
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; linarith
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; linarith
  have hQ4 : 0 ≤ Q4 := by dsimp [Q4]; linarith
  have hQ5 : 0 ≤ Q5 := by dsimp [Q5]; linarith
  have hmono := hullSevenContinuantNumerator_mono
    a b c d e q2 q3 q4 q5 Q2 Q3 Q4 Q5 r14 r15 r25 r26 r36
    (by linarith) (by linarith) (by linarith)
    hq2 hq3 hq4 hq5 hQ2 hQ3 hQ4 hQ5
    hr14 hr15 hr25 hr26 hr36
    (by simpa [Q2] using hear2) (by simpa [Q3] using hear3)
    (by simpa [Q4] using hear4) (by simpa [Q5] using hear5)
    h14 h15 h25 h26 h36
  have hcont := hullSeven_continuant_identity
    a b c d e q2 q3 q4 q5 r14 r15 p16 h14 h15 h16
  have hdennonneg : 0 ≤ b * c * d := by positivity
  have hpLower : b * c * d ≤ b * c * d * p16 := by
    nlinarith [mul_nonneg hdennonneg (sub_nonneg.mpr hp16)]
  have hbase :
      b * c * d ≤ hullSevenMaximalContinuantNumerator a b c d e := by
    dsimp [Q2, Q3, Q4, Q5] at hmono
    rw [← hcont] at hmono
    exact hpLower.trans hmono
  by_contra hn
  have hsum : a + b + c + d + e ≤ 9 := le_of_not_ge hn
  have hstrict := hullSeven_maximalContinuant_lt_denominator ha hb hc hd he hsum
  linarith

/-- Homogeneous form of `nine_le_fanSum_of_hullSeven_continuant`.

Here `m` is the common area floor.  Dividing every minor by `m` preserves all
six quadratic Pluecker rows and changes each ear cap from `a+b-m` to
`a/m+b/m-1`. -/
theorem nine_mul_le_fanSum_of_hullSeven_continuant
    (m a b c d e p16 q2 q3 q4 q5 r14 r15 r25 r26 r36 : ℝ)
    (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hd : m ≤ d) (he : m ≤ e) (hp16 : m ≤ p16)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5)
    (hr14 : 0 ≤ r14) (hr15 : 0 ≤ r15)
    (hr25 : 0 ≤ r25) (hr26 : 0 ≤ r26) (hr36 : 0 ≤ r36)
    (hear2 : q2 ≤ a + b - m) (hear3 : q3 ≤ b + c - m)
    (hear4 : q4 ≤ c + d - m) (hear5 : q5 ≤ d + e - m)
    (h14 : b * r14 = q2 * q3 - a * c)
    (h15 : c * r15 = r14 * q4 - q2 * d)
    (h16 : d * p16 = r15 * q5 - r14 * e)
    (h25 : c * r25 = q3 * q4 - b * d)
    (h26 : d * r26 = r25 * q5 - q3 * e)
    (h36 : d * r36 = q4 * q5 - c * e) :
    9 * m ≤ a + b + c + d + e := by
  have hm0 : 0 ≤ m := hm.le
  have hn := nine_le_fanSum_of_hullSeven_continuant
    (a / m) (b / m) (c / m) (d / m) (e / m) (p16 / m)
    (q2 / m) (q3 / m) (q4 / m) (q5 / m)
    (r14 / m) (r15 / m) (r25 / m) (r26 / m) (r36 / m)
    (by apply (le_div_iff₀ hm).2; simpa using ha)
    (by apply (le_div_iff₀ hm).2; simpa using hb)
    (by apply (le_div_iff₀ hm).2; simpa using hc)
    (by apply (le_div_iff₀ hm).2; simpa using hd)
    (by apply (le_div_iff₀ hm).2; simpa using he)
    (by apply (le_div_iff₀ hm).2; simpa using hp16)
    (div_nonneg hq2 hm0) (div_nonneg hq3 hm0)
    (div_nonneg hq4 hm0) (div_nonneg hq5 hm0)
    (div_nonneg hr14 hm0) (div_nonneg hr15 hm0)
    (div_nonneg hr25 hm0) (div_nonneg hr26 hm0) (div_nonneg hr36 hm0)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q2 ≤ a + b - m := hear2
        _ = (a / m + b / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q3 ≤ b + c - m := hear3
        _ = (b / m + c / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q4 ≤ c + d - m := hear4
        _ = (c / m + d / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      apply (div_le_iff₀ hm).2
      calc
        q5 ≤ d + e - m := hear5
        _ = (d / m + e / m - 1) * m := by
          field_simp [hm.ne']
          <;> ring)
    (by
      calc
        b / m * (r14 / m) = (b * r14) / m ^ 2 := by ring
        _ = (q2 * q3 - a * c) / m ^ 2 := by rw [h14]
        _ = q2 / m * (q3 / m) - a / m * (c / m) := by ring)
    (by
      calc
        c / m * (r15 / m) = (c * r15) / m ^ 2 := by ring
        _ = (r14 * q4 - q2 * d) / m ^ 2 := by rw [h15]
        _ = r14 / m * (q4 / m) - q2 / m * (d / m) := by ring)
    (by
      calc
        d / m * (p16 / m) = (d * p16) / m ^ 2 := by ring
        _ = (r15 * q5 - r14 * e) / m ^ 2 := by rw [h16]
        _ = r15 / m * (q5 / m) - r14 / m * (e / m) := by ring)
    (by
      calc
        c / m * (r25 / m) = (c * r25) / m ^ 2 := by ring
        _ = (q3 * q4 - b * d) / m ^ 2 := by rw [h25]
        _ = q3 / m * (q4 / m) - b / m * (d / m) := by ring)
    (by
      calc
        d / m * (r26 / m) = (d * r26) / m ^ 2 := by ring
        _ = (r25 * q5 - q3 * e) / m ^ 2 := by rw [h26]
        _ = r25 / m * (q5 / m) - q3 / m * (e / m) := by ring)
    (by
      calc
        d / m * (r36 / m) = (d * r36) / m ^ 2 := by ring
        _ = (q4 * q5 - c * e) / m ^ 2 := by rw [h36]
        _ = q4 / m * (q5 / m) - c / m * (e / m) := by ring)
  have hscaled := mul_le_mul_of_nonneg_right hn hm0
  calc
    9 * m ≤ (a / m + b / m + c / m + d / m + e / m) * m := hscaled
    _ = a + b + c + d + e := by
      field_simp [hm.ne']
      <;> ring

end HeilbronnChallenge.N7Upper
