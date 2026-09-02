import Mathlib

/-!
# Scalar closure for the `q = 012/112` hull-six branches

This file isolates the short analytic argument for the `p = 011` chambers
with `-Y11`, `+Y21`, and `-Y22`.  The variables `a,b,c` and `d,e,f` are the
positive upper and lower heights, and `r,s,t,w,z` are the five consecutive
slope gaps.

The only mixed hull input is the ear floor

`1 <= u0 + (-X02) - (-X12)`.

After two exact cross-chord eliminations, the final lower bound is four
reciprocal pairs and the strict inequality

`5/2 < c + e/b + b/(e*c)`.

No generated certificate, case split, or unproved monotonicity assertion is
used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private theorem hullSixThreeThreeQ112_reciprocalPair
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 ≤ x / y + y / x := by
  have hq : 0 ≤ (x - y) ^ 2 / (x * y) :=
    div_nonneg (sq_nonneg (x - y)) (le_of_lt (mul_pos hx hy))
  have hid :
      (x - y) ^ 2 / (x * y) = x / y + y / x - 2 := by
    field_simp [hx.ne', hy.ne']
    <;> ring
  rw [hid] at hq
  linarith

/-!
The notation used inside the proof is:

* `P = X10`, `T = u1`, `W = -X21`, and `Z = l1`;
* `J = -X11`, `K = -X12`, and `D = -X22`;
* `U,E,L,F` are respectively `u0`, `X20`, `l0`, and `-X02`.
-/

/--
Complete normalized scalar closure for the `q = 012/112` signed branch.

The assumptions are the six height floors, the `X10` and upper middle-fan
floors, the signed floors `-Y11 >= 1`, `Y21 >= 1`, `-Y22 >= 1`, and one
mixed hull ear.  The conclusion is the six consecutive-area sum.
-/
theorem hullSixThreeThreeQ112_scalar
    {a b c d e f r s t w z : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hX10 : 1 ≤ b * d * s)
    (hu1 : 1 ≤ b * c * t)
    (hY11neg : 1 ≤ b * e * (t + w) - b - e)
    (hY21pos : 1 ≤ c + e - c * e * w)
    (hY22neg : 1 ≤ c * f * (w + z) - c - f)
    (hEar :
      1 ≤ a * b * (r + s) + a * f * (r + s + t + w + z) -
        b * f * (t + w + z)) :
    (25 : ℝ) / 2 <
      a * b * (r + s) + b * c * t + c * d * (s + t) +
        d * e * (s + t + w) + e * f * z +
          a * f * (r + s + t + w + z) := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1

  let P : ℝ := b * d * s
  let T : ℝ := b * c * t
  let W : ℝ := c * e * w
  let Z : ℝ := e * f * z
  let J : ℝ := b * e * (t + w)
  let K : ℝ := b * f * (t + w + z)
  let D : ℝ := c * f * (w + z)
  let U : ℝ := a * b * (r + s)
  let E : ℝ := c * d * (s + t)
  let L : ℝ := d * e * (s + t + w)
  let F : ℝ := a * f * (r + s + t + w + z)

  have hP : 1 ≤ P := by simpa [P] using hX10
  have hT : 1 ≤ T := by simpa [T] using hu1
  have hJ : b + e + 1 ≤ J := by
    dsimp [J]
    linarith
  have hW : W ≤ c + e - 1 := by
    dsimp [W]
    linarith
  have hD : c + f + 1 ≤ D := by
    dsimp [D]
    linarith
  have hEarBase : 1 + K ≤ U + F := by
    dsimp [K, U, F]
    linarith

  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hJ0 : 0 ≤ J := by
    have : 0 ≤ b + e + 1 := by positivity
    exact this.trans hJ
  have hZidentity : Z = (e / c) * D - (f / c) * W := by
    dsimp [Z, D, W]
    field_simp [hc.ne']
    <;> ring
  have hTidentity : T = (c / e) * J - (b / e) * W := by
    dsimp [T, J, W]
    field_simp [he.ne']
    <;> ring
  have hKidentity : K = (f / e) * J + (b / e) * Z := by
    dsimp [K, J, Z]
    field_simp [he.ne']
    <;> ring
  have hEidentity : E = (c / b) * P + (d / b) * T := by
    dsimp [E, P, T]
    field_simp [hb.ne']
    <;> ring
  have hLidentity : L = (e / b) * P + (d / b) * J := by
    dsimp [L, P, J]
    field_simp [hb.ne']
    <;> ring

  have hPpart :
      (c + e) / b ≤ ((c + e) / b) * P := by
    calc
      (c + e) / b = ((c + e) / b) * 1 := by ring
      _ ≤ ((c + e) / b) * P :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  have hTJpart :
      (T + J) / b ≤ (d / b) * (T + J) := by
    have hcoef : 0 ≤ (T + J) / b := by positivity
    have hmul := mul_le_mul_of_nonneg_left hd1 hcoef
    calc
      (T + J) / b = ((T + J) / b) * 1 := by ring
      _ ≤ ((T + J) / b) * d := hmul
      _ = (d / b) * (T + J) := by ring
  have hEL : (c + e + T + J) / b ≤ E + L := by
    calc
      (c + e + T + J) / b =
          (c + e) / b + (T + J) / b := by ring
      _ ≤ ((c + e) / b) * P + (d / b) * (T + J) :=
        add_le_add hPpart hTJpart
      _ = E + L := by rw [hEidentity, hLidentity]; ring

  have hBase :
      1 + K + T + Z + (c + e + T + J) / b ≤
        U + T + E + L + Z + F := by
    linarith [hEarBase, hEL]
  have hJnum :
      c + e + T + (b + e + 1) ≤ c + e + T + J := by
    linarith
  have hJdiv :
      (c + e + T + (b + e + 1)) / b ≤
        (c + e + T + J) / b :=
    div_le_div_of_nonneg_right hJnum (le_of_lt hb)
  have hMaster :
      2 + (K + Z) + T + (c + 2 * e + T + 1) / b ≤
        U + T + E + L + Z + F := by
    have hid :
        2 + (K + Z) + T + (c + 2 * e + T + 1) / b =
          1 + K + T + Z +
            (c + e + T + (b + e + 1)) / b := by
      field_simp [hb.ne']
      <;> ring
    rw [hid]
    linarith [hJdiv, hBase]

  have hJscaled :
      (c / e) * (b + e + 1) ≤ (c / e) * J :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hWscaled :
      (b / e) * W ≤ (b / e) * (c + e - 1) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have hBT : c + c / e + b / e ≤ b + T := by
    calc
      c + c / e + b / e =
          b + (c / e) * (b + e + 1) -
            (b / e) * (c + e - 1) := by
        field_simp [he.ne']
        <;> ring
      _ ≤ b + (c / e) * J - (b / e) * W := by linarith
      _ = b + T := by rw [hTidentity]; ring

  have hDscaled :
      (e / c) * (c + f + 1) ≤ (e / c) * D :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hWscaled' :
      (f / c) * W ≤ (f / c) * (c + e - 1) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have hFZ : e + (e + f) / c ≤ f + Z := by
    calc
      e + (e + f) / c =
          f + (e / c) * (c + f + 1) -
            (f / c) * (c + e - 1) := by
        field_simp [hc.ne']
        <;> ring
      _ ≤ f + (e / c) * D - (f / c) * W := by linarith
      _ = f + Z := by rw [hZidentity]; ring

  have hJscaled' :
      (f / e) * (b + e + 1) ≤ (f / e) * J :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hKZraw :
      (f + Z) * (1 + b / e) + f / e ≤ K + Z := by
    calc
      (f + Z) * (1 + b / e) + f / e =
          (f / e) * (b + e + 1) + (b / e) * Z + Z := by
        field_simp [he.ne']
        <;> ring
      _ ≤ (f / e) * J + (b / e) * Z + Z := by linarith
      _ = K + Z := by rw [hKidentity]
  have hFZscaled :
      (e + (e + f) / c) * (1 + b / e) ≤
        (f + Z) * (1 + b / e) :=
    mul_le_mul_of_nonneg_right hFZ (by positivity)
  have hRaw :
      (e + (e + f) / c) * (1 + b / e) + f / e ≤ K + Z := by
    linarith [hFZscaled, hKZraw]
  have hcoef : 0 ≤ 1 / c + b / (e * c) + 1 / e := by positivity
  have hfdiff :
      0 ≤ (f - 1) * (1 / c + b / (e * c) + 1 / e) :=
    mul_nonneg (sub_nonneg.mpr hf1) hcoef
  have hRawSplit :
      (e + (e + f) / c) * (1 + b / e) + f / e =
        e + b + (e + 1) / c + b * (e + 1) / (e * c) + 1 / e +
          (f - 1) * (1 / c + b / (e * c) + 1 / e) := by
    field_simp [he.ne', hc.ne']
    <;> ring
  have hKZ :
      e + b + (e + 1) / c + b * (e + 1) / (e * c) + 1 / e ≤
        K + Z := by
    rw [hRawSplit] at hRaw
    linarith

  have hTdiv : 1 / b ≤ T / b :=
    div_le_div_of_nonneg_right hT (le_of_lt hb)
  have hKT :
      e + (e + 1) / c + b * (e + 1) / (e * c) + 1 / e +
          c + c / e + b / e ≤
        K + Z + T := by
    linarith [hKZ, hBT]
  have hMaster' :
      2 + K + Z + T + c / b + 2 * e / b + T / b + 1 / b ≤
        U + T + E + L + Z + F := by
    calc
      2 + K + Z + T + c / b + 2 * e / b + T / b + 1 / b =
          2 + (K + Z) + T + (c + 2 * e + T + 1) / b := by
        field_simp [hb.ne']
        <;> ring
      _ ≤ U + T + E + L + Z + F := hMaster

  let G : ℝ :=
    2 + e + 1 / e + c + c / e + b / e + (e + 1) / c +
      b * (e + 1) / (e * c) + c / b + 2 * e / b + 2 / b
  have htwo : 2 / b ≤ T / b + 1 / b := by
    calc
      2 / b = 1 / b + 1 / b := by ring
      _ ≤ T / b + 1 / b := add_le_add_left hTdiv _
  have hGtoMaster :
      G ≤ 2 + K + Z + T + c / b + 2 * e / b + T / b + 1 / b := by
    dsimp [G]
    calc
      2 + e + 1 / e + c + c / e + b / e + (e + 1) / c +
            b * (e + 1) / (e * c) + c / b + 2 * e / b + 2 / b =
          (2 + c / b + 2 * e / b) +
            ((e + (e + 1) / c + b * (e + 1) / (e * c) + 1 / e +
                c + c / e + b / e) + 2 / b) := by ring
      _ ≤ (2 + c / b + 2 * e / b) +
            ((K + Z + T) + (T / b + 1 / b)) :=
        by
          convert add_le_add (le_refl (2 + c / b + 2 * e / b))
            (add_le_add hKT htwo) using 1 <;> ring
      _ = 2 + K + Z + T + c / b + 2 * e / b + T / b + 1 / b := by
        ring
  have hG : G ≤ U + T + E + L + Z + F := by
    exact hGtoMaster.trans hMaster'

  have hePair : 2 ≤ e + 1 / e := by
    simpa using hullSixThreeThreeQ112_reciprocalPair he
      (by norm_num : (0 : ℝ) < 1)
  have hcePair : 2 ≤ c / e + e / c :=
    hullSixThreeThreeQ112_reciprocalPair hc he
  have hbcPair : 2 ≤ b / c + c / b :=
    hullSixThreeThreeQ112_reciprocalPair hb hc
  have hbePair : 2 ≤ b / e + e / b :=
    hullSixThreeThreeQ112_reciprocalPair hb he

  have hpoly : 0 ≤ (b - e) ^ 2 + e ^ 2 * (c - 1) :=
    add_nonneg (sq_nonneg (b - e))
      (mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hc1))
  have hquot :
      0 ≤ ((b - e) ^ 2 + e ^ 2 * (c - 1)) / (b * e * c) :=
    div_nonneg hpoly (le_of_lt (mul_pos (mul_pos hb he) hc))
  have hquotIdentity :
      ((b - e) ^ 2 + e ^ 2 * (c - 1)) / (b * e * c) =
        b / (e * c) + e / b - 2 / c := by
    field_simp [hb.ne', he.ne', hc.ne']
    <;> ring
  rw [hquotIdentity] at hquot
  have htwoOver : 2 / c ≤ b / (e * c) + e / b := by linarith

  have hcquad : 0 < c ^ 2 - (5 / 2 : ℝ) * c + 2 := by
    nlinarith [sq_nonneg (4 * c - 5)]
  have hcquot : 0 < (c ^ 2 - (5 / 2 : ℝ) * c + 2) / c :=
    div_pos hcquad hc
  have hcquotIdentity :
      (c ^ 2 - (5 / 2 : ℝ) * c + 2) / c =
        c + 2 / c - 5 / 2 := by
    field_simp [hc.ne']
    <;> ring
  rw [hcquotIdentity] at hcquot
  have hTriple :
      (5 : ℝ) / 2 < c + e / b + b / (e * c) := by
    linarith [htwoOver, hcquot]
  have hRemainder : 0 ≤ 1 / c + 2 / b := by positivity
  have hGexpand :
      G = 2 + (e + 1 / e) + (c / e + e / c) +
        (b / c + c / b) + (b / e + e / b) +
          (c + e / b + b / (e * c)) + (1 / c + 2 / b) := by
    dsimp [G]
    field_simp [hb.ne', hc.ne', he.ne']
    <;> ring
  have hGstrict : (25 : ℝ) / 2 < G := by
    rw [hGexpand]
    linarith [hePair, hcePair, hbcPair, hbePair, hTriple, hRemainder]

  have hFinal :
      (25 : ℝ) / 2 < U + T + E + L + Z + F :=
    hGstrict.trans_le hG
  simpa [U, T, E, L, Z, F] using hFinal

end Heilbronn8
