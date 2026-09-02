import Heilbronn8.V8
import Heilbronn8.TriHull.HullSevenEndpointHighPoint

/-!
# Compact scalar closure for the c-positive hull-seven type 1 chamber

This file contains no finite search and no generated certificate bank.  It
separates the proof into three small interfaces.

* `HullSevenType1ThresholdData` is the topology-free output of the endpoint
  threshold construction.  Its two inequalities force `q > 157 / 50`.
* `HullSevenType1EndpointInput` records the five Pluecker/cap facts needed to
  derive the strong additive endpoint inequality.  The bracket dictionary is

```text
a=d01, A=d12, B=d23, C=d34, D=d45, z=d56, G=-d06,
q=d24, R=d25, r=d35, c=d15, m=d26, n=d05, h=-d16.
```

  Thus rows `(1,2,5,6)` and `(0,1,5,6)` give `Az=cm+Rh` and
  `cG=az+nh`.  Row `(2,3,4,5)` gives `CR=qr-DB`; the ear
  `[D3,D4,D5] >= 1` gives `r <= C+D-1`; and row `(2,4,5,6)`
  together with `[D4,D5,D6] >= 1` gives
  `Dm+zq <= R(z+D-1)`.
* `HullSevenType1ScalarData` contains exactly the inequalities consumed by
  the final rational supporting-plane proof.

The full additive endpoint inequality is intentionally retained.  Its much
coarser four-term AM--GM consequence does not by itself imply the desired
area bound.
-/

namespace Heilbronn8.TriHull

set_option maxHeartbeats 800000

/-! ## The topology-free threshold seam -/

/--
Output expected from the high-point/endpoint threshold argument.

Writing `s=A-1`, `u=D-1`, `r=q-1`, the first field is
`s+u <= r*s*u`.  The second field is the compact `P+` inequality.  It can be
produced without hull topology: if positive `t,w` satisfy `t+w <= r`,
`L(1+t)=t(A+q)`, `R(1+w)=w(D+q)`, and `AD+q <= LR`, then elementary AM--GM
gives precisely the displayed inequality.
-/
structure HullSevenType1ThresholdData (A D q : ℝ) : Prop where
  A_gt : 1 < A
  D_gt : 1 < D
  interval :
    (A - 1) + (D - 1) ≤ (q - 1) * (A - 1) * (D - 1)
  pplus :
    4 * (A * D + q) ≤ (q - 1) ^ 2 * (A + D + q - 1)

/-- Exact rational consequence of the interval and `P+` inequalities. -/
theorem hullSevenType1_q_gt_157_div_50
    {A D q : ℝ} (T : HullSevenType1ThresholdData A D q) :
    (157 : ℝ) / 50 < q := by
  let s := A - 1
  let u := D - 1
  let r := q - 1
  let x := s + u
  let j := s * u
  have hs : 0 < s := by simpa [s] using sub_pos.mpr T.A_gt
  have hu : 0 < u := by simpa [u] using sub_pos.mpr T.D_gt
  have hx : 0 < x := by exact add_pos hs hu
  have hj : 0 < j := by exact mul_pos hs hu
  have hinterval : x ≤ r * j := by
    simpa [s, u, r, x, j, mul_assoc] using T.interval
  have hK : A * D + q = j + x + r + 2 := by
    dsimp [s, u, r, x, j]
    ring
  have hS : A + D + q - 1 = x + r + 2 := by
    dsimp [s, u, r, x]
    ring
  have hp := T.pplus
  rw [hK, hS] at hp
  have hP : 4 * j ≤ (r ^ 2 - 4) * (x + r + 2) := by
    nlinarith [hp]
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r ≤ 0 := le_of_not_gt hnot
    have hrj0 : r * j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr0 hj.le
    linarith
  have hrTwo : 2 < r := by
    by_contra hnot
    have hrle : r ≤ 2 := le_of_not_gt hnot
    have hrsq : r ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hrle)]
    have hfac : r ^ 2 - 4 ≤ 0 := by linarith
    have hsum : 0 ≤ x + r + 2 := by positivity
    have hleft : (r ^ 2 - 4) * (x + r + 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hfac hsum
    nlinarith
  have hxsq : 4 * j ≤ x ^ 2 := by
    dsimp [x, j]
    nlinarith [sq_nonneg (s - u)]
  have hrx : 4 ≤ r * x := by
    have hxmul := mul_le_mul_of_nonneg_right hinterval hx.le
    have hscaled : 4 * j ≤ r * j * x := by
      calc
        4 * j ≤ x ^ 2 := hxsq
        _ = x * x := by ring
        _ ≤ r * j * x := hxmul
    have hscaled' : j * 4 ≤ j * (r * x) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
    exact (mul_le_mul_iff_of_pos_left hj).mp hscaled'
  have hbase :
      0 ≤ x * (r ^ 3 - 4 * r - 4) +
        r * (r ^ 2 - 4) * (r + 2) := by
    have hfour := mul_le_mul_of_nonneg_left hinterval
      (by norm_num : (0 : ℝ) ≤ 4)
    have hPr := mul_le_mul_of_nonneg_left hP hr.le
    have hchain : 4 * x ≤ r * ((r ^ 2 - 4) * (x + r + 2)) := by
      calc
        4 * x ≤ 4 * (r * j) := hfour
        _ = r * (4 * j) := by ring
        _ ≤ r * ((r ^ 2 - 4) * (x + r + 2)) := hPr
    nlinarith [hchain]
  by_contra hnot
  have hqle : q ≤ (157 : ℝ) / 50 := le_of_not_gt hnot
  have hrle : r ≤ (107 : ℝ) / 50 := by
    dsimp [r]
    linarith
  let cpoly := r ^ 3 - 4 * r - 4
  have hcneg : cpoly < 0 := by
    let b : ℝ := 107 / 50
    have hrb : r ≤ b := by simpa [b] using hrle
    have hrsq : 4 < r ^ 2 := by
      have hm : 0 < (r - 2) * (r + 2) := by positivity
      nlinarith
    have hbracket : 0 ≤ b ^ 2 + b * r + r ^ 2 - 4 := by
      have hbr : 0 ≤ b * r := by positivity
      nlinarith
    have hprod : 0 ≤ (b - r) * (b ^ 2 + b * r + r ^ 2 - 4) :=
      mul_nonneg (sub_nonneg.mpr hrb) hbracket
    have hfactor :
        (b ^ 3 - 4 * b - 4) - cpoly =
          (b - r) * (b ^ 2 + b * r + r ^ 2 - 4) := by
      dsimp [cpoly]
      ring
    have hcle : cpoly ≤ b ^ 3 - 4 * b - 4 := by
      nlinarith [hfactor, hprod]
    have hcb : b ^ 3 - 4 * b - 4 < 0 := by norm_num [b]
    exact lt_of_le_of_lt hcle hcb
  have hbaseScaled := mul_nonneg hr.le hbase
  have hcScaled : (r * x) * cpoly ≤ 4 * cpoly :=
    mul_le_mul_of_nonpos_right hrx hcneg.le
  have hpnonneg :
      0 ≤ r ^ 5 + 2 * r ^ 4 - 8 * r ^ 2 - 16 * r - 16 := by
    dsimp [cpoly] at hcScaled
    nlinarith [hbaseScaled, hcScaled]
  let y := r - 2
  let b : ℝ := 7 / 50
  have hy : 0 < y := by dsimp [y]; linarith
  have hyb : y ≤ b := by dsimp [y, b]; linarith
  let S : ℝ :=
    b ^ 4 + b ^ 3 * y + b ^ 2 * y ^ 2 + b * y ^ 3 + y ^ 4 +
      12 * (b ^ 3 + b ^ 2 * y + b * y ^ 2 + y ^ 3) +
      56 * (b ^ 2 + b * y + y ^ 2) + 120 * (b + y) + 96
  have hSpos : 0 < S := by
    dsimp [S, b]
    positivity
  have hdiff : 0 ≤ (b - y) * S :=
    mul_nonneg (sub_nonneg.mpr hyb) hSpos.le
  have hfactor :
      (b ^ 5 + 12 * b ^ 4 + 56 * b ^ 3 + 120 * b ^ 2 + 96 * b - 16) -
        (y ^ 5 + 12 * y ^ 4 + 56 * y ^ 3 + 120 * y ^ 2 + 96 * y - 16) =
          (b - y) * S := by
    dsimp [S]
    ring
  have hpyle :
      y ^ 5 + 12 * y ^ 4 + 56 * y ^ 3 + 120 * y ^ 2 + 96 * y - 16 ≤
        b ^ 5 + 12 * b ^ 4 + 56 * b ^ 3 + 120 * b ^ 2 + 96 * b - 16 := by
    nlinarith [hfactor, hdiff]
  have hpshift :
      r ^ 5 + 2 * r ^ 4 - 8 * r ^ 2 - 16 * r - 16 =
        y ^ 5 + 12 * y ^ 4 + 56 * y ^ 3 + 120 * y ^ 2 + 96 * y - 16 := by
    dsimp [y]
    ring
  have hpb :
      b ^ 5 + 12 * b ^ 4 + 56 * b ^ 3 + 120 * b ^ 2 + 96 * b - 16 < 0 := by
    norm_num [b]
  rw [hpshift] at hpnonneg
  linarith

/-! ## Exact determinant/chord adapter for the additive endpoint -/

/-- Minimal signed-bracket and cap data used at the right endpoint. -/
structure HullSevenType1EndpointInput where
  a : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  z : ℝ
  G : ℝ
  q : ℝ
  R : ℝ
  r : ℝ
  c : ℝ
  m : ℝ
  n : ℝ
  h : ℝ
  a_ge : 1 ≤ a
  B_ge : 1 ≤ B
  C_ge : 1 ≤ C
  D_ge : 1 ≤ D
  z_ge : 1 ≤ z
  G_ge : 1 ≤ G
  q_ge : 1 ≤ q
  m_ge : 1 ≤ m
  n_ge : 1 ≤ n
  h_ge : 1 ≤ h
  plucker1256 : A * z = c * m + R * h
  plucker0156 : c * G = a * z + n * h
  plucker2345 : C * R = q * r - D * B
  right_ear : r ≤ C + D - 1
  right_cap : D * m + z * q ≤ R * (z + D - 1)

/-- The right recurrence and the terminal-ear cap imply `R >= 1+q/D`. -/
private theorem hullSevenType1_right_endpoint_lower
    (X : HullSevenType1EndpointInput) : 1 + X.q / X.D ≤ X.R := by
  have hD0 : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
  have hC0 : 0 < X.C := lt_of_lt_of_le (by norm_num) X.C_ge
  have hq0 : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hupper :
      X.C * X.R ≤ X.q * (X.C + X.D - 1) - X.D * X.B := by
    have hm := mul_le_mul_of_nonneg_left X.right_ear hq0.le
    nlinarith [X.plucker2345]
  have hDm : X.D ≤ X.D * X.m := by
    nlinarith [mul_nonneg (le_trans (by norm_num) X.D_ge)
      (sub_nonneg.mpr X.m_ge)]
  have horiginal :
      X.D + X.z * X.q ≤ X.R * (X.z + X.D - 1) :=
    le_trans (by linarith) X.right_cap
  have hbase : 0 ≤ (X.R - X.q) + X.R * (X.D - 1) - X.D := by
    by_contra hnot
    have hfail : (X.R - X.q) + X.R * (X.D - 1) - X.D < 0 :=
      lt_of_not_ge hnot
    have horiginal' :
        0 ≤ X.z * (X.R - X.q) + X.R * (X.D - 1) - X.D := by
      nlinarith [horiginal]
    have hsplit :
        X.z * (X.R - X.q) + X.R * (X.D - 1) - X.D =
          ((X.R - X.q) + X.R * (X.D - 1) - X.D) +
            (X.z - 1) * (X.R - X.q) := by ring
    have hprod : 0 < (X.z - 1) * (X.R - X.q) := by
      rw [hsplit] at horiginal'
      linarith
    have hRq : X.q < X.R := by
      rcases (mul_pos_iff.mp hprod) with hpos | hneg
      · exact sub_pos.mp hpos.2
      · exfalso
        linarith [X.z_ge, hneg.1]
    have hqC : X.q * X.C < X.R * X.C :=
      mul_lt_mul_of_pos_right hRq hC0
    have hbig : X.D * X.B < X.q * (X.D - 1) := by
      nlinarith [hupper, hqC]
    have hDB : X.D ≤ X.D * X.B := by
      nlinarith [mul_nonneg (le_trans (by norm_num) X.D_ge)
        (sub_nonneg.mpr X.B_ge)]
    have hqD : X.q * X.D < X.R * X.D :=
      mul_lt_mul_of_pos_right hRq hD0
    have hsmall : X.q * (X.D - 1) < X.D := by
      nlinarith [hqD, hfail]
    linarith
  rw [show 1 + X.q / X.D = (X.D + X.q) / X.D by
    field_simp [hD0.ne']]
  exact (div_le_iff₀ hD0).2 (by nlinarith [hbase])

/--
The two signed Pluecker rows, normalized floors, and the right endpoint cap
produce the additive inequality consumed by the scalar proof.
-/
theorem hullSevenType1_endpoint_inequality
    (X : HullSevenType1EndpointInput) :
    X.G * (1 + X.q / X.D) + X.a * X.z + 1 ≤ X.A * X.z * X.G := by
  have hRlower := hullSevenType1_right_endpoint_lower X
  have ha0 : 0 ≤ X.a := le_trans (by norm_num) X.a_ge
  have hz0 : 0 ≤ X.z := le_trans (by norm_num) X.z_ge
  have hG0 : 0 ≤ X.G := le_trans (by norm_num) X.G_ge
  have hq0 : 0 ≤ X.q := le_trans (by norm_num) X.q_ge
  have hD0 : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
  have hR0 : 0 ≤ X.R := by
    have : 0 ≤ 1 + X.q / X.D := by positivity
    exact le_trans this hRlower
  have haz : X.a * X.z ≤ X.m * (X.a * X.z) := by
    have hm := mul_le_mul_of_nonneg_right X.m_ge (mul_nonneg ha0 hz0)
    nlinarith
  have hmn : 1 ≤ X.m * X.n := by
    calc
      1 ≤ X.n := X.n_ge
      _ ≤ X.m * X.n := by
        simpa using mul_le_mul_of_nonneg_right X.m_ge
          (le_trans (by norm_num) X.n_ge)
  have hmnh : 1 ≤ X.m * X.n * X.h := by
    have hm := mul_le_mul_of_nonneg_left X.h_ge
      (le_trans (by norm_num) hmn)
    nlinarith
  have hRhG : X.R * X.G ≤ X.R * X.h * X.G := by
    have hm := mul_le_mul_of_nonneg_right X.h_ge hR0
    have hm' := mul_le_mul_of_nonneg_right hm hG0
    nlinarith
  have hRG : X.G * (1 + X.q / X.D) ≤ X.R * X.G := by
    have hm := mul_le_mul_of_nonneg_right hRlower hG0
    nlinarith
  have hidentity :
      X.A * X.z * X.G =
        X.m * (X.a * X.z + X.n * X.h) + X.R * X.h * X.G := by
    calc
      X.A * X.z * X.G = (X.c * X.m + X.R * X.h) * X.G := by
        rw [X.plucker1256]
      _ = X.m * (X.c * X.G) + X.R * X.h * X.G := by ring
      _ = X.m * (X.a * X.z + X.n * X.h) + X.R * X.h * X.G := by
        rw [X.plucker0156]
  rw [hidentity]
  nlinarith [haz, hmnh, hRhG, hRG]

/-! ## The rational supporting-plane finish -/

/-- Three-term AM--GM in the ratio form used by the reciprocal tangent. -/
private lemma hullSevenType1_amgm3_ratio
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    3 * p * q ≤ 1 + p ^ 2 * q + p * q ^ 2 := by
  suffices 0 ≤ 1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q by linarith
  by_cases hp1 : 1 ≤ p
  · by_cases hq1 : 1 ≤ q
    · rw [show 1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q =
          (p - 1) ^ 2 + (p - 1) * (q - 1) + (q - 1) ^ 2 +
            (p - 1) ^ 2 * (q - 1) + (p - 1) * (q - 1) ^ 2 by ring]
      positivity
    · have hq1' : q ≤ 1 := le_of_not_ge hq1
      have hid : 4 * (1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q) =
          q * (2 * p + q - 3) ^ 2 + (1 - q) ^ 2 * (4 - q) := by ring
      have hfour : 0 ≤ 4 - q := by linarith
      have hrhs : 0 ≤ q * (2 * p + q - 3) ^ 2 + (1 - q) ^ 2 * (4 - q) := by
        positivity
      nlinarith
  · have hp1' : p ≤ 1 := le_of_not_ge hp1
    by_cases hq1 : 1 ≤ q
    · have hid : 4 * (1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q) =
          p * (p + 2 * q - 3) ^ 2 + (1 - p) ^ 2 * (4 - p) := by ring
      have hfour : 0 ≤ 4 - p := by linarith
      have hrhs : 0 ≤ p * (p + 2 * q - 3) ^ 2 + (1 - p) ^ 2 * (4 - p) := by
        positivity
      nlinarith
    · have hq1' : q ≤ 1 := le_of_not_ge hq1
      rw [show 1 + p ^ 2 * q + p * q ^ 2 - 3 * p * q =
          (1 - p) ^ 2 * q + (1 - q) ^ 2 * p + (1 - p) * (1 - q) by ring]
      positivity

/-- Global tangent inequality for the reciprocal function. -/
private lemma hullSevenType1_inv_tangent
    {u u0 : ℝ} (hu : 0 < u) (hu0 : 0 < u0) :
    2 / u0 - u / u0 ^ 2 ≤ 1 / u := by
  have hs := sq_nonneg (u - u0)
  field_simp
  nlinarith

/-- Global supporting plane for `(u,v) |-> 1/(u*v)`. -/
private lemma hullSevenType1_invMul_tangent
    {u v u0 v0 : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hu0 : 0 < u0) (hv0 : 0 < v0) :
    3 / (u0 * v0) - u / (u0 ^ 2 * v0) - v / (u0 * v0 ^ 2) ≤
      1 / (u * v) := by
  have hp : 0 < u / u0 := div_pos hu hu0
  have hq : 0 < v / v0 := div_pos hv hv0
  have hamgm := hullSevenType1_amgm3_ratio hp hq
  field_simp at hamgm ⊢
  nlinarith

/-- Exactly the scalar inequalities used by the final type-1 closure. -/
structure HullSevenType1ScalarData (H : ℝ) where
  a : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  z : ℝ
  q : ℝ
  G : ℝ
  a_ge : 1 ≤ a
  z_ge : 1 ≤ z
  G_ge : 1 ≤ G
  threshold : HullSevenType1ThresholdData A D q
  q_ear : q ≤ B + C - 1
  endpoint : G * (1 + q / D) + a * z + 1 ≤ A * z * G
  area : a + A + B + C + D + z + G ≤ H

/-- The compact, certificate-free scalar theorem for hull-seven type 1. -/
theorem hullSevenType1_area_gt
    {H : ℝ} (X : HullSevenType1ScalarData H) : (25 : ℝ) / 2 < H := by
  have hq := hullSevenType1_q_gt_157_div_50 X.threshold
  have hD : 0 < X.D := lt_trans (by norm_num) X.threshold.D_gt
  have hz : 0 < X.z := lt_of_lt_of_le (by norm_num) X.z_ge
  have hG : 0 < X.G := lt_of_lt_of_le (by norm_num) X.G_ge
  have ha0 : 0 ≤ X.a := le_trans (by norm_num) X.a_ge
  have hz0 : 0 ≤ X.z := hz.le
  have hG0 : 0 ≤ X.G := hG.le
  have hqG : ((157 : ℝ) / 50) * X.G ≤ X.q * X.G :=
    mul_le_mul_of_nonneg_right hq.le hG0
  have hDz : X.D * X.z ≤ X.D * X.a * X.z := by
    have hm := mul_le_mul_of_nonneg_left X.a_ge hD.le
    have hm' := mul_le_mul_of_nonneg_right hm hz0
    nlinarith
  have hendpointCleared :
      X.D * X.G + ((157 : ℝ) / 50) * X.G + X.D * X.z + X.D ≤
        X.A * X.D * X.z * X.G := by
    have hm := mul_le_mul_of_nonneg_left X.endpoint hD.le
    have hm' :
        X.D * X.G + X.q * X.G + X.D * X.a * X.z + X.D ≤
          X.A * X.D * X.z * X.G := by
      calc
        X.D * X.G + X.q * X.G + X.D * X.a * X.z + X.D =
            X.D * (X.G * (1 + X.q / X.D) + X.a * X.z + 1) := by
              field_simp [hD.ne']
        _ ≤ X.D * (X.A * X.z * X.G) := hm
        _ = X.A * X.D * X.z * X.G := by ring
    nlinarith [hm', hqG, hDz]
  have hreciprocal :
      1 / X.z + 1 / X.G + ((157 : ℝ) / 50) / (X.D * X.z) +
          1 / (X.z * X.G) ≤ X.A := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos (mul_pos hD hz) hG)).mp
    have hid :
        (1 / X.z + 1 / X.G + ((157 : ℝ) / 50) / (X.D * X.z) +
            1 / (X.z * X.G)) * (X.D * X.z * X.G) =
          X.D * X.G + ((157 : ℝ) / 50) * X.G + X.D * X.z + X.D := by
      field_simp [hD.ne', hz.ne', hG.ne']
      ring
    rw [hid]
    nlinarith [hendpointCleared]
  have hzTan := hullSevenType1_inv_tangent hz
    (by norm_num : (0 : ℝ) < 21 / 10)
  have hGTan := hullSevenType1_inv_tangent hG
    (by norm_num : (0 : ℝ) < 5 / 4)
  have hDzTan0 := hullSevenType1_invMul_tangent hD hz
    (by norm_num : (0 : ℝ) < 5 / 4)
    (by norm_num : (0 : ℝ) < 21 / 10)
  have hDzTan := mul_le_mul_of_nonneg_left hDzTan0
    (by norm_num : (0 : ℝ) ≤ 157 / 50)
  have hzGTan := hullSevenType1_invMul_tangent hz hG
    (by norm_num : (0 : ℝ) < 21 / 10)
    (by norm_num : (0 : ℝ) < 5 / 4)
  have hzTan' :
      (20 : ℝ) / 21 - (100 : ℝ) / 441 * X.z ≤ 1 / X.z := by
    norm_num at hzTan ⊢
    nlinarith [hzTan]
  have hGTan' :
      (8 : ℝ) / 5 - (16 : ℝ) / 25 * X.G ≤ 1 / X.G := by
    norm_num at hGTan ⊢
    nlinarith [hGTan]
  have hDzTan' :
      (628 : ℝ) / 175 - (2512 : ℝ) / 2625 * X.D -
          (1256 : ℝ) / 2205 * X.z ≤
        ((157 : ℝ) / 50) / (X.D * X.z) := by
    calc
      (628 : ℝ) / 175 - (2512 : ℝ) / 2625 * X.D -
          (1256 : ℝ) / 2205 * X.z =
        ((157 : ℝ) / 50) *
          (3 / ((5 : ℝ) / 4 * ((21 : ℝ) / 10)) -
            X.D / (((5 : ℝ) / 4) ^ 2 * ((21 : ℝ) / 10)) -
            X.z / ((5 : ℝ) / 4 * ((21 : ℝ) / 10) ^ 2)) := by ring
      _ ≤ ((157 : ℝ) / 50) * (1 / (X.D * X.z)) := hDzTan
      _ = ((157 : ℝ) / 50) / (X.D * X.z) := by ring
  have hzGTan' :
      (8 : ℝ) / 7 - (80 : ℝ) / 441 * X.z -
          (32 : ℝ) / 105 * X.G ≤ 1 / (X.z * X.G) := by
    norm_num at hzGTan ⊢
    nlinarith [hzGTan]
  have hsupport :
      (3824 : ℝ) / 525 + X.z / 45 + 29 * X.G / 525 +
          113 * X.D / 2625 ≤
        X.D + X.z + X.G + 1 / X.z + 1 / X.G +
          ((157 : ℝ) / 50) / (X.D * X.z) + 1 / (X.z * X.G) := by
    linarith [hzTan', hGTan', hDzTan', hzGTan']
  have hfloorSupport :
      (58309 : ℝ) / 7875 ≤
        X.D + X.z + X.G + 1 / X.z + 1 / X.G +
          ((157 : ℝ) / 50) / (X.D * X.z) + 1 / (X.z * X.G) := by
    nlinarith [hsupport, X.z_ge, X.G_ge, X.threshold.D_gt.le]
  have hADzG : (58309 : ℝ) / 7875 ≤ X.A + X.D + X.z + X.G := by
    linarith [hfloorSupport, hreciprocal]
  have hgap : (184 : ℝ) / 25 < (58309 : ℝ) / 7875 := by norm_num
  have hmiddle : X.q + 1 ≤ X.B + X.C := by linarith [X.q_ear]
  have htotal : (25 : ℝ) / 2 < X.a + X.A + X.B + X.C + X.D + X.z + X.G := by
    nlinarith [X.a_ge, hq, hmiddle, hADzG, hgap]
  exact lt_of_lt_of_le htotal X.area

/-! ## Determinant-only combined input -/

/--
Complete scalar projection of the normalized type-1 bracket chamber.

All fields are determinant identities, triangle floors, or hull-triangle cap
inequalities.  In particular, the high-point parameters used to prove `P+`
are *not* fields: `hullSeven_endpointHighPoint` constructs them from the two
endpoint recurrence/cap packets below.

The sign packet is the unique nonreflected type-1 presentation: every listed
magnitude is positive, while `d06=-G` and `d16=-h`.  The central Pluecker row
has the positive form `L*R=A*D+c*q`.
-/
structure HullSevenType1ChordInput (H : ℝ) where
  a : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  z : ℝ
  G : ℝ
  p : ℝ
  q : ℝ
  r : ℝ
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
  r_ge : 1 ≤ r
  L_ge : 1 ≤ L
  R_ge : 1 ≤ R
  c_ge : 1 ≤ c
  l_ge : 1 ≤ l
  m_ge : 1 ≤ m
  n_ge : 1 ≤ n
  h_ge : 1 ≤ h
  p_ear : p ≤ A + B - 1
  q_ear : q ≤ B + C - 1
  r_ear : r ≤ C + D - 1
  plucker_L : B * L = q * p - A * C
  plucker_R : C * R = q * r - D * B
  left_endpoint : A * l + a * q ≤ L * (a + A - 1)
  right_endpoint : D * m + z * q ≤ R * (z + D - 1)
  plucker_central : L * R = A * D + c * q
  plucker1256 : A * z = c * m + R * h
  plucker0156 : c * G = a * z + n * h
  area : a + A + B + C + D + z + G ≤ H

/-- Forget everything except the endpoint recurrence/cap packet. -/
def HullSevenType1ChordInput.toEndpointHighPointInput
    {H : ℝ} (X : HullSevenType1ChordInput H) :
    HullSevenEndpointHighPointInput where
  a0 := X.a
  A := X.A
  B := X.B
  C := X.C
  D := X.D
  a5 := X.z
  p := X.p
  q := X.q
  r := X.r
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
  r_ge := X.r_ge
  L_ge := X.L_ge
  R_ge := X.R_ge
  l_ge := X.l_ge
  m_ge := X.m_ge
  p_ear := X.p_ear
  q_ear := X.q_ear
  r_ear := X.r_ear
  L_rec := X.plucker_L
  R_rec := X.plucker_R
  left_endpoint := X.left_endpoint
  right_endpoint := X.right_endpoint

/-- Forget everything except the two endpoint Pluecker rows and right cap. -/
def HullSevenType1ChordInput.toEndpointInput
    {H : ℝ} (X : HullSevenType1ChordInput H) :
    HullSevenType1EndpointInput where
  a := X.a
  A := X.A
  B := X.B
  C := X.C
  D := X.D
  z := X.z
  G := X.G
  q := X.q
  R := X.R
  r := X.r
  c := X.c
  m := X.m
  n := X.n
  h := X.h
  a_ge := X.a_ge
  B_ge := X.B_ge
  C_ge := X.C_ge
  D_ge := X.D_ge
  z_ge := X.z_ge
  G_ge := X.G_ge
  q_ge := X.q_ge
  m_ge := X.m_ge
  n_ge := X.n_ge
  h_ge := X.h_ge
  plucker1256 := X.plucker1256
  plucker0156 := X.plucker0156
  plucker2345 := X.plucker_R
  right_ear := X.r_ear
  right_cap := X.right_endpoint

/--
The determinant/cap input produces both threshold inequalities.  The interval
comes from the two outer floors of the constructed high point.  For `P+`, the
positive central row gives `AD+q <= LR`; multiplying the high-point chord
bounds and using `4tw <= (t+w)^2` gives the displayed quadratic inequality.
-/
theorem HullSevenType1ChordInput.toThresholdData
    {H : ℝ} (X : HullSevenType1ChordInput H) :
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
      simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
        P.left_outer
    linarith
  have hDgt : 1 < X.D := by
    by_contra hnot
    have hD : X.D - 1 ≤ 0 := by linarith
    have hm : (X.D - 1) * P.w ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hD hw.le
    have hout : 1 ≤ (X.D - 1) * P.w := by
      simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
        P.right_outer
    linarith
  have hs : 0 < X.A - 1 := sub_pos.mpr hAgt
  have hu : 0 < X.D - 1 := sub_pos.mpr hDgt
  have htLower : 1 / (X.A - 1) ≤ P.t := by
    apply (div_le_iff₀ hs).2
    have hout : 1 ≤ (X.A - 1) * P.t := by
      simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
        P.left_outer
    simpa [mul_comm] using hout
  have hwLower : 1 / (X.D - 1) ≤ P.w := by
    apply (div_le_iff₀ hu).2
    have hout : 1 ≤ (X.D - 1) * P.w := by
      simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
        P.right_outer
    simpa [mul_comm] using hout
  have hsum : P.t + P.w = X.q - 1 := by
    simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
      P.sum_eq
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
    nlinarith [X.plucker_central, hcq]
  have hleft : X.L * (1 + P.t) ≤ P.t * (X.A + X.q) := by
    simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
      P.left_scaled
  have hright : X.R * (1 + P.w) ≤ P.w * (X.D + X.q) := by
    simpa [Y, HullSevenType1ChordInput.toEndpointHighPointInput] using
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

/-- The combined determinant/cap input supplies the exact scalar payload. -/
noncomputable def HullSevenType1ChordInput.toScalarData
    {H : ℝ} (X : HullSevenType1ChordInput H) : HullSevenType1ScalarData H where
  a := X.a
  A := X.A
  B := X.B
  C := X.C
  D := X.D
  z := X.z
  q := X.q
  G := X.G
  a_ge := X.a_ge
  z_ge := X.z_ge
  G_ge := X.G_ge
  threshold := X.toThresholdData
  q_ear := X.q_ear
  endpoint := hullSevenType1_endpoint_inequality X.toEndpointInput
  area := X.area

/-- End-to-end strict area bound from determinant identities and hull caps. -/
theorem hullSevenType1_area_gt_of_chord
    {H : ℝ} (X : HullSevenType1ChordInput H) : (25 : ℝ) / 2 < H :=
  hullSevenType1_area_gt X.toScalarData

/-- Direct sharp-constant consequence used by the hull-seven dispatcher. -/
theorem hullSeven_v8_of_type1_scalar
    {H : ℝ} (X : HullSevenType1ChordInput H) : 1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 < H := hullSevenType1_area_gt_of_chord X
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

end Heilbronn8.TriHull
