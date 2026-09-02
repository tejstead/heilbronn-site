import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM--GM certificate for the `q = 013/113` hull-six branches

The variables `a,b,c` and `d,e,f` are the normalized positive heights of the
three upper and lower hull vertices, and `r,s,t,w,z` are the five successive
slope gaps.  Two signed transitions, from `-Y11/+Y21` and `-Y12/+Y22`, give
two lower bounds for the middle upper fan.  A convex combination with its
area floor reduces the six-area sum to a seventeen-term Laurent sum.

The exact weighted AM--GM certificate has total mass ninety-eight.  The
geometric elimination actually supplies one additional positive monomial;
its discovered multiplicity is zero, so it is discarded before invoking the
positive-weight AM--GM theorem.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The seventeen positive terms used by the ninety-eight-copy certificate. -/
noncomputable def hullSixThreeThreeQ113Laurent
    (b d e f : ℝ) : ℝ :=
  1 / d + b / d + d + 1 / b + e / b + d * e / b + d / b +
    1 / (2 * e) + 1 / (2 * f) + 1 / (2 * b * e) +
    1 / (2 * b * f) + d / (2 * b * e) + d / (2 * b * f) +
    d / (2 * b ^ 2 * f) + e + f / e + 1 / e

/-- The seventeen distinct AM--GM terms. -/
noncomputable def hullSixThreeThreeQ113AMGMTerm
    (b d e f : ℝ) : Fin 17 → ℝ :=
  ![1 / d, b / d, d, 1 / b, e / b, d * e / b, d / b,
    1 / (2 * e), 1 / (2 * f), 1 / (2 * b * e),
    1 / (2 * b * f), d / (2 * b * e), d / (2 * b * f),
    d / (2 * b ^ 2 * f), e, f / e, 1 / e]

/-- Positive multiplicities, totaling ninety-eight. -/
def hullSixThreeThreeQ113AMGMWeight : Fin 17 → ℕ :=
  ![6, 22, 15, 3, 3, 5, 4, 3, 4, 1, 1, 1, 2, 1, 12, 8, 7]

/-- The variable-free product after the four height exponents cancel. -/
noncomputable def hullSixThreeThreeQ113AMGMConstant : ℝ :=
  1 / ((2 : ℝ) ^ 107 * (3 : ℝ) ^ 42 * (5 : ℝ) ^ 20 *
    (7 : ℝ) ^ 7 * (11 : ℝ) ^ 22)

theorem hullSixThreeThreeQ113_amgmWeight_pos
    (i : Fin 17) : 0 < hullSixThreeThreeQ113AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ113AMGMWeight]

theorem hullSixThreeThreeQ113_amgmWeight_sum :
    ∑ i, hullSixThreeThreeQ113AMGMWeight i = 98 := by
  norm_num [hullSixThreeThreeQ113AMGMWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ113_amgmTerm_nonneg
    {b d e f : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (i : Fin 17) :
    0 ≤ hullSixThreeThreeQ113AMGMTerm b d e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ113AMGMTerm] <;>
    positivity

theorem hullSixThreeThreeQ113_amgmTerm_sum
    (b d e f : ℝ) :
    ∑ i, hullSixThreeThreeQ113AMGMTerm b d e f i =
      hullSixThreeThreeQ113Laurent b d e f := by
  simp [hullSixThreeThreeQ113AMGMTerm, hullSixThreeThreeQ113Laurent,
    Fin.sum_univ_succ]
  <;> ring

/-- The ninety-eight scaled terms have the stated exact constant product. -/
theorem hullSixThreeThreeQ113_amgmTerm_product
    {b d e f : ℝ} (hb : 0 < b) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeQ113AMGMTerm b d e f i /
          (hullSixThreeThreeQ113AMGMWeight i : ℝ)) ^
            hullSixThreeThreeQ113AMGMWeight i) =
      hullSixThreeThreeQ113AMGMConstant := by
  simp [hullSixThreeThreeQ113AMGMTerm,
    hullSixThreeThreeQ113AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ113AMGMConstant]
  field_simp [hb.ne', hd.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeQ113_amgmConstant_pos :
    0 < hullSixThreeThreeQ113AMGMConstant := by
  unfold hullSixThreeThreeQ113AMGMConstant
  positivity

/-- Exact prime-power endpoint for the ninety-eight-copy certificate. -/
theorem hullSixThreeThreeQ113_amgm_integer_gap :
    (3 : ℕ) ^ 140 * 5 ^ 20 * 11 ^ 22 < 2 ^ 89 * 7 ^ 91 := by
  norm_num

/-- The certified AM--GM root gives a sum strictly larger than `21/2`. -/
theorem hullSixThreeThreeQ113_amgm_root_gap :
    (21 : ℝ) / 2 <
      98 * hullSixThreeThreeQ113AMGMConstant ^ ((98 : ℝ)⁻¹) := by
  have hpow :
      ((3 : ℝ) / 28) ^ 98 < hullSixThreeThreeQ113AMGMConstant := by
    norm_num [hullSixThreeThreeQ113AMGMConstant]
  have hpowRpow :
      ((3 : ℝ) / 28) ^ (98 : ℝ) <
        hullSixThreeThreeQ113AMGMConstant := by
    change ((3 : ℝ) / 28) ^ ((98 : ℕ) : ℝ) <
      hullSixThreeThreeQ113AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (3 : ℝ) / 28 <
        hullSixThreeThreeQ113AMGMConstant ^ ((98 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ113_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- The exact seventeen-term inequality used by the chamber proof. -/
theorem hullSixThreeThreeQ113_laurent_gt
    {b d e f : ℝ} (hb : 0 < b) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) :
    (21 : ℝ) / 2 < hullSixThreeThreeQ113Laurent b d e f := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ113AMGMWeight
    (hullSixThreeThreeQ113AMGMTerm b d e f)
    hullSixThreeThreeQ113_amgmWeight_pos
    (hullSixThreeThreeQ113_amgmTerm_nonneg
      (le_of_lt hb) (le_of_lt hd) (le_of_lt he) (le_of_lt hf))
  rw [hullSixThreeThreeQ113_amgmWeight_sum,
    hullSixThreeThreeQ113_amgmTerm_product hb hd he hf] at hamgm
  rw [← hullSixThreeThreeQ113_amgmTerm_sum b d e f]
  exact hullSixThreeThreeQ113_amgm_root_gap.trans_le hamgm

/-!
Inside the scalar proof we use

* `C = -X00`, `P = X10`, `T = u1`, `W = -X21`, and `Z = l1`;
* `N = -X01`, `J = -X11`, `K = -X12`, and `D = -X22`;
* `U,E,L,F` for `u0`, `X20`, `l0`, and `-X02`.
-/

/--
Complete normalized scalar closure for the signed `q = 013/113` branch.

The hypotheses are the six height floors, the `-X00`, `X10`, upper middle
fan, and primed lower-fan floors, together with `-Y01`, `-Y11`, `+Y21`,
`-Y12`, and `+Y22`.
-/
theorem hullSixThreeThreeQ113_scalar
    {a b c d e f r s t w z : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hX00 : 1 ≤ a * d * r)
    (hX10 : 1 ≤ b * d * s)
    (hu1 : 1 ≤ b * c * t)
    (hl1q : 1 ≤ e * f * z + f - e)
    (hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e)
    (hY11neg : 1 ≤ b * e * (t + w) - b - e)
    (hY21pos : 1 ≤ c + e - c * e * w)
    (hY12neg : 1 ≤ b * f * (t + w + z) - b - f)
    (hY22pos : 1 ≤ c + f - c * f * (w + z)) :
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

  let C : ℝ := a * d * r
  let P : ℝ := b * d * s
  let T : ℝ := b * c * t
  let W : ℝ := c * e * w
  let Z : ℝ := e * f * z
  let N : ℝ := a * e * (r + s + t + w)
  let J : ℝ := b * e * (t + w)
  let K : ℝ := b * f * (t + w + z)
  let D : ℝ := c * f * (w + z)
  let U : ℝ := a * b * (r + s)
  let E : ℝ := c * d * (s + t)
  let L : ℝ := d * e * (s + t + w)
  let F : ℝ := a * f * (r + s + t + w + z)

  have hC : 1 ≤ C := by simpa [C] using hX00
  have hP : 1 ≤ P := by simpa [P] using hX10
  have hT : 1 ≤ T := by simpa [T] using hu1
  have hZ : e - f + 1 ≤ Z := by
    dsimp [Z]
    linarith
  have hN : a + e + 1 ≤ N := by
    dsimp [N]
    linarith
  have hJ : b + e + 1 ≤ J := by
    dsimp [J]
    linarith
  have hWupper : W ≤ c + e - 1 := by
    dsimp [W]
    linarith
  have hK : b + f + 1 ≤ K := by
    dsimp [K]
    linarith
  have hDupper : D ≤ c + f - 1 := by
    dsimp [D]
    linarith

  have hUidentity : U = (b / d) * C + (a / d) * P := by
    dsimp [U, C, P]
    field_simp [hd.ne']
    <;> ring
  have hCscaled : b / d ≤ (b / d) * C := by
    calc
      b / d = (b / d) * 1 := by ring
      _ ≤ (b / d) * C :=
        mul_le_mul_of_nonneg_left hC (by positivity)
  have hPscaledU : a / d ≤ (a / d) * P := by
    calc
      a / d = (a / d) * 1 := by ring
      _ ≤ (a / d) * P :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  have hU : (a + b) / d ≤ U := by
    calc
      (a + b) / d = b / d + a / d := by ring
      _ ≤ (b / d) * C + (a / d) * P :=
        add_le_add hCscaled hPscaledU
      _ = U := hUidentity.symm

  have hEidentity : E = (c / b) * P + (d / b) * T := by
    dsimp [E, P, T]
    field_simp [hb.ne']
    <;> ring
  have hPscaledE : c / b ≤ (c / b) * P := by
    calc
      c / b = (c / b) * 1 := by ring
      _ ≤ (c / b) * P :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  have hE : c / b + (d / b) * T ≤ E := by
    calc
      c / b + (d / b) * T ≤ (c / b) * P + (d / b) * T :=
        add_le_add_left hPscaledE ((d / b) * T)
      _ = E := hEidentity.symm

  have hLidentity : L = (e / b) * P + (d / b) * J := by
    dsimp [L, P, J]
    field_simp [hb.ne']
    <;> ring
  have hPscaledL : e / b ≤ (e / b) * P := by
    calc
      e / b = (e / b) * 1 := by ring
      _ ≤ (e / b) * P :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  have hJscaledL :
      (d / b) * (b + e + 1) ≤ (d / b) * J :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hL : e / b + d + d * e / b + d / b ≤ L := by
    calc
      e / b + d + d * e / b + d / b =
          e / b + (d / b) * (b + e + 1) := by
        field_simp [hb.ne']
        <;> ring
      _ ≤ (e / b) * P + (d / b) * J :=
        add_le_add hPscaledL hJscaledL
      _ = L := hLidentity.symm

  have hFidentity : F = (f / e) * N + (a / e) * Z := by
    dsimp [F, N, Z]
    field_simp [he.ne']
    <;> ring
  have hNscaledF :
      (f / e) * (a + e + 1) ≤ (f / e) * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have hF : f + f * (a + 1) / e + (a / e) * Z ≤ F := by
    calc
      f + f * (a + 1) / e + (a / e) * Z =
          (f / e) * (a + e + 1) + (a / e) * Z := by
        field_simp [he.ne']
        <;> ring
      _ ≤ (f / e) * N + (a / e) * Z :=
        add_le_add_left hNscaledF ((a / e) * Z)
      _ = F := hFidentity.symm
  have hZscaled :
      (1 + a / e) * (e - f + 1) ≤ (1 + a / e) * Z :=
    mul_le_mul_of_nonneg_left hZ (by positivity)
  have hZF : a + e + 1 + (a + f) / e ≤ Z + F := by
    have hZFraw :
        Z + f + f * (a + 1) / e + (a / e) * Z ≤ Z + F := by
      linarith [hF]
    calc
      a + e + 1 + (a + f) / e =
          f + f * (a + 1) / e +
            (1 + a / e) * (e - f + 1) := by
        field_simp [he.ne']
        <;> ring
      _ ≤ f + f * (a + 1) / e + (1 + a / e) * Z := by
        linarith [hZscaled]
      _ = Z + f + f * (a + 1) / e + (a / e) * Z := by ring
      _ ≤ Z + F := hZFraw

  have hTransitionEIdentity : T = (c / e) * J - (b / e) * W := by
    dsimp [T, J, W]
    field_simp [he.ne']
    <;> ring
  have hJscaled :
      (c / e) * (b + e + 1) ≤ (c / e) * J :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have hWscaled :
      (b / e) * W ≤ (b / e) * (c + e - 1) :=
    mul_le_mul_of_nonneg_left hWupper (by positivity)
  have hTransitionE : c - b + (b + c) / e ≤ T := by
    calc
      c - b + (b + c) / e =
          (c / e) * (b + e + 1) -
            (b / e) * (c + e - 1) := by
        field_simp [he.ne']
        <;> ring
      _ ≤ (c / e) * J - (b / e) * W := by linarith
      _ = T := hTransitionEIdentity.symm

  have hTransitionFIdentity : T = (c / f) * K - (b / f) * D := by
    dsimp [T, K, D]
    field_simp [hf.ne']
    <;> ring
  have hKscaled :
      (c / f) * (b + f + 1) ≤ (c / f) * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hDscaled :
      (b / f) * D ≤ (b / f) * (c + f - 1) :=
    mul_le_mul_of_nonneg_left hDupper (by positivity)
  have hTransitionF : c - b + (b + c) / f ≤ T := by
    calc
      c - b + (b + c) / f =
          (c / f) * (b + f + 1) -
            (b / f) * (c + f - 1) := by
        field_simp [hf.ne']
        <;> ring
      _ ≤ (c / f) * K - (b / f) * D := by linarith
      _ = T := hTransitionFIdentity.symm

  have hInvBLeOne : 1 / b ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ (1 : ℝ) / b)
    calc
      1 / b = (1 / b) * 1 := by ring
      _ ≤ (1 / b) * b := hmul
      _ = 1 := by field_simp [hb.ne']
  have hOneMinus : 0 ≤ 1 - 1 / b := by linarith
  have hInvB : 0 ≤ 1 / b := by positivity
  have hConvexE :
      (c - 1) / b + (b + c) / (b * e) ≤ T := by
    have hfloorScaled :
        (1 - 1 / b) * 1 ≤ (1 - 1 / b) * T :=
      mul_le_mul_of_nonneg_left hT hOneMinus
    have htransitionScaled :
        (1 / b) * (c - b + (b + c) / e) ≤ (1 / b) * T :=
      mul_le_mul_of_nonneg_left hTransitionE hInvB
    calc
      (c - 1) / b + (b + c) / (b * e) =
          (1 - 1 / b) * 1 +
            (1 / b) * (c - b + (b + c) / e) := by
        field_simp [hb.ne', he.ne']
        <;> ring
      _ ≤ (1 - 1 / b) * T + (1 / b) * T :=
        add_le_add hfloorScaled htransitionScaled
      _ = T := by ring
  have hConvexF :
      (c - 1) / b + (b + c) / (b * f) ≤ T := by
    have hfloorScaled :
        (1 - 1 / b) * 1 ≤ (1 - 1 / b) * T :=
      mul_le_mul_of_nonneg_left hT hOneMinus
    have htransitionScaled :
        (1 / b) * (c - b + (b + c) / f) ≤ (1 / b) * T :=
      mul_le_mul_of_nonneg_left hTransitionF hInvB
    calc
      (c - 1) / b + (b + c) / (b * f) =
          (1 - 1 / b) * 1 +
            (1 / b) * (c - b + (b + c) / f) := by
        field_simp [hb.ne', hf.ne']
        <;> ring
      _ ≤ (1 - 1 / b) * T + (1 / b) * T :=
        add_le_add hfloorScaled htransitionScaled
      _ = T := by ring
  have hTcore :
      (b + c) * (e + f) / (2 * b * e * f) ≤ T := by
    have haverage :
        ((c - 1) / b + (b + c) / (b * e) +
          ((c - 1) / b + (b + c) / (b * f))) / 2 ≤ T := by
      linarith [hConvexE, hConvexF]
    have hdiscard : 0 ≤ (c - 1) / b := by positivity
    have hid :
        ((c - 1) / b + (b + c) / (b * e) +
          ((c - 1) / b + (b + c) / (b * f))) / 2 =
            (c - 1) / b + (b + c) * (e + f) / (2 * b * e * f) := by
      field_simp [hb.ne', he.ne', hf.ne']
      <;> ring
    rw [hid] at haverage
    linarith

  let B : ℝ :=
    1 / d + b / d + d + 1 / b + e / b + d * e / b + d / b +
      e + f / e + 1 / e
  have hRawLower :
      (a + b) / d + T + (c / b + (d / b) * T) +
          (e / b + d + d * e / b + d / b) +
            (a + e + 1 + (a + f) / e) ≤
        U + T + E + L + Z + F := by
    linarith [hU, hE, hL, hZF]
  have hBaseDiff :
      0 ≤ (a - 1) / d + (c - 1) / b +
        (a - 1) + (a - 1) / e := by
    positivity
  have hRawIdentity :
      (a + b) / d + T + (c / b + (d / b) * T) +
          (e / b + d + d * e / b + d / b) +
            (a + e + 1 + (a + f) / e) =
        2 + B + (1 + d / b) * T +
          ((a - 1) / d + (c - 1) / b +
            (a - 1) + (a - 1) / e) := by
    dsimp [B]
    field_simp [hb.ne', hd.ne', he.ne']
    <;> ring
  rw [hRawIdentity] at hRawLower
  have hBaseLower :
      2 + B + (1 + d / b) * T ≤ U + T + E + L + Z + F := by
    linarith

  let Q : ℝ :=
    1 / (2 * e) + 1 / (2 * f) + 1 / (2 * b * e) +
      1 / (2 * b * f) + d / (2 * b * e) + d / (2 * b * f) +
        d / (2 * b ^ 2 * f)
  have hTmult :
      (1 + d / b) * ((b + c) * (e + f) / (2 * b * e * f)) ≤
        (1 + d / b) * T :=
    mul_le_mul_of_nonneg_left hTcore (by positivity)
  have hQremainder :
      0 ≤
        (c - 1) * (1 / (2 * b * e) + 1 / (2 * b * f) +
          d / (2 * b ^ 2 * e) + d / (2 * b ^ 2 * f)) +
            d / (2 * b ^ 2 * e) := by
    positivity
  have hQidentity :
      (1 + d / b) * ((b + c) * (e + f) / (2 * b * e * f)) =
        Q +
          (c - 1) * (1 / (2 * b * e) + 1 / (2 * b * f) +
            d / (2 * b ^ 2 * e) + d / (2 * b ^ 2 * f)) +
              d / (2 * b ^ 2 * e) := by
    dsimp [Q]
    field_simp [hb.ne', he.ne', hf.ne']
    <;> ring
  rw [hQidentity] at hTmult
  have hQle : Q ≤ (1 + d / b) * T := by
    linarith

  have hLaurentIdentity : hullSixThreeThreeQ113Laurent b d e f = B + Q := by
    dsimp [B, Q, hullSixThreeThreeQ113Laurent]
    ring
  have hLaurentLe :
      2 + hullSixThreeThreeQ113Laurent b d e f ≤
        U + T + E + L + Z + F := by
    rw [hLaurentIdentity]
    linarith [hBaseLower, hQle]
  have hLaurent := hullSixThreeThreeQ113_laurent_gt hb hd he hf
  have hFinal :
      (25 : ℝ) / 2 < U + T + E + L + Z + F := by
    linarith [hLaurent, hLaurentLe]
  simpa [U, T, E, L, Z, F] using hFinal

end Heilbronn8
