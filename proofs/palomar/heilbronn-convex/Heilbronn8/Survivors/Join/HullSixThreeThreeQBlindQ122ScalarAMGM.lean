import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Uniform scalar certificate for the `q = 022/122` hull-six branches

The variables `a,b,c` and `d,e,f` are the normalized positive heights of the
three upper and lower hull vertices.  The variables `r,s,t,w,z` are the five
successive slope gaps.  This file eliminates those gaps under the signed
floors `-Y01`, `+Y11`, `+Y21`, and `-Y22`.

The only case split is the exact comparison `d >= f` versus `d < f`.  Both
branches reduce to the same nine-term Laurent sum

`b + e + c/b + 1/b + e/b + e/(b*c) + 2*e/c + b/e + 3/e`.

An exact thirty-one-copy weighted AM--GM certificate proves that this sum is
strictly larger than `21/2`, closing the normalized hull target `25/2`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The uniform Laurent lower bound for the `q = 022/122` branches. -/
noncomputable def hullSixThreeThreeQ122Laurent
    (b c e : ℝ) : ℝ :=
  b + e + c / b + 1 / b + e / b + e / (b * c) +
    2 * e / c + b / e + 3 / e

/-- The nine distinct terms in the thirty-one-copy certificate. -/
noncomputable def hullSixThreeThreeQ122AMGMTerm
    (b c e : ℝ) : Fin 9 → ℝ :=
  ![b, e, c / b, 1 / b, e / b, e / (b * c),
    2 * e / c, b / e, 3 / e]

/-- Multiplicities `5,4,4,2,2,1,3,4,6`, of total mass thirty-one. -/
def hullSixThreeThreeQ122AMGMWeight : Fin 9 → ℕ :=
  ![5, 4, 4, 2, 2, 1, 3, 4, 6]

/-- The variable-free product after the `b,c,e` exponents cancel. -/
noncomputable def hullSixThreeThreeQ122AMGMConstant : ℝ :=
  1 / ((5 : ℝ) ^ 5 * (2 : ℝ) ^ 31 * (3 : ℝ) ^ 3)

theorem hullSixThreeThreeQ122_amgmWeight_pos
    (i : Fin 9) : 0 < hullSixThreeThreeQ122AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ122AMGMWeight]

theorem hullSixThreeThreeQ122_amgmWeight_sum :
    ∑ i, hullSixThreeThreeQ122AMGMWeight i = 31 := by
  norm_num [hullSixThreeThreeQ122AMGMWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ122_amgmTerm_nonneg
    {b c e : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (i : Fin 9) :
    0 ≤ hullSixThreeThreeQ122AMGMTerm b c e i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ122AMGMTerm] <;>
    positivity

theorem hullSixThreeThreeQ122_amgmTerm_sum
    (b c e : ℝ) :
    ∑ i, hullSixThreeThreeQ122AMGMTerm b c e i =
      hullSixThreeThreeQ122Laurent b c e := by
  simp [hullSixThreeThreeQ122AMGMTerm, hullSixThreeThreeQ122Laurent,
    Fin.sum_univ_succ]
  <;> ring

/-- The thirty-one scaled terms have exact product `1/(5^5*2^31*3^3)`. -/
theorem hullSixThreeThreeQ122_amgmTerm_product
    {b c e : ℝ} (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    (∏ i,
        (hullSixThreeThreeQ122AMGMTerm b c e i /
          (hullSixThreeThreeQ122AMGMWeight i : ℝ)) ^
            hullSixThreeThreeQ122AMGMWeight i) =
      hullSixThreeThreeQ122AMGMConstant := by
  simp [hullSixThreeThreeQ122AMGMTerm,
    hullSixThreeThreeQ122AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ122AMGMConstant]
  field_simp [hb.ne', hc.ne', he.ne']
  <;> ring

theorem hullSixThreeThreeQ122_amgmConstant_pos :
    0 < hullSixThreeThreeQ122AMGMConstant := by
  unfold hullSixThreeThreeQ122AMGMConstant
  positivity

/-- Exact integer endpoint for the thirty-one-copy certificate. -/
theorem hullSixThreeThreeQ122_amgm_integer_gap :
    (21 : ℕ) ^ 31 * (5 ^ 5 * 2 ^ 31 * 3 ^ 3) < 62 ^ 31 := by
  norm_num

/-- The certified AM--GM root is strictly larger than `21/2`. -/
theorem hullSixThreeThreeQ122_amgm_root_gap :
    (21 : ℝ) / 2 <
      31 * hullSixThreeThreeQ122AMGMConstant ^ ((31 : ℝ)⁻¹) := by
  have hpow :
      ((21 : ℝ) / 62) ^ 31 < hullSixThreeThreeQ122AMGMConstant := by
    norm_num [hullSixThreeThreeQ122AMGMConstant]
  have hpowRpow :
      ((21 : ℝ) / 62) ^ (31 : ℝ) <
        hullSixThreeThreeQ122AMGMConstant := by
    change ((21 : ℝ) / 62) ^ ((31 : ℕ) : ℝ) <
      hullSixThreeThreeQ122AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (21 : ℝ) / 62 <
        hullSixThreeThreeQ122AMGMConstant ^ ((31 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ122_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- The exact nine-term Laurent inequality used by the chamber proof. -/
theorem hullSixThreeThreeQ122_laurent_gt
    {b c e : ℝ} (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    (21 : ℝ) / 2 < hullSixThreeThreeQ122Laurent b c e := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ122AMGMWeight
    (hullSixThreeThreeQ122AMGMTerm b c e)
    hullSixThreeThreeQ122_amgmWeight_pos
    (hullSixThreeThreeQ122_amgmTerm_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt he))
  rw [hullSixThreeThreeQ122_amgmWeight_sum,
    hullSixThreeThreeQ122_amgmTerm_product hb hc he] at hamgm
  rw [← hullSixThreeThreeQ122_amgmTerm_sum b c e]
  exact hullSixThreeThreeQ122_amgm_root_gap.trans_le hamgm

/-!
Inside the scalar proof we use

* `P = X10`, `T = u1`, `W = -X21`, and `Z = l1`;
* `N = -X01`, `J = -X11`, and `D = -X22`;
* `U,E,L,F` for `u0`, `X20`, `l0`, and `-X02`.
-/

/--
Complete normalized scalar closure for the signed `q = 022/122` branch.

The assumptions are exactly the six height floors, four elementary area/fan
floors, the primed lower-fan floor, and the four signed `Y` floors
`-Y01`, `+Y11`, `+Y21`, `-Y22` used by the elimination.
-/
theorem hullSixThreeThreeQ122_scalar
    {a b c d e f r s t w z : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hX10 : 1 ≤ b * d * s)
    (hu1 : 1 ≤ b * c * t)
    (hX21 : 1 ≤ c * e * w)
    (hl1q : 1 ≤ e * f * z + f - e)
    (hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e)
    (hY11pos : 1 ≤ b + e - b * e * (t + w))
    (hY21pos : 1 ≤ c + e - c * e * w)
    (hY22neg : 1 ≤ c * f * (w + z) - c - f) :
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
  let N : ℝ := a * e * (r + s + t + w)
  let J : ℝ := b * e * (t + w)
  let D : ℝ := c * f * (w + z)
  let U : ℝ := a * b * (r + s)
  let E : ℝ := c * d * (s + t)
  let L : ℝ := d * e * (s + t + w)
  let F : ℝ := a * f * (r + s + t + w + z)

  have hP : 1 ≤ P := by simpa [P] using hX10
  have hT : 1 ≤ T := by simpa [T] using hu1
  have hWbase : 1 ≤ W := by simpa [W] using hX21
  have hZbase : e - f + 1 ≤ Z := by
    dsimp [Z]
    linarith
  have hN : a + e + 1 ≤ N := by
    dsimp [N]
    linarith
  have hJupper : J ≤ b + e - 1 := by
    dsimp [J]
    linarith
  have hWupper : W ≤ c + e - 1 := by
    dsimp [W]
    linarith
  have hD : c + f + 1 ≤ D := by
    dsimp [D]
    linarith

  have hUidentity : U = (b / e) * N - (a / e) * J := by
    dsimp [U, N, J]
    field_simp [he.ne']
    <;> ring
  have hNscaled :
      (b / e) * (a + e + 1) ≤ (b / e) * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have hJscaled :
      (a / e) * J ≤ (a / e) * (b + e - 1) :=
    mul_le_mul_of_nonneg_left hJupper (by positivity)
  have hU : b - a + (a + b) / e ≤ U := by
    calc
      b - a + (a + b) / e =
          (b / e) * (a + e + 1) -
            (a / e) * (b + e - 1) := by
        field_simp [he.ne']
        <;> ring
      _ ≤ (b / e) * N - (a / e) * J := by linarith
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
  have hTscaledE : d / b ≤ (d / b) * T := by
    calc
      d / b = (d / b) * 1 := by ring
      _ ≤ (d / b) * T :=
        mul_le_mul_of_nonneg_left hT (by positivity)
  have hE : (c + d) / b ≤ E := by
    calc
      (c + d) / b = c / b + d / b := by ring
      _ ≤ (c / b) * P + (d / b) * T :=
        add_le_add hPscaledE hTscaledE
      _ = E := hEidentity.symm

  have hFidentity : F = (f / e) * N + (a / e) * Z := by
    dsimp [F, N, Z]
    field_simp [he.ne']
    <;> ring
  have hNscaledF :
      (f / e) * (a + e + 1) ≤ (f / e) * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have hZscaledF :
      (a / e) * (e - f + 1) ≤ (a / e) * Z :=
    mul_le_mul_of_nonneg_left hZbase (by positivity)
  have hF : a + f + (a + f) / e ≤ F := by
    calc
      a + f + (a + f) / e =
          (f / e) * (a + e + 1) +
            (a / e) * (e - f + 1) := by
        field_simp [he.ne']
        <;> ring
      _ ≤ (f / e) * N + (a / e) * Z :=
        add_le_add hNscaledF hZscaledF
      _ = F := hFidentity.symm

  have hLidentity :
      L = (e / b) * P + (d * e / (b * c)) * T + (d / c) * W := by
    dsimp [L, P, T, W]
    field_simp [hb.ne', hc.ne']
    <;> ring
  have hPscaledL : e / b ≤ (e / b) * P := by
    calc
      e / b = (e / b) * 1 := by ring
      _ ≤ (e / b) * P :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  have hTscaledL :
      d * e / (b * c) ≤ (d * e / (b * c)) * T := by
    calc
      d * e / (b * c) = (d * e / (b * c)) * 1 := by ring
      _ ≤ (d * e / (b * c)) * T :=
        mul_le_mul_of_nonneg_left hT (by positivity)
  have hLbase :
      e / b + d * e / (b * c) + (d / c) * W ≤ L := by
    calc
      e / b + d * e / (b * c) + (d / c) * W ≤
          (e / b) * P + (d * e / (b * c)) * T + (d / c) * W :=
        add_le_add_left (add_le_add hPscaledL hTscaledL) ((d / c) * W)
      _ = L := hLidentity.symm

  have hDWZidentity :
      (d / c) * W + Z =
        (e / c) * D + ((d - f) / c) * W := by
    dsimp [W, Z, D]
    field_simp [hc.ne']
    <;> ring

  let G : ℝ := 2 + hullSixThreeThreeQ122Laurent b c e
  have hG : G ≤ U + T + E + L + Z + F := by
    by_cases hfd : f ≤ d
    · have hDscaled :
          (e / c) * (c + f + 1) ≤ (e / c) * D :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      have hcoef : 0 ≤ (d - f) / c := by positivity
      have hWscaled :
          ((d - f) / c) * 1 ≤ ((d - f) / c) * W :=
        mul_le_mul_of_nonneg_left hWbase hcoef
      have hDWZ :
          e + e * f / c + e / c ≤ (d / c) * W + Z := by
        calc
          e + e * f / c + e / c =
              (e / c) * (c + f + 1) := by
            field_simp [hc.ne']
            <;> ring
          _ ≤ (e / c) * D := hDscaled
          _ ≤ (e / c) * D + ((d - f) / c) * W := by
            linarith [hWscaled]
          _ = (d / c) * W + Z := hDWZidentity.symm
      have hLZ :
          e / b + d * e / (b * c) + e + e * f / c + e / c ≤
            L + Z := by
        linarith [hLbase, hDWZ]
      have hLower :
          (b - a + (a + b) / e) + 1 + (c + d) / b +
              (e / b + d * e / (b * c) + e + e * f / c + e / c) +
                (a + f + (a + f) / e) ≤
            U + T + E + L + Z + F := by
        linarith [hU, hT, hE, hLZ, hF]
      have hdiff :
          0 ≤ (f - 1) + (d - 1) / b + e * (d - 1) / (b * c) +
            e * (f - 1) / c + (2 * (a - 1) + (f - 1)) / e := by
        positivity
      have hid :
          (b - a + (a + b) / e) + 1 + (c + d) / b +
              (e / b + d * e / (b * c) + e + e * f / c + e / c) +
                (a + f + (a + f) / e) =
            G + (f - 1) + (d - 1) / b + e * (d - 1) / (b * c) +
              e * (f - 1) / c + (2 * (a - 1) + (f - 1)) / e := by
        dsimp [G, hullSixThreeThreeQ122Laurent]
        field_simp [hb.ne', hc.ne', he.ne']
        <;> ring
      rw [hid] at hLower
      linarith
    · have hdf : d < f := lt_of_not_ge hfd
      have hcoef : (d - f) / c < 0 :=
        div_neg_of_neg_of_pos (sub_neg.mpr hdf) hc
      have hDscaled :
          (e / c) * (c + f + 1) ≤ (e / c) * D :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      have hWscaled :
          ((d - f) / c) * (c + e - 1) ≤ ((d - f) / c) * W :=
        mul_le_mul_of_nonpos_left hWupper (le_of_lt hcoef)
      have hDWZ :
          e + d - f + (e * (d + 1) - d + f) / c ≤
            (d / c) * W + Z := by
        calc
          e + d - f + (e * (d + 1) - d + f) / c =
              (e / c) * (c + f + 1) +
                ((d - f) / c) * (c + e - 1) := by
            field_simp [hc.ne']
            <;> ring
          _ ≤ (e / c) * D + ((d - f) / c) * W :=
            add_le_add hDscaled hWscaled
          _ = (d / c) * W + Z := hDWZidentity.symm
      have hLZ :
          e / b + d * e / (b * c) +
              e + d - f + (e * (d + 1) - d + f) / c ≤
            L + Z := by
        linarith [hLbase, hDWZ]
      have hLower :
          (b - a + (a + b) / e) + 1 + (c + d) / b +
              (e / b + d * e / (b * c) + e + d - f +
                (e * (d + 1) - d + f) / c) +
                  (a + f + (a + f) / e) ≤
            U + T + E + L + Z + F := by
        linarith [hU, hT, hE, hLZ, hF]
      have hdiff :
          0 ≤ (d - 1) + (d - 1) / b + e * (d - 1) / (b * c) +
            (2 * (a - 1) + (f - 1)) / e +
              ((d - 1) * (e - 1) + (f - 1)) / c := by
        positivity
      have hid :
          (b - a + (a + b) / e) + 1 + (c + d) / b +
              (e / b + d * e / (b * c) + e + d - f +
                (e * (d + 1) - d + f) / c) +
                  (a + f + (a + f) / e) =
            G + (d - 1) + (d - 1) / b + e * (d - 1) / (b * c) +
              (2 * (a - 1) + (f - 1)) / e +
                ((d - 1) * (e - 1) + (f - 1)) / c := by
        dsimp [G, hullSixThreeThreeQ122Laurent]
        field_simp [hb.ne', hc.ne', he.ne']
        <;> ring
      rw [hid] at hLower
      linarith

  have hLaurent := hullSixThreeThreeQ122_laurent_gt hb hc he
  have hGstrict : (25 : ℝ) / 2 < G := by
    dsimp [G]
    linarith
  have hFinal :
      (25 : ℝ) / 2 < U + T + E + L + Z + F :=
    hGstrict.trans_le hG
  simpa [U, T, E, L, Z, F] using hFinal

end Heilbronn8
