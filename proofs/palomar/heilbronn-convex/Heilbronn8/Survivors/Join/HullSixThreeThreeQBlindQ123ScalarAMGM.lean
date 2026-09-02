import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM--GM certificate for the `q = 023/123` hull-six branches

The variables `a,b,c` and `d,e,f` are the normalized positive heights of the
three upper and lower hull vertices, and `r,s,t,w,z` are the five successive
slope gaps.  The signed floors `-Y12` and `+Y22` give a direct transition
bound for the middle upper fan.  Averaging that bound with the fan floor
reduces the six-area sum to fourteen positive Laurent terms.

An exact forty-copy weighted AM--GM certificate then proves the normalized
target `25/2`.  No generated certificate, height-order split, hull ear, or
unproved monotonicity assertion is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The fourteen-term lower sum for the `q = 023/123` branches. -/
noncomputable def hullSixThreeThreeQ123Laurent
    (b c e f : ℝ) : ℝ :=
  e + 3 / 2 + b / 2 + c / 2 + b / (2 * f) + c / (2 * f) +
    2 / e + b / e + f / e + c / b + 1 / b + e / b +
      e / (b * c) + 1 / c

/-- The fourteen distinct terms in the forty-copy certificate. -/
noncomputable def hullSixThreeThreeQ123AMGMTerm
    (b c e f : ℝ) : Fin 14 → ℝ :=
  ![e, 3 / 2, b / 2, c / 2, b / (2 * f), c / (2 * f),
    2 / e, b / e, f / e, c / b, 1 / b, e / b,
    e / (b * c), 1 / c]

/-- Multiplicities `5,5,3,2,2,1,3,4,3,2,2,3,2,3`, totaling forty. -/
def hullSixThreeThreeQ123AMGMWeight : Fin 14 → ℕ :=
  ![5, 5, 3, 2, 2, 1, 3, 4, 3, 2, 2, 3, 2, 3]

/-- The variable-free product after the four height exponents cancel. -/
noncomputable def hullSixThreeThreeQ123AMGMConstant : ℝ :=
  1 / ((2 : ℝ) ^ 28 * (3 : ℝ) ^ 10 * (5 : ℝ) ^ 10)

theorem hullSixThreeThreeQ123_amgmWeight_pos
    (i : Fin 14) : 0 < hullSixThreeThreeQ123AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeQ123AMGMWeight]

theorem hullSixThreeThreeQ123_amgmWeight_sum :
    ∑ i, hullSixThreeThreeQ123AMGMWeight i = 40 := by
  norm_num [hullSixThreeThreeQ123AMGMWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeQ123_amgmTerm_nonneg
    {b c e f : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hf : 0 ≤ f) (i : Fin 14) :
    0 ≤ hullSixThreeThreeQ123AMGMTerm b c e f i := by
  fin_cases i <;>
    simp [hullSixThreeThreeQ123AMGMTerm] <;>
    positivity

theorem hullSixThreeThreeQ123_amgmTerm_sum
    (b c e f : ℝ) :
    ∑ i, hullSixThreeThreeQ123AMGMTerm b c e f i =
      hullSixThreeThreeQ123Laurent b c e f := by
  simp [hullSixThreeThreeQ123AMGMTerm, hullSixThreeThreeQ123Laurent,
    Fin.sum_univ_succ]
  <;> ring

/-- The forty scaled terms have exact product `1/(2^28*3^10*5^10)`. -/
theorem hullSixThreeThreeQ123_amgmTerm_product
    {b c e f : ℝ} (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) :
    (∏ i,
        (hullSixThreeThreeQ123AMGMTerm b c e f i /
          (hullSixThreeThreeQ123AMGMWeight i : ℝ)) ^
            hullSixThreeThreeQ123AMGMWeight i) =
      hullSixThreeThreeQ123AMGMConstant := by
  simp [hullSixThreeThreeQ123AMGMTerm,
    hullSixThreeThreeQ123AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeQ123AMGMConstant]
  field_simp [hb.ne', hc.ne', he.ne', hf.ne']
  <;> ring

theorem hullSixThreeThreeQ123_amgmConstant_pos :
    0 < hullSixThreeThreeQ123AMGMConstant := by
  unfold hullSixThreeThreeQ123AMGMConstant
  positivity

/-- Exact integer endpoint for the forty-copy certificate. -/
theorem hullSixThreeThreeQ123_amgm_integer_gap :
    (3 : ℕ) ^ 10 * 5 ^ 50 < 2 ^ 132 := by
  norm_num

/-- The certified AM--GM root gives a sum strictly larger than `25/2`. -/
theorem hullSixThreeThreeQ123_amgm_root_gap :
    (25 : ℝ) / 2 <
      40 * hullSixThreeThreeQ123AMGMConstant ^ ((40 : ℝ)⁻¹) := by
  have hpow :
      ((5 : ℝ) / 16) ^ 40 < hullSixThreeThreeQ123AMGMConstant := by
    norm_num [hullSixThreeThreeQ123AMGMConstant]
  have hpowRpow :
      ((5 : ℝ) / 16) ^ (40 : ℝ) <
        hullSixThreeThreeQ123AMGMConstant := by
    change ((5 : ℝ) / 16) ^ ((40 : ℕ) : ℝ) <
      hullSixThreeThreeQ123AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (5 : ℝ) / 16 <
        hullSixThreeThreeQ123AMGMConstant ^ ((40 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeQ123_amgmConstant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

/-- The exact fourteen-term inequality used by the chamber proof. -/
theorem hullSixThreeThreeQ123_laurent_gt
    {b c e f : ℝ} (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) :
    (25 : ℝ) / 2 < hullSixThreeThreeQ123Laurent b c e f := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeQ123AMGMWeight
    (hullSixThreeThreeQ123AMGMTerm b c e f)
    hullSixThreeThreeQ123_amgmWeight_pos
    (hullSixThreeThreeQ123_amgmTerm_nonneg
      (le_of_lt hb) (le_of_lt hc) (le_of_lt he) (le_of_lt hf))
  rw [hullSixThreeThreeQ123_amgmWeight_sum,
    hullSixThreeThreeQ123_amgmTerm_product hb hc he hf] at hamgm
  rw [← hullSixThreeThreeQ123_amgmTerm_sum b c e f]
  exact hullSixThreeThreeQ123_amgm_root_gap.trans_le hamgm

/-!
Inside the scalar proof we use

* `P = X10`, `T = u1`, `W = -X21`, and `Z = l1`;
* `N = -X01`, `J = -X11`, `K = -X12`, and `D = -X22`;
* `U,E,L,F` for `u0`, `X20`, `l0`, and `-X02`.
-/

/--
Complete normalized scalar closure for the signed `q = 023/123` branch.

The hypotheses are the six height floors, the three elementary area/fan
floors and primed lower-fan floor, together with `-Y01`, `+Y11`, `-Y12`,
and `+Y22`.
-/
theorem hullSixThreeThreeQ123_scalar
    {a b c d e f r s t w z : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hX10 : 1 ≤ b * d * s)
    (hu1 : 1 ≤ b * c * t)
    (hX21 : 1 ≤ c * e * w)
    (hl1q : 1 ≤ e * f * z + f - e)
    (hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e)
    (hY11pos : 1 ≤ b + e - b * e * (t + w))
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

  have hP : 1 ≤ P := by simpa [P] using hX10
  have hT : 1 ≤ T := by simpa [T] using hu1
  have hW : 1 ≤ W := by simpa [W] using hX21
  have hZ : e - f + 1 ≤ Z := by
    dsimp [Z]
    linarith
  have hN : a + e + 1 ≤ N := by
    dsimp [N]
    linarith
  have hJupper : J ≤ b + e - 1 := by
    dsimp [J]
    linarith
  have hK : b + f + 1 ≤ K := by
    dsimp [K]
    linarith
  have hDupper : D ≤ c + f - 1 := by
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

  have hTidentity : T = (c / f) * K - (b / f) * D := by
    dsimp [T, K, D]
    field_simp [hf.ne']
    <;> ring
  have hKscaled :
      (c / f) * (b + f + 1) ≤ (c / f) * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hDscaled :
      (b / f) * D ≤ (b / f) * (c + f - 1) :=
    mul_le_mul_of_nonneg_left hDupper (by positivity)
  have hTransition : c - b + (b + c) / f ≤ T := by
    calc
      c - b + (b + c) / f =
          (c / f) * (b + f + 1) -
            (b / f) * (c + f - 1) := by
        field_simp [hf.ne']
        <;> ring
      _ ≤ (c / f) * K - (b / f) * D := by linarith
      _ = T := hTidentity.symm
  have hTaverage :
      (1 + (c - b + (b + c) / f)) / 2 ≤ T := by
    linarith [hT, hTransition]

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
  have hTE :
      (1 + (c - b + (b + c) / f)) / 2 + (c + d) / b ≤
        T + E := by
    linarith [hTaverage, hE]

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
  have hWscaledL : d / c ≤ (d / c) * W := by
    calc
      d / c = (d / c) * 1 := by ring
      _ ≤ (d / c) * W :=
        mul_le_mul_of_nonneg_left hW (by positivity)
  have hL : e / b + d * e / (b * c) + d / c ≤ L := by
    calc
      e / b + d * e / (b * c) + d / c ≤
          (e / b) * P + (d * e / (b * c)) * T + (d / c) * W :=
        add_le_add (add_le_add hPscaledL hTscaledL) hWscaledL
      _ = L := hLidentity.symm

  have hFidentity : F = (f / e) * N + (a / e) * Z := by
    dsimp [F, N, Z]
    field_simp [he.ne']
    <;> ring
  have hNscaledF :
      (f / e) * (a + e + 1) ≤ (f / e) * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have hZscaledF :
      (a / e) * (e - f + 1) ≤ (a / e) * Z :=
    mul_le_mul_of_nonneg_left hZ (by positivity)
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

  have hLower :
      (b - a + (a + b) / e) +
          ((1 + (c - b + (b + c) / f)) / 2 + (c + d) / b) +
            (e / b + d * e / (b * c) + d / c) +
              (e - f + 1) + (a + f + (a + f) / e) ≤
        U + T + E + L + Z + F := by
    linarith [hU, hTE, hL, hZ, hF]
  have hdiff :
      0 ≤ 2 * (a - 1) / e + (d - 1) / b +
        e * (d - 1) / (b * c) + (d - 1) / c := by
    positivity
  have hLowerIdentity :
      (b - a + (a + b) / e) +
          ((1 + (c - b + (b + c) / f)) / 2 + (c + d) / b) +
            (e / b + d * e / (b * c) + d / c) +
              (e - f + 1) + (a + f + (a + f) / e) =
        hullSixThreeThreeQ123Laurent b c e f +
          2 * (a - 1) / e + (d - 1) / b +
            e * (d - 1) / (b * c) + (d - 1) / c := by
    dsimp [hullSixThreeThreeQ123Laurent]
    field_simp [hb.ne', hc.ne', he.ne', hf.ne']
    <;> ring
  rw [hLowerIdentity] at hLower
  have hLaurentLe :
      hullSixThreeThreeQ123Laurent b c e f ≤ U + T + E + L + Z + F := by
    linarith
  have hLaurent := hullSixThreeThreeQ123_laurent_gt hb hc he hf
  have hFinal :
      (25 : ℝ) / 2 < U + T + E + L + Z + F :=
    hLaurent.trans_le hLaurentLe
  simpa [U, T, E, L, Z, F] using hFinal

end Heilbronn8
