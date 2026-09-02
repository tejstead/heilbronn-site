import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Compact AM--GM closure for the end-open `q = 14` packet

This module isolates the scalar argument for the q-blind end-open chamber
whose second cuts are `(1,4)`.  The important input which is absent from the
coarser fan-and-ear relaxation is the upper bound on the first bottom `M`
cell.  Combined with the exact row recurrence, it gives

```text
E0' >= d - c + (c + d) / b.
```

The terminal column recurrence gives the lower bound on `A`, while the
correctly normalized second lower-ear identity gives

```text
E1' > d / (d - f)
```

in the only nontrivial height order `e < d`.  After these three eliminations
the remainder is a nine-term Laurent sum with a fourteen-copy AM--GM
certificate.  No generated certificate is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-- The Laurent remainder after the three end-open transition eliminations. -/
noncomputable def hullSixTwoFourEndOpenQ14Laurent
    (b f t : ℝ) : ℝ :=
  b + f + t + 1 / f + b / f + 1 / b + f / b + t / b + f / t

/-- The nine distinct terms in the fourteen-copy certificate. -/
noncomputable def hullSixTwoFourEndOpenQ14Term
    (b f t : ℝ) : Fin 9 → ℝ :=
  ![b, f, t, 1 / f, b / f, 1 / b, f / b, t / b, f / t]

/-- Multiplicities which cancel the exponents of `b`, `f`, and `t`. -/
def hullSixTwoFourEndOpenQ14Weight : Fin 9 → ℕ :=
  ![2, 1, 1, 2, 2, 2, 1, 1, 2]

/-- The variable-free scaled product of the fourteen AM--GM copies. -/
noncomputable def hullSixTwoFourEndOpenQ14Constant : ℝ :=
  1 / 1024

theorem hullSixTwoFourEndOpenQ14_weight_pos
    (i : Fin 9) : 0 < hullSixTwoFourEndOpenQ14Weight i := by
  fin_cases i <;> norm_num [hullSixTwoFourEndOpenQ14Weight]

theorem hullSixTwoFourEndOpenQ14_weight_sum :
    ∑ i, hullSixTwoFourEndOpenQ14Weight i = 14 := by
  norm_num [hullSixTwoFourEndOpenQ14Weight, Fin.sum_univ_succ]

theorem hullSixTwoFourEndOpenQ14_term_nonneg
    {b f t : ℝ} (hb : 0 ≤ b) (hf : 0 ≤ f) (ht : 0 ≤ t)
    (i : Fin 9) :
    0 ≤ hullSixTwoFourEndOpenQ14Term b f t i := by
  fin_cases i <;>
    simp [hullSixTwoFourEndOpenQ14Term] <;>
    positivity

theorem hullSixTwoFourEndOpenQ14_term_sum
    (b f t : ℝ) :
    ∑ i, hullSixTwoFourEndOpenQ14Term b f t i =
      hullSixTwoFourEndOpenQ14Laurent b f t := by
  simp [hullSixTwoFourEndOpenQ14Term,
    hullSixTwoFourEndOpenQ14Laurent, Fin.sum_univ_succ] <;>
    ring

/-- The fourteen scaled terms have exact product `1 / 2^10`. -/
theorem hullSixTwoFourEndOpenQ14_term_product
    {b f t : ℝ} (hb : 0 < b) (hf : 0 < f) (ht : 0 < t) :
    (∏ i,
        (hullSixTwoFourEndOpenQ14Term b f t i /
          (hullSixTwoFourEndOpenQ14Weight i : ℝ)) ^
            hullSixTwoFourEndOpenQ14Weight i) =
      hullSixTwoFourEndOpenQ14Constant := by
  simp [hullSixTwoFourEndOpenQ14Term,
    hullSixTwoFourEndOpenQ14Weight, Fin.prod_univ_succ,
    hullSixTwoFourEndOpenQ14Constant]
  field_simp [hb.ne', hf.ne', ht.ne'] <;> ring

theorem hullSixTwoFourEndOpenQ14_constant_pos :
    0 < hullSixTwoFourEndOpenQ14Constant := by
  norm_num [hullSixTwoFourEndOpenQ14Constant]

/-- Exact integer endpoint for the fourteen-copy certificate. -/
theorem hullSixTwoFourEndOpenQ14_integer_gap :
    1024 * (17 : ℕ) ^ 14 < 28 ^ 14 := by
  norm_num

/-- The AM--GM floor of the Laurent remainder is larger than `17 / 2`. -/
theorem hullSixTwoFourEndOpenQ14_root_gap :
    (17 : ℝ) / 2 <
      14 * hullSixTwoFourEndOpenQ14Constant ^ ((14 : ℝ)⁻¹) := by
  have hpow :
      ((17 : ℝ) / 28) ^ 14 <
        hullSixTwoFourEndOpenQ14Constant := by
    norm_num [hullSixTwoFourEndOpenQ14Constant]
  have hpowRpow :
      ((17 : ℝ) / 28) ^ (14 : ℝ) <
        hullSixTwoFourEndOpenQ14Constant := by
    change ((17 : ℝ) / 28) ^ ((14 : ℕ) : ℝ) <
      hullSixTwoFourEndOpenQ14Constant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (17 : ℝ) / 28 <
        hullSixTwoFourEndOpenQ14Constant ^ ((14 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixTwoFourEndOpenQ14_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixTwoFourEndOpenQ14_laurent_gt
    {b f t : ℝ} (hb : 0 < b) (hf : 0 < f) (ht : 0 < t) :
    (17 : ℝ) / 2 < hullSixTwoFourEndOpenQ14Laurent b f t := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixTwoFourEndOpenQ14Weight
    (hullSixTwoFourEndOpenQ14Term b f t)
    hullSixTwoFourEndOpenQ14_weight_pos
    (hullSixTwoFourEndOpenQ14_term_nonneg
      (le_of_lt hb) (le_of_lt hf) (le_of_lt ht))
  rw [hullSixTwoFourEndOpenQ14_weight_sum,
    hullSixTwoFourEndOpenQ14_term_product hb hf ht] at hamgm
  rw [← hullSixTwoFourEndOpenQ14_term_sum b f t]
  exact hullSixTwoFourEndOpenQ14_root_gap.trans_le hamgm

/-!
`J1` is the first bottom `Y` cell.  In the `M` chamber its companion
`X` cell has absolute-area floor one, hence `J1 ≤ b + d - 1`.
The row recurrence is retained as an equality below so that the theorem's
public interface cannot accidentally forget this essential compatibility.
-/

/-- Raw normalized scalar closure for the q-blind end-open `q = 14` packet. -/
theorem hullSixTwoFourEndOpenQ14_scalar
    {a b c d e f A C E0p E1p E2p Fp J1 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hed : e < d)
    (hC1 : 1 ≤ C) (hE1p1 : 1 ≤ E1p)
    (hE2p1 : 1 ≤ E2p) (hFp1 : 1 ≤ Fp)
    (hJ1Upper : J1 ≤ b + d - 1)
    (hE0Recurrence : b * E0p + c * J1 = d * (b + c + C))
    (hTerminal : a + b ≤ f * (A + a - b))
    (hEar1 : e ≤ (e - f) * E1p - (d - e) * E2p) :
    (25 : ℝ) / 2 < A + C + E0p + E1p + E2p + Fp + a + c := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  have hd : 0 < d := he.trans hed
  have hE1p : 0 < E1p := lt_of_lt_of_le zero_lt_one hE1p1
  have hE2p0 : 0 ≤ E2p := le_trans (by norm_num) hE2p1

  have hfe : f < e := by
    by_contra hnot
    have hef : e - f ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have hfirst : (e - f) * E1p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hef (le_of_lt hE1p)
    have hsecond : 0 ≤ (d - e) * E2p :=
      mul_nonneg (sub_nonneg.mpr (le_of_lt hed)) hE2p0
    nlinarith
  let t : ℝ := d - f
  have ht : 0 < t := by
    dsimp [t]
    linarith

  have hJ1Scaled : c * J1 ≤ c * (b + d - 1) :=
    mul_le_mul_of_nonneg_left hJ1Upper (le_of_lt hc)
  have hCFloorScaled : d * (b + c + 1) ≤ d * (b + c + C) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hd)
  have hE0Numerator :
      b * (d - c) + c + d ≤ b * E0p := by
    nlinarith [hJ1Scaled, hCFloorScaled]
  have hE0Lower : d - c + (c + d) / b ≤ E0p := by
    have hRewrite :
        d - c + (c + d) / b =
          (b * (d - c) + c + d) / b := by
      field_simp [hb.ne'] <;> ring
    rw [hRewrite, div_le_iff₀ hb]
    nlinarith [hE0Numerator]

  have hTerminalLower : (a + b) / f - a + b ≤ A := by
    have hdiv : (a + b) / f ≤ A + a - b :=
      (div_le_iff₀ hf).2 (by simpa [mul_comm] using hTerminal)
    linarith

  have hEarFloor : d ≤ (e - f) * E1p := by
    have hgapFloor : d - e ≤ (d - e) * E2p := by
      have hde0 : 0 ≤ d - e := sub_nonneg.mpr (le_of_lt hed)
      have := mul_le_mul_of_nonneg_left hE2p1 hde0
      simpa using this
    nlinarith
  have hgapProduct : d < (d - f) * E1p := by
    have hgap : e - f < d - f := by linarith
    have hmul := mul_lt_mul_of_pos_right hgap hE1p
    nlinarith [hEarFloor, hmul]
  have hE1pLower : d / (d - f) < E1p := by
    rw [div_lt_iff₀ ht]
    simpa [mul_comm] using hgapProduct

  have hRawLower :
      3 + b + d + (1 + b) / f + (1 + d) / b + d / (d - f) <
        A + C + E0p + E1p + E2p + Fp + a + c := by
    have haDiv : (1 + b) / f ≤ (a + b) / f := by
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hf)
    have hcDiv : (1 + d) / b ≤ (c + d) / b := by
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hb)
    nlinarith [hTerminalLower, hE0Lower, hE1pLower]

  have hIdentity :
      3 + b + d + (1 + b) / f + (1 + d) / b + d / (d - f) =
        4 + hullSixTwoFourEndOpenQ14Laurent b f t := by
    have hdf : d - f ≠ 0 := by
      dsimp [t] at ht
      exact ne_of_gt ht
    dsimp [hullSixTwoFourEndOpenQ14Laurent, t]
    field_simp [hb.ne', hf.ne', hdf] <;> ring
  have hLaurent := hullSixTwoFourEndOpenQ14_laurent_gt hb hf ht
  rw [hIdentity] at hRawLower
  linarith

/-!
Although the preceding name records the packet in which the argument was
found, its premises use only the common bottom `LMMM` row.  Consequently it
also closes the descending-height branch of `q = 04`.  This alias makes that
generic scope explicit for the eventual chamber adapter.
-/

theorem hullSixTwoFourEndOpenBottomMDescending_scalar
    {a b c d e f A C E0p E1p E2p Fp J1 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hed : e < d)
    (hC1 : 1 ≤ C) (hE1p1 : 1 ≤ E1p)
    (hE2p1 : 1 ≤ E2p) (hFp1 : 1 ≤ Fp)
    (hJ1Upper : J1 ≤ b + d - 1)
    (hE0Recurrence : b * E0p + c * J1 = d * (b + c + C))
    (hTerminal : a + b ≤ f * (A + a - b))
    (hEar1 : e ≤ (e - f) * E1p - (d - e) * E2p) :
    (25 : ℝ) / 2 < A + C + E0p + E1p + E2p + Fp + a + c :=
  hullSixTwoFourEndOpenQ14_scalar ha1 hb1 hc1 he1 hf1 hed
    hC1 hE1p1 hE2p1 hFp1 hJ1Upper hE0Recurrence hTerminal hEar1

end Heilbronn8
