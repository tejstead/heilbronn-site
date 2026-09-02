import Mathlib.Analysis.MeanInequalities

/-!
# Scalar closure for the maximal-q `p = 033` X-frontier

Two consecutive hull-triangle floors and two boundary `Q`-fan floors reduce
the chamber to an eight-term Laurent inequality.  The final estimate is an
eleven-copy weighted AM--GM certificate.  This module is geometry-free.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

private lemma p033_weighted_amgm_nat
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight : ι → ℕ) (term : ι → ℝ)
    (hweight : ∀ i, 0 < weight i) (hterm : ∀ i, 0 ≤ term i) :
    ((↑(∑ i, weight i) : ℝ) *
        (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^
          ((↑(∑ i, weight i) : ℝ)⁻¹)) ≤
      ∑ i, term i := by
  classical
  let mass : ℕ := ∑ i, weight i
  have hmass : 0 < mass := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact Finset.sum_pos' (fun j _ ↦ Nat.zero_le (weight j))
      ⟨i, Finset.mem_univ i, hweight i⟩
  have hmassCast : (mass : ℝ) = ∑ i, (weight i : ℝ) := by
    simp [mass]
  have hsum :
      (∑ i, (weight i : ℝ) * (term i / (weight i : ℝ))) =
        ∑ i, term i := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : (weight i : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hweight i))
    field_simp [hi]
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset ι) (fun i ↦ (weight i : ℝ))
      (fun i ↦ term i / (weight i : ℝ))
      (fun i _ ↦ Nat.cast_nonneg (weight i))
      (by simpa [← hmassCast] using hmass)
      (fun i _ ↦ div_nonneg (hterm i) (Nat.cast_nonneg (weight i)))
  have hroot :
      (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^ ((mass : ℝ)⁻¹) ≤
        (∑ i, term i) / (mass : ℝ) := by
    rw [hmassCast, ← hsum]
    simpa only [Real.rpow_natCast] using hamgm
  change (mass : ℝ) *
      (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^ ((mass : ℝ)⁻¹) ≤
    ∑ i, term i
  calc
    (mass : ℝ) *
          (∏ i, (term i / (weight i : ℝ)) ^ weight i) ^ ((mass : ℝ)⁻¹) ≤
        (mass : ℝ) * ((∑ i, term i) / (mass : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg mass)
    _ = ∑ i, term i := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmass)]

/-- The eight monomials retained by the `p = 033` AM--GM certificate. -/
noncomputable def hullSixThreeThreeP033Laurent
    (t x e : ℝ) : ℝ :=
  t + t / x + t / e + 1 / t + 1 / (e * t) + 2 / e + x + e

noncomputable def hullSixThreeThreeP033AMGMTerm
    (t x e : ℝ) : Fin 8 → ℝ :=
  ![t, t / x, t / e, 1 / t, 1 / (e * t), 2 / e, x, e]

def hullSixThreeThreeP033AMGMWeight : Fin 8 → ℕ :=
  ![1, 1, 1, 2, 1, 1, 1, 3]

noncomputable def hullSixThreeThreeP033AMGMConstant : ℝ := 1 / 54

private lemma p033_weight_pos (i : Fin 8) :
    0 < hullSixThreeThreeP033AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP033AMGMWeight]

private lemma p033_weight_sum :
    ∑ i, hullSixThreeThreeP033AMGMWeight i = 11 := by
  norm_num [hullSixThreeThreeP033AMGMWeight, Fin.sum_univ_succ]

private lemma p033_term_nonneg {t x e : ℝ}
    (ht : 0 ≤ t) (hx : 0 ≤ x) (he : 0 ≤ e) (i : Fin 8) :
    0 ≤ hullSixThreeThreeP033AMGMTerm t x e i := by
  fin_cases i <;> simp [hullSixThreeThreeP033AMGMTerm] <;> positivity

private lemma p033_term_sum (t x e : ℝ) :
    ∑ i, hullSixThreeThreeP033AMGMTerm t x e i =
      hullSixThreeThreeP033Laurent t x e := by
  simp [hullSixThreeThreeP033AMGMTerm, hullSixThreeThreeP033Laurent,
    Fin.sum_univ_succ]
  <;> ring

private lemma p033_term_product {t x e : ℝ}
    (ht : 0 < t) (hx : 0 < x) (he : 0 < e) :
    (∏ i,
        (hullSixThreeThreeP033AMGMTerm t x e i /
          (hullSixThreeThreeP033AMGMWeight i : ℝ)) ^
            hullSixThreeThreeP033AMGMWeight i) =
      hullSixThreeThreeP033AMGMConstant := by
  simp [hullSixThreeThreeP033AMGMTerm,
    hullSixThreeThreeP033AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP033AMGMConstant]
  field_simp [ht.ne', hx.ne', he.ne']
  <;> ring

private lemma p033_constant_pos :
    0 < hullSixThreeThreeP033AMGMConstant := by
  unfold hullSixThreeThreeP033AMGMConstant
  norm_num

private lemma p033_root_gap :
    (15 : ℝ) / 2 <
      11 * hullSixThreeThreeP033AMGMConstant ^ ((11 : ℝ)⁻¹) := by
  have hpow :
      ((15 : ℝ) / 22) ^ 11 < hullSixThreeThreeP033AMGMConstant := by
    norm_num [hullSixThreeThreeP033AMGMConstant]
  have hpowRpow :
      ((15 : ℝ) / 22) ^ (11 : ℝ) <
        hullSixThreeThreeP033AMGMConstant := by
    change ((15 : ℝ) / 22) ^ ((11 : ℕ) : ℝ) <
      hullSixThreeThreeP033AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (15 : ℝ) / 22 <
        hullSixThreeThreeP033AMGMConstant ^ ((11 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt p033_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

private lemma p033_laurent_gt {t x e : ℝ}
    (ht : 0 < t) (hx : 0 < x) (he : 0 < e) :
    (15 : ℝ) / 2 < hullSixThreeThreeP033Laurent t x e := by
  have hamgm := p033_weighted_amgm_nat
    hullSixThreeThreeP033AMGMWeight
    (hullSixThreeThreeP033AMGMTerm t x e)
    p033_weight_pos (p033_term_nonneg ht.le hx.le he.le)
  rw [p033_weight_sum, p033_term_product ht hx he] at hamgm
  rw [← p033_term_sum t x e]
  exact p033_root_gap.trans_le hamgm

/-!
The scalar inputs below are division-free.  `D,E` are the two consecutive
lower `P`-fan sectors, `A,B,C,F` are the other four sectors.  `hLower` is the
`L0 L1 L2` hull-triangle floor, `hCD` is the `U2 L0 L1` hull-triangle floor,
and `hQE`,`hF` are the two boundary `Q`-fan floors.
-/

/-- The normalized `p = 033` determinant inequalities force hull area above
`25/2`. -/
theorem hullSixThreeThree_p033_scalar
    {b c d e D E A B C F H : ℝ}
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hD : 1 ≤ D) (hE : 1 ≤ E)
    (hA : c * d * e + c * D * e + b * c * E + b * d ≤
      b * d * e * A)
    (hCD : e * c + c * E + d + d * e ≤ e * c * (C + D))
    (hLower : e * D + b * E + d ≤ d * (D + E))
    (hQE : d - e + 1 ≤ E)
    (hB : 1 ≤ B) (hF : e + 2 ≤ F)
    (hH : A + B + C + D + E + F ≤ H) :
    25 / 2 < H := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hgap : d - e ≤ E - 1 := by linarith
  have hLower' : b * E ≤ (d - e) * D + d * (E - 1) := by
    nlinarith [hLower]
  have hgapD : (d - e) * D ≤ (E - 1) * D :=
    mul_le_mul_of_nonneg_right hgap hD0.le
  have hratioRaw : b * E ≤ (E - 1) * (d + D) := by
    nlinarith [hLower', hgapD]
  have hx : 0 < E - 1 := by
    by_contra hn
    have hxle : E - 1 ≤ 0 := le_of_not_gt hn
    have hright : (E - 1) * (d + D) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hxle (add_pos hd0 hD0).le
    have hleft : 0 < b * E := mul_pos hb0 hE0
    linarith
  have hratio : E / (E - 1) ≤ (d + D) / b := by
    apply (div_le_div_iff₀ hx hb0).2
    nlinarith [hratioRaw]

  have hAden : 0 < b * d * e := mul_pos (mul_pos hb0 hd0) he0
  have hAlower :
      c / b + c * D / (b * d) + c * E / (d * e) + 1 / e ≤ A := by
    calc
      c / b + c * D / (b * d) + c * E / (d * e) + 1 / e =
          (c * d * e + c * D * e + b * c * E + b * d) /
            (b * d * e) := by
        field_simp [hb0.ne', hd0.ne', he0.ne'] <;> ring
      _ ≤ A := (div_le_iff₀ hAden).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hA)
  have hCDden : 0 < e * c := mul_pos he0 hc0
  have hCDlower :
      1 + E / e + d / (e * c) + d / c ≤ C + D := by
    calc
      1 + E / e + d / (e * c) + d / c =
          (e * c + c * E + d + d * e) / (e * c) := by
        field_simp [he0.ne', hc0.ne'] <;> ring
      _ ≤ C + D := (div_le_iff₀ hCDden).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hCD)

  let x : ℝ := E - 1
  let t : ℝ := c / d
  have hx0 : 0 < x := by simpa [x] using hx
  have ht0 : 0 < t := div_pos hc0 hd0
  have hratioScaled : t * (E / (E - 1)) ≤ t * ((d + D) / b) :=
    mul_le_mul_of_nonneg_left hratio ht0.le
  have hfirst : t + t / x ≤ c / b + c * D / (b * d) := by
    have hleft : t + t / x = t * (E / (E - 1)) := by
      dsimp [t, x]
      field_simp [hd0.ne', hx.ne'] <;> ring
    have hright : t * ((d + D) / b) = c / b + c * D / (b * d) := by
      dsimp [t]
      field_simp [hb0.ne', hd0.ne'] <;> ring
    calc
      t + t / x = t * (E / (E - 1)) := hleft
      _ ≤ t * ((d + D) / b) := hratioScaled
      _ = c / b + c * D / (b * d) := hright
  have hmiddle : c * E / (d * e) = t * x / e + t / e := by
    dsimp [t, x]
    field_simp [hd0.ne', he0.ne'] <;> ring
  have hAlower' :
      t + t / x + t * x / e + t / e + 1 / e ≤ A := by
    rw [hmiddle] at hAlower
    nlinarith [hfirst, hAlower]
  have hCDlower' :
      1 + x / e + 1 / e + 1 / (e * t) + 1 / t ≤ C + D := by
    have hEid : E / e = x / e + 1 / e := by
      dsimp [x]
      field_simp [he0.ne'] <;> ring
    have hcross : d / (e * c) = 1 / (e * t) := by
      dsimp [t]
      field_simp [hc0.ne', hd0.ne', he0.ne'] <;> ring
    have hratioId : d / c = 1 / t := by
      dsimp [t]
      field_simp [hc0.ne', hd0.ne'] <;> ring
    rw [hEid, hcross, hratioId] at hCDlower
    simpa [add_assoc] using hCDlower
  have hfull :
      5 + (t + t / x + t * x / e + t / e + 1 / t +
        1 / (e * t) + x / e + 2 / e + x + e) ≤
        A + B + C + D + E + F := by
    have hEid : E = x + 1 := by dsimp [x]; ring
    have hsum := add_le_add
      (add_le_add hAlower' hCDlower') (add_le_add hB hF)
    have hsumE := add_le_add_right hsum E
    rw [hEid] at hsumE ⊢
    ring_nf at hsumE ⊢
    exact hsumE
  have hsubset :
      hullSixThreeThreeP033Laurent t x e ≤
        t + t / x + t * x / e + t / e + 1 / t +
          1 / (e * t) + x / e + 2 / e + x + e := by
    unfold hullSixThreeThreeP033Laurent
    have htxe : 0 ≤ t * x / e := by positivity
    have hxe : 0 ≤ x / e := by positivity
    linarith
  have hstrict := p033_laurent_gt ht0 hx0 he0
  nlinarith

end Heilbronn8
