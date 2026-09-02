import Heilbronn8.TriHull.HullSevenType7Cyclic
import Mathlib.Analysis.MeanInequalities

/-!
# Compact closure for the retained hull-seven type-3 chamber

This module closes the population-61 chamber without a generated certificate.
It has three independent layers.

* `HullSevenType3ScalarData` contains the six-variable inequality system used
  by the analytic proof.
* `HullSevenType3ChordInput` contains only positive determinant magnitudes,
  Pluecker identities, consecutive-triangle caps, and the fan-area bound.
* `HullSevenType3PointData` is an honest two-dimensional determinant adapter
  for the reoriented rays

  `w = (v0,v1,v2,v4,v5,v6,-v3)`.

In the `w` coordinates every one-, two-, and three-step bracket is positive.
The original fan variables are

```text
a0=d01, A=d12, q=d23, D=d34, a5=d45,
B=d62, C=d36, G=d50.
```

The proof has two genuinely geometric ingredients.  A two-row Farkas
elimination gives

`(q-1)(A-1)(D-1) >= (A-1)+(D-1)`.

Six short Pluecker cancellations give

`G*sqrt(A*D) >= sqrt(G+1)+sqrt(G*q+1)`.

After averaging the two resulting lower bounds for `A+D`, a seven-term,
seventeen-copy AM--GM certificate proves the strict bound `25/2 < H`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

open scoped BigOperators

/-! ## A small reusable weighted AM--GM lemma -/

private lemma type3_weighted_amgm_nat
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

noncomputable def hullSevenType3Laurent (X Y : ℝ) : ℝ :=
  X ^ 2 + Y ^ 2 + 2 / Y ^ 2 + 7 * X / 5 +
    89 / (70 * X) + 4 * Y / (7 * X) + 89 / (70 * X ^ 2)

noncomputable def hullSevenType3AMGMTerm (X Y : ℝ) : Fin 7 → ℝ :=
  ![X ^ 2, Y ^ 2, 2 / Y ^ 2, 7 * X / 5,
    89 / (70 * X), 4 * Y / (7 * X), 89 / (70 * X ^ 2)]

def hullSevenType3AMGMWeight : Fin 7 → ℕ :=
  ![2, 2, 3, 4, 2, 2, 2]

noncomputable def hullSevenType3AMGMConstant : ℝ :=
  (89 : ℝ) ^ 4 / 16934400000000

private lemma hullSevenType3_weight_pos (i : Fin 7) :
    0 < hullSevenType3AMGMWeight i := by
  fin_cases i <;> norm_num [hullSevenType3AMGMWeight]

private lemma hullSevenType3_weight_sum :
    ∑ i, hullSevenType3AMGMWeight i = 17 := by
  norm_num [hullSevenType3AMGMWeight, Fin.sum_univ_succ]

private lemma hullSevenType3_term_nonneg {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (i : Fin 7) :
    0 ≤ hullSevenType3AMGMTerm X Y i := by
  fin_cases i <;> simp [hullSevenType3AMGMTerm] <;> positivity

private lemma hullSevenType3_term_sum (X Y : ℝ) :
    ∑ i, hullSevenType3AMGMTerm X Y i = hullSevenType3Laurent X Y := by
  simp [hullSevenType3AMGMTerm, hullSevenType3Laurent,
    Fin.sum_univ_succ] <;> ring

private lemma hullSevenType3_term_product {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) :
    (∏ i,
        (hullSevenType3AMGMTerm X Y i /
          (hullSevenType3AMGMWeight i : ℝ)) ^
            hullSevenType3AMGMWeight i) =
      hullSevenType3AMGMConstant := by
  simp [hullSevenType3AMGMTerm, hullSevenType3AMGMWeight,
    Fin.prod_univ_succ, hullSevenType3AMGMConstant]
  field_simp [hX.ne', hY.ne']
  ring

private lemma hullSevenType3_constant_pos :
    0 < hullSevenType3AMGMConstant := by
  unfold hullSevenType3AMGMConstant
  positivity

/-- Exact integer endpoint of the seventeen-copy AM--GM certificate. -/
private lemma hullSevenType3_integer_gap :
    (3 : ℕ) ^ 71 * 7 ^ 2 < 4 * 5 ^ 9 * 17 ^ 17 * 89 ^ 4 := by
  norm_num

private lemma hullSevenType3_root_gap :
    (81 : ℝ) / 10 <
      17 * hullSevenType3AMGMConstant ^ ((17 : ℝ)⁻¹) := by
  have hpow :
      ((81 : ℝ) / 170) ^ 17 < hullSevenType3AMGMConstant := by
    norm_num [hullSevenType3AMGMConstant]
  have hpowRpow :
      ((81 : ℝ) / 170) ^ (17 : ℝ) < hullSevenType3AMGMConstant := by
    change ((81 : ℝ) / 170) ^ ((17 : ℕ) : ℝ) <
      hullSevenType3AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (81 : ℝ) / 170 <
        hullSevenType3AMGMConstant ^ ((17 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSevenType3_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

private lemma hullSevenType3_laurent_gt {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) :
    (81 : ℝ) / 10 < hullSevenType3Laurent X Y := by
  have hamgm := type3_weighted_amgm_nat
    hullSevenType3AMGMWeight (hullSevenType3AMGMTerm X Y)
    hullSevenType3_weight_pos
    (hullSevenType3_term_nonneg hX.le hY.le)
  rw [hullSevenType3_weight_sum,
    hullSevenType3_term_product hX hY] at hamgm
  rw [← hullSevenType3_term_sum X Y]
  exact hullSevenType3_root_gap.trans_le hamgm

/-! ## The endpoint Farkas elimination -/

/-- The two endpoint rows force the reciprocal interval inequality. -/
private lemma hullSevenType3_endpoint_interval
    {A B C D q : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hq : 1 ≤ q) (hqEar : q ≤ B + C - 1)
    (hleft :
      A ^ 2 * (C - 1) ≤ ((A - 1) * (q - 1) - 1) * (A + B))
    (hright :
      D ^ 2 * (B - 1) ≤ ((D - 1) * (q - 1) - 1) * (C + D)) :
    (A - 1) + (D - 1) ≤ (q - 1) * (A - 1) * (D - 1) := by
  let x := A - 1
  let y := D - 1
  let t := q - 1
  let b := B - 1
  let c := C - 1
  let kA := x * t - 1
  let kD := y * t - 1
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hkA : 0 ≤ kA := by
    by_contra hn
    have hkAneg : kA < 0 := lt_of_not_ge hn
    have hsum : 0 < A + B := by linarith
    have hneg : kA * (A + B) < 0 := mul_neg_of_neg_of_pos hkAneg hsum
    have hnonneg : 0 ≤ A ^ 2 * (C - 1) := mul_nonneg (sq_nonneg A) hc0
    dsimp [x, t, kA] at hneg
    linarith
  have hkD : 0 ≤ kD := by
    by_contra hn
    have hkDneg : kD < 0 := lt_of_not_ge hn
    have hsum : 0 < C + D := by linarith
    have hneg : kD * (C + D) < 0 := mul_neg_of_neg_of_pos hkDneg hsum
    have hnonneg : 0 ≤ D ^ 2 * (B - 1) := mul_nonneg (sq_nonneg D) hb0
    dsimp [y, t, kD] at hneg
    linarith
  have hx : 0 < x := by
    by_contra hn
    have hxle : x ≤ 0 := le_of_not_gt hn
    have hprod : x * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxle ht0
    dsimp [kA] at hkA
    linarith
  have hy : 0 < y := by
    by_contra hn
    have hyle : y ≤ 0 := le_of_not_gt hn
    have hprod : y * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hyle ht0
    dsimp [kD] at hkD
    linarith
  have ht : 0 < t := by
    by_contra hn
    have htle : t ≤ 0 := le_of_not_gt hn
    have hprod : x * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx.le htle
    dsimp [kA] at hkA
    linarith
  by_contra hn
  have hh : t * x * y < x + y := by
    dsimp [x, y, t]
    exact lt_of_not_ge hn
  have hkAlt : kA < x / y := by
    apply (lt_div_iff₀ hy).2
    dsimp [kA]
    nlinarith
  have hkDlt : kD < y / x := by
    apply (lt_div_iff₀ hx).2
    dsimp [kD]
    nlinarith
  have hkProd : kA * kD < 1 := by
    rcases hkD.eq_or_lt with hkDz | hkDpos
    · rw [← hkDz]
      norm_num
    · calc
        kA * kD < (x / y) * kD := mul_lt_mul_of_pos_right hkAlt hkDpos
        _ ≤ (x / y) * (y / x) :=
          mul_le_mul_of_nonneg_left hkDlt.le (by positivity)
        _ = 1 := by field_simp [hx.ne', hy.ne']
  let delta := A ^ 2 * D ^ 2 - kA * kD
  have hA2 : 1 ≤ A ^ 2 := by nlinarith [sq_nonneg (A - 1)]
  have hD2 : 1 ≤ D ^ 2 := by nlinarith [sq_nonneg (D - 1)]
  have hAD2 : 1 ≤ A ^ 2 * D ^ 2 :=
    by simpa using mul_le_mul hA2 hD2 (by norm_num) (by positivity)
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hleft' : A ^ 2 * c - kA * b ≤ kA * (A + 1) := by
    dsimp [b, c, x, t, kA] at hleft ⊢
    nlinarith
  have hright' : D ^ 2 * b - kD * c ≤ kD * (D + 1) := by
    dsimp [b, c, y, t, kD] at hright ⊢
    nlinarith
  have hwA := mul_le_mul_of_nonneg_left hleft'
    (add_nonneg (sq_nonneg D) hkD)
  have hwD := mul_le_mul_of_nonneg_left hright'
    (add_nonneg (sq_nonneg A) hkA)
  have hweighted := add_le_add hwA hwD
  have hweightedIdentity :
      (D ^ 2 + kD) * (A ^ 2 * c - kA * b) +
          (A ^ 2 + kA) * (D ^ 2 * b - kD * c) =
        delta * (b + c) := by
    dsimp [delta]
    ring
  rw [hweightedIdentity] at hweighted
  have htbc : t ≤ b + c := by
    dsimp [t, b, c]
    linarith
  have hscale := mul_le_mul_of_nonneg_left htbc hdelta.le
  have htdelta :
      t * delta ≤
        (D ^ 2 + kD) * (kA * (A + 1)) +
          (A ^ 2 + kA) * (kD * (D + 1)) := by
    calc
      t * delta = delta * t := by ring
      _ ≤ delta * (b + c) := hscale
      _ ≤ (D ^ 2 + kD) * (kA * (A + 1)) +
          (A ^ 2 + kA) * (kD * (D + 1)) := hweighted
  have hfactor :
      (D ^ 2 + kD) * (kA * (A + 1)) +
          (A ^ 2 + kA) * (kD * (D + 1)) - t * delta =
        (A + t + 1) * (D + t + 1) * (t * x * y - x - y) := by
    dsimp [x, y, kA, kD, delta]
    ring
  have hfactorPos : 0 < (A + t + 1) * (D + t + 1) := by positivity
  have hfactorNeg :
      (A + t + 1) * (D + t + 1) * (t * x * y - x - y) < 0 :=
    mul_neg_of_pos_of_neg hfactorPos (by linarith)
  linarith

private lemma hullSevenType3_endpoint_AD_lower
    {A D q : ℝ} (hA : 1 < A) (hD : 1 < D) (hq : 1 < q)
    (hinterval :
      (A - 1) + (D - 1) ≤ (q - 1) * (A - 1) * (D - 1)) :
    2 + 4 / (q - 1) ≤ A + D := by
  let x := A - 1
  let y := D - 1
  let t := q - 1
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have hxy : 4 * x * y ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have hscaled := mul_le_mul_of_nonneg_left hxy ht.le
  have hchain : 4 * (x + y) ≤ t * (x + y) ^ 2 := by
    dsimp [x, y, t] at hinterval ⊢
    nlinarith
  have hcancel : 4 ≤ t * (x + y) := by
    have hsum : 0 < x + y := add_pos hx hy
    have hm : (x + y) * 4 ≤ (x + y) * (t * (x + y)) := by
      nlinarith [hchain]
    exact (mul_le_mul_iff_of_pos_left hsum).mp hm
  have hdiv : 4 / t ≤ x + y :=
    (div_le_iff₀ ht).2 (by simpa [mul_comm] using hcancel)
  dsimp [t, x, y] at hdiv
  linarith

/-! ## The scalar closer -/

structure HullSevenType3ScalarData (H : ℝ) where
  a0 : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  a5 : ℝ
  G : ℝ
  q : ℝ
  a0_ge : 1 ≤ a0
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  C_ge : 1 ≤ C
  D_ge : 1 ≤ D
  a5_ge : 1 ≤ a5
  G_ge : 1 ≤ G
  q_ge : 1 ≤ q
  q_ear : q ≤ B + C - 1
  left_endpoint :
    A ^ 2 * (C - 1) ≤ ((A - 1) * (q - 1) - 1) * (A + B)
  right_endpoint :
    D ^ 2 * (B - 1) ≤ ((D - 1) * (q - 1) - 1) * (C + D)
  endpoint_product : G + 1 ≤ a0 * a5
  radical :
    Real.sqrt (G + 1) + Real.sqrt (G * q + 1) ≤
      G * Real.sqrt (A * D)
  area : a0 + A + B + C + D + a5 + G ≤ H

private lemma hullSevenType3_sqrt_bound_one {G X : ℝ}
    (hG : 0 ≤ G) (hX : 0 ≤ X) (hXsq : X ^ 2 = G) :
    (7 : ℝ) / 10 * (X + 1) < Real.sqrt (G + 1) := by
  have hrad : 0 ≤ G + 1 := by linarith
  have hsqrtSq : Real.sqrt (G + 1) ^ 2 = G + 1 := Real.sq_sqrt hrad
  have hcauchy : (X + 1) ^ 2 ≤ 2 * (G + 1) := by
    rw [← hXsq]
    nlinarith [sq_nonneg (X - 1)]
  have hsquare :
      ((7 : ℝ) / 10 * (X + 1)) ^ 2 < Real.sqrt (G + 1) ^ 2 := by
    rw [hsqrtSq]
    have hpos : 0 < G + 1 := by linarith
    nlinarith
  exact (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsquare

private lemma hullSevenType3_sqrt_bound_three {G t X Y : ℝ}
    (hG : 0 ≤ G) (ht : 0 ≤ t) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXsq : X ^ 2 = G) (hYsq : Y ^ 2 = t) :
    (4 : ℝ) / 7 * (X + X * Y + 1) <
      Real.sqrt (G * (1 + t) + 1) := by
  have hrad : 0 ≤ G * (1 + t) + 1 := by positivity
  have hsqrtSq :
      Real.sqrt (G * (1 + t) + 1) ^ 2 = G * (1 + t) + 1 :=
    Real.sq_sqrt hrad
  have hcauchy :
      (X + X * Y + 1) ^ 2 ≤
        3 * (G * (1 + t) + 1) := by
    have hsquares : 0 ≤
        (X - X * Y) ^ 2 + (X - 1) ^ 2 + (X * Y - 1) ^ 2 := by positivity
    rw [← hXsq, ← hYsq]
    nlinarith
  have hsquare :
      ((4 : ℝ) / 7 * (X + X * Y + 1)) ^ 2 <
        Real.sqrt (G * (1 + t) + 1) ^ 2 := by
    rw [hsqrtSq]
    have hpos : 0 < G * (1 + t) + 1 := by positivity
    nlinarith
  exact (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsquare

/-- The retained type-3 scalar system has area strictly above `25/2`. -/
theorem hullSevenType3_area_gt {H : ℝ}
    (S : HullSevenType3ScalarData H) : (25 : ℝ) / 2 < H := by
  have hinterval := hullSevenType3_endpoint_interval
    S.A_ge S.B_ge S.C_ge S.D_ge S.q_ge S.q_ear
    S.left_endpoint S.right_endpoint
  have hA : 1 < S.A := by
    by_contra hn
    have hAle : S.A ≤ 1 := le_of_not_gt hn
    have hfactor : (S.A - 1) * (S.q - 1) - 1 < 0 := by
      have : (S.A - 1) * (S.q - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [S.q_ge])
      linarith
    have hsum : 0 < S.A + S.B := by linarith [S.A_ge, S.B_ge]
    have hneg := mul_neg_of_neg_of_pos hfactor hsum
    have hnonneg : 0 ≤ S.A ^ 2 * (S.C - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith [S.C_ge])
    linarith [S.left_endpoint]
  have hD : 1 < S.D := by
    by_contra hn
    have hDle : S.D ≤ 1 := le_of_not_gt hn
    have hfactor : (S.D - 1) * (S.q - 1) - 1 < 0 := by
      have : (S.D - 1) * (S.q - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [S.q_ge])
      linarith
    have hsum : 0 < S.C + S.D := by linarith [S.C_ge, S.D_ge]
    have hneg := mul_neg_of_neg_of_pos hfactor hsum
    have hnonneg : 0 ≤ S.D ^ 2 * (S.B - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith [S.B_ge])
    linarith [S.right_endpoint]
  have hq : 1 < S.q := by
    by_contra hn
    have hqle : S.q ≤ 1 := le_of_not_gt hn
    have hfactor : (S.A - 1) * (S.q - 1) - 1 < 0 := by
      have : (S.A - 1) * (S.q - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith [hA]) (by linarith)
      linarith
    have hsum : 0 < S.A + S.B := by linarith [S.A_ge, S.B_ge]
    have hneg := mul_neg_of_neg_of_pos hfactor hsum
    have hnonneg : 0 ≤ S.A ^ 2 * (S.C - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith [S.C_ge])
    linarith [S.left_endpoint]
  have hendpointAD := hullSevenType3_endpoint_AD_lower hA hD hq hinterval
  have hG : 0 < S.G := lt_of_lt_of_le (by norm_num) S.G_ge
  have hA0 : 0 ≤ S.A := le_trans (by norm_num) hA.le
  have hD0 : 0 ≤ S.D := le_trans (by norm_num) hD.le
  have hAD : 0 ≤ S.A * S.D := mul_nonneg hA0 hD0
  have hsqrtAD : 0 ≤ Real.sqrt (S.A * S.D) := Real.sqrt_nonneg _
  have hsumAD : 2 * Real.sqrt (S.A * S.D) ≤ S.A + S.D := by
    have hs := sq_nonneg (Real.sqrt S.A - Real.sqrt S.D)
    have hAsq := Real.sq_sqrt hA0
    have hDsq := Real.sq_sqrt hD0
    have hmul : Real.sqrt S.A * Real.sqrt S.D = Real.sqrt (S.A * S.D) := by
      rw [Real.sqrt_mul hA0]
    nlinarith
  have hradicalAD :
      2 * (Real.sqrt (S.G + 1) + Real.sqrt (S.G * S.q + 1)) / S.G ≤
        S.A + S.D := by
    have hdiv :
        2 * (Real.sqrt (S.G + 1) + Real.sqrt (S.G * S.q + 1)) / S.G ≤
          2 * Real.sqrt (S.A * S.D) := by
      apply (div_le_iff₀ hG).2
      nlinarith [S.radical]
    exact hdiv.trans hsumAD
  have hends : 2 * Real.sqrt (S.G + 1) ≤ S.a0 + S.a5 := by
    have hprod : S.G + 1 ≤ S.a0 * S.a5 := S.endpoint_product
    have hcross : 4 * S.a0 * S.a5 ≤ (S.a0 + S.a5) ^ 2 := by
      nlinarith [sq_nonneg (S.a0 - S.a5)]
    have hsqrtSq := Real.sq_sqrt (by linarith [S.G_ge] : 0 ≤ S.G + 1)
    have hsquare : (2 * Real.sqrt (S.G + 1)) ^ 2 ≤
        (S.a0 + S.a5) ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) (by linarith [S.a0_ge, S.a5_ge])).mp hsquare
  have hmiddle : S.q + 1 ≤ S.B + S.C := by linarith [S.q_ear]
  let t := S.q - 1
  let X := Real.sqrt S.G
  let Y := Real.sqrt t
  let u := Real.sqrt (S.G + 1)
  let v := Real.sqrt (S.G * (1 + t) + 1)
  have ht : 0 < t := by dsimp [t]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hXsq : X ^ 2 = S.G := by
    dsimp [X]
    exact Real.sq_sqrt hG.le
  have hYsq : Y ^ 2 = t := by
    dsimp [Y]
    exact Real.sq_sqrt ht.le
  have huBound : (7 : ℝ) / 10 * (X + 1) < u := by
    dsimp [u]
    exact hullSevenType3_sqrt_bound_one hG.le hX.le hXsq
  have hvBound : (4 : ℝ) / 7 * (X + X * Y + 1) < v := by
    dsimp [v]
    exact hullSevenType3_sqrt_bound_three hG.le ht.le hX.le hY.le hXsq hYsq
  have hbase :
      S.G + 3 + t + 2 / t + 2 * u + (u + v) / S.G ≤
        S.a0 + S.A + S.B + S.C + S.D + S.a5 + S.G := by
    dsimp [t, u, v]
    simp only [show (1 + (S.q - 1) : ℝ) = S.q by ring]
    have havg :
        (2 + 4 / (S.q - 1) +
          2 * (Real.sqrt (S.G + 1) + Real.sqrt (S.G * S.q + 1)) / S.G) / 2 ≤
          S.A + S.D := by
      linarith [hendpointAD, hradicalAD]
    have hsum := add_le_add (add_le_add havg hends) hmiddle
    calc
      S.G + 3 + (S.q - 1) + 2 / (S.q - 1) +
          2 * Real.sqrt (S.G + 1) +
          (Real.sqrt (S.G + 1) + Real.sqrt (S.G * S.q + 1)) / S.G =
        S.G + (((2 + 4 / (S.q - 1) +
          2 * (Real.sqrt (S.G + 1) + Real.sqrt (S.G * S.q + 1)) / S.G) / 2 +
          2 * Real.sqrt (S.G + 1)) + (S.q + 1)) := by ring
      _ ≤ S.G + (((S.A + S.D) + (S.a0 + S.a5)) + (S.B + S.C)) :=
        add_le_add_right hsum S.G
      _ = S.a0 + S.A + S.B + S.C + S.D + S.a5 + S.G := by ring
  have hstrict :
      (22 : ℝ) / 5 + hullSevenType3Laurent X Y <
        S.G + 3 + t + 2 / t + 2 * u + (u + v) / S.G := by
    have hGform : S.G = X ^ 2 := hXsq.symm
    have htform : t = Y ^ 2 := hYsq.symm
    rw [hGform, htform]
    let u0 : ℝ := (7 : ℝ) / 10 * (X + 1)
    let v0 : ℝ := (4 : ℝ) / 7 * (X + X * Y + 1)
    have hu0 : u0 < u := by simpa [u0] using huBound
    have hv0 : v0 < v := by simpa [v0] using hvBound
    have hsum0 : u0 + v0 < u + v := add_lt_add hu0 hv0
    have hdiv0 : (u0 + v0) / X ^ 2 < (u + v) / X ^ 2 :=
      div_lt_div_of_pos_right hsum0 (sq_pos_of_pos hX)
    have htwice0 : 2 * u0 < 2 * u :=
      mul_lt_mul_of_pos_left hu0 (by norm_num)
    have hcombined :
        2 * u0 + (u0 + v0) / X ^ 2 <
          2 * u + (u + v) / X ^ 2 :=
      add_lt_add htwice0 hdiv0
    have hidentity :
        (22 : ℝ) / 5 + hullSevenType3Laurent X Y =
          (X ^ 2 + 3 + Y ^ 2 + 2 / Y ^ 2) +
            (2 * u0 + (u0 + v0) / X ^ 2) := by
      dsimp [u0, v0, hullSevenType3Laurent]
      field_simp [hX.ne', hY.ne']
      ring
    rw [hidentity]
    convert add_lt_add_left hcombined (X ^ 2 + 3 + Y ^ 2 + 2 / Y ^ 2) using 1 <;>
      ring
  have hLaurent := hullSevenType3_laurent_gt hX hY
  have htotal : (25 : ℝ) / 2 <
      S.a0 + S.A + S.B + S.C + S.D + S.a5 + S.G := by
    nlinarith [hLaurent, hstrict, hbase]
  exact htotal.trans_le S.area

/-! ## Positive-chord input and its scalar projection -/

/-- The exact positive determinant packet used by the retained type-3
presentation.  No coordinate-box or generated-certificate hypothesis occurs
here: the fields are unit determinant floors, five ear caps, ten rank-two
Pluecker rows, and the fan-area row.

The variables are the following brackets of the reoriented seven-cycle:

```text
a0=d01, A=d12, q=d23, D=d34, a5=d45,
e0=d02, L=d13, R=d24, e1=d35, r=d46, G=d50, p=d61,
l=d03, c=d14, m=d25, C=d36, n=d40, h=d51, B=d62.
```
-/
structure HullSevenType3ChordInput (H : ℝ) where
  a0 : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  a5 : ℝ
  G : ℝ
  p : ℝ
  q : ℝ
  r : ℝ
  L : ℝ
  R : ℝ
  e0 : ℝ
  e1 : ℝ
  c : ℝ
  l : ℝ
  m : ℝ
  n : ℝ
  h : ℝ
  a0_ge : 1 ≤ a0
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  C_ge : 1 ≤ C
  D_ge : 1 ≤ D
  a5_ge : 1 ≤ a5
  G_ge : 1 ≤ G
  p_ge : 1 ≤ p
  q_ge : 1 ≤ q
  r_ge : 1 ≤ r
  L_ge : 1 ≤ L
  R_ge : 1 ≤ R
  e0_ge : 1 ≤ e0
  e1_ge : 1 ≤ e1
  c_ge : 1 ≤ c
  l_ge : 1 ≤ l
  m_ge : 1 ≤ m
  n_ge : 1 ≤ n
  h_ge : 1 ≤ h
  e0_ear : e0 ≤ a0 + A - 1
  p_ear : p ≤ A + B - 1
  q_ear : q ≤ B + C - 1
  r_ear : r ≤ C + D - 1
  e1_ear : e1 ≤ D + a5 - 1
  e0L : e0 * L = a0 * q + A * l
  BL : B * L = q * p - A * C
  CR : C * R = q * r - D * B
  e1R : e1 * R = q * a5 + D * m
  a0D : a0 * D = n * L + c * l
  Aa5 : A * a5 = R * h + c * m
  a0a5 : a0 * a5 = c * G + n * h
  gL : G * L = h * l + a0 * e1
  gR : G * R = n * m + a5 * e0
  e0e1 : e0 * e1 = l * m + G * q
  area : a0 + A + B + C + D + a5 + G ≤ H

/-- A short endpoint argument preserving the lower endpoint ear after the
outer endpoint variable is forgotten. -/
private lemma hullSevenType3_endpoint_ear_preserved
    {a A B C q L : ℝ}
    (ha : 1 ≤ a) (hA : 1 ≤ A) (hB : 0 < B) (hC : 1 ≤ C)
    (hq : 0 < q)
    (hupper : B * L ≤ q * (A + B - 1) - A * C)
    (horiginal : A + a * q ≤ L * (a + A - 1)) :
    0 ≤ (L - q) + L * (A - 1) - A := by
  by_contra hnot
  have hfail : (L - q) + L * (A - 1) - A < 0 := lt_of_not_ge hnot
  have horiginal' : 0 ≤ a * (L - q) + L * (A - 1) - A := by
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
  have hqB : q * B < L * B := mul_lt_mul_of_pos_right hLq hB
  have hbig : A * C < q * (A - 1) := by
    nlinarith [hqB, hupper]
  have hAC : A ≤ A * C := by
    have hm := mul_nonneg (le_trans (by norm_num) hA)
      (sub_nonneg.mpr hC)
    nlinarith
  have hqA : q * A < L * A :=
    mul_lt_mul_of_pos_right hLq (lt_of_lt_of_le (by norm_num) hA)
  have hsmall : q * (A - 1) < A := by
    nlinarith [hqA, hfail]
  linarith

private lemma HullSevenType3ChordInput.left_scalar_endpoint
    {H : ℝ} (X : HullSevenType3ChordInput H) :
    X.A ^ 2 * (X.C - 1) ≤
      ((X.A - 1) * (X.q - 1) - 1) * (X.A + X.B) := by
  have hA0 : 0 < X.A := lt_of_lt_of_le (by norm_num) X.A_ge
  have hB0 : 0 < X.B := lt_of_lt_of_le (by norm_num) X.B_ge
  have hq0 : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hupper :
      X.B * X.L ≤ X.q * (X.A + X.B - 1) - X.A * X.C := by
    rw [X.BL]
    have hm := mul_le_mul_of_nonneg_left X.p_ear
      (le_trans (by norm_num) X.q_ge)
    linarith
  have hAl : X.A ≤ X.A * X.l := by
    nlinarith [mul_nonneg (le_trans (by norm_num) X.A_ge)
      (sub_nonneg.mpr X.l_ge)]
  have horiginal : X.A + X.a0 * X.q ≤
      X.L * (X.a0 + X.A - 1) := by
    have hleft : X.A + X.a0 * X.q ≤ X.e0 * X.L := by
      rw [X.e0L]
      nlinarith [hAl]
    have hm := mul_le_mul_of_nonneg_right X.e0_ear
      (le_trans (by norm_num) X.L_ge)
    nlinarith [hleft, hm]
  have hear := hullSevenType3_endpoint_ear_preserved X.a0_ge X.A_ge
    hB0 X.C_ge hq0 hupper horiginal
  have hAL : X.A + X.q ≤ X.A * X.L := by nlinarith [hear]
  have hlower := mul_le_mul_of_nonneg_left hAL
    (le_trans (by norm_num) X.B_ge)
  have hupperscaled := mul_le_mul_of_nonneg_left hupper
    (le_trans (by norm_num) X.A_ge)
  nlinarith

private lemma HullSevenType3ChordInput.right_scalar_endpoint
    {H : ℝ} (X : HullSevenType3ChordInput H) :
    X.D ^ 2 * (X.B - 1) ≤
      ((X.D - 1) * (X.q - 1) - 1) * (X.C + X.D) := by
  have hD0 : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
  have hC0 : 0 < X.C := lt_of_lt_of_le (by norm_num) X.C_ge
  have hq0 : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hupper :
      X.C * X.R ≤ X.q * (X.D + X.C - 1) - X.D * X.B := by
    rw [X.CR]
    have hm := mul_le_mul_of_nonneg_left X.r_ear
      (le_trans (by norm_num) X.q_ge)
    linarith
  have hDm : X.D ≤ X.D * X.m := by
    nlinarith [mul_nonneg (le_trans (by norm_num) X.D_ge)
      (sub_nonneg.mpr X.m_ge)]
  have horiginal : X.D + X.a5 * X.q ≤
      X.R * (X.a5 + X.D - 1) := by
    have hleft : X.D + X.a5 * X.q ≤ X.e1 * X.R := by
      rw [X.e1R]
      nlinarith [hDm]
    have hm := mul_le_mul_of_nonneg_right X.e1_ear
      (le_trans (by norm_num) X.R_ge)
    nlinarith [hleft, hm]
  have hear := hullSevenType3_endpoint_ear_preserved X.a5_ge X.D_ge
    hC0 X.B_ge hq0 hupper horiginal
  have hDR : X.D + X.q ≤ X.D * X.R := by nlinarith [hear]
  have hlower := mul_le_mul_of_nonneg_left hDR
    (le_trans (by norm_num) X.C_ge)
  have hupperscaled := mul_le_mul_of_nonneg_left hupper
    (le_trans (by norm_num) X.D_ge)
  nlinarith

private lemma HullSevenType3ChordInput.GD_identity
    {H : ℝ} (X : HullSevenType3ChordInput H) :
    X.G * X.D = X.l * X.a5 + X.n * X.e1 := by
  have hcg : X.c * X.G = X.a0 * X.a5 - X.n * X.h := by
    nlinarith [X.a0a5]
  have hcancel :
      X.a0 * (X.G * X.D) =
        X.a0 * (X.l * X.a5 + X.n * X.e1) := by
    calc
      X.a0 * (X.G * X.D) = X.G * (X.a0 * X.D) := by ring
      _ = X.G * (X.n * X.L + X.c * X.l) := by rw [X.a0D]
      _ = X.n * (X.G * X.L) + X.l * (X.c * X.G) := by ring
      _ = X.n * (X.h * X.l + X.a0 * X.e1) +
          X.l * (X.a0 * X.a5 - X.n * X.h) := by rw [X.gL, hcg]
      _ = X.a0 * (X.l * X.a5 + X.n * X.e1) := by ring
  have ha0 : X.a0 ≠ 0 := by linarith [X.a0_ge]
  exact mul_left_cancel₀ ha0 hcancel

private lemma HullSevenType3ChordInput.GA_identity
    {H : ℝ} (X : HullSevenType3ChordInput H) :
    X.G * X.A = X.m * X.a0 + X.h * X.e0 := by
  have hcg : X.c * X.G = X.a0 * X.a5 - X.n * X.h := by
    nlinarith [X.a0a5]
  have hcancel :
      X.a5 * (X.G * X.A) =
        X.a5 * (X.m * X.a0 + X.h * X.e0) := by
    calc
      X.a5 * (X.G * X.A) = X.G * (X.A * X.a5) := by ring
      _ = X.G * (X.R * X.h + X.c * X.m) := by rw [X.Aa5]
      _ = X.h * (X.G * X.R) + X.m * (X.c * X.G) := by ring
      _ = X.h * (X.n * X.m + X.a5 * X.e0) +
          X.m * (X.a0 * X.a5 - X.n * X.h) := by rw [X.gR, hcg]
      _ = X.a5 * (X.m * X.a0 + X.h * X.e0) := by ring
  have ha5 : X.a5 ≠ 0 := by linarith [X.a5_ge]
  exact mul_left_cancel₀ ha5 hcancel

/-- The six closing Pluecker rows imply the radical inequality used by the
scalar closer. -/
private lemma HullSevenType3ChordInput.radical_bound
    {H : ℝ} (X : HullSevenType3ChordInput H) :
    Real.sqrt (X.G + 1) + Real.sqrt (X.G * X.q + 1) ≤
      X.G * Real.sqrt (X.A * X.D) := by
  have hGD : X.a5 + X.e1 ≤ X.G * X.D := by
    rw [X.GD_identity]
    have hl := mul_le_mul_of_nonneg_right X.l_ge
      (le_trans (by norm_num) X.a5_ge)
    have hn := mul_le_mul_of_nonneg_right X.n_ge
      (le_trans (by norm_num) X.e1_ge)
    nlinarith
  have hGA : X.a0 + X.e0 ≤ X.G * X.A := by
    rw [X.GA_identity]
    have hm := mul_le_mul_of_nonneg_right X.m_ge
      (le_trans (by norm_num) X.a0_ge)
    have hh := mul_le_mul_of_nonneg_right X.h_ge
      (le_trans (by norm_num) X.e0_ge)
    nlinarith
  have hproduct :
      (X.a0 + X.e0) * (X.a5 + X.e1) ≤
        (X.G * X.A) * (X.G * X.D) :=
    mul_le_mul hGA hGD (by linarith [X.a5_ge, X.e1_ge])
      (mul_nonneg (le_trans (by norm_num) X.G_ge)
        (le_trans (by norm_num) X.A_ge))
  have hcauchy :
      (Real.sqrt (X.a0 * X.a5) + Real.sqrt (X.e0 * X.e1)) ^ 2 ≤
        (X.a0 + X.e0) * (X.a5 + X.e1) := by
    rw [Real.sqrt_mul (le_trans (by norm_num) X.a0_ge),
      Real.sqrt_mul (le_trans (by norm_num) X.e0_ge)]
    have ha0sq := Real.sq_sqrt (le_trans (by norm_num) X.a0_ge)
    have ha5sq := Real.sq_sqrt (le_trans (by norm_num) X.a5_ge)
    have he0sq := Real.sq_sqrt (le_trans (by norm_num) X.e0_ge)
    have he1sq := Real.sq_sqrt (le_trans (by norm_num) X.e1_ge)
    nlinarith [sq_nonneg
      (Real.sqrt X.a0 * Real.sqrt X.e1 -
        Real.sqrt X.e0 * Real.sqrt X.a5)]
  have hAD : 0 ≤ X.A * X.D := mul_nonneg
    (le_trans (by norm_num) X.A_ge) (le_trans (by norm_num) X.D_ge)
  have hGsqrt : 0 ≤ X.G * Real.sqrt (X.A * X.D) :=
    mul_nonneg (le_trans (by norm_num) X.G_ge) (Real.sqrt_nonneg _)
  have hsquare :
      (Real.sqrt (X.a0 * X.a5) + Real.sqrt (X.e0 * X.e1)) ^ 2 ≤
        (X.G * Real.sqrt (X.A * X.D)) ^ 2 := by
    have hsqrtAD := Real.sq_sqrt hAD
    calc
      (Real.sqrt (X.a0 * X.a5) + Real.sqrt (X.e0 * X.e1)) ^ 2 ≤
          (X.a0 + X.e0) * (X.a5 + X.e1) := hcauchy
      _ ≤ (X.G * X.A) * (X.G * X.D) := hproduct
      _ = (X.G * Real.sqrt (X.A * X.D)) ^ 2 := by
        calc
          (X.G * X.A) * (X.G * X.D) = X.G ^ 2 * (X.A * X.D) := by ring
          _ = X.G ^ 2 * Real.sqrt (X.A * X.D) ^ 2 := by rw [hsqrtAD]
          _ = (X.G * Real.sqrt (X.A * X.D)) ^ 2 := by ring
  have hrootSum :
      Real.sqrt (X.a0 * X.a5) + Real.sqrt (X.e0 * X.e1) ≤
        X.G * Real.sqrt (X.A * X.D) :=
    (sq_le_sq₀ (by positivity) hGsqrt).mp hsquare
  have hcG : X.G ≤ X.c * X.G := by
    simpa using mul_le_mul_of_nonneg_right X.c_ge
      (le_trans (by norm_num) X.G_ge)
  have hnh : 1 ≤ X.n * X.h := by
    calc
      1 ≤ X.h := X.h_ge
      _ ≤ X.n * X.h := by
        simpa using mul_le_mul_of_nonneg_right X.n_ge
          (le_trans (by norm_num) X.h_ge)
  have hfirst : Real.sqrt (X.G + 1) ≤ Real.sqrt (X.a0 * X.a5) := by
    apply Real.sqrt_le_sqrt
    nlinarith [X.a0a5, hcG, hnh]
  have hlm : 1 ≤ X.l * X.m := by
    calc
      1 ≤ X.m := X.m_ge
      _ ≤ X.l * X.m := by
        simpa using mul_le_mul_of_nonneg_right X.l_ge
          (le_trans (by norm_num) X.m_ge)
  have hsecond :
      Real.sqrt (X.G * X.q + 1) ≤ Real.sqrt (X.e0 * X.e1) := by
    apply Real.sqrt_le_sqrt
    nlinarith [X.e0e1, hlm]
  linarith

/-- Exact projection from positive determinant magnitudes to the compact
type-3 scalar system. -/
noncomputable def HullSevenType3ChordInput.toScalarData
    {H : ℝ} (X : HullSevenType3ChordInput H) :
    HullSevenType3ScalarData H where
  a0 := X.a0
  A := X.A
  B := X.B
  C := X.C
  D := X.D
  a5 := X.a5
  G := X.G
  q := X.q
  a0_ge := X.a0_ge
  A_ge := X.A_ge
  B_ge := X.B_ge
  C_ge := X.C_ge
  D_ge := X.D_ge
  a5_ge := X.a5_ge
  G_ge := X.G_ge
  q_ge := X.q_ge
  q_ear := X.q_ear
  left_endpoint := X.left_scalar_endpoint
  right_endpoint := X.right_scalar_endpoint
  endpoint_product := by
    have hcG : X.G ≤ X.c * X.G := by
      simpa using mul_le_mul_of_nonneg_right X.c_ge
        (le_trans (by norm_num) X.G_ge)
    have hnh : 1 ≤ X.n * X.h := by
      calc
        1 ≤ X.h := X.h_ge
        _ ≤ X.n * X.h := by
          simpa using mul_le_mul_of_nonneg_right X.n_ge
            (le_trans (by norm_num) X.h_ge)
    nlinarith [X.a0a5, hcG, hnh]
  radical := X.radical_bound
  area := X.area

theorem hullSevenType3_area_gt_of_chord {H : ℝ}
    (X : HullSevenType3ChordInput H) : (25 : ℝ) / 2 < H :=
  hullSevenType3_area_gt X.toScalarData

/-- Direct sharp-constant consequence for a retained type-3 chord packet. -/
theorem hullSeven_v8_of_type3_chord {H : ℝ}
    (X : HullSevenType3ChordInput H) : 1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 < H := hullSevenType3_area_gt_of_chord X
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

end Heilbronn8.TriHull
