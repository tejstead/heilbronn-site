import Heilbronn8.Survivors.Join.HullSixThreeThreeSoundSemanticBridge
import Mathlib.Analysis.MeanInequalities

/-!
# The maximal-q `p = 013` X-frontier

This file closes the partial `X`-frontier with first cuts `013`.  It uses no
`Y` sign.  Around `P`, the six rays have the merged slope order

```text
U0, L0, U1, L1, L2, U2.
```

The five successive determinants in this order are at least `minTri`.  On
expanding the five non-wrap hull sectors in those successive determinants,
and using the positive `Q`-fan wrap sector, the geometry reduces to a
twelve-term Laurent inequality.  A 29-copy weighted AM--GM certificate
proves the required strict `25/2` bound.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

open scoped BigOperators

/-! ## The scalar AM--GM certificate -/

private lemma p013_weighted_amgm_nat
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

noncomputable def hullSixThreeThreeP013Laurent
    (b c d e : ℝ) : ℝ :=
  c / b + 1 / b + 1 / d + c / (d * e) + c / e +
    1 / c + b / (c * d) + b / (d * e) + b / e +
      d / c + b / c + e

noncomputable def hullSixThreeThreeP013AMGMTerm
    (b c d e : ℝ) : Fin 12 → ℝ :=
  ![c / b, 1 / b, 1 / d, c / (d * e), c / e, 1 / c,
    b / (c * d), b / (d * e), b / e, d / c, b / c, e]

def hullSixThreeThreeP013AMGMWeight : Fin 12 → ℕ :=
  ![4, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7]

noncomputable def hullSixThreeThreeP013AMGMConstant : ℝ :=
  1 / ((4 : ℝ) ^ 8 * 2 ^ 6 * 3 ^ 3 * 7 ^ 7)

private lemma p013_weight_pos (i : Fin 12) :
    0 < hullSixThreeThreeP013AMGMWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP013AMGMWeight]

private lemma p013_weight_sum :
    ∑ i, hullSixThreeThreeP013AMGMWeight i = 29 := by
  norm_num [hullSixThreeThreeP013AMGMWeight, Fin.sum_univ_succ]

private lemma p013_term_nonneg {b c d e : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (i : Fin 12) :
    0 ≤ hullSixThreeThreeP013AMGMTerm b c d e i := by
  fin_cases i <;> simp [hullSixThreeThreeP013AMGMTerm] <;> positivity

private lemma p013_term_sum (b c d e : ℝ) :
    ∑ i, hullSixThreeThreeP013AMGMTerm b c d e i =
      hullSixThreeThreeP013Laurent b c d e := by
  simp [hullSixThreeThreeP013AMGMTerm, hullSixThreeThreeP013Laurent,
    Fin.sum_univ_succ]
  <;> ring

private lemma p013_term_product {b c d e : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    (∏ i,
        (hullSixThreeThreeP013AMGMTerm b c d e i /
          (hullSixThreeThreeP013AMGMWeight i : ℝ)) ^
            hullSixThreeThreeP013AMGMWeight i) =
      hullSixThreeThreeP013AMGMConstant := by
  simp [hullSixThreeThreeP013AMGMTerm,
    hullSixThreeThreeP013AMGMWeight, Fin.prod_univ_succ,
    hullSixThreeThreeP013AMGMConstant]
  field_simp [hb.ne', hc.ne', hd.ne', he.ne']
  <;> ring

private lemma p013_constant_pos :
    0 < hullSixThreeThreeP013AMGMConstant := by
  unfold hullSixThreeThreeP013AMGMConstant
  positivity

private lemma p013_root_gap :
    (19 : ℝ) / 2 <
      29 * hullSixThreeThreeP013AMGMConstant ^ ((29 : ℝ)⁻¹) := by
  have hpow :
      ((19 : ℝ) / 58) ^ 29 < hullSixThreeThreeP013AMGMConstant := by
    norm_num [hullSixThreeThreeP013AMGMConstant]
  have hpowRpow :
      ((19 : ℝ) / 58) ^ (29 : ℝ) <
        hullSixThreeThreeP013AMGMConstant := by
    change ((19 : ℝ) / 58) ^ ((29 : ℕ) : ℝ) <
      hullSixThreeThreeP013AMGMConstant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (19 : ℝ) / 58 <
        hullSixThreeThreeP013AMGMConstant ^ ((29 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt p013_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

private lemma p013_laurent_gt {b c d e : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    (19 : ℝ) / 2 < hullSixThreeThreeP013Laurent b c d e := by
  have hamgm := p013_weighted_amgm_nat
    hullSixThreeThreeP013AMGMWeight
    (hullSixThreeThreeP013AMGMTerm b c d e)
    p013_weight_pos
    (p013_term_nonneg hb.le hc.le hd.le he.le)
  rw [p013_weight_sum, p013_term_product hb hc hd he] at hamgm
  rw [← p013_term_sum b c d e]
  exact p013_root_gap.trans_le hamgm

/-- Product-form scalar endpoint supplied by the five successive `P`-ray
floors and the positive `Q`-wrap floor. -/
theorem hullSixThreeThree_p013_scalar
    {b c d e A B C D E F H : ℝ}
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hA : c + 1 ≤ b * A)
    (hB : e + c + c * d ≤ d * e * B)
    (hC : d * e + b * e + b * c + b * c * d ≤ c * d * e * C)
    (hD : d + b ≤ c * D)
    (hE : 1 ≤ E) (hF : e + 2 ≤ F)
    (hH : A + B + C + D + E + F ≤ H) :
    25 / 2 < H := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have he0 : 0 < e := lt_of_lt_of_le zero_lt_one he
  have hde0 : 0 < d * e := mul_pos hd0 he0
  have hcde0 : 0 < c * d * e := mul_pos (mul_pos hc0 hd0) he0
  have hAlower : c / b + 1 / b ≤ A := by
    rw [← add_div]
    exact (div_le_iff₀ hb0).2 (by simpa [mul_comm] using hA)
  have hBlower : 1 / d + c / (d * e) + c / e ≤ B := by
    calc
      1 / d + c / (d * e) + c / e =
          (e + c + c * d) / (d * e) := by
        field_simp [hd0.ne', he0.ne'] <;> ring
      _ ≤ B := (div_le_iff₀ hde0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hB)
  have hClower :
      1 / c + b / (c * d) + b / (d * e) + b / e ≤ C := by
    calc
      1 / c + b / (c * d) + b / (d * e) + b / e =
          (d * e + b * e + b * c + b * c * d) / (c * d * e) := by
        field_simp [hc0.ne', hd0.ne', he0.ne'] <;> ring
      _ ≤ C := (div_le_iff₀ hcde0).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hC)
  have hDlower : d / c + b / c ≤ D := by
    rw [← add_div]
    exact (div_le_iff₀ hc0).2 (by simpa [mul_comm] using hD)
  have hLaurent :
      hullSixThreeThreeP013Laurent b c d e + 3 ≤
        A + B + C + D + E + F := by
    unfold hullSixThreeThreeP013Laurent
    linarith
  have hstrict := p013_laurent_gt hb0 hc0 hd0 he0
  nlinarith

/-! ## Determinant adapter -/

private lemma p013_shiftedBoundary_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : ∀ i, 0 < sig (cfg base) (cfg (cycle i)) (cfg (cycle (i + 1))))
    (rotation offset : Fin 6) :
    minTri cfg ≤ sig (cfg base) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig cfg cycle R.cycle_injective
    base hOutside (rotation + offset) (hpos (rotation + offset))
  have hnext : (rotation + offset) + 1 = rotation + (offset + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

namespace HullSixCompactCrossChordResidual

/-- The `p = 013` successive-ray floors contradict a beating normalized
`3 + 3` frame. -/
theorem threeThreeP013At_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hX00 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))) ≤
      -minTri cfg)
    (hX10 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX11 : sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
      -minTri cfg)
    (hX22 : minTri cfg ≤ sig (cfg P)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2)))) :
    False := by
  let m := minTri cfg
  let U : Fin 3 → ℝ × ℝ := fun i =>
    cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))
  let L : Fin 3 → ℝ × ℝ := fun j =>
    cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))
  let a := sig (cfg P) (cfg Q) (U 0) / m
  let b := (-sig (cfg P) (cfg Q) (L 0)) / m
  let c := sig (cfg P) (cfg Q) (U 1) / m
  let d := (-sig (cfg P) (cfg Q) (L 1)) / m
  let e := (-sig (cfg P) (cfg Q) (L 2)) / m
  let f := sig (cfg P) (cfg Q) (U 2) / m
  let r1 := (-sig (cfg P) (U 0) (L 0)) / m
  let r2 := sig (cfg P) (U 1) (L 0) / m
  let r3 := (-sig (cfg P) (U 1) (L 1)) / m
  let r4 := sig (cfg P) (L 1) (L 2) / m
  let r5 := sig (cfg P) (U 2) (L 2) / m
  let A := sig (cfg P) (U 0) (U 1) / m
  let B := sig (cfg P) (U 1) (U 2) / m
  let C := sig (cfg P) (U 2) (L 0) / m
  let D := sig (cfg P) (L 0) (L 1) / m
  let E := sig (cfg P) (L 1) (L 2) / m
  let F := sig (cfg P) (L 2) (U 0) / m
  let Fq := sig (cfg Q) (L 2) (U 0) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {x : ℝ} (hx : m ≤ x) : 1 ≤ x / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hx)

  have ha : 1 ≤ a := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, a, U] using h)
  have hb : 1 ≤ b := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    exact hnorm (by simpa [m, b, L] using h)
  have hc : 1 ≤ c := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, c, U] using h)
  have hd : 1 ≤ d := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    exact hnorm (by simpa [m, d, L] using h)
  have he : 1 ≤ e := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    exact hnorm (by simpa [m, e, L] using h)
  have hf : 1 ≤ f := by
    have h := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at h
    exact hnorm (by simpa [m, f, U] using h)

  have hr1 : 1 ≤ r1 := by
    apply hnorm
    dsimp [r1, U, L]
    linarith
  have hr2 : 1 ≤ r2 := by
    exact hnorm (by simpa [m, r2, U, L] using hX10)
  have hr3 : 1 ≤ r3 := by
    apply hnorm
    dsimp [r3, U, L]
    linarith
  have hr4raw : m ≤ sig (cfg P) (L 1) (L 2) := by
    simpa [m, L, hullSixThreeThreeLowerOffset, add_assoc] using
      p013_shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
        rotation 4
  have hr4 : 1 ≤ r4 := hnorm (by simpa [r4] using hr4raw)
  have hr5 : 1 ≤ r5 := by
    exact hnorm (by simpa [m, r5, U, L] using hX22)

  have hFqRaw : m ≤ sig (cfg Q) (L 2) (U 0) := by
    simpa [m, U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset, add_assoc] using
      p013_shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos
        rotation 5
  have hFq : 1 ≤ Fq := hnorm (by simpa [Fq] using hFqRaw)
  have hFbase : Fq = F - a - e := by
    dsimp [Fq, F, a, e, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hFlower : e + 2 ≤ F := by linarith

  have hAtransport : b * A = c * r1 + a * r2 := by
    dsimp [b, A, c, r1, a, r2, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hBtransport :
      d * e * B = f * e * r3 + c * f * r4 + c * d * r5 := by
    dsimp [d, e, B, f, r3, c, r4, r5, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hCtransport :
      c * d * e * C =
        f * d * e * r2 + f * b * e * r3 +
          f * b * c * r4 + b * c * d * r5 := by
    dsimp [c, d, e, C, f, r2, b, r3, r4, r5, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hDtransport : c * D = d * r2 + b * r3 := by
    dsimp [c, D, d, r2, b, r3, U, L]
    field_simp [hmNe] <;> simp only [sig] <;> ring
  have hEid : E = r4 := by rfl

  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have he0 : 0 ≤ e := le_trans zero_le_one he
  have hf0 : 0 ≤ f := le_trans zero_le_one hf
  have hr10 : 0 ≤ r1 := le_trans zero_le_one hr1
  have hr20 : 0 ≤ r2 := le_trans zero_le_one hr2
  have hr30 : 0 ≤ r3 := le_trans zero_le_one hr3
  have hr40 : 0 ≤ r4 := le_trans zero_le_one hr4
  have hr50 : 0 ≤ r5 := le_trans zero_le_one hr5
  have hAprod : c + 1 ≤ b * A := by
    rw [hAtransport]
    have h1 : c ≤ c * r1 := by
      simpa using mul_le_mul_of_nonneg_left hr1 hc0
    have h2 : 1 ≤ a * r2 := by
      simpa using mul_le_mul ha hr2 zero_le_one ha0
    linarith
  have hBprod : e + c + c * d ≤ d * e * B := by
    rw [hBtransport]
    have h1 : e ≤ f * e * r3 := by
      calc
        e = 1 * e := by ring
        _ ≤ f * e := mul_le_mul_of_nonneg_right hf he0
        _ ≤ f * e * r3 := by
          simpa using
            mul_le_mul_of_nonneg_left hr3 (mul_nonneg hf0 he0)
    have h2 : c ≤ c * f * r4 := by
      calc
        c = c * 1 := by ring
        _ ≤ c * f := mul_le_mul_of_nonneg_left hf hc0
        _ ≤ c * f * r4 := by
          simpa using
            mul_le_mul_of_nonneg_left hr4 (mul_nonneg hc0 hf0)
    have h3 : c * d ≤ c * d * r5 := by
      simpa using mul_le_mul_of_nonneg_left hr5 (mul_nonneg hc0 hd0)
    nlinarith
  have hCprod :
      d * e + b * e + b * c + b * c * d ≤ c * d * e * C := by
    rw [hCtransport]
    have h1 : d * e ≤ f * d * e * r2 := by
      calc
        d * e = 1 * (d * e) := by ring
        _ ≤ f * (d * e) :=
          mul_le_mul_of_nonneg_right hf (mul_nonneg hd0 he0)
        _ = f * d * e := by ring
        _ ≤ f * d * e * r2 := by
          simpa using mul_le_mul_of_nonneg_left hr2
            (mul_nonneg (mul_nonneg hf0 hd0) he0)
    have h2 : b * e ≤ f * b * e * r3 := by
      calc
        b * e = 1 * (b * e) := by ring
        _ ≤ f * (b * e) :=
          mul_le_mul_of_nonneg_right hf (mul_nonneg hb0 he0)
        _ = f * b * e := by ring
        _ ≤ f * b * e * r3 := by
          simpa using mul_le_mul_of_nonneg_left hr3
            (mul_nonneg (mul_nonneg hf0 hb0) he0)
    have h3 : b * c ≤ f * b * c * r4 := by
      calc
        b * c = 1 * (b * c) := by ring
        _ ≤ f * (b * c) :=
          mul_le_mul_of_nonneg_right hf (mul_nonneg hb0 hc0)
        _ = f * b * c := by ring
        _ ≤ f * b * c * r4 := by
          simpa using mul_le_mul_of_nonneg_left hr4
            (mul_nonneg (mul_nonneg hf0 hb0) hc0)
    have h4 : b * c * d ≤ b * c * d * r5 := by
      simpa using mul_le_mul_of_nonneg_left hr5
        (mul_nonneg (mul_nonneg hb0 hc0) hd0)
    nlinarith
  have hDprod : d + b ≤ c * D := by
    rw [hDtransport]
    have h1 : d ≤ d * r2 := by
      simpa using mul_le_mul_of_nonneg_left hr2 hd0
    have h2 : b ≤ b * r3 := by
      simpa using mul_le_mul_of_nonneg_left hr3 hb0
    linarith
  have hElower : 1 ≤ E := by simpa [hEid] using hr4

  let fan : Fin 6 → ℝ := fun i =>
    sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i => sig (cfg P) (cfg (cycle (rotation + i)))
        (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun : (fun i => sig (cfg P) (cfg (cycle (rotation + i)))
          (cfg (cycle (rotation + (i + 1))))) =
        (fun i => fan (rotation + i)) := by
      funext i
      simp [fan, add_assoc]
    rw [hfun, sumFinSix_add_left]
    exact V.P_fan_sum
  have hSumRaw : doubledHullArea cfg =
      sig (cfg P) (U 0) (U 1) + sig (cfg P) (U 1) (U 2) +
      sig (cfg P) (U 2) (L 0) + sig (cfg P) (L 0) (L 1) +
      sig (cfg P) (L 1) (L 2) + sig (cfg P) (L 2) (U 0) := by
    have hraw : doubledHullArea cfg =
        sig (cfg P) (cfg (cycle rotation)) (cfg (cycle (rotation + 1))) +
        sig (cfg P) (cfg (cycle (rotation + 1)))
          (cfg (cycle (rotation + 2))) +
        sig (cfg P) (cfg (cycle (rotation + 2)))
          (cfg (cycle (rotation + 3))) +
        sig (cfg P) (cfg (cycle (rotation + 3)))
          (cfg (cycle (rotation + 4))) +
        sig (cfg P) (cfg (cycle (rotation + 4)))
          (cfg (cycle (rotation + 5))) +
        sig (cfg P) (cfg (cycle (rotation + 5)))
          (cfg (cycle rotation)) := by
      rw [← hshifted]
      simp [sumFinSix] <;> ring
    simpa [U, L, hullSixThreeThreeUpperOffset,
      hullSixThreeThreeLowerOffset] using hraw
  have hFan : H = A + B + C + D + E + F := by
    dsimp [H, A, B, C, D, E, F]
    rw [hSumRaw]
    ring

  have hscalar : 25 / 2 < H :=
    hullSixThreeThree_p013_scalar hb hc hd he hAprod hBprod hCprod
      hDprod hElower hFlower (le_of_eq hFan.symm)
  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeGeometricFrame

/-- The single maximal-q remaining frontier with first cuts `013`. -/
def IsP013RemainingFrontier (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    T.p0 = 0 ∧ T.p1 = 1 ∧ T.p2 = 3

/-- The `013` X-frontier is closed in its original frame. -/
theorem p013_xFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts)
    (hp0 : T.p0 = 0) (hp1 : T.p1 = 1) (hp2 : T.p2 = 3) :
    F.XFrontierClosed T := by
  intro hFrontier
  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00 : F.X 0 0 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp0]
  have hX10 : minTri cfg ≤ F.X 1 0 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX11 : F.X 1 1 ≤ -minTri cfg := by
    apply hNegative
    simp [HullSixThreeThreeCuts.p, hp1]
  have hX22 : minTri cfg ≤ F.X 2 2 := by
    apply hLeft
    simp [HullSixThreeThreeCuts.p, hp2]
  exact R.threeThreeP013At_false F.view F.rotation F.upper_pos F.lower_neg
    (by simpa [X] using hX00) (by simpa [X] using hX10)
    (by simpa [X] using hX11) (by simpa [X] using hX22)

end HullSixThreeThreeGeometricFrame

/-- Provider for the `p = 013`, `q = 233` X-frontier fibre. -/
theorem hullSixThreeThreeP013XFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsP013RemainingFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with ⟨hRemaining, hp0, hp1, hp2⟩
  exact F.p013_xFrontierClosed T hp0 hp1 hp2

end Heilbronn8
