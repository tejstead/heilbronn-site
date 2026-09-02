import Heilbronn8.V8
import Mathlib.Analysis.MeanInequalities

/-!
# The cyclic three-step hull-seven chamber

This module isolates a compact proof for the full-retained hull-seven order
type `type7` (population 18).  In that chamber all seven cyclic determinants

`[v_i,v_{i+3}]`

are positive.  Put

* `a_i = [v_i,v_{i+1}]`,
* `b_i = [v_i,v_{i+2}]`, and
* `u_i = [v_i,v_{i+3}]`.

After normalizing the minimum triangle area to one, every `a_i`, `b_i`, and
`u_i` is at least one.  Two cyclic Pluecker identities and the multiplicative
Minkowski inequality imply a sharp-enough quartic obstruction.  The result is
the rational bound `25/2 < sum a_i`, slightly stronger than the `v8` target.

The proof is independent of the C24 transfer and its all-above-cap branch.
-/

namespace Heilbronn8.TriHull

open scoped BigOperators

abbrev HullSevenCycleIndex := ZMod 7

/-- The geometric mean of seven nonnegative cyclic quantities. -/
noncomputable def hullSevenGeom7 (x : HullSevenCycleIndex → ℝ) : ℝ :=
  ∏ i, (x i) ^ (1 / 7 : ℝ)

private lemma hullSevenGeom7_nonneg {x : HullSevenCycleIndex → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    0 ≤ hullSevenGeom7 x := by
  unfold hullSevenGeom7
  exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx i) _

private lemma hullSevenGeom7_pos {x : HullSevenCycleIndex → ℝ}
    (hx : ∀ i, 0 < x i) :
    0 < hullSevenGeom7 x := by
  unfold hullSevenGeom7
  exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _

private lemma hullSevenGeom7_mul
    {x y : HullSevenCycleIndex → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    hullSevenGeom7 (fun i => x i * y i) =
      hullSevenGeom7 x * hullSevenGeom7 y := by
  unfold hullSevenGeom7
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.mul_rpow (hx i) (hy i)

private lemma hullSevenGeom7_div
    {x y : HullSevenCycleIndex → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    hullSevenGeom7 (fun i => x i / y i) =
      hullSevenGeom7 x / hullSevenGeom7 y := by
  unfold hullSevenGeom7
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.div_rpow (hx i) (hy i) _

private lemma hullSevenGeom7_shift
    (x : HullSevenCycleIndex → ℝ) (k : HullSevenCycleIndex) :
    hullSevenGeom7 (fun i => x (i + k)) = hullSevenGeom7 x := by
  unfold hullSevenGeom7
  simpa using
    Equiv.prod_comp (Equiv.addRight k) (fun i : HullSevenCycleIndex =>
      (x i) ^ (1 / 7 : ℝ))

private lemma hullSevenGeom7_mul_shift
    (x y : HullSevenCycleIndex → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (k l : HullSevenCycleIndex) :
    hullSevenGeom7 (fun i => x (i + k) * y (i + l)) =
      hullSevenGeom7 x * hullSevenGeom7 y := by
  rw [hullSevenGeom7_mul
    (fun i => hx (i + k)) (fun i => hy (i + l))]
  rw [hullSevenGeom7_shift, hullSevenGeom7_shift]

/-- Uniform seven-term AM-GM, in the exact form used below. -/
private lemma hullSevenGeom7_le_average
    {x : HullSevenCycleIndex → ℝ} (hx : ∀ i, 0 ≤ x i) :
    hullSevenGeom7 x ≤ (∑ i, x i) / 7 := by
  have h := Real.geom_mean_le_arith_mean_weighted
    (s := Finset.univ)
    (fun _ : HullSevenCycleIndex => (1 / 7 : ℝ)) x
    (by intro i hi; norm_num)
    (by norm_num)
    (by intro i hi; exact hx i)
  have hright :
      (∑ i : HullSevenCycleIndex, (1 / 7 : ℝ) * x i) =
        (∑ i, x i) / 7 := by
    rw [← Finset.mul_sum]
    ring
  have h' : hullSevenGeom7 x ≤
      ∑ i : HullSevenCycleIndex, (1 / 7 : ℝ) * x i := by
    simpa [hullSevenGeom7] using h
  rw [hright] at h'
  exact h'

/-- Multiplicative Minkowski for seven positive terms.

This is proved by applying AM-GM to `x_i/(x_i+y_i)` and
`y_i/(x_i+y_i)`.  It avoids any separate seventh-root API. -/
private lemma hullSevenGeom7_add
    {x y : HullSevenCycleIndex → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    hullSevenGeom7 x + hullSevenGeom7 y ≤
      hullSevenGeom7 (fun i => x i + y i) := by
  let s : HullSevenCycleIndex → ℝ := fun i => x i + y i
  let zx : HullSevenCycleIndex → ℝ := fun i => x i / s i
  let zy : HullSevenCycleIndex → ℝ := fun i => y i / s i
  have hs : ∀ i, 0 < s i := fun i => by
    dsimp [s]
    exact add_pos (hx i) (hy i)
  have hzx : ∀ i, 0 ≤ zx i := fun i => by
    dsimp [zx]
    exact div_nonneg (hx i).le (hs i).le
  have hzy : ∀ i, 0 ≤ zy i := fun i => by
    dsimp [zy]
    exact div_nonneg (hy i).le (hs i).le
  have hpoint : ∀ i, zx i + zy i = 1 := by
    intro i
    dsimp [zx, zy, s]
    have hden : x i + y i ≠ 0 := ne_of_gt (add_pos (hx i) (hy i))
    field_simp [hden]
  have hxMean := hullSevenGeom7_le_average hzx
  have hyMean := hullSevenGeom7_le_average hzy
  have hmeanSum :
      (∑ i, zx i) / 7 + (∑ i, zy i) / 7 = 1 := by
    rw [← add_div]
    rw [← Finset.sum_add_distrib]
    simp_rw [hpoint]
    norm_num
  have hnormalized : hullSevenGeom7 zx + hullSevenGeom7 zy ≤ 1 := by
    linarith
  have hzxForm :
      hullSevenGeom7 zx = hullSevenGeom7 x / hullSevenGeom7 s := by
    dsimp [zx]
    exact hullSevenGeom7_div (fun i => (hx i).le) (fun i => (hs i).le)
  have hzyForm :
      hullSevenGeom7 zy = hullSevenGeom7 y / hullSevenGeom7 s := by
    dsimp [zy]
    exact hullSevenGeom7_div (fun i => (hy i).le) (fun i => (hs i).le)
  rw [hzxForm, hzyForm, ← add_div] at hnormalized
  have hscaled :=
    (div_le_iff₀ (hullSevenGeom7_pos hs)).1 hnormalized
  simpa [s] using hscaled

/-- Scalar data supplied by the cyclic three-step sign chamber. -/
structure HullSevenType7CyclicData (H : ℝ) where
  a : HullSevenCycleIndex → ℝ
  b : HullSevenCycleIndex → ℝ
  u : HullSevenCycleIndex → ℝ
  a_ge : ∀ i, 1 ≤ a i
  b_ge : ∀ i, 1 ≤ b i
  u_ge : ∀ i, 1 ≤ u i
  plucker_three : ∀ i,
    a i * a (i + 3) =
      u i * u (i + 1) + u (i + 4) * b (i + 1)
  plucker_two : ∀ i,
    b i * b (i + 1) =
      a i * a (i + 2) + a (i + 1) * u i
  area : (∑ i, a i) ≤ H

/-- A determinant-level semantic seam for the population-18 chamber.

The generic Grassmann-Pluecker relation and skew-symmetry are enough to
construct the two scalar recurrences.  A future point-geometry adapter only
has to instantiate `bracket i j` by the commonly normalized determinant
`[v_i,v_j]`, and discharge the three sign-floor fields from the audited key.
-/
structure HullSevenType7BracketData (H : ℝ) where
  bracket : HullSevenCycleIndex → HullSevenCycleIndex → ℝ
  skew : ∀ i j, bracket i j = -bracket j i
  plucker : ∀ i j k l,
    bracket i j * bracket k l -
      bracket i k * bracket j l +
      bracket i l * bracket j k = 0
  adjacent_ge : ∀ i, 1 ≤ bracket i (i + 1)
  twoStep_ge : ∀ i, 1 ≤ bracket i (i + 2)
  threeStep_ge : ∀ i, 1 ≤ bracket i (i + 3)
  area : (∑ i, bracket i (i + 1)) ≤ H

/-- The generic determinant seam constructs the scalar type-7 payload. -/
noncomputable def HullSevenType7BracketData.toCyclicData {H : ℝ}
    (X : HullSevenType7BracketData H) : HullSevenType7CyclicData H := by
  let a : HullSevenCycleIndex → ℝ := fun i => X.bracket i (i + 1)
  let b : HullSevenCycleIndex → ℝ := fun i => X.bracket i (i + 2)
  let u : HullSevenCycleIndex → ℝ := fun i => X.bracket i (i + 3)
  refine
    { a := a
      b := b
      u := u
      a_ge := ?_
      b_ge := ?_
      u_ge := ?_
      plucker_three := ?_
      plucker_two := ?_
      area := ?_ }
  · intro i
    exact X.adjacent_ge i
  · intro i
    exact X.twoStep_ge i
  · intro i
    exact X.threeStep_ge i
  · intro i
    have hwrap : i + 4 + 3 = i := by
      rw [add_assoc, show (4 : ZMod 7) + 3 = 0 by decide, add_zero]
    have hflip :
        X.bracket i (i + 4) =
          -X.bracket (i + 4) (i + 4 + 3) := by
      rw [hwrap]
      exact X.skew i (i + 4)
    have hp := X.plucker i (i + 1) (i + 3) (i + 4)
    dsimp [a, b, u]
    rw [hflip] at hp
    norm_num [add_assoc] at hp ⊢
    nlinarith
  · intro i
    have hp := X.plucker i (i + 1) (i + 2) (i + 3)
    dsimp [a, b, u]
    norm_num [add_assoc] at hp ⊢
    nlinarith
  · simpa [a] using X.area

private lemma hullSevenType7_quartic_threshold {A : ℝ}
    (hA : 1 < A) (hquartic : 0 ≤ A ^ 4 - 3 * A ^ 2 - A + 1) :
    25 / 14 < A := by
  by_contra hnot
  have hAupper : A ≤ 25 / 14 := le_of_not_gt hnot
  let q : ℝ := 25 / 14
  let S : ℝ :=
    q ^ 3 + q ^ 2 * A + q * A ^ 2 + A ^ 3 - 3 * (q + A) - 1
  have hqA : 0 ≤ q - A := by
    dsimp [q]
    linarith
  have hSbase : (0 : ℝ) < 6343 / 2744 := by norm_num
  have hcoef : (0 : ℝ) < 583 / 196 := by norm_num
  have hSdecomp :
      S = 6343 / 2744 +
        (A - 1) * (A ^ 2 + (q + 1) * A + 583 / 196) := by
    dsimp [S, q]
    ring
  have hS : 0 < S := by
    rw [hSdecomp]
    have hA1 : 0 ≤ A - 1 := by linarith
    have hinner : 0 < A ^ 2 + (q + 1) * A + 583 / 196 := by
      dsimp [q]
      nlinarith [sq_nonneg A]
    positivity
  have hfactor :
      (q ^ 4 - 3 * q ^ 2 - q + 1) -
          (A ^ 4 - 3 * A ^ 2 - A + 1) = (q - A) * S := by
    dsimp [S]
    ring
  have hqvalue : q ^ 4 - 3 * q ^ 2 - q + 1 =
      -(7059 / 38416 : ℝ) := by
    dsimp [q]
    norm_num
  have hnonneg : 0 ≤ (q - A) * S := mul_nonneg hqA hS.le
  rw [hqvalue] at hfactor
  nlinarith

set_option maxHeartbeats 1000000

/-- The cyclic three-step chamber has normalized area strictly above `25/2`.

The small numerical slack is intentional: `25/2` is already stronger than
the exact sharp denominator `1/v8`. -/
theorem hullSeven_type7_area_gt {H : ℝ}
    (X : HullSevenType7CyclicData H) :
    25 / 2 < H := by
  let ga := hullSevenGeom7 X.a
  let gb := hullSevenGeom7 X.b
  let gu := hullSevenGeom7 X.u
  have ha0 : ∀ i, 0 < X.a i := fun i => lt_of_lt_of_le (by norm_num) (X.a_ge i)
  have hb0 : ∀ i, 0 < X.b i := fun i => lt_of_lt_of_le (by norm_num) (X.b_ge i)
  have hu0 : ∀ i, 0 < X.u i := fun i => lt_of_lt_of_le (by norm_num) (X.u_ge i)
  have hga : 0 < ga := hullSevenGeom7_pos ha0
  have hgb : 0 < gb := hullSevenGeom7_pos hb0
  have hgu : 0 < gu := hullSevenGeom7_pos hu0

  have hmThree := hullSevenGeom7_add
    (x := fun i => X.u i * X.u (i + 1))
    (y := fun i => X.u (i + 4) * X.b (i + 1))
    (fun i => mul_pos (hu0 i) (hu0 (i + 1)))
    (fun i => mul_pos (hu0 (i + 4)) (hb0 (i + 1)))
  have hthreeEq :
      (fun i => X.u i * X.u (i + 1) + X.u (i + 4) * X.b (i + 1)) =
        (fun i => X.a i * X.a (i + 3)) := by
    funext i
    exact (X.plucker_three i).symm
  rw [hthreeEq] at hmThree
  have hu01 :
      hullSevenGeom7 (fun i => X.u i * X.u (i + 1)) = gu * gu := by
    simpa [gu] using hullSevenGeom7_mul_shift X.u X.u
      (fun i => (hu0 i).le) (fun i => (hu0 i).le) 0 1
  have hu4b1 :
      hullSevenGeom7 (fun i => X.u (i + 4) * X.b (i + 1)) = gu * gb := by
    simpa [gu, gb] using hullSevenGeom7_mul_shift X.u X.b
      (fun i => (hu0 i).le) (fun i => (hb0 i).le) 4 1
  have ha03 :
      hullSevenGeom7 (fun i => X.a i * X.a (i + 3)) = ga * ga := by
    simpa [ga] using hullSevenGeom7_mul_shift X.a X.a
      (fun i => (ha0 i).le) (fun i => (ha0 i).le) 0 3
  rw [hu01, hu4b1, ha03] at hmThree

  have hmTwo := hullSevenGeom7_add
    (x := fun i => X.a i * X.a (i + 2))
    (y := fun i => X.a (i + 1) * X.u i)
    (fun i => mul_pos (ha0 i) (ha0 (i + 2)))
    (fun i => mul_pos (ha0 (i + 1)) (hu0 i))
  have htwoEq :
      (fun i => X.a i * X.a (i + 2) + X.a (i + 1) * X.u i) =
        (fun i => X.b i * X.b (i + 1)) := by
    funext i
    exact (X.plucker_two i).symm
  rw [htwoEq] at hmTwo
  have ha02 :
      hullSevenGeom7 (fun i => X.a i * X.a (i + 2)) = ga * ga := by
    simpa [ga] using hullSevenGeom7_mul_shift X.a X.a
      (fun i => (ha0 i).le) (fun i => (ha0 i).le) 0 2
  have ha1u0 :
      hullSevenGeom7 (fun i => X.a (i + 1) * X.u i) = ga * gu := by
    simpa [ga, gu] using hullSevenGeom7_mul_shift X.a X.u
      (fun i => (ha0 i).le) (fun i => (hu0 i).le) 1 0
  have hb01 :
      hullSevenGeom7 (fun i => X.b i * X.b (i + 1)) = gb * gb := by
    simpa [gb] using hullSevenGeom7_mul_shift X.b X.b
      (fun i => (hb0 i).le) (fun i => (hb0 i).le) 0 1
  rw [ha02, ha1u0, hb01] at hmTwo

  let A := ga / gu
  let B := gb / gu
  have hA : 0 < A := div_pos hga hgu
  have hB : 0 < B := div_pos hgb hgu
  have hgaEq : ga = A * gu := by
    dsimp [A]
    field_simp [hgu.ne']
  have hgbEq : gb = B * gu := by
    dsimp [B]
    field_simp [hgu.ne']
  rw [hgaEq, hgbEq] at hmThree hmTwo
  have hguSq : 0 < gu ^ 2 := sq_pos_of_pos hgu
  have hA2 : 1 + B ≤ A ^ 2 := by
    apply le_of_mul_le_mul_left (a := gu ^ 2) ?_ hguSq
    nlinarith [hmThree]
  have hB2 : A ^ 2 + A ≤ B ^ 2 := by
    apply le_of_mul_le_mul_left (a := gu ^ 2) ?_ hguSq
    nlinarith [hmTwo]
  have hAone : 1 < A := by
    nlinarith [hA2, hB]
  have hupperB : B ≤ A ^ 2 - 1 := by linarith
  have hsquare : B ^ 2 ≤ (A ^ 2 - 1) ^ 2 := by
    have hplus : 0 ≤ A ^ 2 - 1 + B := by nlinarith [hupperB, hB.le]
    have hprod := mul_nonneg (sub_nonneg.mpr hupperB) hplus
    nlinarith
  have hquartic : 0 ≤ A ^ 4 - 3 * A ^ 2 - A + 1 := by
    nlinarith [hB2, hsquare]
  have hArational : 25 / 14 < A :=
    hullSevenType7_quartic_threshold hAone hquartic

  have hguOne : 1 ≤ gu := by
    dsimp [gu, hullSevenGeom7]
    apply Finset.one_le_prod
    intro i hi
    have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (X.u_ge i) (by norm_num : (0 : ℝ) ≤ 1 / 7)
    simpa using hp
  have hAga : A ≤ ga := by
    rw [hgaEq]
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hguOne)]
  have hgaMean := hullSevenGeom7_le_average (fun i => (ha0 i).le)
  have hsum : 7 * ga ≤ ∑ i, X.a i := by
    calc
      7 * ga ≤ 7 * ((∑ i, X.a i) / 7) :=
        mul_le_mul_of_nonneg_left hgaMean (by norm_num)
      _ = ∑ i, X.a i := by ring
  have hsumRational : 25 / 2 < ∑ i, X.a i := by
    calc
      (25 : ℝ) / 2 = 7 * (25 / 14) := by norm_num
      _ < 7 * A := mul_lt_mul_of_pos_left hArational (by norm_num)
      _ ≤ 7 * ga := mul_le_mul_of_nonneg_left hAga (by norm_num)
      _ ≤ ∑ i, X.a i := hsum
  exact lt_of_lt_of_le hsumRational X.area

/-- Direct `v8` consequence of the cyclic type-7 scalar theorem. -/
theorem hullSeven_v8_of_type7_cyclic {H : ℝ}
    (X : HullSevenType7CyclicData H) :
    1 ≤ v8 * H := by
  have hH : 25 / 2 < H := hullSeven_type7_area_gt X
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

/-- Determinant-level entry point for the full-retained population-18 key. -/
theorem hullSeven_v8_of_type7_bracket {H : ℝ}
    (X : HullSevenType7BracketData H) :
    1 ≤ v8 * H :=
  hullSeven_v8_of_type7_cyclic X.toCyclicData

end Heilbronn8.TriHull
