import Heilbronn8.QuadHull.Main
import Mathlib.RingTheory.Polynomial.Bernstein

namespace Heilbronn8.QuadHull

noncomputable section

/-!
# The low scalar remainder in orbit I

This file closes the last scalar interval in the analytic orbit-I argument.
The proof uses two small, exact tensor-product Bernstein certificates.  An
exact slack identity makes the other orientation strictly stronger, so it
needs no additional certificate.  The proof does not depend on the generated
`50t` certificate bank.
-/

private def bernsteinWeight (n : Nat) (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  (n.choose i : ℝ) * x ^ (i : Nat) * (1 - x) ^ (n - (i : Nat))

private lemma bernsteinWeight_nonneg {n : Nat} {i : Fin (n + 1)}
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinWeight n i x := by
  unfold bernsteinWeight
  positivity

private lemma sum_bernsteinWeight (n : Nat) (x : ℝ) :
    ∑ i : Fin (n + 1), bernsteinWeight n i x = 1 := by
  have h := bernsteinPolynomial.sum ℝ n
  apply_fun fun p : Polynomial ℝ ↦ Polynomial.aeval x p at h
  simpa [bernsteinWeight, bernsteinPolynomial, Finset.sum_range,
    Fin.sum_univ_eq_sum_range] using h

private lemma tensorBernstein_le
    {p q : Nat} (c : Fin (p + 1) → Fin (q + 1) → ℝ)
    {u v C : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hc : ∀ i j, c i j ≤ C) :
    (∑ i, ∑ j, c i j * bernsteinWeight p i u *
      bernsteinWeight q j v) ≤ C := by
  calc
    (∑ i, ∑ j, c i j * bernsteinWeight p i u *
        bernsteinWeight q j v) ≤
        ∑ i, ∑ j, C * bernsteinWeight p i u *
          bernsteinWeight q j v := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hc i j)
          (bernsteinWeight_nonneg hu0 hu1))
        (bernsteinWeight_nonneg hv0 hv1)
    _ = C := by
      simp_rw [← Finset.mul_sum]
      rw [sum_bernsteinWeight]
      simp only [mul_one]
      rw [← Finset.mul_sum, sum_bernsteinWeight, mul_one]

private def firstTargetN (n r : ℝ) : ℝ :=
  r * ((63 : ℝ) / 5 - n - 2 * r)

private def firstTargetL (n r : ℝ) : ℝ := n + r

private def secondTargetN (n r : ℝ) : ℝ :=
  (58 : ℝ) / 5 * r - r * n - 1

private def secondTargetL (n _r : ℝ) : ℝ := n + 1

private def targetFeasibility
    (N L n r : ℝ) : ℝ :=
  N * (n - 3) - L * (3 - 2 * r)

private def boundaryA (N L n r : ℝ) : ℝ :=
  (n + 1 - 4 * r) * L - 3 * N

private def boundaryQ1 (N L n r : ℝ) : ℝ :=
  (n - 1 - 6 * r) * L - 3 * N

private def boundaryE1 (N L n : ℝ) : ℝ :=
  (n - 3) * N - L

private def boundaryQ2 (N L n r : ℝ) : ℝ :=
  (n - 3 - 4 * r) * L - N

private def boundaryE2 (N L n r : ℝ) : ℝ :=
  (n - 3) * N + (2 * r - 3) * L

private def boundaryZ1 (N L n r : ℝ) : ℝ :=
  N * boundaryA N L n r ^ 2 +
    4 * L * boundaryQ1 N L n r * boundaryE1 N L n -
    4 * n * L ^ 2 * N

private def boundaryZ2 (N L n r : ℝ) : ℝ :=
  N * boundaryA N L n r ^ 2 +
    4 * L * boundaryQ2 N L n r * boundaryE2 N L n r -
    4 * n * L ^ 2 * N

private def firstP1CoefficientNumerator : Fin 6 → Fin 7 → ℝ := ![
  ![-187404820000, -144149793500, -103458528000, -67244853430,
    -37424025320, -15914059275, -4637101900],
  ![-129149168000, -95637838400, -64283263592, -37086913940,
    -16050698072, -3178294520, -476519810],
  ![-118007016000, -94438347800, -72557181328, -54455502261,
    -42224741912, -37957106035, -43746940080],
  ![-169025088000, -155279501600, -142688863312, -133438576788,
    -129712493396, -133694238190, -147568572330],
  ![-299872000000, -295444864000, -291575941120, -290546983432,
    -294637187512, -306124517575, -327287065060],
  ![-531174400000, -535101120000, -538924428800, -545025385120,
    -555781483680, -573567975500, -600759224650]
  ]

private def firstP1Coefficients (i : Fin 6) (j : Fin 7) : ℝ :=
  firstP1CoefficientNumerator i j / 400000000

private lemma firstP1Coefficients_le (i : Fin 6) (j : Fin 7) :
    firstP1Coefficients i j ≤ (-47651981 : ℝ) / 40000000 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [firstP1Coefficients, firstP1CoefficientNumerator]

set_option maxRecDepth 1000000 in
private lemma firstP1_bernstein_identity (a s : ℝ) :
    let n := (83 : ℝ) / 10 + a
    let r := 1 - s
    let N := firstTargetN n r
    let L := firstTargetL n r
    boundaryZ1 N L n r + 500 * targetFeasibility N L n r =
      ∑ i : Fin 6, ∑ j : Fin 7,
        firstP1Coefficients i j * bernsteinWeight 5 i (10 * a / 7) *
          bernsteinWeight 6 j (20 * s / 3) := by
  dsimp
  simp [firstP1Coefficients, firstP1CoefficientNumerator,
    bernsteinWeight, Fin.sum_univ_succ,
    firstTargetN, firstTargetL, boundaryZ1, boundaryA, boundaryQ1,
    boundaryE1, targetFeasibility]
  norm_num [Nat.choose]
  ring

private def firstP2CoefficientNumerator : Fin 6 → Fin 7 → ℝ := ![
  ![-567590100000, -518306945500, -483986810240, -465566139810,
    -463991139760, -480219458375, -515221905900],
  ![-444728368000, -415496628800, -401433401064, -403531955500,
    -422794199360, -460232367720, -516870751210],
  ![-358596840000, -350640874200, -358029094608, -381814035339,
    -423055722468, -482823373815, -562197135180],
  ![-323034880000, -337352700000, -367160431760, -413572357396,
    -477709085232, -560699258090, -663681298030],
  ![-354350080000, -391654528000, -444564705280, -514259172856,
    -601921631032, -708742636195, -835921354060],
  ![-471654400000, -532305920000, -608649292800, -701929935520,
    -813397196480, -944306080500, -1095919010650]
  ]

private def firstP2Coefficients (i : Fin 6) (j : Fin 7) : ℝ :=
  firstP2CoefficientNumerator i j / 400000000

private lemma firstP2Coefficients_le (i : Fin 6) (j : Fin 7) :
    firstP2Coefficients i j ≤ (-504742 : ℝ) / 625 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [firstP2Coefficients, firstP2CoefficientNumerator]

set_option maxRecDepth 1000000 in
private lemma firstP2_bernstein_identity (a s : ℝ) :
    let n := (83 : ℝ) / 10 + a
    let r := 1 - s
    let N := firstTargetN n r
    let L := firstTargetL n r
    boundaryZ2 N L n r =
      ∑ i : Fin 6, ∑ j : Fin 7,
        firstP2Coefficients i j * bernsteinWeight 5 i (10 * a / 7) *
          bernsteinWeight 6 j (20 * s / 3) := by
  dsimp
  simp [firstP2Coefficients, firstP2CoefficientNumerator,
    bernsteinWeight, Fin.sum_univ_succ,
    firstTargetN, firstTargetL, boundaryZ2, boundaryA, boundaryQ2,
    boundaryE2]
  norm_num [Nat.choose]
  ring

private lemma firstP1_boundary_certificate
    {a s : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ (7 : ℝ) / 10)
    (hs0 : 0 ≤ s) (hs1 : s ≤ (3 : ℝ) / 20) :
    let n := (83 : ℝ) / 10 + a
    let r := 1 - s
    let N := firstTargetN n r
    let L := firstTargetL n r
    boundaryZ1 N L n r + 500 * targetFeasibility N L n r < 0 := by
  dsimp
  have hu0 : 0 ≤ 10 * a / 7 := by positivity
  have hu1 : 10 * a / 7 ≤ 1 := by linarith
  have hv0 : 0 ≤ 20 * s / 3 := by positivity
  have hv1 : 20 * s / 3 ≤ 1 := by linarith
  have hsum := tensorBernstein_le firstP1Coefficients
    hu0 hu1 hv0 hv1 firstP1Coefficients_le
  rw [firstP1_bernstein_identity a s]
  exact lt_of_le_of_lt hsum (by norm_num)

private lemma firstP2_boundary_certificate
    {a s : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ (7 : ℝ) / 10)
    (hs0 : 0 ≤ s) (hs1 : s ≤ (3 : ℝ) / 20) :
    let n := (83 : ℝ) / 10 + a
    let r := 1 - s
    let N := firstTargetN n r
    let L := firstTargetL n r
    boundaryZ2 N L n r < 0 := by
  dsimp
  have hu0 : 0 ≤ 10 * a / 7 := by positivity
  have hu1 : 10 * a / 7 ≤ 1 := by linarith
  have hv0 : 0 ≤ 20 * s / 3 := by positivity
  have hv1 : 20 * s / 3 ≤ 1 := by linarith
  have hsum := tensorBernstein_le firstP2Coefficients
    hu0 hu1 hv0 hv1 firstP2Coefficients_le
  rw [firstP2_bernstein_identity a s]
  exact lt_of_le_of_lt hsum (by norm_num)

/-- The denominator-cleared first scalar leaf. -/
def orbitILowP1 (n r y : ℝ) : ℝ :=
  let A := n + 1 - 4 * r - 3 * y
  let Q := n - 1 - 6 * r - 3 * y
  y * A ^ 2 + 4 * Q * (y * (n - 3) - 1) - 4 * n * y

/-- The denominator-cleared second scalar leaf. -/
def orbitILowP2 (n r y : ℝ) : ℝ :=
  let A := n + 1 - 4 * r - 3 * y
  let Q := n - 3 - 4 * r - y
  y * A ^ 2 + 4 * Q * (y * (n - 3) - (3 - 2 * r)) - 4 * n * y

private lemma orbitILowP1_neg_of_Q_le_one
    {n r y : ℝ}
    (hn0 : (83 : ℝ) / 10 < n) (_hn1 : n < 9)
    (hr1 : r ≤ 1) (hy0 : 0 < y) (hy1 : y < (1 : ℝ) / 4)
    (hCD : 3 - 2 * r ≤ y * (n - 3))
    (hQ : n - 1 - 6 * r - 3 * y ≤ 1) :
    orbitILowP1 n r y < 0 := by
  let A := n + 1 - 4 * r - 3 * y
  let Q := n - 1 - 6 * r - 3 * y
  let E := y * (n - 3) - 1
  have hE0 : 0 ≤ E := by
    dsimp [E]
    linarith
  have hyn : y * (n - 5) < y * 4 :=
    mul_lt_mul_of_pos_left (by linarith) hy0
  have hy4 : y * 4 < 1 := by linarith
  have hE2 : E < 2 * y := by
    dsimp [E]
    nlinarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    linarith
  have hA5 : A ≤ 5 := by
    dsimp [A, Q] at hQ ⊢
    linarith
  have hA2 : A ^ 2 ≤ 25 := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hA5)]
  have hQE : Q * E ≤ E := by
    have hm := mul_le_mul_of_nonneg_right hQ hE0
    simpa [Q] using hm
  have hlast : y * (33 - 4 * n) < 0 :=
    mul_neg_of_pos_of_neg hy0 (by linarith)
  dsimp [orbitILowP1, A, Q, E]
  nlinarith

private lemma orbitILowP2_neg_of_Q_le_one
    {n r y : ℝ}
    (hn0 : (83 : ℝ) / 10 < n) (_hn1 : n < 9)
    (hr1 : r ≤ 1) (hy0 : 0 < y) (hy1 : y < (1 : ℝ) / 4)
    (_hCD : 3 - 2 * r ≤ y * (n - 3))
    (hQ : n - 3 - 4 * r - y ≤ 1) :
    orbitILowP2 n r y < 0 := by
  let A := n + 1 - 4 * r - 3 * y
  let Q := n - 3 - 4 * r - y
  let E := y * (n - 3) - (3 - 2 * r)
  have hE0 : 0 ≤ E := by
    dsimp [E]
    linarith
  have hyn : y * (n - 5) < y * 4 :=
    mul_lt_mul_of_pos_left (by linarith) hy0
  have hy4 : y * 4 < 1 := by linarith
  have hrLower : 1 ≤ 3 - 2 * r := by linarith
  have hE2 : E < 2 * y := by
    dsimp [E]
    nlinarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    linarith
  have hA5 : A ≤ 5 := by
    dsimp [A, Q] at hQ ⊢
    linarith
  have hA2 : A ^ 2 ≤ 25 := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hA5)]
  have hQE : Q * E ≤ E := by
    have hm := mul_le_mul_of_nonneg_right hQ hE0
    simpa [Q] using hm
  have hlast : y * (33 - 4 * n) < 0 :=
    mul_neg_of_pos_of_neg hy0 (by linarith)
  dsimp [orbitILowP2, A, Q, E]
  nlinarith

private lemma orbitILowP1_div_lt_of_lt
    {n r y Y : ℝ}
    (hn1 : n < 9) (hr0 : (17 : ℝ) / 20 < r)
    (hy0 : 0 < y) (hyY : y < Y) (hY1 : Y < (1 : ℝ) / 4)
    (hQY : 1 ≤ n - 1 - 6 * r - 3 * Y) :
    orbitILowP1 n r y / y < orbitILowP1 n r Y / Y := by
  have hY0 : 0 < Y := hy0.trans hyY
  have hy1 : y < (1 : ℝ) / 4 := hyY.trans hY1
  have hp0 : 0 < Y * y := mul_pos hY0 hy0
  have hp1 : 16 * (Y * y) < 1 := by
    have h1 : Y * y < Y * ((1 : ℝ) / 4) :=
      mul_lt_mul_of_pos_left hy1 hY0
    have h2 : Y * ((1 : ℝ) / 4) < (1 : ℝ) / 16 := by
      nlinarith
    nlinarith
  have hinvprod : 16 < 1 / (Y * y) :=
    (lt_div_iff₀ hp0).2 hp1
  have hinvprod0 : 0 ≤ 1 / (Y * y) := by positivity
  have hqprod : 16 <
      (n - 1 - 6 * r - 3 * Y) / (Y * y) := by
    calc
      16 < 1 / (Y * y) := hinvprod
      _ ≤ (n - 1 - 6 * r - 3 * Y) * (1 / (Y * y)) :=
        by simpa using mul_le_mul_of_nonneg_right hQY hinvprod0
      _ = (n - 1 - 6 * r - 3 * Y) / (Y * y) := by ring
  have hinvy : 4 < 1 / y := by
    apply (lt_div_iff₀ hy0).2
    nlinarith
  have h3invy : 12 < 3 / y := by
    calc
      (12 : ℝ) = 3 * 4 := by norm_num
      _ < 3 * (1 / y) := mul_lt_mul_of_pos_left hinvy (by norm_num)
      _ = 3 / y := by ring
  have hA : n + 1 - 4 * r < (33 : ℝ) / 5 := by linarith
  let K :=
    (n - 1 - 6 * r - 3 * Y) / (Y * y) + 3 / y -
      3 * (n + 1 - 4 * r) / 2 + 9 * (Y + y) / 4 -
      3 * (n - 3)
  have hK : 0 < K := by
    dsimp [K]
    have hpos : 0 < 9 * (Y + y) / 4 := by positivity
    nlinarith
  have hid :
      orbitILowP1 n r Y / Y - orbitILowP1 n r y / y =
        4 * (Y - y) * K := by
    dsimp [orbitILowP1, K]
    field_simp [hy0.ne', hY0.ne']
    <;> ring
  have hdiff : 0 <
      orbitILowP1 n r Y / Y - orbitILowP1 n r y / y := by
    rw [hid]
    positivity
  linarith

private lemma orbitILowP2_div_lt_of_lt
    {n r y Y : ℝ}
    (hn1 : n < 9) (hr0 : (17 : ℝ) / 20 < r) (hr1 : r ≤ 1)
    (hy0 : 0 < y) (hyY : y < Y) (hY1 : Y < (1 : ℝ) / 4)
    (hQY : 1 ≤ n - 3 - 4 * r - Y) :
    orbitILowP2 n r y / y < orbitILowP2 n r Y / Y := by
  have hY0 : 0 < Y := hy0.trans hyY
  have hy1 : y < (1 : ℝ) / 4 := hyY.trans hY1
  have hp0 : 0 < Y * y := mul_pos hY0 hy0
  have hp1 : 16 * (Y * y) < 1 := by
    have h1 : Y * y < Y * ((1 : ℝ) / 4) :=
      mul_lt_mul_of_pos_left hy1 hY0
    have h2 : Y * ((1 : ℝ) / 4) < (1 : ℝ) / 16 := by
      nlinarith
    nlinarith
  have hinvprod : 16 < 1 / (Y * y) :=
    (lt_div_iff₀ hp0).2 hp1
  have hinvprod0 : 0 ≤ 1 / (Y * y) := by positivity
  have hfactor : 1 ≤ 3 - 2 * r := by linarith
  have hfactor0 : 0 ≤ 3 - 2 * r := hfactor.trans' (by norm_num)
  have hqprod : 16 <
      (3 - 2 * r) * (n - 3 - 4 * r - Y) / (Y * y) := by
    have hq : 1 ≤
        (3 - 2 * r) * (n - 3 - 4 * r - Y) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hfactor)
        (sub_nonneg.mpr hQY)]
    calc
      16 < 1 / (Y * y) := hinvprod
      _ ≤ ((3 - 2 * r) * (n - 3 - 4 * r - Y)) *
          (1 / (Y * y)) :=
        by simpa using mul_le_mul_of_nonneg_right hq hinvprod0
      _ = (3 - 2 * r) * (n - 3 - 4 * r - Y) / (Y * y) := by
        ring
  have hinvy : 4 < 1 / y := by
    apply (lt_div_iff₀ hy0).2
    nlinarith
  have hinvy0 : 0 ≤ 1 / y := le_trans (by norm_num) hinvy.le
  have hfinvy : 4 < (3 - 2 * r) / y := by
    calc
      4 < 1 / y := hinvy
      _ ≤ (3 - 2 * r) * (1 / y) :=
        by simpa using mul_le_mul_of_nonneg_right hfactor hinvy0
      _ = (3 - 2 * r) / y := by ring
  have hA : n + 1 - 4 * r < (33 : ℝ) / 5 := by linarith
  let K :=
    (3 - 2 * r) * (n - 3 - 4 * r - Y) / (Y * y) +
      (3 - 2 * r) / y - 3 * (n + 1 - 4 * r) / 2 +
      9 * (Y + y) / 4 - (n - 3)
  have hK : 0 < K := by
    dsimp [K]
    have hpos : 0 < 9 * (Y + y) / 4 := by positivity
    nlinarith
  have hid :
      orbitILowP2 n r Y / Y - orbitILowP2 n r y / y =
        4 * (Y - y) * K := by
    dsimp [orbitILowP2, K]
    field_simp [hy0.ne', hY0.ne']
    <;> ring
  have hdiff : 0 <
      orbitILowP2 n r Y / Y - orbitILowP2 n r y / y := by
    rw [hid]
    positivity
  linarith

/-- Both low scalar leaves under the `U ≤ V` target inequality. -/
theorem orbitILow_first_orientation
    {n r y : ℝ}
    (hn0 : (83 : ℝ) / 10 < n) (hn1 : n < 9)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hy0 : 0 < y)
    (hCD : 3 - 2 * r ≤ y * (n - 3))
    (hTarget : y * firstTargetL n r < firstTargetN n r) :
    orbitILowP1 n r y < 0 ∧ orbitILowP2 n r y < 0 := by
  let N := firstTargetN n r
  let L := firstTargetL n r
  let Y := N / L
  let a := n - (83 : ℝ) / 10
  let s := 1 - r
  have hn3 : 0 < n - 3 := by linarith
  have hL : 0 < L := by dsimp [L, firstTargetL]; linarith
  have hN : 0 < N := by
    dsimp [N]
    nlinarith [mul_pos hy0 hL]
  have hY0 : 0 < Y := div_pos hN hL
  have hyY : y < Y := by
    dsimp [Y]
    exact (lt_div_iff₀ hL).2 hTarget
  have hF : 0 < targetFeasibility N L n r := by
    have ht := mul_lt_mul_of_pos_right hTarget hn3
    have hc := mul_le_mul_of_nonneg_left hCD hL.le
    dsimp [N, L, targetFeasibility] at ht hc ⊢
    nlinarith
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ (7 : ℝ) / 10 := by dsimp [a]; linarith
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hsOne : s ≤ 1 := by dsimp [s]; linarith
  have hs1 : s < (3 : ℝ) / 20 := by
    by_contra hnot
    have hslow : (3 : ℝ) / 20 ≤ s := le_of_not_gt hnot
    have hsquare : (9 : ℝ) / 400 ≤ s ^ 2 := by
      have hp : 0 ≤ (s - (3 : ℝ) / 20) *
          (s + (3 : ℝ) / 20) :=
        mul_nonneg (sub_nonneg.mpr hslow) (by linarith)
      nlinarith
    have haTerm : 0 ≤ a * (4 - 3 * s + 2 * s ^ 2) := by
      apply mul_nonneg ha0
      nlinarith [sq_nonneg s]
    have ha2Term : 0 ≤ a ^ 2 * (1 - s) :=
      mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hsOne)
    have hExpand :
        targetFeasibility N L n r =
          (289 : ℝ) / 100 - (1919 : ℝ) / 100 * s -
            (43 : ℝ) / 5 * s ^ 2 -
            a * (4 - 3 * s + 2 * s ^ 2) - a ^ 2 * (1 - s) := by
      dsimp [N, L, a, s, firstTargetN, firstTargetL,
        targetFeasibility]
      ring
    rw [hExpand] at hF
    nlinarith
  have hrStrong : (17 : ℝ) / 20 < r := by
    dsimp [s] at hs1
    linarith
  have hY1 : Y < (1 : ℝ) / 4 := by
    have hgap : 0 < L - 4 * N := by
      have hcoef : 0 ≤ 5 - 4 * s := by linarith
      have hp : 0 ≤ a * (5 - 4 * s) := mul_nonneg ha0 hcoef
      have hid :
          L - 4 * N = (1 : ℝ) / 10 + a * (5 - 4 * s) +
            (1 : ℝ) / 5 * s + 8 * s ^ 2 := by
        dsimp [N, L, a, s, firstTargetN, firstTargetL]
        ring
      rw [hid]
      positivity
    dsimp [Y]
    apply (div_lt_iff₀ hL).2
    nlinarith
  have hy1 : y < (1 : ℝ) / 4 := hyY.trans hY1
  have hN1 : N = firstTargetN n r := rfl
  have hL1 : L = firstTargetL n r := rfl
  have hZ1 : boundaryZ1 N L n r < 0 := by
    have hcert := firstP1_boundary_certificate
      ha0 ha1 hs0 hs1.le
    have hnEq : (83 : ℝ) / 10 + a = n := by dsimp [a]; ring
    have hrEq : 1 - s = r := by dsimp [s]; ring
    rw [hnEq, hrEq] at hcert
    change boundaryZ1 N L n r +
      500 * targetFeasibility N L n r < 0 at hcert
    nlinarith
  have hZ2 : boundaryZ2 N L n r < 0 := by
    have hcert := firstP2_boundary_certificate
      ha0 ha1 hs0 hs1.le
    have hnEq : (83 : ℝ) / 10 + a = n := by dsimp [a]; ring
    have hrEq : 1 - s = r := by dsimp [s]; ring
    rw [hnEq, hrEq] at hcert
    exact hcert
  have hPY1 : orbitILowP1 n r Y < 0 := by
    have hid : orbitILowP1 n r Y = boundaryZ1 N L n r / L ^ 3 := by
      dsimp [Y, orbitILowP1, boundaryZ1, boundaryA, boundaryQ1,
        boundaryE1]
      field_simp [hL.ne']
      <;> ring
    rw [hid]
    exact div_neg_of_neg_of_pos hZ1 (pow_pos hL 3)
  have hPY2 : orbitILowP2 n r Y < 0 := by
    have hid : orbitILowP2 n r Y = boundaryZ2 N L n r / L ^ 3 := by
      dsimp [Y, orbitILowP2, boundaryZ2, boundaryA, boundaryQ2,
        boundaryE2]
      field_simp [hL.ne']
      <;> ring
    rw [hid]
    exact div_neg_of_neg_of_pos hZ2 (pow_pos hL 3)
  constructor
  · by_cases hQ : n - 1 - 6 * r - 3 * y ≤ 1
    · exact orbitILowP1_neg_of_Q_le_one hn0 hn1 hr1 hy0 hy1 hCD hQ
    · have hQy : 1 < n - 1 - 6 * r - 3 * y := lt_of_not_ge hQ
      by_cases hQY : 1 ≤ n - 1 - 6 * r - 3 * Y
      · have hm := orbitILowP1_div_lt_of_lt hn1 hrStrong hy0 hyY hY1 hQY
        have hneg : orbitILowP1 n r y / y < 0 :=
          hm.trans (div_neg_of_neg_of_pos hPY1 hY0)
        exact neg_of_div_neg_left hneg hy0.le
      · let z := (n - 2 - 6 * r) / 3
        have hyz : y < z := by dsimp [z]; linarith
        have hzY : z < Y := by
          have := lt_of_not_ge hQY
          dsimp [z]
          linarith
        have hz0 : 0 < z := hy0.trans hyz
        have hz1 : z < (1 : ℝ) / 4 := hzY.trans hY1
        have hCDz : 3 - 2 * r ≤ z * (n - 3) := by
          have hm := mul_lt_mul_of_pos_right hyz hn3
          nlinarith
        have hQz : n - 1 - 6 * r - 3 * z ≤ 1 := by
          dsimp [z]
          ring_nf
          norm_num
        have hPz := orbitILowP1_neg_of_Q_le_one
          hn0 hn1 hr1 hz0 hz1 hCDz hQz
        have hm := orbitILowP1_div_lt_of_lt hn1 hrStrong hy0 hyz hz1
          (by dsimp [z]; ring_nf; norm_num)
        have hneg : orbitILowP1 n r y / y < 0 :=
          hm.trans (div_neg_of_neg_of_pos hPz hz0)
        exact neg_of_div_neg_left hneg hy0.le
  · by_cases hQ : n - 3 - 4 * r - y ≤ 1
    · exact orbitILowP2_neg_of_Q_le_one hn0 hn1 hr1 hy0 hy1 hCD hQ
    · have hQy : 1 < n - 3 - 4 * r - y := lt_of_not_ge hQ
      by_cases hQY : 1 ≤ n - 3 - 4 * r - Y
      · have hm := orbitILowP2_div_lt_of_lt
          hn1 hrStrong hr1 hy0 hyY hY1 hQY
        have hneg : orbitILowP2 n r y / y < 0 :=
          hm.trans (div_neg_of_neg_of_pos hPY2 hY0)
        exact neg_of_div_neg_left hneg hy0.le
      · let z := n - 4 - 4 * r
        have hyz : y < z := by dsimp [z]; linarith
        have hzY : z < Y := by
          have := lt_of_not_ge hQY
          dsimp [z]
          linarith
        have hz0 : 0 < z := hy0.trans hyz
        have hz1 : z < (1 : ℝ) / 4 := hzY.trans hY1
        have hCDz : 3 - 2 * r ≤ z * (n - 3) := by
          have hm := mul_lt_mul_of_pos_right hyz hn3
          nlinarith
        have hQz : n - 3 - 4 * r - z ≤ 1 := by
          dsimp [z]
          linarith
        have hPz := orbitILowP2_neg_of_Q_le_one
          hn0 hn1 hr1 hz0 hz1 hCDz hQz
        have hm := orbitILowP2_div_lt_of_lt hn1 hrStrong hr1 hy0 hyz hz1
          (by dsimp [z]; linarith)
        have hneg : orbitILowP2 n r y / y < 0 :=
          hm.trans (div_neg_of_neg_of_pos hPz hz0)
        exact neg_of_div_neg_left hneg hy0.le

/--
The other orientation has a stronger target inequality.  Its slack is the
first-orientation slack plus the nonnegative correction
`(1-r) * (2*r+1+y)`, so no second certificate bank is needed.
-/
theorem orbitILow_second_orientation
    {n r y : ℝ}
    (hn0 : (83 : ℝ) / 10 < n) (hn1 : n < 9)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hy0 : 0 < y)
    (hCD : 3 - 2 * r ≤ y * (n - 3))
    (hTarget : y * secondTargetL n r < secondTargetN n r) :
    orbitILowP1 n r y < 0 ∧ orbitILowP2 n r y < 0 := by
  have hcorrection : 0 ≤ (1 - r) * (2 * r + 1 + y) :=
    mul_nonneg (sub_nonneg.mpr hr1) (by positivity)
  have hslack :
      firstTargetN n r - y * firstTargetL n r =
        (secondTargetN n r - y * secondTargetL n r) +
          (1 - r) * (2 * r + 1 + y) := by
    unfold firstTargetN firstTargetL secondTargetN secondTargetL
    ring
  have hFirst : y * firstTargetL n r < firstTargetN n r := by
    have hSecondSlack : 0 <
        secondTargetN n r - y * secondTargetL n r :=
      sub_pos.mpr hTarget
    apply sub_pos.mp
    rw [hslack]
    exact add_pos_of_pos_of_nonneg hSecondSlack hcorrection
  exact orbitILow_first_orientation hn0 hn1 hr0 hr1 hy0 hCD hFirst

/-- The first scalar numerator before dividing by the smaller fan scale. -/
def orbitILowP1Numerator (n D M : ℝ) : ℝ :=
  M * (D * (n + 1) - 4 * n - 3 * M) ^ 2 +
    4 * D * (D * (n - 1) - 6 * n - 3 * M) *
      (M * (n - 3) - D) -
    4 * n * D ^ 2 * M

/-- The second scalar numerator before dividing by the smaller fan scale. -/
def orbitILowP2Numerator (n D M : ℝ) : ℝ :=
  M * (D * (n + 1) - 4 * n - 3 * M) ^ 2 +
    4 * D * (D * (n - 3) - 4 * n - M) *
      (M * (n - 3) + 2 * n - 3 * D) -
    4 * n * D ^ 2 * M

/-- The two original numerators under the `U ≤ V` target failure. -/
theorem orbitILow_numerators_first_orientation
    {n D M : ℝ}
    (hn0 : (83 : ℝ) / 10 < n) (hn1 : n < 9)
    (hD : 0 < D) (hnD : n ≤ D) (hM : 0 < M)
    (hCD : 3 * D - 2 * n ≤ M * (n - 3))
    (hTarget : M * (D + 1) < D * ((63 : ℝ) / 5 - n) - 2 * n) :
    orbitILowP1Numerator n D M < 0 ∧
      orbitILowP2Numerator n D M < 0 := by
  let r := n / D
  let y := M / D
  have hnpos : 0 < n := by linarith
  have hr0 : 0 < r := div_pos hnpos hD
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one hD).2 hnD
  have hy0 : 0 < y := div_pos hM hD
  have hCD' : 3 - 2 * r ≤ y * (n - 3) := by
    by_contra hnot
    have hpos : 0 < 3 - 2 * r - y * (n - 3) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hmul := mul_pos hD hpos
    have hid :
        D * (3 - 2 * r - y * (n - 3)) =
          3 * D - 2 * n - M * (n - 3) := by
      dsimp [r, y]
      field_simp [hD.ne']
      <;> ring
    rw [hid] at hmul
    nlinarith
  have hTarget' : y * firstTargetL n r < firstTargetN n r := by
    apply sub_pos.mp
    by_contra hnot
    have hle : firstTargetN n r - y * firstTargetL n r ≤ 0 :=
      le_of_not_gt hnot
    have hscale : 0 ≤ D ^ 2 / n := (div_pos (sq_pos_of_pos hD) hnpos).le
    have hmul := mul_nonpos_of_nonneg_of_nonpos hscale hle
    have hid :
        (D ^ 2 / n) *
            (firstTargetN n r - y * firstTargetL n r) =
          D * ((63 : ℝ) / 5 - n) - 2 * n - M * (D + 1) := by
      dsimp [r, y, firstTargetN, firstTargetL]
      field_simp [hD.ne', hnpos.ne']
      <;> ring
    rw [hid] at hmul
    nlinarith
  have hsmall := orbitILow_first_orientation
    hn0 hn1 hr0 hr1 hy0 hCD' hTarget'
  have hscale : 0 < D ^ 3 := pow_pos hD 3
  constructor
  · have hid : orbitILowP1Numerator n D M =
        D ^ 3 * orbitILowP1 n r y := by
      dsimp [r, y, orbitILowP1Numerator, orbitILowP1]
      field_simp [hD.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_pos_of_neg hscale hsmall.1
  · have hid : orbitILowP2Numerator n D M =
        D ^ 3 * orbitILowP2 n r y := by
      dsimp [r, y, orbitILowP2Numerator, orbitILowP2]
      field_simp [hD.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_pos_of_neg hscale hsmall.2

/-- The two original numerators under the `V ≤ U` target failure. -/
theorem orbitILow_numerators_second_orientation
    {n D M : ℝ}
    (hn0 : (83 : ℝ) / 10 < n) (hn1 : n < 9)
    (hD : 0 < D) (hnD : n ≤ D) (hM : 0 < M)
    (hCD : 3 * D - 2 * n ≤ M * (n - 3))
    (hTarget : M * (n + 1) < (58 : ℝ) / 5 * n - n ^ 2 - D) :
    orbitILowP1Numerator n D M < 0 ∧
      orbitILowP2Numerator n D M < 0 := by
  let r := n / D
  let y := M / D
  have hnpos : 0 < n := by linarith
  have hr0 : 0 < r := div_pos hnpos hD
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one hD).2 hnD
  have hy0 : 0 < y := div_pos hM hD
  have hCD' : 3 - 2 * r ≤ y * (n - 3) := by
    by_contra hnot
    have hpos : 0 < 3 - 2 * r - y * (n - 3) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hmul := mul_pos hD hpos
    have hid :
        D * (3 - 2 * r - y * (n - 3)) =
          3 * D - 2 * n - M * (n - 3) := by
      dsimp [r, y]
      field_simp [hD.ne']
      <;> ring
    rw [hid] at hmul
    nlinarith
  have hTarget' : y * secondTargetL n r < secondTargetN n r := by
    apply sub_pos.mp
    by_contra hnot
    have hle : secondTargetN n r - y * secondTargetL n r ≤ 0 :=
      le_of_not_gt hnot
    have hmul := mul_nonpos_of_nonneg_of_nonpos hD.le hle
    have hid :
        D * (secondTargetN n r - y * secondTargetL n r) =
          (58 : ℝ) / 5 * n - n ^ 2 - D - M * (n + 1) := by
      dsimp [r, y, secondTargetN, secondTargetL]
      field_simp [hD.ne']
      <;> ring
    rw [hid] at hmul
    nlinarith
  have hsmall := orbitILow_second_orientation
    hn0 hn1 hr0 hr1 hy0 hCD' hTarget'
  have hscale : 0 < D ^ 3 := pow_pos hD 3
  constructor
  · have hid : orbitILowP1Numerator n D M =
        D ^ 3 * orbitILowP1 n r y := by
      dsimp [r, y, orbitILowP1Numerator, orbitILowP1]
      field_simp [hD.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_pos_of_neg hscale hsmall.1
  · have hid : orbitILowP2Numerator n D M =
        D ^ 3 * orbitILowP2 n r y := by
      dsimp [r, y, orbitILowP2Numerator, orbitILowP2]
      field_simp [hD.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_pos_of_neg hscale hsmall.2

end

end Heilbronn8.QuadHull
