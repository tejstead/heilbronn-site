import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar AM-GM packets for the `p = 111`, `q = 223/233` cells

This file contains only scalar inequalities. Geometry adapters supply the
determinant variables and the displayed lower bounds.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Heilbronn8

open scoped BigOperators

/-! ## The `q = 223` height relation -/

theorem hullSixThreeThreeP111Q223_height
    {a b c e A B g : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hA : b - a + 1 ≤ A) (hB : 1 ≤ B)
    (hX21 : 1 ≤ c * e * g)
    (hY01 :
      e * A / b + a * e * B / (b * c) + a * e * g ≤ a + e - 1) :
    c ≤ a * (c - 1) := by
  let Z : ℝ := a - 1 - a / c
  let K : ℝ := A / b + a * B / (b * c) - 1
  have hscale : a / c ≤ a * e * g := by
    have hmul := mul_le_mul_of_nonneg_left hX21 (le_of_lt (div_pos ha hc))
    have hid : a / c * (c * e * g) = a * e * g := by
      field_simp [hc.ne']
    simpa [hid] using hmul
  have hEK : e * K ≤ Z := by
    have hreplace :
        e * A / b + a * e * B / (b * c) + a / c ≤ a + e - 1 := by
      calc
        e * A / b + a * e * B / (b * c) + a / c ≤
            e * A / b + a * e * B / (b * c) + a * e * g := by
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_left hscale
              (e * A / b + a * e * B / (b * c))
        _ ≤ a + e - 1 := hY01
    have hbase :
        e * A / b + a * e * B / (b * c) ≤
          a + e - 1 - a / c := by
      exact (le_sub_iff_add_le).2 hreplace
    calc
      e * K = e * A / b + a * e * B / (b * c) - e := by
        dsimp [K]
        ring
      _ ≤ (a + e - 1 - a / c) - e := sub_le_sub_right hbase e
      _ = Z := by
        dsimp [Z]
        ring
  have hAB : a / c ≤ a * B / c := by
    have hmul : a ≤ a * B := by
      nlinarith [mul_le_mul_of_nonneg_left hB (le_of_lt ha)]
    exact div_le_div_of_nonneg_right
      hmul (le_of_lt hc)
  have hK : -Z / b ≤ K := by
    apply (div_le_iff₀ hb).2
    have hid : b * K = A + a * B / c - b := by
      dsimp [K]
      field_simp [hb.ne', hc.ne']
      <;> ring
    rw [mul_comm K b, hid]
    dsimp [Z]
    nlinarith
  have hZ : 0 ≤ Z := by
    have hchain : -e * Z / b ≤ Z := by
      have hmul : e * (-Z / b) ≤ e * K :=
        mul_le_mul_of_nonneg_left hK (le_of_lt he)
      calc
        -e * Z / b = e * (-Z / b) := by ring
        _ ≤ e * K := hmul
        _ ≤ Z := hEK
    have hfac : 0 < 1 + e / b := by positivity
    have hid : Z * (1 + e / b) = Z + e * Z / b := by ring
    have : 0 ≤ Z * (1 + e / b) := by
      rw [hid]
      have hnonneg : 0 ≤ Z - (-e * Z / b) :=
        sub_nonneg.mpr hchain
      have hsum : Z - (-e * Z / b) = Z + e * Z / b := by ring
      rw [← hsum]
      exact hnonneg
    exact nonneg_of_mul_nonneg_left this hfac
  have hmul := mul_nonneg hZ (le_of_lt hc)
  have hid : Z * c = a * c - c - a := by
    dsimp [Z]
    field_simp [hc.ne']
    <;> ring
  rw [hid] at hmul
  nlinarith

/-! ## The `q = 223` weighted certificate -/

noncomputable def hullSixThreeThreeP111Q223Term
    (y z : ℝ) : Fin 6 → ℝ :=
  ![z ^ 2, y ^ 2, 1 / y ^ 2, 16 * y / 5, 3 * z / 5,
    3 * y / (4 * z)]

def hullSixThreeThreeP111Q223Weight : Fin 6 → ℕ :=
  ![1, 2, 7, 7, 1, 3]

noncomputable def hullSixThreeThreeP111Q223Constant : ℝ :=
  (1 / 2 : ℝ) ^ 2 * (1 / 7 : ℝ) ^ 7 *
    (16 / 35 : ℝ) ^ 7 * (3 / 5 : ℝ) * (1 / 4 : ℝ) ^ 3

theorem hullSixThreeThreeP111Q223_weight_pos
    (i : Fin 6) : 0 < hullSixThreeThreeP111Q223Weight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP111Q223Weight]

theorem hullSixThreeThreeP111Q223_weight_sum :
    ∑ i, hullSixThreeThreeP111Q223Weight i = 21 := by
  norm_num [hullSixThreeThreeP111Q223Weight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP111Q223_term_nonneg
    {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (i : Fin 6) :
    0 ≤ hullSixThreeThreeP111Q223Term y z i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP111Q223Term] <;>
    positivity

theorem hullSixThreeThreeP111Q223_term_sum
    (y z : ℝ) :
    ∑ i, hullSixThreeThreeP111Q223Term y z i =
      z ^ 2 + y ^ 2 + 1 / y ^ 2 + 16 * y / 5 + 3 * z / 5 +
        3 * y / (4 * z) := by
  simp [hullSixThreeThreeP111Q223Term, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP111Q223_term_product
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (∏ i,
        (hullSixThreeThreeP111Q223Term y z i /
          (hullSixThreeThreeP111Q223Weight i : ℝ)) ^
            hullSixThreeThreeP111Q223Weight i) =
      hullSixThreeThreeP111Q223Constant := by
  simp [hullSixThreeThreeP111Q223Term,
    hullSixThreeThreeP111Q223Weight, Fin.prod_univ_succ,
    hullSixThreeThreeP111Q223Constant]
  field_simp [hy.ne', hz.ne']
  <;> ring

theorem hullSixThreeThreeP111Q223_constant_pos :
    0 < hullSixThreeThreeP111Q223Constant := by
  unfold hullSixThreeThreeP111Q223Constant
  positivity

theorem hullSixThreeThreeP111Q223_root_gap :
    (63 : ℝ) / 10 <
      21 * hullSixThreeThreeP111Q223Constant ^ ((21 : ℝ)⁻¹) := by
  have hpow :
      ((3 : ℝ) / 10) ^ 21 < hullSixThreeThreeP111Q223Constant := by
    norm_num [hullSixThreeThreeP111Q223Constant]
  have hpowRpow :
      ((3 : ℝ) / 10) ^ (21 : ℝ) <
        hullSixThreeThreeP111Q223Constant := by
    change ((3 : ℝ) / 10) ^ ((21 : ℕ) : ℝ) <
      hullSixThreeThreeP111Q223Constant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (3 : ℝ) / 10 <
        hullSixThreeThreeP111Q223Constant ^ ((21 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP111Q223_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP111Q223_amgm
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (63 : ℝ) / 10 <
      z ^ 2 + y ^ 2 + 1 / y ^ 2 + 16 * y / 5 + 3 * z / 5 +
        3 * y / (4 * z) := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP111Q223Weight
    (hullSixThreeThreeP111Q223Term y z)
    hullSixThreeThreeP111Q223_weight_pos
    (hullSixThreeThreeP111Q223_term_nonneg
      (le_of_lt hy) (le_of_lt hz))
  rw [hullSixThreeThreeP111Q223_weight_sum,
    hullSixThreeThreeP111Q223_term_product hy hz] at hamgm
  rw [← hullSixThreeThreeP111Q223_term_sum y z]
  exact hullSixThreeThreeP111Q223_root_gap.trans_le hamgm

theorem hullSixThreeThreeP111Q223_finish
    {H y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hlower :
      (31 : ℝ) / 5 +
          (z ^ 2 + y ^ 2 + 1 / y ^ 2 + 16 * y / 5 + 3 * z / 5 +
            3 * y / (4 * z)) ≤ H) :
    (25 : ℝ) / 2 < H := by
  have h := hullSixThreeThreeP111Q223_amgm hy hz
  linarith

noncomputable def hullSixThreeThreeP111Q223Phi
    (a b c f : ℝ) : ℝ :=
  4 + c + f + a / b + b / f + c / f + f / b + 1 / b +
    2 * f / a + f / (a * b)

private theorem hullSixThreeThreeP111_two_mul_le_add
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t)
    (hprod : t ^ 2 ≤ u * v) :
    2 * t ≤ u + v := by
  by_cases hu0 : u = 0
  · subst u
    have ht0 : t = 0 := by nlinarith [sq_nonneg t]
    subst t
    linarith
  · have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hmul : u * (2 * t) ≤ u * (u + v) := by
      nlinarith [sq_nonneg (u - t)]
    exact le_of_mul_le_mul_left hmul huPos

theorem hullSixThreeThreeP111Q223_phi_of_roots
    {a b c f x r y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (hx : 0 < x) (hr : 0 < r) (hy : 0 < y) (hz : 0 < z)
    (hxDef : x = c - 1) (hrDef : r = f / b)
    (hySq : y ^ 2 = r) (hzSq : z ^ 2 = x)
    (hheight : c ≤ a * (c - 1)) :
    (25 : ℝ) / 2 < hullSixThreeThreeP111Q223Phi a b c f := by
  have hheightTerm : c / (2 * b * x) ≤ a / (2 * b) := by
    have hcx : c ≤ a * x := by rwa [hxDef]
    have hac : c / x ≤ a := (div_le_iff₀ hx).2 hcx
    calc
      c / (2 * b * x) = (c / x) / (2 * b) := by
        field_simp [hb.ne', hx.ne']
        <;> ring
      _ ≤ a / (2 * b) :=
        (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * b)).2 hac
  have hprod0 :
      y ^ 2 ≤ (a / (2 * b)) * (f * (2 + 1 / b) / a) := by
    have hid :
        (a / (2 * b)) * (f * (2 + 1 / b) / a) =
          f / b + f / (2 * b ^ 2) := by
      field_simp [ha.ne', hb.ne']
      <;> ring
    rw [hid, hySq, hrDef]
    exact le_add_of_nonneg_right (by positivity)
  have hpair0 :
      2 * y ≤ a / (2 * b) + f * (2 + 1 / b) / a :=
    hullSixThreeThreeP111_two_mul_le_add
      (by positivity) (by positivity) (le_of_lt hy) hprod0
  have hsplit :
      c / (2 * b * x) + 2 * y ≤
        a / b + 2 * f / a + f / (a * b) := by
    have hid :
        a / b + 2 * f / a + f / (a * b) =
          a / (2 * b) + (a / (2 * b) + f * (2 + 1 / b) / a) := by
      field_simp [ha.ne', hb.ne']
      <;> ring
    rw [hid]
    linarith
  have hp1 :
      (6 : ℝ) / 5 ≤ 9 * f / 25 + 1 / f := by
    have hnonneg : 0 ≤ (3 * f - 5) ^ 2 / (25 * f) := by positivity
    have hid :
        9 * f / 25 + 1 / f - (6 : ℝ) / 5 =
          (3 * f - 5) ^ 2 / (25 * f) := by
      field_simp [hf.ne']
      <;> ring
    nlinarith
  have hprod2 :
      ((3 * z / 10) : ℝ) ^ 2 ≤ (9 * f / 100) * (x / f) := by
    field_simp [hf.ne']
    nlinarith [hzSq]
  have hp2 :
      3 * z / 5 ≤ 9 * f / 100 + x / f := by
    have h := hullSixThreeThreeP111_two_mul_le_add
      (u := 9 * f / 100) (v := x / f) (t := 3 * z / 10)
      (by positivity) (by positivity) (by positivity) hprod2
    nlinarith
  have hprod3 :
      ((3 * y / 5) : ℝ) ^ 2 ≤ (f / 4) * (3 * r / (2 * f)) := by
    field_simp [hf.ne']
    nlinarith [hySq]
  have hp3 :
      6 * y / 5 ≤ f / 4 + 3 * r / (2 * f) := by
    have h := hullSixThreeThreeP111_two_mul_le_add
      (u := f / 4) (v := 3 * r / (2 * f)) (t := 3 * y / 5)
      (by positivity) (by positivity) (by positivity) hprod3
    nlinarith
  have hprod4 :
      ((3 * y / (8 * z)) : ℝ) ^ 2 ≤
        (3 * f / 10) * (r / (2 * x * f)) := by
    field_simp [hf.ne', hx.ne', hz.ne']
    nlinarith [hySq, hzSq]
  have hp4 :
      3 * y / (4 * z) ≤ 3 * f / 10 + r / (2 * x * f) := by
    have h := hullSixThreeThreeP111_two_mul_le_add
      (u := 3 * f / 10) (v := r / (2 * x * f))
      (t := 3 * y / (8 * z))
      (by positivity) (by positivity) (by positivity) hprod4
    calc
      3 * y / (4 * z) = 2 * (3 * y / (8 * z)) := by
        field_simp [hz.ne']
        <;> ring
      _ ≤ 3 * f / 10 + r / (2 * x * f) := h
  have halloc :
      (6 : ℝ) / 5 + 3 * z / 5 + 6 * y / 5 + 3 * y / (4 * z) ≤
        f + (1 + x + 3 * r / 2 + r / (2 * x)) / f := by
    have hid :
        9 * f / 25 + 9 * f / 100 + f / 4 + 3 * f / 10 +
            (1 / f + x / f + 3 * r / (2 * f) + r / (2 * x * f)) =
          f + (1 + x + 3 * r / 2 + r / (2 * x)) / f := by
      field_simp [hf.ne', hx.ne']
      <;> ring
    rw [← hid]
    linarith
  have hform :
      4 + c + f + b / f + c / f + f / b + 1 / b +
          c / (2 * b * x) + 2 * y =
        5 + x + r + 1 / r + 2 * y +
          (f + (1 + x + 3 * r / 2 + r / (2 * x)) / f) := by
    have hcEq : c = 1 + x := by linarith
    have hfEq : f = r * b := by
      have h := (eq_div_iff hb.ne').mp hrDef
      nlinarith
    rw [hcEq, hfEq]
    field_simp [hb.ne', hf.ne', hx.ne', hr.ne']
    <;> ring
  have hlower :
      (31 : ℝ) / 5 +
          (z ^ 2 + y ^ 2 + 1 / y ^ 2 + 16 * y / 5 + 3 * z / 5 +
            3 * y / (4 * z)) ≤
        hullSixThreeThreeP111Q223Phi a b c f := by
    have hbase :
        4 + c + f + b / f + c / f + f / b + 1 / b +
            c / (2 * b * x) + 2 * y ≤
          hullSixThreeThreeP111Q223Phi a b c f := by
      unfold hullSixThreeThreeP111Q223Phi
      linarith
    rw [hform] at hbase
    have hinv : 1 / y ^ 2 = 1 / r := by rw [hySq]
    rw [hinv, hzSq, hySq]
    nlinarith
  exact hullSixThreeThreeP111Q223_finish hy hz hlower

theorem hullSixThreeThreeP111Q223_phi
    {a b c f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (hheight : c ≤ a * (c - 1)) :
    (25 : ℝ) / 2 < hullSixThreeThreeP111Q223Phi a b c f := by
  have hx : 0 < c - 1 := by
    by_contra h
    have hnon : a * (c - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) (le_of_not_gt h)
    linarith
  have hr : 0 < f / b := div_pos hf hb
  let y : ℝ := Real.sqrt (f / b)
  let z : ℝ := Real.sqrt (c - 1)
  have hy : 0 < y := by dsimp [y]; exact Real.sqrt_pos.2 hr
  have hz : 0 < z := by dsimp [z]; exact Real.sqrt_pos.2 hx
  have hySq : y ^ 2 = f / b := by
    dsimp [y]
    exact Real.sq_sqrt (le_of_lt hr)
  have hzSq : z ^ 2 = c - 1 := by
    dsimp [z]
    exact Real.sq_sqrt (le_of_lt hx)
  exact hullSixThreeThreeP111Q223_phi_of_roots
    ha hb hc hf hx hr hy hz rfl rfl hySq hzSq hheight

theorem hullSixThreeThreeP111Q223_phi_finish
    {H a b c f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (hheight : c ≤ a * (c - 1))
    (hlower : hullSixThreeThreeP111Q223Phi a b c f ≤ H) :
    (25 : ℝ) / 2 < H :=
  (hullSixThreeThreeP111Q223_phi ha hb hc hf hheight).trans_le hlower

/-! ## The `q = 233` weighted certificate -/

noncomputable def hullSixThreeThreeP111Q233Term
    (p q : ℝ) : Fin 8 → ℝ :=
  ![(1 / 2 : ℝ) * p ^ 4,
    (1 / 2 : ℝ) * p ^ 4 / q ^ 4,
    q ^ 4,
    2 * q ^ 4 / p ^ 4,
    2 / p ^ 4,
    (1 / 2 : ℝ) / q ^ 4,
    (1 / 2 : ℝ) / (p ^ 4 * q ^ 4),
    2 * p / q ^ 3]

def hullSixThreeThreeP111Q233Weight : Fin 8 → ℕ :=
  ![7, 5, 9, 8, 6, 2, 1, 12]

noncomputable def hullSixThreeThreeP111Q233Constant : ℝ :=
  (1 / 14 : ℝ) ^ 7 * (1 / 10 : ℝ) ^ 5 *
    (1 / 9 : ℝ) ^ 9 * (1 / 4 : ℝ) ^ 8 *
    (1 / 3 : ℝ) ^ 6 * (1 / 4 : ℝ) ^ 2 *
    (1 / 2 : ℝ) * (1 / 6 : ℝ) ^ 12

theorem hullSixThreeThreeP111Q233_weight_pos
    (i : Fin 8) : 0 < hullSixThreeThreeP111Q233Weight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP111Q233Weight]

theorem hullSixThreeThreeP111Q233_weight_sum :
    ∑ i, hullSixThreeThreeP111Q233Weight i = 50 := by
  norm_num [hullSixThreeThreeP111Q233Weight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP111Q233_term_nonneg
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (i : Fin 8) :
    0 ≤ hullSixThreeThreeP111Q233Term p q i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP111Q233Term] <;>
    positivity

theorem hullSixThreeThreeP111Q233_term_sum
    (p q : ℝ) :
    ∑ i, hullSixThreeThreeP111Q233Term p q i =
      (1 / 2 : ℝ) * p ^ 4 + (1 / 2 : ℝ) * p ^ 4 / q ^ 4 +
        q ^ 4 + 2 * q ^ 4 / p ^ 4 + 2 / p ^ 4 +
        (1 / 2 : ℝ) / q ^ 4 + (1 / 2 : ℝ) / (p ^ 4 * q ^ 4) +
        2 * p / q ^ 3 := by
  simp [hullSixThreeThreeP111Q233Term, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP111Q233_term_product
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∏ i,
        (hullSixThreeThreeP111Q233Term p q i /
          (hullSixThreeThreeP111Q233Weight i : ℝ)) ^
            hullSixThreeThreeP111Q233Weight i) =
      hullSixThreeThreeP111Q233Constant := by
  simp [hullSixThreeThreeP111Q233Term,
    hullSixThreeThreeP111Q233Weight, Fin.prod_univ_succ,
    hullSixThreeThreeP111Q233Constant]
  field_simp [hp.ne', hq.ne']
  <;> ring

theorem hullSixThreeThreeP111Q233_constant_pos :
    0 < hullSixThreeThreeP111Q233Constant := by
  unfold hullSixThreeThreeP111Q233Constant
  positivity

theorem hullSixThreeThreeP111Q233_root_gap :
    (15 : ℝ) / 2 <
      50 * hullSixThreeThreeP111Q233Constant ^ ((50 : ℝ)⁻¹) := by
  have hpow :
      ((3 : ℝ) / 20) ^ 50 < hullSixThreeThreeP111Q233Constant := by
    norm_num [hullSixThreeThreeP111Q233Constant]
  have hpowRpow :
      ((3 : ℝ) / 20) ^ (50 : ℝ) <
        hullSixThreeThreeP111Q233Constant := by
    change ((3 : ℝ) / 20) ^ ((50 : ℕ) : ℝ) <
      hullSixThreeThreeP111Q233Constant
    rw [Real.rpow_natCast]
    exact hpow
  have hroot :
      (3 : ℝ) / 20 <
        hullSixThreeThreeP111Q233Constant ^ ((50 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity)
      (le_of_lt hullSixThreeThreeP111Q233_constant_pos) (by norm_num)]
    exact hpowRpow
  nlinarith

theorem hullSixThreeThreeP111Q233_amgm
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (15 : ℝ) / 2 <
      (1 / 2 : ℝ) * p ^ 4 + (1 / 2 : ℝ) * p ^ 4 / q ^ 4 +
        q ^ 4 + 2 * q ^ 4 / p ^ 4 + 2 / p ^ 4 +
        (1 / 2 : ℝ) / q ^ 4 + (1 / 2 : ℝ) / (p ^ 4 * q ^ 4) +
        2 * p / q ^ 3 := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP111Q233Weight
    (hullSixThreeThreeP111Q233Term p q)
    hullSixThreeThreeP111Q233_weight_pos
    (hullSixThreeThreeP111Q233_term_nonneg
      (le_of_lt hp) (le_of_lt hq))
  rw [hullSixThreeThreeP111Q233_weight_sum,
    hullSixThreeThreeP111Q233_term_product hp hq] at hamgm
  rw [← hullSixThreeThreeP111Q233_term_sum p q]
  exact hullSixThreeThreeP111Q233_root_gap.trans_le hamgm

theorem hullSixThreeThreeP111Q233_finish
    {H p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hlower :
      (9 : ℝ) / 2 + (1 / 2 : ℝ) +
          ((1 / 2 : ℝ) * p ^ 4 + (1 / 2 : ℝ) * p ^ 4 / q ^ 4 +
            q ^ 4 + 2 * q ^ 4 / p ^ 4 + 2 / p ^ 4 +
            (1 / 2 : ℝ) / q ^ 4 +
            (1 / 2 : ℝ) / (p ^ 4 * q ^ 4) + 2 * p / q ^ 3) ≤ H) :
    (25 : ℝ) / 2 < H := by
  have h := hullSixThreeThreeP111Q233_amgm hp hq
  linarith

noncomputable def hullSixThreeThreeP111Q233Reduced
    (a f : ℝ) : ℝ :=
  a * (f + 1) / (2 * f) + f + (2 * f + (3 : ℝ) / 2) / a +
    (a + 1) * (f + 1) / (2 * a * f) +
    Real.sqrt ((a + 1) * (f + 1)) / f

theorem hullSixThreeThreeP111Q233_reduced_gt
    {a f : ℝ} (ha1 : 1 ≤ a) (hf1 : 1 ≤ f) :
    8 < hullSixThreeThreeP111Q233Reduced a f := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1
  let p : ℝ := hullSixHardChamberFourthRoot a
  let q : ℝ := hullSixHardChamberFourthRoot f
  have hp : 0 < p := by
    dsimp [p, hullSixHardChamberFourthRoot]
    positivity
  have hq : 0 < q := by
    dsimp [q, hullSixHardChamberFourthRoot]
    positivity
  have hp4 : p ^ 4 = a := by
    dsimp [p]
    exact hullSixHardChamber_fourthRoot_pow_four (le_of_lt ha)
  have hq4 : q ^ 4 = f := by
    dsimp [q]
    exact hullSixHardChamber_fourthRoot_pow_four (le_of_lt hf)
  have hinside :
      (2 * p * q) ^ 2 ≤ (a + 1) * (f + 1) := by
    rw [← hp4, ← hq4]
    nlinarith [sq_nonneg (p ^ 2 * q ^ 2 - 1),
      sq_nonneg (p ^ 2 - q ^ 2)]
  have hsqrt :
      2 * p * q ≤ Real.sqrt ((a + 1) * (f + 1)) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ (a + 1) * (f + 1))]
    exact hinside
  have hcross :
      2 * p / q ^ 3 ≤ Real.sqrt ((a + 1) * (f + 1)) / f := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt
      (by positivity : 0 ≤ (1 : ℝ) / f)
    have hleft : 2 * p * q * (1 / f) = 2 * p / q ^ 3 := by
      rw [← hq4]
      field_simp [hq.ne']
      <;> ring
    have hright :
        Real.sqrt ((a + 1) * (f + 1)) * (1 / f) =
          Real.sqrt ((a + 1) * (f + 1)) / f := by ring
    rwa [hleft, hright] at hmul
  have hlower :
      (1 : ℝ) / 2 +
          ((1 / 2 : ℝ) * p ^ 4 + (1 / 2 : ℝ) * p ^ 4 / q ^ 4 +
            q ^ 4 + 2 * q ^ 4 / p ^ 4 + 2 / p ^ 4 +
            (1 / 2 : ℝ) / q ^ 4 +
            (1 / 2 : ℝ) / (p ^ 4 * q ^ 4) + 2 * p / q ^ 3) ≤
        hullSixThreeThreeP111Q233Reduced a f := by
    have hid :
        hullSixThreeThreeP111Q233Reduced a f -
            ((1 : ℝ) / 2 +
              ((1 / 2 : ℝ) * p ^ 4 +
                (1 / 2 : ℝ) * p ^ 4 / q ^ 4 + q ^ 4 +
                2 * q ^ 4 / p ^ 4 + 2 / p ^ 4 +
                (1 / 2 : ℝ) / q ^ 4 +
                (1 / 2 : ℝ) / (p ^ 4 * q ^ 4) + 2 * p / q ^ 3)) =
          Real.sqrt ((a + 1) * (f + 1)) / f - 2 * p / q ^ 3 := by
      unfold hullSixThreeThreeP111Q233Reduced
      rw [hp4, hq4]
      field_simp [ha.ne', hf.ne', hp.ne', hq.ne']
      <;> ring
    nlinarith
  have hamgm := hullSixThreeThreeP111Q233_amgm hp hq
  nlinarith

theorem hullSixThreeThreeP111Q233_reduced_finish
    {H a f : ℝ} (ha1 : 1 ≤ a) (hf1 : 1 ≤ f)
    (hlower :
      (9 : ℝ) / 2 + hullSixThreeThreeP111Q233Reduced a f ≤ H) :
    (25 : ℝ) / 2 < H := by
  have h := hullSixThreeThreeP111Q233_reduced_gt ha1 hf1
  linarith

end Heilbronn8
