import Heilbronn8.Survivors.Join.HullSixHardChamberAMGM

/-!
# Scalar closure for the `p = 222` partial-X frontier

The determinant recurrence along the five cross cells reduces this frontier
to two lower bounds for the middle and final fan sectors.  Only the first two
hull-ear inequalities are then needed.  Splitting on the order of the first
three line heights leaves two six-term AM--GM certificates (both with product
at least four) and one three-term certificate.

This module is deliberately scalar: it contains no configuration or tableau
semantics and no generated certificate.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Heilbronn8

open scoped BigOperators

/-! ## Small unit-weight AM--GM endpoints -/

noncomputable def hullSixThreeThreeP222SixTerm
    (s0 s1 s2 s3 s4 s5 : ℝ) : Fin 6 → ℝ :=
  ![s0, s1, s2, s3, s4, s5]

def hullSixThreeThreeP222SixWeight : Fin 6 → ℕ :=
  ![1, 1, 1, 1, 1, 1]

theorem hullSixThreeThreeP222_sixWeight_pos
    (i : Fin 6) : 0 < hullSixThreeThreeP222SixWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP222SixWeight]

theorem hullSixThreeThreeP222_sixWeight_sum :
    ∑ i, hullSixThreeThreeP222SixWeight i = 6 := by
  norm_num [hullSixThreeThreeP222SixWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP222_sixTerm_nonneg
    {s0 s1 s2 s3 s4 s5 : ℝ}
    (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) (h2 : 0 ≤ s2)
    (h3 : 0 ≤ s3) (h4 : 0 ≤ s4) (h5 : 0 ≤ s5)
    (i : Fin 6) :
    0 ≤ hullSixThreeThreeP222SixTerm s0 s1 s2 s3 s4 s5 i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP222SixTerm, h0, h1, h2, h3, h4, h5]

theorem hullSixThreeThreeP222_sixTerm_sum
    (s0 s1 s2 s3 s4 s5 : ℝ) :
    ∑ i, hullSixThreeThreeP222SixTerm s0 s1 s2 s3 s4 s5 i =
      s0 + s1 + s2 + s3 + s4 + s5 := by
  simp [hullSixThreeThreeP222SixTerm, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP222_sixTerm_product
    (s0 s1 s2 s3 s4 s5 : ℝ) :
    (∏ i,
        (hullSixThreeThreeP222SixTerm s0 s1 s2 s3 s4 s5 i /
          (hullSixThreeThreeP222SixWeight i : ℝ)) ^
            hullSixThreeThreeP222SixWeight i) =
      s0 * s1 * s2 * s3 * s4 * s5 := by
  simp [hullSixThreeThreeP222SixTerm,
    hullSixThreeThreeP222SixWeight, Fin.prod_univ_succ]
  <;> ring

theorem hullSixThreeThreeP222_six_root_gap :
    (15 : ℝ) / 2 < 6 * (4 : ℝ) ^ ((6 : ℝ)⁻¹) := by
  have hpow : ((5 : ℝ) / 4) ^ 6 < 4 := by norm_num
  have hpowRpow : ((5 : ℝ) / 4) ^ (6 : ℝ) < 4 := by
    change ((5 : ℝ) / 4) ^ ((6 : ℕ) : ℝ) < 4
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (5 : ℝ) / 4 < (4 : ℝ) ^ ((6 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by norm_num)
      (by norm_num)]
    exact hpowRpow
  nlinarith

/-- Six positive terms whose product is at least four have sum above `15/2`. -/
theorem hullSixThreeThreeP222_six_sum_gt
    {s0 s1 s2 s3 s4 s5 : ℝ}
    (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) (h2 : 0 ≤ s2)
    (h3 : 0 ≤ s3) (h4 : 0 ≤ s4) (h5 : 0 ≤ s5)
    (hprod : 4 ≤ s0 * s1 * s2 * s3 * s4 * s5) :
    (15 : ℝ) / 2 < s0 + s1 + s2 + s3 + s4 + s5 := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP222SixWeight
    (hullSixThreeThreeP222SixTerm s0 s1 s2 s3 s4 s5)
    hullSixThreeThreeP222_sixWeight_pos
    (hullSixThreeThreeP222_sixTerm_nonneg h0 h1 h2 h3 h4 h5)
  rw [hullSixThreeThreeP222_sixWeight_sum,
    hullSixThreeThreeP222_sixTerm_product] at hamgm
  have hroot :
      (4 : ℝ) ^ ((6 : ℝ)⁻¹) ≤
        (s0 * s1 * s2 * s3 * s4 * s5) ^ ((6 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by norm_num) hprod (by norm_num)
  rw [← hullSixThreeThreeP222_sixTerm_sum s0 s1 s2 s3 s4 s5]
  exact hullSixThreeThreeP222_six_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hroot (by norm_num)).trans hamgm)

noncomputable def hullSixThreeThreeP222ThreeTerm
    (s0 s1 s2 : ℝ) : Fin 3 → ℝ :=
  ![s0, s1, s2]

def hullSixThreeThreeP222ThreeWeight : Fin 3 → ℕ :=
  ![1, 1, 1]

theorem hullSixThreeThreeP222_threeWeight_pos
    (i : Fin 3) : 0 < hullSixThreeThreeP222ThreeWeight i := by
  fin_cases i <;> norm_num [hullSixThreeThreeP222ThreeWeight]

theorem hullSixThreeThreeP222_threeWeight_sum :
    ∑ i, hullSixThreeThreeP222ThreeWeight i = 3 := by
  norm_num [hullSixThreeThreeP222ThreeWeight, Fin.sum_univ_succ]

theorem hullSixThreeThreeP222_threeTerm_nonneg
    {s0 s1 s2 : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) (h2 : 0 ≤ s2)
    (i : Fin 3) :
    0 ≤ hullSixThreeThreeP222ThreeTerm s0 s1 s2 i := by
  fin_cases i <;>
    simp [hullSixThreeThreeP222ThreeTerm, h0, h1, h2]

theorem hullSixThreeThreeP222_threeTerm_sum
    (s0 s1 s2 : ℝ) :
    ∑ i, hullSixThreeThreeP222ThreeTerm s0 s1 s2 i = s0 + s1 + s2 := by
  simp [hullSixThreeThreeP222ThreeTerm, Fin.sum_univ_succ]
  <;> ring

theorem hullSixThreeThreeP222_threeTerm_product
    (s0 s1 s2 : ℝ) :
    (∏ i,
        (hullSixThreeThreeP222ThreeTerm s0 s1 s2 i /
          (hullSixThreeThreeP222ThreeWeight i : ℝ)) ^
            hullSixThreeThreeP222ThreeWeight i) =
      s0 * s1 * s2 := by
  simp [hullSixThreeThreeP222ThreeTerm,
    hullSixThreeThreeP222ThreeWeight, Fin.prod_univ_succ]
  <;> ring

theorem hullSixThreeThreeP222_three_root_gap :
    (9 : ℝ) / 2 < 3 * (4 : ℝ) ^ ((3 : ℝ)⁻¹) := by
  have hpow : ((3 : ℝ) / 2) ^ 3 < 4 := by norm_num
  have hpowRpow : ((3 : ℝ) / 2) ^ (3 : ℝ) < 4 := by
    change ((3 : ℝ) / 2) ^ ((3 : ℕ) : ℝ) < 4
    rw [Real.rpow_natCast]
    exact hpow
  have hroot : (3 : ℝ) / 2 < (4 : ℝ) ^ ((3 : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by norm_num)
      (by norm_num)]
    exact hpowRpow
  nlinarith

/-- Three positive terms whose product is at least four have sum above `9/2`. -/
theorem hullSixThreeThreeP222_three_sum_gt
    {s0 s1 s2 : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) (h2 : 0 ≤ s2)
    (hprod : 4 ≤ s0 * s1 * s2) :
    (9 : ℝ) / 2 < s0 + s1 + s2 := by
  have hamgm := scalar_weighted_amgm_nat
    hullSixThreeThreeP222ThreeWeight
    (hullSixThreeThreeP222ThreeTerm s0 s1 s2)
    hullSixThreeThreeP222_threeWeight_pos
    (hullSixThreeThreeP222_threeTerm_nonneg h0 h1 h2)
  rw [hullSixThreeThreeP222_threeWeight_sum,
    hullSixThreeThreeP222_threeTerm_product] at hamgm
  have hroot :
      (4 : ℝ) ^ ((3 : ℝ)⁻¹) ≤
        (s0 * s1 * s2) ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by norm_num) hprod (by norm_num)
  rw [← hullSixThreeThreeP222_threeTerm_sum s0 s1 s2]
  exact hullSixThreeThreeP222_three_root_gap.trans_le
    ((mul_le_mul_of_nonneg_left hroot (by norm_num)).trans hamgm)

/-! ## The reduced scalar packet -/

/--
Closure of the normalized `p = 222` recurrence-and-ear packet.

The variables `x,y,z` and `p,q,r` are the three upper and lower line heights;
`a,b,g,C,l,m` are the six consecutive `P`-fan sectors.  The hypotheses `hg`,
`hl`, and `hm` are precisely the three recurrence consequences used below.
-/
theorem hullSixThreeThreeP222PartialX_scalar
    {x y z p q r a b g C l m : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hg1 : 1 ≤ g)
    (hC : 1 ≤ C) (hl1 : 1 ≤ l) (hm1 : 1 ≤ m)
    (hB0 : 1 ≤ a + x - y)
    (hE0 : y ≤ a * (y - z) + b * (y - x))
    (hE1 : z ≤ b * (z + p) + g * (z - y))
    (hg : p * z / (q * x) + p * z * a / (x * y) + p * b / y +
      z * C / q ≤ g)
    (hl : q + (q + r + q * r) / x ≤ l)
    (hm : 1 + x + r ≤ m) :
    (25 : ℝ) / 2 < a + b + g + C + l + m := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC

  have scale_one_le {s t : ℝ} (hs : 1 ≤ s) (ht : 0 ≤ t) :
      t ≤ s * t := by
    have hmul := mul_nonneg (sub_nonneg.mpr hs) ht
    nlinarith

  have hp_zqx : z / (q * x) ≤ p * z / (q * x) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      scale_one_le hp (by positivity : 0 ≤ z / (q * x))
  have hp_zaxy : z * a / (x * y) ≤ p * z * a / (x * y) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      scale_one_le hp (by positivity : 0 ≤ z * a / (x * y))
  have hp_by : b / y ≤ p * b / y := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      scale_one_le hp (by positivity : 0 ≤ b / y)
  have hC_zq : z / q ≤ z * C / q := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      scale_one_le hC (by positivity : 0 ≤ z / q)
  have hgWeak :
      z / (q * x) + z * a / (x * y) + b / y + z / q ≤ g := by
    linarith

  have hqr : q ≤ q * r := by
    simpa [mul_comm] using scale_one_le hr (le_of_lt hq0)
  have hnum : 2 * q + 1 ≤ q + r + q * r := by linarith
  have hfrac : (2 * q + 1) / x ≤ (q + r + q * r) / x :=
    (div_le_div_iff_of_pos_right hx0).2 hnum
  have hlWeak : q + (2 * q + 1) / x ≤ l := by linarith
  have hmWeak : x + 2 ≤ m := by linarith

  by_cases hyz : y ≤ z
  · have hyx : x < y := by
      by_contra hxy
      have hyx' : y ≤ x := le_of_not_gt hxy
      have hleft : a * (y - z) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha0) (by linarith)
      have hright : b * (y - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb0) (by linarith)
      linarith
    let t : ℝ := y / x
    have ht : 1 < t := by
      dsimp [t]
      exact (lt_div_iff₀ hx0).2 (by simpa using hyx)
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hyqx : y / (q * x) = t / q := by
      dsimp [t]
      field_simp [hx0.ne', hq0.ne']
      <;> ring
    have hyq : y / q = x * t / q := by
      dsimp [t]
      field_simp [hx0.ne', hq0.ne']
      <;> ring
    have hzyqx : y / (q * x) ≤ z / (q * x) :=
      (div_le_div_iff_of_pos_right (mul_pos hq0 hx0)).2 hyz
    have hza : y ≤ z * a := by
      calc
        y ≤ z := hyz
        _ ≤ z * a := by
          simpa only [mul_comm] using scale_one_le ha (le_of_lt hz0)
    have hzaDiv : 1 / x ≤ z * a / (x * y) := by
      calc
        1 / x = y / (x * y) := by
          field_simp [hx0.ne', hy0.ne']
        _ ≤ z * a / (x * y) :=
          (div_le_div_iff_of_pos_right (mul_pos hx0 hy0)).2 hza
    have hzyq : y / q ≤ z / q :=
      (div_le_div_iff_of_pos_right hq0).2 hyz
    have hbdiv : 0 < b / y := div_pos hb0 hy0
    have hbase :
        5 + (x + 2 / x + q + 2 * q / x + t / q + x * t / q) <
          a + b + g + C + l + m := by
      rw [← hyqx, ← hyq]
      have hgBase :
          y / (q * x) + 1 / x + y / q < g := by
        calc
          y / (q * x) + 1 / x + y / q <
              z / (q * x) + z * a / (x * y) + b / y + z / q := by
            linarith only [hzyqx, hzaDiv, hzyq, hbdiv]
          _ ≤ g := hgWeak
      have hconst : (3 : ℝ) ≤ a + b + C := by
        calc
          (3 : ℝ) = (1 + 1) + 1 := by norm_num
          _ ≤ (a + b) + C := add_le_add (add_le_add ha hb) hC
      have hfixed :
          3 + (q + (2 * q + 1) / x) + (x + 2) ≤
            (a + b + C) + l + m :=
        add_le_add (add_le_add hconst hlWeak) hmWeak
      calc
        5 + (x + 2 / x + q + 2 * q / x +
            y / (q * x) + y / q) =
            (3 + (q + (2 * q + 1) / x) + (x + 2)) +
              (y / (q * x) + 1 / x + y / q) := by ring
        _ < ((a + b + C) + l + m) + g :=
          add_lt_add_of_le_of_lt hfixed hgBase
        _ = a + b + g + C + l + m := by ring
    have htSq : 1 ≤ t * t := by nlinarith
    have hprod :
        4 ≤ x * (2 / x) * q * (2 * q / x) * (t / q) * (x * t / q) := by
      calc
        (4 : ℝ) ≤ 4 * (t * t) := by nlinarith
        _ = x * (2 / x) * q * (2 * q / x) * (t / q) *
              (x * t / q) := by
          field_simp [hx0.ne', hq0.ne']
          <;> ring
    have hsix := hullSixThreeThreeP222_six_sum_gt
      (le_of_lt hx0) (by positivity : 0 ≤ 2 / x)
      (le_of_lt hq0) (by positivity : 0 ≤ 2 * q / x)
      (by positivity : 0 ≤ t / q) (by positivity : 0 ≤ x * t / q)
      hprod
    linarith
  · have hzy : z < y := lt_of_not_ge hyz
    let D : ℝ :=
      p * z / (q * x) + p * z * a / (x * y) + z * C / q
    have hD0 : 0 ≤ D := by
      dsimp [D]
      positivity
    have hgD : D + p * b / y ≤ g := by
      simpa [D, add_assoc, add_comm, add_left_comm] using hg
    have hneg : z - y ≤ 0 := by linarith
    have hscaled :
        g * (z - y) ≤ (D + p * b / y) * (z - y) :=
      mul_le_mul_of_nonpos_right hgD hneg
    have hEarWeak :
        z ≤ b * (z + p) + (D + p * b / y) * (z - y) := by
      calc
        z ≤ b * (z + p) + g * (z - y) := hE1
        _ ≤ b * (z + p) + (D + p * b / y) * (z - y) := by
          simpa only [add_comm] using
            (add_le_add_left hscaled (b * (z + p)))
    have hEarIdentity :
        b * (z + p) + (D + p * b / y) * (z - y) - z =
          z * (b * (1 + p / y) - (1 + (y / z - 1) * D)) := by
      field_simp [hy0.ne', hz0.ne']
      <;> ring
    have hEarNonneg :
        0 ≤ z * (b * (1 + p / y) - (1 + (y / z - 1) * D)) := by
      rw [← hEarIdentity]
      linarith
    have hEarNormalized :
        1 + (y / z - 1) * D ≤ b * (1 + p / y) := by
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hz0).mp hEarNonneg)
    have hPairD : 1 + (y / z) * D ≤ b + g := by
      have hbg : D + b * (1 + p / y) ≤ b + g := by
        calc
          D + b * (1 + p / y) = b + (D + p * b / y) := by ring
          _ ≤ b + g := by
            simpa only [add_comm] using add_le_add_left hgD b
      linarith
    have hDidentity :
        (y / z) * D = p * y / (q * x) + p * a / x + y * C / q := by
      dsimp [D]
      field_simp [hx0.ne', hy0.ne', hz0.ne', hq0.ne']
      <;> ring
    have hp_yqx : y / (q * x) ≤ p * y / (q * x) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        scale_one_le hp (by positivity : 0 ≤ y / (q * x))
    have hp_ax : a / x ≤ p * a / x := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        scale_one_le hp (by positivity : 0 ≤ a / x)
    have hPair :
        1 + y / (q * x) + a / x + y * C / q ≤ b + g := by
      rw [hDidentity] at hPairD
      linarith
    have hF :
        3 + x + q + (2 * q + 1) / x + a + C +
            y / (q * x) + a / x + y * C / q ≤
          a + b + g + C + l + m := by
      linarith [hPair, hlWeak, hmWeak]
    by_cases hxy : x < y
    · have hyqxStrict : 1 / q < y / (q * x) := by
        calc
          1 / q = x / (q * x) := by
            field_simp [hx0.ne', hq0.ne']
          _ < y / (q * x) :=
            (div_lt_div_iff_of_pos_right (mul_pos hq0 hx0)).2 hxy
      have hxyq : x / q < y * C / q := by
        have hxyC : x < y * C :=
          lt_of_lt_of_le hxy
            (by simpa only [mul_comm] using scale_one_le hC (le_of_lt hy0))
        exact (div_lt_div_iff_of_pos_right hq0).2 hxyC
      have hax : 1 / x ≤ a / x :=
        (div_le_div_iff_of_pos_right hx0).2 ha
      have hbase :
          5 + (x + 2 / x + q + 2 * q / x + x / q + 1 / q) <
            a + b + g + C + l + m := by
        have htail :
            2 + 1 / x + 1 / q + x / q <
              a + C + a / x + y / (q * x) + y * C / q := by
          calc
            2 + 1 / x + 1 / q + x / q =
                (1 + 1) + ((1 / x + 1 / q) + x / q) := by ring
            _ < (a + C) +
                  ((a / x + y / (q * x)) + y * C / q) :=
              add_lt_add_of_le_of_lt (add_le_add ha hC)
                (add_lt_add
                  (add_lt_add_of_le_of_lt hax hyqxStrict) hxyq)
            _ = a + C + a / x + y / (q * x) + y * C / q := by ring
        calc
          5 + (x + 2 / x + q + 2 * q / x + x / q + 1 / q) =
              (3 + x + q + (2 * q + 1) / x) +
                (2 + 1 / x + 1 / q + x / q) := by ring
          _ < (3 + x + q + (2 * q + 1) / x) +
              (a + C + a / x + y / (q * x) + y * C / q) :=
            add_lt_add_of_le_of_lt le_rfl htail
          _ = 3 + x + q + (2 * q + 1) / x + a + C +
              y / (q * x) + a / x + y * C / q := by ring
          _ ≤ a + b + g + C + l + m := hF
      have hprod :
          4 ≤ x * (2 / x) * q * (2 * q / x) * (x / q) * (1 / q) := by
        calc
          (4 : ℝ) ≤ 4 := le_rfl
          _ = x * (2 / x) * q * (2 * q / x) * (x / q) * (1 / q) := by
            field_simp [hx0.ne', hq0.ne']
            <;> ring
      have hsix := hullSixThreeThreeP222_six_sum_gt
        (le_of_lt hx0) (by positivity : 0 ≤ 2 / x)
        (le_of_lt hq0) (by positivity : 0 ≤ 2 * q / x)
        (by positivity : 0 ≤ x / q) (by positivity : 0 ≤ 1 / q)
        hprod
      linarith
    · have hyx : y ≤ x := le_of_not_gt hxy
      have hright : b * (y - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb0) (by linarith)
      have hfirst : y ≤ a * (y - z) := by linarith
      have hayOne : y ≤ a * (y - 1) := by
        have hyzOne : y - z ≤ y - 1 := by linarith
        exact hfirst.trans (mul_le_mul_of_nonneg_left hyzOne (le_of_lt ha0))
      have hyOne : 0 < y - 1 := by linarith
      have haRatio : y / (y - 1) ≤ a :=
        (div_le_iff₀ hyOne).2 (by simpa [mul_comm] using hayOne)
      have hratioFour : 4 ≤ y * y / (y - 1) := by
        apply (le_div_iff₀ hyOne).2
        nlinarith [sq_nonneg (y - 2)]
      have hratioMul : y * y / (y - 1) ≤ a * y := by
        have hmul := mul_le_mul_of_nonneg_right haRatio (le_of_lt hy0)
        calc
          y * y / (y - 1) = (y / (y - 1)) * y := by ring
          _ ≤ a * y := hmul
      have hay : 4 ≤ a * y := hratioFour.trans hratioMul
      have hayC : 4 ≤ a * q * (y * C / q) := by
        have hCscale : a * y ≤ a * y * C := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hC
              (mul_nonneg (le_of_lt ha0) (le_of_lt hy0)))
        calc
          (4 : ℝ) ≤ a * y := hay
          _ ≤ a * y * C := hCscale
          _ = a * q * (y * C / q) := by
            field_simp [hq0.ne']
            <;> ring
      have hthree := hullSixThreeThreeP222_three_sum_gt
        (le_of_lt ha0) (le_of_lt hq0) (by positivity : 0 ≤ y * C / q)
        hayC
      have hpairNum : (14 : ℝ) / 5 < 2 * q + y / q := by
        have hnum : ((14 : ℝ) / 5) * q < 2 * q * q + y := by
          nlinarith [sq_nonneg (10 * q - 7)]
        calc
          (14 : ℝ) / 5 < (2 * q * q + y) / q :=
            (lt_div_iff₀ hq0).2 hnum
          _ = 2 * q + y / q := by
            field_simp [hq0.ne']
            <;> ring
      have hcoeff : (24 : ℝ) / 5 < 2 * q + 1 + a + y / q := by
        linarith
      have hxRat : 4 < x + (24 : ℝ) / (5 * x) := by
        have hnum : 0 < 5 * x ^ 2 - 20 * x + 24 := by
          nlinarith [sq_nonneg (x - 2)]
        have hid :
            x + (24 : ℝ) / (5 * x) - 4 =
              (5 * x ^ 2 - 20 * x + 24) / (5 * x) := by
          field_simp [hx0.ne']
          <;> ring
        apply sub_pos.mp
        rw [hid]
        exact div_pos hnum (by positivity)
      have hcoeffDiv :
          (24 : ℝ) / (5 * x) < (2 * q + 1 + a + y / q) / x := by
        simpa only [div_div] using
          ((div_lt_div_iff_of_pos_right hx0).2 hcoeff)
      have hxCoeff : 4 < x + (2 * q + 1 + a + y / q) / x := by
        linarith
      have hdecomp :
          3 + (a + q + y * C / q) + C +
              (x + (2 * q + 1 + a + y / q) / x) =
            3 + x + q + (2 * q + 1) / x + a + C +
              y / (q * x) + a / x + y * C / q := by
        field_simp [hx0.ne', hq0.ne']
        <;> ring
      rw [← hdecomp] at hF
      linarith

end Heilbronn8
