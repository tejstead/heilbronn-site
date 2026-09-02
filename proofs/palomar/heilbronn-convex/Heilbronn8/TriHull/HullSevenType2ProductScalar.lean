import Heilbronn8.TriHull.HullSevenType2HyperbolicBracket
import Heilbronn8.TriHull.HullSevenType2TwoVarCore

/-!
# Compact product-ear closer for the honest hull-seven type-2 chart

This file contains the human reduction from the honest hyperbolic packet to
the two-variable inequalities checked separately by
`HullSevenType2TwoVarCertificate`.  It deliberately imports only the checker
core: the final scalar theorem takes the two branch inequalities through one
small proposition, so the certificate can instantiate that proposition in a
cycle-free downstream file.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

open HullSevenType2TwoVar

/-- The only numerical interface consumed by the product-ear reduction.

The fields deliberately match the two public theorems exported by
`HullSevenType2TwoVarCertificate`. -/
structure HullSevenType2TwoVarBound : Prop where
  lower : ∀ {x d y t : ℝ},
    1 ≤ x →
    1 < x * d →
    d ≤ x →
    0 ≤ y →
    0 ≤ t →
    y ^ 2 = ySqValue x d →
    t ^ 2 = radValue .lower x d →
    19 / 2 < y * (1 + 1 / d) + 2 * t
  upper : ∀ {x d y t : ℝ},
    1 ≤ x →
    1 < x * d →
    x ≤ d →
    0 ≤ y →
    0 ≤ t →
    y ^ 2 = ySqValue x d →
    t ^ 2 = radValue .upper x d →
    19 / 2 < y * (1 + 1 / d) + 2 * t

private lemma two_sqrt_mul_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  rw [Real.sqrt_mul ha]
  have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]

namespace HullSevenType2HyperbolicPacket

/-- The honest type-2 product-ear packet cannot have normalized area at most
`25/2`, assuming only the two exact two-variable branch bounds. -/
theorem product_not_beats {H : ℝ} (D : HullSevenType2HyperbolicPacket H)
    (hTwoVar : HullSevenType2TwoVarBound) : 25 / 2 < H := by
  let m : ℝ := Real.sqrt (D.X ^ 2 + D.Q)
  let u : ℝ := Real.sqrt (D.r ^ 2 + D.Z)
  let d : ℝ := m - D.X
  let alpha : ℝ := m + D.X
  let p : ℝ := D.s - D.Y
  let e : ℝ := u - D.r

  have hWpos : 0 < D.W := lt_of_lt_of_le (by norm_num) D.W_floor
  have hUpos : 0 < D.U := lt_of_lt_of_le (by norm_num) D.U_floor

  have hm_sq : m ^ 2 = D.X ^ 2 + D.Q := by
    dsimp [m]
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) D.Q_pos.le)
  have hu_sq : u ^ 2 = D.r ^ 2 + D.Z := by
    dsimp [u]
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) D.Z_pos.le)
  have hXm : D.X < m := by
    dsimp [m]
    apply (Real.lt_sqrt D.X_pos.le).2
    nlinarith [D.Q_pos]
  have hru : D.r < u := by
    dsimp [u]
    apply (Real.lt_sqrt D.r_pos.le).2
    nlinarith [D.Z_pos]
  have huU : u ≤ D.U := by
    have hzscale : D.Z ≤ D.h * D.Z := by
      simpa using mul_le_mul_of_nonneg_right D.h_floor D.Z_pos.le
    have husq : u ^ 2 ≤ D.U ^ 2 := by
      nlinarith [hu_sq, D.U_sq, hzscale]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hUpos.le).mp husq

  have hR1 : D.X * D.Z + D.Y * u ≤ D.r * D.s :=
    (add_le_add_right (mul_le_mul_of_nonneg_left huU D.Y_pos.le) _).trans
      D.old_left_row
  have hR2 : u + D.r ≤ D.Z * D.W :=
    (add_le_add_left huU D.r).trans D.terminal_sum

  have hd : 0 < d := by simpa [d] using hXm
  have hp : 0 < p := by simpa [p] using D.Y_lt_s
  have he : 0 < e := by simpa [e] using hru
  have hm0 : 0 ≤ m := by dsimp [m]; exact Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := by dsimp [u]; exact Real.sqrt_nonneg _
  have halpha : 0 < alpha := by
    change 0 < m + D.X
    exact add_pos_of_nonneg_of_pos hm0 D.X_pos
  have hsum : 0 < u + D.r :=
    add_pos_of_nonneg_of_pos hu0 D.r_pos

  have hQ : d * alpha = D.Q := by
    dsimp [d, alpha]
    nlinarith [hm_sq]
  have hZ : e * (u + D.r) = D.Z := by
    dsimp [e]
    nlinarith [hu_sq]
  have hZQ : p * (D.s + D.Y) = D.Z * D.Q := by
    dsimp [p]
    nlinarith [D.s_sq]
  have halpha_eq : alpha = 2 * D.X + d := by
    dsimp [alpha, d]
    ring

  /- The first reflected row collapses to `alpha*e ≤ p`. -/
  have hfac1 :
      2 * p * (D.r * D.s - D.X * D.Z - D.Y * u) =
        (u + D.r) * (p - alpha * e) * (p + d * e) := by
    calc
      2 * p * (D.r * D.s - D.X * D.Z - D.Y * u) =
          (u + D.r) * p ^ 2 - e * (p * (D.s + D.Y)) -
            alpha * D.Z * p + d * D.Z * p := by
        dsimp [p, e, d, alpha]
        ring
      _ = (u + D.r) * p ^ 2 - e * (D.Z * D.Q) -
            alpha * D.Z * p + d * D.Z * p := by rw [hZQ]
      _ = (u + D.r) * (p - alpha * e) * (p + d * e) := by
        rw [← hQ, ← hZ]
        ring
  have hpa : alpha * e ≤ p := by
    have hlhs :
        0 ≤ 2 * p * (D.r * D.s - D.X * D.Z - D.Y * u) := by
      have hrow : 0 ≤ D.r * D.s - D.X * D.Z - D.Y * u := by
        linarith [hR1]
      positivity
    rw [hfac1] at hlhs
    by_contra hn
    have hneg : p - alpha * e < 0 := by linarith
    have hlast : 0 < p + d * e := by positivity
    have hrhs : (u + D.r) * (p - alpha * e) * (p + d * e) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hsum hneg) hlast
    linarith

  /- A second exact factorization gives the useful lower bound on `r`. -/
  have hfac2 :
      2 * e * (D.r * D.Q - D.X * D.s - D.Y * m) =
        (p - alpha * e) * (2 * D.Y + p + d * e) := by
    symm
    calc
      (p - alpha * e) * (2 * D.Y + p + d * e) =
          p * (D.s + D.Y) + d * e * p -
            alpha * e * (D.s + D.Y) - alpha * d * e ^ 2 := by
        dsimp [p]
        ring
      _ = D.Z * D.Q + d * e * p -
            alpha * e * (D.s + D.Y) - alpha * d * e ^ 2 := by rw [hZQ]
      _ = 2 * e * (D.r * D.Q - D.X * D.s - D.Y * m) := by
        rw [← hZ, ← hQ]
        dsimp [d, e, alpha, p]
        ring
  have hF2 : D.X * D.s + D.Y * m ≤ D.r * D.Q := by
    have htail : 0 ≤ 2 * D.Y + p + d * e :=
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) D.Y_pos.le) hp.le)
        (mul_nonneg hd.le he.le)
    have hrhs : 0 ≤ (p - alpha * e) * (2 * D.Y + p + d * e) :=
      mul_nonneg (sub_nonneg.mpr hpa) htail
    rw [← hfac2] at hrhs
    by_contra hn
    have hneg : D.r * D.Q - D.X * D.s - D.Y * m < 0 := by linarith
    have hlhs : 2 * e * (D.r * D.Q - D.X * D.s - D.Y * m) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith

  /- The terminal row and the two product caps give the reciprocal bounds. -/
  have hF3 : 1 ≤ D.W * e := by
    have heR2 := mul_le_mul_of_nonneg_left hR2 he.le
    have hz : D.Z * 1 ≤ D.Z * (D.W * e) := by
      calc
        D.Z * 1 = e * (u + D.r) := by rw [hZ]; ring
        _ ≤ e * (D.Z * D.W) := heR2
        _ = D.Z * (D.W * e) := by ring
    exact le_of_mul_le_mul_left hz D.Z_pos
  have hF4 : alpha ≤ D.W * p := by
    have ha1 := mul_le_mul_of_nonneg_left hF3 halpha.le
    have hwp := mul_le_mul_of_nonneg_left hpa hWpos.le
    calc
      alpha = alpha * 1 := by ring
      _ ≤ alpha * (D.W * e) := ha1
      _ = D.W * (alpha * e) := by ring
      _ ≤ D.W * p := hwp
  have hF5 : d * alpha ≤ D.P * p := by
    rw [hQ]
    exact D.Q_le_Pp
  have hF6 : d * alpha ≤ D.X * D.W * p := by
    calc
      d * alpha ≤ D.P * p := hF5
      _ ≤ (D.X * D.W) * p :=
        mul_le_mul_of_nonneg_right D.P_product hp.le

  have hr_lower :
      D.Y / d + D.X * p / (d * alpha) ≤ D.r := by
    have hdiv : (D.X * D.s + D.Y * m) / D.Q ≤ D.r :=
      (div_le_iff₀ D.Q_pos).2 hF2
    calc
      D.Y / d + D.X * p / (d * alpha) =
          (D.X * D.s + D.Y * m) / D.Q := by
        rw [← hQ]
        field_simp [hd.ne', halpha.ne']
        dsimp [p, d, alpha]
        ring
      _ ≤ D.r := hdiv
  have hP_lower : d * alpha / p ≤ D.P :=
    (div_le_iff₀ hp).2 hF5
  have hW_lower : alpha / p ≤ D.W :=
    (div_le_iff₀ hp).2 hF4
  have hW_product_lower : d * alpha / (D.X * p) ≤ D.W := by
    apply (div_le_iff₀ (mul_pos D.X_pos hp)).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hF6

  /- The first product cap supplies the strict two-variable domain. -/
  have hcap :
      D.X * p + D.Y * alpha ≤ D.X * D.Y * (d * alpha) := by
    calc
      D.X * p + D.Y * alpha = D.X * D.s + D.Y * m := by
        dsimp [p, alpha]
        ring
      _ ≤ D.r * D.Q := hF2
      _ ≤ (D.X * D.Y) * D.Q :=
        mul_le_mul_of_nonneg_right D.r_product D.Q_pos.le
      _ = D.X * D.Y * (d * alpha) := by rw [hQ]
  have hprod : 1 < D.X * d := by
    by_contra hn
    have hxd : D.X * d ≤ 1 := le_of_not_gt hn
    have hright : D.X * D.Y * (d * alpha) ≤ D.Y * alpha := by
      calc
        D.X * D.Y * (d * alpha) = (D.X * d) * (D.Y * alpha) := by ring
        _ ≤ 1 * (D.Y * alpha) :=
          mul_le_mul_of_nonneg_right hxd (mul_nonneg D.Y_pos.le halpha.le)
        _ = D.Y * alpha := one_mul _
    have hxp_nonpos : D.X * p ≤ 0 := by linarith [hcap, hright]
    exact (not_le_of_gt (mul_pos D.X_pos hp)) hxp_nonpos
  have hdom : 1 / D.X < d := by
    apply (div_lt_iff₀ D.X_pos).2
    nlinarith [hprod]
  have hxp : D.X * p ≤ D.Y * alpha * (D.X * d - 1) := by
    nlinarith [hcap]

  let pR : ℝ := D.Y * alpha * (d - 1 / D.X)
  have hpR : p ≤ pR := by
    have hmul : D.X * p ≤ D.X * pR := by
      calc
        D.X * p ≤ D.Y * alpha * (D.X * d - 1) := hxp
        _ = D.X * pR := by
          dsimp [pR]
          field_simp [D.X_pos.ne']
    exact le_of_mul_le_mul_left hmul D.X_pos
  have hpRpos : 0 < pR := lt_of_lt_of_le hp hpR

  /- The paired second ear lowers `Y` to the exact checker expression. -/
  let delta0 : ℝ := delta D.X d
  have hdelta : 0 < delta0 := by
    dsimp [delta0, delta]
    have hfirst : 0 < d - 1 / D.X := sub_pos.mpr hdom
    have hsecond : 0 < d + 2 * D.X - 1 / D.X := by nlinarith
    exact mul_pos hfirst hsecond
  have hqValue : qValue D.X d = D.Q := by
    dsimp [qValue]
    rw [← hQ, halpha_eq]
  have hsecond :
      2 + alpha * (d - 1 / D.X) =
        d * (d + 2 * D.X - 1 / D.X) := by
    rw [halpha_eq]
    field_simp [D.X_pos.ne']
    ring
  have hpRfac :
      pR * (2 * D.Y + pR) = (delta0 * D.Y ^ 2) * D.Q := by
    calc
      pR * (2 * D.Y + pR) =
          D.Y ^ 2 * (alpha * (d - 1 / D.X)) *
            (2 + alpha * (d - 1 / D.X)) := by
        dsimp [pR]
        ring
      _ = D.Y ^ 2 * (alpha * (d - 1 / D.X)) *
            (d * (d + 2 * D.X - 1 / D.X)) := by rw [hsecond]
      _ = (delta0 * D.Y ^ 2) * (d * alpha) := by
        dsimp [delta0, delta]
        ring
      _ = (delta0 * D.Y ^ 2) * D.Q := by rw [hQ]
  have hZT : D.Z ≤ delta0 * D.Y ^ 2 := by
    have hnum :
        p * (2 * D.Y + p) ≤ pR * (2 * D.Y + pR) := by
      have htail : 0 ≤ 2 * D.Y + pR + p :=
        add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) D.Y_pos.le) hpRpos.le)
          hp.le
      have hnonneg : 0 ≤ (pR - p) * (2 * D.Y + pR + p) :=
        mul_nonneg (sub_nonneg.mpr hpR) htail
      nlinarith
    have hZnum : D.Z * D.Q = p * (2 * D.Y + p) := by
      calc
        D.Z * D.Q = p * (D.s + D.Y) := hZQ.symm
        _ = p * (2 * D.Y + p) := by dsimp [p]; ring
    have hmul : D.Z * D.Q ≤ (delta0 * D.Y ^ 2) * D.Q := by
      rw [hZnum, ← hpRfac]
      exact hnum
    exact le_of_mul_le_mul_right hmul D.Q_pos

  let T : ℝ := delta0 * D.Y ^ 2
  let E : ℝ → ℝ := fun z => (z - 1) * (D.Y ^ 2 + z) - z * D.Q
  have hTpos : 0 < T := by
    dsimp [T]
    exact mul_pos hdelta (sq_pos_of_pos D.Y_pos)
  have hEZ : 0 ≤ E D.Z := by
    dsimp [E]
    linarith [D.secondEar_product]
  have htransfer :
      D.Z * E T - T * E D.Z =
        (T - D.Z) * (D.Z * T + D.Y ^ 2) := by
    dsimp [E]
    ring
  have hET : 0 ≤ E T := by
    have hdiff : 0 ≤ D.Z * E T - T * E D.Z := by
      rw [htransfer]
      exact mul_nonneg (sub_nonneg.mpr (by simpa [T] using hZT))
        (add_nonneg (mul_nonneg D.Z_pos.le hTpos.le) (sq_nonneg D.Y))
    have hTE : 0 ≤ T * E D.Z := mul_nonneg hTpos.le hEZ
    have hZET : 0 ≤ D.Z * E T := by linarith
    exact (mul_nonneg_iff_of_pos_left D.Z_pos).mp hZET
  have hbracket :
      0 ≤ (delta0 * D.Y ^ 2 - 1) * (1 + delta0) - delta0 * D.Q := by
    have hre :
        E T = D.Y ^ 2 *
          ((delta0 * D.Y ^ 2 - 1) * (1 + delta0) - delta0 * D.Q) := by
      dsimp [E, T]
      ring
    rw [hre] at hET
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos D.Y_pos)).mp hET
  have hyValueEq :
      ySqValue D.X d = 1 / delta0 + D.Q / (1 + delta0) := by
    dsimp only [ySqValue]
    rw [hqValue]
  have hySq_le : ySqValue D.X d ≤ D.Y ^ 2 := by
    have hden : 0 < delta0 * (1 + delta0) := by positivity
    have hid :
        delta0 * (1 + delta0) *
            (D.Y ^ 2 - ySqValue D.X d) =
          (delta0 * D.Y ^ 2 - 1) * (1 + delta0) - delta0 * D.Q := by
      rw [hyValueEq]
      field_simp [hdelta.ne', (by positivity : (1 + delta0) ≠ 0)]
      ring
    have hmul :
        0 ≤ delta0 * (1 + delta0) *
          (D.Y ^ 2 - ySqValue D.X d) := by rw [hid]; exact hbracket
    have := (mul_nonneg_iff_of_pos_left hden).mp hmul
    linarith

  let y0 : ℝ := Real.sqrt (ySqValue D.X d)
  have hyValuePos : 0 < ySqValue D.X d := by
    rw [hyValueEq]
    exact add_pos (div_pos (by norm_num) hdelta)
      (div_pos D.Q_pos (by linarith [hdelta]))
  have hy0 : 0 ≤ y0 := by dsimp [y0]; positivity
  have hy0sq : y0 ^ 2 = ySqValue D.X d := by
    dsimp [y0]
    exact Real.sq_sqrt hyValuePos.le
  have hy0Y : y0 ≤ D.Y := by
    apply (sq_le_sq₀ hy0 D.Y_pos.le).mp
    rw [hy0sq]
    exact hySq_le

  /- The two reciprocal choices are closed separately by AM-GM. -/
  have hinvd_nonneg : 0 ≤ (1 : ℝ) / d := div_nonneg zero_le_one hd.le
  have hfactor_nonneg : 0 ≤ 1 + 1 / d :=
    add_nonneg zero_le_one hinvd_nonneg
  have hyterm : y0 * (1 + 1 / d) ≤ D.Y * (1 + 1 / d) :=
    mul_le_mul_of_nonneg_right hy0Y hfactor_nonneg

  have hdalpha_pos : 0 < d * alpha := mul_pos hd halpha
  have hfrac_lower : 0 ≤ D.X / (d * alpha) :=
    div_nonneg D.X_pos.le hdalpha_pos.le
  have hd_one_nonneg : 0 ≤ d + 1 := by linarith [hd]
  have hrecipX_nonneg : 0 ≤ (1 : ℝ) / D.X :=
    one_div_nonneg.mpr D.X_pos.le

  have hJ : 19 / 2 < D.r + D.s + D.P + D.W := by
    rcases le_total d D.X with horder | horder
    · let aa : ℝ := p * (1 + D.X / (d * alpha))
      let bb : ℝ := alpha * (d + 1) / p
      let t : ℝ := Real.sqrt (radValue .lower D.X d)
      have haa : 0 ≤ aa := by
        dsimp [aa]
        exact mul_nonneg hp.le (add_nonneg zero_le_one hfrac_lower)
      have hbb : 0 ≤ bb := by
        dsimp [bb]
        exact div_nonneg (mul_nonneg halpha.le hd_one_nonneg) hp.le
      have hradeq : aa * bb = radValue .lower D.X d := by
        calc
          aa * bb = (alpha + D.X / d) * (d + 1) := by
            dsimp [aa, bb]
            field_simp [hd.ne', halpha.ne', hp.ne']
          _ = radValue .lower D.X d := by
            rw [halpha_eq]
            simp only [radValue]
      have hradminus : 0 ≤ radValue .lower D.X d := by
        rw [← hradeq]
        exact mul_nonneg haa hbb
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have htsq : t ^ 2 = radValue .lower D.X d := by
        dsimp [t]
        exact Real.sq_sqrt hradminus
      have hcert := hTwoVar.lower D.X_floor hprod horder hy0 ht hy0sq htsq
      have hamgm : 2 * t ≤ aa + bb := by
        have hraw := two_sqrt_mul_le_add haa hbb
        rw [hradeq] at hraw
        simpa [t] using hraw
      have hsumlower :
          D.Y * (1 + 1 / d) + aa + bb ≤ D.r + D.s + D.P + D.W := by
        calc
          D.Y * (1 + 1 / d) + aa + bb =
              (D.Y / d + D.X * p / (d * alpha)) + D.s +
                (d * alpha / p) + (alpha / p) := by
            dsimp [aa, bb, p]
            field_simp [hd.ne', halpha.ne', hp.ne']
            ring
          _ ≤ D.r + D.s + D.P + D.W := by
            linarith [hr_lower, hP_lower, hW_lower]
      have hGJ : y0 * (1 + 1 / d) + 2 * t ≤
          D.r + D.s + D.P + D.W :=
        calc
          y0 * (1 + 1 / d) + 2 * t ≤
              D.Y * (1 + 1 / d) + (aa + bb) :=
            add_le_add hyterm hamgm
          _ ≤ D.r + D.s + D.P + D.W := by
            linarith [hsumlower]
      exact hcert.trans_le hGJ
    · let aa : ℝ := p * (1 + D.X / (d * alpha))
      let bb : ℝ := d * alpha * (1 + 1 / D.X) / p
      let t : ℝ := Real.sqrt (radValue .upper D.X d)
      have haa : 0 ≤ aa := by
        dsimp [aa]
        exact mul_nonneg hp.le (add_nonneg zero_le_one hfrac_lower)
      have hbb : 0 ≤ bb := by
        dsimp [bb]
        exact div_nonneg
          (mul_nonneg hdalpha_pos.le
            (add_nonneg zero_le_one hrecipX_nonneg)) hp.le
      have hradeq : aa * bb = radValue .upper D.X d := by
        calc
          aa * bb = (d * alpha + D.X) * (1 + 1 / D.X) := by
            dsimp [aa, bb]
            field_simp [D.X_pos.ne', hd.ne', halpha.ne', hp.ne']
          _ = radValue .upper D.X d := by
            rw [halpha_eq]
            simp only [radValue]
      have hradplus : 0 ≤ radValue .upper D.X d := by
        rw [← hradeq]
        exact mul_nonneg haa hbb
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have htsq : t ^ 2 = radValue .upper D.X d := by
        dsimp [t]
        exact Real.sq_sqrt hradplus
      have hcert := hTwoVar.upper D.X_floor hprod horder hy0 ht hy0sq htsq
      have hamgm : 2 * t ≤ aa + bb := by
        have hraw := two_sqrt_mul_le_add haa hbb
        rw [hradeq] at hraw
        simpa [t] using hraw
      have hsumlower :
          D.Y * (1 + 1 / d) + aa + bb ≤ D.r + D.s + D.P + D.W := by
        calc
          D.Y * (1 + 1 / d) + aa + bb =
              (D.Y / d + D.X * p / (d * alpha)) + D.s +
                (d * alpha / p) + (d * alpha / (D.X * p)) := by
            dsimp [aa, bb, p]
            field_simp [D.X_pos.ne', hd.ne', halpha.ne', hp.ne']
            ring
          _ ≤ D.r + D.s + D.P + D.W := by
            linarith [hr_lower, hP_lower, hW_product_lower]
      have hGJ : y0 * (1 + 1 / d) + 2 * t ≤
          D.r + D.s + D.P + D.W :=
        calc
          y0 * (1 + 1 / d) + 2 * t ≤
              D.Y * (1 + 1 / d) + (aa + bb) :=
            add_le_add hyterm hamgm
          _ ≤ D.r + D.s + D.P + D.W := by
            linarith [hsumlower]
      exact hcert.trans_le hGJ

  nlinarith [D.product_objective]

end HullSevenType2HyperbolicPacket

end Heilbronn8.TriHull
