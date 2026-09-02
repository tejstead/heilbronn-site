import Heilbronn8.TriHull.HullSevenType2ScalarCore

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

noncomputable section

/-! ## The reflection-GM seam -/

/-- Exact scalar information consumed by the type-2 closer.

The first four inequalities are the reflection-GM forms of cyclic Pluecker
rows.  `secondEar` is the paired second-ear product.  `firstEarWeighted` is
the first paired-ear product after
`2*sqrt(P*Q) <= (3/2)*P + (2/3)*Q`; this is the only weighted relaxation in
the proof. -/
structure HullSevenType2ScalarData (H : ℝ) where
  X : ℝ
  Y : ℝ
  Z : ℝ
  W : ℝ
  r : ℝ
  s : ℝ
  U : ℝ
  Q : ℝ
  R : ℝ
  M : ℝ
  A : ℝ
  B : ℝ
  X_floor : 1 ≤ X
  Y_floor : 1 ≤ Y
  Z_floor : 1 ≤ Z
  W_floor : 1 ≤ W
  r_floor : 1 ≤ r
  s_floor : 1 ≤ s
  U_floor : 1 ≤ U
  Q_floor : 1 ≤ Q
  R_floor : 1 ≤ R
  M_floor : 1 ≤ M
  A_floor : X ≤ A
  B_floor : Y ≤ B
  rs : X * Z + Y * U ≤ r * s
  s_sq : s ^ 2 = Y ^ 2 + Z * Q
  UQ : X * Y + M * s ≤ U * Q
  ZW : R * (U + r) ≤ Z * W
  Q_cap : Q ≤ X ^ 2 - 1
  area : 2 * A + 2 * B + Z + 2 * W ≤ H
  firstEarSum : r + 1 ≤ A + B
  secondEar : s ^ 2 ≤ Y ^ 2 + 2 * B * (Z - 1) + (Z - 1) ^ 2
  firstEarWeighted :
    r ^ 2 ≤ (A + B - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
      (B ^ 2 - Y ^ 2) / 3

namespace HullSevenType2ScalarData

/-- The first two reflection rows collapse to the long-chord lower bound. -/
lemma rQ {H : ℝ} (h : HullSevenType2ScalarData H) :
    h.X * h.s + h.Y ≤ h.r * h.Q := by
  have hQ0 : 0 ≤ h.Q := le_trans (by norm_num) h.Q_floor
  have hs0 : 0 ≤ h.s := le_trans (by norm_num) h.s_floor
  have hspos : 0 < h.s := lt_of_lt_of_le (by norm_num) h.s_floor
  have hY0 : 0 ≤ h.Y := le_trans (by norm_num) h.Y_floor
  have hMs : h.s ≤ h.M * h.s := by
    have hp := mul_nonneg (sub_nonneg.mpr h.M_floor) hs0
    nlinarith only [hp]
  have hUQ' : h.X * h.Y + h.s ≤ h.U * h.Q := by
    calc
      h.X * h.Y + h.s ≤ h.X * h.Y + h.M * h.s :=
        add_le_add_right hMs _
      _ ≤ h.U * h.Q := h.UQ
  have hYUQ := mul_le_mul_of_nonneg_left hUQ' hY0
  have hrsQ := mul_le_mul_of_nonneg_left h.rs hQ0
  have hmul : h.s * (h.X * h.s + h.Y) ≤ h.s * (h.r * h.Q) := by
    calc
      h.s * (h.X * h.s + h.Y) =
          h.X * (h.s ^ 2 - h.Y ^ 2) +
            h.Y * (h.X * h.Y + h.s) := by ring
      _ = h.X * (h.Z * h.Q) + h.Y * (h.X * h.Y + h.s) := by
        rw [h.s_sq]
        ring
      _ ≤ h.X * (h.Z * h.Q) + h.Y * (h.U * h.Q) :=
        by
          simpa [add_comm] using
            add_le_add_right hYUQ (h.X * (h.Z * h.Q))
      _ = h.Q * (h.X * h.Z + h.Y * h.U) := by ring
      _ ≤ h.Q * (h.r * h.s) := hrsQ
      _ = h.s * (h.r * h.Q) := by ring
  exact le_of_mul_le_mul_left hmul hspos

/-- The remaining two reflection rows turn the long-chord bound into the
boundary-cell bound used by both branches of the closer. -/
lemma pW {H : ℝ} (h : HullSevenType2ScalarData H) :
    h.X + 1 ≤ h.W * (h.s - h.Y) := by
  have hQ0 : 0 ≤ h.Q := le_trans (by norm_num) h.Q_floor
  have hs0 : 0 ≤ h.s := le_trans (by norm_num) h.s_floor
  have hMs : h.s ≤ h.M * h.s := by
    have hp := mul_nonneg (sub_nonneg.mpr h.M_floor) hs0
    nlinarith only [hp]
  have hUQ' : h.X * h.Y + h.s ≤ h.U * h.Q := by
    calc
      h.X * h.Y + h.s ≤ h.X * h.Y + h.M * h.s :=
        add_le_add_right hMs _
      _ ≤ h.U * h.Q := h.UQ
  have hsum : (h.X + 1) * (h.s + h.Y) ≤ h.Q * (h.U + h.r) := by
    calc
      (h.X + 1) * (h.s + h.Y) =
          (h.X * h.Y + h.s) + (h.X * h.s + h.Y) := by ring
      _ ≤ h.U * h.Q + h.r * h.Q := add_le_add hUQ' h.rQ
      _ = h.Q * (h.U + h.r) := by ring
  have hU0 : 0 ≤ h.U := le_trans (by norm_num) h.U_floor
  have hr0 : 0 ≤ h.r := le_trans (by norm_num) h.r_floor
  have hQsum0 : 0 ≤ h.Q * (h.U + h.r) :=
    mul_nonneg hQ0 (add_nonneg hU0 hr0)
  have hRmul : h.Q * (h.U + h.r) ≤ h.R * (h.Q * (h.U + h.r)) := by
    simpa using mul_le_mul_of_nonneg_right h.R_floor hQsum0
  have hZWQ := mul_le_mul_of_nonneg_right h.ZW hQ0
  have hZQ : h.Z * h.Q = h.s ^ 2 - h.Y ^ 2 := by
    nlinarith only [h.s_sq]
  have hbig : (h.X + 1) * (h.s + h.Y) ≤
      (h.W * (h.s - h.Y)) * (h.s + h.Y) := by
    calc
      (h.X + 1) * (h.s + h.Y) ≤ h.Q * (h.U + h.r) := hsum
      _ ≤ h.R * (h.Q * (h.U + h.r)) := hRmul
      _ = h.Q * (h.R * (h.U + h.r)) := by ring
      _ ≤ h.Q * (h.Z * h.W) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hZWQ
      _ = h.W * (h.Z * h.Q) := by ring
      _ = h.W * (h.s ^ 2 - h.Y ^ 2) := by rw [hZQ]
      _ = (h.W * (h.s - h.Y)) * (h.s + h.Y) := by ring
  have hspos : 0 < h.s := lt_of_lt_of_le (by norm_num) h.s_floor
  have hYpos : 0 < h.Y := lt_of_lt_of_le (by norm_num) h.Y_floor
  have hsy : 0 < h.s + h.Y := add_pos hspos hYpos
  exact le_of_mul_le_mul_right hbig hsy

end HullSevenType2ScalarData

/-! ## The scalar closer -/

/-- Every scalar packet satisfying the type-2 reflection rows and the two
paired-ear inequalities has normalized boundary area strictly larger than
`25/2`. -/
theorem hullSevenType2_area_gt {H : ℝ}
    (h : HullSevenType2ScalarData H) : (25 : ℝ) / 2 < H := by
  have hXpos : 0 < h.X := lt_of_lt_of_le (by norm_num) h.X_floor
  have hX1 : 0 < h.X + 1 := by linarith only [hXpos]
  have hYpos : 0 < h.Y := lt_of_lt_of_le (by norm_num) h.Y_floor
  have hspos : 0 < h.s := lt_of_lt_of_le (by norm_num) h.s_floor
  have hQpos : 0 < h.Q := lt_of_lt_of_le (by norm_num) h.Q_floor
  have hZpos : 0 < h.Z := lt_of_lt_of_le (by norm_num) h.Z_floor
  have hrpos : 0 < h.r := lt_of_lt_of_le (by norm_num) h.r_floor
  have hWpos : 0 < h.W := lt_of_lt_of_le (by norm_num) h.W_floor
  have hApos : 0 < h.A := lt_of_lt_of_le hXpos h.A_floor
  have hBpos : 0 < h.B := lt_of_lt_of_le hYpos h.B_floor

  let p : ℝ := h.s - h.Y
  let t : ℝ := h.Z - 1
  let rho : ℝ := p / (h.X + 1)
  let C : ℝ := h.A + h.B

  have hsypos : 0 < h.s + h.Y := by positivity
  have hZQpos : 0 < h.Z * h.Q := mul_pos hZpos hQpos
  have hfactor : (h.s - h.Y) * (h.s + h.Y) = h.Z * h.Q := by
    nlinarith only [h.s_sq]
  have hp : 0 < p := by
    dsimp [p]
    by_contra hn
    have hnonpos : h.s - h.Y ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonpos_of_nonneg hnonpos hsypos.le
    nlinarith only [hm, hfactor, hZQpos]
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith only [h.Z_floor]
  have ht : 0 < t := by
    rcases ht0.eq_or_lt with hzero | hpositive
    · have hZ1 : h.Z = 1 := by
        dsimp [t] at hzero
        linarith only [hzero]
      have hsEq := h.s_sq
      have hEar := h.secondEar
      rw [hZ1] at hsEq hEar
      norm_num at hsEq hEar
      nlinarith only [hsEq, hEar, h.Q_floor]
    · exact hpositive
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hrhop : rho * (h.X + 1) = p := by
    dsimp [rho]
    field_simp [hX1.ne']
  have hQrel : h.Q * (t + 1) = p * (p + 2 * h.Y) := by
    dsimp [p, t]
    nlinarith only [h.s_sq]

  have hpLower : p * (p + 2) ≤ p * (p + 2 * h.Y) := by
    have hm := mul_nonneg hp.le (sub_nonneg.mpr h.Y_floor)
    nlinarith only [hm]
  have ht1 : 0 < t + 1 := by linarith only [ht0]
  have hQcapT := mul_le_mul_of_nonneg_right h.Q_cap ht1.le
  have hcapRaw : p * (p + 2) ≤ (h.X ^ 2 - 1) * (t + 1) := by
    calc
      p * (p + 2) ≤ p * (p + 2 * h.Y) := hpLower
      _ = h.Q * (t + 1) := hQrel.symm
      _ ≤ (h.X ^ 2 - 1) * (t + 1) := hQcapT
  have hcap : rho ^ 2 * (h.X + 1) + 2 * rho ≤
      (h.X - 1) * (t + 1) := by
    have hmul :
        (h.X + 1) * (rho ^ 2 * (h.X + 1) + 2 * rho) ≤
          (h.X + 1) * ((h.X - 1) * (t + 1)) := by
      calc
        (h.X + 1) * (rho ^ 2 * (h.X + 1) + 2 * rho) =
            (rho * (h.X + 1)) * (rho * (h.X + 1) + 2) := by ring
        _ = p * (p + 2) := by rw [hrhop]
        _ ≤ (h.X ^ 2 - 1) * (t + 1) := hcapRaw
        _ = (h.X + 1) * ((h.X - 1) * (t + 1)) := by ring
    exact le_of_mul_le_mul_left hmul hX1
  have hXD : 0 < h.X * hullSevenType2D rho t := by
    unfold hullSevenType2D
    nlinarith only [hcap, ht0, hrho, sq_nonneg rho]
  have hD : 0 < hullSevenType2D rho t := by
    by_contra hn
    have hDn : hullSevenType2D rho t ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hXpos.le hDn
    linarith only [hm, hXD]
  have hXDid : 2 * (t + 1 + rho) ≤
      (h.X + 1) * hullSevenType2D rho t := by
    unfold hullSevenType2D
    nlinarith only [hcap]

  have hrQ := h.rQ
  have hsExpr : h.s = h.Y + rho * (h.X + 1) := by
    calc
      h.s = h.Y + p := by
        dsimp [p]
        ring
      _ = h.Y + rho * (h.X + 1) := by rw [hrhop]
  have hRid :
      2 * rho * (h.X * h.s + h.Y) =
        h.Q * (t + 1) + rho ^ 2 * (h.X ^ 2 - 1) := by
    calc
      2 * rho * (h.X * h.s + h.Y) =
          (rho * (h.X + 1)) *
              (rho * (h.X + 1) + 2 * h.Y) +
            rho ^ 2 * (h.X ^ 2 - 1) := by
        rw [hsExpr]
        ring
      _ = p * (p + 2 * h.Y) + rho ^ 2 * (h.X ^ 2 - 1) := by
        rw [hrhop]
      _ = h.Q * (t + 1) + rho ^ 2 * (h.X ^ 2 - 1) := by
        rw [hQrel]
  have hrQmul := mul_le_mul_of_nonneg_left hrQ
    (by positivity : 0 ≤ 2 * rho)
  have hcapR := mul_le_mul_of_nonneg_left h.Q_cap
    (sq_nonneg rho)
  have hQR : h.Q * (t + 1 + rho ^ 2) ≤
      h.Q * (2 * rho * h.r) := by
    nlinarith only [hrQmul, hRid, hcapR]
  have h2r : t + 1 + rho ^ 2 ≤ 2 * rho * h.r :=
    le_of_mul_le_mul_left hQR hQpos
  have hR0id :
      (2 * rho) * hullSevenType2R0 rho t = t + 1 + rho ^ 2 := by
    unfold hullSevenType2R0
    field_simp [hrho.ne']
    <;> ring
  have hR0 : hullSevenType2R0 rho t ≤ h.r := by
    have hm : (2 * rho) * hullSevenType2R0 rho t ≤
        (2 * rho) * h.r := by nlinarith only [hR0id, h2r]
    have h2rho : 0 < 2 * rho := mul_pos (by norm_num) hrho
    exact le_of_mul_le_mul_left hm h2rho

  have hpW := h.pW
  have hpW' : h.X + 1 ≤ h.W * (rho * (h.X + 1)) := by
    rw [hrhop]
    exact hpW
  have hrhoW : 1 ≤ rho * h.W := by
    have hm : (h.X + 1) * 1 ≤ (h.X + 1) * (rho * h.W) := by
      calc
        (h.X + 1) * 1 = h.X + 1 := by ring
        _ ≤ h.W * (rho * (h.X + 1)) := hpW'
        _ = (h.X + 1) * (rho * h.W) := by ring
    exact le_of_mul_le_mul_left hm hX1
  have hWinv : 1 / rho ≤ h.W := by
    apply (div_le_iff₀ hrho).2
    simpa [mul_comm] using hrhoW

  have hAreaC : 2 * C + t + 1 + 2 * h.W ≤ H := by
    dsimp [C, t]
    linarith only [h.area]
  have hCsum : h.r + 1 ≤ C := by
    simpa [C] using h.firstEarSum
  by_contra hnot
  have hH : H ≤ (25 : ℝ) / 2 := le_of_not_gt hnot
  have hAreaInv : 2 * C + t + 1 + 2 * (1 / rho) ≤ (25 : ℝ) / 2 := by
    linarith only [hAreaC, hWinv, hH]
  have hC0 : C ≤ hullSevenType2C0 rho t := by
    unfold hullSevenType2C0
    linarith only [hAreaInv]

  rcases le_total p t with hpt | htp
  · -- The short-gap branch is closed by one cubic sum of squares.
    have hscaled :
        2 * rho * (t + 1 + rho) ≤
          p * hullSevenType2D rho t := by
      calc
        2 * rho * (t + 1 + rho) ≤
            rho * ((h.X + 1) * hullSevenType2D rho t) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_le_mul_of_nonneg_left hXDid hrho.le)
        _ = p * hullSevenType2D rho t := by
          rw [← mul_assoc, hrhop]
    have hpD := mul_le_mul_of_nonneg_right hpt hD.le
    have htineq :
        2 * rho * (t + 1 + rho) ≤
          t * hullSevenType2D rho t := le_trans hscaled hpD
    have htstrong : rho ^ 2 + 2 * rho < t := by
      by_contra hn
      have hta : t ≤ rho ^ 2 + 2 * rho := le_of_not_gt hn
      have hprod :
          (t - (rho ^ 2 + 2 * rho)) * (t + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith only [hta]) ht1.le
      have hr2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
      unfold hullSevenType2D at htineq
      nlinarith only [htineq, hprod, hr2]
    have hHbase :
        2 * hullSevenType2R0 rho t + t + 3 + 2 / rho ≤ H := by
      have hRC : hullSevenType2R0 rho t + 1 ≤ C :=
        (add_le_add_left hR0 1).trans hCsum
      have hRC2 : 2 * (hullSevenType2R0 rho t + 1) ≤ 2 * C :=
        mul_le_mul_of_nonneg_left hRC (by norm_num)
      have hWinv2 : 2 * (1 / rho) ≤ 2 * h.W :=
        mul_le_mul_of_nonneg_left hWinv (by norm_num)
      have hbaseArea :
          2 * hullSevenType2R0 rho t + t + 3 + 2 / rho ≤
            2 * C + t + 1 + 2 * h.W := by
        calc
          2 * hullSevenType2R0 rho t + t + 3 + 2 / rho =
              2 * (hullSevenType2R0 rho t + 1) + (t + 1) +
                2 * (1 / rho) := by ring
          _ ≤ 2 * C + (t + 1) + 2 * h.W :=
            add_le_add (add_le_add hRC2 (le_refl (t + 1))) hWinv2
          _ = 2 * C + t + 1 + 2 * h.W := by ring
      exact hbaseArea.trans hAreaC
    have hbaseId :
        2 * hullSevenType2R0 rho t + t + 3 + 2 / rho =
          3 + t + (t + 3) / rho + rho := by
      unfold hullSevenType2R0
      field_simp [hrho.ne']
      <;> ring
    rw [hbaseId] at hHbase
    have hinc :
        5 + rho ^ 2 + 4 * rho + 3 / rho <
          3 + t + (t + 3) / rho + rho := by
      have hcoef : 0 < 1 + 1 / rho := by positivity
      have hmul := mul_pos (sub_pos.mpr htstrong) hcoef
      have hid :
          (3 + t + (t + 3) / rho + rho) -
              (5 + rho ^ 2 + 4 * rho + 3 / rho) =
            (t - (rho ^ 2 + 2 * rho)) * (1 + 1 / rho) := by
        field_simp [hrho.ne']
        <;> ring
      nlinarith only [hmul, hid]
    have hsos : 0 <
        2 * rho * (rho - 2 / 3) ^ 2 +
          (32 / 3) * (rho - 143 / 192) ^ 2 + 287 / 3456 := by
      positivity
    have hpoly : 0 < 2 * rho ^ 3 + 8 * rho ^ 2 - 15 * rho + 6 := by
      have hid :
          2 * rho ^ 3 + 8 * rho ^ 2 - 15 * rho + 6 =
            2 * rho * (rho - 2 / 3) ^ 2 +
              (32 / 3) * (rho - 143 / 192) ^ 2 + 287 / 3456 := by
        ring
      rw [hid]
      exact hsos
    have hgap : (25 : ℝ) / 2 <
        5 + rho ^ 2 + 4 * rho + 3 / rho := by
      have hid :
          (2 * rho) *
              ((5 + rho ^ 2 + 4 * rho + 3 / rho) - 25 / 2) =
            2 * rho ^ 3 + 8 * rho ^ 2 - 15 * rho + 6 := by
        field_simp [hrho.ne']
        <;> ring
      have hm : 0 < (2 * rho) *
          ((5 + rho ^ 2 + 4 * rho + 3 / rho) - 25 / 2) := by
        rw [hid]
        exact hpoly
      by_contra hn
      have hdiff :
          (5 + rho ^ 2 + 4 * rho + 3 / rho) - 25 / 2 ≤ 0 := by
        exact sub_nonpos.mpr (le_of_not_gt hn)
      have hnon := mul_nonpos_of_nonneg_of_nonpos
        (by positivity : 0 ≤ 2 * rho) hdiff
      exact (not_lt_of_ge hnon) hm
    have hgt : (25 : ℝ) / 2 < H :=
      lt_of_lt_of_le (lt_trans hgap hinc) hHbase
    exact (not_lt_of_ge hH) hgt
  · -- The long-gap branch reduces to the audited two-variable core.
    let g : ℝ := (p - t) * (t + 1) / t
    have hpt0 : 0 ≤ p - t := sub_nonneg.mpr htp
    have hg0 : 0 ≤ g := by
      dsimp [g]
      positivity
    have hsec : p * (p + 2 * h.Y) ≤ 2 * h.B * t + t ^ 2 := by
      dsimp [p, t]
      nlinarith only [h.secondEar]
    have hraw : (p - t) * (p + t + 2 * h.Y) ≤
        2 * t * (h.B - h.Y) := by
      nlinarith only [hsec]
    have hwide : 2 * (p - t) * (t + 1) ≤
        (p - t) * (p + t + 2 * h.Y) := by
      have hfac : 2 * (t + 1) ≤ p + t + 2 * h.Y := by
        linarith only [htp, h.Y_floor]
      nlinarith only [mul_le_mul_of_nonneg_left hfac hpt0]
    have htg : t * g = (p - t) * (t + 1) := by
      dsimp [g]
      field_simp [ht.ne']
    have hBgap : g ≤ h.B - h.Y := by
      have hm : t * g ≤ t * (h.B - h.Y) := by
        nlinarith only [hwide, hraw, htg]
      exact le_of_mul_le_mul_left hm ht
    have hB1g : 1 + g ≤ h.B := by
      linarith only [hBgap, h.Y_floor]

    have hX0 : hullSevenType2X0 rho t ≤ h.X := by
      have hnum : t + 1 + rho ^ 2 + 2 * rho ≤
          h.X * hullSevenType2D rho t := by
        unfold hullSevenType2D
        nlinarith only [hcap]
      unfold hullSevenType2X0
      exact (div_le_iff₀ hD).2 hnum
    have hgid :
        g - hullSevenType2G0 rho t =
          ((t + 1) * rho / t) *
            (h.X - hullSevenType2X0 rho t) := by
      dsimp [g]
      unfold hullSevenType2G0
      rw [← hrhop]
      field_simp [ht.ne']
      <;> ring
    have hk : 0 ≤ (t + 1) * rho / t := by positivity
    have hG0g : hullSevenType2G0 rho t ≤ g := by
      have hm := mul_nonneg hk (sub_nonneg.mpr hX0)
      nlinarith only [hm, hgid]
    have hAup : h.A ≤ C - 1 - g := by
      dsimp [C]
      linarith only [hB1g]
    have hCmin :
        hullSevenType2X0 rho t + 1 + hullSevenType2G0 rho t ≤ C := by
      dsimp [C]
      linarith only [h.A_floor, hB1g, hX0, hG0g]
    have heps : 0 ≤ hullSevenType2Eps rho t := by
      unfold hullSevenType2Eps
      linarith only [hR0, hCsum, hC0]
    have hu0 : 0 ≤ hullSevenType2U0 rho t := by
      unfold hullSevenType2U0
      linarith only [hCmin, hC0]
    have hcore := hullSevenType2_rho_core rho t hrho ht hD heps hu0

    have hR0pos : 0 < hullSevenType2R0 rho t := by
      unfold hullSevenType2R0
      positivity
    have hR0sq : (hullSevenType2R0 rho t) ^ 2 ≤ h.r ^ 2 := by
      have hm := mul_nonneg (sub_nonneg.mpr hR0)
        (by positivity : 0 ≤ h.r + hullSevenType2R0 rho t)
      nlinarith only [hm]
    have hBsq : 2 * g ≤ h.B ^ 2 - h.Y ^ 2 := by
      have h1 := mul_nonneg
        (by linarith only [hBgap] : 0 ≤ h.B - h.Y - g)
        (by positivity : 0 ≤ h.B + h.Y)
      have h2 := mul_nonneg hg0
        (by linarith only [h.B_floor, h.Y_floor] : 0 ≤ h.B + h.Y - 2)
      nlinarith only [h1, h2]
    have hAupPos : 0 < C - 1 - g := lt_of_lt_of_le hApos hAup
    have hAsq : h.A ^ 2 ≤ (C - 1 - g) ^ 2 := by
      have hm := mul_nonneg (sub_nonneg.mpr hAup)
        (by linarith only [hAupPos, hApos] :
          0 ≤ (C - 1 - g) + h.A)
      nlinarith only [hm]
    let F : ℝ :=
      (C - 1) ^ 2 + ((C - 1 - g) ^ 2 - h.X ^ 2) / 2 - 2 * g / 3
    have hrF : h.r ^ 2 ≤ F := by
      dsimp [F]
      nlinarith only [h.firstEarWeighted, hAsq, hBsq]
    have hR0F : (hullSevenType2R0 rho t) ^ 2 ≤ F :=
      le_trans hR0sq hrF

    let FC : ℝ :=
      (hullSevenType2C0 rho t - 1) ^ 2 +
        ((hullSevenType2C0 rho t - 1 - g) ^ 2 - h.X ^ 2) / 2 -
        2 * g / 3
    have hCpos : 0 < C - 1 := by
      dsimp [C]
      linarith only [h.A_floor, h.B_floor, h.X_floor, h.Y_floor]
    have hC0pos : 0 < hullSevenType2C0 rho t - 1 :=
      lt_of_lt_of_le hCpos (by linarith only [hC0])
    have hs1 : (C - 1) ^ 2 ≤
        (hullSevenType2C0 rho t - 1) ^ 2 := by
      have hm := mul_nonneg
        (sub_nonneg.mpr (by linarith only [hC0] :
          C - 1 ≤ hullSevenType2C0 rho t - 1))
        (by linarith only [hC0pos, hCpos] :
          0 ≤ (hullSevenType2C0 rho t - 1) + (C - 1))
      nlinarith only [hm]
    have hC0A : 0 < hullSevenType2C0 rho t - 1 - g :=
      lt_of_lt_of_le hAupPos (by linarith only [hC0])
    have hs2 : (C - 1 - g) ^ 2 ≤
        (hullSevenType2C0 rho t - 1 - g) ^ 2 := by
      have hm := mul_nonneg
        (sub_nonneg.mpr (by linarith only [hC0] :
          C - 1 - g ≤ hullSevenType2C0 rho t - 1 - g))
        (by linarith only [hC0A, hAupPos] :
          0 ≤ (hullSevenType2C0 rho t - 1 - g) + (C - 1 - g))
      nlinarith only [hm]
    have hFFC : F ≤ FC := by
      dsimp [F, FC]
      nlinarith only [hs1, hs2]

    have hX0pos : 0 < hullSevenType2X0 rho t := by
      unfold hullSevenType2X0
      exact div_pos (by positivity) hD
    have hXsq : (hullSevenType2X0 rho t) ^ 2 ≤ h.X ^ 2 := by
      have hm := mul_nonneg (sub_nonneg.mpr hX0)
        (by linarith only [hXpos, hX0pos] :
          0 ≤ h.X + hullSevenType2X0 rho t)
      nlinarith only [hm]
    have hGsq :
        (hullSevenType2C0 rho t - 1 - g) ^ 2 ≤
          (hullSevenType2C0 rho t - 1 -
            hullSevenType2G0 rho t) ^ 2 := by
      have hright : 0 <
          hullSevenType2C0 rho t - 1 - hullSevenType2G0 rho t := by
        linarith only [hC0A, hG0g]
      have hm := mul_nonneg
        (sub_nonneg.mpr (by linarith only [hG0g] :
          hullSevenType2C0 rho t - 1 - g ≤
            hullSevenType2C0 rho t - 1 - hullSevenType2G0 rho t))
        (by linarith only [hC0A, hright] : 0 ≤
          (hullSevenType2C0 rho t - 1 - g) +
            (hullSevenType2C0 rho t - 1 - hullSevenType2G0 rho t))
      nlinarith only [hm]
    have hFCF0 : FC ≤ hullSevenType2F0 rho t := by
      dsimp [FC]
      unfold hullSevenType2F0
      nlinarith only [hGsq, hXsq, hG0g]
    have hneed : (hullSevenType2R0 rho t) ^ 2 ≤
        hullSevenType2F0 rho t :=
      le_trans hR0F (le_trans hFFC hFCF0)
    exact (not_lt_of_ge hneed) hcore

end

end Heilbronn8.TriHull
