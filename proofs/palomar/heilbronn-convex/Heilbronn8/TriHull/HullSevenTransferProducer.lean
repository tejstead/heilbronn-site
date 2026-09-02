import Heilbronn8.TriHull.HullSevenTransferAlgebra

/-!
# Scalar producer for the sharp hull-seven transfer

This file is the recurrence/chord side of `HullSevenBroadTransferData`.  It
does not assume a coordinate box.  The protected C24a/C24b records have the
same chord chamber, so a geometric adapter for either record only has to
construct `HullSevenChordInput` below.

There are genuinely two scalar outcomes.  If the central-ear surrogate
interval meets the central cap, a `HullSevenCappedSurrogate` produces
`HullSevenBroadTransferData`.  If the whole interval lies above the cap, no
such broad-core payload exists; that branch must prove the sharp estimate
directly from `HullSevenAllAboveCapData`.
-/

namespace Heilbronn8.TriHull

noncomputable def hullSevenTransferZ (q t : ℝ) : ℝ :=
  t * (q - 1 - t)

noncomputable def hullSevenTransferI (s u q : ℝ) : Set ℝ :=
  Set.Icc (1 / s) (q - 1 - 1 / u)

noncomputable def hullSevenLeftMax (A B C q : ℝ) : ℝ :=
  (q * (A + B - 1) - A * C) / B

noncomputable def hullSevenRightMax (B C D q : ℝ) : ℝ :=
  (q * (C + D - 1) - D * B) / C

/-- Exact scalar information supplied by the common C24 chord chamber.

The variables are the notation of `risk-review/HULL7_SHARP_TRANSFER.md`.
All recurrence identities are denominator-cleared, which keeps the producer
independent of a particular coordinate or Plücker implementation. -/
structure HullSevenChordInput (H : ℝ) where
  a0 : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  a5 : ℝ
  p : ℝ
  q : ℝ
  r : ℝ
  L : ℝ
  R : ℝ
  c : ℝ
  l : ℝ
  m : ℝ
  G : ℝ
  a0_ge : 1 ≤ a0
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  C_ge : 1 ≤ C
  D_ge : 1 ≤ D
  a5_ge : 1 ≤ a5
  p_ge : 1 ≤ p
  q_ge : 1 ≤ q
  r_ge : 1 ≤ r
  L_ge : 1 ≤ L
  R_ge : 1 ≤ R
  c_ge : 1 ≤ c
  l_ge : 1 ≤ l
  m_ge : 1 ≤ m
  G_ge : 1 ≤ G
  p_ear : p ≤ A + B - 1
  q_ear : q ≤ B + C - 1
  r_ear : r ≤ C + D - 1
  L_rec : B * L = q * p - A * C
  R_rec : C * R = q * r - D * B
  LR_rec : L * R = A * D - c * q
  left_endpoint : A * l + a0 * q ≤ L * (a0 + A - 1)
  right_endpoint : D * m + a5 * q ≤ R * (a5 + D - 1)
  closing_rec :
    G * (L * R) =
      c * l * m + A * a5 * l + D * a0 * m + a0 * a5 * q
  area : a0 + A + B + C + D + a5 + G ≤ H

private lemma hullSeven_endpoint_ear_preserved
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
    · exact (sub_pos.mp hpos.2)
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

private lemma hullSeven_endpoint_parameter_strict
    {A B C q L : ℝ}
    (hA : 1 ≤ A) (hB : 0 < B) (hC : 1 ≤ C)
    (hupper : B * L ≤ q * (A + B - 1) - A * C)
    (hear : 0 ≤ (L - q) + L * (A - 1) - A) :
    1 < A := by
  by_contra hnot
  have hAeq : A = 1 := le_antisymm (le_of_not_gt hnot) hA
  subst A
  have hL : q + 1 ≤ L := by nlinarith [hear]
  have hmul := mul_le_mul_of_nonneg_left hL hB.le
  nlinarith [hupper, hmul, hC]

private lemma hullSeven_endpoint_lower
    {A q L : ℝ} (hA : 0 < A)
    (hear : 0 ≤ (L - q) + L * (A - 1) - A) :
    1 + q / A ≤ L := by
  have hdiv : q / A ≤ L - 1 := by
    apply (div_le_iff₀ hA).2
    nlinarith [hear]
  linarith

private lemma hullSeven_endpoint_twoStep_floor
    {A B C q L : ℝ}
    (hA : 1 ≤ A) (hB : 0 < B) (hC : 1 ≤ C) (hq : 0 < q)
    (hL : 0 < L) (hqEar : q ≤ B + C - 1)
    (hupper : B * L ≤ q * (A + B - 1) - A * C) :
    1 ≤ (A + q) / L := by
  have hBC : 0 < B + C - q := by linarith
  have hmargin : 0 < A * (B + C - q) + q := by positivity
  have hstrict :
      q * (A + B - 1) - A * C < B * (A + q) := by
    nlinarith [hmargin]
  have hBL : B * L < B * (A + q) := lt_of_le_of_lt hupper hstrict
  have hLA : L < A + q := by
    by_contra hnot
    have hrev : A + q ≤ L := le_of_not_gt hnot
    have hm : B * (A + q) ≤ B * L :=
      mul_le_mul_of_nonneg_left hrev hB.le
    exact (not_lt_of_ge hm) hBL
  apply (le_div_iff₀ hL).2
  nlinarith

private lemma hullSeven_endpoint_ear_floor
    {A q L : ℝ} (hL : 0 < L)
    (hear : 0 ≤ (L - q) + L * (A - 1) - A) :
    (A + q) / L ≤ A := by
  apply (div_le_iff₀ hL).2
  nlinarith [hear]

lemma hullSeven_left_recurrence_upper {H : ℝ}
    (X : HullSevenChordInput H) :
    X.B * X.L ≤ X.q * (X.A + X.B - 1) - X.A * X.C := by
  rw [X.L_rec]
  have hm := mul_le_mul_of_nonneg_left X.p_ear
    (le_trans (by norm_num) X.q_ge)
  linarith

lemma hullSeven_right_recurrence_upper {H : ℝ}
    (X : HullSevenChordInput H) :
    X.C * X.R ≤ X.q * (X.D + X.C - 1) - X.D * X.B := by
  rw [X.R_rec]
  have hm := mul_le_mul_of_nonneg_left X.r_ear
    (le_trans (by norm_num) X.q_ge)
  linarith

/-- Lowering the left long chord and endpoint fan to one preserves both the
two-step floor and the endpoint-ear floor. -/
lemma hullSeven_left_endpoint_preserved {H : ℝ}
    (X : HullSevenChordInput H) :
    1 < X.A ∧
      1 + X.q / X.A ≤ X.L ∧
      1 ≤ (X.A + X.q) / X.L ∧
      (X.A + X.q) / X.L ≤ X.A ∧
      X.L ≤ hullSevenLeftMax X.A X.B X.C X.q := by
  have hA0 : 0 < X.A := lt_of_lt_of_le (by norm_num) X.A_ge
  have hB0 : 0 < X.B := lt_of_lt_of_le (by norm_num) X.B_ge
  have hL0 : 0 < X.L := lt_of_lt_of_le (by norm_num) X.L_ge
  have hupper := hullSeven_left_recurrence_upper X
  have hAl : X.A ≤ X.A * X.l := by
    have hm := mul_nonneg (le_trans (by norm_num) X.A_ge)
      (sub_nonneg.mpr X.l_ge)
    nlinarith
  have horiginal : X.A + X.a0 * X.q ≤
      X.L * (X.a0 + X.A - 1) := le_trans (by linarith) X.left_endpoint
  have hear := hullSeven_endpoint_ear_preserved X.a0_ge X.A_ge hB0
    X.C_ge (lt_of_lt_of_le (by norm_num) X.q_ge) hupper horiginal
  have hAstr := hullSeven_endpoint_parameter_strict X.A_ge hB0 X.C_ge
    hupper hear
  have hlower := hullSeven_endpoint_lower hA0 hear
  have htwo := hullSeven_endpoint_twoStep_floor X.A_ge hB0 X.C_ge
    (lt_of_lt_of_le (by norm_num) X.q_ge) hL0 X.q_ear hupper
  have hearFloor := hullSeven_endpoint_ear_floor hL0 hear
  have hmax : X.L ≤ hullSevenLeftMax X.A X.B X.C X.q := by
    unfold hullSevenLeftMax
    apply (le_div_iff₀ hB0).2
    nlinarith [hupper]
  exact ⟨hAstr, hlower, htwo, hearFloor, hmax⟩

/-- Right-hand reflection of `hullSeven_left_endpoint_preserved`. -/
lemma hullSeven_right_endpoint_preserved {H : ℝ}
    (X : HullSevenChordInput H) :
    1 < X.D ∧
      1 + X.q / X.D ≤ X.R ∧
      1 ≤ (X.D + X.q) / X.R ∧
      (X.D + X.q) / X.R ≤ X.D ∧
      X.R ≤ hullSevenRightMax X.B X.C X.D X.q := by
  have hD0 : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
  have hC0 : 0 < X.C := lt_of_lt_of_le (by norm_num) X.C_ge
  have hR0 : 0 < X.R := lt_of_lt_of_le (by norm_num) X.R_ge
  have hupper := hullSeven_right_recurrence_upper X
  have hDm : X.D ≤ X.D * X.m := by
    have hm := mul_nonneg (le_trans (by norm_num) X.D_ge)
      (sub_nonneg.mpr X.m_ge)
    nlinarith
  have horiginal : X.D + X.a5 * X.q ≤
      X.R * (X.a5 + X.D - 1) := le_trans (by linarith) X.right_endpoint
  have hear := hullSeven_endpoint_ear_preserved X.a5_ge X.D_ge hC0
    X.B_ge (lt_of_lt_of_le (by norm_num) X.q_ge) hupper horiginal
  have hDstr := hullSeven_endpoint_parameter_strict X.D_ge hC0 X.B_ge
    hupper hear
  have hlower := hullSeven_endpoint_lower hD0 hear
  have htwo := hullSeven_endpoint_twoStep_floor X.D_ge hC0 X.B_ge
    (lt_of_lt_of_le (by norm_num) X.q_ge) hR0
    (by linarith [X.q_ear]) hupper
  have hearFloor := hullSeven_endpoint_ear_floor hR0 hear
  have hmax : X.R ≤ hullSevenRightMax X.B X.C X.D X.q := by
    unfold hullSevenRightMax
    apply (le_div_iff₀ hC0).2
    nlinarith [hupper]
  exact ⟨hDstr, hlower, htwo, hearFloor, hmax⟩

/-- The original closing cell dominates the endpoint-tightened rational
closing expression. -/
lemma hullSeven_original_closing_lower {H : ℝ}
    (X : HullSevenChordInput H) :
    (X.c + X.A + X.D + X.q) / (X.L * X.R) ≤ X.G := by
  have hL0 : 0 < X.L := lt_of_lt_of_le (by norm_num) X.L_ge
  have hR0 : 0 < X.R := lt_of_lt_of_le (by norm_num) X.R_ge
  have hLR : 0 < X.L * X.R := mul_pos hL0 hR0
  have hc0 : 0 ≤ X.c := le_trans (by norm_num) X.c_ge
  have hA0 : 0 ≤ X.A := le_trans (by norm_num) X.A_ge
  have hD0 : 0 ≤ X.D := le_trans (by norm_num) X.D_ge
  have hq0 : 0 ≤ X.q := le_trans (by norm_num) X.q_ge
  have hcl : X.c ≤ X.c * X.l := by
    have hm := mul_le_mul_of_nonneg_left X.l_ge hc0
    simpa using hm
  have hcl0 : 0 ≤ X.c * X.l :=
    mul_nonneg hc0 (le_trans (by norm_num) X.l_ge)
  have hclm : X.c ≤ X.c * X.l * X.m :=
    le_trans hcl (by
      have hm := mul_le_mul_of_nonneg_left X.m_ge hcl0
      simpa using hm)
  have hAa5 : X.A ≤ X.A * X.a5 := by
    have hm := mul_le_mul_of_nonneg_left X.a5_ge hA0
    simpa using hm
  have hAa50 : 0 ≤ X.A * X.a5 :=
    mul_nonneg hA0 (le_trans (by norm_num) X.a5_ge)
  have hAa5l : X.A ≤ X.A * X.a5 * X.l :=
    le_trans hAa5 (by
      have hm := mul_le_mul_of_nonneg_left X.l_ge hAa50
      simpa using hm)
  have hDa0 : X.D ≤ X.D * X.a0 := by
    have hm := mul_le_mul_of_nonneg_left X.a0_ge hD0
    simpa using hm
  have hDa00 : 0 ≤ X.D * X.a0 :=
    mul_nonneg hD0 (le_trans (by norm_num) X.a0_ge)
  have hDa0m : X.D ≤ X.D * X.a0 * X.m :=
    le_trans hDa0 (by
      have hm := mul_le_mul_of_nonneg_left X.m_ge hDa00
      simpa using hm)
  have ha0a5 : 1 ≤ X.a0 * X.a5 := by
    have ha0nonneg : 0 ≤ X.a0 :=
      le_trans (by norm_num) X.a0_ge
    have ha0_le : X.a0 ≤ X.a0 * X.a5 := by
      have hm := mul_le_mul_of_nonneg_left X.a5_ge ha0nonneg
      simpa using hm
    exact le_trans X.a0_ge ha0_le
  have hq : X.q ≤ X.a0 * X.a5 * X.q := by
    have hm := mul_le_mul_of_nonneg_right ha0a5 hq0
    simpa [mul_assoc] using hm
  apply (div_le_iff₀ hLR).2
  rw [X.closing_rec]
  linarith

/-- Area comparison after selecting a positive central-ear surrogate. -/
lemma hullSeven_selected_surrogate_area {H t w : ℝ}
    (X : HullSevenChordInput H) (hsum : t + w = X.q - 1)
    (hclosing : 1 / (t * w) ≤ X.G) :
    6 + (X.A - 1) + t + w + (X.D - 1) + 1 / (t * w) ≤ H := by
  linarith [X.a0_ge, X.a5_ge, X.q_ear, X.area]

/-- A selected cap-meeting surrogate.  Its three inequalities are exactly
what the broad-core data constructor consumes. -/
structure HullSevenCappedSurrogate {H : ℝ} (X : HullSevenChordInput H) where
  t : ℝ
  w : ℝ
  t_pos : 0 < t
  w_pos : 0 < w
  sum_eq : t + w = X.q - 1
  left_outer : 1 ≤ (X.A - 1) * t
  right_outer : 1 ≤ (X.D - 1) * w
  product_lower :
    X.L * X.R ≤ hullSevenSurrogateP X.A X.D X.q (t * w)
  product_upper :
    hullSevenSurrogateP X.A X.D X.q (t * w) ≤ X.A * X.D - X.q

lemma hullSeven_surrogate_closing_le {H : ℝ}
    (X : HullSevenChordInput H) {z : ℝ} (hz : 0 < z)
    (hP : X.L * X.R ≤ hullSevenSurrogateP X.A X.D X.q z) :
    1 / z ≤ X.G := by
  let P := hullSevenSurrogateP X.A X.D X.q z
  have hA : 0 < X.A := lt_of_lt_of_le (by norm_num) X.A_ge
  have hD : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
  have hq : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hL0 : 0 < X.L := lt_of_lt_of_le (by norm_num) X.L_ge
  have hR0 : 0 < X.R := lt_of_lt_of_le (by norm_num) X.R_ge
  have hLR : 0 < X.L * X.R := mul_pos hL0 hR0
  have hPpos : 0 < P := by
    dsimp [P]
    unfold hullSevenSurrogateP
    positivity
  have hmono :
      ((X.A * X.D - P) / X.q + X.A + X.D + X.q) / P ≤
        ((X.A * X.D - X.L * X.R) / X.q + X.A + X.D + X.q) /
          (X.L * X.R) := by
    apply (div_le_div_iff₀ hPpos hLR).2
    have hK : 0 ≤ (X.A + X.q) * (X.D + X.q) := by positivity
    have hm := mul_nonneg (sub_nonneg.mpr (by simpa [P] using hP)) hK
    field_simp [hq.ne'] <;> nlinarith [hm]
  have hcEq : X.c = (X.A * X.D - X.L * X.R) / X.q := by
    apply (eq_div_iff hq.ne').2
    nlinarith [X.LR_rec]
  have hclose := hullSeven_original_closing_lower X
  rw [hcEq] at hclose
  have hvalue := hullSevenSurrogate_closing hA hD hq hz
  dsimp [P] at hvalue hmono
  rw [hvalue] at hmono
  exact le_trans hmono hclose

/-- Construct the already-green broad transfer payload from a selected
surrogate. -/
noncomputable def hullSevenBroadTransferData_of_cappedSurrogate
    {H : ℝ} (X : HullSevenChordInput H)
    (S : HullSevenCappedSurrogate X) : HullSevenBroadTransferData H := by
  have hs : 0 < X.A - 1 := sub_pos.mpr (hullSeven_left_endpoint_preserved X).1
  have hu : 0 < X.D - 1 := sub_pos.mpr (hullSeven_right_endpoint_preserved X).1
  have hq : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hz : 0 < S.t * S.w := mul_pos S.t_pos S.w_pos
  have hclose := hullSeven_surrogate_closing_le X hz S.product_lower
  have hfloor :
      1 ≤ ((X.A * X.D -
        hullSevenSurrogateP X.A X.D (S.t + S.w + 1) (S.t * S.w)) /
          (S.t + S.w + 1)) := by
    have hqEq : S.t + S.w + 1 = X.q := by linarith [S.sum_eq]
    rw [hqEq]
    apply (le_div_iff₀ hq).2
    linarith [S.product_upper]
  have harea := hullSeven_selected_surrogate_area X S.sum_eq hclose
  exact hullSevenBroadTransferData_of_surrogate
    (s := X.A - 1) (t := S.t) (w := S.w) (u := X.D - 1)
    hs S.t_pos S.w_pos hu S.left_outer S.right_outer
    (by simpa only [sub_add_cancel] using hfloor) harea

theorem hullSeven_v8_of_cappedSurrogate {H : ℝ}
    (X : HullSevenChordInput H) (S : HullSevenCappedSurrogate X) :
    1 ≤ v8 * H :=
  hullSeven_v8_of_broad_transfer
    (hullSevenBroadTransferData_of_cappedSurrogate X S)

/-! ## The genuinely separate all-above-cap outcome -/

/-- Recurrence-free scalar facts left after the whole surrogate interval is
strictly above the central cap. -/
structure HullSevenAllAboveCapData (H : ℝ) where
  s : ℝ
  u : ℝ
  q : ℝ
  rho : ℝ
  s_pos : 0 < s
  u_pos : 0 < u
  rho_pos : 0 < rho
  radial_q : 1 + 2 * rho ≤ q
  radial_q_strict : 1 + 2 * rho < q
  interval : 1 / s + 1 / u ≤ q - 1
  cap_identity :
    (s + 1 - rho ^ 2) * (u + 1 - rho ^ 2) =
      (1 + rho ^ 2) * (q + rho ^ 2)
  area : 5 + q + s + u + 1 / rho ^ 2 ≤ H

/-- Exact scalar statement still needed in the all-above-cap outcome.  It is
deliberately recurrence-free; its proof is the audited `rho/x/j` argument.
Keeping this as the only explicit premise prevents any hidden coordinate-box
or geometric assumption from entering the producer. -/
def HullSevenAllAboveCapClosure : Prop :=
  ∀ {H : ℝ}, HullSevenAllAboveCapData H → 1 ≤ v8 * H

/-- Exact remaining scalar selector.  Its cap-meeting branch is obtained by
the high-point/IVT argument; its other branch is obtained by evaluating the
strict all-above-cap hypothesis at both endpoints.  The only genuinely
geometric premise upstream of this selector is construction of
`HullSevenChordInput H` from the C24 chord signs and Plücker recurrence. -/
def HullSevenChordSelection {H : ℝ} (X : HullSevenChordInput H) : Prop :=
  Nonempty (HullSevenCappedSurrogate X) ∨
    Nonempty (HullSevenAllAboveCapData H)

private theorem hullSeven_v8_of_nonempty_cappedSurrogate {H : ℝ}
    (X : HullSevenChordInput H)
    (hS : Nonempty (HullSevenCappedSurrogate X)) :
    1 ≤ v8 * H := by
  have hout : Nonempty (1 ≤ v8 * H) :=
    Nonempty.map (hullSeven_v8_of_cappedSurrogate X) hS
  exact Classical.choice hout

private theorem hullSeven_v8_of_nonempty_allAbove {H : ℝ}
    (closeAbove : HullSevenAllAboveCapClosure)
    (hdata : Nonempty (HullSevenAllAboveCapData H)) :
    1 ≤ v8 * H := by
  have hout : Nonempty (1 ≤ v8 * H) :=
    Nonempty.map (fun data => closeAbove data) hdata
  exact Classical.choice hout

/-- Sound two-outcome wrapper.  A cap-meeting selector produces broad-core
data; the strict all-above branch is discharged only by the reduced scalar
closure above. -/
theorem hullSeven_v8_of_chord_input_split {H : ℝ}
    (X : HullSevenChordInput H)
    (select : HullSevenChordSelection X)
    (closeAbove : HullSevenAllAboveCapClosure) :
    1 ≤ v8 * H := by
  change Nonempty (HullSevenCappedSurrogate X) ∨
    Nonempty (HullSevenAllAboveCapData H) at select
  rcases select with hS | habove
  · exact hullSeven_v8_of_nonempty_cappedSurrogate X hS
  · exact hullSeven_v8_of_nonempty_allAbove closeAbove habove

end Heilbronn8.TriHull
