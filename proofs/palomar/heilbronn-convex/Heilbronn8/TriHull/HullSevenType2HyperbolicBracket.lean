import Mathlib

/-!
# Honest hyperbolic bracket packet for hull-seven type 2

The canonical type-2 key is `100000111001111111111`.  Rotating its direct
presentation by two positions gives the increasing-pair sign chart whose
only negative pairs are `06`, `16`, and `26`.  In cyclic notation this means

* every boundary cell `a i = [i,i+1]` is positive;
* every two-step chord `b i = [i,i+2]` is positive except `b 5 < 0`;
* every three-step chord `u i = [i,i+3]` is positive except `u 4,u 5 < 0`.

This file contains no scalar closer and imports none of the older files whose
`Type2` name belongs to a different chamber.  It records the exact Pluecker
rows and packages their geometric-mean consequences for the honest type-2
chart.  The point-geometry construction is in
`HullSevenType2HyperbolicPointAdapter`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

open scoped BigOperators

abbrev HullSevenType2HyperbolicIndex := ZMod 7

/-- Positive magnitude of a cyclic two-step chord.  Only `b 5` is negative. -/
def hullSevenType2HyperbolicTwoStepMagnitude
    (bracket : HullSevenType2HyperbolicIndex →
      HullSevenType2HyperbolicIndex → ℝ)
    (i : HullSevenType2HyperbolicIndex) : ℝ :=
  if i = 5 then -bracket i (i + 2) else bracket i (i + 2)

/-- Positive magnitude of a cyclic three-step chord.  Exactly `u 4,u 5`
are negative. -/
def hullSevenType2HyperbolicThreeStepMagnitude
    (bracket : HullSevenType2HyperbolicIndex →
      HullSevenType2HyperbolicIndex → ℝ)
    (i : HullSevenType2HyperbolicIndex) : ℝ :=
  if i = 4 ∨ i = 5 then -bracket i (i + 3) else bracket i (i + 3)

/-- Normalized signed brackets in the preferred honest type-2 chart.

The six ear fields are precisely the positive two-step ears.  There is no
ear field for the negative chord `b 5`. -/
structure HullSevenType2HyperbolicBracketData (H : ℝ) where
  bracket : HullSevenType2HyperbolicIndex →
    HullSevenType2HyperbolicIndex → ℝ
  skew : ∀ i j, bracket i j = -bracket j i
  plucker : ∀ i j k l,
    bracket i j * bracket k l - bracket i k * bracket j l +
      bracket i l * bracket j k = 0
  adjacent_ge : ∀ i, 1 ≤ bracket i (i + 1)
  twoStepMagnitude_ge : ∀ i,
    1 ≤ hullSevenType2HyperbolicTwoStepMagnitude bracket i
  threeStepMagnitude_ge : ∀ i,
    1 ≤ hullSevenType2HyperbolicThreeStepMagnitude bracket i
  ear0 : bracket 0 2 ≤ bracket 0 1 + bracket 1 2 - 1
  ear1 : bracket 1 3 ≤ bracket 1 2 + bracket 2 3 - 1
  ear2 : bracket 2 4 ≤ bracket 2 3 + bracket 3 4 - 1
  ear3 : bracket 3 5 ≤ bracket 3 4 + bracket 4 5 - 1
  ear4 : bracket 4 6 ≤ bracket 4 5 + bracket 5 6 - 1
  ear6 : bracket 6 1 ≤ bracket 6 0 + bracket 0 1 - 1
  area : (∑ i, bracket i (i + 1)) ≤ H

/-- The scalar seam exported by the honest type-2 determinant chart.

The two older reflection-GM rows are deliberately replaced by the single
hyperbolic gap row.  The namespace below proves that, under the three exact
square-gap identities, each old row is equivalent to this one inequality. -/
structure HullSevenType2HyperbolicPacket (H : ℝ) where
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
  h : ℝ
  P : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
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
  h_floor : 1 ≤ h
  P_floor : 1 ≤ P
  A_floor : X ≤ A
  B_floor : (Y : ℝ) ≤ B
  C_floor : (W : ℝ) ≤ C
  A_allocation : 2 * A ≤ X ^ 2 + 1
  B_allocation : 2 * B ≤ Y ^ 2 + 1
  C_allocation : 2 * C ≤ W ^ 2 + 1
  M_sq : M ^ 2 - X ^ 2 = h * Q
  s_sq : s ^ 2 - Y ^ 2 = Z * Q
  U_sq : U ^ 2 - r ^ 2 = h * Z
  gap : Q * (U - r) ≤ (M - X) * (s - Y)
  Wd : h * P ≤ W * (M - X)
  We : h * R ≤ W * (U - r)
  Pp : Q * R ≤ P * (s - Y)
  ZW : R * (U + r) ≤ Z * W
  r_ear : r + 1 ≤ A + B
  s_ear : s + 1 ≤ B + Z
  P_ear : P + 1 ≤ A + C
  r_product : r ≤ X * Y
  s_product : s ≤ Y * Z
  P_product : P ≤ X * W
  s_secondEar :
    s ^ 2 ≤ Y ^ 2 + 2 * B * (Z - 1) + (Z - 1) ^ 2
  r_weighted :
    r ^ 2 ≤ (A + B - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
      (B ^ 2 - Y ^ 2) / 3
  P_weighted :
    P ^ 2 ≤ (A + C - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
      (C ^ 2 - W ^ 2) / 3
  area : 2 * A + 2 * B + Z + 2 * C ≤ H

namespace HullSevenType2HyperbolicPacket

variable {H : ℝ} (D : HullSevenType2HyperbolicPacket H)

lemma X_pos : 0 < D.X := lt_of_lt_of_le (by norm_num) D.X_floor
lemma Y_pos : 0 < D.Y := lt_of_lt_of_le (by norm_num) D.Y_floor
lemma Z_pos : 0 < D.Z := lt_of_lt_of_le (by norm_num) D.Z_floor
lemma r_pos : 0 < D.r := lt_of_lt_of_le (by norm_num) D.r_floor
lemma Q_pos : 0 < D.Q := lt_of_lt_of_le (by norm_num) D.Q_floor
lemma h_pos : 0 < D.h := lt_of_lt_of_le (by norm_num) D.h_floor

/-- The first square gap is strict. -/
lemma X_lt_M : D.X < D.M := by
  have hgap : 0 < D.h * D.Q := mul_pos D.h_pos D.Q_pos
  have hsq : D.X ^ 2 < D.M ^ 2 := by nlinarith only [D.M_sq, hgap]
  have hM0 : 0 ≤ D.M := le_trans (by norm_num) D.M_floor
  exact (sq_lt_sq₀ D.X_pos.le hM0).mp hsq

/-- The middle square gap is strict. -/
lemma Y_lt_s : D.Y < D.s := by
  have hgap : 0 < D.Z * D.Q := mul_pos D.Z_pos D.Q_pos
  have hsq : D.Y ^ 2 < D.s ^ 2 := by nlinarith only [D.s_sq, hgap]
  have hs0 : 0 ≤ D.s := le_trans (by norm_num) D.s_floor
  exact (sq_lt_sq₀ D.Y_pos.le hs0).mp hsq

/-- The last square gap is strict. -/
lemma r_lt_U : D.r < D.U := by
  have hgap : 0 < D.h * D.Z := mul_pos D.h_pos D.Z_pos
  have hsq : D.r ^ 2 < D.U ^ 2 := by nlinarith only [D.U_sq, hgap]
  have hU0 : 0 ≤ D.U := le_trans (by norm_num) D.U_floor
  exact (sq_lt_sq₀ D.r_pos.le hU0).mp hsq

/-- Exact factorization of the first traditional reflection-GM row. -/
lemma left_gap_factor :
    2 * (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) *
        (D.r * D.s - D.X * D.Z - D.Y * D.U) =
      D.Z * ((D.M - D.X) * (D.s - D.Y) - D.Q * (D.U - D.r)) *
        (D.h * (D.s - D.Y) + (D.M - D.X) * (D.U - D.r)) := by
  let d := D.M - D.X
  let p := D.s - D.Y
  let e := D.U - D.r
  have h2dX : 2 * d * D.X = D.h * D.Q - d ^ 2 := by
    dsimp [d]
    nlinarith [D.M_sq]
  have h2pY : 2 * p * D.Y = D.Z * D.Q - p ^ 2 := by
    dsimp [p]
    nlinarith [D.s_sq]
  have h2er : 2 * e * D.r = D.h * D.Z - e ^ 2 := by
    dsimp [e]
    nlinarith [D.U_sq]
  change 2 * d * e * p *
      (D.r * D.s - D.X * D.Z - D.Y * D.U) =
    D.Z * (d * p - D.Q * e) * (D.h * p + d * e)
  calc
    2 * d * e * p *
        (D.r * D.s - D.X * D.Z - D.Y * D.U) =
      d * p ^ 2 * (2 * e * D.r) -
        d * e ^ 2 * (2 * p * D.Y) -
        e * p * D.Z * (2 * d * D.X) := by
          dsimp [d, p, e]
          ring
    _ = d * p ^ 2 * (D.h * D.Z - e ^ 2) -
        d * e ^ 2 * (D.Z * D.Q - p ^ 2) -
        e * p * D.Z * (D.h * D.Q - d ^ 2) := by
          rw [h2er, h2pY, h2dX]
    _ = D.Z * (d * p - D.Q * e) * (D.h * p + d * e) := by ring

/-- Exact factorization of the second traditional reflection-GM row. -/
lemma right_gap_factor :
    2 * (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) *
        (D.U * D.Q - D.X * D.Y - D.M * D.s) =
      ((D.M - D.X) * (D.s - D.Y) - D.Q * (D.U - D.r)) *
        (D.Q * D.Z * D.h -
          (D.M - D.X) * (D.U - D.r) * (D.s - D.Y)) := by
  let d := D.M - D.X
  let p := D.s - D.Y
  let e := D.U - D.r
  have h2eU : 2 * e * D.U = D.h * D.Z + e ^ 2 := by
    dsimp [e]
    nlinarith [D.U_sq]
  have h2dX : 2 * d * D.X = D.h * D.Q - d ^ 2 := by
    dsimp [d]
    nlinarith [D.M_sq]
  have h2dM : 2 * d * D.M = D.h * D.Q + d ^ 2 := by
    dsimp [d]
    nlinarith [D.M_sq]
  have h2pY : 2 * p * D.Y = D.Z * D.Q - p ^ 2 := by
    dsimp [p]
    nlinarith [D.s_sq]
  have h2ps : 2 * p * D.s = D.Z * D.Q + p ^ 2 := by
    dsimp [p]
    nlinarith [D.s_sq]
  change 2 * d * e * p *
      (D.U * D.Q - D.X * D.Y - D.M * D.s) =
    (d * p - D.Q * e) * (D.Q * D.Z * D.h - d * e * p)
  calc
    2 * d * e * p *
        (D.U * D.Q - D.X * D.Y - D.M * D.s) =
      ((2 * e * D.U) * (2 * d * p * D.Q) -
        e * (2 * d * D.X) * (2 * p * D.Y) -
        e * (2 * d * D.M) * (2 * p * D.s)) / 2 := by ring
    _ = ((D.h * D.Z + e ^ 2) * (2 * d * p * D.Q) -
        e * (D.h * D.Q - d ^ 2) * (D.Z * D.Q - p ^ 2) -
        e * (D.h * D.Q + d ^ 2) * (D.Z * D.Q + p ^ 2)) / 2 := by
          rw [h2eU, h2dX, h2pY, h2dM, h2ps]
    _ = (d * p - D.Q * e) *
        (D.Q * D.Z * D.h - d * e * p) := by ring

/-- The second factor in `right_gap_factor` is strictly positive. -/
lemma gap_factor_lt :
    (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) < D.Q * D.Z * D.h := by
  let d := D.M - D.X
  let p := D.s - D.Y
  let e := D.U - D.r
  have hd : 0 < d := by simpa [d] using D.X_lt_M
  have hp : 0 < p := by simpa [p] using D.Y_lt_s
  have he : 0 < e := by simpa [e] using D.r_lt_U
  have hd2 : d ^ 2 < D.h * D.Q := by
    have hx := D.X_pos
    dsimp [d]
    nlinarith [D.M_sq]
  have hp2 : p ^ 2 < D.Z * D.Q := by
    have hy := D.Y_pos
    dsimp [p]
    nlinarith [D.s_sq]
  have he2 : e ^ 2 < D.h * D.Z := by
    have hr := D.r_pos
    dsimp [e]
    nlinarith [D.U_sq]
  have hde : d ^ 2 * e ^ 2 < (D.h * D.Q) * (D.h * D.Z) :=
    mul_lt_mul hd2 he2.le (sq_pos_of_pos he) (mul_pos D.h_pos D.Q_pos).le
  have hdep : d ^ 2 * e ^ 2 * p ^ 2 <
      (D.h * D.Q) * (D.h * D.Z) * (D.Z * D.Q) :=
    mul_lt_mul hde hp2.le (sq_pos_of_pos hp)
      (mul_nonneg (mul_pos D.h_pos D.Q_pos).le
        (mul_pos D.h_pos D.Z_pos).le)
  have hsquare : (d * e * p) ^ 2 < (D.Q * D.Z * D.h) ^ 2 := by
    calc
      (d * e * p) ^ 2 = d ^ 2 * e ^ 2 * p ^ 2 := by ring
      _ < (D.h * D.Q) * (D.h * D.Z) * (D.Z * D.Q) := hdep
      _ = (D.Q * D.Z * D.h) ^ 2 := by ring
  change d * e * p < D.Q * D.Z * D.h
  have hleft0 : 0 ≤ d * e * p := (mul_pos (mul_pos hd he) hp).le
  have hright0 : 0 ≤ D.Q * D.Z * D.h :=
    (mul_pos (mul_pos D.Q_pos D.Z_pos) D.h_pos).le
  exact (sq_lt_sq₀ hleft0 hright0).mp hsquare

/-- The first old reflection row is exactly the hyperbolic gap row. -/
lemma left_row_iff_gap :
    D.X * D.Z + D.Y * D.U ≤ D.r * D.s ↔
      D.Q * (D.U - D.r) ≤ (D.M - D.X) * (D.s - D.Y) := by
  have hd : 0 < D.M - D.X := sub_pos.mpr D.X_lt_M
  have hp : 0 < D.s - D.Y := sub_pos.mpr D.Y_lt_s
  have he : 0 < D.U - D.r := sub_pos.mpr D.r_lt_U
  have hscale : 0 <
      2 * (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hd) he) hp
  have htail : 0 < D.h * (D.s - D.Y) +
      (D.M - D.X) * (D.U - D.r) :=
    add_pos (mul_pos D.h_pos hp) (mul_pos hd he)
  constructor
  · intro hrow
    have hlhs : 0 ≤
        2 * (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) *
          (D.r * D.s - D.X * D.Z - D.Y * D.U) := by
      have hrow0 : 0 ≤ D.r * D.s - D.X * D.Z - D.Y * D.U := by
        linarith only [hrow]
      exact mul_nonneg hscale.le hrow0
    rw [D.left_gap_factor] at hlhs
    by_contra hn
    have hneg : (D.M - D.X) * (D.s - D.Y) -
        D.Q * (D.U - D.r) < 0 := by linarith
    have : D.Z *
        ((D.M - D.X) * (D.s - D.Y) - D.Q * (D.U - D.r)) *
          (D.h * (D.s - D.Y) +
            (D.M - D.X) * (D.U - D.r)) < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg D.Z_pos hneg)
        htail
    linarith
  · intro hgap
    have hfirst : 0 ≤ (D.M - D.X) * (D.s - D.Y) -
        D.Q * (D.U - D.r) := sub_nonneg.mpr hgap
    have hlast : 0 ≤ D.h * (D.s - D.Y) +
        (D.M - D.X) * (D.U - D.r) := htail.le
    have hrhs : 0 ≤ D.Z *
        ((D.M - D.X) * (D.s - D.Y) - D.Q * (D.U - D.r)) *
          (D.h * (D.s - D.Y) +
            (D.M - D.X) * (D.U - D.r)) :=
      mul_nonneg (mul_nonneg D.Z_pos.le hfirst) hlast
    rw [← D.left_gap_factor] at hrhs
    have hrow0 := nonneg_of_mul_nonneg_right hrhs hscale
    linarith only [hrow0]

/-- The second old reflection row is the same hyperbolic gap row. -/
lemma right_row_iff_gap :
    D.X * D.Y + D.M * D.s ≤ D.U * D.Q ↔
      D.Q * (D.U - D.r) ≤ (D.M - D.X) * (D.s - D.Y) := by
  have hd : 0 < D.M - D.X := sub_pos.mpr D.X_lt_M
  have hp : 0 < D.s - D.Y := sub_pos.mpr D.Y_lt_s
  have he : 0 < D.U - D.r := sub_pos.mpr D.r_lt_U
  have hscale : 0 <
      2 * (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hd) he) hp
  have hsecond : 0 < D.Q * D.Z * D.h -
      (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) := by
    exact sub_pos.mpr D.gap_factor_lt
  constructor
  · intro hrow
    have hlhs : 0 ≤
        2 * (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) *
          (D.U * D.Q - D.X * D.Y - D.M * D.s) := by
      have hrow0 : 0 ≤ D.U * D.Q - D.X * D.Y - D.M * D.s := by
        linarith only [hrow]
      exact mul_nonneg hscale.le hrow0
    rw [D.right_gap_factor] at hlhs
    by_contra hn
    have hneg : (D.M - D.X) * (D.s - D.Y) -
        D.Q * (D.U - D.r) < 0 := by linarith
    have : ((D.M - D.X) * (D.s - D.Y) - D.Q * (D.U - D.r)) *
        (D.Q * D.Z * D.h -
          (D.M - D.X) * (D.U - D.r) * (D.s - D.Y)) < 0 :=
      mul_neg_of_neg_of_pos hneg hsecond
    linarith
  · intro hgap
    have hfirst : 0 ≤ (D.M - D.X) * (D.s - D.Y) -
        D.Q * (D.U - D.r) := sub_nonneg.mpr hgap
    have hlast : 0 ≤ D.Q * D.Z * D.h -
        (D.M - D.X) * (D.U - D.r) * (D.s - D.Y) := hsecond.le
    have hrhs : 0 ≤
        ((D.M - D.X) * (D.s - D.Y) - D.Q * (D.U - D.r)) *
          (D.Q * D.Z * D.h -
            (D.M - D.X) * (D.U - D.r) * (D.s - D.Y)) :=
      mul_nonneg hfirst hlast
    rw [← D.right_gap_factor] at hrhs
    have hrow0 := nonneg_of_mul_nonneg_right hrhs hscale
    linarith only [hrow0]

lemma old_left_row : D.X * D.Z + D.Y * D.U ≤ D.r * D.s :=
  D.left_row_iff_gap.mpr D.gap

lemma old_right_row : D.X * D.Y + D.M * D.s ≤ D.U * D.Q :=
  D.right_row_iff_gap.mpr D.gap

/-- Minimal scalar row obtained by weakening the terminal factor `R` to
its normalized floor. -/
lemma terminal_sum : D.U + D.r ≤ D.Z * D.W := by
  have hU0 : 0 ≤ D.U := le_trans (by norm_num) D.U_floor
  have hsum : 0 ≤ D.U + D.r := add_nonneg hU0 D.r_pos.le
  have hmul : D.U + D.r ≤ D.R * (D.U + D.r) := by
    simpa using mul_le_mul_of_nonneg_right D.R_floor hsum
  exact le_trans hmul D.ZW

/-- Minimal scalar row obtained from `Pp` by weakening `R` to one. -/
lemma Q_le_Pp : D.Q ≤ D.P * (D.s - D.Y) := by
  have hQR : D.Q ≤ D.Q * D.R := by
    have hQ0 : 0 ≤ D.Q := D.Q_pos.le
    simpa using mul_le_mul_of_nonneg_left D.R_floor hQ0
  exact le_trans hQR D.Pp

/-- Product-ear form of the paired second-ear cap. -/
lemma secondEar_product :
    D.Z * D.Q ≤ (D.Z - 1) * (D.Y ^ 2 + D.Z) := by
  have hZ1 : 0 ≤ D.Z - 1 := sub_nonneg.mpr D.Z_floor
  have hB : 2 * D.B ≤ D.Y ^ 2 + 1 := D.B_allocation
  nlinarith [D.s_sq, D.s_secondEar,
    mul_nonneg hZ1 (sub_nonneg.mpr hB)]

/-- The additive ears and the fan allocation give the exact objective seam
used by the product-ear closer. -/
lemma product_objective : D.r + D.s + D.P + D.W + 3 ≤ H := by
  linarith [D.r_ear, D.s_ear, D.P_ear, D.C_floor, D.area]

end HullSevenType2HyperbolicPacket

namespace HullSevenType2HyperbolicBracketData

private lemma index_seven : (7 : HullSevenType2HyperbolicIndex) = 0 := by decide
private lemma index_eight : (8 : HullSevenType2HyperbolicIndex) = 1 := by decide
private lemma index_nine : (9 : HullSevenType2HyperbolicIndex) = 2 := by decide
private lemma index_eleven : (11 : HullSevenType2HyperbolicIndex) = 4 := by decide

/-- Cyclic boundary cells. -/
def a {H : ℝ} (D : HullSevenType2HyperbolicBracketData H)
    (i : HullSevenType2HyperbolicIndex) : ℝ :=
  D.bracket i (i + 1)

/-- Signed cyclic two-step chords; `b 5` is negative. -/
def b {H : ℝ} (D : HullSevenType2HyperbolicBracketData H)
    (i : HullSevenType2HyperbolicIndex) : ℝ :=
  D.bracket i (i + 2)

/-- Signed cyclic three-step chords; `u 4,u 5` are negative. -/
def u {H : ℝ} (D : HullSevenType2HyperbolicBracketData H)
    (i : HullSevenType2HyperbolicIndex) : ℝ :=
  D.bracket i (i + 3)

/-- Consecutive four-index Pluecker row. -/
lemma e2 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H)
    (i : HullSevenType2HyperbolicIndex) :
    D.b i * D.b (i + 1) =
      D.a i * D.a (i + 2) + D.a (i + 1) * D.u i := by
  have hp := D.plucker i (i + 1) (i + 2) (i + 3)
  dsimp [a, b, u]
  norm_num [add_assoc] at hp ⊢
  nlinarith

/-- Separated four-index Pluecker row. -/
lemma e1 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H)
    (i : HullSevenType2HyperbolicIndex) :
    D.a i * D.a (i + 3) =
      D.u i * D.u (i + 1) + D.u (i + 4) * D.b (i + 1) := by
  have hwrap : i + 4 + 3 = i := by
    rw [add_assoc, show (4 : ZMod 7) + 3 = 0 by decide, add_zero]
  have hflip : D.bracket i (i + 4) =
      -D.bracket (i + 4) (i + 4 + 3) := by
    rw [hwrap]
    exact D.skew i (i + 4)
  have hp := D.plucker i (i + 1) (i + 3) (i + 4)
  dsimp [a, b, u]
  rw [hflip] at hp
  norm_num [add_assoc] at hp ⊢
  nlinarith

/-! The nine named raw rows used by the hyperbolic packet. -/

/-- `GP0235`: the exceptional negative two-step chord creates the `U-r`
square gap. -/
lemma gp0235 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.u 0 * D.u 2 = D.b 0 * D.b 3 + (-D.b 5) * D.a 2 := by
  have hp := D.plucker 0 2 3 5
  have h05 := D.skew 0 5
  rw [h05] at hp
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_seven] at hp ⊢
  nlinarith

/-- `GP0145`: the same negative chord creates the `M-X` square gap. -/
lemma gp0145 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    (-D.u 4) * (-D.u 5) =
      D.a 0 * D.a 4 + (-D.b 5) * D.u 1 := by
  have hp := D.e1 4
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_seven, index_eight, index_eleven] at hp ⊢
  nlinarith

/-- `GP1234`: the central positive row creates the `s-Y` square gap. -/
lemma gp1234 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.b 1 * D.b 2 = D.a 1 * D.a 3 + D.a 2 * D.u 1 := by
  have hp := D.e2 1
  norm_num [a, b, u, add_assoc] at hp ⊢
  exact hp

/-- `GP1246`, one half of the `P(s-Y)` pair. -/
lemma gp1246 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.b 2 * D.b 6 = D.a 1 * D.b 4 + D.u 1 * D.u 6 := by
  have hp := D.plucker 1 2 4 6
  have h16 := D.skew 1 6
  have h26 := D.skew 2 6
  rw [h16, h26] at hp
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_eight, index_nine] at hp ⊢
  nlinarith

/-- `GP1346`, the reflected half of the `P(s-Y)` pair. -/
lemma gp1346 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.b 1 * D.b 4 = D.u 1 * D.u 3 + D.a 3 * D.b 6 := by
  have hp := D.plucker 1 3 4 6
  have h16 := D.skew 1 6
  rw [h16] at hp
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_eight, index_nine] at hp ⊢
  nlinarith

/-- `GP0456`, one half of the `W(M-X)` pair. -/
lemma gp0456 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.a 5 * (-D.u 4) = D.a 4 * D.a 6 + (-D.b 5) * D.b 4 := by
  have hp := D.e2 4
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_seven] at hp ⊢
  nlinarith

/-- `GP0156`, the reflected half of the `W(M-X)` pair. -/
lemma gp0156 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.a 6 * (-D.u 5) = D.a 0 * D.a 5 + (-D.b 5) * D.b 6 := by
  have hp := D.e2 5
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_seven, index_eight] at hp ⊢
  nlinarith

/-- `GP0256`, one half of the `W(U-r)` pair. -/
lemma gp0256 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.a 6 * D.u 2 = D.a 5 * D.b 0 + (-D.b 5) * D.u 6 := by
  have hp := D.plucker 0 2 5 6
  have h05 := D.skew 0 5
  have h06 := D.skew 0 6
  have h26 := D.skew 2 6
  rw [h05, h06, h26] at hp
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_seven, index_nine] at hp ⊢
  nlinarith

/-- `GP0356`, the reflected half of the `W(U-r)` pair. -/
lemma gp0356 {H : ℝ} (D : HullSevenType2HyperbolicBracketData H) :
    D.a 5 * D.u 0 = D.a 6 * D.b 3 + (-D.b 5) * D.u 3 := by
  have hp := D.plucker 0 3 5 6
  have h05 := D.skew 0 5
  have h06 := D.skew 0 6
  rw [h05, h06] at hp
  norm_num [a, b, u, add_assoc] at hp ⊢
  simp only [index_seven] at hp ⊢
  nlinarith

private lemma one_le_sqrt_mul {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ Real.sqrt (x * y) := by
  apply Real.one_le_sqrt.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

private lemma two_sqrt_mul_le_add {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  rw [Real.sqrt_mul hx]
  have hxsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hysq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]

private lemma sqrt_mul_self {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x * x) = x := by
  rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

private lemma sqrt_four_reassociate {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt ((a * b) * (c * d)) =
      Real.sqrt (a * c) * Real.sqrt (b * d) := by
  calc
    Real.sqrt ((a * b) * (c * d)) =
        Real.sqrt (a * b) * Real.sqrt (c * d) :=
      Real.sqrt_mul (mul_nonneg ha hb) (c * d)
    _ = (Real.sqrt a * Real.sqrt b) *
        (Real.sqrt c * Real.sqrt d) := by
      rw [Real.sqrt_mul ha, Real.sqrt_mul hc]
    _ = (Real.sqrt a * Real.sqrt c) *
        (Real.sqrt b * Real.sqrt d) := by ring
    _ = Real.sqrt (a * c) * Real.sqrt (b * d) := by
      rw [Real.sqrt_mul ha, Real.sqrt_mul hb]

/-- Multiplicative Minkowski for two positive additive Pluecker rows. -/
private lemma paired_sum_gm
    {x₁ y₁ x₂ y₂ a₁ b₁ a₂ b₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁)
    (hx₂ : 0 ≤ x₂) (hy₂ : 0 ≤ y₂)
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁)
    (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂)
    (h₁ : x₁ * y₁ = a₁ + b₁)
    (h₂ : x₂ * y₂ = a₂ + b₂) :
    Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
      Real.sqrt (x₁ * x₂) * Real.sqrt (y₁ * y₂) := by
  have hleft : 0 ≤ Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) := by
    positivity
  have hright : 0 ≤ Real.sqrt ((a₁ + b₁) * (a₂ + b₂)) :=
    Real.sqrt_nonneg _
  have hsquare :
      (Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂)) ^ 2 ≤
        (Real.sqrt ((a₁ + b₁) * (a₂ + b₂))) ^ 2 := by
    have ha : (Real.sqrt (a₁ * a₂)) ^ 2 = a₁ * a₂ :=
      Real.sq_sqrt (mul_nonneg ha₁ ha₂)
    have hb : (Real.sqrt (b₁ * b₂)) ^ 2 = b₁ * b₂ :=
      Real.sq_sqrt (mul_nonneg hb₁ hb₂)
    have hab : (Real.sqrt ((a₁ + b₁) * (a₂ + b₂))) ^ 2 =
        (a₁ + b₁) * (a₂ + b₂) :=
      Real.sq_sqrt (mul_nonneg (add_nonneg ha₁ hb₁)
        (add_nonneg ha₂ hb₂))
    have hcross : 2 * Real.sqrt (a₁ * a₂) * Real.sqrt (b₁ * b₂) ≤
        a₁ * b₂ + b₁ * a₂ := by
      calc
        2 * Real.sqrt (a₁ * a₂) * Real.sqrt (b₁ * b₂) =
            2 * (Real.sqrt a₁ * Real.sqrt b₂) *
              (Real.sqrt b₁ * Real.sqrt a₂) := by
          rw [Real.sqrt_mul ha₁, Real.sqrt_mul hb₁]
          ring
        _ ≤ (Real.sqrt a₁ * Real.sqrt b₂) ^ 2 +
            (Real.sqrt b₁ * Real.sqrt a₂) ^ 2 := by
          nlinarith [sq_nonneg
            (Real.sqrt a₁ * Real.sqrt b₂ -
              Real.sqrt b₁ * Real.sqrt a₂)]
        _ = a₁ * b₂ + b₁ * a₂ := by
          rw [mul_pow, mul_pow, Real.sq_sqrt ha₁, Real.sq_sqrt hb₁,
            Real.sq_sqrt ha₂, Real.sq_sqrt hb₂]
    rw [add_sq, ha, hb, hab]
    nlinarith
  have hminkowski : Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
      Real.sqrt ((a₁ + b₁) * (a₂ + b₂)) :=
    (sq_le_sq₀ hleft hright).mp hsquare
  calc
    Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
        Real.sqrt ((a₁ + b₁) * (a₂ + b₂)) := hminkowski
    _ = Real.sqrt ((x₁ * y₁) * (x₂ * y₂)) := by rw [h₁, h₂]
    _ = Real.sqrt (x₁ * x₂) * Real.sqrt (y₁ * y₂) :=
      sqrt_four_reassociate hx₁ hy₁ hx₂ hy₂

/-! ## Construction of the exported packet -/

/-- All fields of the honest hyperbolic packet follow from the preferred
signed bracket chart. -/
noncomputable def toHyperbolicPacket {H : ℝ}
    (D : HullSevenType2HyperbolicBracketData H) :
    HullSevenType2HyperbolicPacket H := by
  let a : HullSevenType2HyperbolicIndex → ℝ := D.a
  let b : HullSevenType2HyperbolicIndex → ℝ := D.b
  let u : HullSevenType2HyperbolicIndex → ℝ := D.u
  let x : ℝ := -u 4
  let y : ℝ := -u 5
  let h : ℝ := -b 5
  let X : ℝ := Real.sqrt (a 0 * a 4)
  let Y : ℝ := Real.sqrt (a 1 * a 3)
  let Z : ℝ := a 2
  let W : ℝ := Real.sqrt (a 5 * a 6)
  let r : ℝ := Real.sqrt (b 0 * b 3)
  let s : ℝ := Real.sqrt (b 1 * b 2)
  let P : ℝ := Real.sqrt (b 4 * b 6)
  let U : ℝ := Real.sqrt (u 0 * u 2)
  let Q : ℝ := u 1
  let R : ℝ := Real.sqrt (u 3 * u 6)
  let M : ℝ := Real.sqrt (x * y)
  let A : ℝ := (a 0 + a 4) / 2
  let B : ℝ := (a 1 + a 3) / 2
  let C : ℝ := (a 5 + a 6) / 2

  have ha : ∀ i, 1 ≤ a i := fun i => D.adjacent_ge i
  have hb0 : 1 ≤ b 0 := by
    have ht := D.twoStepMagnitude_ge 0
    norm_num [b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht
  have hb1 : 1 ≤ b 1 := by
    have ht := D.twoStepMagnitude_ge 1
    norm_num [b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht
  have hb2 : 1 ≤ b 2 := by
    have ht := D.twoStepMagnitude_ge 2
    norm_num [b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht
  have hb3 : 1 ≤ b 3 := by
    have ht := D.twoStepMagnitude_ge 3
    norm_num [b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht
  have hb4 : 1 ≤ b 4 := by
    have ht := D.twoStepMagnitude_ge 4
    norm_num [b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht
  have hh : 1 ≤ h := by
    have ht := D.twoStepMagnitude_ge 5
    norm_num [h, b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht
  have hb6 : 1 ≤ b 6 := by
    have ht := D.twoStepMagnitude_ge 6
    norm_num [b, HullSevenType2HyperbolicBracketData.b,
      hullSevenType2HyperbolicTwoStepMagnitude] at ht ⊢
    exact ht

  have hu0 : 1 ≤ u 0 := by
    have ht := D.threeStepMagnitude_ge 0
    norm_num [u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht
  have hu1 : 1 ≤ u 1 := by
    have ht := D.threeStepMagnitude_ge 1
    norm_num [u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht
  have hu2 : 1 ≤ u 2 := by
    have ht := D.threeStepMagnitude_ge 2
    norm_num [u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht
  have hu3 : 1 ≤ u 3 := by
    have ht := D.threeStepMagnitude_ge 3
    norm_num [u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht
  have hx : 1 ≤ x := by
    have ht := D.threeStepMagnitude_ge 4
    norm_num [x, u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht
  have hy : 1 ≤ y := by
    have ht := D.threeStepMagnitude_ge 5
    norm_num [y, u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht
  have hu6 : 1 ≤ u 6 := by
    have ht := D.threeStepMagnitude_ge 6
    norm_num [u, HullSevenType2HyperbolicBracketData.u,
      hullSevenType2HyperbolicThreeStepMagnitude] at ht ⊢
    exact ht

  have ha0 : 0 ≤ a 0 := le_trans (by norm_num) (ha 0)
  have ha1 : 0 ≤ a 1 := le_trans (by norm_num) (ha 1)
  have ha2 : 0 ≤ a 2 := le_trans (by norm_num) (ha 2)
  have ha3 : 0 ≤ a 3 := le_trans (by norm_num) (ha 3)
  have ha4 : 0 ≤ a 4 := le_trans (by norm_num) (ha 4)
  have ha5 : 0 ≤ a 5 := le_trans (by norm_num) (ha 5)
  have ha6 : 0 ≤ a 6 := le_trans (by norm_num) (ha 6)
  have hb0n : 0 ≤ b 0 := le_trans (by norm_num) hb0
  have hb1n : 0 ≤ b 1 := le_trans (by norm_num) hb1
  have hb2n : 0 ≤ b 2 := le_trans (by norm_num) hb2
  have hb3n : 0 ≤ b 3 := le_trans (by norm_num) hb3
  have hb4n : 0 ≤ b 4 := le_trans (by norm_num) hb4
  have hb6n : 0 ≤ b 6 := le_trans (by norm_num) hb6
  have hhn : 0 ≤ h := le_trans (by norm_num) hh
  have hu0n : 0 ≤ u 0 := le_trans (by norm_num) hu0
  have hu1n : 0 ≤ u 1 := le_trans (by norm_num) hu1
  have hu2n : 0 ≤ u 2 := le_trans (by norm_num) hu2
  have hu3n : 0 ≤ u 3 := le_trans (by norm_num) hu3
  have hu6n : 0 ≤ u 6 := le_trans (by norm_num) hu6
  have hxn : 0 ≤ x := le_trans (by norm_num) hx
  have hyn : 0 ≤ y := le_trans (by norm_num) hy

  have hXsq : X ^ 2 = a 0 * a 4 := by
    dsimp [X]
    exact Real.sq_sqrt (mul_nonneg ha0 ha4)
  have hYsq : Y ^ 2 = a 1 * a 3 := by
    dsimp [Y]
    exact Real.sq_sqrt (mul_nonneg ha1 ha3)
  have hWsq : W ^ 2 = a 5 * a 6 := by
    dsimp [W]
    exact Real.sq_sqrt (mul_nonneg ha5 ha6)
  have hrsq : r ^ 2 = b 0 * b 3 := by
    dsimp [r]
    exact Real.sq_sqrt (mul_nonneg hb0n hb3n)
  have hssqRaw : s ^ 2 = b 1 * b 2 := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hb1n hb2n)
  have hPsq : P ^ 2 = b 4 * b 6 := by
    dsimp [P]
    exact Real.sq_sqrt (mul_nonneg hb4n hb6n)
  have hUsqRaw : U ^ 2 = u 0 * u 2 := by
    dsimp [U]
    exact Real.sq_sqrt (mul_nonneg hu0n hu2n)
  have hMsqRaw : M ^ 2 = x * y := by
    dsimp [M]
    exact Real.sq_sqrt (mul_nonneg hxn hyn)

  have hgp0235 := D.gp0235
  have hgp0145 := D.gp0145
  have hgp1234 := D.gp1234
  have hgp1246 := D.gp1246
  have hgp1346 := D.gp1346
  have hgp0456 := D.gp0456
  have hgp0156 := D.gp0156
  have hgp0256 := D.gp0256
  have hgp0356 := D.gp0356
  change u 0 * u 2 = b 0 * b 3 + h * a 2 at hgp0235
  change x * y = a 0 * a 4 + h * u 1 at hgp0145
  change b 1 * b 2 = a 1 * a 3 + a 2 * u 1 at hgp1234
  change b 2 * b 6 = a 1 * b 4 + u 1 * u 6 at hgp1246
  change b 1 * b 4 = u 1 * u 3 + a 3 * b 6 at hgp1346
  change a 5 * x = a 4 * a 6 + h * b 4 at hgp0456
  change a 6 * y = a 0 * a 5 + h * b 6 at hgp0156
  change a 6 * u 2 = a 5 * b 0 + h * u 6 at hgp0256
  change a 5 * u 0 = a 6 * b 3 + h * u 3 at hgp0356

  have hM_sq : M ^ 2 - X ^ 2 = h * Q := by
    dsimp [Q]
    nlinarith only [hMsqRaw, hXsq, hgp0145]
  have hs_sq : s ^ 2 - Y ^ 2 = Z * Q := by
    dsimp [Z, Q]
    nlinarith only [hssqRaw, hYsq, hgp1234]
  have hU_sq : U ^ 2 - r ^ 2 = h * Z := by
    dsimp [Z]
    nlinarith only [hUsqRaw, hrsq, hgp0235]

  have he20 := D.e2 0
  have he22 := D.e2 2
  have he12 := D.e1 2
  have he16 := D.e1 6
  norm_num [a, b, u, add_assoc] at he20 he22 he12 he16
  change a 6 * a 2 = u 6 * u 0 + u 3 * b 0 at he16

  have hOldLeft : X * Z + Y * U ≤ r * s := by
    have hraw := paired_sum_gm
      hb0n hb1n hb3n hb2n
      (mul_nonneg ha0 ha2) (mul_nonneg ha1 hu0n)
      (mul_nonneg ha4 ha2) (mul_nonneg ha3 hu2n)
      he20 (by nlinarith only [he22])
    have hfirst : Real.sqrt ((a 0 * a 2) * (a 4 * a 2)) = X * Z := by
      calc
        Real.sqrt ((a 0 * a 2) * (a 4 * a 2)) =
            Real.sqrt (a 0 * a 4) * Real.sqrt (a 2 * a 2) :=
          sqrt_four_reassociate ha0 ha2 ha4 ha2
        _ = X * Z := by rw [sqrt_mul_self ha2]
    have hsecond : Real.sqrt ((a 1 * u 0) * (a 3 * u 2)) = Y * U := by
      calc
        Real.sqrt ((a 1 * u 0) * (a 3 * u 2)) =
            Real.sqrt (a 1 * a 3) * Real.sqrt (u 0 * u 2) :=
          sqrt_four_reassociate ha1 hu0n ha3 hu2n
        _ = Y * U := rfl
    rw [hfirst, hsecond] at hraw
    exact hraw

  let d : ℝ := M - X
  let p : ℝ := s - Y
  let e : ℝ := U - r
  have hXpos : 0 < X := by
    dsimp [X]
    exact Real.sqrt_pos.2 (mul_pos
      (lt_of_lt_of_le (by norm_num) (ha 0))
      (lt_of_lt_of_le (by norm_num) (ha 4)))
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact Real.sqrt_pos.2 (mul_pos
      (lt_of_lt_of_le (by norm_num) (ha 1))
      (lt_of_lt_of_le (by norm_num) (ha 3)))
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 (mul_pos
      (lt_of_lt_of_le (by norm_num) hb0)
      (lt_of_lt_of_le (by norm_num) hb3))
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hu1
  have hhpos : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) (ha 2)
  have hd : 0 < d := by
    dsimp [d]
    have hgap : 0 < h * Q := mul_pos hhpos hQpos
    nlinarith only [hM_sq, hXpos,
      (Real.sqrt_nonneg (x * y) : 0 ≤ M), hgap]
  have hp : 0 < p := by
    dsimp [p]
    have hgap : 0 < Z * Q := mul_pos hZpos hQpos
    nlinarith only [hs_sq, hYpos,
      (Real.sqrt_nonneg (b 1 * b 2) : 0 ≤ s), hgap]
  have he : 0 < e := by
    dsimp [e]
    have hgap : 0 < h * Z := mul_pos hhpos hZpos
    nlinarith only [hU_sq, hrpos,
      (Real.sqrt_nonneg (u 0 * u 2) : 0 ≤ U), hgap]
  have h2dX : 2 * d * X = h * Q - d ^ 2 := by
    dsimp [d]
    nlinarith only [hM_sq]
  have h2pY : 2 * p * Y = Z * Q - p ^ 2 := by
    dsimp [p]
    nlinarith only [hs_sq]
  have h2er : 2 * e * r = h * Z - e ^ 2 := by
    dsimp [e]
    nlinarith only [hU_sq]
  have hfactor :
      2 * d * e * p * (r * s - X * Z - Y * U) =
        Z * (d * p - Q * e) * (h * p + d * e) := by
    calc
      2 * d * e * p * (r * s - X * Z - Y * U) =
          d * p ^ 2 * (2 * e * r) -
            d * e ^ 2 * (2 * p * Y) -
            e * p * Z * (2 * d * X) := by
        dsimp [d, p, e]
        ring
      _ = d * p ^ 2 * (h * Z - e ^ 2) -
          d * e ^ 2 * (Z * Q - p ^ 2) -
          e * p * Z * (h * Q - d ^ 2) := by
        rw [h2er, h2pY, h2dX]
      _ = Z * (d * p - Q * e) * (h * p + d * e) := by ring
  have hgap : Q * e ≤ d * p := by
    have hlhs : 0 ≤ 2 * d * e * p * (r * s - X * Z - Y * U) := by
      have hrow : 0 ≤ r * s - X * Z - Y * U := by
        linarith only [hOldLeft]
      have hscale : 0 ≤ 2 * d * e * p :=
        (mul_pos (mul_pos (mul_pos (by norm_num) hd) he) hp).le
      exact mul_nonneg hscale hrow
    rw [hfactor] at hlhs
    by_contra hn
    have hneg : d * p - Q * e < 0 := by
      linarith only [hn]
    have htail : 0 < h * p + d * e :=
      add_pos (mul_pos hhpos hp) (mul_pos hd he)
    have hright : Z * (d * p - Q * e) * (h * p + d * e) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hZpos hneg) htail
    linarith only [hlhs, hright]

  have hZW : R * (U + r) ≤ Z * W := by
    have hrow6 : a 2 * a 6 = u 0 * u 6 + u 3 * b 0 := by
      nlinarith only [he16]
    have hraw := paired_sum_gm
      ha2 ha5 ha2 ha6
      (mul_nonneg hu2n hu3n) (mul_nonneg hu6n hb3n)
      (mul_nonneg hu0n hu6n) (mul_nonneg hu3n hb0n)
      he12 hrow6
    have hfirst : Real.sqrt ((u 2 * u 3) * (u 0 * u 6)) = U * R := by
      calc
        Real.sqrt ((u 2 * u 3) * (u 0 * u 6)) =
            Real.sqrt (u 2 * u 0) * Real.sqrt (u 3 * u 6) :=
          sqrt_four_reassociate hu2n hu3n hu0n hu6n
        _ = U * R := by rw [mul_comm (u 2) (u 0)]
    have hsecond : Real.sqrt ((u 6 * b 3) * (u 3 * b 0)) = R * r := by
      calc
        Real.sqrt ((u 6 * b 3) * (u 3 * b 0)) =
            Real.sqrt (u 6 * u 3) * Real.sqrt (b 3 * b 0) :=
          sqrt_four_reassociate hu6n hb3n hu3n hb0n
        _ = R * r := by
          rw [mul_comm (u 6) (u 3), mul_comm (b 3) (b 0)]
    have hz : Real.sqrt (a 2 * a 2) = Z := by
      rw [sqrt_mul_self ha2]
    rw [hfirst, hsecond, hz] at hraw
    nlinarith only [hraw]

  have hWd : h * P ≤ W * d := by
    have hraw := paired_sum_gm
      ha5 hxn ha6 hyn
      (mul_nonneg ha4 ha6) (mul_nonneg hhn hb4n)
      (mul_nonneg ha0 ha5) (mul_nonneg hhn hb6n)
      hgp0456 hgp0156
    have hfirst : Real.sqrt ((a 4 * a 6) * (a 0 * a 5)) = X * W := by
      calc
        Real.sqrt ((a 4 * a 6) * (a 0 * a 5)) =
            Real.sqrt (a 4 * a 0) * Real.sqrt (a 6 * a 5) :=
          sqrt_four_reassociate ha4 ha6 ha0 ha5
        _ = X * W := by
          rw [mul_comm (a 4) (a 0), mul_comm (a 6) (a 5)]
    have hsecond : Real.sqrt ((h * b 4) * (h * b 6)) = h * P := by
      calc
        Real.sqrt ((h * b 4) * (h * b 6)) =
            Real.sqrt (h * h) * Real.sqrt (b 4 * b 6) :=
          sqrt_four_reassociate hhn hb4n hhn hb6n
        _ = h * P := by rw [sqrt_mul_self hhn]
    have hright : Real.sqrt (a 5 * a 6) * Real.sqrt (x * y) = W * M := rfl
    rw [hfirst, hsecond, hright] at hraw
    dsimp [d]
    nlinarith only [hraw]

  have hWe : h * R ≤ W * e := by
    have hraw := paired_sum_gm
      ha6 hu2n ha5 hu0n
      (mul_nonneg ha5 hb0n) (mul_nonneg hhn hu6n)
      (mul_nonneg ha6 hb3n) (mul_nonneg hhn hu3n)
      hgp0256 hgp0356
    have hfirst : Real.sqrt ((a 5 * b 0) * (a 6 * b 3)) = W * r := by
      calc
        Real.sqrt ((a 5 * b 0) * (a 6 * b 3)) =
            Real.sqrt (a 5 * a 6) * Real.sqrt (b 0 * b 3) :=
          sqrt_four_reassociate ha5 hb0n ha6 hb3n
        _ = W * r := rfl
    have hsecond : Real.sqrt ((h * u 6) * (h * u 3)) = h * R := by
      calc
        Real.sqrt ((h * u 6) * (h * u 3)) =
            Real.sqrt (h * h) * Real.sqrt (u 6 * u 3) :=
          sqrt_four_reassociate hhn hu6n hhn hu3n
        _ = h * R := by
          rw [sqrt_mul_self hhn, mul_comm (u 6) (u 3)]
    have hright : Real.sqrt (a 6 * a 5) * Real.sqrt (u 2 * u 0) = W * U := by
      rw [mul_comm (a 6) (a 5), mul_comm (u 2) (u 0)]
    rw [hfirst, hsecond, hright] at hraw
    dsimp [e]
    nlinarith only [hraw]

  have hPp : Q * R ≤ P * p := by
    have hraw := paired_sum_gm
      hb1n hb4n hb2n hb6n
      (mul_nonneg hu1n hu3n) (mul_nonneg ha3 hb6n)
      (mul_nonneg hu1n hu6n) (mul_nonneg ha1 hb4n)
      hgp1346 (by simpa [add_comm] using hgp1246)
    have hfirst : Real.sqrt ((u 1 * u 3) * (u 1 * u 6)) = Q * R := by
      calc
        Real.sqrt ((u 1 * u 3) * (u 1 * u 6)) =
            Real.sqrt (u 1 * u 1) * Real.sqrt (u 3 * u 6) :=
          sqrt_four_reassociate hu1n hu3n hu1n hu6n
        _ = Q * R := by rw [sqrt_mul_self hu1n]
    have hsecond : Real.sqrt ((a 3 * b 6) * (a 1 * b 4)) = Y * P := by
      calc
        Real.sqrt ((a 3 * b 6) * (a 1 * b 4)) =
            Real.sqrt (a 3 * a 1) * Real.sqrt (b 6 * b 4) :=
          sqrt_four_reassociate ha3 hb6n ha1 hb4n
        _ = Y * P := by
          rw [mul_comm (a 3) (a 1), mul_comm (b 6) (b 4)]
    have hright : Real.sqrt (b 1 * b 2) * Real.sqrt (b 4 * b 6) = s * P := rfl
    rw [hfirst, hsecond, hright] at hraw
    dsimp [p]
    nlinarith only [hraw]

  have hear0 := D.ear0
  have hear1 := D.ear1
  have hear2 := D.ear2
  have hear3 := D.ear3
  have hear4 := D.ear4
  have hear6 := D.ear6
  change b 0 ≤ a 0 + a 1 - 1 at hear0
  change b 1 ≤ a 1 + a 2 - 1 at hear1
  change b 2 ≤ a 2 + a 3 - 1 at hear2
  change b 3 ≤ a 3 + a 4 - 1 at hear3
  change b 4 ≤ a 4 + a 5 - 1 at hear4
  change b 6 ≤ a 6 + a 0 - 1 at hear6

  have hr_ear : r + 1 ≤ A + B := by
    have hamgm := two_sqrt_mul_le_add hb0n hb3n
    dsimp [r, A, B] at hamgm ⊢
    linarith only [hamgm, hear0, hear3]
  have hs_ear : s + 1 ≤ B + Z := by
    have hamgm := two_sqrt_mul_le_add hb1n hb2n
    dsimp [s, B, Z] at hamgm ⊢
    linarith only [hamgm, hear1, hear2]
  have hP_ear : P + 1 ≤ A + C := by
    have hamgm := two_sqrt_mul_le_add hb4n hb6n
    dsimp [P, A, C] at hamgm ⊢
    linarith only [hamgm, hear4, hear6]

  have hear0prod : b 0 ≤ a 0 * a 1 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 0)) (sub_nonneg.mpr (ha 1))
    nlinarith only [hear0, hmul]
  have hear1prod : b 1 ≤ a 1 * a 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 1)) (sub_nonneg.mpr (ha 2))
    nlinarith only [hear1, hmul]
  have hear2prod : b 2 ≤ a 2 * a 3 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 2)) (sub_nonneg.mpr (ha 3))
    nlinarith only [hear2, hmul]
  have hear3prod : b 3 ≤ a 3 * a 4 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 3)) (sub_nonneg.mpr (ha 4))
    nlinarith only [hear3, hmul]
  have hear4prod : b 4 ≤ a 4 * a 5 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 4)) (sub_nonneg.mpr (ha 5))
    nlinarith only [hear4, hmul]
  have hear6prod : b 6 ≤ a 6 * a 0 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 6)) (sub_nonneg.mpr (ha 0))
    nlinarith only [hear6, hmul]
  have hr_product : r ≤ X * Y := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))).mp
    rw [hrsq, mul_pow, hXsq, hYsq]
    have hm := mul_le_mul hear0prod hear3prod hb3n (mul_nonneg ha0 ha1)
    nlinarith only [hm]
  have hs_product : s ≤ Y * Z := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha2)).mp
    rw [hssqRaw, mul_pow, hYsq]
    have hm := mul_le_mul hear1prod hear2prod hb2n (mul_nonneg ha1 ha2)
    nlinarith only [hm]
  have hP_product : P ≤ X * W := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))).mp
    rw [hPsq, mul_pow, hXsq, hWsq]
    have hm := mul_le_mul hear4prod hear6prod hb6n (mul_nonneg ha4 ha5)
    nlinarith only [hm]

  have hear12 : b 1 * b 2 ≤
      (a 1 + a 2 - 1) * (a 3 + a 2 - 1) := by
    simpa [add_comm] using
      mul_le_mul hear1 hear2 hb2n (by
        nlinarith only [ha 1, ha 2])
  have hs_secondEar :
      s ^ 2 ≤ Y ^ 2 + 2 * B * (Z - 1) + (Z - 1) ^ 2 := by
    dsimp [B, Z]
    nlinarith only [hssqRaw, hYsq, hear12]

  have hear03 : b 0 * b 3 ≤
      (a 0 + a 1 - 1) * (a 3 + a 4 - 1) :=
    mul_le_mul hear0 hear3 hb3n (by
      nlinarith only [ha 0, ha 1])
  have hr_weighted :
      r ^ 2 ≤ (A + B - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
        (B ^ 2 - Y ^ 2) / 3 := by
    have hgapSq : 0 ≤
        (3 * (a 0 - a 4) + 2 * (a 1 - a 3)) ^ 2 := sq_nonneg _
    have hid :
        (A + B - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
            (B ^ 2 - Y ^ 2) / 3 -
            ((a 0 + a 1 - 1) * (a 3 + a 4 - 1)) =
          (3 * (a 0 - a 4) + 2 * (a 1 - a 3)) ^ 2 / 24 := by
      dsimp [A, B]
      rw [hXsq, hYsq]
      ring
    nlinarith only [hgapSq, hid, hrsq, hear03]

  have hear46 : b 4 * b 6 ≤
      (a 4 + a 5 - 1) * (a 6 + a 0 - 1) :=
    mul_le_mul hear4 hear6 hb6n (by
      nlinarith only [ha 4, ha 5])
  have hP_weighted :
      P ^ 2 ≤ (A + C - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
        (C ^ 2 - W ^ 2) / 3 := by
    have hgapSq : 0 ≤
        (3 * (a 0 - a 4) - 2 * (a 5 - a 6)) ^ 2 := sq_nonneg _
    have hid :
        (A + C - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
            (C ^ 2 - W ^ 2) / 3 -
            ((a 4 + a 5 - 1) * (a 6 + a 0 - 1)) =
          (3 * (a 0 - a 4) - 2 * (a 5 - a 6)) ^ 2 / 24 := by
      dsimp [A, C]
      rw [hXsq, hWsq]
      ring
    nlinarith only [hgapSq, hid, hPsq, hear46]

  have hA_floor : X ≤ A := by
    have hamgm := two_sqrt_mul_le_add ha0 ha4
    dsimp [X, A] at hamgm ⊢
    linarith only [hamgm]
  have hB_floor : Y ≤ B := by
    have hamgm := two_sqrt_mul_le_add ha1 ha3
    dsimp [Y, B] at hamgm ⊢
    linarith only [hamgm]
  have hC_floor : W ≤ C := by
    have hamgm := two_sqrt_mul_le_add ha5 ha6
    dsimp [W, C] at hamgm ⊢
    linarith only [hamgm]
  have hA_allocation : 2 * A ≤ X ^ 2 + 1 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 0)) (sub_nonneg.mpr (ha 4))
    dsimp [A]
    nlinarith only [hmul, hXsq]
  have hB_allocation : 2 * B ≤ Y ^ 2 + 1 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 1)) (sub_nonneg.mpr (ha 3))
    dsimp [B]
    nlinarith only [hmul, hYsq]
  have hC_allocation : 2 * C ≤ W ^ 2 + 1 := by
    have hmul := mul_nonneg (sub_nonneg.mpr (ha 5)) (sub_nonneg.mpr (ha 6))
    dsimp [C]
    nlinarith only [hmul, hWsq]

  have harea : 2 * A + 2 * B + Z + 2 * C ≤ H := by
    have hraw : (∑ i, a i) ≤ H := by
      simpa [a, HullSevenType2HyperbolicBracketData.a] using D.area
    have hsum : (∑ i, a i) =
        a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 := by
      classical
      change Finset.sum (Finset.univ : Finset (ZMod 7)) a = _
      rw [show (Finset.univ : Finset (ZMod 7)) =
        {0, 1, 2, 3, 4, 5, 6} by decide]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      ring
    rw [hsum] at hraw
    dsimp [A, B, C, Z]
    linarith only [hraw]

  refine
    { X := X
      Y := Y
      Z := Z
      W := W
      r := r
      s := s
      U := U
      Q := Q
      R := R
      M := M
      h := h
      P := P
      A := A
      B := B
      C := C
      X_floor := one_le_sqrt_mul (ha 0) (ha 4)
      Y_floor := one_le_sqrt_mul (ha 1) (ha 3)
      Z_floor := ha 2
      W_floor := one_le_sqrt_mul (ha 5) (ha 6)
      r_floor := one_le_sqrt_mul hb0 hb3
      s_floor := one_le_sqrt_mul hb1 hb2
      U_floor := one_le_sqrt_mul hu0 hu2
      Q_floor := hu1
      R_floor := one_le_sqrt_mul hu3 hu6
      M_floor := one_le_sqrt_mul hx hy
      h_floor := hh
      P_floor := one_le_sqrt_mul hb4 hb6
      A_floor := hA_floor
      B_floor := hB_floor
      C_floor := hC_floor
      A_allocation := hA_allocation
      B_allocation := hB_allocation
      C_allocation := hC_allocation
      M_sq := hM_sq
      s_sq := hs_sq
      U_sq := hU_sq
      gap := by simpa [d, p, e] using hgap
      Wd := by simpa [d] using hWd
      We := by simpa [e] using hWe
      Pp := by simpa [p] using hPp
      ZW := hZW
      r_ear := hr_ear
      s_ear := hs_ear
      P_ear := hP_ear
      r_product := hr_product
      s_product := hs_product
      P_product := hP_product
      s_secondEar := hs_secondEar
      r_weighted := hr_weighted
      P_weighted := hP_weighted
      area := harea }

end HullSevenType2HyperbolicBracketData

end Heilbronn8.TriHull
