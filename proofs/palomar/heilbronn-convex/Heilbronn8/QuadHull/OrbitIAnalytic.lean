import Heilbronn8.QuadHull.Main

namespace Heilbronn8.QuadHull

/-!
# Analytic reductions for the orbit-I cyclic leaf

This file records reductions which use only the ordinary three-row cyclic fan,
independently of the generated `50t` certificates.  The first reduction rules
out the whole range `7 ≤ U ≤ 83 / 10` from the central determinant
constraint and the nine unit lower bounds.
-/

/--
The central determinant cannot be too negative when the three rows have the
cyclic lower-bound patterns `(3,1,3)`, `(1,3,3)`, and `(3,3,1)`.

Writing the row excesses as
`(a,b,c)`, `(d,e,f)`, and `(g,h,i)`, each triple has total at most
`q = U - 7`.  After eliminating the third coordinate,
`-det / U` is bounded by
`e*g + a*h + d*b + 2*(g+h) + 4`, and the cyclic bilinear term is at most
`q^2`.
-/
lemma cyclicDet_div_upper_of_row_lower_bounds
    {U Sx Sj Tx Tj Rx Rj : ℝ}
    (hU : 7 ≤ U)
    (hSx : 3 ≤ Sx) (hSj : 1 ≤ Sj)
    (hSy : 3 ≤ cyclicY U Sx Sj)
    (hTx : 1 ≤ Tx) (hTj : 3 ≤ Tj)
    (hTy : 3 ≤ cyclicY U Tx Tj)
    (hRx : 3 ≤ Rx) (hRj : 3 ≤ Rj)
    (hRy : 1 ≤ cyclicY U Rx Rj) :
    -cyclicDet U Sx Sj Tx Tj Rx Rj / U ≤
      (U - 7) ^ 2 + 2 * (U - 7) + 4 := by
  have hUpos : 0 < U := by linarith
  let q : ℝ := U - 7
  let a : ℝ := Sx - 3
  let b : ℝ := Sj - 1
  let d : ℝ := Tx - 1
  let e : ℝ := Tj - 3
  let g : ℝ := Rx - 3
  let h : ℝ := Rj - 3
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hg : 0 ≤ g := by dsimp [g]; linarith
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hab : a + b ≤ q := by
    dsimp [a, b, q]
    unfold cyclicY at hSy
    linarith
  have hde : d + e ≤ q := by
    dsimp [d, e, q]
    unfold cyclicY at hTy
    linarith
  have hgh : g + h ≤ q := by
    dsimp [g, h, q]
    unfold cyclicY at hRy
    linarith
  have hbilinear : e * g + a * h + d * b ≤ q ^ 2 := by
    by_cases hae : a ≤ e
    · have hegh : e * (g + h) ≤ e * q :=
        mul_le_mul_of_nonneg_left hgh he
      have hdb : d * b ≤ d * q := by
        apply mul_le_mul_of_nonneg_left _ hd
        nlinarith [hab]
      have hedq : (e + d) * q ≤ q * q := by
        apply mul_le_mul_of_nonneg_right _ hq
        linarith
      have hreplace : e * g + a * h ≤ e * (g + h) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hae) hh]
      nlinarith
    · have hea : e ≤ a := le_of_not_ge hae
      have hagh : a * (g + h) ≤ a * q :=
        mul_le_mul_of_nonneg_left hgh ha
      have hbqa : b ≤ q - a := by linarith [hab]
      have hqa : 0 ≤ q - a := by linarith [hab, hb]
      have hdq : d ≤ q := by linarith [hde, he]
      have hdb : d * b ≤ d * (q - a) :=
        mul_le_mul_of_nonneg_left hbqa hd
      have hdqa : d * (q - a) ≤ q * (q - a) :=
        mul_le_mul_of_nonneg_right hdq hqa
      have hreplace : e * g + a * h ≤ a * (g + h) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hea) hg]
      nlinarith
  have hE :
      (e - b + 2) * (g - a) - (d - a - 2) * (h - b + 2) ≤
        q ^ 2 + 2 * q + 4 := by
    nlinarith [hbilinear, mul_nonneg he ha, mul_nonneg hb hg,
      mul_nonneg hd hh]
  have hdet :
      -cyclicDet U Sx Sj Tx Tj Rx Rj =
        U * ((Tj - Sj) * (Rx - Sx) -
          (Tx - Sx) * (Rj - Sj)) := by
    unfold cyclicDet areaDet cyclicY
    ring
  rw [hdet]
  have hcancel :
      U * ((Tj - Sj) * (Rx - Sx) -
        (Tx - Sx) * (Rj - Sj)) / U =
        (Tj - Sj) * (Rx - Sx) -
          (Tx - Sx) * (Rj - Sj) := by
    field_simp
  rw [hcancel]
  dsimp [a, b, d, e, g, h, q] at hE
  nlinarith [hE]

/--
Every `50t` cyclic domain already satisfies the strict analytic cutoff
`83 / 10 < U`.  Thus a certificate partition may discard the entire lower
`U` interval before using any prime-fan or `CD` inequalities.
-/
theorem CyclicLeaf50tDomain.U_gt_eighty_three_tenths
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj) :
    (83 : ℝ) / 10 < U := by
  have hUpos : 0 < U := by linarith [r.U_lower]
  have hupper := cyclicDet_div_upper_of_row_lower_bounds
    r.U_lower r.Sx_lower r.Sj_lower
    (by linarith [r.Sy_lower])
    r.Tx_lower r.Tj_lower
    (by linarith [r.Ty_lower])
    r.Rx_lower r.Rj_lower
    (by linarith [r.Ry_lower])
  have hcentral : U ≤ -cyclicDet U Sx Sj Tx Tj Rx Rj / U := by
    apply (le_div_iff₀ hUpos).2
    nlinarith [r.central]
  have hpoly : 0 ≤ U ^ 2 - 13 * U + 39 := by
    nlinarith [hcentral, hupper]
  by_contra hn
  have hUupper : U ≤ (83 : ℝ) / 10 := le_of_not_gt hn
  have hfactor :
      (U - (83 : ℝ) / 10) * (U - (47 : ℝ) / 10) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (by linarith) (by linarith [r.U_lower])
  nlinarith

/-!
## The high-fan branch

The `CD` inequalities have the same interpretation in both cyclic fans.  If
`U ≤ V`, use the ordinary `T` row.  If `V ≤ U`, transport `CDR` through
the exact numerator formulas and use the primed `R` row.  In either case, for
`n = min U V`, `d = |V - U|`, and `M = max G (cyclicW U V G)`, the selected
row gives

`n + 3*d ≤ M * (n - 3)`.
-/

/-- The selected ordinary `T` row when `U` is the smaller fan. -/
lemma CyclicLeaf50tDomain.high_CD_of_U_le_V
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj)
    (hUV : U ≤ V) :
    U + 3 * (V - U) ≤ cyclicW U V G * (U - 3) := by
  have hd : 0 ≤ V - U := sub_nonneg.mpr hUV
  have hW : 0 ≤ cyclicW U V G := by linarith [r.W_lower]
  have hrow : Tx + cyclicY U Tx Tj ≤ U - 3 := by
    unfold cyclicY
    linarith [r.Tj_lower]
  have hrowMul :
      cyclicW U V G * (Tx + cyclicY U Tx Tj) ≤
        cyclicW U V G * (U - 3) :=
    mul_le_mul_of_nonneg_left hrow hW
  have hdTy :
      3 * (V - U) ≤ (V - U) * cyclicY U Tx Tj := by
    nlinarith [mul_nonneg hd r.Ty_lower]
  have hCD := r.CDT
  unfold cyclicW at hCD hrowMul ⊢
  nlinarith

/--
The exact `CDR` transport identity.  The two numerator expressions are the
primed `x` and `y` coordinates with their common positive denominator `U`.
-/
lemma cyclic_CD_transport_R
    (U V G Rx Rj : ℝ) :
    G * cyclicYNum U V G (cyclicY U Rx Rj) Rj +
        cyclicW U V G * cyclicXNum V G Rx Rj =
      V * (G * cyclicY U Rx Rj + cyclicW U V G * Rx) := by
  unfold cyclicYNum cyclicXNum cyclicW cyclicY
  ring

/-- The exact primed-row sum, in denominator-cleared form. -/
lemma cyclic_primed_R_sum
    (U V G Rx Rj : ℝ) :
    cyclicXNum V G Rx Rj +
        cyclicYNum U V G (cyclicY U Rx Rj) Rj + U * Rj =
      U * V := by
  unfold cyclicYNum cyclicXNum cyclicW cyclicY
  ring

/-- The transported primed `R` row when `V` is the smaller fan. -/
lemma CyclicLeaf50tDomain.high_CD_of_V_le_U
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj)
    (hVU : V ≤ U) :
    V + 3 * (U - V) ≤ G * (V - 3) := by
  let X : ℝ := cyclicXNum V G Rx Rj
  let Y : ℝ := cyclicYNum U V G (cyclicY U Rx Rj) Rj
  have hUpos : 0 < U := by linarith [r.U_lower]
  have hVnonneg : 0 ≤ V := by linarith [r.V_lower]
  have hGnonneg : 0 ≤ G := by linarith [r.G_lower]
  have hd : 0 ≤ U - V := sub_nonneg.mpr hVU
  have hX : 3 * U ≤ X := by
    dsimp [X]
    linarith [r.Rx'_lower]
  have hsumEq : X + Y + U * Rj = U * V := by
    dsimp [X, Y]
    exact cyclic_primed_R_sum U V G Rx Rj
  have hURj : 3 * U ≤ U * Rj := by
    nlinarith [mul_nonneg hUpos.le (sub_nonneg.mpr r.Rj_lower)]
  have hsum : X + Y ≤ U * (V - 3) := by
    nlinarith [hsumEq, hURj]
  have hGsum : G * (X + Y) ≤ G * (U * (V - 3)) :=
    mul_le_mul_of_nonneg_left hsum hGnonneg
  have hdX : 3 * U * (U - V) ≤ (U - V) * X := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hX)]
  have hCD : U ≤
      G * cyclicY U Rx Rj + cyclicW U V G * Rx := by
    linarith [r.CDR]
  have hCDscaled :
      U * V ≤
        G * Y + cyclicW U V G * X := by
    have hm := mul_le_mul_of_nonneg_left hCD hVnonneg
    rw [cyclic_CD_transport_R U V G Rx Rj] at ⊢
    nlinarith
  have hrewrite :
      G * Y + cyclicW U V G * X =
        G * (X + Y) - (U - V) * X := by
    unfold cyclicW
    ring
  have hcleared :
      U * (V + 3 * (U - V)) ≤ U * (G * (V - 3)) := by
    rw [hrewrite] at hCDscaled
    nlinarith [hCDscaled, hGsum, hdX]
  exact le_of_mul_le_mul_left hcleared hUpos

/-- The one-variable lower bound left after the high-row estimate. -/
private lemma high_n_scalar_lower {n : ℝ} (hn : 9 ≤ n) :
    (58 : ℝ) / 5 ≤ n + 1 + (n + 1) / (n - 3) := by
  have hden : 0 < n - 3 := by linarith
  have hfactor : 0 ≤ (n - 9) * (5 * n - 18) :=
    mul_nonneg (by linarith) (by linarith)
  have hpoly : 0 ≤ 5 * n ^ 2 - 63 * n + 164 := by
    nlinarith
  have hid :
      n + 1 + (n + 1) / (n - 3) - (58 : ℝ) / 5 =
        (5 * n ^ 2 - 63 * n + 164) / (5 * (n - 3)) := by
    field_simp
    <;> ring
  rw [← sub_nonneg]
  rw [hid]
  exact div_nonneg hpoly (by positivity)

/-- Scalar monotonicity for the `U ≤ V` orientation. -/
private lemma high_first_orientation
    {n d M : ℝ}
    (hn : 9 ≤ n) (hd : 0 ≤ d)
    (hM : n + 3 * d ≤ M * (n - 3)) :
    n + 1 + (n + 1) / (n - 3) ≤
      (M - d) + (n + d) + ((M - d) + n) / (n + d) := by
  have hA : 0 < n - 3 := by linarith
  have hnd : 0 < n + d := by linarith
  have hslack : 0 ≤ M * (n - 3) - (n + 3 * d) := by linarith
  have hnum : 0 ≤
      (n + d + 1) * (M * (n - 3) - (n + 3 * d)) +
        d * (n + 8 + 3 * d) :=
    add_nonneg
      (mul_nonneg (by linarith) hslack)
      (mul_nonneg hd (by nlinarith))
  have hid :
      ((M - d) + (n + d) + ((M - d) + n) / (n + d)) -
          (n + 1 + (n + 1) / (n - 3)) =
        ((n + d + 1) * (M * (n - 3) - (n + 3 * d)) +
          d * (n + 8 + 3 * d)) / ((n - 3) * (n + d)) := by
    field_simp
    <;> ring
  rw [← sub_nonneg]
  rw [hid]
  exact div_nonneg hnum (mul_nonneg hA.le hnd.le)

/-- Scalar monotonicity for the `V ≤ U` orientation. -/
private lemma high_second_orientation
    {n d M : ℝ}
    (hn : 9 ≤ n) (hd : 0 ≤ d)
    (hM : n + 3 * d ≤ M * (n - 3)) :
    n + 1 + (n + 1) / (n - 3) ≤
      M + n + (M + (n + d)) / n := by
  have hA : 0 < n - 3 := by linarith
  have hnpos : 0 < n := by linarith
  have hslack : 0 ≤ M * (n - 3) - (n + 3 * d) := by linarith
  have hnum : 0 ≤
      (n + 1) * (M * (n - 3) - (n + 3 * d)) + 4 * n * d :=
    add_nonneg
      (mul_nonneg (by linarith) hslack)
      (mul_nonneg (mul_nonneg (by norm_num) hnpos.le) hd)
  have hid :
      (M + n + (M + (n + d)) / n) -
          (n + 1 + (n + 1) / (n - 3)) =
        ((n + 1) * (M * (n - 3) - (n + 3 * d)) + 4 * n * d) /
          ((n - 3) * n) := by
    field_simp
    <;> ring
  rw [← sub_nonneg]
  rw [hid]
  exact div_nonneg hnum (mul_nonneg hA.le hnpos.le)

/--
The high-fan part of the orbit-I residual bound is analytic: no generated
`50t` certificate is needed once both fan totals are at least `9`.
-/
theorem CyclicLeaf50tDomain.bound_of_nine_le_min
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj)
    (hnine : (9 : ℝ) ≤ min U V) :
    (58 : ℝ) / 5 ≤ G + V + (G + U) / V := by
  have hU9 : (9 : ℝ) ≤ U := le_trans hnine (min_le_left U V)
  have hV9 : (9 : ℝ) ≤ V := le_trans hnine (min_le_right U V)
  by_cases hUV : U ≤ V
  · have hCD := r.high_CD_of_U_le_V hUV
    have hbase := high_n_scalar_lower hU9
    have horient := high_first_orientation hU9 (sub_nonneg.mpr hUV) hCD
    unfold cyclicW at horient
    have htarget :
        U + 1 + (U + 1) / (U - 3) ≤ G + V + (G + U) / V := by
      convert horient using 1 <;> ring
    exact hbase.trans htarget
  · have hVU : V ≤ U := le_of_not_ge hUV
    have hCD := r.high_CD_of_V_le_U hVU
    have hbase := high_n_scalar_lower hV9
    have horient := high_second_orientation hV9 (sub_nonneg.mpr hVU) hCD
    exact hbase.trans (by simpa [add_assoc, add_left_comm, add_comm] using horient)

end Heilbronn8.QuadHull
