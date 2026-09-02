import Heilbronn8.TriHull.Core

/-!
# Scalar algebra for the hull-five singleton sectors

This file contains the certificate-free real algebra used by the `2 + 1`
pentagon argument after the two diagonals of `A-B-X-C` have been drawn.
It deliberately contains no points, determinants, finite tables, or generated
data.  The geometric layer only has to supply the fan-area rows exposed by
`singleton_of_fan_rows` below.

All areas are doubled.  Thus an empty selected triangle has lower bound `2`,
a one-point triangle has lower bound `6`, and the desired quadrilateral bound
is `23`.
-/

namespace Heilbronn8.TriHull

/-! ## Small fan-row adapters

These lemmas isolate the only order reasoning needed after a determinant
identity has been expanded.  Keeping them here makes the geometric module a
collection of ring identities, sign extractions, and calls to these adapters.
-/

/-- The fixed outer-cell row.  In applications `X` is the doubled area of a
selected triangle and `alpha`, `gamma` are two positive fan pieces. -/
lemma singleton_fan_fixed_row
    {A alpha gamma U N X : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (halpha : alpha ≤ A - 4) (hgamma : 2 ≤ gamma) (hX : 2 ≤ X)
    (hid : A * X = alpha * U - gamma * N) :
    2 * (N + 4) ≤ (A - 4) * (U - 2) := by
  have halphaU : 0 ≤ (A - 4 - alpha) * U :=
    mul_nonneg (by linarith) hU
  have hAX : 0 ≤ A * (X - 2) :=
    mul_nonneg hA (by linarith)
  have hgammaN : 0 ≤ (gamma - 2) * N :=
    mul_nonneg (by linarith) hN
  nlinarith

/-- The sign-independent intrinsic row.  The sign of `X` chooses which of
the two adjacent fan cells receives the product lower bound. -/
lemma singleton_fan_sign_rows
    {A alpha beta Z D X : ℝ}
    (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hD : 0 ≤ D)
    (halphaLo : 2 ≤ alpha) (hbetaLo : 2 ≤ beta)
    (halphaHi : alpha ≤ A - 4) (hbetaHi : beta ≤ A - 4)
    (hX : 2 ≤ |X|) (hid : A * X = beta * D - alpha * Z) :
    2 * (D + 4) ≤ (A - 4) * (Z - 2) ∨
      2 * (Z + 4) ≤ (A - 4) * (D - 2) := by
  by_cases hXnonneg : 0 ≤ X
  · right
    have hXtwo : 2 ≤ X := by
      simpa [abs_of_nonneg hXnonneg] using hX
    have hbetaD : 0 ≤ (A - 4 - beta) * D :=
      mul_nonneg (by linarith) hD
    have hAX : 0 ≤ A * (X - 2) :=
      mul_nonneg hA (by linarith)
    have halphaZ : 0 ≤ (alpha - 2) * Z :=
      mul_nonneg (by linarith) hZ
    nlinarith
  · left
    have hXneg : X < 0 := lt_of_not_ge hXnonneg
    have hXtwo : 2 ≤ -X := by
      simpa [abs_of_neg hXneg] using hX
    have halphaZ : 0 ≤ (A - 4 - alpha) * Z :=
      mul_nonneg (by linarith) hZ
    have hbetaD : 0 ≤ (beta - 2) * D :=
      mul_nonneg (by linarith) hD
    have hAX : 0 ≤ A * (-X - 2) :=
      mul_nonneg hA (by linarith)
    nlinarith

/-- The strong inner-cell row.  It packages the extra positive fan term
which distinguishes the `AN`, `ZG`, and `ZN` leaves from the outer `AG`
leaf. -/
lemma singleton_fan_strong_row
    {Z alpha beta gamma U N V X : ℝ}
    (hZ : 0 ≤ Z) (hU : 0 ≤ U) (hN : 0 ≤ N) (hV : 0 ≤ V)
    (halpha : 2 ≤ alpha) (hgamma : 2 ≤ gamma)
    (hbeta : beta ≤ Z - 4) (hX : 2 ≤ X)
    (hid : Z * X = beta * U - gamma * N - alpha * V) :
    2 * (N + V + 4) ≤ (Z - 4) * (U - 2) := by
  have hbetaU : 0 ≤ (Z - 4 - beta) * U :=
    mul_nonneg (by linarith) hU
  have hZX : 0 ≤ Z * (X - 2) :=
    mul_nonneg hZ (by linarith)
  have hgammaN : 0 ≤ (gamma - 2) * N :=
    mul_nonneg (by linarith) hN
  have halphaV : 0 ≤ (alpha - 2) * V :=
    mul_nonneg (by linarith) hV
  nlinarith

/-- The denominator-free polynomial which closes the unique hard `AG` leaf. -/
def singletonHardF (a g d : ℝ) : ℝ :=
  ((a + d + 6) * (g + d + 6) - 23 * (d + 2)) * (a + 2) * (g + 2) -
    (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8)

/-- A rational weighted AM-GM estimate used to keep the hard leaf free of
square roots and divisions in its final polynomial. -/
lemma weighted_amgm_49_29 {x y d : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d)
    (hxy : 2 * (d + 6) ≤ x * y) :
    (257 : ℝ) / 29 - d ≤ x + (49 : ℝ) / 29 * y := by
  by_cases hlarge : (257 : ℝ) / 29 ≤ d
  · have hsum : 0 ≤ x + (49 : ℝ) / 29 * y :=
      add_nonneg hx (mul_nonneg (by norm_num) hy)
    linarith
  · have hdsmall : d < (257 : ℝ) / 29 := lt_of_not_ge hlarge
    let L : ℝ := x + (49 : ℝ) / 29 * y
    let R : ℝ := (257 : ℝ) / 29 - d
    have hL : 0 ≤ L := by
      dsimp [L]
      exact add_nonneg hx (mul_nonneg (by norm_num) hy)
    have hR : 0 < R := by
      dsimp [R]
      linarith
    have hamgm : 4 * ((49 : ℝ) / 29) * (x * y) ≤ L ^ 2 := by
      dsimp [L]
      nlinarith [sq_nonneg (x - (49 : ℝ) / 29 * y)]
    have hscaled :
        (392 : ℝ) / 29 * (d + 6) ≤
          4 * ((49 : ℝ) / 29) * (x * y) := by
      nlinarith [hxy]
    have hlow : (392 : ℝ) / 29 * (d + 6) ≤ L ^ 2 :=
      le_trans hscaled hamgm
    have hcoef : 0 < 26274 - 841 * d := by
      nlinarith [hdsmall]
    have hdcoef : 0 ≤ d * (26274 - 841 * d) :=
      mul_nonneg hd hcoef.le
    have hgap : 0 < 2159 + 26274 * d - 841 * d ^ 2 := by
      nlinarith [hdcoef]
    have hupp : R ^ 2 < (392 : ℝ) / 29 * (d + 6) := by
      dsimp [R]
      nlinarith [hgap]
    by_contra hnot
    have hLR : L < R := lt_of_not_ge hnot
    have hdiff : 0 < (R - L) * (R + L) :=
      mul_pos (sub_pos.mpr hLR) (by nlinarith [hL, hR])
    nlinarith [hlow, hupp, hdiff]

/-- Manifest positivity of the hard polynomial in its feasible chamber. -/
lemma singletonHardF_pos {a g d : ℝ}
    (ha : (29 : ℝ) / 10 < a) (hg : (29 : ℝ) / 10 < g)
    (hd : 0 ≤ d) :
    0 < singletonHardF a g d := by
  let A : ℝ := a - (29 : ℝ) / 10
  let G : ℝ := g - (29 : ℝ) / 10
  have hA : 0 < A := by dsimp [A]; linarith
  have hG : 0 < G := by dsimp [G]; linarith
  have hexpand :
      singletonHardF a g d =
        A * (23 * A * G + 2 * A * d + (787 : ℝ) / 10 * A +
          23 * G ^ 2 + 23 * G * d + (219 : ℝ) / 5 * G +
          2 * d ^ 2 + (523 : ℝ) / 10 * d + (12719 : ℝ) / 100) +
        G * (2 * G * d + (787 : ℝ) / 10 * G + 2 * d ^ 2 +
          (523 : ℝ) / 10 * d + (12719 : ℝ) / 100) +
        d * ((78 : ℝ) / 5 * d + (3227 : ℝ) / 100) +
        (7938 : ℝ) / 125 := by
    dsimp [singletonHardF, A, G]
    ring
  rw [hexpand]
  have hAterm : 0 ≤
      A * (23 * A * G + 2 * A * d + (787 : ℝ) / 10 * A +
        23 * G ^ 2 + 23 * G * d + (219 : ℝ) / 5 * G +
        2 * d ^ 2 + (523 : ℝ) / 10 * d + (12719 : ℝ) / 100) := by
    positivity
  have hGterm : 0 ≤
      G * (2 * G * d + (787 : ℝ) / 10 * G + 2 * d ^ 2 +
        (523 : ℝ) / 10 * d + (12719 : ℝ) / 100) := by
    positivity
  have hdterm : 0 ≤
      d * ((78 : ℝ) / 5 * d + (3227 : ℝ) / 100) := by
    positivity
  linarith only [hAterm, hGterm, hdterm]

/-- The hard outer/outer leaf.  The variables are the shifted fan areas
`a=A-4`, `g=G-4`, `z=Z-2`, `n=N-2`, `d=D-2`, `e=E-2`, and `u=U-2`. -/
lemma singleton_hard_AZ_GN
    {a g z n d e u K : ℝ}
    (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hz : 0 ≤ z) (hn : 0 ≤ n) (hd : 0 ≤ d)
    (he : 4 ≤ e) (hu : 4 ≤ u)
    (hK₁ : K = 10 + d + a + z + e)
    (hK₂ : K = 10 + d + g + n + u)
    (haz : 2 * (d + 6) ≤ a * z)
    (hgn : 2 * (d + 6) ≤ g * n)
    (hau : 2 * (n + 6) ≤ a * u)
    (hge : 2 * (z + 6) ≤ g * e)
    (hid : K * (d + 2) =
      (a + d + 6) * (g + d + 6) - (z + 2) * (n + 2)) :
    23 ≤ K := by
  by_contra hnot
  have hKlt : K < 23 := lt_of_not_ge hnot
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hg0 : 0 < g := lt_of_lt_of_le (by norm_num) hg
  have he0 : 0 ≤ e := le_trans (by norm_num) he
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu

  have ha29 : (29 : ℝ) / 10 < a := by
    by_contra hanot
    have hale : a ≤ (29 : ℝ) / 10 := le_of_not_gt hanot
    have haupper : a * u ≤ ((29 : ℝ) / 10) * u :=
      mul_le_mul_of_nonneg_right hale hu0
    have hulower : 20 * (n + 6) ≤ 29 * u := by
      nlinarith [hau, haupper]
    have hsumlt : 29 * g + 49 * n < 257 - 29 * d := by
      nlinarith [hK₂, hKlt, hulower]
    have hw := weighted_amgm_49_29 (by linarith [hg]) hn hd hgn
    nlinarith

  have hg29 : (29 : ℝ) / 10 < g := by
    by_contra hgnot
    have hgle : g ≤ (29 : ℝ) / 10 := le_of_not_gt hgnot
    have hgupper : g * e ≤ ((29 : ℝ) / 10) * e :=
      mul_le_mul_of_nonneg_right hgle he0
    have helower : 20 * (z + 6) ≤ 29 * e := by
      nlinarith [hge, hgupper]
    have hsumlt : 29 * a + 49 * z < 257 - 29 * d := by
      nlinarith [hK₁, hKlt, helower]
    have hw := weighted_amgm_49_29 (by linarith [ha]) hz hd haz
    nlinarith

  have hzslack : 0 < 13 - d - a - z - e := by
    nlinarith [hK₁, hKlt]
  have hzmul : 0 < g * (13 - d - a - z - e) :=
    mul_pos hg0 hzslack
  have hzup :
      (g + 2) * (z + 2) < g * (15 - d - a) - 8 := by
    nlinarith [hge, hzmul]

  have hnslack : 0 < 13 - d - g - n - u := by
    nlinarith [hK₂, hKlt]
  have hnmul : 0 < a * (13 - d - g - n - u) :=
    mul_pos ha0 hnslack
  have hnup :
      (a + 2) * (n + 2) < a * (15 - d - g) - 8 := by
    nlinarith [hau, hnmul]

  have hleftz : 0 < (g + 2) * (z + 2) :=
    mul_pos (by linarith) (by linarith)
  have hleftn : 0 < (a + 2) * (n + 2) :=
    mul_pos (by linarith) (by linarith)
  have hrightz : 0 < g * (15 - d - a) - 8 :=
    lt_trans hleftz hzup
  have hfirst :
      ((g + 2) * (z + 2)) * ((a + 2) * (n + 2)) <
        (g * (15 - d - a) - 8) * ((a + 2) * (n + 2)) :=
    mul_lt_mul_of_pos_right hzup hleftn
  have hsecond :
      (g * (15 - d - a) - 8) * ((a + 2) * (n + 2)) <
        (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8) :=
    mul_lt_mul_of_pos_left hnup hrightz
  have hprod :
      (a + 2) * (g + 2) * (z + 2) * (n + 2) <
        (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8) := by
    calc
      (a + 2) * (g + 2) * (z + 2) * (n + 2) =
          ((g + 2) * (z + 2)) * ((a + 2) * (n + 2)) := by ring
      _ < (g * (15 - d - a) - 8) * ((a + 2) * (n + 2)) := hfirst
      _ < (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8) := hsecond

  have hd2 : 0 < d + 2 := by linarith
  have hKprod : K * (d + 2) < 23 * (d + 2) :=
    mul_lt_mul_of_pos_right hKlt hd2
  have hcore :
      (a + d + 6) * (g + d + 6) - 23 * (d + 2) <
        (z + 2) * (n + 2) := by
    nlinarith [hid, hKprod]
  have hfactor : 0 < (a + 2) * (g + 2) :=
    mul_pos (by linarith) (by linarith)
  have hcoremul := mul_lt_mul_of_pos_left hcore hfactor
  have hchain :
      (a + 2) * (g + 2) *
          ((a + d + 6) * (g + d + 6) - 23 * (d + 2)) <
        (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8) := by
    calc
      (a + 2) * (g + 2) *
          ((a + d + 6) * (g + d + 6) - 23 * (d + 2)) <
          (a + 2) * (g + 2) * ((z + 2) * (n + 2)) := hcoremul
      _ = (a + 2) * (g + 2) * (z + 2) * (n + 2) := by ring
      _ < (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8) := hprod
  have hFid : singletonHardF a g d =
      (a + 2) * (g + 2) *
          ((a + d + 6) * (g + d + 6) - 23 * (d + 2)) -
        (g * (15 - d - a) - 8) * (a * (15 - d - g) - 8) := by
    dsimp [singletonHardF]
    ring
  have hFneg : singletonHardF a g d < 0 := by
    rw [hFid]
    linarith only [hchain]
  have hFpos := singletonHardF_pos ha29 hg29 hd
  linarith

/-- A hard `Z` row on one side and a `D` row on the other cannot occur below
`23`.  Swapping the two sides gives the other mixed-sign leaf. -/
lemma singleton_shifted_mixed
    {a g z n d e u K : ℝ}
    (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hz : 0 ≤ z) (hn : 0 ≤ n) (hd : 0 ≤ d)
    (he : 4 ≤ e) (hu : 4 ≤ u)
    (hK₁ : K = 10 + d + a + z + e)
    (hK₂ : K = 10 + d + g + n + u)
    (haz : 2 * (d + 6) ≤ a * z)
    (hgd : 2 * (n + 6) ≤ g * d) :
    23 ≤ K := by
  by_contra hnot
  have hKlt : K < 23 := lt_of_not_ge hnot
  have hsumaz : a + z < 9 - d := by nlinarith [hK₁, he]
  have hsumgn : g + n < 9 - d := by nlinarith [hK₂, hu]
  have hsq : 4 * (a * z) ≤ (a + z) ^ 2 := by
    nlinarith [sq_nonneg (a - z)]
  have hsumpos : 0 < 9 - d := by nlinarith [ha, hz, hsumaz]
  have hdiff : 0 < (9 - d - (a + z)) * (9 - d + (a + z)) :=
    mul_pos (by linarith) (by nlinarith [ha, hz])
  have hquad : 0 < d ^ 2 - 26 * d + 33 := by
    nlinarith [haz, hsq, hdiff]
  have hdlt : d < (3 : ℝ) / 2 := by
    by_contra hdnot
    have hdge : (3 : ℝ) / 2 ≤ d := le_of_not_gt hdnot
    have hd9 : d < 9 := by linarith
    have hfac :
        (d - (3 : ℝ) / 2) * (d - (49 : ℝ) / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith [hquad, hfac]
  have hgd12 : 12 ≤ g * d := by nlinarith [hgd, hn]
  have hd0 : 0 < d := by
    by_contra hdz
    have : d = 0 := le_antisymm (le_of_not_gt hdz) hd
    nlinarith [hgd12]
  have hgup : g < 9 - d := by nlinarith [hsumgn, hn]
  have hgdlt : g * d < d * (9 - d) := by
    simpa [mul_comm] using mul_lt_mul_of_pos_right hgup hd0
  have hfac :
      0 < (d - (3 : ℝ) / 2) * (d - (15 : ℝ) / 2) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hbound : d * (9 - d) < (45 : ℝ) / 4 := by
    nlinarith [hfac]
  nlinarith

/-- The double-`D` outer leaf.  The negative discriminant gives the stronger
strict lower bound needed for `23`. -/
lemma singleton_shifted_DD
    {a g z n d e u K : ℝ}
    (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hz : 0 ≤ z) (hn : 0 ≤ n) (hd : 0 ≤ d)
    (he : 4 ≤ e) (hu : 4 ≤ u)
    (hK₁ : K = 10 + d + a + z + e)
    (hK₂ : K = 10 + d + g + n + u)
    (had : 2 * (z + 6) ≤ a * d)
    (hgd : 2 * (n + 6) ≤ g * d)
    (hid : K * (d + 2) =
      (a + d + 6) * (g + d + 6) - (z + 2) * (n + 2)) :
    23 ≤ K := by
  by_contra hnot
  have hKlt : K < 23 := lt_of_not_ge hnot
  have hzup : z + 2 < 11 - a - d := by nlinarith [hK₁, he]
  have hnup : n + 2 < 11 - g - d := by nlinarith [hK₂, hu]
  have hzpos : 0 < z + 2 := by linarith
  have hnpos : 0 < n + 2 := by linarith
  have hrz : 0 < 11 - a - d := lt_trans hzpos hzup
  have hfirst := mul_lt_mul_of_pos_right hzup hnpos
  have hsecond := mul_lt_mul_of_pos_left hnup hrz
  have hprod :
      (z + 2) * (n + 2) < (11 - a - d) * (11 - g - d) :=
    lt_trans hfirst hsecond
  have hlower :
      17 * (a + g + 2 * d) - 85 < K * (d + 2) := by
    nlinarith [hid, hprod]
  have hd0 : 0 < d := by
    have had12 : 12 ≤ a * d := by nlinarith [had, hz]
    by_contra hdz
    have : d = 0 := le_antisymm (le_of_not_gt hdz) hd
    nlinarith
  have hdagsum : 24 ≤ d * (a + g) := by
    have ha12 : 12 ≤ a * d := by nlinarith [had, hz]
    have hg12 : 12 ≤ g * d := by nlinarith [hgd, hn]
    nlinarith
  have hKup : K * (d + 2) < 23 * (d + 2) :=
    mul_lt_mul_of_pos_right hKlt (by linarith)
  have hbad : 11 * d ^ 2 - 131 * d + 408 < 0 := by
    have hmul := mul_lt_mul_of_pos_right
      (lt_trans hlower hKup) hd0
    nlinarith [hdagsum]
  have hdisc := sq_nonneg (22 * d - 131)
  nlinarith [hbad, hdisc]

/-- The mixed occupied-sector scalar lemma.  It is used directly for `ZG`
and, after swapping the two diagonal triangles, for `AN`. -/
lemma singleton_mixed_strong
    {x z r T V E U K : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hr : 0 ≤ r)
    (hT : z + 8 ≤ T)
    (hV : V = x + r + 8)
    (hxr : 12 ≤ x * r)
    (hE : 2 * (z + 8) ≤ x * (E - 2))
    (hU : 2 * (V + 6) ≤ z * (U - 2))
    (hKT : K = T + E) (hKV : K = V + U) :
    23 ≤ K := by
  by_contra hnot
  have hKlt : K < 23 := lt_of_not_ge hnot
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  let y : ℝ := x + 12 / x
  have hxne : x ≠ 0 := hx0.ne'
  have hyrel : x * y = x ^ 2 + 12 := by
    dsimp [y]
    field_simp [hxne] <;> ring
  have hy0 : 0 < y := by
    dsimp [y]
    positivity
  have hdiv : 12 / x ≤ r := by
    apply (div_le_iff₀ hx0).2
    simpa [mul_comm] using hxr
  have hyV : y + 8 ≤ V := by
    dsimp [y]
    nlinarith [hV, hdiv]
  have hzup : z * (x + 2) < 13 * x - 16 := by
    have hEup : E - 2 < 13 - z := by nlinarith [hKT, hKlt, hT]
    have hmul : x * (E - 2) < x * (13 - z) :=
      mul_lt_mul_of_pos_left hEup hx0
    nlinarith only [hE, hmul]
  have hylow : 2 * (y + 14) < z * (13 - y) := by
    have hUup : U - 2 < 13 - y := by nlinarith [hKV, hKlt, hyV]
    have hz0 : 0 < z := by linarith only [hz]
    have hmul : z * (U - 2) < z * (13 - y) :=
      mul_lt_mul_of_pos_left hUup hz0
    nlinarith only [hU, hyV, hmul]
  have h13y : 0 < 13 - y := by
    have : 0 < z * (13 - y) := lt_of_lt_of_le
      (by nlinarith [hy0] : 0 < 2 * (y + 14)) hylow.le
    rcases (mul_pos_iff.mp this) with h | h
    · exact h.2
    · linarith [h.1, hz]
  have hx2 : 0 < x + 2 := by linarith
  have hcross₁ := mul_lt_mul_of_pos_right hylow hx2
  have hcross₂ := mul_lt_mul_of_pos_right hzup h13y
  have hcross :
      2 * (y + 14) * (x + 2) < (13 * x - 16) * (13 - y) := by
    calc
      2 * (y + 14) * (x + 2) < z * (13 - y) * (x + 2) := hcross₁
      _ = z * (x + 2) * (13 - y) := by ring
      _ < (13 * x - 16) * (13 - y) := hcross₂
  have hpoly : 0 < 5 * x ^ 3 - 51 * x ^ 2 + 148 * x - 48 := by
    have hfac : 0 ≤ (x - 5) ^ 2 * (5 * x - 1) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [hx])
    nlinarith [hfac]
  have hxgap :
      x * (2 * (y + 14) * (x + 2) -
        (13 * x - 16) * (13 - y)) =
          3 * (5 * x ^ 3 - 51 * x ^ 2 + 148 * x - 48) := by
    dsimp [y]
    field_simp [hxne] <;> ring
  have hxgappos :
      0 < x * (2 * (y + 14) * (x + 2) -
        (13 * x - 16) * (13 - y)) := by
    nlinarith [hxgap, hpoly]
  have hgap :
      0 < 2 * (y + 14) * (x + 2) - (13 * x - 16) * (13 - y) := by
    rcases (mul_pos_iff.mp hxgappos) with h | h
    · exact h.2
    · linarith [h.1, hx0]
  linarith

/-- The inner/inner occupied sectors close without the two-point constant or
maximality: the two strong fan rows alone are inconsistent below `23`. -/
lemma singleton_inner_inner
    {z n T V E U K : ℝ}
    (hz : 2 ≤ z) (hn : 2 ≤ n)
    (hT : z + 8 ≤ T) (hV : n + 8 ≤ V)
    (hU : 4 * (n + 8) ≤ z * (U - 2))
    (hE : 4 * (z + 8) ≤ n * (E - 2))
    (hKT : K = T + E) (hKV : K = V + U) :
    23 ≤ K := by
  by_contra hnot
  have hKlt : K < 23 := lt_of_not_ge hnot
  rcases le_total n z with hnz | hzn
  · have hEup : E - 2 < 13 - z := by nlinarith [hKT, hKlt, hT]
    have hn0 : 0 < n := by linarith only [hn]
    have hmul : n * (E - 2) < n * (13 - z) :=
      mul_lt_mul_of_pos_left hEup hn0
    have horder : 13 - z ≤ 13 - n := by linarith only [hnz]
    have hnnonneg : 0 ≤ n := by linarith only [hn]
    have hmono : n * (13 - z) ≤ n * (13 - n) :=
      mul_le_mul_of_nonneg_left horder hnnonneg
    have hbad : 4 * (n + 8) < n * (13 - n) := by
      calc
        4 * (n + 8) ≤ 4 * (z + 8) := by linarith only [hnz]
        _ ≤ n * (E - 2) := hE
        _ < n * (13 - z) := hmul
        _ ≤ n * (13 - n) := hmono
    have hreverse : n * (13 - n) ≤ 4 * (n + 8) := by
      nlinarith only [sq_nonneg (n - (9 : ℝ) / 2)]
    exact (not_lt_of_ge hreverse) hbad
  · have hUup : U - 2 < 13 - n := by nlinarith [hKV, hKlt, hV]
    have hz0 : 0 < z := by linarith only [hz]
    have hmul : z * (U - 2) < z * (13 - n) :=
      mul_lt_mul_of_pos_left hUup hz0
    have horder : 13 - n ≤ 13 - z := by linarith only [hzn]
    have hznonneg : 0 ≤ z := by linarith only [hz]
    have hmono : z * (13 - n) ≤ z * (13 - z) :=
      mul_le_mul_of_nonneg_left horder hznonneg
    have hbad : 4 * (z + 8) < z * (13 - z) := by
      calc
        4 * (z + 8) ≤ 4 * (n + 8) := by linarith only [hzn]
        _ ≤ z * (U - 2) := hU
        _ < z * (13 - n) := hmul
        _ ≤ z * (13 - z) := hmono
    have hreverse : z * (13 - z) ≤ 4 * (z + 8) := by
      nlinarith only [sq_nonneg (z - (9 : ℝ) / 2)]
    exact (not_lt_of_ge hreverse) hbad

/-- Complete scalar dispatcher for the singleton diagonal sectors.

`A,Z,D` are the `R`-fan cells in `ABC`; `G,N,D` are those in `AXC`.
The two alternatives in `hP` and `hQ` are exactly the strict fan placements
of the points in `ABO` and `XCO`, including the determinant sign split when
the occupied cell is outer. -/
theorem singleton_of_fan_rows
    {A Z D G N E U K : ℝ}
    (hA : 2 ≤ A) (hZ : 2 ≤ Z) (hD : 2 ≤ D)
    (hG : 2 ≤ G) (hN : 2 ≤ N)
    (hE : 6 ≤ E) (hU : 6 ≤ U)
    (hK₁ : K = A + Z + D + E)
    (hK₂ : K = G + N + D + U)
    (hid : K * D = (A + D) * (G + D) - Z * N)
    (hP :
      (6 ≤ A ∧ 2 * (N + 4) ≤ (A - 4) * (U - 2) ∧
        (2 * (D + 4) ≤ (A - 4) * (Z - 2) ∨
          2 * (Z + 4) ≤ (A - 4) * (D - 2))) ∨
      (6 ≤ Z ∧
        2 * (N + (G + N + D) + 4) ≤ (Z - 4) * (U - 2)))
    (hQ :
      (6 ≤ G ∧ 2 * (Z + 4) ≤ (G - 4) * (E - 2) ∧
        (2 * (D + 4) ≤ (G - 4) * (N - 2) ∨
          2 * (N + 4) ≤ (G - 4) * (D - 2))) ∨
      (6 ≤ N ∧
        2 * (Z + (A + Z + D) + 4) ≤ (N - 4) * (E - 2))) :
    23 ≤ K := by
  rcases hP with hPA | hPZ
  · rcases hPA with ⟨hA6, hAU, hAsign⟩
    rcases hQ with hQG | hQN
    · rcases hQG with ⟨hG6, hGE, hGsign⟩
      rcases hAsign with hAZ | hAD
      · rcases hGsign with hGN | hGD
        · refine singleton_hard_AZ_GN
              (a := A - 4) (g := G - 4) (z := Z - 2) (n := N - 2)
              (d := D - 2) (e := E - 2) (u := U - 2) (K := K)
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · linarith only [hA6]
          · linarith only [hG6]
          · linarith only [hZ]
          · linarith only [hN]
          · linarith only [hD]
          · linarith only [hE]
          · linarith only [hU]
          · linarith only [hK₁]
          · linarith only [hK₂]
          · nlinarith only [hAZ]
          · nlinarith only [hGN]
          · nlinarith only [hAU]
          · nlinarith only [hGE]
          · convert hid using 1 <;> ring
        · refine singleton_shifted_mixed
              (a := A - 4) (g := G - 4) (z := Z - 2) (n := N - 2)
              (d := D - 2) (e := E - 2) (u := U - 2) (K := K)
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · linarith only [hA6]
          · linarith only [hG6]
          · linarith only [hZ]
          · linarith only [hN]
          · linarith only [hD]
          · linarith only [hE]
          · linarith only [hU]
          · linarith only [hK₁]
          · linarith only [hK₂]
          · nlinarith only [hAZ]
          · nlinarith only [hGD]
      · rcases hGsign with hGN | hGD
        · refine singleton_shifted_mixed
              (a := G - 4) (g := A - 4) (z := N - 2) (n := Z - 2)
              (d := D - 2) (e := U - 2) (u := E - 2) (K := K)
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · linarith only [hG6]
          · linarith only [hA6]
          · linarith only [hN]
          · linarith only [hZ]
          · linarith only [hD]
          · linarith only [hU]
          · linarith only [hE]
          · linarith only [hK₂]
          · linarith only [hK₁]
          · nlinarith only [hGN]
          · nlinarith only [hAD]
        · refine singleton_shifted_DD
              (a := A - 4) (g := G - 4) (z := Z - 2) (n := N - 2)
              (d := D - 2) (e := E - 2) (u := U - 2) (K := K)
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · linarith only [hA6]
          · linarith only [hG6]
          · linarith only [hZ]
          · linarith only [hN]
          · linarith only [hD]
          · linarith only [hE]
          · linarith only [hU]
          · linarith only [hK₁]
          · linarith only [hK₂]
          · nlinarith only [hAD]
          · nlinarith only [hGD]
          · convert hid using 1 <;> ring
    · rcases hQN with ⟨hN6, hNE⟩
      rcases hAsign with hAZ | hAD
      · have hADnonneg : 0 ≤ (A - 4) * (D - 2) :=
          mul_nonneg (by linarith) (by linarith)
        refine singleton_mixed_strong
            (x := A - 4) (z := N - 4)
            (r := (Z - 2) + (D - 2))
            (T := G + N + D) (V := A + Z + D)
            (E := U) (U := E) (K := K)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · linarith only [hA6]
        · linarith only [hN6]
        · linarith only [hZ, hD]
        · linarith only [hG, hD]
        · ring
        · calc
            12 ≤ (A - 4) * (Z - 2) := by
              nlinarith only [hAZ, hD]
            _ ≤ (A - 4) * ((Z - 2) + (D - 2)) := by
              rw [mul_add]
              linarith only [hADnonneg]
        · nlinarith only [hAU]
        · nlinarith only [hNE, hZ]
        · linarith only [hK₂]
        · linarith only [hK₁]
      · have hAZnonneg : 0 ≤ (A - 4) * (Z - 2) :=
          mul_nonneg (by linarith) (by linarith)
        refine singleton_mixed_strong
            (x := A - 4) (z := N - 4)
            (r := (Z - 2) + (D - 2))
            (T := G + N + D) (V := A + Z + D)
            (E := U) (U := E) (K := K)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · linarith only [hA6]
        · linarith only [hN6]
        · linarith only [hZ, hD]
        · linarith only [hG, hD]
        · ring
        · calc
            12 ≤ (A - 4) * (D - 2) := by
              nlinarith only [hAD, hZ]
            _ ≤ (A - 4) * ((Z - 2) + (D - 2)) := by
              rw [mul_add]
              linarith only [hAZnonneg]
        · nlinarith only [hAU]
        · nlinarith only [hNE, hZ]
        · linarith only [hK₂]
        · linarith only [hK₁]
  · rcases hPZ with ⟨hZ6, hZU⟩
    rcases hQ with hQG | hQN
    · rcases hQG with ⟨hG6, hGE, hGsign⟩
      rcases hGsign with hGN | hGD
      · have hGDnonneg : 0 ≤ (G - 4) * (D - 2) :=
          mul_nonneg (by linarith) (by linarith)
        refine singleton_mixed_strong
            (x := G - 4) (z := Z - 4)
            (r := (N - 2) + (D - 2))
            (T := A + Z + D) (V := G + N + D)
            (E := E) (U := U) (K := K)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · linarith only [hG6]
        · linarith only [hZ6]
        · linarith only [hN, hD]
        · linarith only [hA, hD]
        · ring
        · calc
            12 ≤ (G - 4) * (N - 2) := by
              nlinarith only [hGN, hD]
            _ ≤ (G - 4) * ((N - 2) + (D - 2)) := by
              rw [mul_add]
              linarith only [hGDnonneg]
        · nlinarith only [hGE]
        · nlinarith only [hZU, hN]
        · linarith only [hK₁]
        · linarith only [hK₂]
      · have hGNnonneg : 0 ≤ (G - 4) * (N - 2) :=
          mul_nonneg (by linarith) (by linarith)
        refine singleton_mixed_strong
            (x := G - 4) (z := Z - 4)
            (r := (N - 2) + (D - 2))
            (T := A + Z + D) (V := G + N + D)
            (E := E) (U := U) (K := K)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · linarith only [hG6]
        · linarith only [hZ6]
        · linarith only [hN, hD]
        · linarith only [hA, hD]
        · ring
        · calc
            12 ≤ (G - 4) * (D - 2) := by
              nlinarith only [hGD, hN]
            _ ≤ (G - 4) * ((N - 2) + (D - 2)) := by
              rw [mul_add]
              linarith only [hGNnonneg]
        · nlinarith only [hGE]
        · nlinarith only [hZU, hN]
        · linarith only [hK₁]
        · linarith only [hK₂]
    · rcases hQN with ⟨hN6, hNE⟩
      refine singleton_inner_inner
        (z := Z - 4) (n := N - 4)
        (T := A + Z + D) (V := G + N + D)
        (E := E) (U := U) (K := K)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · linarith only [hZ6]
      · linarith only [hN6]
      · linarith only [hA, hD]
      · linarith only [hG, hD]
      · nlinarith only [hZU, hG, hD]
      · nlinarith only [hNE, hA, hD]
      · linarith only [hK₁]
      · linarith only [hK₂]

end Heilbronn8.TriHull
