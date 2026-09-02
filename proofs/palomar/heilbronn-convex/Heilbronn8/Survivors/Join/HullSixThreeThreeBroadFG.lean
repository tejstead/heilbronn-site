import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadInactive

/-!
# The four-boundary `F/G` wrapper for the broad `3 x 3` chamber

This file isolates the rational monotonicity argument used after the broad
chamber has been reduced to one lower and one upper bound for its central
split.  The difficult polynomial is deliberately not proved here.  Instead,
`HullSixThreeThreeBroadRawBoundary` records exactly the cleared raw-boundary
comparison which a separate polynomial adapter must supply.

There are two algebraic lower boundaries,

* `(y + 2) / U` for `L`, and
* `(x + 2) / v` for `ell`.

The physical boundaries are their maxima with one.  The proof below treats
all four active/inactive cases separately.  In particular, a mixed case never
continues a monotonicity argument below one.  It moves the corresponding
parameter of `F` to `x + 2` or `y + 2` and invokes the raw comparison there.
This is the domain-preserving replacement for the invalid global sequential
reduction.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The lower rational bound for the central split in the broad chamber. -/
noncomputable def hullSixThreeThreeBroadF (x y U v : ℝ) : ℝ :=
  (U * v * (x + y + 1) + U * x ^ 2 + v * y ^ 2 + x + y + 1) /
    ((U + y) * (v + x))

/-- The upper rational bound for the central split in the broad chamber. -/
noncomputable def hullSixThreeThreeBroadG (x y L ell : ℝ) : ℝ :=
  (x * y * (L + ell + x + y) - L * ell - x - y - 1) /
    ((L + y) * (ell + x))

/-- The hard input expected from the four-variable polynomial theorem.

The positivity and product-range assumptions used by that theorem remain
outside this predicate.  This predicate only records its cleared rational
conclusion, with the positivity domain of both fan parameters explicit. -/
def HullSixThreeThreeBroadRawBoundary (x y : ℝ) : Prop :=
  ∀ {U v : ℝ}, 1 ≤ U → 1 ≤ v →
    hullSixThreeThreeBroadG x y ((y + 2) / U) ((x + 2) / v) <
      hullSixThreeThreeBroadF x y U v

private theorem hullSixThreeThreeBroadF_sub_U
    {x y U₁ U₂ v : ℝ}
    (hU₁y : U₁ + y ≠ 0) (hU₂y : U₂ + y ≠ 0)
    (hvx : v + x ≠ 0) :
    hullSixThreeThreeBroadF x y U₂ v -
        hullSixThreeThreeBroadF x y U₁ v =
      (U₂ - U₁) * (x + 1) * (y * (v + x - 1) - 1) /
        ((U₂ + y) * (U₁ + y) * (v + x)) := by
  simp only [hullSixThreeThreeBroadF]
  field_simp [hU₁y, hU₂y, hvx]
  ring

private theorem hullSixThreeThreeBroadF_sub_v
    {x y U v₁ v₂ : ℝ}
    (hUy : U + y ≠ 0) (hv₁x : v₁ + x ≠ 0)
    (hv₂x : v₂ + x ≠ 0) :
    hullSixThreeThreeBroadF x y U v₂ -
        hullSixThreeThreeBroadF x y U v₁ =
      (v₂ - v₁) * (y + 1) * (x * (U + y - 1) - 1) /
        ((v₂ + x) * (v₁ + x) * (U + y)) := by
  simp only [hullSixThreeThreeBroadF]
  field_simp [hUy, hv₁x, hv₂x]
  ring

private theorem hullSixThreeThreeBroadG_sub_L
    {x y L₁ L₂ ell : ℝ}
    (hL₁y : L₁ + y ≠ 0) (hL₂y : L₂ + y ≠ 0)
    (hellx : ell + x ≠ 0) :
    hullSixThreeThreeBroadG x y L₂ ell -
        hullSixThreeThreeBroadG x y L₁ ell =
      -((L₂ - L₁) * (x + 1) * (y * (ell + x - 1) - 1)) /
        ((L₂ + y) * (L₁ + y) * (ell + x)) := by
  simp only [hullSixThreeThreeBroadG]
  field_simp [hL₁y, hL₂y, hellx]
  ring

private theorem hullSixThreeThreeBroadG_sub_ell
    {x y L ell₁ ell₂ : ℝ}
    (hLy : L + y ≠ 0) (hell₁x : ell₁ + x ≠ 0)
    (hell₂x : ell₂ + x ≠ 0) :
    hullSixThreeThreeBroadG x y L ell₂ -
        hullSixThreeThreeBroadG x y L ell₁ =
      -((ell₂ - ell₁) * (y + 1) * (x * (L + y - 1) - 1)) /
        ((ell₂ + x) * (ell₁ + x) * (L + y)) := by
  simp only [hullSixThreeThreeBroadG]
  field_simp [hLy, hell₁x, hell₂x]
  ring

/-- `F` is increasing in `U` on the physical domain.  Notice that the
other fan coordinate `v` is explicitly required to remain at least one. -/
theorem hullSixThreeThreeBroadF_mono_U
    {x y U₁ U₂ v : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : 1 ≤ x * y)
    (hU₁ : 1 ≤ U₁) (hU₁U₂ : U₁ ≤ U₂) (hv : 1 ≤ v) :
    hullSixThreeThreeBroadF x y U₁ v ≤
      hullSixThreeThreeBroadF x y U₂ v := by
  have hU₂ : 1 ≤ U₂ := le_trans hU₁ hU₁U₂
  have hU₁y : 0 < U₁ + y := by linarith
  have hU₂y : 0 < U₂ + y := by linarith
  have hvx : 0 < v + x := by linarith
  have hshift : x ≤ v + x - 1 := by linarith
  have hmul : y * x ≤ y * (v + x - 1) :=
    mul_le_mul_of_nonneg_left hshift (le_of_lt hy)
  have hbracket : 0 ≤ y * (v + x - 1) - 1 := by nlinarith
  have hnum :
      0 ≤ (U₂ - U₁) * (x + 1) * (y * (v + x - 1) - 1) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hU₁U₂) (by linarith)) hbracket
  have hden : 0 < (U₂ + y) * (U₁ + y) * (v + x) :=
    mul_pos (mul_pos hU₂y hU₁y) hvx
  have hid := hullSixThreeThreeBroadF_sub_U
    (x := x) (y := y) (U₁ := U₁) (U₂ := U₂) (v := v)
    (ne_of_gt hU₁y) (ne_of_gt hU₂y) (ne_of_gt hvx)
  have hdiff :
      0 ≤ hullSixThreeThreeBroadF x y U₂ v -
        hullSixThreeThreeBroadF x y U₁ v := by
    rw [hid]
    exact div_nonneg hnum (le_of_lt hden)
  linarith

/-- `F` is increasing in `v` on the physical domain.  The coordinate `U`
is kept at least one throughout the comparison. -/
theorem hullSixThreeThreeBroadF_mono_v
    {x y U v₁ v₂ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : 1 ≤ x * y)
    (hv₁ : 1 ≤ v₁) (hv₁v₂ : v₁ ≤ v₂) (hU : 1 ≤ U) :
    hullSixThreeThreeBroadF x y U v₁ ≤
      hullSixThreeThreeBroadF x y U v₂ := by
  have hv₂ : 1 ≤ v₂ := le_trans hv₁ hv₁v₂
  have hUy : 0 < U + y := by linarith
  have hv₁x : 0 < v₁ + x := by linarith
  have hv₂x : 0 < v₂ + x := by linarith
  have hshift : y ≤ U + y - 1 := by linarith
  have hmul : x * y ≤ x * (U + y - 1) :=
    mul_le_mul_of_nonneg_left hshift (le_of_lt hx)
  have hbracket : 0 ≤ x * (U + y - 1) - 1 := by nlinarith
  have hnum :
      0 ≤ (v₂ - v₁) * (y + 1) * (x * (U + y - 1) - 1) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hv₁v₂) (by linarith)) hbracket
  have hden : 0 < (v₂ + x) * (v₁ + x) * (U + y) :=
    mul_pos (mul_pos hv₂x hv₁x) hUy
  have hid := hullSixThreeThreeBroadF_sub_v
    (x := x) (y := y) (U := U) (v₁ := v₁) (v₂ := v₂)
    (ne_of_gt hUy) (ne_of_gt hv₁x) (ne_of_gt hv₂x)
  have hdiff :
      0 ≤ hullSixThreeThreeBroadF x y U v₂ -
        hullSixThreeThreeBroadF x y U v₁ := by
    rw [hid]
    exact div_nonneg hnum (le_of_lt hden)
  linarith

/-- `G` is decreasing in `L` while both `L` endpoints and the fixed
`ell` coordinate stay in the physical domain. -/
theorem hullSixThreeThreeBroadG_antitone_L
    {x y L₁ L₂ ell : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : 1 ≤ x * y)
    (hL₁ : 1 ≤ L₁) (hL₁L₂ : L₁ ≤ L₂) (hell : 1 ≤ ell) :
    hullSixThreeThreeBroadG x y L₂ ell ≤
      hullSixThreeThreeBroadG x y L₁ ell := by
  have hL₂ : 1 ≤ L₂ := le_trans hL₁ hL₁L₂
  have hL₁y : 0 < L₁ + y := by linarith
  have hL₂y : 0 < L₂ + y := by linarith
  have hellx : 0 < ell + x := by linarith
  have hshift : x ≤ ell + x - 1 := by linarith
  have hmul : y * x ≤ y * (ell + x - 1) :=
    mul_le_mul_of_nonneg_left hshift (le_of_lt hy)
  have hbracket : 0 ≤ y * (ell + x - 1) - 1 := by nlinarith
  have hnum :
      0 ≤ (L₂ - L₁) * (x + 1) * (y * (ell + x - 1) - 1) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hL₁L₂) (by linarith)) hbracket
  have hden : 0 < (L₂ + y) * (L₁ + y) * (ell + x) :=
    mul_pos (mul_pos hL₂y hL₁y) hellx
  have hid := hullSixThreeThreeBroadG_sub_L
    (x := x) (y := y) (L₁ := L₁) (L₂ := L₂) (ell := ell)
    (ne_of_gt hL₁y) (ne_of_gt hL₂y) (ne_of_gt hellx)
  have hdiff :
      hullSixThreeThreeBroadG x y L₂ ell -
          hullSixThreeThreeBroadG x y L₁ ell ≤ 0 := by
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) (le_of_lt hden)
  linarith

/-- `G` is decreasing in `ell` while both `ell` endpoints and the fixed
`L` coordinate stay in the physical domain. -/
theorem hullSixThreeThreeBroadG_antitone_ell
    {x y L ell₁ ell₂ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : 1 ≤ x * y)
    (hell₁ : 1 ≤ ell₁) (hell₁ell₂ : ell₁ ≤ ell₂) (hL : 1 ≤ L) :
    hullSixThreeThreeBroadG x y L ell₂ ≤
      hullSixThreeThreeBroadG x y L ell₁ := by
  have hell₂ : 1 ≤ ell₂ := le_trans hell₁ hell₁ell₂
  have hLy : 0 < L + y := by linarith
  have hell₁x : 0 < ell₁ + x := by linarith
  have hell₂x : 0 < ell₂ + x := by linarith
  have hshift : y ≤ L + y - 1 := by linarith
  have hmul : x * y ≤ x * (L + y - 1) :=
    mul_le_mul_of_nonneg_left hshift (le_of_lt hx)
  have hbracket : 0 ≤ x * (L + y - 1) - 1 := by nlinarith
  have hnum :
      0 ≤ (ell₂ - ell₁) * (y + 1) * (x * (L + y - 1) - 1) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hell₁ell₂) (by linarith)) hbracket
  have hden : 0 < (ell₂ + x) * (ell₁ + x) * (L + y) :=
    mul_pos (mul_pos hell₂x hell₁x) hLy
  have hid := hullSixThreeThreeBroadG_sub_ell
    (x := x) (y := y) (L := L) (ell₁ := ell₁) (ell₂ := ell₂)
    (ne_of_gt hLy) (ne_of_gt hell₁x) (ne_of_gt hell₂x)
  have hdiff :
      hullSixThreeThreeBroadG x y L ell₂ -
          hullSixThreeThreeBroadG x y L ell₁ ≤ 0 := by
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) (le_of_lt hden)
  linarith

private theorem hullSixThreeThreeBroadF_pos
    {x y U v : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hU : 1 ≤ U) (hv : 1 ≤ v) :
    0 < hullSixThreeThreeBroadF x y U v := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  simp only [hullSixThreeThreeBroadF]
  positivity

private theorem hullSixThreeThreeBroadG_nonpos_of_product_le_one
    {x y L ell : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x * y ≤ 1)
    (hL : 1 ≤ L) (hell : 1 ≤ ell) :
    hullSixThreeThreeBroadG x y L ell ≤ 0 := by
  have hfirst : 0 ≤ (1 - x * y) * (L + ell + x + y) := by
    exact mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have hsecond : 0 ≤ (L - 1) * (ell - 1) :=
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hell)
  have hnum :
      x * y * (L + ell + x + y) - L * ell - x - y - 1 ≤ 0 := by
    have hid :
        x * y * (L + ell + x + y) - L * ell - x - y - 1 =
          -((1 - x * y) * (L + ell + x + y)) -
            (L - 1) * (ell - 1) := by
      ring
    rw [hid]
    linarith
  have hden : 0 < (L + y) * (ell + x) := by positivity
  simp only [hullSixThreeThreeBroadG]
  exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)

private theorem hullSixThreeThreeBroad_inactive_gap
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy9 : x * y ≤ 9) :
    hullSixThreeThreeBroadG x y 1 1 <
      hullSixThreeThreeBroadF x y (y + 2) (x + 2) := by
  have hN := hullSixThreeThree_broad_inactiveNumerator_pos hx hy hxy9
  have hfactor : 0 < 4 * (x + 1) * (y + 1) := by positivity
  have hFy : y + 2 + y ≠ 0 := ne_of_gt (by linarith)
  have hFx : x + 2 + x ≠ 0 := ne_of_gt (by linarith)
  have hGy : (1 : ℝ) + y ≠ 0 := ne_of_gt (by linarith)
  have hGx : (1 : ℝ) + x ≠ 0 := ne_of_gt (by linarith)
  have hid :
      4 * (x + 1) * (y + 1) *
          (hullSixThreeThreeBroadF x y (y + 2) (x + 2) -
            hullSixThreeThreeBroadG x y 1 1) =
        4 * (x ^ 2 + y ^ 2) + 11 * (x + y) + 13 -
          2 * (x * y) * (x + y) - 3 * (x * y) := by
    simp only [hullSixThreeThreeBroadF, hullSixThreeThreeBroadG]
    field_simp [hFy, hFx, hGy, hGx]
    ring
  have hproduct :
      0 < 4 * (x + 1) * (y + 1) *
        (hullSixThreeThreeBroadF x y (y + 2) (x + 2) -
          hullSixThreeThreeBroadG x y 1 1) := by
    rw [hid]
    exact hN
  rcases mul_pos_iff.mp hproduct with hpos | hneg
  · linarith [hpos.2]
  · linarith [hfactor, hneg.1]

/-- Abstract four-case router for two decreasing physical variables bounded
below by `max 1` product boundaries.

This theorem contains no rational algebra.  Its monotonicity hypotheses state
the physical domains explicitly.  In either mixed case it stops the inactive
coordinate at one, changes the matching parameter of `F`, and applies the raw
comparison at that physical endpoint. -/
theorem hullSixThreeThree_broad_maxBoundary_noSandwich
    (F G : ℝ → ℝ → ℝ)
    {x y U v L ell B : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hU : 1 ≤ U) (hv : 1 ≤ v) (hL : 1 ≤ L) (hell : 1 ≤ ell)
    (hUL : y + 2 ≤ U * L) (hvell : x + 2 ≤ v * ell)
    (hFB : F U v ≤ B) (hBG : B ≤ G L ell)
    (hFU : ∀ {U₁ U₂ v}, 1 ≤ U₁ → U₁ ≤ U₂ → 1 ≤ v →
      F U₁ v ≤ F U₂ v)
    (hFv : ∀ {U v₁ v₂}, 1 ≤ U → 1 ≤ v₁ → v₁ ≤ v₂ →
      F U v₁ ≤ F U v₂)
    (hGL : ∀ {L₁ L₂ ell}, 1 ≤ L₁ → L₁ ≤ L₂ → 1 ≤ ell →
      G L₂ ell ≤ G L₁ ell)
    (hGell : ∀ {L ell₁ ell₂}, 1 ≤ L → 1 ≤ ell₁ → ell₁ ≤ ell₂ →
      G L ell₂ ≤ G L ell₁)
    (hraw : ∀ U' v', 1 ≤ U' → 1 ≤ v' →
      G ((y + 2) / U') ((x + 2) / v') < F U' v')
    (hinactive : G 1 1 < F (y + 2) (x + 2)) :
    False := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hy2 : 1 ≤ y + 2 := by linarith
  have hx2 : 1 ≤ x + 2 := by linarith
  have hy2pos : 0 < y + 2 := by linarith
  have hx2pos : 0 < x + 2 := by linarith
  have hLquot : (y + 2) / U ≤ L := by
    apply (div_le_iff₀ hUpos).2
    simpa only [mul_comm] using hUL
  have hellquot : (x + 2) / v ≤ ell := by
    apply (div_le_iff₀ hvpos).2
    simpa only [mul_comm] using hvell
  have hLstar : max 1 ((y + 2) / U) ≤ L := max_le hL hLquot
  have hellstar : max 1 ((x + 2) / v) ≤ ell := max_le hell hellquot
  have hGcut :
      G L ell ≤ G (max 1 ((y + 2) / U)) (max 1 ((x + 2) / v)) := by
    calc
      G L ell ≤ G (max 1 ((y + 2) / U)) ell :=
        hGL (le_max_left _ _) hLstar hell
      _ ≤ G (max 1 ((y + 2) / U)) (max 1 ((x + 2) / v)) :=
        hGell (le_max_left _ _) (le_max_left _ _) hellstar
  have hboundary :
      G (max 1 ((y + 2) / U)) (max 1 ((x + 2) / v)) < F U v := by
    by_cases hUa : U ≤ y + 2
    · have hLa : 1 ≤ (y + 2) / U := by
        apply (le_div_iff₀ hUpos).2
        simpa using hUa
      rw [max_eq_right hLa]
      by_cases hva : v ≤ x + 2
      · have hella : 1 ≤ (x + 2) / v := by
          apply (le_div_iff₀ hvpos).2
          simpa using hva
        rw [max_eq_right hella]
        exact hraw U v hU hv
      · have helli : (x + 2) / v ≤ 1 :=
          (div_le_one hvpos).2 (le_of_not_ge hva)
        rw [max_eq_left helli]
        have hr := hraw U (x + 2) hU hx2
        rw [div_self (ne_of_gt hx2pos)] at hr
        exact lt_of_lt_of_le hr (hFv hU hx2 (le_of_not_ge hva))
    · have hLi : (y + 2) / U ≤ 1 :=
        (div_le_one hUpos).2 (le_of_not_ge hUa)
      rw [max_eq_left hLi]
      by_cases hva : v ≤ x + 2
      · have hella : 1 ≤ (x + 2) / v := by
          apply (le_div_iff₀ hvpos).2
          simpa using hva
        rw [max_eq_right hella]
        have hr := hraw (y + 2) v hy2 hv
        rw [div_self (ne_of_gt hy2pos)] at hr
        exact lt_of_lt_of_le hr (hFU hy2 (le_of_not_ge hUa) hv)
      · have helli : (x + 2) / v ≤ 1 :=
          (div_le_one hvpos).2 (le_of_not_ge hva)
        rw [max_eq_left helli]
        calc
          G 1 1 < F (y + 2) (x + 2) := hinactive
          _ ≤ F U (x + 2) := hFU hy2 (le_of_not_ge hUa) hx2
          _ ≤ F U v := hFv hU hx2 (le_of_not_ge hva)
  have hGltF : G L ell < F U v := lt_of_le_of_lt hGcut hboundary
  exact (not_lt_of_ge (hFB.trans hBG)) hGltF

/-- Correct four-case `max 1` wrapper for the broad chamber.

`B` is the eliminated central split.  The two product inequalities put the
physical variables above their raw algebraic boundaries.  The hard
polynomial theorem is supplied through `hRaw`, and only after the elementary
branch `x*y ≤ 1` has been excluded. -/
theorem hullSixThreeThree_broad_product_ge_nine_of_rawBoundary
    {x y U v L ell B : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hU : 1 ≤ U) (hv : 1 ≤ v) (hL : 1 ≤ L) (hell : 1 ≤ ell)
    (hUL : y + 2 ≤ U * L) (hvell : x + 2 ≤ v * ell)
    (hFB : hullSixThreeThreeBroadF x y U v ≤ B)
    (hBG : B ≤ hullSixThreeThreeBroadG x y L ell)
    (hRaw : 1 < x * y → x * y < 9 →
      HullSixThreeThreeBroadRawBoundary x y) :
    9 ≤ x * y := by
  by_contra hnot
  have hxy9 : x * y < 9 := lt_of_not_ge hnot
  have hxy1 : 1 < x * y := by
    by_contra hnotOne
    have hxyLe : x * y ≤ 1 := le_of_not_gt hnotOne
    have hFpos : 0 < hullSixThreeThreeBroadF x y U v :=
      hullSixThreeThreeBroadF_pos hx hy hU hv
    have hGnonpos : hullSixThreeThreeBroadG x y L ell ≤ 0 :=
      hullSixThreeThreeBroadG_nonpos_of_product_le_one hx hy hxyLe hL hell
    linarith
  have hxy : 1 ≤ x * y := le_of_lt hxy1
  have hRawNow : HullSixThreeThreeBroadRawBoundary x y := hRaw hxy1 hxy9
  have hInactiveGap :
      hullSixThreeThreeBroadG x y 1 1 <
        hullSixThreeThreeBroadF x y (y + 2) (x + 2) :=
    hullSixThreeThreeBroad_inactive_gap hx hy (le_of_lt hxy9)
  exact hullSixThreeThree_broad_maxBoundary_noSandwich
    (F := fun U' v' ↦ hullSixThreeThreeBroadF x y U' v')
    (G := fun L' ell' ↦ hullSixThreeThreeBroadG x y L' ell')
    hx hy hU hv hL hell hUL hvell hFB hBG
    (fun hU₁ hU₁U₂ hv' ↦
      hullSixThreeThreeBroadF_mono_U hx hy hxy hU₁ hU₁U₂ hv')
    (fun hU' hv₁ hv₁v₂ ↦
      hullSixThreeThreeBroadF_mono_v hx hy hxy hv₁ hv₁v₂ hU')
    (fun hL₁ hL₁L₂ hell' ↦
      hullSixThreeThreeBroadG_antitone_L hx hy hxy hL₁ hL₁L₂ hell')
    (fun hL' hell₁ hell₁ell₂ ↦
      hullSixThreeThreeBroadG_antitone_ell hx hy hxy hell₁ hell₁ell₂ hL')
    (fun U' v' hU' hv' ↦ hRawNow hU' hv') hInactiveGap

end Heilbronn8
