import Heilbronn8.TriHull.HullSevenTransferProducer

/-!
# Endpoint-only high point for the hull-seven transfer

This file extracts the high-point construction from the chord selector.  Its
input is deliberately limited to the two endpoint recurrences and endpoint
caps, the three consecutive ear caps, and the relevant unit floors.  In
particular, it contains no central `L * R` recurrence, closing recurrence, or
area hypothesis.

The output produces the two positive parameters; callers do not supply them.
Besides the surrogate-product bound, it records denominator-free bounds for
the two long chords.  Those bounds are convenient for consumers which want to
multiply through by `(1 + t) * (1 + w)` without introducing divisions.
-/

namespace Heilbronn8.TriHull

/-- Exactly the endpoint data needed to construct the hull-seven high point.

This is the projection of `HullSevenChordInput` obtained by deleting the
central recurrence, closing recurrence, closing-cell variables, and area
bound. -/
structure HullSevenEndpointHighPointInput where
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
  l : ℝ
  m : ℝ
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
  l_ge : 1 ≤ l
  m_ge : 1 ≤ m
  p_ear : p ≤ A + B - 1
  q_ear : q ≤ B + C - 1
  r_ear : r ≤ C + D - 1
  L_rec : B * L = q * p - A * C
  R_rec : C * R = q * r - D * B
  left_endpoint : A * l + a0 * q ≤ L * (a0 + A - 1)
  right_endpoint : D * m + a5 * q ≤ R * (a5 + D - 1)

/-- Forget the central and closing data of a full chord input. -/
def HullSevenEndpointHighPointInput.ofChordInput {H : ℝ}
    (X : HullSevenChordInput H) : HullSevenEndpointHighPointInput where
  a0 := X.a0
  A := X.A
  B := X.B
  C := X.C
  D := X.D
  a5 := X.a5
  p := X.p
  q := X.q
  r := X.r
  L := X.L
  R := X.R
  l := X.l
  m := X.m
  a0_ge := X.a0_ge
  A_ge := X.A_ge
  B_ge := X.B_ge
  C_ge := X.C_ge
  D_ge := X.D_ge
  a5_ge := X.a5_ge
  p_ge := X.p_ge
  q_ge := X.q_ge
  r_ge := X.r_ge
  L_ge := X.L_ge
  R_ge := X.R_ge
  l_ge := X.l_ge
  m_ge := X.m_ge
  p_ear := X.p_ear
  q_ear := X.q_ear
  r_ear := X.r_ear
  L_rec := X.L_rec
  R_rec := X.R_rec
  left_endpoint := X.left_endpoint
  right_endpoint := X.right_endpoint

/-- The endpoint-only high point.  The scaled inequalities are equivalent to
the two pointwise surrogate bounds, but are stated without denominators. -/
structure HullSevenEndpointHighPointOutput
    (X : HullSevenEndpointHighPointInput) where
  t : ℝ
  w : ℝ
  t_pos : 0 < t
  w_pos : 0 < w
  sum_eq : t + w = X.q - 1
  left_outer : 1 ≤ (X.A - 1) * t
  right_outer : 1 ≤ (X.D - 1) * w
  left_scaled : X.L * (1 + t) ≤ t * (X.A + X.q)
  right_scaled : X.R * (1 + w) ≤ w * (X.D + X.q)
  product_lower :
    X.L * X.R ≤ hullSevenSurrogateP X.A X.D X.q (t * w)

private lemma hullSevenEndpoint_surrogateL_strictMono {s q x y : ℝ}
    (hsq : 0 < q + s + 1) (hx : -1 < x) (hxy : x < y) :
    hullSevenSurrogateL s x q < hullSevenSurrogateL s y q := by
  have hy : -1 < y := lt_trans hx hxy
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  have hden : 0 < (x + 1) * (y + 1) := mul_pos hx1 hy1
  have hid :
      hullSevenSurrogateL s y q - hullSevenSurrogateL s x q =
        (y - x) * (q + s + 1) / ((x + 1) * (y + 1)) := by
    unfold hullSevenSurrogateL
    field_simp [hx1.ne', hy1.ne']
    ring
  rw [← sub_pos, hid]
  exact div_pos (mul_pos (sub_pos.mpr hxy) hsq) hden

private lemma hullSevenEndpoint_surrogateL_mono {s q x y : ℝ}
    (hsq : 0 < q + s + 1) (hx : -1 < x) (hxy : x ≤ y) :
    hullSevenSurrogateL s x q ≤ hullSevenSurrogateL s y q := by
  rcases hxy.eq_or_lt with h | h
  · subst y
    exact le_rfl
  · exact (hullSevenEndpoint_surrogateL_strictMono hsq hx h).le

private lemma hullSevenEndpoint_surrogateL_reflect_order {s q x y : ℝ}
    (hsq : 0 < q + s + 1) (hx : -1 < x)
    (hvalue : hullSevenSurrogateL s y q ≤ hullSevenSurrogateL s x q) :
    y ≤ x := by
  by_contra hnot
  have hxy : x < y := lt_of_not_ge hnot
  exact (not_lt_of_ge hvalue)
    (hullSevenEndpoint_surrogateL_strictMono hsq hx hxy)

private lemma hullSevenEndpoint_ear_preserved
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
    · exact sub_pos.mp hpos.2
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

private lemma hullSevenEndpoint_parameter_strict
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

private lemma hullSevenEndpoint_lower
    {A q L : ℝ} (hA : 0 < A)
    (hear : 0 ≤ (L - q) + L * (A - 1) - A) :
    1 + q / A ≤ L := by
  have hdiv : q / A ≤ L - 1 := by
    apply (div_le_iff₀ hA).2
    nlinarith [hear]
  linarith

private lemma hullSevenEndpoint_left_recurrence_upper
    (X : HullSevenEndpointHighPointInput) :
    X.B * X.L ≤ X.q * (X.A + X.B - 1) - X.A * X.C := by
  rw [X.L_rec]
  have hm := mul_le_mul_of_nonneg_left X.p_ear
    (le_trans (by norm_num) X.q_ge)
  linarith

private lemma hullSevenEndpoint_right_recurrence_upper
    (X : HullSevenEndpointHighPointInput) :
    X.C * X.R ≤ X.q * (X.D + X.C - 1) - X.D * X.B := by
  rw [X.R_rec]
  have hm := mul_le_mul_of_nonneg_left X.r_ear
    (le_trans (by norm_num) X.q_ge)
  linarith

private lemma hullSevenEndpoint_left_preserved
    (X : HullSevenEndpointHighPointInput) :
    1 < X.A ∧
      1 + X.q / X.A ≤ X.L ∧
      X.L ≤ hullSevenLeftMax X.A X.B X.C X.q := by
  have hA0 : 0 < X.A := lt_of_lt_of_le (by norm_num) X.A_ge
  have hB0 : 0 < X.B := lt_of_lt_of_le (by norm_num) X.B_ge
  have hupper := hullSevenEndpoint_left_recurrence_upper X
  have hAl : X.A ≤ X.A * X.l := by
    have hm := mul_nonneg (le_trans (by norm_num) X.A_ge)
      (sub_nonneg.mpr X.l_ge)
    nlinarith
  have horiginal : X.A + X.a0 * X.q ≤
      X.L * (X.a0 + X.A - 1) := le_trans (by linarith) X.left_endpoint
  have hear := hullSevenEndpoint_ear_preserved X.a0_ge X.A_ge hB0
    X.C_ge (lt_of_lt_of_le (by norm_num) X.q_ge) hupper horiginal
  have hAstr := hullSevenEndpoint_parameter_strict X.A_ge hB0 X.C_ge
    hupper hear
  have hlower := hullSevenEndpoint_lower hA0 hear
  have hmax : X.L ≤ hullSevenLeftMax X.A X.B X.C X.q := by
    unfold hullSevenLeftMax
    apply (le_div_iff₀ hB0).2
    nlinarith [hupper]
  exact ⟨hAstr, hlower, hmax⟩

private lemma hullSevenEndpoint_right_preserved
    (X : HullSevenEndpointHighPointInput) :
    1 < X.D ∧
      1 + X.q / X.D ≤ X.R ∧
      X.R ≤ hullSevenRightMax X.B X.C X.D X.q := by
  have hD0 : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
  have hC0 : 0 < X.C := lt_of_lt_of_le (by norm_num) X.C_ge
  have hupper := hullSevenEndpoint_right_recurrence_upper X
  have hDm : X.D ≤ X.D * X.m := by
    have hm := mul_nonneg (le_trans (by norm_num) X.D_ge)
      (sub_nonneg.mpr X.m_ge)
    nlinarith
  have horiginal : X.D + X.a5 * X.q ≤
      X.R * (X.a5 + X.D - 1) := le_trans (by linarith) X.right_endpoint
  have hear := hullSevenEndpoint_ear_preserved X.a5_ge X.D_ge hC0
    X.B_ge (lt_of_lt_of_le (by norm_num) X.q_ge) hupper horiginal
  have hDstr := hullSevenEndpoint_parameter_strict X.D_ge hC0 X.B_ge
    hupper hear
  have hlower := hullSevenEndpoint_lower hD0 hear
  have hmax : X.R ≤ hullSevenRightMax X.B X.C X.D X.q := by
    unfold hullSevenRightMax
    apply (le_div_iff₀ hC0).2
    nlinarith [hupper]
  exact ⟨hDstr, hlower, hmax⟩

private noncomputable def hullSevenEndpoint_leftThreshold
    (X : HullSevenEndpointHighPointInput) : ℝ :=
  let s := X.A - 1
  let v := X.B - 1
  let d := X.B + X.C - 1 - X.q
  (v * (X.q + s + 1) - d * (s + 1)) /
    (X.q + s + 1 + d * (s + 1))

private noncomputable def hullSevenEndpoint_rightEndpoint
    (X : HullSevenEndpointHighPointInput) : ℝ :=
  let u := X.D - 1
  let v := X.B - 1
  let w := X.C - 1
  let d := X.B + X.C - 1 - X.q
  v - d + d * (u + 1) * (w + 1) /
    (X.q + u + 1 + d * (u + 1))

/-- A denominator-explicit form of the surrogate evaluation used twice in
the high-point construction.  Keeping this identity separate prevents the
main theorem's simplifier from having to discover that `N / D + 1` is
positive while clearing a nested rational expression. -/
private lemma hullSevenEndpoint_surrogate_fraction
    {s q N D V : ℝ} (hD : 0 < D) (hV : 0 < V)
    (hQ : 0 < q + s + 1)
    (hsum : N + D = V * (q + s + 1)) :
    hullSevenSurrogateL s (N / D) q = N / V := by
  have honeEq : N / D + 1 = V * (q + s + 1) / D := by
    field_simp [hD.ne']
    linear_combination hsum
  have hone : 0 < N / D + 1 := by
    rw [honeEq]
    exact div_pos (mul_pos hV hQ) hD
  unfold hullSevenSurrogateL
  apply (div_eq_iff hone.ne').2
  field_simp [hD.ne', hV.ne']
  linear_combination -N * hsum

/-- The same numerator-sum identity also places the surrogate parameter in
the monotonicity domain `(-1, +infinity)`. -/
private lemma hullSevenEndpoint_fraction_gt_neg_one
    {s q N D V : ℝ} (hD : 0 < D) (hV : 0 < V)
    (hQ : 0 < q + s + 1)
    (hsum : N + D = V * (q + s + 1)) :
    -1 < N / D := by
  have honeEq : N / D + 1 = V * (q + s + 1) / D := by
    field_simp [hD.ne']
    linear_combination hsum
  have hone : 0 < N / D + 1 := by
    rw [honeEq]
    exact div_pos (mul_pos hV hQ) hD
  linarith

set_option maxHeartbeats 1000000 in
/-- Endpoint recurrences and caps alone produce the common high point used by
the hull-seven selector.  The selected `t,w` are part of the conclusion, not
additional assumptions. -/
noncomputable def hullSeven_endpointHighPoint
    (X : HullSevenEndpointHighPointInput) :
    HullSevenEndpointHighPointOutput X := by
  let s := X.A - 1
  let u := X.D - 1
  let v := X.B - 1
  let w := X.C - 1
  let d := X.B + X.C - 1 - X.q
  let D0 := X.q + s + 1 + d * (s + 1)
  let D1 := X.q + u + 1 + d * (u + 1)
  let t0 := hullSevenEndpoint_leftThreshold X
  let t1 := hullSevenEndpoint_rightEndpoint X
  have hs : 0 < s := sub_pos.mpr (hullSevenEndpoint_left_preserved X).1
  have hu : 0 < u := sub_pos.mpr (hullSevenEndpoint_right_preserved X).1
  have hv : 0 ≤ v := by dsimp [v]; linarith [X.B_ge]
  have hw : 0 ≤ w := by dsimp [w]; linarith [X.C_ge]
  have hd : 0 ≤ d := by dsimp [d]; linarith [X.q_ear]
  have hq : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hqeq : X.q = v + w + 1 - d := by
    dsimp [v, w, d]
    ring
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  have hD1 : 0 < D1 := by dsimp [D1]; positivity
  have hthreshold := hullSevenSurrogate_threshold_identity
    (s := s) (u := u) (v := v) (w := w) (d := d) (q := X.q)
    hs hu hv hw hd hqeq hD0 hD1
  have htOrder : t0 ≤ t1 := by
    have hrhs :
        0 ≤ d * X.q *
          (d * s * u + s * u + s * v + s + u * w + u) := by
      positivity
    have hden : 0 < D0 * D1 := mul_pos hD0 hD1
    have hfactor :
        (t1 - t0) * (D0 * D1) =
          d * X.q *
            (d * s * u + s * u + s * v + s + u * w + u) := by
      simpa [t0, t1, D0, D1, hullSevenEndpoint_leftThreshold,
        hullSevenEndpoint_rightEndpoint, s, u, v, w, d, mul_assoc] using hthreshold
    by_contra hnot
    have hneg : t1 - t0 < 0 := sub_neg.mpr (lt_of_not_ge hnot)
    have hp := mul_neg_of_neg_of_pos hneg hden
    rw [hfactor] at hp
    exact (not_lt_of_ge hrhs) hp
  have hleftFormula :
      hullSevenLeftMax X.A X.B X.C X.q =
        (v * (X.q + s + 1) - d * (s + 1)) / (v + 1) := by
    unfold hullSevenLeftMax
    dsimp [s, v, w, d] at hqeq ⊢
    rw [hqeq]
    have hv1 : 0 < v + 1 := by dsimp [v]; linarith [X.B_ge]
    have hB0 : 0 < X.B := lt_of_lt_of_le (by norm_num) X.B_ge
    field_simp [hv1.ne', hB0.ne']
    ring
  let N0 := v * (X.q + s + 1) - d * (s + 1)
  have ht0Formula : t0 = N0 / D0 := by
    rfl
  have hsum0 : N0 + D0 = (v + 1) * (X.q + s + 1) := by
    dsimp [N0, D0]
    ring
  have hKs : 0 < X.q + s + 1 := by linarith [hq, hs]
  have hv1 : 0 < v + 1 := by dsimp [v]; linarith [X.B_ge]
  have ht0Above : -1 < t0 := by
    rw [ht0Formula]
    exact hullSevenEndpoint_fraction_gt_neg_one hD0 hv1 hKs hsum0
  have hrightFormula :
      hullSevenRightMax X.B X.C X.D X.q =
        (w * (X.q + u + 1) - d * (u + 1)) / (w + 1) := by
    unfold hullSevenRightMax
    dsimp [u, v, w, d] at hqeq ⊢
    rw [hqeq]
    have hw1 : 0 < w + 1 := by dsimp [w]; linarith [X.C_ge]
    have hC0 : 0 < X.C := lt_of_lt_of_le (by norm_num) X.C_ge
    field_simp [hw1.ne', hC0.ne']
    ring
  have hleftValue :
      hullSevenSurrogateL s t0 X.q =
        hullSevenLeftMax X.A X.B X.C X.q := by
    rw [hleftFormula, ht0Formula]
    simpa [N0] using
      (hullSevenEndpoint_surrogate_fraction hD0 hv1 hKs hsum0)
  let wr := X.q - 1 - t1
  have hwrFormula :
      wr = (w * (X.q + u + 1) - d * (u + 1)) /
        (X.q + u + 1 + d * (u + 1)) := by
    have ht1Formula :
        t1 = v - d + d * (u + 1) * (w + 1) / D1 := by
      rfl
    dsimp only [wr]
    rw [ht1Formula]
    change
      X.q - 1 - (v - d + d * (u + 1) * (w + 1) / D1) =
        (w * (X.q + u + 1) - d * (u + 1)) / D1
    field_simp [hD1.ne']
    rw [hqeq]
    ring
  let N1 := w * (X.q + u + 1) - d * (u + 1)
  have hwrFormula' : wr = N1 / D1 := by
    simpa [N1, D1] using hwrFormula
  have hsum1 : N1 + D1 = (w + 1) * (X.q + u + 1) := by
    dsimp [N1, D1]
    ring
  have hKu : 0 < X.q + u + 1 := by linarith [hq, hu]
  have hw1 : 0 < w + 1 := by dsimp [w]; linarith [X.C_ge]
  have hwrAbove : -1 < wr := by
    rw [hwrFormula']
    exact hullSevenEndpoint_fraction_gt_neg_one hD1 hw1 hKu hsum1
  have hrightValue :
      hullSevenSurrogateL u wr X.q =
        hullSevenRightMax X.B X.C X.D X.q := by
    rw [hrightFormula, hwrFormula']
    simpa [N1, D1] using
      (hullSevenEndpoint_surrogate_fraction hD1 hw1 hKu hsum1)
  have hleftBase :
      hullSevenSurrogateL s (1 / s) X.q = 1 + X.q / X.A := by
    unfold hullSevenSurrogateL
    dsimp [s]
    have hs0 : 0 < X.A - 1 := hs
    have hA0 : 0 < X.A := lt_of_lt_of_le (by norm_num) X.A_ge
    field_simp [hs0.ne', hA0.ne']
    ring
  have hrightBase :
      hullSevenSurrogateL u (1 / u) X.q = 1 + X.q / X.D := by
    unfold hullSevenSurrogateL
    dsimp [u]
    have hu0 : 0 < X.D - 1 := hu
    have hD0' : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
    field_simp [hu0.ne', hD0'.ne']
    ring
  have ht0Lower : 1 / s ≤ t0 := by
    have hvalue :
        hullSevenSurrogateL s (1 / s) X.q ≤
          hullSevenSurrogateL s t0 X.q := by
      rw [hleftBase, hleftValue]
      exact le_trans (hullSevenEndpoint_left_preserved X).2.1
        (hullSevenEndpoint_left_preserved X).2.2
    have hsq : 0 < X.q + s + 1 := by
      dsimp [s]
      linarith [X.q_ge, X.A_ge]
    have hx : -1 < 1 / s := by
      have hsInv : 0 < 1 / s := one_div_pos.mpr hs
      linarith
    exact hullSevenEndpoint_surrogateL_reflect_order hsq ht0Above hvalue
  have hwrLower : 1 / u ≤ wr := by
    have hvalue :
        hullSevenSurrogateL u (1 / u) X.q ≤
          hullSevenSurrogateL u wr X.q := by
      rw [hrightBase, hrightValue]
      exact le_trans (hullSevenEndpoint_right_preserved X).2.1
        (hullSevenEndpoint_right_preserved X).2.2
    have hsq : 0 < X.q + u + 1 := by
      dsimp [u]
      linarith [X.q_ge, X.D_ge]
    have hx : -1 < 1 / u := by
      have huInv : 0 < 1 / u := one_div_pos.mpr hu
      linarith
    exact hullSevenEndpoint_surrogateL_reflect_order hsq hwrAbove hvalue
  have ht0Pos : 0 < t0 := lt_of_lt_of_le (one_div_pos.mpr hs) ht0Lower
  have hwrPos : 0 < wr := lt_of_lt_of_le (one_div_pos.mpr hu) hwrLower
  let w0 := X.q - 1 - t0
  have hw0wr : wr ≤ w0 := by dsimp [wr, w0]; linarith
  have hw0Pos : 0 < w0 := lt_of_lt_of_le hwrPos hw0wr
  have hleftHigh : X.L ≤ hullSevenSurrogateL s t0 X.q := by
    rw [hleftValue]
    exact (hullSevenEndpoint_left_preserved X).2.2
  have hrightHigh : X.R ≤ hullSevenSurrogateL u w0 X.q := by
    calc
      X.R ≤ hullSevenRightMax X.B X.C X.D X.q :=
        (hullSevenEndpoint_right_preserved X).2.2
      _ = hullSevenSurrogateL u wr X.q := hrightValue.symm
      _ ≤ hullSevenSurrogateL u w0 X.q :=
        hullSevenEndpoint_surrogateL_mono
          (by dsimp [u]; linarith [hq, hu]) (by linarith [hwrPos]) hw0wr
  have hleftScaled : X.L * (1 + t0) ≤ t0 * (X.A + X.q) := by
    have hden : 0 < t0 + 1 := by linarith [ht0Pos]
    have hvalue : X.L ≤ t0 * (X.q + s + 1) / (t0 + 1) := by
      simpa [hullSevenSurrogateL] using hleftHigh
    have hm := (le_div_iff₀ hden).1 hvalue
    calc
      X.L * (1 + t0) = X.L * (t0 + 1) := by ring
      _ ≤ t0 * (X.q + s + 1) := hm
      _ = t0 * (X.A + X.q) := by dsimp [s]; ring
  have hrightScaled : X.R * (1 + w0) ≤ w0 * (X.D + X.q) := by
    have hden : 0 < w0 + 1 := by linarith [hw0Pos]
    have hvalue : X.R ≤ w0 * (X.q + u + 1) / (w0 + 1) := by
      simpa [hullSevenSurrogateL] using hrightHigh
    have hm := (le_div_iff₀ hden).1 hvalue
    calc
      X.R * (1 + w0) = X.R * (w0 + 1) := by ring
      _ ≤ w0 * (X.q + u + 1) := hm
      _ = w0 * (X.D + X.q) := by dsimp [u]; ring
  have hproduct :
      X.L * X.R ≤ hullSevenSurrogateP X.A X.D X.q (t0 * w0) := by
    have hnonnegL : 0 ≤ hullSevenSurrogateL s t0 X.q :=
      le_trans (le_trans (by norm_num) X.L_ge) hleftHigh
    have hmul := mul_le_mul hleftHigh hrightHigh
      (le_trans (by norm_num) X.R_ge) hnonnegL
    have hsum : t0 + w0 = X.q - 1 := by dsimp [w0]; ring
    rw [hullSevenSurrogate_product ht0Pos hw0Pos hsum] at hmul
    simpa [s, u, sub_add_cancel] using hmul
  refine
    { t := t0
      w := w0
      t_pos := ht0Pos
      w_pos := hw0Pos
      sum_eq := by dsimp [w0]; ring
      left_outer := ?_
      right_outer := ?_
      left_scaled := hleftScaled
      right_scaled := hrightScaled
      product_lower := hproduct }
  · have hm := mul_le_mul_of_nonneg_left ht0Lower hs.le
    simpa [hs.ne'] using hm
  · have hm := mul_le_mul_of_nonneg_left
      (le_trans hwrLower hw0wr) hu.le
    simpa [hu.ne'] using hm

end Heilbronn8.TriHull
