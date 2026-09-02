import Heilbronn8.QuadHull.Main

/-!
# Scalar fan exclusion for coarse orbit I

This is the arithmetic part of the top-level `(4,0,0,0)` reduction.  The
four fan areas around a side-minimal point are `alpha,beta,gamma,delta`;
`u,t` are the two diagonal cells.  This module deliberately knows nothing
about how the four geometric points are selected or assigned to fan cells.

The nine constructors of `OrbitICoarseDirectBounds` are exactly the nine
non-residual triples `(k_alpha,k_gamma,k_delta)` left after side minimality
forces `k_beta = 0`.  The omitted triple `(0,0,3)` is the common-geometry
residual and is not asserted to satisfy a direct fan inequality here.
-/

namespace Heilbronn8.QuadHull

/-- Normalized scalar data available before the coarse orbit-I fan census is
dispatched. -/
structure OrbitICoarseFan (H : ℝ) where
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  delta : ℝ
  u : ℝ
  t : ℝ
  hull_eq : H = alpha + beta + gamma + delta
  alpha_unit : 1 ≤ alpha
  beta_unit : 1 ≤ beta
  gamma_unit : 1 ≤ gamma
  delta_unit : 1 ≤ delta
  u_unit : 1 ≤ u
  t_unit : 1 ≤ t
  plucker : beta * delta = alpha * gamma + u * t
  diagonal_AC : (21 : ℝ) / 2 ≤ alpha + beta + u
  diagonal_BD : (21 : ℝ) / 2 ≤ alpha + delta + t

/-- Generic rational row checker behind the eight regular fan-count rows.
`U` and `T` may use either the unit floor or the strict diagonal floor that
follows from the contradictory hypothesis `H < 63/5`. -/
private theorem OrbitICoarseFan.bound_of_cell_bounds
    {H A G D U T : ℝ} (f : OrbitICoarseFan H)
    (hA0 : 0 ≤ A) (hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hT0 : 0 ≤ T)
    (hA : A ≤ f.alpha) (hG : G ≤ f.gamma) (hD : D ≤ f.delta)
    (hU : U ≤ 1 ∨ U ≤ G + D - (21 : ℝ) / 10)
    (hT : T ≤ 1 ∨ T ≤ G - (11 : ℝ) / 10)
    (hnumeric :
      (((63 : ℝ) / 5 - A - G) ^ 2) / 4 < A * G + U * T) :
    (63 : ℝ) / 5 ≤ H := by
  by_contra hn
  have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
  have hsum :
      f.beta + f.delta < (63 : ℝ) / 5 - A - G := by
    nlinarith [f.hull_eq]
  have hsqsum :
      (f.beta + f.delta) ^ 2 <
        ((63 : ℝ) / 5 - A - G) ^ 2 := by
    have hp : 0 <
        ((63 : ℝ) / 5 - A - G - (f.beta + f.delta)) *
          ((63 : ℝ) / 5 - A - G + (f.beta + f.delta)) :=
      mul_pos (by linarith)
        (by linarith [f.beta_unit, f.delta_unit])
    nlinarith
  have hamgm :
      4 * (f.beta * f.delta) ≤ (f.beta + f.delta) ^ 2 := by
    nlinarith [sq_nonneg (f.beta - f.delta)]
  have hupper :
      f.beta * f.delta <
        (((63 : ℝ) / 5 - A - G) ^ 2) / 4 := by
    nlinarith
  have huLower : U ≤ f.u := by
    rcases hU with hUunit | hUdiag
    · exact hUunit.trans f.u_unit
    · nlinarith [f.diagonal_AC, f.hull_eq]
  have htLower : T ≤ f.t := by
    rcases hT with hTunit | hTdiag
    · exact hTunit.trans f.t_unit
    · nlinarith [f.diagonal_BD, f.hull_eq, f.beta_unit]
  have hAG : A * G ≤ f.alpha * f.gamma :=
    mul_le_mul hA hG hG0 (by linarith)
  have hUT : U * T ≤ f.u * f.t :=
    mul_le_mul huLower htLower hT0 (by linarith)
  have hlower : A * G + U * T ≤ f.beta * f.delta := by
    nlinarith [f.plucker, hAG, hUT]
  nlinarith

/-- The single exceptional row `(1,0,2)`, where separate upper bounds on
`beta` and `delta` are sharper than AM-GM. -/
private theorem OrbitICoarseFan.bound_102
    {H : ℝ} (f : OrbitICoarseFan H)
    (halpha : 3 ≤ f.alpha)
    (hdelta : (149 : ℝ) / 20 < f.delta) :
    (63 : ℝ) / 5 ≤ H := by
  by_contra hn
  have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
  have hbeta : f.beta < (23 : ℝ) / 20 := by
    nlinarith [f.hull_eq, f.gamma_unit]
  have hdeltaUpper : f.delta < (38 : ℝ) / 5 := by
    nlinarith [f.hull_eq, f.beta_unit, f.gamma_unit]
  have hbetaDelta :
      f.beta * f.delta < (437 : ℝ) / 50 := by
    calc
      f.beta * f.delta < (23 : ℝ) / 20 * f.delta :=
        mul_lt_mul_of_pos_right hbeta
          (by linarith [f.delta_unit])
      _ < (23 : ℝ) / 20 * ((38 : ℝ) / 5) :=
        mul_lt_mul_of_pos_left hdeltaUpper (by norm_num)
      _ = (437 : ℝ) / 50 := by norm_num
  have hu : (127 : ℝ) / 20 < f.u := by
    nlinarith [f.diagonal_AC, f.hull_eq, f.gamma_unit]
  have hAG : 3 ≤ f.alpha * f.gamma := by
    have hm := mul_le_mul halpha f.gamma_unit
      (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [halpha] : 0 ≤ f.alpha)
    norm_num at hm ⊢
    exact hm
  have hUT : (127 : ℝ) / 20 < f.u * f.t := by
    have hu0 : 0 ≤ f.u := by linarith
    have hm := mul_le_mul_of_nonneg_left f.t_unit hu0
    nlinarith
  nlinarith [f.plucker]

/-- Exact direct fan-count rows after `k_beta = 0`.  Constructor names are
the triples `(k_alpha,k_gamma,k_delta)`. -/
inductive OrbitICoarseDirectBounds {H : ℝ}
    (f : OrbitICoarseFan H) : Prop
  | c012
      (hgamma : 3 ≤ f.gamma)
      (hdelta : (149 : ℝ) / 20 < f.delta)
  | c021
      (hgamma : (149 : ℝ) / 20 < f.gamma)
      (hdelta : 3 ≤ f.delta)
  | c030 (hgamma : (17 : ℝ) / 2 ≤ f.gamma)
  | c111
      (halpha : 3 ≤ f.alpha)
      (hgamma : 3 ≤ f.gamma)
      (hdelta : 3 ≤ f.delta)
  | c120
      (halpha : 3 ≤ f.alpha)
      (hgamma : (149 : ℝ) / 20 < f.gamma)
  | c201
      (halpha : (149 : ℝ) / 20 < f.alpha)
      (hdelta : 3 ≤ f.delta)
  | c210
      (halpha : (149 : ℝ) / 20 < f.alpha)
      (hgamma : 3 ≤ f.gamma)
  | c300 (halpha : (17 : ℝ) / 2 ≤ f.alpha)
  | c102
      (halpha : 3 ≤ f.alpha)
      (hdelta : (149 : ℝ) / 20 < f.delta)

/-- Every non-residual fan-count row proves the normalized `63/5` hull
bound.  The proof is compact because the rational table is checked by the
generic row lemma above. -/
theorem OrbitICoarseDirectBounds.bound
    {H : ℝ} {f : OrbitICoarseFan H}
    (h : OrbitICoarseDirectBounds f) : (63 : ℝ) / 5 ≤ H := by
  cases h with
  | c012 hgamma hdelta =>
      apply f.bound_of_cell_bounds
        (A := 1) (G := 3) (D := (149 : ℝ) / 20)
        (U := (167 : ℝ) / 20) (T := (19 : ℝ) / 10)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        f.alpha_unit hgamma hdelta.le (Or.inr (by norm_num))
        (Or.inr (by norm_num)) (by norm_num)
  | c021 hgamma hdelta =>
      apply f.bound_of_cell_bounds
        (A := 1) (G := (149 : ℝ) / 20) (D := 3)
        (U := (167 : ℝ) / 20) (T := (127 : ℝ) / 20)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        f.alpha_unit hgamma.le hdelta (Or.inr (by norm_num))
        (Or.inr (by norm_num)) (by norm_num)
  | c030 hgamma =>
      apply f.bound_of_cell_bounds
        (A := 1) (G := (17 : ℝ) / 2) (D := 1)
        (U := (37 : ℝ) / 5) (T := (37 : ℝ) / 5)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        f.alpha_unit hgamma f.delta_unit (Or.inr (by norm_num))
        (Or.inr (by norm_num)) (by norm_num)
  | c111 halpha hgamma hdelta =>
      apply f.bound_of_cell_bounds
        (A := 3) (G := 3) (D := 3)
        (U := (39 : ℝ) / 10) (T := (19 : ℝ) / 10)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        halpha hgamma hdelta (Or.inr (by norm_num))
        (Or.inr (by norm_num)) (by norm_num)
  | c120 halpha hgamma =>
      apply f.bound_of_cell_bounds
        (A := 3) (G := (149 : ℝ) / 20) (D := 1)
        (U := (127 : ℝ) / 20) (T := (127 : ℝ) / 20)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        halpha hgamma.le f.delta_unit (Or.inr (by norm_num))
        (Or.inr (by norm_num)) (by norm_num)
  | c201 halpha hdelta =>
      apply f.bound_of_cell_bounds
        (A := (149 : ℝ) / 20) (G := 1) (D := 3)
        (U := (19 : ℝ) / 10) (T := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        halpha.le f.gamma_unit hdelta (Or.inr (by norm_num))
        (Or.inl (by norm_num)) (by norm_num)
  | c210 halpha hgamma =>
      apply f.bound_of_cell_bounds
        (A := (149 : ℝ) / 20) (G := 3) (D := 1)
        (U := (19 : ℝ) / 10) (T := (19 : ℝ) / 10)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        halpha.le hgamma f.delta_unit (Or.inr (by norm_num))
        (Or.inr (by norm_num)) (by norm_num)
  | c300 halpha =>
      apply f.bound_of_cell_bounds
        (A := (17 : ℝ) / 2) (G := 1) (D := 1)
        (U := 1) (T := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        halpha f.gamma_unit f.delta_unit (Or.inl (by norm_num))
        (Or.inl (by norm_num)) (by norm_num)
  | c102 halpha hdelta =>
      exact f.bound_102 halpha hdelta

end Heilbronn8.QuadHull
