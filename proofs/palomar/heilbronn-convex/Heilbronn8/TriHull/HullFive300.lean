import Heilbronn8.TriHull.Bridge

/-!
# The hull-five `3 + 0 + 0` adapter

Fix the counterclockwise pentagon `A-B-X-C-D` and three selected points
`P,Q,R`.  This module packages the two possible three-point cells used by
the hull-five survivor families:

* the central triangle `ABC`;
* the right ear `BXC`.

The only geometric input beyond the cell memberships is maximality of
`ABC` over `BXC`.  The right-ear branch already forces the full hull bound.
The central branch is reduced to the explicit residual
`17 * H < 25 * sig A B C`; a box or hull-ratio argument can discharge that
last inequality without reopening the three-point geometry.
-/

namespace Heilbronn8.TriHull

/-- The two three-point cells needed for the live hull-five survivor words.

The labels supplied by `e` are, in order, `A,B,X,C,D,P,Q,R`.
-/
inductive HullFive300Cell (v : Fin 8 → Point) (e : Fin 8 → Fin 8) : Prop
  | central
      (hP : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 3)))
      (hQ : InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 3)))
      (hR : InTriStrict (v (e 7)) (v (e 0)) (v (e 1)) (v (e 3)))
  | right
      (hP : InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)))
      (hQ : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)))
      (hR : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3)))

/-- Three selected points in the central triangle give its normalized
`17 / 2` lower bound. -/
theorem hullFive300_central_lower_bound
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hP : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 3)))
    (hQ : InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 3)))
    (hR : InTriStrict (v (e 7)) (v (e 0)) (v (e 1)) (v (e 3))) :
    (17 : ℝ) / 2 ≤
      sig (v (e 0)) (v (e 1)) (v (e 3)) / minTri v := by
  let f : Fin 6 → Fin 8 := e ∘ ![0, 1, 3, 5, 6, 7]
  have hf : Function.Injective f := he.comp (by decide)
  exact threePointTriangle_normalized_lower_bound_unconditional
    v f hf hm (by simpa [f] using hABC)
      (by simpa [f] using hP) (by simpa [f] using hQ)
      (by simpa [f] using hR)

/-- Three selected points in the right ear give its normalized `17 / 2`
lower bound. -/
theorem hullFive300_right_lower_bound
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hP : InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hQ : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hR : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3))) :
    (17 : ℝ) / 2 ≤
      sig (v (e 1)) (v (e 2)) (v (e 3)) / minTri v := by
  let f : Fin 6 → Fin 8 := e ∘ ![1, 2, 3, 5, 6, 7]
  have hf : Function.Injective f := he.comp (by decide)
  exact threePointTriangle_normalized_lower_bound_unconditional
    v f hf hm (by simpa [f] using hBXC)
      (by simpa [f] using hP) (by simpa [f] using hQ)
      (by simpa [f] using hR)

/-- The disjunctive point-level lower bound before using hull maximality. -/
theorem hullFive300_cell_lower_bound
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hcell : HullFive300Cell v e) :
    (17 : ℝ) / 2 ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)) / minTri v ∨
      (17 : ℝ) / 2 ≤
        sig (v (e 1)) (v (e 2)) (v (e 3)) / minTri v := by
  cases hcell with
  | central hP hQ hR =>
      exact Or.inl
        (hullFive300_central_lower_bound v e he hm hABC hP hQ hR)
  | right hP hQ hR =>
      exact Or.inr
        (hullFive300_right_lower_bound v e he hm hBXC hP hQ hR)

/-- Scalar closure of the right-ear branch.  If `ABC` is positive and at
least as large as `BXC`, the three-point estimate in `BXC` is incompatible
with a failure of the target hull bound. -/
lemma hullFive300_right_scalar
    {m T E F H : ℝ}
    (hm : 0 < m) (hT : 0 < T) (hE : 0 < E) (hF : 0 < F)
    (hEmax : E ≤ T) (hH : H = T + E + F)
    (hthree : (17 : ℝ) / 2 ≤ E / m) :
    m * 25 ≤ 2 * H := by
  have hscaled : ((17 : ℝ) / 2) * m ≤ E :=
    (le_div_iff₀ hm).mp hthree
  by_contra hn
  have hfail : 2 * H < m * 25 := lt_of_not_ge hn
  have hHpos : 0 < H := by linarith
  have hEH : 17 * H < 25 * E := by nlinarith
  nlinarith

/-- The right-ear `3 + 0 + 0` branch forces the full hull target. -/
theorem hullFive300_right_forces_hull_bound
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (H : ℝ)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hCDA : 0 < sig (v (e 3)) (v (e 4)) (v (e 0)))
    (hBXCmax :
      sig (v (e 1)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hH : H =
      sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) +
      sig (v (e 3)) (v (e 4)) (v (e 0)))
    (hP : InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hQ : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hR : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3))) :
    minTri v * 25 ≤ 2 * H := by
  apply hullFive300_right_scalar hm hABC hBXC hCDA hBXCmax hH
  exact hullFive300_right_lower_bound v e he hm hBXC hP hQ hR

/-- If the central three-point estimate does not already prove the hull
target, the hull must lie in the explicit ratio residual
`17 * H < 25 * T`. -/
lemma hullFive300_central_scalar_residual
    {m T H : ℝ}
    (hm : 0 < m)
    (hthree : (17 : ℝ) / 2 ≤ T / m)
    (hfail : 2 * H < m * 25) :
    17 * H < 25 * T := by
  have hscaled : ((17 : ℝ) / 2) * m ≤ T :=
    (le_div_iff₀ hm).mp hthree
  nlinarith

/-- Complete two-cell adapter.  The right-ear branch is closed outright;
the central branch returns only the sharp hull-ratio residual needed by the
remaining box argument. -/
theorem hullFive300_bound_or_central_residual
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (H : ℝ)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hCDA : 0 < sig (v (e 3)) (v (e 4)) (v (e 0)))
    (hBXCmax :
      sig (v (e 1)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hH : H =
      sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) +
      sig (v (e 3)) (v (e 4)) (v (e 0)))
    (hcell : HullFive300Cell v e) :
    minTri v * 25 ≤ 2 * H ∨
      17 * H <
        25 * sig (v (e 0)) (v (e 1)) (v (e 3)) := by
  cases hcell with
  | central hP hQ hR =>
      by_cases hbound : minTri v * 25 ≤ 2 * H
      · exact Or.inl hbound
      · right
        apply hullFive300_central_scalar_residual hm
          (hullFive300_central_lower_bound v e he hm hABC hP hQ hR)
        exact lt_of_not_ge hbound
  | right hP hQ hR =>
      exact Or.inl (hullFive300_right_forces_hull_bound
        v e he hm H hABC hBXC hCDA hBXCmax hH hP hQ hR)

/-! ## A common machine-box closure

The first quotient row together with the three positive `01p` beat rows
and the positive `BXC` beat row gives the same short linear certificate on
many of the live central-cell boxes.  This lemma keeps that calculation
independent of any particular survivor record.  Its final hypothesis is a
single affine upper bound that callers can discharge from their five
coordinate intervals.
-/

/-- The common five-row certificate for the central `3 + 0 + 0` boxes.

The reference coordinates are `A=(0,0)`, `B=(1,0)`, `C=(0,1)`, and
`H = x4 + y4 - x3`.  The four rows after `hquotient` are beat rows at
`q0 = 2/25`.  The condition `hy3` is the standard gauge-box inequality
`-x3 <= y3`.
-/
lemma hullFive300_common_box_contradiction
    {H x3 x4 x5 x6 x7 y3 y4 y5 y6 y7 : ℝ}
    (hH : H = x4 + y4 - x3)
    (hquotient :
      0 ≤ 3 * (x3 + x4 + x5 + x6 + x7) -
        3 * (y3 + y4 + y5 + y6 + y7))
    (hy3 : 0 ≤ x3 + y3)
    (h015 : 0 ≤ y5 - (2 / 25 : ℝ) * H)
    (h016 : 0 ≤ y6 - (2 / 25 : ℝ) * H)
    (h017 : 0 ≤ y7 - (2 / 25 : ℝ) * H)
    (h124 : 0 ≤ x4 + y4 - 1 - (2 / 25 : ℝ) * H)
    (hbox :
      54 * x3 + 46 * x4 + 23 * (x5 + x6 + x7) < 31) : False := by
  have hcertificate : 0 ≤
      23 * (3 * (x3 + x4 + x5 + x6 + x7) -
        3 * (y3 + y4 + y5 + y6 + y7)) +
      69 * (y5 - (2 / 25 : ℝ) * H) +
      69 * (y6 - (2 / 25 : ℝ) * H) +
      69 * (y7 - (2 / 25 : ℝ) * H) +
      93 * (x4 + y4 - 1 - (2 / 25 : ℝ) * H) := by
    positivity
  have hidentity :
      23 * (3 * (x3 + x4 + x5 + x6 + x7) -
        3 * (y3 + y4 + y5 + y6 + y7)) +
      69 * (y5 - (2 / 25 : ℝ) * H) +
      69 * (y6 - (2 / 25 : ℝ) * H) +
      69 * (y7 - (2 / 25 : ℝ) * H) +
      93 * (x4 + y4 - 1 - (2 / 25 : ℝ) * H) =
        93 * x3 + 138 * x4 + 69 * (x5 + x6 + x7) -
          69 * y3 - 93 := by
    rw [hH]
    ring
  nlinarith only [hcertificate, hidentity, hy3, hbox]

end Heilbronn8.TriHull
