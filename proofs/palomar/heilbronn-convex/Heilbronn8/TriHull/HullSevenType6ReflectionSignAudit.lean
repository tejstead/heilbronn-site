import Heilbronn8.TriHull.HullSevenType6Reflection

/-!
# Honest sign and determinant seam for hull-seven type 6

The canonical type-6 presentation is useful for census routing, but it is not
the presentation in which the geometric-mean reflection has the advertised
last two Pluecker inequalities: its chord `26` is negative.  Rotating once
gives the unique reflection-symmetric sign packet with positive `03` and
positive `26`.  Its only negative increasing brackets are

`04, 05, 06, 15, 16`.

The finite classifier fact is isolated in `HullSevenType6SignClassification`.
This file records the exact raw Pluecker packet in the rotated presentation.
Six of the eight rows of
`HullSevenType6ReflectionData`, together with its area row, follow from this
packet by two-term multiplicative Minkowski.  The two additive caps do not
follow from the two reflected ear floors in general, so the final conversion
takes those caps as explicit hypotheses.  This makes the remaining geometric
seam visible instead of assuming a false scalar-swap invariance.
-/

namespace Heilbronn8.TriHull

abbrev HullSevenType6Index := Fin 7

/-- A product of two normalized floors is again at least one after taking
its square root. -/
lemma hullSeven_type6_one_le_sqrt_mul {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ Real.sqrt (x * y) := by
  apply Real.one_le_sqrt.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

/-- Two-term AM-GM in the form used for the boundary-area row. -/
lemma hullSeven_type6_two_sqrt_mul_le_add {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  rw [Real.sqrt_mul hx]
  have hxsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hysq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]

/-- Reassociate four nonnegative factors underneath square roots. -/
lemma hullSeven_type6_sqrt_four_reassociate {a b c d : ℝ}
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
        (Real.sqrt b * Real.sqrt d) := by
      ring
    _ = Real.sqrt (a * c) * Real.sqrt (b * d) := by
      rw [Real.sqrt_mul ha, Real.sqrt_mul hb]

/-- Two-term multiplicative Minkowski (the two-dimensional Cauchy
inequality) for nonnegative scalars. -/
lemma hullSeven_type6_two_term_minkowski
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * c) + Real.sqrt (b * d) ≤
      Real.sqrt ((a + b) * (c + d)) := by
  have hleft : 0 ≤ Real.sqrt (a * c) + Real.sqrt (b * d) := by
    positivity
  have hright : 0 ≤ Real.sqrt ((a + b) * (c + d)) :=
    Real.sqrt_nonneg _
  apply (sq_le_sq₀ hleft hright).1
  have hac : (Real.sqrt (a * c)) ^ 2 = a * c :=
    Real.sq_sqrt (mul_nonneg ha hc)
  have hbd : (Real.sqrt (b * d)) ^ 2 = b * d :=
    Real.sq_sqrt (mul_nonneg hb hd)
  have habcd : (Real.sqrt ((a + b) * (c + d))) ^ 2 =
      (a + b) * (c + d) :=
    Real.sq_sqrt (mul_nonneg (add_nonneg ha hb) (add_nonneg hc hd))
  have hcross :
      2 * Real.sqrt (a * c) * Real.sqrt (b * d) ≤ a * d + b * c := by
    calc
      2 * Real.sqrt (a * c) * Real.sqrt (b * d) =
          2 * (Real.sqrt a * Real.sqrt d) *
            (Real.sqrt b * Real.sqrt c) := by
        rw [Real.sqrt_mul ha, Real.sqrt_mul hb]
        ring
      _ ≤ (Real.sqrt a * Real.sqrt d) ^ 2 +
          (Real.sqrt b * Real.sqrt c) ^ 2 := by
        nlinarith [sq_nonneg
          (Real.sqrt a * Real.sqrt d - Real.sqrt b * Real.sqrt c)]
      _ = a * d + b * c := by
        rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb,
          Real.sq_sqrt hc, Real.sq_sqrt hd]
  rw [add_sq, hac, hbd, habcd]
  nlinarith

/-- Pair two additive Pluecker rows and regroup their four factors. -/
lemma hullSeven_type6_paired_sum_gm
    {x₁ y₁ x₂ y₂ a₁ b₁ a₂ b₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁)
    (hx₂ : 0 ≤ x₂) (hy₂ : 0 ≤ y₂)
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁)
    (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂)
    (h₁ : x₁ * y₁ = a₁ + b₁)
    (h₂ : x₂ * y₂ = a₂ + b₂) :
    Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
      Real.sqrt (x₁ * x₂) * Real.sqrt (y₁ * y₂) := by
  calc
    Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
        Real.sqrt ((a₁ + b₁) * (a₂ + b₂)) :=
      hullSeven_type6_two_term_minkowski ha₁ hb₁ ha₂ hb₂
    _ = Real.sqrt ((x₁ * y₁) * (x₂ * y₂)) := by rw [h₁, h₂]
    _ = Real.sqrt (x₁ * x₂) * Real.sqrt (y₁ * y₂) :=
      hullSeven_type6_sqrt_four_reassociate hx₁ hy₁ hx₂ hy₂

/-- Lagrange's two-square identity for square-root coordinates.  It turns a
comparison of the two geometric-mean sums into the complementary comparison
of their cross determinants. -/
lemma hullSeven_type6_sqrt_lagrange
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 +
        (Real.sqrt (a * d) - Real.sqrt (b * c)) ^ 2 =
      (a + b) * (c + d) := by
  have hac : (Real.sqrt (a * c)) ^ 2 = a * c :=
    Real.sq_sqrt (mul_nonneg ha hc)
  have hbd : (Real.sqrt (b * d)) ^ 2 = b * d :=
    Real.sq_sqrt (mul_nonneg hb hd)
  have had : (Real.sqrt (a * d)) ^ 2 = a * d :=
    Real.sq_sqrt (mul_nonneg ha hd)
  have hbc : (Real.sqrt (b * c)) ^ 2 = b * c :=
    Real.sq_sqrt (mul_nonneg hb hc)
  have hcross :
      Real.sqrt (a * c) * Real.sqrt (b * d) =
        Real.sqrt (a * d) * Real.sqrt (b * c) := by
    calc
      Real.sqrt (a * c) * Real.sqrt (b * d) =
          Real.sqrt ((a * c) * (b * d)) :=
        (Real.sqrt_mul (mul_nonneg ha hc) (b * d)).symm
      _ = Real.sqrt ((a * d) * (b * c)) := by
        congr 1
        ring
      _ = Real.sqrt (a * d) * Real.sqrt (b * c) :=
        Real.sqrt_mul (mul_nonneg ha hd) (b * c)
  rw [add_sq, sub_sq, hac, hbd, had, hbc]
  nlinarith

/-- The exact cross-square condition missing from the reflected raw ears.

The two displayed sum equalities say that `p,t` split the first boundary
pair and `n,u` split its reflection.  Lagrange's identity says that a lower
bound on the cross-determinant spread is precisely what reverses the generic
Cauchy direction. -/
lemma hullSeven_type6_reverse_minkowski_of_cross_square
    {p t n u A B G Z : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hn : 0 ≤ n) (hu : 0 ≤ u)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hleft : p + t = A + B) (hright : n + u = G + Z)
    (hcross :
      (Real.sqrt (A * Z) - Real.sqrt (B * G)) ^ 2 ≤
        (Real.sqrt (p * u) - Real.sqrt (t * n)) ^ 2) :
    Real.sqrt (p * n) + Real.sqrt (t * u) ≤
      Real.sqrt (A * G) + Real.sqrt (B * Z) := by
  have hsource := hullSeven_type6_sqrt_lagrange hp ht hn hu
  have htarget := hullSeven_type6_sqrt_lagrange hA hB hG hZ
  have htotal : (p + t) * (n + u) = (A + B) * (G + Z) := by
    rw [hleft, hright]
  have hsquares :
      (Real.sqrt (p * n) + Real.sqrt (t * u)) ^ 2 ≤
        (Real.sqrt (A * G) + Real.sqrt (B * Z)) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquares

/-- Exact equivalence form of the missing cross-determinant condition. -/
lemma hullSeven_type6_reverse_minkowski_iff_cross_square
    {p t n u A B G Z : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hn : 0 ≤ n) (hu : 0 ≤ u)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hleft : p + t = A + B) (hright : n + u = G + Z) :
    Real.sqrt (p * n) + Real.sqrt (t * u) ≤
        Real.sqrt (A * G) + Real.sqrt (B * Z) ↔
      (Real.sqrt (A * Z) - Real.sqrt (B * G)) ^ 2 ≤
        (Real.sqrt (p * u) - Real.sqrt (t * n)) ^ 2 := by
  constructor
  · intro hsum
    have hsource := hullSeven_type6_sqrt_lagrange hp ht hn hu
    have htarget := hullSeven_type6_sqrt_lagrange hA hB hG hZ
    have htotal : (p + t) * (n + u) = (A + B) * (G + Z) := by
      rw [hleft, hright]
    have hsquares :
        (Real.sqrt (p * n) + Real.sqrt (t * u)) ^ 2 ≤
          (Real.sqrt (A * G) + Real.sqrt (B * Z)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
    nlinarith
  · intro hcross
    exact hullSeven_type6_reverse_minkowski_of_cross_square
      hp ht hn hu hA hB hG hZ hleft hright hcross

/-- The cap used by `HullSevenType6ReflectionData` follows from the exact
cross-square condition and the two normalized reflected ear floors. -/
lemma hullSeven_type6_gm_cap_of_cross_square
    {p t n u A B G Z : ℝ}
    (hp : 1 ≤ p) (ht : 1 ≤ t) (hn : 1 ≤ n) (hu : 1 ≤ u)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hG : 1 ≤ G) (hZ : 1 ≤ Z)
    (hleft : p + t = A + B) (hright : n + u = G + Z)
    (hcross :
      (Real.sqrt (A * Z) - Real.sqrt (B * G)) ^ 2 ≤
        (Real.sqrt (p * u) - Real.sqrt (t * n)) ^ 2) :
    Real.sqrt (p * n) ≤
      Real.sqrt (A * G) + Real.sqrt (B * Z) - 1 := by
  have hreverse := hullSeven_type6_reverse_minkowski_of_cross_square
    (le_trans (by norm_num) hp) (le_trans (by norm_num) ht)
    (le_trans (by norm_num) hn) (le_trans (by norm_num) hu)
    (le_trans (by norm_num) hA) (le_trans (by norm_num) hB)
    (le_trans (by norm_num) hG) (le_trans (by norm_num) hZ)
    hleft hright hcross
  have hear : 1 ≤ Real.sqrt (t * u) :=
    hullSeven_type6_one_le_sqrt_mul ht hu
  linarith

/-- The two reflected raw ear floors alone do not imply the corresponding
geometric-mean cap.  This exact scalar packet is the smallest useful warning
against applying a subtraction form of Minkowski in the wrong direction. -/
theorem hullSeven_type6_reflected_ears_do_not_force_gm_cap :
    let A : ℝ := 10
    let B : ℝ := 1
    let G : ℝ := 1
    let Z : ℝ := 10
    let p : ℝ := 11 / 2
    let n : ℝ := 11 / 2
    1 ≤ A ∧ 1 ≤ B ∧ 1 ≤ G ∧ 1 ≤ Z ∧
      1 ≤ p ∧ 1 ≤ n ∧
      1 ≤ A + B - p ∧ 1 ≤ G + Z - n ∧
      ¬ Real.sqrt (p * n) ≤
        Real.sqrt (A * G) + Real.sqrt (B * Z) - 1 := by
  dsimp
  have hsqrt : Real.sqrt 10 < (13 : ℝ) / 4 := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have hpn :
      Real.sqrt (((11 : ℝ) / 2) * ((11 : ℝ) / 2)) = 11 / 2 := by
    rw [show ((11 : ℝ) / 2) * (11 / 2) = (11 / 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro hcap
  rw [hpn] at hcap
  norm_num only [mul_one, one_mul] at hcap
  nlinarith

/-- Even charging both cap deficits to three paired boundary sums is not, by
itself, a replacement for the missing geometric caps.  This exact rational
packet satisfies rows 3--8 and the two aggregate ear allocations, but its
allocated area is below `25/2`. -/
theorem hullSeven_type6_aggregate_caps_do_not_force_area :
    let a : ℝ := 37709 / 24244
    let A : ℝ := 101 / 50
    let B : ℝ := 1
    let U : ℝ := 209 / 100
    let P : ℝ := 26109 / 11600
    let Q : ℝ := 58 / 25
    let R : ℝ := 9509 / 5000
    let E : ℝ := 15100 / 9509
    let SA : ℝ := 101 / 25
    let SB : ℝ := 14277 / 5800
    let SU : ℝ := 209 / 50
    1 ≤ a ∧ 1 ≤ A ∧ 1 ≤ B ∧ 1 ≤ U ∧
      1 ≤ P ∧ 1 ≤ Q ∧ 1 ≤ R ∧ 1 ≤ E ∧
      B + A * U ≤ P * Q ∧
      R + Q ≤ A * U ∧
      1 + P ≤ a * U ∧
      E + A ≤ a * Q ∧
      P + B * E ≤ A * R ∧
      1 + A * B ≤ R * E ∧
      2 * A ≤ SA ∧ 2 * B ≤ SB ∧ 2 * U ≤ SU ∧
      2 * P + 2 ≤ SA + SB ∧
      2 * Q + 2 ≤ SB + SU ∧
      a + SA + SB + SU < (25 : ℝ) / 2 := by
  norm_num

/-- The universally valid part of the reflected scalar packet.

It is exactly `HullSevenType6ReflectionData` without the two additive
geometric-mean caps. -/
structure HullSevenType6ReflectionCoreData (H : ℝ) where
  a : ℝ
  A : ℝ
  B : ℝ
  U : ℝ
  P : ℝ
  Q : ℝ
  R : ℝ
  E : ℝ
  a_ge : 1 ≤ a
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  U_ge : 1 ≤ U
  P_ge : 1 ≤ P
  Q_ge : 1 ≤ Q
  R_ge : 1 ≤ R
  E_ge : 1 ≤ E
  central : B + A * U ≤ P * Q
  right_cap : R + Q ≤ A * U
  p_to_a : 1 + P ≤ a * U
  e_to_a : E + A ≤ a * Q
  p_e_to_r : P + B * E ≤ A * R
  terminal : 1 + A * B ≤ R * E
  area : a + 2 * (A + B + U) ≤ H

/-- The exact residual seam: only the two additive caps remain to construct. -/
def HullSevenType6ReflectionCoreData.toReflectionData
    {H : ℝ} (X : HullSevenType6ReflectionCoreData H)
    (p_cap : X.P ≤ X.A + X.B - 1)
    (q_cap : X.Q ≤ X.B + X.U - 1) :
    HullSevenType6ReflectionData H where
  a := X.a
  A := X.A
  B := X.B
  U := X.U
  P := X.P
  Q := X.Q
  R := X.R
  E := X.E
  a_ge := X.a_ge
  A_ge := X.A_ge
  B_ge := X.B_ge
  U_ge := X.U_ge
  P_ge := X.P_ge
  Q_ge := X.Q_ge
  R_ge := X.R_ge
  E_ge := X.E_ge
  p_cap := p_cap
  q_cap := q_cap
  central := X.central
  right_cap := X.right_cap
  p_to_a := X.p_to_a
  e_to_a := X.e_to_a
  p_e_to_r := X.p_e_to_r
  terminal := X.terminal
  area := X.area

/-- Positive raw determinant magnitudes in the rotation-one chart.

The dictionary is

```
a=d01, e=d02, x=d03, l=-d04, n=-d05, G=-d06,
A=d12, p=d13, L=d14, c=-d15, h=-d16,
B=d23, q=d24, R=d25, m=d26,
C=d34, r=d35, k=d36, D=d45, S=d46, Z=d56.
```

The four ear rows are retained to document the exact cap input available
from point geometry.  They are deliberately not used to manufacture the two
geometric-mean caps. -/
structure HullSevenType6RawReflectionData (H : ℝ) where
  a : ℝ
  e : ℝ
  x : ℝ
  l : ℝ
  n : ℝ
  G : ℝ
  A : ℝ
  p : ℝ
  L : ℝ
  c : ℝ
  h : ℝ
  B : ℝ
  q : ℝ
  R : ℝ
  m : ℝ
  C : ℝ
  r : ℝ
  k : ℝ
  D : ℝ
  S : ℝ
  Z : ℝ

  a_ge : 1 ≤ a
  e_ge : 1 ≤ e
  x_ge : 1 ≤ x
  l_ge : 1 ≤ l
  n_ge : 1 ≤ n
  G_ge : 1 ≤ G
  A_ge : 1 ≤ A
  p_ge : 1 ≤ p
  L_ge : 1 ≤ L
  c_ge : 1 ≤ c
  h_ge : 1 ≤ h
  B_ge : 1 ≤ B
  q_ge : 1 ≤ q
  R_ge : 1 ≤ R
  m_ge : 1 ≤ m
  C_ge : 1 ≤ C
  r_ge : 1 ≤ r
  k_ge : 1 ≤ k
  D_ge : 1 ≤ D
  S_ge : 1 ≤ S
  Z_ge : 1 ≤ Z

  p_left_ear : 1 ≤ A + B - p
  p_right_ear : 1 ≤ G + Z - n
  q_left_ear : 1 ≤ B + C - q
  q_right_ear : 1 ≤ D + Z - S

  gp1234 : (p : ℝ) * q = A * C + L * B
  gp0456 : (n : ℝ) * S = G * D + l * Z
  gp1245 : (A : ℝ) * D = L * R + c * q
  gp0346 : (G : ℝ) * C = l * k + x * S
  gp0134 : (a : ℝ) * C = x * L + l * p
  gp0145 : (a : ℝ) * D = l * c + n * L
  gp0124 : (a : ℝ) * q = e * L + l * A
  gp0146 : (a : ℝ) * S = l * h + G * L
  gp1236 : (A : ℝ) * k = p * m + h * B
  gp0256 : (G : ℝ) * R = e * Z + n * m
  gp0236 : (e : ℝ) * k = x * m + G * B
  gp1256 : (h : ℝ) * R = A * Z + c * m

  area : a + A + B + C + D + Z + G ≤ H

/-- The honest geometric-mean construction.  It proves rows 3--8 and the
area row; no additive cap is assumed here. -/
noncomputable def HullSevenType6RawReflectionData.toCoreData
    {H : ℝ} (X : HullSevenType6RawReflectionData H) :
    HullSevenType6ReflectionCoreData H := by
  let Abar := Real.sqrt (X.A * X.G)
  let Bbar := Real.sqrt (X.B * X.Z)
  let U := Real.sqrt (X.C * X.D)
  let P := Real.sqrt (X.p * X.n)
  let Q := Real.sqrt (X.q * X.S)
  let Rbar := Real.sqrt (X.R * X.k)
  let E := Real.sqrt (X.e * X.h)
  let V := Real.sqrt (X.L * X.l)
  let W := Real.sqrt (X.x * X.c)

  have ha : 0 ≤ X.a := le_trans (by norm_num) X.a_ge
  have he : 0 ≤ X.e := le_trans (by norm_num) X.e_ge
  have hx : 0 ≤ X.x := le_trans (by norm_num) X.x_ge
  have hl : 0 ≤ X.l := le_trans (by norm_num) X.l_ge
  have hn : 0 ≤ X.n := le_trans (by norm_num) X.n_ge
  have hG : 0 ≤ X.G := le_trans (by norm_num) X.G_ge
  have hA : 0 ≤ X.A := le_trans (by norm_num) X.A_ge
  have hp : 0 ≤ X.p := le_trans (by norm_num) X.p_ge
  have hL : 0 ≤ X.L := le_trans (by norm_num) X.L_ge
  have hc : 0 ≤ X.c := le_trans (by norm_num) X.c_ge
  have hh : 0 ≤ X.h := le_trans (by norm_num) X.h_ge
  have hB : 0 ≤ X.B := le_trans (by norm_num) X.B_ge
  have hq : 0 ≤ X.q := le_trans (by norm_num) X.q_ge
  have hR : 0 ≤ X.R := le_trans (by norm_num) X.R_ge
  have hm : 0 ≤ X.m := le_trans (by norm_num) X.m_ge
  have hC : 0 ≤ X.C := le_trans (by norm_num) X.C_ge
  have hk : 0 ≤ X.k := le_trans (by norm_num) X.k_ge
  have hD : 0 ≤ X.D := le_trans (by norm_num) X.D_ge
  have hS : 0 ≤ X.S := le_trans (by norm_num) X.S_ge
  have hZ : 0 ≤ X.Z := le_trans (by norm_num) X.Z_ge

  have hAge : 1 ≤ Abar :=
    hullSeven_type6_one_le_sqrt_mul X.A_ge X.G_ge
  have hBge : 1 ≤ Bbar :=
    hullSeven_type6_one_le_sqrt_mul X.B_ge X.Z_ge
  have hUge : 1 ≤ U :=
    hullSeven_type6_one_le_sqrt_mul X.C_ge X.D_ge
  have hPge : 1 ≤ P :=
    hullSeven_type6_one_le_sqrt_mul X.p_ge X.n_ge
  have hQge : 1 ≤ Q :=
    hullSeven_type6_one_le_sqrt_mul X.q_ge X.S_ge
  have hRge : 1 ≤ Rbar :=
    hullSeven_type6_one_le_sqrt_mul X.R_ge X.k_ge
  have hEge : 1 ≤ E :=
    hullSeven_type6_one_le_sqrt_mul X.e_ge X.h_ge
  have hVge : 1 ≤ V :=
    hullSeven_type6_one_le_sqrt_mul X.L_ge X.l_ge
  have hWge : 1 ≤ W :=
    hullSeven_type6_one_le_sqrt_mul X.x_ge X.c_ge

  have hcentralStrong : Abar * U + V * Bbar ≤ P * Q := by
    have hraw := hullSeven_type6_paired_sum_gm
      hp hq hn hS
      (mul_nonneg hA hC) (mul_nonneg hL hB)
      (mul_nonneg hG hD) (mul_nonneg hl hZ)
      X.gp1234 X.gp0456
    have h₁ : Real.sqrt ((X.A * X.C) * (X.G * X.D)) = Abar * U := by
      dsimp [Abar, U]
      exact hullSeven_type6_sqrt_four_reassociate hA hC hG hD
    have h₂ : Real.sqrt ((X.L * X.B) * (X.l * X.Z)) = V * Bbar := by
      dsimp [V, Bbar]
      exact hullSeven_type6_sqrt_four_reassociate hL hB hl hZ
    rw [h₁, h₂] at hraw
    exact hraw

  have hrightStrong : V * Rbar + W * Q ≤ Abar * U := by
    have hraw := hullSeven_type6_paired_sum_gm
      hA hD hG hC
      (mul_nonneg hL hR) (mul_nonneg hc hq)
      (mul_nonneg hl hk) (mul_nonneg hx hS)
      X.gp1245 X.gp0346
    have h₁ : Real.sqrt ((X.L * X.R) * (X.l * X.k)) = V * Rbar := by
      dsimp [V, Rbar]
      exact hullSeven_type6_sqrt_four_reassociate hL hR hl hk
    have h₂ : Real.sqrt ((X.c * X.q) * (X.x * X.S)) = W * Q := by
      calc
        Real.sqrt ((X.c * X.q) * (X.x * X.S)) =
            Real.sqrt (X.c * X.x) * Real.sqrt (X.q * X.S) :=
          hullSeven_type6_sqrt_four_reassociate hc hq hx hS
        _ = W * Q := by
          dsimp [W, Q]
          rw [mul_comm X.c X.x]
    have h₃ : Real.sqrt (X.A * X.G) * Real.sqrt (X.D * X.C) =
        Abar * U := by
      dsimp [Abar, U]
      rw [mul_comm X.D X.C]
    rw [h₁, h₂, h₃] at hraw
    exact hraw

  have hpToAStrong : W * V + V * P ≤ X.a * U := by
    have hraw := hullSeven_type6_paired_sum_gm
      ha hC ha hD
      (mul_nonneg hx hL) (mul_nonneg hl hp)
      (mul_nonneg hl hc) (mul_nonneg hn hL)
      X.gp0134 X.gp0145
    have h₁ : Real.sqrt ((X.x * X.L) * (X.l * X.c)) = W * V := by
      calc
        Real.sqrt ((X.x * X.L) * (X.l * X.c)) =
            Real.sqrt ((X.x * X.L) * (X.c * X.l)) := by
          congr 1
          ring
        _ = W * V := by
          dsimp [W, V]
          exact hullSeven_type6_sqrt_four_reassociate hx hL hc hl
    have h₂ : Real.sqrt ((X.l * X.p) * (X.n * X.L)) = V * P := by
      calc
        Real.sqrt ((X.l * X.p) * (X.n * X.L)) =
            Real.sqrt ((X.L * X.l) * (X.p * X.n)) := by
          congr 1
          ring
        _ = V * P := by
          dsimp [V, P]
          exact Real.sqrt_mul (mul_nonneg hL hl) (X.p * X.n)
    have haa : Real.sqrt (X.a * X.a) = X.a := by
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
    rw [h₁, h₂, haa] at hraw
    exact hraw

  have heToAStrong : E * V + Abar * V ≤ X.a * Q := by
    have hraw := hullSeven_type6_paired_sum_gm
      ha hq ha hS
      (mul_nonneg he hL) (mul_nonneg hl hA)
      (mul_nonneg hl hh) (mul_nonneg hG hL)
      X.gp0124 X.gp0146
    have h₁ : Real.sqrt ((X.e * X.L) * (X.l * X.h)) = E * V := by
      calc
        Real.sqrt ((X.e * X.L) * (X.l * X.h)) =
            Real.sqrt ((X.e * X.L) * (X.h * X.l)) := by
          congr 1
          ring
        _ = E * V := by
          dsimp [E, V]
          exact hullSeven_type6_sqrt_four_reassociate he hL hh hl
    have h₂ : Real.sqrt ((X.l * X.A) * (X.G * X.L)) = Abar * V := by
      calc
        Real.sqrt ((X.l * X.A) * (X.G * X.L)) =
            Real.sqrt ((X.A * X.l) * (X.G * X.L)) := by
          congr 1
          ring
        _ = Abar * V := by
          dsimp [Abar, V]
          simpa [mul_comm X.l X.L] using
            (hullSeven_type6_sqrt_four_reassociate hA hl hG hL)
    have haa : Real.sqrt (X.a * X.a) = X.a := by
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
    rw [h₁, h₂, haa] at hraw
    exact hraw

  have hpERStrong : X.m * P + E * Bbar ≤ Abar * Rbar := by
    have hraw := hullSeven_type6_paired_sum_gm
      hA hk hG hR
      (mul_nonneg hp hm) (mul_nonneg hh hB)
      (mul_nonneg hn hm) (mul_nonneg he hZ)
      X.gp1236 (by linarith [X.gp0256] : X.G * X.R = X.n * X.m + X.e * X.Z)
    have h₁ : Real.sqrt ((X.p * X.m) * (X.n * X.m)) = X.m * P := by
      calc
        Real.sqrt ((X.p * X.m) * (X.n * X.m)) =
            Real.sqrt (X.p * X.n) * Real.sqrt (X.m * X.m) :=
          hullSeven_type6_sqrt_four_reassociate hp hm hn hm
        _ = X.m * P := by
          have hmm : Real.sqrt (X.m * X.m) = X.m := by
            rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hm]
          dsimp [P]
          rw [hmm]
          ring
    have h₂ : Real.sqrt ((X.h * X.B) * (X.e * X.Z)) = E * Bbar := by
      calc
        Real.sqrt ((X.h * X.B) * (X.e * X.Z)) =
            Real.sqrt (X.h * X.e) * Real.sqrt (X.B * X.Z) :=
          hullSeven_type6_sqrt_four_reassociate hh hB he hZ
        _ = E * Bbar := by
          dsimp [E, Bbar]
          rw [mul_comm X.h X.e]
    have h₃ : Real.sqrt (X.A * X.G) * Real.sqrt (X.k * X.R) =
        Abar * Rbar := by
      dsimp [Abar, Rbar]
      rw [mul_comm X.k X.R]
    rw [h₁, h₂, h₃] at hraw
    exact hraw

  have hterminalStrong : X.m * W + Abar * Bbar ≤ E * Rbar := by
    have hraw := hullSeven_type6_paired_sum_gm
      he hk hh hR
      (mul_nonneg hx hm) (mul_nonneg hG hB)
      (mul_nonneg hc hm) (mul_nonneg hA hZ)
      X.gp0236 (by simpa [add_comm] using X.gp1256)
    have h₁ : Real.sqrt ((X.x * X.m) * (X.c * X.m)) = X.m * W := by
      calc
        Real.sqrt ((X.x * X.m) * (X.c * X.m)) =
            Real.sqrt (X.x * X.c) * Real.sqrt (X.m * X.m) :=
          hullSeven_type6_sqrt_four_reassociate hx hm hc hm
        _ = X.m * W := by
          have hmm : Real.sqrt (X.m * X.m) = X.m := by
            rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hm]
          dsimp [W]
          rw [hmm]
          ring
    have h₂ : Real.sqrt ((X.G * X.B) * (X.A * X.Z)) = Abar * Bbar := by
      calc
        Real.sqrt ((X.G * X.B) * (X.A * X.Z)) =
            Real.sqrt (X.G * X.A) * Real.sqrt (X.B * X.Z) :=
          hullSeven_type6_sqrt_four_reassociate hG hB hA hZ
        _ = Abar * Bbar := by
          dsimp [Abar, Bbar]
          rw [mul_comm X.G X.A]
    have h₃ : Real.sqrt (X.e * X.h) * Real.sqrt (X.k * X.R) =
        E * Rbar := by
      dsimp [E, Rbar]
      rw [mul_comm X.k X.R]
    rw [h₁, h₂, h₃] at hraw
    exact hraw

  have hareaA := hullSeven_type6_two_sqrt_mul_le_add hA hG
  have hareaB := hullSeven_type6_two_sqrt_mul_le_add hB hZ
  have hareaU := hullSeven_type6_two_sqrt_mul_le_add hC hD

  refine
    { a := X.a
      A := Abar
      B := Bbar
      U := U
      P := P
      Q := Q
      R := Rbar
      E := E
      a_ge := X.a_ge
      A_ge := hAge
      B_ge := hBge
      U_ge := hUge
      P_ge := hPge
      Q_ge := hQge
      R_ge := hRge
      E_ge := hEge
      central := ?_
      right_cap := ?_
      p_to_a := ?_
      e_to_a := ?_
      p_e_to_r := ?_
      terminal := ?_
      area := ?_ }
  · have hweak : Bbar ≤ V * Bbar := by
      have hB0 : 0 ≤ Bbar := le_trans (by norm_num) hBge
      simpa using mul_le_mul_of_nonneg_right hVge hB0
    linarith
  · have hweakR : Rbar ≤ V * Rbar := by
      have hR0 : 0 ≤ Rbar := le_trans (by norm_num) hRge
      simpa using mul_le_mul_of_nonneg_right hVge hR0
    have hweakQ : Q ≤ W * Q := by
      have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQge
      simpa using mul_le_mul_of_nonneg_right hWge hQ0
    linarith
  · have hweakOne : 1 ≤ W * V := by
      exact one_le_mul_of_one_le_of_one_le hWge hVge
    have hweakP : P ≤ V * P := by
      have hP0 : 0 ≤ P := le_trans (by norm_num) hPge
      simpa using mul_le_mul_of_nonneg_right hVge hP0
    linarith
  · have hweakE : E ≤ E * V := by
      have hE0 : 0 ≤ E := le_trans (by norm_num) hEge
      simpa using mul_le_mul_of_nonneg_left hVge hE0
    have hweakA : Abar ≤ Abar * V := by
      have hA0 : 0 ≤ Abar := le_trans (by norm_num) hAge
      simpa using mul_le_mul_of_nonneg_left hVge hA0
    linarith
  · have hweakP : P ≤ X.m * P := by
      have hP0 : 0 ≤ P := le_trans (by norm_num) hPge
      simpa using mul_le_mul_of_nonneg_right X.m_ge hP0
    linarith
  · have hweakOne : 1 ≤ X.m * W := by
      exact one_le_mul_of_one_le_of_one_le X.m_ge hWge
    linarith
  · dsimp [Abar, Bbar, U] at hareaA hareaB hareaU ⊢
    linarith [X.area]

/-- Final conversion with the two genuinely additional cap hypotheses. -/
noncomputable def HullSevenType6RawReflectionData.toReflectionData
    {H : ℝ} (X : HullSevenType6RawReflectionData H)
    (p_cap : Real.sqrt (X.p * X.n) ≤
      Real.sqrt (X.A * X.G) + Real.sqrt (X.B * X.Z) - 1)
    (q_cap : Real.sqrt (X.q * X.S) ≤
      Real.sqrt (X.B * X.Z) + Real.sqrt (X.C * X.D) - 1) :
    HullSevenType6ReflectionData H :=
  X.toCoreData.toReflectionData p_cap q_cap

/-- Equivalent geometric seam expressed as the two missing cross-square
bounds.  The raw ear floors then supply the `-1` in each scalar cap. -/
noncomputable def HullSevenType6RawReflectionData.toReflectionDataOfCrossSquares
    {H : ℝ} (X : HullSevenType6RawReflectionData H)
    (p_cross :
      (Real.sqrt (X.A * X.Z) - Real.sqrt (X.B * X.G)) ^ 2 ≤
        (Real.sqrt (X.p * (X.G + X.Z - X.n)) -
          Real.sqrt ((X.A + X.B - X.p) * X.n)) ^ 2)
    (q_cross :
      (Real.sqrt (X.B * X.D) - Real.sqrt (X.C * X.Z)) ^ 2 ≤
        (Real.sqrt (X.q * (X.D + X.Z - X.S)) -
          Real.sqrt ((X.B + X.C - X.q) * X.S)) ^ 2) :
    HullSevenType6ReflectionData H := by
  apply X.toReflectionData
  · exact hullSeven_type6_gm_cap_of_cross_square
      X.p_ge X.p_left_ear X.n_ge X.p_right_ear
      X.A_ge X.B_ge X.G_ge X.Z_ge
      (by ring) (by ring) p_cross
  · exact hullSeven_type6_gm_cap_of_cross_square
      X.q_ge X.q_left_ear X.S_ge X.q_right_ear
      X.B_ge X.C_ge X.Z_ge X.D_ge
      (by ring) (by ring) q_cross

/-- Generic normalized bracket data in the honest rotation-one chart. -/
structure HullSevenType6BracketData (H : ℝ) where
  bracket : HullSevenType6Index → HullSevenType6Index → ℝ
  skew : ∀ i j, bracket i j = -bracket j i
  plucker : ∀ i j k l,
    bracket i j * bracket k l -
      bracket i k * bracket j l +
      bracket i l * bracket j k = 0

  d01_ge : 1 ≤ bracket 0 1
  d02_ge : 1 ≤ bracket 0 2
  d03_ge : 1 ≤ bracket 0 3
  neg_d04_ge : 1 ≤ -bracket 0 4
  neg_d05_ge : 1 ≤ -bracket 0 5
  neg_d06_ge : 1 ≤ -bracket 0 6
  d12_ge : 1 ≤ bracket 1 2
  d13_ge : 1 ≤ bracket 1 3
  d14_ge : 1 ≤ bracket 1 4
  neg_d15_ge : 1 ≤ -bracket 1 5
  neg_d16_ge : 1 ≤ -bracket 1 6
  d23_ge : 1 ≤ bracket 2 3
  d24_ge : 1 ≤ bracket 2 4
  d25_ge : 1 ≤ bracket 2 5
  d26_ge : 1 ≤ bracket 2 6
  d34_ge : 1 ≤ bracket 3 4
  d35_ge : 1 ≤ bracket 3 5
  d36_ge : 1 ≤ bracket 3 6
  d45_ge : 1 ≤ bracket 4 5
  d46_ge : 1 ≤ bracket 4 6
  d56_ge : 1 ≤ bracket 5 6

  ear123 : 1 ≤ bracket 1 2 + bracket 2 3 - bracket 1 3
  ear560 : 1 ≤ bracket 5 6 - bracket 0 6 + bracket 0 5
  ear234 : 1 ≤ bracket 2 3 + bracket 3 4 - bracket 2 4
  ear456 : 1 ≤ bracket 4 5 + bracket 5 6 - bracket 4 6
  area : bracket 0 1 + bracket 1 2 + bracket 2 3 + bracket 3 4 +
      bracket 4 5 + bracket 5 6 - bracket 0 6 ≤ H

/-- Every raw identity is obtained from the generic rank-two Pluecker row;
none is a separately assumed recurrence of the bracket packet. -/
def HullSevenType6BracketData.toRawReflectionData
    {H : ℝ} (X : HullSevenType6BracketData H) :
    HullSevenType6RawReflectionData H := by
  refine
    { a := X.bracket 0 1
      e := X.bracket 0 2
      x := X.bracket 0 3
      l := -X.bracket 0 4
      n := -X.bracket 0 5
      G := -X.bracket 0 6
      A := X.bracket 1 2
      p := X.bracket 1 3
      L := X.bracket 1 4
      c := -X.bracket 1 5
      h := -X.bracket 1 6
      B := X.bracket 2 3
      q := X.bracket 2 4
      R := X.bracket 2 5
      m := X.bracket 2 6
      C := X.bracket 3 4
      r := X.bracket 3 5
      k := X.bracket 3 6
      D := X.bracket 4 5
      S := X.bracket 4 6
      Z := X.bracket 5 6
      a_ge := X.d01_ge
      e_ge := X.d02_ge
      x_ge := X.d03_ge
      l_ge := X.neg_d04_ge
      n_ge := X.neg_d05_ge
      G_ge := X.neg_d06_ge
      A_ge := X.d12_ge
      p_ge := X.d13_ge
      L_ge := X.d14_ge
      c_ge := X.neg_d15_ge
      h_ge := X.neg_d16_ge
      B_ge := X.d23_ge
      q_ge := X.d24_ge
      R_ge := X.d25_ge
      m_ge := X.d26_ge
      C_ge := X.d34_ge
      r_ge := X.d35_ge
      k_ge := X.d36_ge
      D_ge := X.d45_ge
      S_ge := X.d46_ge
      Z_ge := X.d56_ge
      p_left_ear := by linarith [X.ear123]
      p_right_ear := by linarith [X.ear560]
      q_left_ear := by linarith [X.ear234]
      q_right_ear := by linarith [X.ear456]
      gp1234 := ?_
      gp0456 := ?_
      gp1245 := ?_
      gp0346 := ?_
      gp0134 := ?_
      gp0145 := ?_
      gp0124 := ?_
      gp0146 := ?_
      gp1236 := ?_
      gp0256 := ?_
      gp0236 := ?_
      gp1256 := ?_
      area := X.area }
  · nlinarith [X.plucker 1 2 3 4]
  · nlinarith [X.plucker 0 4 5 6]
  · nlinarith [X.plucker 1 2 4 5]
  · nlinarith [X.plucker 0 3 4 6]
  · nlinarith [X.plucker 0 1 3 4]
  · nlinarith [X.plucker 0 1 4 5]
  · nlinarith [X.plucker 0 1 2 4]
  · nlinarith [X.plucker 0 1 4 6]
  · nlinarith [X.plucker 1 2 3 6]
  · nlinarith [X.plucker 0 2 5 6]
  · nlinarith [X.plucker 0 2 3 6]
  · nlinarith [X.plucker 1 2 5 6]

end Heilbronn8.TriHull
