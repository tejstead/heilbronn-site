import Heilbronn8.V8
import Heilbronn8.TriHull.HullSevenType4Scalar

/-!
# Bracket adapter for hull-seven type 4

Rotate the canonical type-4 wheel by three positions.  In this presentation
all cyclic one- and two-step brackets are positive.  Among the signed
three-step brackets only `u₄` and `u₅` are negative.  Pairing the exact
Pluecker rows in this chart produces precisely the reflection-GM packet
already closed by `HullSevenType4ScalarData`.

The adapter retains exactly the four ordinary ear caps used by the scalar
proof and the fan-area row.  No wraparound ear, geometric-mean ear cap,
coordinate choice, or numerical certificate is assumed.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

open scoped BigOperators

abbrev HullSevenType4Index := ZMod 7

/-- Positive magnitude of the signed three-step bracket in the preferred
type-4 chart. -/
def hullSevenType4ThreeStepMagnitude
    (bracket : HullSevenType4Index → HullSevenType4Index → ℝ)
    (i : HullSevenType4Index) : ℝ :=
  if i = 4 ∨ i = 5 then -bracket i (i + 3) else bracket i (i + 3)

/-- Generic normalized bracket data in the rotated type-4 presentation. -/
structure HullSevenType4BracketData (H : ℝ) where
  bracket : HullSevenType4Index → HullSevenType4Index → ℝ
  skew : ∀ i j, bracket i j = -bracket j i
  plucker : ∀ i j k l,
    bracket i j * bracket k l - bracket i k * bracket j l +
      bracket i l * bracket j k = 0
  adjacent_ge : ∀ i, 1 ≤ bracket i (i + 1)
  twoStep_ge : ∀ i, 1 ≤ bracket i (i + 2)
  threeStepMagnitude_ge : ∀ i,
    1 ≤ hullSevenType4ThreeStepMagnitude bracket i
  ear0 : bracket 0 2 ≤ bracket 0 1 + bracket 1 2 - 1
  ear1 : bracket 1 3 ≤ bracket 1 2 + bracket 2 3 - 1
  ear2 : bracket 2 4 ≤ bracket 2 3 + bracket 3 4 - 1
  ear3 : bracket 3 5 ≤ bracket 3 4 + bracket 4 5 - 1
  area : (∑ i, bracket i (i + 1)) ≤ H

namespace HullSevenType4BracketData

/-- Cyclic boundary cells. -/
def a {H : ℝ} (D : HullSevenType4BracketData H)
    (i : HullSevenType4Index) : ℝ :=
  D.bracket i (i + 1)

/-- Cyclic two-step chords. -/
def b {H : ℝ} (D : HullSevenType4BracketData H)
    (i : HullSevenType4Index) : ℝ :=
  D.bracket i (i + 2)

/-- Signed cyclic three-step chords.  Thus `u 4` and `u 5` are negative. -/
def u {H : ℝ} (D : HullSevenType4BracketData H)
    (i : HullSevenType4Index) : ℝ :=
  D.bracket i (i + 3)

/-- The consecutive four-index Pluecker row. -/
lemma e2 {H : ℝ} (D : HullSevenType4BracketData H)
    (i : HullSevenType4Index) :
    D.b i * D.b (i + 1) =
      D.a i * D.a (i + 2) + D.a (i + 1) * D.u i := by
  have hp := D.plucker i (i + 1) (i + 2) (i + 3)
  dsimp [a, b, u]
  norm_num [add_assoc] at hp ⊢
  nlinarith

/-- The separated four-index Pluecker row. -/
lemma e1 {H : ℝ} (D : HullSevenType4BracketData H)
    (i : HullSevenType4Index) :
    D.a i * D.a (i + 3) =
      D.u i * D.u (i + 1) + D.u (i + 4) * D.b (i + 1) := by
  have hwrap : i + 4 + 3 = i := by
    rw [add_assoc, show (4 : ZMod 7) + 3 = 0 by decide, add_zero]
  have hflip :
      D.bracket i (i + 4) =
        -D.bracket (i + 4) (i + 4 + 3) := by
    rw [hwrap]
    exact D.skew i (i + 4)
  have hp := D.plucker i (i + 1) (i + 3) (i + 4)
  dsimp [a, b, u]
  rw [hflip] at hp
  norm_num [add_assoc] at hp ⊢
  nlinarith

private lemma one_le_sqrt_mul {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ Real.sqrt (x * y) := by
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

/-- Pair two positive additive rows by multiplicative Minkowski. -/
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
    have hab :
        (Real.sqrt ((a₁ + b₁) * (a₂ + b₂))) ^ 2 =
          (a₁ + b₁) * (a₂ + b₂) :=
      Real.sq_sqrt (mul_nonneg (add_nonneg ha₁ hb₁)
        (add_nonneg ha₂ hb₂))
    have hcross :
        2 * Real.sqrt (a₁ * a₂) * Real.sqrt (b₁ * b₂) ≤
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
  have hminkowski :
      Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
        Real.sqrt ((a₁ + b₁) * (a₂ + b₂)) :=
    (sq_le_sq₀ hleft hright).mp hsquare
  calc
    Real.sqrt (a₁ * a₂) + Real.sqrt (b₁ * b₂) ≤
        Real.sqrt ((a₁ + b₁) * (a₂ + b₂)) := hminkowski
    _ = Real.sqrt ((x₁ * y₁) * (x₂ * y₂)) := by rw [h₁, h₂]
    _ = Real.sqrt (x₁ * x₂) * Real.sqrt (y₁ * y₂) :=
      sqrt_four_reassociate hx₁ hy₁ hx₂ hy₂

/-- The preferred type-4 determinant chart constructs the complete shared
reflection-GM scalar packet. -/
noncomputable def toScalarData {H : ℝ}
    (D : HullSevenType4BracketData H) : HullSevenType4ScalarData H := by
  let a : HullSevenType4Index → ℝ := D.a
  let b : HullSevenType4Index → ℝ := D.b
  let u : HullSevenType4Index → ℝ := D.u
  let x : ℝ := -u 4
  let y : ℝ := -u 5
  let X : ℝ := Real.sqrt (a 0 * a 4)
  let Y : ℝ := Real.sqrt (a 1 * a 3)
  let Z : ℝ := a 2
  let W : ℝ := Real.sqrt (a 5 * a 6)
  let r : ℝ := Real.sqrt (b 0 * b 3)
  let s : ℝ := Real.sqrt (b 1 * b 2)
  let U : ℝ := Real.sqrt (u 0 * u 2)
  let Q : ℝ := u 1
  let R : ℝ := Real.sqrt (u 3 * u 6)
  let M : ℝ := Real.sqrt (x * y)
  let A : ℝ := (a 0 + a 4) / 2
  let B : ℝ := (a 1 + a 3) / 2

  have ha : ∀ i, 1 ≤ a i := fun i => D.adjacent_ge i
  have hb : ∀ i, 1 ≤ b i := fun i => D.twoStep_ge i
  have hu0 : 1 ≤ u 0 := by
    have h := D.threeStepMagnitude_ge 0
    norm_num [u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h
  have hu1 : 1 ≤ u 1 := by
    have h := D.threeStepMagnitude_ge 1
    norm_num [u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h
  have hu2 : 1 ≤ u 2 := by
    have h := D.threeStepMagnitude_ge 2
    norm_num [u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h
  have hu3 : 1 ≤ u 3 := by
    have h := D.threeStepMagnitude_ge 3
    norm_num [u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h
  have hx : 1 ≤ x := by
    have h := D.threeStepMagnitude_ge 4
    norm_num [x, u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h
  have hy : 1 ≤ y := by
    have h := D.threeStepMagnitude_ge 5
    norm_num [y, u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h
  have hu6 : 1 ≤ u 6 := by
    have h := D.threeStepMagnitude_ge 6
    norm_num [u, HullSevenType4BracketData.u,
      hullSevenType4ThreeStepMagnitude] at h ⊢
    exact h

  have ha0 : 0 ≤ a 0 := le_trans (by norm_num) (ha 0)
  have ha1 : 0 ≤ a 1 := le_trans (by norm_num) (ha 1)
  have ha2 : 0 ≤ a 2 := le_trans (by norm_num) (ha 2)
  have ha3 : 0 ≤ a 3 := le_trans (by norm_num) (ha 3)
  have ha4 : 0 ≤ a 4 := le_trans (by norm_num) (ha 4)
  have ha5 : 0 ≤ a 5 := le_trans (by norm_num) (ha 5)
  have ha6 : 0 ≤ a 6 := le_trans (by norm_num) (ha 6)
  have hb0 : 0 ≤ b 0 := le_trans (by norm_num) (hb 0)
  have hb1 : 0 ≤ b 1 := le_trans (by norm_num) (hb 1)
  have hb2 : 0 ≤ b 2 := le_trans (by norm_num) (hb 2)
  have hb3 : 0 ≤ b 3 := le_trans (by norm_num) (hb 3)
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
  have hrsq : r ^ 2 = b 0 * b 3 := by
    dsimp [r]
    exact Real.sq_sqrt (mul_nonneg hb0 hb3)
  have hssqRaw : s ^ 2 = b 1 * b 2 := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hb1 hb2)

  have he20 := D.e2 0
  have he21 := D.e2 1
  have he22 := D.e2 2
  have he10 := D.e1 0
  have he11 := D.e1 1
  have he12 := D.e1 2
  have he14 := D.e1 4
  have he16 := D.e1 6
  norm_num [a, b, u, add_assoc] at he20 he21 he22 he10 he11 he12 he14 he16
  change a 4 * a 0 = u 4 * u 5 + u 1 * b 5 at he14
  change a 6 * a 2 = u 6 * u 0 + u 3 * b 0 at he16

  have hrs : X * Z + Y * U ≤ r * s := by
    have hraw := paired_sum_gm
      hb0 hb1 hb3 hb2
      (mul_nonneg ha0 ha2) (mul_nonneg ha1 hu0n)
      (mul_nonneg ha4 ha2) (mul_nonneg ha3 hu2n)
      he20 (by nlinarith [he22])
    have hfirst :
        Real.sqrt ((a 0 * a 2) * (a 4 * a 2)) = X * Z := by
      calc
        Real.sqrt ((a 0 * a 2) * (a 4 * a 2)) =
            Real.sqrt (a 0 * a 4) * Real.sqrt (a 2 * a 2) :=
          sqrt_four_reassociate ha0 ha2 ha4 ha2
        _ = X * Z := by rw [sqrt_mul_self ha2]
    have hsecond :
        Real.sqrt ((a 1 * u 0) * (a 3 * u 2)) = Y * U := by
      calc
        Real.sqrt ((a 1 * u 0) * (a 3 * u 2)) =
            Real.sqrt (a 1 * a 3) * Real.sqrt (u 0 * u 2) :=
          sqrt_four_reassociate ha1 hu0n ha3 hu2n
        _ = Y * U := rfl
    rw [hfirst, hsecond] at hraw
    exact hraw

  have hs_sq : s ^ 2 = Y ^ 2 + Z * Q := by
    dsimp [Z, Q]
    nlinarith [hssqRaw, hYsq, he21]

  have hUQ : X * Y + M * s ≤ U * Q := by
    have hrow0 : u 0 * u 1 = a 0 * a 3 + x * b 1 := by
      dsimp [x]
      nlinarith [he10]
    have hrow1 : u 2 * u 1 = a 4 * a 1 + y * b 2 := by
      dsimp [y]
      nlinarith [he11]
    have hraw := paired_sum_gm
      hu0n hu1n hu2n hu1n
      (mul_nonneg ha0 ha3) (mul_nonneg hxn hb1)
      (mul_nonneg ha4 ha1) (mul_nonneg hyn hb2)
      hrow0 hrow1
    have hfirst :
        Real.sqrt ((a 0 * a 3) * (a 4 * a 1)) = X * Y := by
      calc
        Real.sqrt ((a 0 * a 3) * (a 4 * a 1)) =
            Real.sqrt (a 0 * a 4) * Real.sqrt (a 3 * a 1) :=
          sqrt_four_reassociate ha0 ha3 ha4 ha1
        _ = X * Y := by rw [mul_comm (a 3) (a 1)]
    have hsecond :
        Real.sqrt ((x * b 1) * (y * b 2)) = M * s := by
      calc
        Real.sqrt ((x * b 1) * (y * b 2)) =
            Real.sqrt (x * y) * Real.sqrt (b 1 * b 2) :=
          sqrt_four_reassociate hxn hb1 hyn hb2
        _ = M * s := rfl
    have hq : Real.sqrt (u 1 * u 1) = Q := by
      rw [sqrt_mul_self hu1n]
    rw [hfirst, hsecond, hq] at hraw
    exact hraw

  have hZW : R * (U + r) ≤ Z * W := by
    have hrow6 : a 2 * a 6 = u 0 * u 6 + u 3 * b 0 := by
      nlinarith [he16]
    have hraw := paired_sum_gm
      ha2 ha5 ha2 ha6
      (mul_nonneg hu2n hu3n) (mul_nonneg hu6n hb3)
      (mul_nonneg hu0n hu6n) (mul_nonneg hu3n hb0)
      he12 hrow6
    have hfirst :
        Real.sqrt ((u 2 * u 3) * (u 0 * u 6)) = U * R := by
      calc
        Real.sqrt ((u 2 * u 3) * (u 0 * u 6)) =
            Real.sqrt (u 2 * u 0) * Real.sqrt (u 3 * u 6) :=
          sqrt_four_reassociate hu2n hu3n hu0n hu6n
        _ = U * R := by rw [mul_comm (u 2) (u 0)]
    have hsecond :
        Real.sqrt ((u 6 * b 3) * (u 3 * b 0)) = R * r := by
      calc
        Real.sqrt ((u 6 * b 3) * (u 3 * b 0)) =
            Real.sqrt (u 6 * u 3) * Real.sqrt (b 3 * b 0) :=
          sqrt_four_reassociate hu6n hb3 hu3n hb0
        _ = R * r := by
          rw [mul_comm (u 6) (u 3), mul_comm (b 3) (b 0)]
    have hZ : Real.sqrt (a 2 * a 2) = Z := by
      rw [sqrt_mul_self ha2]
    rw [hfirst, hsecond, hZ] at hraw
    nlinarith

  have hQcap : Q ≤ X ^ 2 - 1 := by
    have hxy : 1 ≤ x * y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
    have hQb : Q ≤ Q * b 5 := by
      dsimp [Q]
      nlinarith [mul_nonneg hu1n (sub_nonneg.mpr (hb 5))]
    have hrow4 : a 0 * a 4 = x * y + Q * b 5 := by
      dsimp [x, y, Q]
      nlinarith [he14]
    nlinarith [hXsq, hrow4]

  have hareaW := two_sqrt_mul_le_add ha5 ha6
  have harea : 2 * A + 2 * B + Z + 2 * W ≤ H := by
    have hraw : (∑ i, a i) ≤ H := by
      simpa [a, HullSevenType4BracketData.a] using D.area
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
    dsimp [A, B, Z, W] at hareaW ⊢
    linarith

  have hear0 := D.ear0
  have hear1 := D.ear1
  have hear2 := D.ear2
  have hear3 := D.ear3
  change b 0 ≤ a 0 + a 1 - 1 at hear0
  change b 1 ≤ a 1 + a 2 - 1 at hear1
  change b 2 ≤ a 2 + a 3 - 1 at hear2
  change b 3 ≤ a 3 + a 4 - 1 at hear3

  have hfirstEarSum : r + 1 ≤ A + B := by
    have hamgm := two_sqrt_mul_le_add hb0 hb3
    dsimp [r, A, B] at hamgm ⊢
    linarith

  have hear12 : b 1 * b 2 ≤
      (a 1 + a 2 - 1) * (a 3 + a 2 - 1) := by
    simpa [add_comm] using
      mul_le_mul hear1 hear2 hb2 (by nlinarith [ha 1, ha 2])
  have hsecondEar :
      s ^ 2 ≤ Y ^ 2 + 2 * B * (Z - 1) + (Z - 1) ^ 2 := by
    dsimp [B, Z]
    nlinarith [hssqRaw, hYsq, hear12]

  have hear03 : b 0 * b 3 ≤
      (a 0 + a 1 - 1) * (a 3 + a 4 - 1) := by
    exact mul_le_mul hear0 hear3 hb3
      (by nlinarith [ha 0, ha 1])
  have hfirstEarWeighted :
      r ^ 2 ≤ (A + B - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
        (B ^ 2 - Y ^ 2) / 3 := by
    have hgap : 0 ≤
        (3 * (a 0 - a 4) + 2 * (a 1 - a 3)) ^ 2 := sq_nonneg _
    have hid :
        (A + B - 1) ^ 2 + (A ^ 2 - X ^ 2) / 2 -
            (B ^ 2 - Y ^ 2) / 3 -
            ((a 0 + a 1 - 1) * (a 3 + a 4 - 1)) =
          (3 * (a 0 - a 4) + 2 * (a 1 - a 3)) ^ 2 / 24 := by
      dsimp [A, B]
      rw [hXsq, hYsq]
      ring
    nlinarith [hrsq, hear03]

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
      A := A
      B := B
      X_floor := one_le_sqrt_mul (ha 0) (ha 4)
      Y_floor := one_le_sqrt_mul (ha 1) (ha 3)
      Z_floor := ha 2
      W_floor := one_le_sqrt_mul (ha 5) (ha 6)
      r_floor := one_le_sqrt_mul (hb 0) (hb 3)
      s_floor := one_le_sqrt_mul (hb 1) (hb 2)
      U_floor := one_le_sqrt_mul hu0 hu2
      Q_floor := hu1
      R_floor := one_le_sqrt_mul hu3 hu6
      M_floor := one_le_sqrt_mul hx hy
      A_floor := by
        have hamgm := two_sqrt_mul_le_add ha0 ha4
        dsimp [X, A] at hamgm ⊢
        linarith
      B_floor := by
        have hamgm := two_sqrt_mul_le_add ha1 ha3
        dsimp [Y, B] at hamgm ⊢
        linarith
      rs := hrs
      s_sq := hs_sq
      UQ := hUQ
      ZW := hZW
      Q_cap := hQcap
      area := harea
      firstEarSum := hfirstEarSum
      secondEar := hsecondEar
      firstEarWeighted := hfirstEarWeighted }

end HullSevenType4BracketData

/-- The determinant chart forces normalized area above `25/2`. -/
theorem hullSeven_type4_area_gt {H : ℝ}
    (D : HullSevenType4BracketData H) : (25 : ℝ) / 2 < H :=
  hullSevenType4_area_gt D.toScalarData

/-- Direct sharp-constant consequence of the preferred type-4 bracket
packet. -/
theorem hullSeven_v8_of_type4_bracket {H : ℝ}
    (D : HullSevenType4BracketData H) : 1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 < H := hullSeven_type4_area_gt D
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH.le (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

end Heilbronn8.TriHull
