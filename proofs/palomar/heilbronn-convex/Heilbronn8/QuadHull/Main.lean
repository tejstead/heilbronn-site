import Heilbronn8.TriHull.Core

namespace Heilbronn8.QuadHull

abbrev Point := ℝ × ℝ

/-- Ordinary oriented area; `sig` is doubled signed area. -/
noncomputable def oarea (p q r : Point) : ℝ :=
  sig p q r / 2

/-- Ordinary unsigned triangle area. -/
noncomputable def area (p q r : Point) : ℝ :=
  |sig p q r| / 2

/-- Fixed counterclockwise convention for the hull vertices. -/
def CCWQuad (A B C D : Point) : Prop :=
  0 < sig A B C ∧ 0 < sig B C D ∧
  0 < sig C D A ∧ 0 < sig D A B

/-- Three-cell signed fan decomposition. -/
lemma fan_three (P A B C : Point) :
    oarea P A B + oarea P B C + oarea P C A = oarea A B C := by
  simp only [oarea, sig]
  ring

/-- Four-cell signed fan decomposition of a quadrilateral. -/
lemma fan_four (P A B C D : Point) :
    oarea P A B + oarea P B C + oarea P C D + oarea P D A =
      oarea A B C + oarea A C D := by
  simp only [oarea, sig]
  ring

/-- Division-free four-fan Plücker identity, equation (13). -/
lemma four_fan_plucker (Q A B C D : Point) :
    oarea Q A B * oarea Q C D - oarea Q B C * oarea Q D A =
      oarea Q C A * oarea Q D B := by
  simp only [oarea, sig]
  ring

/-- The four diagonal decompositions, equation (25). -/
lemma diagonal_decompositions (Q A B C D : Point) :
    oarea A B C = oarea Q A B + oarea Q B C + oarea Q C A ∧
    oarea B C D = oarea Q B C + oarea Q C D + oarea Q D B ∧
    oarea A C D = oarea Q C D + oarea Q D A - oarea Q C A ∧
    oarea A B D = oarea Q A B + oarea Q D A - oarea Q D B := by
  simp only [oarea, sig]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/--
Pending identity (47), stated exactly and intentionally not proved here.
In the notation of section 7 this is `x * δ - u * x' = k * γ`.
-/
def CrossApexIdentity47 : Prop :=
  ∀ P A C D R : Point,
    oarea P C R * oarea P D A - oarea P C A * oarea P D R =
      oarea P R A * oarea P C D

/--
Pending identity (48), stated exactly and intentionally not proved here.
In the notation of section 7 this is `u * y' - δ * y = k * w`.
-/
def CrossApexIdentity48 : Prop :=
  ∀ P A C D R : Point,
    oarea P C A * oarea R D A - oarea P D A * oarea R C A =
      oarea P R A * oarea A C D

/-- The paper lower bounds `F₀,...,F₄`, in ordinary-area normalization. -/
noncomputable def triangleLowerBound : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | 2 => 4 + 2 * Real.sqrt 3
  | 3 => 17 / 2
  | _ => 21 / 2

/-- Every diagonal split gives the unconditional `23/2` lower bound. -/
lemma diagonal_decomposition_bound {H L R : ℝ} {i : ℕ}
    (hi : i ≤ 4)
    (hH : H = L + R)
    (hL : triangleLowerBound i ≤ L)
    (hR : triangleLowerBound (4 - i) ≤ R) :
    (23 : ℝ) / 2 ≤ H := by
  interval_cases i <;>
    simp [triangleLowerBound] at hL hR <;>
    nlinarith [TriHull.sixty_nine_fortieths_lt_sqrt_three]

/-- Rational form of TH8 Lemma 1 used in the orbit estimates. -/
noncomputable def F2 : ℝ :=
  149 / 20

lemma F2_pos : 0 < F2 := by
  norm_num [F2]

/-- A balanced `2+2` diagonal exceeds the `63/5` target. -/
lemma balanced_two_two_bound {H L R : ℝ}
    (hH : H = L + R)
    (hL : F2 < L) (hR : F2 < R) :
    (63 : ℝ) / 5 ≤ H := by
  norm_num [F2] at hL hR
  nlinarith

/-- Scalar four-fan data for the `Q ∈ BCO` sign convention. -/
structure PositivePluckerFan (H : ℝ) where
  α : ℝ
  β : ℝ
  γ : ℝ
  δ : ℝ
  u : ℝ
  v : ℝ
  hull_eq : H = α + β + γ + δ
  α_unit : 1 ≤ α
  β_unit : 1 ≤ β
  γ_unit : 1 ≤ γ
  δ_unit : 1 ≤ δ
  u_unit : 1 ≤ u
  v_unit : 1 ≤ v
  plucker : α * γ = β * δ + u * v

/-- Opposite `3+1`; also the `j=0` branch in orbits II and IV. -/
lemma opposite_three_one_bound {H : ℝ}
    (f : PositivePluckerFan H)
    (hδ : (17 : ℝ) / 2 ≤ f.δ) :
    (63 : ℝ) / 5 ≤ H := by
  have hβδ : (17 : ℝ) / 2 ≤ f.β * f.δ := by
    have hm := mul_le_mul f.β_unit hδ
      (by norm_num : (0 : ℝ) ≤ 17 / 2)
      (by linarith [f.β_unit] : 0 ≤ f.β)
    norm_num at hm ⊢
    exact hm
  have huv : 1 ≤ f.u * f.v := by
    have hm := mul_le_mul f.u_unit f.v_unit
      (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [f.u_unit] : 0 ≤ f.u)
    norm_num at hm ⊢
    exact hm
  have hprod : (19 : ℝ) / 2 ≤ f.α * f.γ := by
    rw [f.plucker]
    linarith
  have hsum : (31 : ℝ) / 10 ≤ f.α + f.γ := by
    by_contra hn
    have hlt : f.α + f.γ < (31 : ℝ) / 10 :=
      lt_of_not_ge hn
    have hdif : 0 <
        ((31 : ℝ) / 10 - (f.α + f.γ)) *
          ((31 : ℝ) / 10 + (f.α + f.γ)) :=
      mul_pos (by linarith)
        (by linarith [f.α_unit, f.γ_unit])
    nlinarith [sq_nonneg (f.α - f.γ)]
  nlinarith [f.hull_eq, f.β_unit]

/-- The `j=1` branch in orbits II and IV. -/
lemma one_two_fan_bound {H : ℝ}
    (f : PositivePluckerFan H)
    (hα : 3 ≤ f.α) (hδ : F2 < f.δ) :
    (63 : ℝ) / 5 ≤ H := by
  have hβpos : 0 < f.β := by
    linarith [f.β_unit]
  have hm := mul_lt_mul_of_pos_right hδ hβpos
  have hF2β : F2 ≤ F2 * f.β := by
    have hn : 0 ≤ F2 * (f.β - 1) :=
      mul_nonneg F2_pos.le (by linarith [f.β_unit])
    nlinarith
  have hβδ : F2 < f.β * f.δ := by
    nlinarith
  have huv : 1 ≤ f.u * f.v := by
    have hp := mul_le_mul f.u_unit f.v_unit
      (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [f.u_unit] : 0 ≤ f.u)
    norm_num at hp ⊢
    exact hp
  have hprod : (169 : ℝ) / 20 < f.α * f.γ := by
    rw [f.plucker]
    norm_num [F2] at hβδ
    linarith
  have hsum : (83 : ℝ) / 20 < f.α + f.γ := by
    by_contra hn
    have hle : f.α + f.γ ≤ (83 : ℝ) / 20 :=
      le_of_not_gt hn
    have hp : 0 ≤
        ((83 : ℝ) / 20 - (f.α + f.γ)) *
          ((83 : ℝ) / 20 + (f.α + f.γ)) :=
      mul_nonneg (by linarith)
        (by linarith [f.α_unit, f.γ_unit])
    nlinarith [sq_nonneg (f.α - f.γ)]
  norm_num [F2] at hδ
  nlinarith [f.hull_eq, f.β_unit]

/-- Orbit IV, secondary split `j=2`. -/
lemma orbit_IV_j2_bound {H : ℝ}
    (f : PositivePluckerFan H)
    (hα : F2 < f.α) (hδ : 3 ≤ f.δ)
    (hu : f.u ≤ f.γ + f.δ - 3)
    (hv : f.v ≤ f.α + f.δ - (17 : ℝ) / 2) :
    (63 : ℝ) / 5 ≤ H := by
  by_contra hn
  have hH : H < (63 : ℝ) / 5 :=
    lt_of_not_ge hn
  have hβlt : f.β < (23 : ℝ) / 20 := by
    norm_num [F2] at hα
    nlinarith [f.hull_eq, f.γ_unit]
  have hγlt : f.γ < (23 : ℝ) / 20 := by
    norm_num [F2] at hα
    nlinarith [f.hull_eq, f.β_unit]
  have hδlt : f.δ < (63 : ℝ) / 20 := by
    norm_num [F2] at hα
    nlinarith [f.hull_eq, f.β_unit, f.γ_unit]
  have hult : f.u < (13 : ℝ) / 10 := by
    linarith
  have hvlt : f.v < (21 : ℝ) / 10 := by
    nlinarith [f.hull_eq, f.β_unit, f.γ_unit]
  have hαγ : F2 < f.α * f.γ := by
    have hαpos : 0 < f.α :=
      lt_trans F2_pos hα
    have hn : 0 ≤ f.α * (f.γ - 1) :=
      mul_nonneg hαpos.le (by linarith [f.γ_unit])
    nlinarith
  have hβδ :
      f.β * f.δ < (23 : ℝ) / 20 * ((63 : ℝ) / 20) := by
    calc
      f.β * f.δ < (23 : ℝ) / 20 * f.δ :=
        mul_lt_mul_of_pos_right hβlt
          (by linarith [f.δ_unit])
      _ < (23 : ℝ) / 20 * ((63 : ℝ) / 20) :=
        mul_lt_mul_of_pos_left hδlt (by norm_num)
  have huvLow : (1531 : ℝ) / 400 < f.u * f.v := by
    norm_num [F2] at hαγ
    nlinarith [f.plucker]
  have huvHigh : f.u * f.v < (273 : ℝ) / 100 := by
    calc
      f.u * f.v < (13 : ℝ) / 10 * f.v :=
        mul_lt_mul_of_pos_right hult
          (by linarith [f.v_unit])
      _ < (13 : ℝ) / 10 * ((21 : ℝ) / 10) :=
        mul_lt_mul_of_pos_left hvlt (by norm_num)
      _ = (273 : ℝ) / 100 := by norm_num
  nlinarith

/-- Orbit II, secondary split `j=3`. -/
lemma orbit_II_j3_bound {H : ℝ}
    (f : PositivePluckerFan H)
    (hα : (17 : ℝ) / 2 ≤ f.α)
    (hu : f.u ≤ f.γ + f.δ - 1)
    (hv : f.v ≤ f.α + f.δ - (17 : ℝ) / 2) :
    (63 : ℝ) / 5 ≤ H := by
  by_contra hn
  have hH : H < (63 : ℝ) / 5 :=
    lt_of_not_ge hn
  have hsum : f.β + f.δ < (31 : ℝ) / 10 := by
    nlinarith [f.hull_eq, f.γ_unit]
  have hsqsum :
      (f.β + f.δ) ^ 2 < ((31 : ℝ) / 10) ^ 2 := by
    have hp : 0 <
        ((31 : ℝ) / 10 - (f.β + f.δ)) *
          ((31 : ℝ) / 10 + (f.β + f.δ)) :=
      mul_pos (by linarith)
        (by linarith [f.β_unit, f.δ_unit])
    nlinarith
  have hamgm :
      4 * (f.β * f.δ) ≤ (f.β + f.δ) ^ 2 := by
    nlinarith [sq_nonneg (f.β - f.δ)]
  have hβδ : f.β * f.δ < ((31 : ℝ) / 20) ^ 2 := by
    nlinarith
  have hαγ : (17 : ℝ) / 2 ≤ f.α * f.γ := by
    have hm := mul_le_mul hα f.γ_unit
      (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [hα] : 0 ≤ f.α)
    norm_num at hm ⊢
    nlinarith
  have huvLow : (2439 : ℝ) / 400 < f.u * f.v := by
    nlinarith [f.plucker]
  have hult : f.u < (21 : ℝ) / 10 := by
    nlinarith [f.hull_eq, f.α_unit, f.β_unit, hα]
  have hvlt : f.v < (21 : ℝ) / 10 := by
    nlinarith [f.hull_eq, f.β_unit, f.γ_unit]
  have huvHigh : f.u * f.v < (441 : ℝ) / 100 := by
    calc
      f.u * f.v < (21 : ℝ) / 10 * f.v :=
        mul_lt_mul_of_pos_right hult
          (by linarith [f.v_unit])
      _ < (21 : ℝ) / 10 * ((21 : ℝ) / 10) :=
        mul_lt_mul_of_pos_left hvlt (by norm_num)
      _ = (441 : ℝ) / 100 := by norm_num
  nlinarith

/-- The remaining orbit-I scalar configuration from (41). -/
structure OrbitIResidual (H : ℝ) where
  α : ℝ
  β : ℝ
  γ : ℝ
  δ : ℝ
  u : ℝ
  t : ℝ
  hull_eq : H = α + β + γ + δ
  α_unit : 1 ≤ α
  β_unit : 1 ≤ β
  γ_unit : 1 ≤ γ
  δ_three : (17 : ℝ) / 2 ≤ δ
  u_unit : 1 ≤ u
  t_unit : 1 ≤ t
  plucker : β * δ = α * γ + u * t
  diagonal_AC : (21 : ℝ) / 2 ≤ α + β + u
  diagonal_BD : (21 : ℝ) / 2 ≤ α + δ + t

/-- The sole remaining orbit-II split, `j=2`. -/
structure OrbitIIJ2Residual (H : ℝ)
    extends PositivePluckerFan H where
  α_two : F2 < α
  δ_one : 3 ≤ δ
  diagonal_AC : u ≤ γ + δ - 1
  diagonal_BD : v ≤ α + δ - (17 : ℝ) / 2

/-
Direct signed-area data for orbit II, secondary split `j = 2`.

The old closure interface required a `43 / 5` double-apex overlap bound.
That bound had no sound geometric producer.  The fields below instead record
the three exact determinant identities obtained by inserting the remaining
point `Z` into the `QDA` fan.  No containment relation between the two points
in `QAB` and the triangle `ZAB` is required.
-/
structure OrbitIIJ2Direct (H : ℝ)
    extends PositivePluckerFan H where
  a : ℝ
  b : ℝ
  c : ℝ
  x : ℝ
  e : ℝ
  w : ℝ
  alpha_two : F2 < α
  delta_split : δ = a + x + e
  qab_split : c + b = α + a
  qdz_identity : α * x = δ * b - a * v
  zda_identity : α * e = δ * c - a * (α + δ - v)
  azc_identity : α * w = c * u - a * (α + β + u)
  a_unit : 1 ≤ a
  x_unit : 1 ≤ x
  e_unit : 1 ≤ e
  w_unit : 1 ≤ |w|
  diagonal_AC : u ≤ γ + δ - 1


section residualClosure

set_option maxHeartbeats 2000000

/-
The direct orbit-II/j=2 estimate.  Its only nonlinear input is the Plücker
identity already carried by `PositivePluckerFan`; the remaining equalities are
ordinary fan decompositions around `Z`.
-/
lemma orbit_II_j2_direct_bound {H : ℝ}
    (r : OrbitIIJ2Direct H) :
    (63 : ℝ) / 5 ≤ H := by
  by_contra hn
  have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
  have halpha : (149 : ℝ) / 20 < r.α := by
    simpa [F2] using r.alpha_two
  have hdelta_three : 3 ≤ r.δ := by
    nlinarith [r.delta_split, r.a_unit, r.x_unit, r.e_unit]
  have hgamma_lt : r.γ < (23 : ℝ) / 20 := by
    nlinarith [r.hull_eq, r.β_unit]
  have hdelta_lt : r.δ < (63 : ℝ) / 20 := by
    nlinarith [r.hull_eq, r.β_unit, r.γ_unit]
  have ha_lt : r.a < (23 : ℝ) / 20 := by
    nlinarith [r.delta_split, r.x_unit, r.e_unit]
  have halpha_pos : 0 < r.α := by nlinarith
  have hdelta_pos : 0 < r.δ := by nlinarith
  have hu_nonneg : 0 ≤ r.u := by nlinarith [r.u_unit]
  let D0 : ℝ := r.c * r.u - r.a * (r.α + r.β + r.u)
  let Bp : ℝ := r.u * (r.δ - 1) - r.a * (r.γ + r.δ)
  let Bm : ℝ := r.u * (1 + r.a) - r.a * (r.γ + r.δ)
  have hwprod : 0 ≤ r.α * (|r.w| - 1) :=
    mul_nonneg halpha_pos.le (sub_nonneg.mpr r.w_unit)
  have hcross : r.α ≤ |D0| := by
    dsimp [D0]
    rw [← r.azc_identity, abs_mul, abs_of_pos halpha_pos]
    nlinarith
  have hxprod : 0 ≤ r.α * (r.x - 1) :=
    mul_nonneg halpha_pos.le (sub_nonneg.mpr r.x_unit)
  have hxgap : 0 ≤ r.δ * r.b - r.a * r.v - r.α := by
    nlinarith [r.qdz_identity]
  have hupper_identity :
      r.α * Bp - r.δ * D0 =
        r.u * (r.δ * r.b - r.a * r.v - r.α) := by
    dsimp [Bp, D0]
    linear_combination
      -r.δ * r.u * r.qab_split - r.a * r.plucker
  have hupper : r.δ * D0 ≤ r.α * Bp := by
    have hnonneg :
        0 ≤ r.u * (r.δ * r.b - r.a * r.v - r.α) :=
      mul_nonneg hu_nonneg hxgap
    nlinarith [hupper_identity]
  have hdelta_minus_one : 0 ≤ r.δ - 1 := by nlinarith
  have hsum_nonneg : 0 ≤ r.γ + r.δ := by
    nlinarith [r.γ_unit]
  have hu_mul := mul_le_mul_of_nonneg_right
    r.diagonal_AC hdelta_minus_one
  have ha_mul := mul_le_mul_of_nonneg_right r.a_unit hsum_nonneg
  have hBp_bound :
      Bp ≤ r.γ * (r.δ - 2) + r.δ * (r.δ - 3) + 1 := by
    dsimp [Bp]
    nlinarith
  have hdelta_minus_two_pos : 0 < r.δ - 2 := by nlinarith
  have hdelta_minus_two_lt : r.δ - 2 < (23 : ℝ) / 20 := by
    nlinarith
  have hgamma_product :
      r.γ * (r.δ - 2) < (529 : ℝ) / 400 := by
    calc
      r.γ * (r.δ - 2) <
          ((23 : ℝ) / 20) * (r.δ - 2) :=
        mul_lt_mul_of_pos_right hgamma_lt hdelta_minus_two_pos
      _ < ((23 : ℝ) / 20) * ((23 : ℝ) / 20) :=
        mul_lt_mul_of_pos_left hdelta_minus_two_lt (by norm_num)
      _ = (529 : ℝ) / 400 := by norm_num
  have hdelta_minus_three : 0 ≤ r.δ - 3 := by nlinarith
  have hdelta_minus_three_lt : r.δ - 3 < (3 : ℝ) / 20 := by
    nlinarith
  have hdelta_product :
      r.δ * (r.δ - 3) < (189 : ℝ) / 400 := by
    calc
      r.δ * (r.δ - 3) ≤
          ((63 : ℝ) / 20) * (r.δ - 3) :=
        mul_le_mul_of_nonneg_right hdelta_lt.le hdelta_minus_three
      _ < ((63 : ℝ) / 20) * ((3 : ℝ) / 20) :=
        mul_lt_mul_of_pos_left hdelta_minus_three_lt (by norm_num)
      _ = (189 : ℝ) / 400 := by norm_num
  have hBp_lt : Bp < (559 : ℝ) / 200 := by
    nlinarith [hBp_bound, hgamma_product, hdelta_product]
  have hBp_delta : Bp < r.δ := by nlinarith
  have hD0_lt : D0 < r.α := by
    have hmul : r.δ * D0 < r.δ * r.α := by
      calc
        r.δ * D0 ≤ r.α * Bp := hupper
        _ < r.α * r.δ :=
          mul_lt_mul_of_pos_left hBp_delta halpha_pos
        _ = r.δ * r.α := by ring
    exact lt_of_mul_lt_mul_left hmul hdelta_pos.le
  have heprod : 0 ≤ r.α * (r.e - 1) :=
    mul_nonneg halpha_pos.le (sub_nonneg.mpr r.e_unit)
  have hegap :
      0 ≤ r.δ * r.c - r.a * (r.α + r.δ - r.v) - r.α := by
    nlinarith [r.zda_identity]
  have hlower_identity :
      r.δ * D0 - r.α * Bm =
        r.u *
          (r.δ * r.c - r.a * (r.α + r.δ - r.v) - r.α) := by
    dsimp [Bm, D0]
    linear_combination r.a * r.plucker
  have hlower : r.α * Bm ≤ r.δ * D0 := by
    have hnonneg :
        0 ≤ r.u *
          (r.δ * r.c - r.a * (r.α + r.δ - r.v) - r.α) :=
      mul_nonneg hu_nonneg hegap
    nlinarith [hlower_identity]
  have hu_one_a : 2 ≤ r.u * (1 + r.a) := by
    have h := mul_le_mul r.u_unit (by nlinarith [r.a_unit] : 2 ≤ 1 + r.a)
      (by norm_num : (0 : ℝ) ≤ 2) (by nlinarith [r.u_unit] : 0 ≤ r.u)
    norm_num at h ⊢
    exact h
  have ha_gamma : r.a * r.γ < (529 : ℝ) / 400 := by
    calc
      r.a * r.γ < ((23 : ℝ) / 20) * r.γ :=
        mul_lt_mul_of_pos_right ha_lt (by nlinarith [r.γ_unit])
      _ < ((23 : ℝ) / 20) * ((23 : ℝ) / 20) :=
        mul_lt_mul_of_pos_left hgamma_lt (by norm_num)
      _ = (529 : ℝ) / 400 := by norm_num
  have ha_minus_one : 0 ≤ r.a - 1 := by nlinarith [r.a_unit]
  have ha_minus_one_lt : r.a - 1 < (3 : ℝ) / 20 := by nlinarith
  have hdelta_a : r.δ * (r.a - 1) < (189 : ℝ) / 400 := by
    calc
      r.δ * (r.a - 1) ≤ ((63 : ℝ) / 20) * (r.a - 1) :=
        mul_le_mul_of_nonneg_right hdelta_lt.le ha_minus_one
      _ < ((63 : ℝ) / 20) * ((3 : ℝ) / 20) :=
        mul_lt_mul_of_pos_left ha_minus_one_lt (by norm_num)
      _ = (189 : ℝ) / 400 := by norm_num
  have hBm_delta : -r.δ < Bm := by
    dsimp [Bm]
    nlinarith [hu_one_a, ha_gamma, hdelta_a]
  have hD0_gt : -r.α < D0 := by
    have hmul : r.δ * (-r.α) < r.δ * D0 := by
      calc
        r.δ * (-r.α) = r.α * (-r.δ) := by ring
        _ < r.α * Bm :=
          mul_lt_mul_of_pos_left hBm_delta halpha_pos
        _ ≤ r.δ * D0 := hlower
    exact lt_of_mul_lt_mul_left hmul hdelta_pos.le
  have habs : |D0| < r.α := abs_lt.2 ⟨hD0_gt, hD0_lt⟩
  exact (not_lt_of_ge hcross) habs

def cyclicY (U X J : ℝ) : ℝ := U - X - J
def cyclicW (U V G : ℝ) : ℝ := G + V - U
def cyclicXNum (V G X J : ℝ) : ℝ := V * X - G * J
def cyclicYNum (U V G Y J : ℝ) : ℝ :=
  V * Y + cyclicW U V G * J

def areaDet
    (Sx Sj Sy Tx Tj Ty Rx Rj Ry : ℝ) : ℝ :=
  Sx * (Tj * Ry - Ty * Rj) -
  Sj * (Tx * Ry - Ty * Rx) +
  Sy * (Tx * Rj - Tj * Rx)

def cyclicDet
    (U Sx Sj Tx Tj Rx Rj : ℝ) : ℝ :=
  areaDet Sx Sj (cyclicY U Sx Sj)
    Tx Tj (cyclicY U Tx Tj) Rx Rj (cyclicY U Rx Rj)

structure CyclicLeaf50tDomain
    (U V G Sx Sj Tx Tj Rx Rj : ℝ) : Prop where
  U_lower : 7 ≤ U
  U_upper : U ≤ (53 : ℝ) / 5
  V_lower : 7 ≤ V
  V_upper : V ≤ (53 : ℝ) / 5
  G_lower : 1 ≤ G
  G_upper : G ≤ (23 : ℝ) / 5
  Sx_lower : 3 ≤ Sx
  Sx_upper : Sx ≤ (33 : ℝ) / 5
  Sj_lower : 1 ≤ Sj
  Sj_upper : Sj ≤ (23 : ℝ) / 5
  Tx_lower : 1 ≤ Tx
  Tx_upper : Tx ≤ (23 : ℝ) / 5
  Tj_lower : 3 ≤ Tj
  Tj_upper : Tj ≤ (33 : ℝ) / 5
  Rx_lower : 3 ≤ Rx
  Rx_upper : Rx ≤ (33 : ℝ) / 5
  Rj_lower : 3 ≤ Rj
  Rj_upper : Rj ≤ (33 : ℝ) / 5
  W_lower : 0 ≤ cyclicW U V G - 1
  Sy_lower : 0 ≤ cyclicY U Sx Sj - 3
  Ty_lower : 0 ≤ cyclicY U Tx Tj - 3
  Ry_lower : 0 ≤ cyclicY U Rx Rj - 1
  Sx'_lower : 0 ≤ cyclicXNum V G Sx Sj - 3 * U
  Sj'_lower : 0 ≤ U * Sj - U
  Sy'_lower : 0 ≤ cyclicYNum U V G (cyclicY U Sx Sj) Sj - 3 * U
  Tx'_lower : 0 ≤ cyclicXNum V G Tx Tj - U
  Tj'_lower : 0 ≤ U * Tj - 3 * U
  Ty'_lower : 0 ≤ cyclicYNum U V G (cyclicY U Tx Tj) Tj - 3 * U
  Rx'_lower : 0 ≤ cyclicXNum V G Rx Rj - 3 * U
  Rj'_lower : 0 ≤ U * Rj - 3 * U
  Ry'_lower : 0 ≤ cyclicYNum U V G (cyclicY U Rx Rj) Rj - U
  C_ST_XY : 0 ≤ cyclicY U Tx Tj * Sx - Tx * cyclicY U Sx Sj - U
  C_ST_YJ : 0 ≤ Tj * cyclicY U Sx Sj - cyclicY U Tx Tj * Sj - U
  C_SR_YX : 0 ≤ Rx * cyclicY U Sx Sj - cyclicY U Rx Rj * Sx - U
  C_SR_XJ : 0 ≤ Rj * Sx - Rx * Sj - U
  C_TR_YJ : 0 ≤ Rj * cyclicY U Tx Tj - cyclicY U Rx Rj * Tj - U
  C_TR_JX : 0 ≤ Rx * Tj - Rj * Tx - U
  D_ST_XY : 0 ≤
    cyclicYNum U V G (cyclicY U Tx Tj) Tj * cyclicXNum V G Sx Sj -
      cyclicXNum V G Tx Tj * cyclicYNum U V G (cyclicY U Sx Sj) Sj -
      V * U ^ 2
  D_ST_YJ : 0 ≤
    (U * Tj) * cyclicYNum U V G (cyclicY U Sx Sj) Sj -
      cyclicYNum U V G (cyclicY U Tx Tj) Tj * (U * Sj) -
      V * U ^ 2
  D_SR_YX : 0 ≤
    cyclicXNum V G Rx Rj * cyclicYNum U V G (cyclicY U Sx Sj) Sj -
      cyclicYNum U V G (cyclicY U Rx Rj) Rj * cyclicXNum V G Sx Sj -
      V * U ^ 2
  D_SR_XJ : 0 ≤
    (U * Rj) * cyclicXNum V G Sx Sj -
      cyclicXNum V G Rx Rj * (U * Sj) -
      V * U ^ 2
  D_TR_YJ : 0 ≤
    (U * Rj) * cyclicYNum U V G (cyclicY U Tx Tj) Tj -
      cyclicYNum U V G (cyclicY U Rx Rj) Rj * (U * Tj) -
      V * U ^ 2
  D_TR_JX : 0 ≤
    cyclicXNum V G Rx Rj * (U * Tj) -
      (U * Rj) * cyclicXNum V G Tx Tj -
      V * U ^ 2
  central : 0 ≤ -cyclicDet U Sx Sj Tx Tj Rx Rj - U ^ 2
  CDS : 0 ≤ G * cyclicY U Sx Sj + cyclicW U V G * Sx - U
  CDT : 0 ≤ G * cyclicY U Tx Tj + cyclicW U V G * Tx - U
  CDR : 0 ≤ G * cyclicY U Rx Rj + cyclicW U V G * Rx - U

def ResidualBoundHypothesis : Prop :=
  ∀ {U V G Sx Sj Tx Tj Rx Rj : ℝ},
    CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj →
      (58 : ℝ) / 5 ≤ G + V + (G + U) / V

structure OrbitIResidualGeometry (H : ℝ)
    extends Heilbronn8.QuadHull.OrbitIResidual H where
  w : ℝ
  w_eq : w = γ + δ - u
  w_unit : 1 ≤ w

lemma OrbitIResidualGeometry.δ_pos {H : ℝ}
    (g : OrbitIResidualGeometry H) : 0 < g.δ := by
  linarith [g.δ_three]

lemma OrbitIResidualGeometry.fifty_s {H : ℝ}
    (g : OrbitIResidualGeometry H) :
    1 + g.γ + g.δ + (g.γ + g.u) / g.δ ≤ H := by
  have hγ0 : 0 ≤ g.γ := by linarith [g.γ_unit]
  have hu0 : 0 ≤ g.u := by linarith [g.u_unit]
  have hαγ : g.γ ≤ g.α * g.γ := by
    simpa using mul_le_mul_of_nonneg_right g.α_unit hγ0
  have hut : g.u ≤ g.u * g.t := by
    simpa using mul_le_mul_of_nonneg_left g.t_unit hu0
  have hβδ : g.γ + g.u ≤ g.β * g.δ := by
    nlinarith [g.plucker]
  have hdiv : (g.γ + g.u) / g.δ ≤ g.β := by
    apply (div_le_iff₀ g.δ_pos).2
    nlinarith
  nlinarith [g.hull_eq, g.α_unit]

/-- The complete fan data available at the cyclic row before compactification. -/
structure CyclicLeaf (H : ℝ) where
  core : OrbitIResidualGeometry H
  Sx : ℝ
  Sj : ℝ
  Sy : ℝ
  Tx : ℝ
  Tj : ℝ
  Ty : ℝ
  Rx : ℝ
  Rj : ℝ
  Ry : ℝ
  Sx' : ℝ
  Sy' : ℝ
  Tx' : ℝ
  Ty' : ℝ
  Rx' : ℝ
  Ry' : ℝ
  S_sum : core.u = Sx + Sj + Sy
  T_sum : core.u = Tx + Tj + Ty
  R_sum : core.u = Rx + Rj + Ry
  S'_sum : core.δ = Sx' + Sj + Sy'
  T'_sum : core.δ = Tx' + Tj + Ty'
  R'_sum : core.δ = Rx' + Rj + Ry'
  Sx_num : cyclicXNum core.δ core.γ Sx Sj = core.u * Sx'
  Sy_num : cyclicYNum core.u core.δ core.γ Sy Sj = core.u * Sy'
  Tx_num : cyclicXNum core.δ core.γ Tx Tj = core.u * Tx'
  Ty_num : cyclicYNum core.u core.δ core.γ Ty Tj = core.u * Ty'
  Rx_num : cyclicXNum core.δ core.γ Rx Rj = core.u * Rx'
  Ry_num : cyclicYNum core.u core.δ core.γ Ry Rj = core.u * Ry'
  Sx_lower : 3 ≤ Sx
  Sj_lower : 1 ≤ Sj
  Sy_lower : 3 ≤ Sy
  Tx_lower : 1 ≤ Tx
  Tj_lower : 3 ≤ Tj
  Ty_lower : 3 ≤ Ty
  Rx_lower : 3 ≤ Rx
  Rj_lower : 3 ≤ Rj
  Ry_lower : 1 ≤ Ry
  Sx'_lower : 3 ≤ Sx'
  Sy'_lower : 3 ≤ Sy'
  Tx'_lower : 1 ≤ Tx'
  Ty'_lower : 3 ≤ Ty'
  Rx'_lower : 3 ≤ Rx'
  Ry'_lower : 1 ≤ Ry'
  C_ST_XY : core.u ≤ Ty * Sx - Tx * Sy
  C_ST_YJ : core.u ≤ Tj * Sy - Ty * Sj
  C_SR_YX : core.u ≤ Rx * Sy - Ry * Sx
  C_SR_XJ : core.u ≤ Rj * Sx - Rx * Sj
  C_TR_YJ : core.u ≤ Rj * Ty - Ry * Tj
  C_TR_JX : core.u ≤ Rx * Tj - Rj * Tx
  D_ST_XY : core.δ ≤ Ty' * Sx' - Tx' * Sy'
  D_ST_YJ : core.δ ≤ Tj * Sy' - Ty' * Sj
  D_SR_YX : core.δ ≤ Rx' * Sy' - Ry' * Sx'
  D_SR_XJ : core.δ ≤ Rj * Sx' - Rx' * Sj
  D_TR_YJ : core.δ ≤ Rj * Ty' - Ry' * Tj
  D_TR_JX : core.δ ≤ Rx' * Tj - Rj * Tx'
  central : core.u ^ 2 ≤
    -areaDet Sx Sj Sy Tx Tj Ty Rx Rj Ry
  CDS : core.u ≤ core.γ * Sy + core.w * Sx
  CDT : core.u ≤ core.γ * Ty + core.w * Tx
  CDR : core.u ≤ core.γ * Ry + core.w * Rx

private lemma cleared_gap {U V a b c d A B C D : ℝ}
    (hA : A = U * a) (hB : B = U * b)
    (hC : C = U * c) (hD : D = U * d)
    (hgap : V ≤ a * b - c * d) :
    0 ≤ A * B - C * D - V * U ^ 2 := by
  rw [hA, hB, hC, hD]
  calc
    0 ≤ U ^ 2 * ((a * b - c * d) - V) :=
      mul_nonneg (sq_nonneg U) (sub_nonneg.mpr hgap)
    _ = (U * a) * (U * b) - (U * c) * (U * d) - V * U ^ 2 := by
      ring

lemma CyclicLeaf.to50tDomain {H : ℝ} (leaf : CyclicLeaf H)
    (hsmall : leaf.core.γ + leaf.core.δ +
        (leaf.core.γ + leaf.core.u) / leaf.core.δ < (58 : ℝ) / 5) :
    CyclicLeaf50tDomain leaf.core.u leaf.core.δ leaf.core.γ
      leaf.Sx leaf.Sj leaf.Tx leaf.Tj leaf.Rx leaf.Rj := by
  have hU : 7 ≤ leaf.core.u := by
    nlinarith [leaf.S_sum, leaf.Sx_lower, leaf.Sj_lower, leaf.Sy_lower]
  have hV : 7 ≤ leaf.core.δ := by
    nlinarith [leaf.S'_sum, leaf.Sx'_lower, leaf.Sj_lower, leaf.Sy'_lower]
  have hfrac : 0 <
      (leaf.core.γ + leaf.core.u) / leaf.core.δ :=
    div_pos (by nlinarith [leaf.core.γ_unit, hU]) (by linarith [hV])
  have hGV : leaf.core.γ + leaf.core.δ < (58 : ℝ) / 5 := by
    linarith
  have hW : cyclicW leaf.core.u leaf.core.δ leaf.core.γ =
      leaf.core.w := by
    unfold cyclicW
    linarith [leaf.core.w_eq]
  have hUupper : leaf.core.u < (53 : ℝ) / 5 := by
    nlinarith [hGV, leaf.core.w_eq, leaf.core.w_unit]
  have hVupper : leaf.core.δ < (53 : ℝ) / 5 := by
    nlinarith [hGV, leaf.core.γ_unit]
  have hGupper : leaf.core.γ < (23 : ℝ) / 5 := by
    nlinarith [hGV, hV]
  have hSy : cyclicY leaf.core.u leaf.Sx leaf.Sj = leaf.Sy := by
    unfold cyclicY
    linarith [leaf.S_sum]
  have hTy : cyclicY leaf.core.u leaf.Tx leaf.Tj = leaf.Ty := by
    unfold cyclicY
    linarith [leaf.T_sum]
  have hRy : cyclicY leaf.core.u leaf.Rx leaf.Rj = leaf.Ry := by
    unfold cyclicY
    linarith [leaf.R_sum]
  have hSxN : cyclicXNum leaf.core.δ leaf.core.γ leaf.Sx leaf.Sj =
      leaf.core.u * leaf.Sx' := leaf.Sx_num
  have hSyN : cyclicYNum leaf.core.u leaf.core.δ leaf.core.γ
      (cyclicY leaf.core.u leaf.Sx leaf.Sj) leaf.Sj =
        leaf.core.u * leaf.Sy' := by
    rw [hSy]
    exact leaf.Sy_num
  have hTxN : cyclicXNum leaf.core.δ leaf.core.γ leaf.Tx leaf.Tj =
      leaf.core.u * leaf.Tx' := leaf.Tx_num
  have hTyN : cyclicYNum leaf.core.u leaf.core.δ leaf.core.γ
      (cyclicY leaf.core.u leaf.Tx leaf.Tj) leaf.Tj =
        leaf.core.u * leaf.Ty' := by
    rw [hTy]
    exact leaf.Ty_num
  have hRxN : cyclicXNum leaf.core.δ leaf.core.γ leaf.Rx leaf.Rj =
      leaf.core.u * leaf.Rx' := leaf.Rx_num
  have hRyN : cyclicYNum leaf.core.u leaf.core.δ leaf.core.γ
      (cyclicY leaf.core.u leaf.Rx leaf.Rj) leaf.Rj =
        leaf.core.u * leaf.Ry' := by
    rw [hRy]
    exact leaf.Ry_num
  have hU0 : 0 ≤ leaf.core.u := by linarith [hU]
  have hSx'poly : 0 ≤
      cyclicXNum leaf.core.δ leaf.core.γ leaf.Sx leaf.Sj -
        3 * leaf.core.u := by
    rw [hSxN]
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Sx'_lower)
    nlinarith
  have hSj'poly : 0 ≤ leaf.core.u * leaf.Sj - leaf.core.u := by
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Sj_lower)
    nlinarith
  have hSy'poly : 0 ≤
      cyclicYNum leaf.core.u leaf.core.δ leaf.core.γ
          (cyclicY leaf.core.u leaf.Sx leaf.Sj) leaf.Sj -
        3 * leaf.core.u := by
    rw [hSyN]
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Sy'_lower)
    nlinarith
  have hTx'poly : 0 ≤
      cyclicXNum leaf.core.δ leaf.core.γ leaf.Tx leaf.Tj -
        leaf.core.u := by
    rw [hTxN]
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Tx'_lower)
    nlinarith
  have hTj'poly : 0 ≤ leaf.core.u * leaf.Tj - 3 * leaf.core.u := by
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Tj_lower)
    nlinarith
  have hTy'poly : 0 ≤
      cyclicYNum leaf.core.u leaf.core.δ leaf.core.γ
          (cyclicY leaf.core.u leaf.Tx leaf.Tj) leaf.Tj -
        3 * leaf.core.u := by
    rw [hTyN]
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Ty'_lower)
    nlinarith
  have hRx'poly : 0 ≤
      cyclicXNum leaf.core.δ leaf.core.γ leaf.Rx leaf.Rj -
        3 * leaf.core.u := by
    rw [hRxN]
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Rx'_lower)
    nlinarith
  have hRj'poly : 0 ≤ leaf.core.u * leaf.Rj - 3 * leaf.core.u := by
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Rj_lower)
    nlinarith
  have hRy'poly : 0 ≤
      cyclicYNum leaf.core.u leaf.core.δ leaf.core.γ
          (cyclicY leaf.core.u leaf.Rx leaf.Rj) leaf.Rj -
        leaf.core.u := by
    rw [hRyN]
    have hm := mul_nonneg hU0 (sub_nonneg.mpr leaf.Ry'_lower)
    nlinarith
  refine {
    U_lower := hU
    U_upper := hUupper.le
    V_lower := hV
    V_upper := hVupper.le
    G_lower := leaf.core.γ_unit
    G_upper := hGupper.le
    Sx_lower := leaf.Sx_lower
    Sx_upper := ?_
    Sj_lower := leaf.Sj_lower
    Sj_upper := ?_
    Tx_lower := leaf.Tx_lower
    Tx_upper := ?_
    Tj_lower := leaf.Tj_lower
    Tj_upper := ?_
    Rx_lower := leaf.Rx_lower
    Rx_upper := ?_
    Rj_lower := leaf.Rj_lower
    Rj_upper := ?_
    W_lower := ?_
    Sy_lower := ?_
    Ty_lower := ?_
    Ry_lower := ?_
    Sx'_lower := hSx'poly
    Sj'_lower := hSj'poly
    Sy'_lower := hSy'poly
    Tx'_lower := hTx'poly
    Tj'_lower := hTj'poly
    Ty'_lower := hTy'poly
    Rx'_lower := hRx'poly
    Rj'_lower := hRj'poly
    Ry'_lower := hRy'poly
    C_ST_XY := ?_
    C_ST_YJ := ?_
    C_SR_YX := ?_
    C_SR_XJ := ?_
    C_TR_YJ := ?_
    C_TR_JX := ?_
    D_ST_XY := ?_
    D_ST_YJ := ?_
    D_SR_YX := ?_
    D_SR_XJ := ?_
    D_TR_YJ := ?_
    D_TR_JX := ?_
    central := ?_
    CDS := ?_
    CDT := ?_
    CDR := ?_ }
  · nlinarith [leaf.S_sum, leaf.Sj_lower, leaf.Sy_lower]
  · nlinarith [leaf.S_sum, leaf.Sx_lower, leaf.Sy_lower]
  · nlinarith [leaf.T_sum, leaf.Tj_lower, leaf.Ty_lower]
  · nlinarith [leaf.T_sum, leaf.Tx_lower, leaf.Ty_lower]
  · nlinarith [leaf.R_sum, leaf.Rj_lower, leaf.Ry_lower]
  · nlinarith [leaf.R_sum, leaf.Rx_lower, leaf.Ry_lower]
  · rw [hW]
    linarith [leaf.core.w_unit]
  · rw [hSy]
    linarith [leaf.Sy_lower]
  · rw [hTy]
    linarith [leaf.Ty_lower]
  · rw [hRy]
    linarith [leaf.Ry_lower]
  · rw [hSy, hTy]
    linarith [leaf.C_ST_XY]
  · rw [hSy, hTy]
    linarith [leaf.C_ST_YJ]
  · rw [hSy, hRy]
    linarith [leaf.C_SR_YX]
  · linarith [leaf.C_SR_XJ]
  · rw [hTy, hRy]
    linarith [leaf.C_TR_YJ]
  · linarith [leaf.C_TR_JX]
  · exact cleared_gap hTyN hSxN hTxN hSyN leaf.D_ST_XY
  · exact cleared_gap (by rfl) hSyN hTyN (by rfl) leaf.D_ST_YJ
  · exact cleared_gap hRxN hSyN hRyN hSxN leaf.D_SR_YX
  · exact cleared_gap (by rfl) hSxN hRxN (by rfl) leaf.D_SR_XJ
  · exact cleared_gap (by rfl) hTyN hRyN (by rfl) leaf.D_TR_YJ
  · exact cleared_gap hRxN (by rfl) (by rfl) hTxN leaf.D_TR_JX
  · simp only [cyclicDet, hSy, hTy, hRy]
    linarith [leaf.central]
  · rw [hSy, hW]
    linarith [leaf.CDS]
  · rw [hTy, hW]
    linarith [leaf.CDT]
  · rw [hRy, hW]
    linarith [leaf.CDR]

lemma cyclic_leaf_bound
    (hResidual : ResidualBoundHypothesis)
    {H : ℝ} (leaf : CyclicLeaf H) :
    (63 : ℝ) / 5 ≤ H := by
  have h50t : (58 : ℝ) / 5 ≤
      leaf.core.γ + leaf.core.δ +
        (leaf.core.γ + leaf.core.u) / leaf.core.δ := by
    by_contra hn
    have hsmall : leaf.core.γ + leaf.core.δ +
        (leaf.core.γ + leaf.core.u) / leaf.core.δ < (58 : ℝ) / 5 :=
      lt_of_not_ge hn
    exact (not_lt_of_ge (hResidual (leaf.to50tDomain hsmall))) hsmall
  nlinarith [leaf.core.fifty_s]

/-- One candidate and its five cells in the two fans sharing `PA`. -/
structure CrossApexFan {H : ℝ} (g : OrbitIResidualGeometry H) where
  P : Point
  A : Point
  C : Point
  D : Point
  R : Point
  x : ℝ
  x' : ℝ
  y : ℝ
  y' : ℝ
  k : ℝ
  x_area : x = oarea P C R
  x'_area : x' = oarea P D R
  y_area : y = oarea R C A
  y'_area : y' = oarea R D A
  k_area : k = oarea P R A
  u_area : g.u = oarea P C A
  δ_area : g.δ = oarea P D A
  γ_area : g.γ = oarea P C D
  w_area : g.w = oarea A C D
  u_decomp : g.u = x + k + y
  δ_decomp : g.δ = x' + k + y'
  x_unit : 1 ≤ x
  x'_unit : 1 ≤ x'
  y_unit : 1 ≤ y
  y'_unit : 1 ≤ y'
  k_unit : 1 ≤ k

lemma CrossApexFan.identity47 {H : ℝ}
    {g : OrbitIResidualGeometry H} (f : CrossApexFan g)
    (h47 : CrossApexIdentity47) :
    f.x * g.δ - g.u * f.x' = f.k * g.γ := by
  rw [f.x_area, f.δ_area, f.u_area, f.x'_area, f.k_area, f.γ_area]
  exact h47 f.P f.A f.C f.D f.R

lemma CrossApexFan.identity48 {H : ℝ}
    {g : OrbitIResidualGeometry H} (f : CrossApexFan g)
    (h48 : CrossApexIdentity48) :
    g.u * f.y' - g.δ * f.y = f.k * g.w := by
  rw [f.u_area, f.y'_area, f.δ_area, f.y_area, f.k_area, f.w_area]
  exact h48 f.P f.A f.C f.D f.R

lemma OrbitIResidualGeometry.u_pos {H : ℝ}
    (g : OrbitIResidualGeometry H) : 0 < g.u := by
  linarith [g.u_unit]

lemma OrbitIResidualGeometry.hull_ge_u {H : ℝ}
    (g : OrbitIResidualGeometry H) : g.u ≤ H := by
  nlinarith [g.hull_eq, g.w_eq, g.w_unit, g.α_unit, g.β_unit]

lemma OrbitIResidualGeometry.hull_product {H : ℝ}
    (g : OrbitIResidualGeometry H) :
    1 + g.u ≤ g.δ * (H - g.δ - 2) := by
  have hγ0 : 0 ≤ g.γ := by linarith [g.γ_unit]
  have hu0 : 0 ≤ g.u := by linarith [g.u_unit]
  have hαγ : g.γ ≤ g.α * g.γ := by
    simpa using mul_le_mul_of_nonneg_right g.α_unit hγ0
  have hut : g.u ≤ g.u * g.t := by
    simpa using mul_le_mul_of_nonneg_left g.t_unit hu0
  have hβδ : 1 + g.u ≤ g.β * g.δ := by
    nlinarith [g.plucker, g.γ_unit]
  have hrest : g.β ≤ H - g.δ - 2 := by
    nlinarith [g.hull_eq, g.α_unit, g.γ_unit]
  have hm := mul_le_mul_of_nonneg_left hrest g.δ_pos.le
  nlinarith

structure SharedCommonCellLeaf (H : ℝ) where
  core : OrbitIResidualGeometry H
  fan : CrossApexFan core
  common_large : F2 < fan.k

structure PCommonCellLeaf (H : ℝ) where
  core : OrbitIResidualGeometry H
  fan : CrossApexFan core
  x_large : F2 < fan.x
  x'_large : F2 < fan.x'

structure ACommonCellLeaf (H : ℝ) where
  core : OrbitIResidualGeometry H
  fan : CrossApexFan core
  y_large : F2 < fan.y
  y'_large : F2 < fan.y'

inductive DPCommonKind {H : ℝ}
    (g : OrbitIResidualGeometry H) (f : CrossApexFan g) : Prop
  | split
      (x_three : 3 ≤ f.x)
      (y_three : 3 ≤ f.y)
      (x'_large : F2 < f.x')
  | opposite
      (y_large : F2 < f.y)
      (x'_large : F2 < f.x')

structure DPCommonResidualLeaf (H : ℝ) where
  core : OrbitIResidualGeometry H
  fan : CrossApexFan core
  kind : DPCommonKind core fan

structure CACommonDSplitLeaf (H : ℝ) where
  core : OrbitIResidualGeometry H
  fan : CrossApexFan core
  y_large : F2 < fan.y
  x'_three : 3 ≤ fan.x'
  y'_three : 3 ≤ fan.y'

private lemma high_delta_closure {H : ℝ}
    (g : OrbitIResidualGeometry H)
    (hu : (189 : ℝ) / 20 < g.u)
    (hδ : (19 : ℝ) / 2 ≤ g.δ) :
    (63 : ℝ) / 5 ≤ H := by
  by_contra hn
  have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
  have hfactor : 0 ≤
      (g.δ - (11 : ℝ) / 10) * (g.δ - (19 : ℝ) / 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [g.hull_product]

lemma shared_common_cell_bound
    (h48 : CrossApexIdentity48)
    {H : ℝ} (leaf : SharedCommonCellLeaf H) :
    (63 : ℝ) / 5 ≤ H := by
  let g := leaf.core
  let f := leaf.fan
  have hcommon := leaf.common_large
  norm_num [F2] at hcommon
  have hu : (189 : ℝ) / 20 < g.u := by
    nlinarith [f.u_decomp, f.x_unit, f.y_unit]
  by_cases hδ : (19 : ℝ) / 2 ≤ g.δ
  · exact high_delta_closure g hu hδ
  · have hδlt : g.δ < (19 : ℝ) / 2 := lt_of_not_ge hδ
    have hkw : f.k ≤ f.k * g.w := by
      have hk0 : 0 ≤ f.k := by linarith [f.k_unit]
      simpa using mul_le_mul_of_nonneg_left g.w_unit hk0
    have hδy : g.δ ≤ g.δ * f.y := by
      simpa using mul_le_mul_of_nonneg_left f.y_unit g.δ_pos.le
    have hprod : g.δ + f.k ≤ g.u * f.y' := by
      nlinarith [f.identity48 h48]
    have hy'lt : f.y' < (21 : ℝ) / 20 := by
      nlinarith [f.δ_decomp, f.x'_unit, hcommon]
    have hprodlarge : (169 : ℝ) / 10 < g.u * f.y' := by
      nlinarith [f.δ_decomp, f.x'_unit, f.y'_unit, hprod, hcommon]
    have huK : (63 : ℝ) / 5 < g.u := by
      by_contra hn
      have hule : g.u ≤ (63 : ℝ) / 5 := le_of_not_gt hn
      have hy'0 : 0 ≤ f.y' := by linarith [f.y'_unit]
      have hm : g.u * f.y' <
          ((63 : ℝ) / 5) * ((21 : ℝ) / 20) := by
        calc
          g.u * f.y' ≤ ((63 : ℝ) / 5) * f.y' :=
            mul_le_mul_of_nonneg_right hule hy'0
          _ < ((63 : ℝ) / 5) * ((21 : ℝ) / 20) :=
            mul_lt_mul_of_pos_left hy'lt (by norm_num)
      norm_num at hm
      nlinarith
    linarith [g.hull_ge_u]

lemma p_common_cell_bound
    (h48 : CrossApexIdentity48)
    {H : ℝ} (leaf : PCommonCellLeaf H) :
    (63 : ℝ) / 5 ≤ H := by
  let g := leaf.core
  let f := leaf.fan
  have hx := leaf.x_large
  have hx' := leaf.x'_large
  norm_num [F2] at hx hx'
  have hu : (189 : ℝ) / 20 < g.u := by
    nlinarith [f.u_decomp, f.k_unit, f.y_unit, hx]
  have hδL : (189 : ℝ) / 20 < g.δ := by
    nlinarith [f.δ_decomp, f.k_unit, f.y'_unit, hx']
  by_cases hδ : (19 : ℝ) / 2 ≤ g.δ
  · exact high_delta_closure g hu hδ
  · have hδlt : g.δ < (19 : ℝ) / 2 := lt_of_not_ge hδ
    have hkw : f.k ≤ f.k * g.w := by
      have hk0 : 0 ≤ f.k := by linarith [f.k_unit]
      simpa using mul_le_mul_of_nonneg_left g.w_unit hk0
    have hδy : g.δ ≤ g.δ * f.y := by
      simpa using mul_le_mul_of_nonneg_left f.y_unit g.δ_pos.le
    have hprod : g.δ + 1 ≤ g.u * f.y' := by
      nlinarith [f.identity48 h48, f.k_unit]
    have hy'lt : f.y' < (21 : ℝ) / 20 := by
      nlinarith [f.δ_decomp, f.k_unit, hx']
    have huLow : (209 : ℝ) / 21 < g.u := by
      by_contra hn
      have hule : g.u ≤ (209 : ℝ) / 21 := le_of_not_gt hn
      have hy'0 : 0 ≤ f.y' := by linarith [f.y'_unit]
      have hm : g.u * f.y' <
          ((209 : ℝ) / 21) * ((21 : ℝ) / 20) := by
        calc
          g.u * f.y' ≤ ((209 : ℝ) / 21) * f.y' :=
            mul_le_mul_of_nonneg_right hule hy'0
          _ < ((209 : ℝ) / 21) * ((21 : ℝ) / 20) :=
            mul_lt_mul_of_pos_left hy'lt (by norm_num)
      norm_num at hm
      nlinarith
    by_contra hn
    have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
    have hfactor : 0 ≤
        (g.δ - (189 : ℝ) / 20) *
          (g.δ + (189 : ℝ) / 20 - (53 : ℝ) / 5) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [g.hull_product]

lemma a_common_cell_bound
    (h47 : CrossApexIdentity47)
    {H : ℝ} (leaf : ACommonCellLeaf H) :
    (63 : ℝ) / 5 ≤ H := by
  let g := leaf.core
  let f := leaf.fan
  have hy := leaf.y_large
  have hy' := leaf.y'_large
  norm_num [F2] at hy hy'
  have hu : (189 : ℝ) / 20 < g.u := by
    nlinarith [f.u_decomp, f.x_unit, f.k_unit, hy]
  have hδL : (189 : ℝ) / 20 < g.δ := by
    nlinarith [f.δ_decomp, f.x'_unit, f.k_unit, hy']
  by_cases hδ : (19 : ℝ) / 2 ≤ g.δ
  · exact high_delta_closure g hu hδ
  · have hδlt : g.δ < (19 : ℝ) / 2 := lt_of_not_ge hδ
    have hkγ : 1 ≤ f.k * g.γ := by
      have := mul_le_mul f.k_unit g.γ_unit
        (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith [f.k_unit] : 0 ≤ f.k)
      norm_num at this ⊢
      exact this
    have hux' : g.u ≤ g.u * f.x' := by
      simpa using mul_le_mul_of_nonneg_left f.x'_unit g.u_pos.le
    have hxδ : g.u + 1 ≤ f.x * g.δ := by
      nlinarith [f.identity47 h47]
    have hxlt : f.x < g.u - (169 : ℝ) / 20 := by
      nlinarith [f.u_decomp, f.k_unit, hy]
    have h55 : g.u + 1 ≤ g.δ * (g.u - (169 : ℝ) / 20) := by
      have hm := mul_lt_mul_of_pos_right hxlt g.δ_pos
      nlinarith
    have huδ : g.δ < g.u := by
      by_contra hn
      have huδle : g.u ≤ g.δ := le_of_not_gt hn
      have hmul : (g.δ - 1) * g.u ≤ (g.δ - 1) * g.δ :=
        mul_le_mul_of_nonneg_left huδle (by linarith [g.δ_three])
      have hfactor : 0 <
          ((19 : ℝ) / 2 - g.δ) *
            (g.δ + (19 : ℝ) / 2 - (189 : ℝ) / 20) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
    have hγ : 1 + g.u - g.δ ≤ g.γ := by
      nlinarith [g.w_eq, g.w_unit]
    have hβδ : g.γ + g.u ≤ g.β * g.δ := by
      have hγ0 : 0 ≤ g.γ := by linarith [g.γ_unit]
      have hu0 : 0 ≤ g.u := by linarith [g.u_unit]
      have hαγ : g.γ ≤ g.α * g.γ := by
        simpa using mul_le_mul_of_nonneg_right g.α_unit hγ0
      have hut : g.u ≤ g.u * g.t := by
        simpa using mul_le_mul_of_nonneg_left g.t_unit hu0
      nlinarith [g.plucker]
    have hmain : 1 + 2 * g.u ≤ g.δ * (H - g.u - 1) := by
      have hrest : g.β + 1 ≤ H - g.u - 1 := by
        nlinarith [g.hull_eq, g.w_eq, g.α_unit, g.w_unit]
      have hm := mul_le_mul_of_nonneg_left hrest g.δ_pos.le
      nlinarith
    by_contra hn
    have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
    have hleft : 0 ≤
        (g.δ + 2) *
          (g.δ * (g.u - (169 : ℝ) / 20) - (g.u + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    have hright : 0 <
        (g.δ - 1) *
          (g.δ * ((58 : ℝ) / 5 - g.u) - (1 + 2 * g.u)) :=
      mul_pos (by linarith [g.δ_three]) (by nlinarith)
    have hnumer : 0 < 610 * g.δ + 20 - 63 * g.δ ^ 2 := by
      have hfactor : 0 <
          ((19 : ℝ) / 2 - g.δ) *
            (63 * (g.δ + (19 : ℝ) / 2) - 610) :=
        mul_pos (by linarith) (by nlinarith [g.δ_three])
      nlinarith
    nlinarith

lemma dp_common_residual_bound
    (h47 : CrossApexIdentity47)
    (h48 : CrossApexIdentity48)
    {H : ℝ} (leaf : DPCommonResidualLeaf H) :
    (63 : ℝ) / 5 ≤ H := by
  let g := leaf.core
  let f := leaf.fan
  by_contra hn
  have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
  have huK : g.u < (63 : ℝ) / 5 := lt_of_le_of_lt g.hull_ge_u hH
  have hδK : g.δ < (48 : ℝ) / 5 := by
    nlinarith [g.hull_eq, g.α_unit, g.β_unit, g.γ_unit]
  cases leaf.kind with
  | split hx3 hy3 hx'F =>
      change 3 ≤ f.x at hx3
      change 3 ≤ f.y at hy3
      change F2 < f.x' at hx'F
      have hxle : f.x ≤ g.u - 4 := by
        nlinarith [f.u_decomp, f.k_unit, hy3]
      have hux' : g.u * F2 < g.u * f.x' :=
        mul_lt_mul_of_pos_left hx'F g.u_pos
      have hkγ : 1 ≤ f.k * g.γ := by
        have := mul_le_mul f.k_unit g.γ_unit
          (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith [f.k_unit] : 0 ≤ f.k)
        norm_num at this ⊢
        exact this
      have hmain : g.u * (g.δ - F2) > 4 * g.δ + 1 := by
        have hm := mul_le_mul_of_nonneg_right hxle g.δ_pos.le
        nlinarith [f.identity47 h47]
      have hden : 0 ≤ g.δ - F2 := by
        nlinarith [f.δ_decomp, f.k_unit, f.y'_unit, hx'F]
      have hupp : g.u * (g.δ - F2) ≤
          ((63 : ℝ) / 5) * (g.δ - F2) :=
        mul_le_mul_of_nonneg_right huK.le hden
      norm_num [F2] at hmain hupp
      nlinarith
  | opposite hyF hx'F =>
      change F2 < f.y at hyF
      change F2 < f.x' at hx'F
      have hy'lt : f.y' < g.δ - F2 - 1 := by
        nlinarith [f.δ_decomp, hx'F, f.k_unit]
      have hδy : g.δ * F2 < g.δ * f.y :=
        mul_lt_mul_of_pos_left hyF g.δ_pos
      have hkw : 1 ≤ f.k * g.w := by
        have hk0 : 0 ≤ f.k := by linarith [f.k_unit]
        have := mul_le_mul f.k_unit g.w_unit
          (by norm_num : (0 : ℝ) ≤ 1) hk0
        norm_num at this ⊢
        exact this
      have hmain : g.u * (g.δ - F2 - 1) >
          g.δ * F2 + 1 := by
        have hm := mul_lt_mul_of_pos_left hy'lt g.u_pos
        nlinarith [f.identity48 h48]
      have hden : 0 ≤ g.δ - F2 - 1 := by
        nlinarith [f.δ_decomp, hx'F, f.y'_unit, f.k_unit]
      have hupp : g.u * (g.δ - F2 - 1) ≤
          ((63 : ℝ) / 5) * (g.δ - F2 - 1) :=
        mul_le_mul_of_nonneg_right huK.le hden
      norm_num [F2] at hmain hupp
      nlinarith

lemma ca_common_d_split_bound
    (h48 : CrossApexIdentity48)
    {H : ℝ} (leaf : CACommonDSplitLeaf H) :
    (63 : ℝ) / 5 ≤ H := by
  let g := leaf.core
  let f := leaf.fan
  by_contra hn
  have hH : H < (63 : ℝ) / 5 := lt_of_not_ge hn
  have huK : g.u < (63 : ℝ) / 5 := lt_of_le_of_lt g.hull_ge_u hH
  have hδK : g.δ < (48 : ℝ) / 5 := by
    nlinarith [g.hull_eq, g.α_unit, g.β_unit, g.γ_unit]
  have hy'le : f.y' ≤ g.δ - 4 := by
    nlinarith [f.δ_decomp, leaf.x'_three, f.k_unit]
  have hδy : g.δ * F2 < g.δ * f.y :=
    mul_lt_mul_of_pos_left leaf.y_large g.δ_pos
  have hkw : 1 ≤ f.k * g.w := by
    have hk0 : 0 ≤ f.k := by linarith [f.k_unit]
    have := mul_le_mul f.k_unit g.w_unit
      (by norm_num : (0 : ℝ) ≤ 1) hk0
    norm_num at this ⊢
    exact this
  have hmain : g.u * (g.δ - 4) > g.δ * F2 + 1 := by
    have hm := mul_le_mul_of_nonneg_left hy'le g.u_pos.le
    nlinarith [f.identity48 h48]
  have hden : 0 ≤ g.δ - 4 := by
    nlinarith [f.δ_decomp, leaf.x'_three, leaf.y'_three, f.k_unit]
  have hupp : g.u * (g.δ - 4) ≤
      ((63 : ℝ) / 5) * (g.δ - 4) :=
    mul_le_mul_of_nonneg_right huK.le hden
  norm_num [F2] at hmain hupp
  nlinarith

/-- The repaired six-leaf residual census. -/
inductive ResidualCase (H : ℝ) : Prop
  | shared : SharedCommonCellLeaf H → ResidualCase H
  | p_common : PCommonCellLeaf H → ResidualCase H
  | a_common : ACommonCellLeaf H → ResidualCase H
  | d_p_common_residual : DPCommonResidualLeaf H → ResidualCase H
  | c_a_common_d_split : CACommonDSplitLeaf H → ResidualCase H
  | cyclic : CyclicLeaf H → ResidualCase H

lemma residual_case_bound
    (h47 : CrossApexIdentity47)
    (h48 : CrossApexIdentity48)
    (hResidual : ResidualBoundHypothesis)
    {H : ℝ} (h : ResidualCase H) :
    (63 : ℝ) / 5 ≤ H := by
  cases h with
  | shared leaf => exact shared_common_cell_bound h48 leaf
  | p_common leaf => exact p_common_cell_bound h48 leaf
  | a_common leaf => exact a_common_cell_bound h47 leaf
  | d_p_common_residual leaf =>
      exact dp_common_residual_bound h47 h48 leaf
  | c_a_common_d_split leaf =>
      exact ca_common_d_split_bound h48 leaf
  | cyclic leaf => exact cyclic_leaf_bound hResidual leaf

/-- Section 11 data after the double-apex overlap lemma. -/
structure OrbitIIJ2Closure (H : ℝ)
    extends Heilbronn8.QuadHull.OrbitIIJ2Residual H where
  QAB : ℝ
  AQZ : ℝ
  QBC : ℝ
  QCD : ℝ
  QDA : ℝ
  overlap : ℝ
  hull_cells : H = QAB + QBC + QCD + QDA
  overlap_eq : overlap = QAB + AQZ
  overlap_bound : (43 : ℝ) / 5 ≤ overlap
  QBC_unit : 1 ≤ QBC
  QCD_unit : 1 ≤ QCD
  QDA_split : AQZ + 2 ≤ QDA

lemma orbit_II_j2_residual_bound {H : ℝ}
    (r : OrbitIIJ2Closure H) :
    (63 : ℝ) / 5 ≤ H := by
  nlinarith [r.hull_cells, r.overlap_eq, r.overlap_bound,
    r.QBC_unit, r.QCD_unit, r.QDA_split]

/-- Exhaustive normalized orbit certificate, including the closed II/j=2 branch. -/
inductive NormalizedOrbitCase (H : ℝ) : Prop
  | balanced (L R : ℝ) (hH : H = L + R)
      (hL : F2 < L) (hR : F2 < R)
  | opposite_three_one (f : PositivePluckerFan H)
      (hδ : (17 : ℝ) / 2 ≤ f.δ)
  | orbit_IV_j0 (f : PositivePluckerFan H)
      (hδ : (17 : ℝ) / 2 ≤ f.δ)
  | orbit_IV_j1 (f : PositivePluckerFan H)
      (hα : 3 ≤ f.α) (hδ : F2 < f.δ)
  | orbit_IV_j2 (f : PositivePluckerFan H)
      (hα : F2 < f.α) (hδ : 3 ≤ f.δ)
      (hu : f.u ≤ f.γ + f.δ - 3)
      (hv : f.v ≤ f.α + f.δ - (17 : ℝ) / 2)
  | orbit_II_j0 (f : PositivePluckerFan H)
      (hδ : (17 : ℝ) / 2 ≤ f.δ)
  | orbit_II_j1 (f : PositivePluckerFan H)
      (hα : 3 ≤ f.α) (hδ : F2 < f.δ)
  | orbit_II_j2 (r : OrbitIIJ2Direct H)
  | orbit_II_j3 (f : PositivePluckerFan H)
      (hα : (17 : ℝ) / 2 ≤ f.α)
      (hu : f.u ≤ f.γ + f.δ - 1)
      (hv : f.v ≤ f.α + f.δ - (17 : ℝ) / 2)
  | residual : ResidualCase H → NormalizedOrbitCase H

theorem normalized_quadHull8_bound
    (h47 : CrossApexIdentity47)
    (h48 : CrossApexIdentity48)
    (hResidual : ResidualBoundHypothesis)
    {H : ℝ} (hcase : NormalizedOrbitCase H) :
    (63 : ℝ) / 5 ≤ H := by
  cases hcase with
  | balanced L R hH hL hR =>
      exact balanced_two_two_bound hH hL hR
  | opposite_three_one f hδ =>
      exact opposite_three_one_bound f hδ
  | orbit_IV_j0 f hδ =>
      exact opposite_three_one_bound f hδ
  | orbit_IV_j1 f hα hδ =>
      exact one_two_fan_bound f hα hδ
  | orbit_IV_j2 f hα hδ hu hv =>
      exact Heilbronn8.QuadHull.orbit_IV_j2_bound f hα hδ hu hv
  | orbit_II_j0 f hδ =>
      exact opposite_three_one_bound f hδ
  | orbit_II_j1 f hα hδ =>
      exact one_two_fan_bound f hα hδ
  | orbit_II_j2 r =>
      exact orbit_II_j2_direct_bound r
  | orbit_II_j3 f hα hu hv =>
      exact Heilbronn8.QuadHull.orbit_II_j3_bound f hα hu hv
  | residual h =>
      exact residual_case_bound h47 h48 hResidual h


end residualClosure

/-- Ordinary oriented area of `ABCD`, split along `AC`. -/
noncomputable def quadHullArea (A B C D : Point) : ℝ :=
  oarea A B C + oarea A C D

/-- Normalization/orbit certificate, including the zero-area escape. -/
def OrbitCertificate
    (v : Fin 8 → Point) (A B C D : Fin 8) : Prop :=
  minTri v = 0 ∨
    ∃ H : ℝ,
      quadHullArea (v A) (v B) (v C) (v D) =
        minTri v / 2 * H ∧
      NormalizedOrbitCase H

/--
QuadHull8 at ordinary-area constant `5/63` for a unit-area quadrilateral.
Since `minTri` is doubled area, the conclusion divides it by two.
-/
theorem quadHull8
    (h47 : CrossApexIdentity47)
    (h48 : CrossApexIdentity48)
    (hResidual : ResidualBoundHypothesis)
    (v : Fin 8 → Point) (A B C D : Fin 8)
    (hunit : quadHullArea (v A) (v B) (v C) (v D) = 1)
    (hcert : OrbitCertificate v A B C D) :
    minTri v / 2 ≤ (5 : ℝ) / 63 := by
  rcases hcert with hmzero | ⟨H, hscale, hcase⟩
  · rw [hmzero]
    norm_num
  · have hH : (63 : ℝ) / 5 ≤ H :=
      normalized_quadHull8_bound h47 h48 hResidual hcase
    have hm : 0 ≤ minTri v / 2 := by
      have := minTri_nonneg v
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hH hm
    rw [← hscale, hunit] at hmul
    nlinarith

end Heilbronn8.QuadHull
