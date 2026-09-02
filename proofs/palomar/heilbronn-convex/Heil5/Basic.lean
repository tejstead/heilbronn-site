/-
Formalization of the algebraic core of the convex Heilbronn n = 5 proof
(PROOF.md, section 3b/3c).

Setting: a convex pentagon is affinely normalized to
  v1 = (0,0), v2 = (1,0), v3 = (u, 1+a), v4 = (1+b, w), v5 = (0,1)
with u, w > 0 and a, b >= 0, where the ear at v1 is minimal (doubled area 1).
Exact identities (checked symbolically in verify.py):
  2*E3 = u*w - w - b*(1+a),  2*E4 = u*w - u - a*(1+b),  2*[H] = 1 + u*w - a*b.
The minimality of E1 gives the hypotheses h1, h2 below.

Theorems:
  * `sum_ge`   : u + w >= 1 + sqrt 5
  * `core`     : 1 + u*w - a*b >= (5 + sqrt 5)/2   (i.e. [H] >= (5+sqrt 5)/4)
  * `ratio_le` : E1/[H] = (1/2)/([H]) <= tau = (5 - sqrt 5)/10
  * `equality` : equality forces a = b = 0 and u = w = phi
  * `attained` : the affinely regular data attains tau exactly
-/
import Mathlib

namespace Heilbronn5

noncomputable def tau : ℝ := (5 - Real.sqrt 5) / 10

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma sqrt5_mul_self : Real.sqrt 5 * Real.sqrt 5 = 5 :=
  Real.mul_self_sqrt (by norm_num)

lemma sqrt5_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5

lemma two_le_sqrt5 : (2 : ℝ) ≤ Real.sqrt 5 := by
  nlinarith [sqrt5_mul_self, sqrt5_nonneg]

lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [sqrt5_mul_self, sqrt5_nonneg]

lemma tau_pos : 0 < tau := by
  unfold tau; nlinarith [sqrt5_lt_three]

/-- Step 1 of the proof: the two ear constraints force `u + w ≥ 1 + √5`. -/
theorem sum_ge (u w a b : ℝ) (hu : 0 < u) (hw : 0 < w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : 1 ≤ u * w - w - b * (1 + a)) (h2 : 1 ≤ u * w - u - a * (1 + b)) :
    1 + Real.sqrt 5 ≤ u + w := by
  have hb1 : 0 ≤ b * (1 + a) := mul_nonneg hb (by linarith)
  have ha1 : 0 ≤ a * (1 + b) := mul_nonneg ha (by linarith)
  -- from the constraints: 2uw ≥ 2 + u + w; with (u-w)² ≥ 0: (u+w)² ≥ 2(u+w) + 4
  have key : 0 ≤ (u + w) ^ 2 - 2 * (u + w) - 4 := by
    nlinarith [sq_nonneg (u - w), hb1, ha1]
  by_contra hlt
  push_neg at hlt
  have hfac : 0 < u + w - 1 + Real.sqrt 5 := by
    nlinarith [two_le_sqrt5]
  have hprod : 0 < (1 + Real.sqrt 5 - (u + w)) * (u + w - 1 + Real.sqrt 5) :=
    mul_pos (by linarith) hfac
  nlinarith [hprod, sqrt5_mul_self, key]

/-- Step 2: the doubled hull area `1 + uw - ab` is at least `(5 + √5)/2`. -/
theorem core (u w a b : ℝ) (hu : 0 < u) (hw : 0 < w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : 1 ≤ u * w - w - b * (1 + a)) (h2 : 1 ≤ u * w - u - a * (1 + b)) :
    (5 + Real.sqrt 5) / 2 ≤ 1 + u * w - a * b := by
  have hs := sum_ge u w a b hu hw ha hb h1 h2
  nlinarith [hs, ha, hb]

lemma tau_mul_bound : tau * ((5 + Real.sqrt 5) / 4) = 1 / 2 := by
  unfold tau
  have h := sqrt5_mul_self
  field_simp
  linear_combination (-2 : ℝ) * h

/-- The normalized ear-to-area ratio is at most `τ = (5 - √5)/10`. -/
theorem ratio_le (u w a b : ℝ) (hu : 0 < u) (hw : 0 < w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : 1 ≤ u * w - w - b * (1 + a)) (h2 : 1 ≤ u * w - u - a * (1 + b)) :
    (1 / 2) / ((1 + u * w - a * b) / 2) ≤ tau := by
  have hcore := core u w a b hu hw ha hb h1 h2
  have hApos : 0 < (1 + u * w - a * b) / 2 := by
    nlinarith [sqrt5_nonneg]
  rw [div_le_iff₀ hApos]
  calc (1 : ℝ) / 2 = tau * ((5 + Real.sqrt 5) / 4) := tau_mul_bound.symm
    _ ≤ tau * ((1 + u * w - a * b) / 2) := by
        apply mul_le_mul_of_nonneg_left _ tau_pos.le
        linarith

/-- Equality analysis: the area bound is attained only at the affinely
regular pentagon, i.e. `a = b = 0` and `u = w = φ`. -/
theorem equality (u w a b : ℝ) (hu : 0 < u) (hw : 0 < w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : 1 ≤ u * w - w - b * (1 + a)) (h2 : 1 ≤ u * w - u - a * (1 + b))
    (heq : 1 + u * w - a * b = (5 + Real.sqrt 5) / 2) :
    a = 0 ∧ b = 0 ∧ u = phi ∧ w = phi := by
  have hs := sum_ge u w a b hu hw ha hb h1 h2
  -- adding h1 and h2: 2uw - (u+w) - (a+b) - 2ab ≥ 2; with heq this pins a + b ≤ 0
  have ha0 : a = 0 := by nlinarith [hs, mul_nonneg ha hb]
  have hb0 : b = 0 := by nlinarith [hs, mul_nonneg ha hb]
  subst ha0; subst hb0
  -- now uw = (3+√5)/2, and h1, h2 read uw - w ≥ 1, uw - u ≥ 1
  have huw : u * w = (3 + Real.sqrt 5) / 2 := by linarith [heq]
  have hu_le : u ≤ phi := by unfold phi; nlinarith [h2]
  have hw_le : w ≤ phi := by unfold phi; nlinarith [h1]
  have hsum : 2 * phi ≤ u + w := by unfold phi; linarith [hs]
  exact ⟨rfl, rfl, by linarith, by linarith⟩

/-- The bound `τ` is attained at the affinely regular data. -/
theorem attained :
    (1 / 2) / ((1 + phi * phi - 0 * 0) / 2) = tau := by
  have h := sqrt5_mul_self
  have hphi : phi * phi = (3 + Real.sqrt 5) / 2 := by
    unfold phi; field_simp; linear_combination h
  rw [hphi]
  unfold tau
  rw [div_eq_iff (by nlinarith [sqrt5_nonneg] : ((1 + (3 + Real.sqrt 5) / 2 - 0 * 0) / 2 : ℝ) ≠ 0)]
  field_simp
  linear_combination h

end Heilbronn5
