/-
Attainment and equality-bridging, addressing the cross-review findings:
(1) a bridge from ratio equality to area equality;
(2) the golden data satisfies the ear constraints with EQUALITY;
(3) concrete geometric attainment: the golden pentagon has
    minTri = tau * penArea, is in convex position, and is affinely regular.
-/
import Heil5.Defs
import Heil5.Basic

namespace Heilbronn5

lemma phi_sq : phi * phi = phi + 1 := by
  unfold phi
  have h := sqrt5_mul_self
  field_simp
  linear_combination h

lemma one_le_phi : 1 ≤ phi := by
  unfold phi
  nlinarith [two_le_sqrt5]

lemma phi_pos : 0 < phi := lt_of_lt_of_le one_pos one_le_phi

/-- The golden data satisfies the ear constraints with equality. -/
lemma golden_constraint : phi * phi - phi - (0 : ℝ) * (1 + 0) = 1 := by
  rw [phi_sq]; ring

/-- Bridge (cross-review finding 1): ratio equality forces area equality. -/
lemma area_eq_of_ratio_eq (u w a b : ℝ)
    (hcore : (5 + Real.sqrt 5) / 2 ≤ 1 + u * w - a * b)
    (heq : (1 / 2) / ((1 + u * w - a * b) / 2) = tau) :
    1 + u * w - a * b = (5 + Real.sqrt 5) / 2 := by
  have hApos : 0 < (1 + u * w - a * b) / 2 := by nlinarith [sqrt5_nonneg]
  have h2 : (1 : ℝ) / 2 = tau * ((1 + u * w - a * b) / 2) :=
    (div_eq_iff (ne_of_gt hApos)).mp heq
  have h4 : tau * ((5 + Real.sqrt 5) / 4) = tau * ((1 + u * w - a * b) / 2) := by
    rw [tau_mul_bound, h2]
  have := mul_left_cancel₀ (ne_of_gt tau_pos) h4
  linarith

lemma golden_sig_ears :
    sig (golden 0) (golden 1) (golden 2) = 1 ∧
    sig (golden 1) (golden 2) (golden 3) = 1 ∧
    sig (golden 2) (golden 3) (golden 4) = 1 ∧
    sig (golden 0) (golden 3) (golden 4) = 1 ∧
    sig (golden 0) (golden 1) (golden 4) = 1 := by
  have h := phi_sq
  have hg : ((1 + Real.sqrt 5) / 2 : ℝ) = phi := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [golden, sig, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.cons_val_four]
    try simp only [hg]
    first
      | ring1
      | linear_combination h
      | linear_combination -h

lemma golden_sig_nonears :
    sig (golden 0) (golden 1) (golden 3) = phi ∧
    sig (golden 0) (golden 2) (golden 3) = phi ∧
    sig (golden 0) (golden 2) (golden 4) = phi ∧
    sig (golden 1) (golden 2) (golden 4) = phi ∧
    sig (golden 1) (golden 3) (golden 4) = phi := by
  have h := phi_sq
  have hg : ((1 + Real.sqrt 5) / 2 : ℝ) = phi := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [golden, sig, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.cons_val_four]
    try simp only [hg]
    first
      | ring1
      | linear_combination h
      | linear_combination -h

/-- Attainment (cross-review finding 2), geometric form. -/
theorem golden_attains : minTri golden = tau * penArea golden := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := golden_sig_ears
  obtain ⟨n1, n2, n3, n4, n5⟩ := golden_sig_nonears
  have hphi : (1 : ℝ) ≤ phi := one_le_phi
  have hmin : minTri golden = 1 := by
    unfold minTri
    rw [e1, e2, e3, e4, e5, n1, n2, n3, n4, n5, abs_one, abs_of_pos phi_pos]
    simp only [min_eq_left hphi, min_eq_right hphi, min_self]
  have hpen : penArea golden = 2 + phi := by
    unfold penArea
    rw [e1, n2, e4]; ring
  rw [hmin, hpen]
  unfold phi
  linear_combination (-2 : ℝ) * tau_mul_bound

/-- The golden pentagon is in convex position (CCW). -/
theorem golden_convexPos : ConvexPos golden := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := golden_sig_ears
  obtain ⟨n1, n2, n3, n4, n5⟩ := golden_sig_nonears
  have hphi : (0 : ℝ) ≤ phi := phi_pos.le
  exact ⟨by rw [e1]; norm_num, by rw [n1]; exact hphi, by rw [e5]; norm_num,
    by rw [n2]; exact hphi, by rw [n3]; exact hphi, by rw [e4]; norm_num,
    by rw [e2]; norm_num, by rw [n4]; exact hphi, by rw [n5]; exact hphi,
    by rw [e3]; norm_num⟩

/-- The golden pentagon is affinely regular (witness: the identity map). -/
theorem golden_isAffineRegular : IsAffineRegular golden :=
  ⟨Equiv.refl _, 1, 0, 0, 1, 0, 0, by norm_num,
    fun i => Prod.ext (by simp) (by simp)⟩

end Heilbronn5
