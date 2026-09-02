/-
Rigidity layer for n = 5: the equality case of the pentagon ear bound, and
the fact that an optimal configuration's hull is a pentagon.
-/
import Heil5.Main

set_option linter.style.header false

namespace Heilbronn5

lemma quarter_lt_tau : (1 / 4 : ℝ) < tau := by
  have hsqrt : Real.sqrt 5 < 5 / 2 := by
    nlinarith [sqrt5_mul_self, sqrt5_nonneg]
  unfold tau
  linarith

lemma fifth_lt_tau : (1 / 5 : ℝ) < tau := by
  unfold tau
  linarith [sqrt5_lt_three]

theorem ear_min_bound_eq (p0 p1 p2 p3 p4 : ℝ × ℝ)
    (hD : 0 < sig p0 p1 p4)
    (hu : 0 < sig p0 p2 p4) (hw : 0 < sig p0 p1 p3)
    (h1e : sig p0 p1 p4 ≤ sig p0 p1 p2)
    (h2e : sig p0 p1 p4 ≤ sig p1 p2 p3)
    (h3e : sig p0 p1 p4 ≤ sig p2 p3 p4)
    (h4e : sig p0 p1 p4 ≤ sig p0 p3 p4)
    (heq : sig p0 p1 p4
      = tau * (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4)) :
    sig p0 p1 p2 = sig p0 p1 p4 ∧ sig p0 p3 p4 = sig p0 p1 p4 ∧
      sig p0 p2 p4 = phi * sig p0 p1 p4 ∧
      sig p0 p1 p3 = phi * sig p0 p1 p4 := by
  have hD' : sig p0 p1 p4 ≠ 0 := ne_of_gt hD
  -- the frame data for the algebraic core
  have hu' : 0 < sig p0 p2 p4 / sig p0 p1 p4 := div_pos hu hD
  have hw' : 0 < sig p0 p1 p3 / sig p0 p1 p4 := div_pos hw hD
  have ha : 0 ≤ sig p0 p1 p2 / sig p0 p1 p4 - 1 :=
    sub_nonneg.mpr ((one_le_div hD).mpr h1e)
  have hb : 0 ≤ sig p0 p3 p4 / sig p0 p1 p4 - 1 :=
    sub_nonneg.mpr ((one_le_div hD).mpr h4e)
  have key1 : (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - sig p0 p1 p3 / sig p0 p1 p4
      - (sig p0 p3 p4 / sig p0 p1 p4 - 1)
        * (1 + (sig p0 p1 p2 / sig p0 p1 p4 - 1))
      = sig p1 p2 p3 / sig p0 p1 p4 := by
    field_simp
    linear_combination transfer1 p0 p1 p2 p3 p4
  have key2 : (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - sig p0 p2 p4 / sig p0 p1 p4
      - (sig p0 p1 p2 / sig p0 p1 p4 - 1)
        * (1 + (sig p0 p3 p4 / sig p0 p1 p4 - 1))
      = sig p2 p3 p4 / sig p0 p1 p4 := by
    field_simp
    linear_combination transfer2 p0 p1 p2 p3 p4
  have h1 : 1 ≤ (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - sig p0 p1 p3 / sig p0 p1 p4
      - (sig p0 p3 p4 / sig p0 p1 p4 - 1)
        * (1 + (sig p0 p1 p2 / sig p0 p1 p4 - 1)) := by
    rw [key1]
    exact (one_le_div hD).mpr h2e
  have h2 : 1 ≤ (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - sig p0 p2 p4 / sig p0 p1 p4
      - (sig p0 p1 p2 / sig p0 p1 p4 - 1)
        * (1 + (sig p0 p3 p4 / sig p0 p1 p4 - 1)) := by
    rw [key2]
    exact (one_le_div hD).mpr h3e
  have keyA : 1 + (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - (sig p0 p1 p2 / sig p0 p1 p4 - 1) * (sig p0 p3 p4 / sig p0 p1 p4 - 1)
      = (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) / sig p0 p1 p4 := by
    field_simp
    linear_combination transfer3 p0 p1 p2 p3 p4
  have htau2 : tau * ((5 + Real.sqrt 5) / 2) = 1 := by
    have h := tau_mul_bound
    linarith
  have hratio :
      (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) / sig p0 p1 p4
        = (5 + Real.sqrt 5) / 2 := by
    apply (div_eq_iff hD').2
    calc
      sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4 =
          1 * (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) := by ring
      _ = (tau * ((5 + Real.sqrt 5) / 2)) *
          (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) := by rw [htau2]
      _ = ((5 + Real.sqrt 5) / 2) * sig p0 p1 p4 := by rw [heq]; ring
  have hframe :
      1 + (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
        - (sig p0 p1 p2 / sig p0 p1 p4 - 1) *
          (sig p0 p3 p4 / sig p0 p1 p4 - 1)
        = (5 + Real.sqrt 5) / 2 := by
    rw [keyA, hratio]
  obtain ⟨ha0, hb0, hu0, hw0⟩ :=
    Heilbronn5.equality (sig p0 p2 p4 / sig p0 p1 p4)
      (sig p0 p1 p3 / sig p0 p1 p4)
      (sig p0 p1 p2 / sig p0 p1 p4 - 1)
      (sig p0 p3 p4 / sig p0 p1 p4 - 1)
      hu' hw' ha hb h1 h2 hframe
  have ha1 : sig p0 p1 p2 / sig p0 p1 p4 = 1 := by linarith
  have hb1 : sig p0 p3 p4 / sig p0 p1 p4 = 1 := by linarith
  exact ⟨(div_eq_one_iff_eq hD').mp ha1, (div_eq_one_iff_eq hD').mp hb1,
    (div_eq_iff hD').mp hu0, (div_eq_iff hD').mp hw0⟩

theorem hull_pent_of_optimal (v : Fin 5 → ℝ × ℝ) (H : ℝ)
    (hH : IsHullArea v H) (hone : H = 1) (hmin : minTri v = 2 * tau) :
    ∃ f : Fin 5 → Fin 5, Function.Injective f ∧ ConvexPos (v ∘ f) ∧
      penArea (v ∘ f) = 2 := by
  cases hH with
  | pent f hf hc =>
      exact ⟨f, hf, hc, by linarith⟩
  | quad f hf hq hw =>
      have hm := minTri_comp_inj_le v f hf
      have hqc := quad_case (v ∘ f) hq hw
      exfalso
      linarith [quarter_lt_tau]
  | tri f hf h012 h3 h4 =>
      have hm := minTri_comp_inj_le v f hf
      have htc := tri_case (v ∘ f) h012 h3 h4
      exfalso
      linarith [fifth_lt_tau]

end Heilbronn5
