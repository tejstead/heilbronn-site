/-
The pentagon case: a convex-position five-tuple's minimal ear is at most
tau times the (doubled) shoelace area. The frame variables u, w, a, b of
Basic.lean are realized as ratios of signed areas; the three transfer
identities below (verified symbolically in sympy first) convert the ear
constraints and the area into the algebraic core's hypotheses.
-/
import Heil5.Ident
import Heil5.Basic

namespace Heilbronn5

lemma transfer1 (p0 p1 p2 p3 p4 : ℝ × ℝ) :
    sig p0 p2 p4 * sig p0 p1 p3 - sig p0 p1 p3 * sig p0 p1 p4
      - (sig p0 p3 p4 - sig p0 p1 p4) * sig p0 p1 p2
      = sig p1 p2 p3 * sig p0 p1 p4 := by
  simp only [sig]; ring

lemma transfer2 (p0 p1 p2 p3 p4 : ℝ × ℝ) :
    sig p0 p2 p4 * sig p0 p1 p3 - sig p0 p2 p4 * sig p0 p1 p4
      - (sig p0 p1 p2 - sig p0 p1 p4) * sig p0 p3 p4
      = sig p2 p3 p4 * sig p0 p1 p4 := by
  simp only [sig]; ring

lemma transfer3 (p0 p1 p2 p3 p4 : ℝ × ℝ) :
    sig p0 p1 p4 ^ 2 + sig p0 p2 p4 * sig p0 p1 p3
      - (sig p0 p1 p2 - sig p0 p1 p4) * (sig p0 p3 p4 - sig p0 p1 p4)
      = (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) * sig p0 p1 p4 := by
  simp only [sig]; ring

/-- Minimal-ear bound in abstract position: if the ear `sig p0 p1 p4` is
positive, the two skip triples through `p0` are positive, and the four
other ears are at least the ear at `p0`, then that ear is at most `tau`
times the doubled shoelace area (fanned from `p0`). -/
theorem ear_min_bound (p0 p1 p2 p3 p4 : ℝ × ℝ)
    (hD : 0 < sig p0 p1 p4)
    (hu : 0 < sig p0 p2 p4) (hw : 0 < sig p0 p1 p3)
    (h1e : sig p0 p1 p4 ≤ sig p0 p1 p2)
    (h2e : sig p0 p1 p4 ≤ sig p1 p2 p3)
    (h3e : sig p0 p1 p4 ≤ sig p2 p3 p4)
    (h4e : sig p0 p1 p4 ≤ sig p0 p3 p4) :
    sig p0 p1 p4 ≤ tau * (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) := by
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
    rw [key1]; exact (one_le_div hD).mpr h2e
  have h2 : 1 ≤ (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - sig p0 p2 p4 / sig p0 p1 p4
      - (sig p0 p1 p2 / sig p0 p1 p4 - 1)
        * (1 + (sig p0 p3 p4 / sig p0 p1 p4 - 1)) := by
    rw [key2]; exact (one_le_div hD).mpr h3e
  have hcore := core _ _ _ _ hu' hw' ha hb h1 h2
  -- convert the core's area bound into the shoelace form
  have keyA : 1 + (sig p0 p2 p4 / sig p0 p1 p4) * (sig p0 p1 p3 / sig p0 p1 p4)
      - (sig p0 p1 p2 / sig p0 p1 p4 - 1) * (sig p0 p3 p4 / sig p0 p1 p4 - 1)
      = (sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4) / sig p0 p1 p4 := by
    field_simp
    linear_combination transfer3 p0 p1 p2 p3 p4
  rw [keyA] at hcore
  -- (5+sqrt5)/2 <= S/D  and  tau*(5+sqrt5)/2 = 1  give  D <= tau*S
  have hS : sig p0 p1 p4 * ((5 + Real.sqrt 5) / 2)
      ≤ sig p0 p1 p2 + sig p0 p2 p3 + sig p0 p3 p4 := by
    have h := (le_div_iff₀ hD).mp hcore
    rw [mul_comm]
    exact h
  have htau2 : tau * ((5 + Real.sqrt 5) / 2) = 1 := by
    have h := tau_mul_bound
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hS tau_pos.le, htau2, hD]

/-- The pentagon case of the main theorem. -/
theorem pentagon_case (v : Fin 5 → ℝ × ℝ) (hc : ConvexPos v) :
    minTri v ≤ tau * penArea v := by
  obtain ⟨c012, c013, c014, c023, c024, c034, c123, c124, c134, c234⟩ := hc
  rcases eq_or_lt_of_le (minTri_nonneg v) with hz | hpos
  · -- degenerate: the minimum triangle is zero
    have hpen : 0 ≤ penArea v := by unfold penArea; linarith
    rw [← hz]
    exact mul_nonneg tau_pos.le hpen
  -- otherwise every canonical signed area is strictly positive
  · have s012 : 0 < sig (v 0) (v 1) (v 2) := by
      have h := minTri_le_012 v; rw [abs_of_nonneg c012] at h; linarith
    have s013 : 0 < sig (v 0) (v 1) (v 3) := by
      have h := minTri_le_013 v; rw [abs_of_nonneg c013] at h; linarith
    have s014 : 0 < sig (v 0) (v 1) (v 4) := by
      have h := minTri_le_014 v; rw [abs_of_nonneg c014] at h; linarith
    have s023 : 0 < sig (v 0) (v 2) (v 3) := by
      have h := minTri_le_023 v; rw [abs_of_nonneg c023] at h; linarith
    have s024 : 0 < sig (v 0) (v 2) (v 4) := by
      have h := minTri_le_024 v; rw [abs_of_nonneg c024] at h; linarith
    have s034 : 0 < sig (v 0) (v 3) (v 4) := by
      have h := minTri_le_034 v; rw [abs_of_nonneg c034] at h; linarith
    have s123 : 0 < sig (v 1) (v 2) (v 3) := by
      have h := minTri_le_123 v; rw [abs_of_nonneg c123] at h; linarith
    have s124 : 0 < sig (v 1) (v 2) (v 4) := by
      have h := minTri_le_124 v; rw [abs_of_nonneg c124] at h; linarith
    have s134 : 0 < sig (v 1) (v 3) (v 4) := by
      have h := minTri_le_134 v; rw [abs_of_nonneg c134] at h; linarith
    have s234 : 0 < sig (v 2) (v 3) (v 4) := by
      have h := minTri_le_234 v; rw [abs_of_nonneg c234] at h; linarith
    -- the five case blocks, one per position of the minimal ear
    have case0 : sig (v 0) (v 1) (v 4) ≤ sig (v 0) (v 1) (v 2) →
        sig (v 0) (v 1) (v 4) ≤ sig (v 1) (v 2) (v 3) →
        sig (v 0) (v 1) (v 4) ≤ sig (v 2) (v 3) (v 4) →
        sig (v 0) (v 1) (v 4) ≤ sig (v 0) (v 3) (v 4) →
        minTri v ≤ tau * penArea v := by
      intro k1 k2 k3 k4
      have hb := ear_min_bound (v 0) (v 1) (v 2) (v 3) (v 4)
        s014 s024 s013 k1 k2 k3 k4
      have hm : minTri v ≤ sig (v 0) (v 1) (v 4) := by
        have h := minTri_le_014 v; rwa [abs_of_pos s014] at h
      calc minTri v ≤ sig (v 0) (v 1) (v 4) := hm
        _ ≤ _ := hb
        _ = tau * penArea v := by unfold penArea; ring
    have case1 : sig (v 0) (v 1) (v 2) ≤ sig (v 1) (v 2) (v 3) →
        sig (v 0) (v 1) (v 2) ≤ sig (v 2) (v 3) (v 4) →
        sig (v 0) (v 1) (v 2) ≤ sig (v 0) (v 3) (v 4) →
        sig (v 0) (v 1) (v 2) ≤ sig (v 0) (v 1) (v 4) →
        minTri v ≤ tau * penArea v := by
      intro k1 k2 k3 k4
      have r0 : sig (v 1) (v 2) (v 0) = sig (v 0) (v 1) (v 2) := by
        simp only [sig]; ring
      have r1 : sig (v 1) (v 3) (v 0) = sig (v 0) (v 1) (v 3) := by
        simp only [sig]; ring
      have r2 : sig (v 3) (v 4) (v 0) = sig (v 0) (v 3) (v 4) := by
        simp only [sig]; ring
      have r3 : sig (v 1) (v 4) (v 0) = sig (v 0) (v 1) (v 4) := by
        simp only [sig]; ring
      have hb := ear_min_bound (v 1) (v 2) (v 3) (v 4) (v 0)
        (by rw [r0]; exact s012) (by rw [r1]; exact s013) s124
        (by rw [r0]; exact k1) (by rw [r0]; exact k2)
        (by rw [r0, r2]; exact k3) (by rw [r0, r3]; exact k4)
      have rb : sig (v 1) (v 2) (v 3) + sig (v 1) (v 3) (v 4)
          + sig (v 1) (v 4) (v 0) = penArea v := by
        unfold penArea; simp only [sig]; ring
      rw [rb, r0] at hb
      have hm : minTri v ≤ sig (v 0) (v 1) (v 2) := by
        have h := minTri_le_012 v; rwa [abs_of_pos s012] at h
      linarith
    have case2 : sig (v 1) (v 2) (v 3) ≤ sig (v 2) (v 3) (v 4) →
        sig (v 1) (v 2) (v 3) ≤ sig (v 0) (v 3) (v 4) →
        sig (v 1) (v 2) (v 3) ≤ sig (v 0) (v 1) (v 4) →
        sig (v 1) (v 2) (v 3) ≤ sig (v 0) (v 1) (v 2) →
        minTri v ≤ tau * penArea v := by
      intro k1 k2 k3 k4
      have r0 : sig (v 2) (v 3) (v 1) = sig (v 1) (v 2) (v 3) := by
        simp only [sig]; ring
      have r1 : sig (v 2) (v 4) (v 1) = sig (v 1) (v 2) (v 4) := by
        simp only [sig]; ring
      have r2 : sig (v 2) (v 3) (v 0) = sig (v 0) (v 2) (v 3) := by
        simp only [sig]; ring
      have r3 : sig (v 3) (v 4) (v 0) = sig (v 0) (v 3) (v 4) := by
        simp only [sig]; ring
      have r4 : sig (v 4) (v 0) (v 1) = sig (v 0) (v 1) (v 4) := by
        simp only [sig]; ring
      have r5 : sig (v 2) (v 0) (v 1) = sig (v 0) (v 1) (v 2) := by
        simp only [sig]; ring
      have hb := ear_min_bound (v 2) (v 3) (v 4) (v 0) (v 1)
        (by rw [r0]; exact s123) (by rw [r1]; exact s124)
        (by rw [r2]; exact s023)
        (by rw [r0]; exact k1) (by rw [r0, r3]; exact k2)
        (by rw [r0, r4]; exact k3) (by rw [r0, r5]; exact k4)
      have rb : sig (v 2) (v 3) (v 4) + sig (v 2) (v 4) (v 0)
          + sig (v 2) (v 0) (v 1) = penArea v := by
        unfold penArea; simp only [sig]; ring
      rw [rb, r0] at hb
      have hm : minTri v ≤ sig (v 1) (v 2) (v 3) := by
        have h := minTri_le_123 v; rwa [abs_of_pos s123] at h
      linarith
    have case3 : sig (v 2) (v 3) (v 4) ≤ sig (v 0) (v 3) (v 4) →
        sig (v 2) (v 3) (v 4) ≤ sig (v 0) (v 1) (v 4) →
        sig (v 2) (v 3) (v 4) ≤ sig (v 0) (v 1) (v 2) →
        sig (v 2) (v 3) (v 4) ≤ sig (v 1) (v 2) (v 3) →
        minTri v ≤ tau * penArea v := by
      intro k1 k2 k3 k4
      have r0 : sig (v 3) (v 4) (v 2) = sig (v 2) (v 3) (v 4) := by
        simp only [sig]; ring
      have r1 : sig (v 3) (v 0) (v 2) = sig (v 0) (v 2) (v 3) := by
        simp only [sig]; ring
      have r2 : sig (v 3) (v 4) (v 1) = sig (v 1) (v 3) (v 4) := by
        simp only [sig]; ring
      have r3 : sig (v 3) (v 4) (v 0) = sig (v 0) (v 3) (v 4) := by
        simp only [sig]; ring
      have r4 : sig (v 4) (v 0) (v 1) = sig (v 0) (v 1) (v 4) := by
        simp only [sig]; ring
      have r5 : sig (v 3) (v 1) (v 2) = sig (v 1) (v 2) (v 3) := by
        simp only [sig]; ring
      have hb := ear_min_bound (v 3) (v 4) (v 0) (v 1) (v 2)
        (by rw [r0]; exact s234) (by rw [r1]; exact s023)
        (by rw [r2]; exact s134)
        (by rw [r0, r3]; exact k1) (by rw [r0, r4]; exact k2)
        (by rw [r0]; exact k3) (by rw [r0, r5]; exact k4)
      have rb : sig (v 3) (v 4) (v 0) + sig (v 3) (v 0) (v 1)
          + sig (v 3) (v 1) (v 2) = penArea v := by
        unfold penArea; simp only [sig]; ring
      rw [rb, r0] at hb
      have hm : minTri v ≤ sig (v 2) (v 3) (v 4) := by
        have h := minTri_le_234 v; rwa [abs_of_pos s234] at h
      linarith
    have case4 : sig (v 0) (v 3) (v 4) ≤ sig (v 0) (v 1) (v 4) →
        sig (v 0) (v 3) (v 4) ≤ sig (v 0) (v 1) (v 2) →
        sig (v 0) (v 3) (v 4) ≤ sig (v 1) (v 2) (v 3) →
        sig (v 0) (v 3) (v 4) ≤ sig (v 2) (v 3) (v 4) →
        minTri v ≤ tau * penArea v := by
      intro k1 k2 k3 k4
      have r0 : sig (v 4) (v 0) (v 3) = sig (v 0) (v 3) (v 4) := by
        simp only [sig]; ring
      have r1 : sig (v 4) (v 1) (v 3) = sig (v 1) (v 3) (v 4) := by
        simp only [sig]; ring
      have r2 : sig (v 4) (v 0) (v 2) = sig (v 0) (v 2) (v 4) := by
        simp only [sig]; ring
      have r3 : sig (v 4) (v 0) (v 1) = sig (v 0) (v 1) (v 4) := by
        simp only [sig]; ring
      have r4 : sig (v 4) (v 2) (v 3) = sig (v 2) (v 3) (v 4) := by
        simp only [sig]; ring
      have hb := ear_min_bound (v 4) (v 0) (v 1) (v 2) (v 3)
        (by rw [r0]; exact s034) (by rw [r1]; exact s134)
        (by rw [r2]; exact s024)
        (by rw [r0, r3]; exact k1) (by rw [r0]; exact k2)
        (by rw [r0]; exact k3) (by rw [r0, r4]; exact k4)
      have rb : sig (v 4) (v 0) (v 1) + sig (v 4) (v 1) (v 2)
          + sig (v 4) (v 2) (v 3) = penArea v := by
        unfold penArea; simp only [sig]; ring
      rw [rb, r0] at hb
      have hm : minTri v ≤ sig (v 0) (v 3) (v 4) := by
        have h := minTri_le_034 v; rwa [abs_of_pos s034] at h
      linarith
    -- tournament over the five ears
    rcases le_total (sig (v 0) (v 1) (v 4)) (sig (v 0) (v 1) (v 2)) with h1 | h1
    · rcases le_total (sig (v 0) (v 1) (v 4)) (sig (v 1) (v 2) (v 3)) with h2 | h2
      · rcases le_total (sig (v 0) (v 1) (v 4)) (sig (v 2) (v 3) (v 4)) with h3 | h3
        · rcases le_total (sig (v 0) (v 1) (v 4)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case0 h1 h2 h3 h4
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
        · rcases le_total (sig (v 2) (v 3) (v 4)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total (sig (v 1) (v 2) (v 3)) (sig (v 2) (v 3) (v 4)) with h3 | h3
        · rcases le_total (sig (v 1) (v 2) (v 3)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case2 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
        · rcases le_total (sig (v 2) (v 3) (v 4)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
    · rcases le_total (sig (v 0) (v 1) (v 2)) (sig (v 1) (v 2) (v 3)) with h2 | h2
      · rcases le_total (sig (v 0) (v 1) (v 2)) (sig (v 2) (v 3) (v 4)) with h3 | h3
        · rcases le_total (sig (v 0) (v 1) (v 2)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case1 h2 h3 h4 h1
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
        · rcases le_total (sig (v 2) (v 3) (v 4)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total (sig (v 1) (v 2) (v 3)) (sig (v 2) (v 3) (v 4)) with h3 | h3
        · rcases le_total (sig (v 1) (v 2) (v 3)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case2 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
        · rcases le_total (sig (v 2) (v 3) (v 4)) (sig (v 0) (v 3) (v 4)) with h4 | h4
          · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)

end Heilbronn5
