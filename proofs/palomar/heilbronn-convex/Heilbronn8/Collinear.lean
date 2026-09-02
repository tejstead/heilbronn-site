/-
Collinear and degenerate configurations. A zero determinant at any increasing
triple forces the finite minimum triangle area to vanish. Three collinear
points also have the standard betweenness alternative.
-/
import Heilbronn8.Defs

namespace Heilbronn8

/-- A concrete witness that one of the 56 increasing triples is degenerate. -/
def HasZeroTriple (v : Fin 8 → ℝ × ℝ) : Prop :=
  ∃ i j k : Fin 8, i < j ∧ j < k ∧ sig (v i) (v j) (v k) = 0

/-- Every one of the 56 increasing triples has a nonzero orientation. -/
def AllTripleSignsStrict (v : Fin 8 → ℝ × ℝ) : Prop :=
  ∀ i j k : Fin 8, i < j → j < k → sig (v i) (v j) (v k) ≠ 0

/-- The exhaustive top-level sign dispatcher. Equality belongs to the
degenerate branch, so the strict branch contains no hidden generic-position
assumption. -/
theorem zeroTriple_or_allTripleSignsStrict (v : Fin 8 → ℝ × ℝ) :
    HasZeroTriple v ∨ AllTripleSignsStrict v := by
  classical
  by_cases hzero : HasZeroTriple v
  · exact Or.inl hzero
  · right
    intro i j k hij hjk hsig
    exact hzero ⟨i, j, k, hij, hjk, hsig⟩

/-- A zero signed area at one of the 56 increasing triples forces the minimum
triangle area to be zero. -/
lemma minTri_eq_zero_of_sig_zero (v : Fin 8 → ℝ × ℝ)
    {i j k : Fin 8} (h : sig (v i) (v j) (v k) = 0)
    (hij : i < j) (hjk : j < k) :
    minTri v = 0 := by
  apply le_antisymm
  · calc
      minTri v ≤ |sig (v i) (v j) (v k)| := minTri_le v hij hjk
      _ = 0 := by rw [h, abs_zero]
  · exact minTri_nonneg v

/-- Dispatcher-friendly form of `minTri_eq_zero_of_sig_zero`. -/
lemma minTri_eq_zero_of_hasZeroTriple (v : Fin 8 → ℝ × ℝ)
    (h : HasZeroTriple v) : minTri v = 0 := by
  obtain ⟨i, j, k, hij, hjk, hzero⟩ := h
  exact minTri_eq_zero_of_sig_zero v hzero hij hjk

/-- If `sig p q r = 0`, one of the three points lies in the triangle of the
other two and any auxiliary fourth point `w`. -/
lemma collinear_between (p q r w : ℝ × ℝ) (h : sig p q r = 0) :
    InTri p q r w ∨ InTri q p r w ∨ InTri r p q w := by
  by_cases hqr : q = r
  · exact Or.inr (Or.inl ⟨0, 1, 0, le_refl 0, zero_le_one, le_refl 0,
      by norm_num, by subst hqr; module⟩)
  · have hdd : 0 < (r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2 := by
      rcases eq_or_ne r.1 q.1 with h1 | h1
      · rcases eq_or_ne r.2 q.2 with h2 | h2
        · exact absurd (Prod.ext h1.symm h2.symm) hqr
        · have h2' : (r.2 - q.2) ^ 2 > 0 := by
            have : r.2 - q.2 ≠ 0 := sub_ne_zero.mpr h2
            positivity
          nlinarith [sq_nonneg (r.1 - q.1)]
      · have h1' : (r.1 - q.1) ^ 2 > 0 := by
          have : r.1 - q.1 ≠ 0 := sub_ne_zero.mpr h1
          positivity
        nlinarith [sq_nonneg (r.2 - q.2)]
    have hddne : (r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2 ≠ 0 := ne_of_gt hdd
    have hsig :
        (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2) = 0 := h
    set t : ℝ :=
      ((p.1 - q.1) * (r.1 - q.1) + (p.2 - q.2) * (r.2 - q.2)) /
        ((r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2) with htdef
    have key1 :
        p.1 * ((r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2)
          =
        (((r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2) -
            ((p.1 - q.1) * (r.1 - q.1) +
              (p.2 - q.2) * (r.2 - q.2))) * q.1
          +
        ((p.1 - q.1) * (r.1 - q.1) +
            (p.2 - q.2) * (r.2 - q.2)) * r.1 := by
      linear_combination (q.2 - r.2) * hsig
    have key2 :
        p.2 * ((r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2)
          =
        (((r.1 - q.1) ^ 2 + (r.2 - q.2) ^ 2) -
            ((p.1 - q.1) * (r.1 - q.1) +
              (p.2 - q.2) * (r.2 - q.2))) * q.2
          +
        ((p.1 - q.1) * (r.1 - q.1) +
            (p.2 - q.2) * (r.2 - q.2)) * r.2 := by
      linear_combination (r.1 - q.1) * hsig
    have hp1 : p.1 = (1 - t) * q.1 + t * r.1 := by
      rw [htdef]
      field_simp
      linear_combination key1
    have hp2 : p.2 = (1 - t) * q.2 + t * r.2 := by
      rw [htdef]
      field_simp
      linear_combination key2
    rcases le_total 0 t with ht0 | ht0
    · rcases le_total t 1 with ht1 | ht1
      · refine Or.inl
          ⟨1 - t, t, 0, by linarith, ht0, le_refl 0, by ring, ?_⟩
        refine Prod.ext ?_ ?_
        · show p.1 = ((1 - t) • q + t • r + (0 : ℝ) • w).1
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          rw [hp1]
          ring
        · show p.2 = ((1 - t) • q + t • r + (0 : ℝ) • w).2
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          rw [hp2]
          ring
      · have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
        have htne : t ≠ 0 := ne_of_gt htpos
        refine Or.inr (Or.inr
          ⟨1 / t, 1 - 1 / t, 0, by positivity, ?_, le_refl 0, by ring, ?_⟩)
        · have : 1 / t ≤ 1 := by
            rw [div_le_one htpos]
            exact ht1
          linarith
        · refine Prod.ext ?_ ?_
          · show r.1 =
                ((1 / t) • p + (1 - 1 / t) • q + (0 : ℝ) • w).1
            simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
            rw [hp1]
            field_simp
            ring
          · show r.2 =
                ((1 / t) • p + (1 - 1 / t) • q + (0 : ℝ) • w).2
            simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
            rw [hp2]
            field_simp
            ring
    · have h1t : 0 < 1 - t := by
        linarith
      have h1tne : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t
      refine Or.inr (Or.inl
        ⟨1 / (1 - t), -t / (1 - t), 0, by positivity,
          div_nonneg (by linarith) (by linarith), le_refl 0, ?_, ?_⟩)
      · rw [show (1 : ℝ) / (1 - t) + -t / (1 - t) + 0 =
          (1 - t) / (1 - t) from by ring, div_self h1tne]
      · refine Prod.ext ?_ ?_
        · show q.1 =
              ((1 / (1 - t)) • p + (-t / (1 - t)) • r +
                (0 : ℝ) • w).1
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          rw [hp1]
          field_simp
          ring
        · show q.2 =
              ((1 / (1 - t)) • p + (-t / (1 - t)) • r +
                (0 : ℝ) • w).2
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          rw [hp2]
          field_simp
          ring

end Heilbronn8
