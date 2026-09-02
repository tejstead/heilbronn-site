/-
Structure of the optimal five-point configurations: the hull is a pentagon in
convex position whose five ear areas and two diagonals are pinned.
-/
import Heil5.Rigid
import Heil5.Bridge

set_option linter.style.header false

namespace Heilbronn5

def rot1 : Fin 5 → Fin 5 := ![1, 2, 3, 4, 0]

def rot4 : Fin 5 → Fin 5 := ![4, 0, 1, 2, 3]

def rot0 : Fin 5 → Fin 5 := ![0, 1, 2, 3, 4]

def rot2 : Fin 5 → Fin 5 := ![2, 3, 4, 0, 1]

def rot3 : Fin 5 → Fin 5 := ![3, 4, 0, 1, 2]

lemma rot1_injective : Function.Injective rot1 := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rot1]

lemma rot4_injective : Function.Injective rot4 := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rot4]

lemma rot0_injective : Function.Injective rot0 := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rot0]

lemma rot2_injective : Function.Injective rot2 := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rot2]

lemma rot3_injective : Function.Injective rot3 := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rot3]

lemma comp_rot1_rot4 (v : Fin 5 → ℝ × ℝ) : (v ∘ rot1) ∘ rot4 = v := by
  funext i
  fin_cases i <;> rfl

lemma comp_rot2 (v : Fin 5 → ℝ × ℝ) :
    v ∘ rot2 = (v ∘ rot1) ∘ rot1 := by
  funext i
  fin_cases i <;> rfl

lemma comp_rot3 (v : Fin 5 → ℝ × ℝ) :
    v ∘ rot3 = ((v ∘ rot1) ∘ rot1) ∘ rot1 := by
  funext i
  fin_cases i <;> rfl

lemma comp_rot4_iter (v : Fin 5 → ℝ × ℝ) :
    v ∘ rot4 = (((v ∘ rot1) ∘ rot1) ∘ rot1) ∘ rot1 := by
  funext i
  fin_cases i <;> rfl

lemma penArea_rot1 (v : Fin 5 → ℝ × ℝ) : penArea (v ∘ rot1) = penArea v := by
  simp only [penArea, Function.comp_apply, rot1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, Matrix.cons_val_four]
  simp only [sig]
  ring

lemma convexPos_rot1 (v : Fin 5 → ℝ × ℝ) (h : ConvexPos v) :
    ConvexPos (v ∘ rot1) := by
  obtain ⟨c012, c013, c014, c023, c024, c034, c123, c124, c134, c234⟩ := h
  simp only [ConvexPos, Function.comp_apply, rot1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, Matrix.cons_val_four]
  refine ⟨c123, c124, ?_, c134, ?_, ?_, c234, ?_, ?_, ?_⟩
  · rw [show sig (v 1) (v 2) (v 0) = sig (v 0) (v 1) (v 2) by
      simp only [sig]; ring]
    exact c012
  · rw [show sig (v 1) (v 3) (v 0) = sig (v 0) (v 1) (v 3) by
      simp only [sig]; ring]
    exact c013
  · rw [show sig (v 1) (v 4) (v 0) = sig (v 0) (v 1) (v 4) by
      simp only [sig]; ring]
    exact c014
  · rw [show sig (v 2) (v 3) (v 0) = sig (v 0) (v 2) (v 3) by
      simp only [sig]; ring]
    exact c023
  · rw [show sig (v 2) (v 4) (v 0) = sig (v 0) (v 2) (v 4) by
      simp only [sig]; ring]
    exact c024
  · rw [show sig (v 3) (v 4) (v 0) = sig (v 0) (v 3) (v 4) by
      simp only [sig]; ring]
    exact c034

lemma minTri_rot1 (v : Fin 5 → ℝ × ℝ) : minTri (v ∘ rot1) = minTri v := by
  have hforward := minTri_comp_inj_le v rot1 rot1_injective
  have hback := minTri_comp_inj_le (v ∘ rot1) rot4 rot4_injective
  rw [comp_rot1_rot4] at hback
  exact le_antisymm hback hforward

lemma penArea_rot2 (v : Fin 5 → ℝ × ℝ) : penArea (v ∘ rot2) = penArea v := by
  rw [comp_rot2, penArea_rot1, penArea_rot1]

lemma penArea_rot3 (v : Fin 5 → ℝ × ℝ) : penArea (v ∘ rot3) = penArea v := by
  rw [comp_rot3, penArea_rot1, penArea_rot1, penArea_rot1]

lemma penArea_rot4 (v : Fin 5 → ℝ × ℝ) : penArea (v ∘ rot4) = penArea v := by
  rw [comp_rot4_iter, penArea_rot1, penArea_rot1, penArea_rot1, penArea_rot1]

lemma convexPos_rot2 (v : Fin 5 → ℝ × ℝ) (h : ConvexPos v) :
    ConvexPos (v ∘ rot2) := by
  rw [comp_rot2]
  exact convexPos_rot1 (v ∘ rot1) (convexPos_rot1 v h)

lemma convexPos_rot3 (v : Fin 5 → ℝ × ℝ) (h : ConvexPos v) :
    ConvexPos (v ∘ rot3) := by
  rw [comp_rot3]
  exact convexPos_rot1 ((v ∘ rot1) ∘ rot1)
    (convexPos_rot1 (v ∘ rot1) (convexPos_rot1 v h))

lemma convexPos_rot4 (v : Fin 5 → ℝ × ℝ) (h : ConvexPos v) :
    ConvexPos (v ∘ rot4) := by
  rw [comp_rot4_iter]
  exact convexPos_rot1 (((v ∘ rot1) ∘ rot1) ∘ rot1)
    (convexPos_rot1 ((v ∘ rot1) ∘ rot1)
      (convexPos_rot1 (v ∘ rot1) (convexPos_rot1 v h)))

lemma minTri_rot2 (v : Fin 5 → ℝ × ℝ) : minTri (v ∘ rot2) = minTri v := by
  rw [comp_rot2, minTri_rot1, minTri_rot1]

lemma minTri_rot3 (v : Fin 5 → ℝ × ℝ) : minTri (v ∘ rot3) = minTri v := by
  rw [comp_rot3, minTri_rot1, minTri_rot1, minTri_rot1]

lemma minTri_rot4 (v : Fin 5 → ℝ × ℝ) : minTri (v ∘ rot4) = minTri v := by
  rw [comp_rot4_iter, minTri_rot1, minTri_rot1, minTri_rot1, minTri_rot1]

lemma minTri_comp_equiv (v : Fin 5 → ℝ × ℝ) (e : Equiv.Perm (Fin 5)) :
    minTri (v ∘ e) = minTri v := by
  have hforward := minTri_comp_inj_le v e e.injective
  have hback := minTri_comp_inj_le (v ∘ e) e.symm e.symm.injective
  have hcancel : (v ∘ e) ∘ e.symm = v := by
    funext i
    simp
  rw [hcancel] at hback
  exact le_antisymm hback hforward

theorem five_aligned (w : Fin 5 → ℝ × ℝ) (hc : ConvexPos w)
    (hpen : penArea w = 2) (hmin : minTri w = 2 * tau)
    (k1 : sig (w 0) (w 1) (w 4) ≤ sig (w 0) (w 1) (w 2))
    (k2 : sig (w 0) (w 1) (w 4) ≤ sig (w 1) (w 2) (w 3))
    (k3 : sig (w 0) (w 1) (w 4) ≤ sig (w 2) (w 3) (w 4))
    (k4 : sig (w 0) (w 1) (w 4) ≤ sig (w 0) (w 3) (w 4)) :
    sig (w 0) (w 1) (w 4) = 2 * tau ∧
    sig (w 0) (w 1) (w 2) = 2 * tau ∧
    sig (w 0) (w 3) (w 4) = 2 * tau ∧
    sig (w 0) (w 2) (w 4) = phi * (2 * tau) ∧
    sig (w 0) (w 1) (w 3) = phi * (2 * tau) := by
  obtain ⟨c012, c013, c014, c023, c024, c034, c123, c124, c134, c234⟩ := hc
  have hpos : 0 < minTri w := by
    rw [hmin]
    nlinarith [tau_pos]
  have s012 : 0 < sig (w 0) (w 1) (w 2) := by
    have h := minTri_le_012 w
    rw [abs_of_nonneg c012] at h
    linarith
  have s013 : 0 < sig (w 0) (w 1) (w 3) := by
    have h := minTri_le_013 w
    rw [abs_of_nonneg c013] at h
    linarith
  have s014 : 0 < sig (w 0) (w 1) (w 4) := by
    have h := minTri_le_014 w
    rw [abs_of_nonneg c014] at h
    linarith
  have s023 : 0 < sig (w 0) (w 2) (w 3) := by
    have h := minTri_le_023 w
    rw [abs_of_nonneg c023] at h
    linarith
  have s024 : 0 < sig (w 0) (w 2) (w 4) := by
    have h := minTri_le_024 w
    rw [abs_of_nonneg c024] at h
    linarith
  have s034 : 0 < sig (w 0) (w 3) (w 4) := by
    have h := minTri_le_034 w
    rw [abs_of_nonneg c034] at h
    linarith
  have s123 : 0 < sig (w 1) (w 2) (w 3) := by
    have h := minTri_le_123 w
    rw [abs_of_nonneg c123] at h
    linarith
  have s124 : 0 < sig (w 1) (w 2) (w 4) := by
    have h := minTri_le_124 w
    rw [abs_of_nonneg c124] at h
    linarith
  have s134 : 0 < sig (w 1) (w 3) (w 4) := by
    have h := minTri_le_134 w
    rw [abs_of_nonneg c134] at h
    linarith
  have s234 : 0 < sig (w 2) (w 3) (w 4) := by
    have h := minTri_le_234 w
    rw [abs_of_nonneg c234] at h
    linarith
  have hb := ear_min_bound (w 0) (w 1) (w 2) (w 3) (w 4)
    s014 s024 s013 k1 k2 k3 k4
  have harea : sig (w 0) (w 1) (w 2) + sig (w 0) (w 2) (w 3) +
      sig (w 0) (w 3) (w 4) = 2 := by
    simpa only [penArea] using hpen
  have hupper : sig (w 0) (w 1) (w 4) ≤ 2 * tau := by
    rw [harea] at hb
    linarith
  have hlower : 2 * tau ≤ sig (w 0) (w 1) (w 4) := by
    have h := minTri_le_014 w
    rw [abs_of_pos s014, hmin] at h
    exact h
  have hD2 : sig (w 0) (w 1) (w 4) = 2 * tau :=
    le_antisymm hupper hlower
  have heq : sig (w 0) (w 1) (w 4) =
      tau * (sig (w 0) (w 1) (w 2) + sig (w 0) (w 2) (w 3) +
        sig (w 0) (w 3) (w 4)) := by
    rw [hD2, harea]
    ring
  obtain ⟨e012, e034, e024, e013⟩ :=
    ear_min_bound_eq (w 0) (w 1) (w 2) (w 3) (w 4)
      s014 s024 s013 k1 k2 k3 k4 heq
  exact ⟨hD2, e012.trans hD2, e034.trans hD2,
    e024.trans (congrArg (phi * ·) hD2),
    e013.trans (congrArg (phi * ·) hD2)⟩

theorem five_pent_structure (w : Fin 5 → ℝ × ℝ) (hc : ConvexPos w)
    (hpen : penArea w = 2) (hmin : minTri w = 2 * tau) :
    ∃ r : Fin 5 → Fin 5, Function.Injective r ∧
      sig (w (r 0)) (w (r 1)) (w (r 4)) = 2 * tau ∧
      sig (w (r 0)) (w (r 1)) (w (r 2)) = 2 * tau ∧
      sig (w (r 0)) (w (r 3)) (w (r 4)) = 2 * tau ∧
      sig (w (r 0)) (w (r 2)) (w (r 4)) = phi * (2 * tau) ∧
      sig (w (r 0)) (w (r 1)) (w (r 3)) = phi * (2 * tau) := by
  let Good (r : Fin 5 → Fin 5) : Prop := Function.Injective r ∧
    sig (w (r 0)) (w (r 1)) (w (r 4)) = 2 * tau ∧
    sig (w (r 0)) (w (r 1)) (w (r 2)) = 2 * tau ∧
    sig (w (r 0)) (w (r 3)) (w (r 4)) = 2 * tau ∧
    sig (w (r 0)) (w (r 2)) (w (r 4)) = phi * (2 * tau) ∧
    sig (w (r 0)) (w (r 1)) (w (r 3)) = phi * (2 * tau)
  change ∃ r, Good r
  have case0 : sig (w 0) (w 1) (w 4) ≤ sig (w 0) (w 1) (w 2) →
      sig (w 0) (w 1) (w 4) ≤ sig (w 1) (w 2) (w 3) →
      sig (w 0) (w 1) (w 4) ≤ sig (w 2) (w 3) (w 4) →
      sig (w 0) (w 1) (w 4) ≤ sig (w 0) (w 3) (w 4) →
      ∃ r, Good r := by
    intro k1 k2 k3 k4
    obtain ⟨e1, e2, e3, e4, e5⟩ := five_aligned w hc hpen hmin k1 k2 k3 k4
    refine ⟨rot0, rot0_injective, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [rot0] using e1
    · simpa [rot0] using e2
    · simpa [rot0] using e3
    · simpa [rot0] using e4
    · simpa [rot0] using e5
  have case1 : sig (w 0) (w 1) (w 2) ≤ sig (w 1) (w 2) (w 3) →
      sig (w 0) (w 1) (w 2) ≤ sig (w 2) (w 3) (w 4) →
      sig (w 0) (w 1) (w 2) ≤ sig (w 0) (w 3) (w 4) →
      sig (w 0) (w 1) (w 2) ≤ sig (w 0) (w 1) (w 4) →
      ∃ r, Good r := by
    intro k1 k2 k3 k4
    have r0 : sig (w 1) (w 2) (w 0) = sig (w 0) (w 1) (w 2) := by
      simp only [sig]
      ring
    have r2 : sig (w 3) (w 4) (w 0) = sig (w 0) (w 3) (w 4) := by
      simp only [sig]
      ring
    have r3 : sig (w 1) (w 4) (w 0) = sig (w 0) (w 1) (w 4) := by
      simp only [sig]
      ring
    obtain ⟨e1, e2, e3, e4, e5⟩ := five_aligned (w ∘ rot1)
      (convexPos_rot1 w hc) ((penArea_rot1 w).trans hpen)
      ((minTri_rot1 w).trans hmin)
      (by
        change sig (w 1) (w 2) (w 0) ≤ sig (w 1) (w 2) (w 3)
        rw [r0]
        exact k1)
      (by
        change sig (w 1) (w 2) (w 0) ≤ sig (w 2) (w 3) (w 4)
        rw [r0]
        exact k2)
      (by
        change sig (w 1) (w 2) (w 0) ≤ sig (w 3) (w 4) (w 0)
        rw [r0, r2]
        exact k3)
      (by
        change sig (w 1) (w 2) (w 0) ≤ sig (w 1) (w 4) (w 0)
        rw [r0, r3]
        exact k4)
    exact ⟨rot1, rot1_injective, e1, e2, e3, e4, e5⟩
  have case2 : sig (w 1) (w 2) (w 3) ≤ sig (w 2) (w 3) (w 4) →
      sig (w 1) (w 2) (w 3) ≤ sig (w 0) (w 3) (w 4) →
      sig (w 1) (w 2) (w 3) ≤ sig (w 0) (w 1) (w 4) →
      sig (w 1) (w 2) (w 3) ≤ sig (w 0) (w 1) (w 2) →
      ∃ r, Good r := by
    intro k1 k2 k3 k4
    have r0 : sig (w 2) (w 3) (w 1) = sig (w 1) (w 2) (w 3) := by
      simp only [sig]
      ring
    have r3 : sig (w 3) (w 4) (w 0) = sig (w 0) (w 3) (w 4) := by
      simp only [sig]
      ring
    have r4 : sig (w 4) (w 0) (w 1) = sig (w 0) (w 1) (w 4) := by
      simp only [sig]
      ring
    have r5 : sig (w 2) (w 0) (w 1) = sig (w 0) (w 1) (w 2) := by
      simp only [sig]
      ring
    obtain ⟨e1, e2, e3, e4, e5⟩ := five_aligned (w ∘ rot2)
      (convexPos_rot2 w hc) ((penArea_rot2 w).trans hpen)
      ((minTri_rot2 w).trans hmin)
      (by
        change sig (w 2) (w 3) (w 1) ≤ sig (w 2) (w 3) (w 4)
        rw [r0]
        exact k1)
      (by
        change sig (w 2) (w 3) (w 1) ≤ sig (w 3) (w 4) (w 0)
        rw [r0, r3]
        exact k2)
      (by
        change sig (w 2) (w 3) (w 1) ≤ sig (w 4) (w 0) (w 1)
        rw [r0, r4]
        exact k3)
      (by
        change sig (w 2) (w 3) (w 1) ≤ sig (w 2) (w 0) (w 1)
        rw [r0, r5]
        exact k4)
    exact ⟨rot2, rot2_injective, e1, e2, e3, e4, e5⟩
  have case3 : sig (w 2) (w 3) (w 4) ≤ sig (w 0) (w 3) (w 4) →
      sig (w 2) (w 3) (w 4) ≤ sig (w 0) (w 1) (w 4) →
      sig (w 2) (w 3) (w 4) ≤ sig (w 0) (w 1) (w 2) →
      sig (w 2) (w 3) (w 4) ≤ sig (w 1) (w 2) (w 3) →
      ∃ r, Good r := by
    intro k1 k2 k3 k4
    have r0 : sig (w 3) (w 4) (w 2) = sig (w 2) (w 3) (w 4) := by
      simp only [sig]
      ring
    have r3 : sig (w 3) (w 4) (w 0) = sig (w 0) (w 3) (w 4) := by
      simp only [sig]
      ring
    have r4 : sig (w 4) (w 0) (w 1) = sig (w 0) (w 1) (w 4) := by
      simp only [sig]
      ring
    have r5 : sig (w 3) (w 1) (w 2) = sig (w 1) (w 2) (w 3) := by
      simp only [sig]
      ring
    obtain ⟨e1, e2, e3, e4, e5⟩ := five_aligned (w ∘ rot3)
      (convexPos_rot3 w hc) ((penArea_rot3 w).trans hpen)
      ((minTri_rot3 w).trans hmin)
      (by
        change sig (w 3) (w 4) (w 2) ≤ sig (w 3) (w 4) (w 0)
        rw [r0, r3]
        exact k1)
      (by
        change sig (w 3) (w 4) (w 2) ≤ sig (w 4) (w 0) (w 1)
        rw [r0, r4]
        exact k2)
      (by
        change sig (w 3) (w 4) (w 2) ≤ sig (w 0) (w 1) (w 2)
        rw [r0]
        exact k3)
      (by
        change sig (w 3) (w 4) (w 2) ≤ sig (w 3) (w 1) (w 2)
        rw [r0, r5]
        exact k4)
    exact ⟨rot3, rot3_injective, e1, e2, e3, e4, e5⟩
  have case4 : sig (w 0) (w 3) (w 4) ≤ sig (w 0) (w 1) (w 4) →
      sig (w 0) (w 3) (w 4) ≤ sig (w 0) (w 1) (w 2) →
      sig (w 0) (w 3) (w 4) ≤ sig (w 1) (w 2) (w 3) →
      sig (w 0) (w 3) (w 4) ≤ sig (w 2) (w 3) (w 4) →
      ∃ r, Good r := by
    intro k1 k2 k3 k4
    have r0 : sig (w 4) (w 0) (w 3) = sig (w 0) (w 3) (w 4) := by
      simp only [sig]
      ring
    have r3 : sig (w 4) (w 0) (w 1) = sig (w 0) (w 1) (w 4) := by
      simp only [sig]
      ring
    have r4 : sig (w 4) (w 2) (w 3) = sig (w 2) (w 3) (w 4) := by
      simp only [sig]
      ring
    obtain ⟨e1, e2, e3, e4, e5⟩ := five_aligned (w ∘ rot4)
      (convexPos_rot4 w hc) ((penArea_rot4 w).trans hpen)
      ((minTri_rot4 w).trans hmin)
      (by
        change sig (w 4) (w 0) (w 3) ≤ sig (w 4) (w 0) (w 1)
        rw [r0, r3]
        exact k1)
      (by
        change sig (w 4) (w 0) (w 3) ≤ sig (w 0) (w 1) (w 2)
        rw [r0]
        exact k2)
      (by
        change sig (w 4) (w 0) (w 3) ≤ sig (w 1) (w 2) (w 3)
        rw [r0]
        exact k3)
      (by
        change sig (w 4) (w 0) (w 3) ≤ sig (w 4) (w 2) (w 3)
        rw [r0, r4]
        exact k4)
    exact ⟨rot4, rot4_injective, e1, e2, e3, e4, e5⟩
  rcases le_total (sig (w 0) (w 1) (w 4)) (sig (w 0) (w 1) (w 2)) with h1 | h1
  · rcases le_total (sig (w 0) (w 1) (w 4)) (sig (w 1) (w 2) (w 3)) with h2 | h2
    · rcases le_total (sig (w 0) (w 1) (w 4)) (sig (w 2) (w 3) (w 4)) with h3 | h3
      · rcases le_total (sig (w 0) (w 1) (w 4)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case0 h1 h2 h3 h4
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total (sig (w 2) (w 3) (w 4)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
    · rcases le_total (sig (w 1) (w 2) (w 3)) (sig (w 2) (w 3) (w 4)) with h3 | h3
      · rcases le_total (sig (w 1) (w 2) (w 3)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case2 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total (sig (w 2) (w 3) (w 4)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
  · rcases le_total (sig (w 0) (w 1) (w 2)) (sig (w 1) (w 2) (w 3)) with h2 | h2
    · rcases le_total (sig (w 0) (w 1) (w 2)) (sig (w 2) (w 3) (w 4)) with h3 | h3
      · rcases le_total (sig (w 0) (w 1) (w 2)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case1 h2 h3 h4 h1
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total (sig (w 2) (w 3) (w 4)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
    · rcases le_total (sig (w 1) (w 2) (w 3)) (sig (w 2) (w 3) (w 4)) with h3 | h3
      · rcases le_total (sig (w 1) (w 2) (w 3)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case2 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total (sig (w 2) (w 3) (w 4)) (sig (w 0) (w 3) (w 4)) with h4 | h4
        · exact case3 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact case4 (by linarith) (by linarith) (by linarith) (by linarith)

theorem five_optimal_structure (v : Fin 5 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hmin : minTri v = 2 * tau) :
    ∃ g : Fin 5 → Fin 5, Function.Injective g ∧
      sig (v (g 0)) (v (g 1)) (v (g 4)) = 2 * tau ∧
      sig (v (g 0)) (v (g 1)) (v (g 2)) = 2 * tau ∧
      sig (v (g 0)) (v (g 3)) (v (g 4)) = 2 * tau ∧
      sig (v (g 0)) (v (g 2)) (v (g 4)) = phi * (2 * tau) ∧
      sig (v (g 0)) (v (g 1)) (v (g 3)) = phi * (2 * tau) := by
  have hpos : 0 < minTri v := by
    rw [hmin]
    nlinarith [tau_pos]
  obtain ⟨H, hH⟩ := exists_hullArea v
  have hHvol := isHullArea_eq_volume v H hH hpos
  rw [hvol] at hHvol
  have hone : H = 1 := ENNReal.ofReal_eq_one.mp hHvol
  obtain ⟨f, hf, hc, hpen⟩ := hull_pent_of_optimal v H hH hone hmin
  let fe : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hcomp : v ∘ f = v ∘ fe := by
    funext i
    rfl
  have hminf : minTri (v ∘ f) = 2 * tau := by
    calc
      minTri (v ∘ f) = minTri (v ∘ fe) := congrArg minTri hcomp
      _ = minTri v := minTri_comp_equiv v fe
      _ = 2 * tau := hmin
  obtain ⟨r, hr, e1, e2, e3, e4, e5⟩ :=
    five_pent_structure (v ∘ f) hc hpen hminf
  refine ⟨f ∘ r, hf.comp hr, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using e1
  · simpa only [Function.comp_apply] using e2
  · simpa only [Function.comp_apply] using e3
  · simpa only [Function.comp_apply] using e4
  · simpa only [Function.comp_apply] using e5

end Heilbronn5
