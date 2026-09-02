/-
Permutation robustness: the minimum triangle bounds every ordered distinct
triple of the five points. Machine-generated case analysis.
-/
import Heil5.Defs

namespace Heilbronn5

lemma minTri_le_any (v : Fin 5 → ℝ × ℝ) (i j k : Fin 5)
    (h1 : i ≠ j) (h2 : i ≠ k) (h3 : j ≠ k) :
    minTri v ≤ |sig (v i) (v j) (v k)| := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact minTri_le_012 v
  · exact minTri_le_013 v
  · exact minTri_le_014 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 0) (v 2) (v 1)|
    rw [show sig (v 0) (v 2) (v 1) = -sig (v 0) (v 1) (v 2) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_012 v
  · exact absurd rfl h3
  · exact minTri_le_023 v
  · exact minTri_le_024 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 0) (v 3) (v 1)|
    rw [show sig (v 0) (v 3) (v 1) = -sig (v 0) (v 1) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_013 v
  · show minTri v ≤ |sig (v 0) (v 3) (v 2)|
    rw [show sig (v 0) (v 3) (v 2) = -sig (v 0) (v 2) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_023 v
  · exact absurd rfl h3
  · exact minTri_le_034 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 0) (v 4) (v 1)|
    rw [show sig (v 0) (v 4) (v 1) = -sig (v 0) (v 1) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_014 v
  · show minTri v ≤ |sig (v 0) (v 4) (v 2)|
    rw [show sig (v 0) (v 4) (v 2) = -sig (v 0) (v 2) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_024 v
  · show minTri v ≤ |sig (v 0) (v 4) (v 3)|
    rw [show sig (v 0) (v 4) (v 3) = -sig (v 0) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_034 v
  · exact absurd rfl h3
  · exact absurd rfl h3
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 1) (v 0) (v 2)|
    rw [show sig (v 1) (v 0) (v 2) = -sig (v 0) (v 1) (v 2) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_012 v
  · show minTri v ≤ |sig (v 1) (v 0) (v 3)|
    rw [show sig (v 1) (v 0) (v 3) = -sig (v 0) (v 1) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_013 v
  · show minTri v ≤ |sig (v 1) (v 0) (v 4)|
    rw [show sig (v 1) (v 0) (v 4) = -sig (v 0) (v 1) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_014 v
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · show minTri v ≤ |sig (v 1) (v 2) (v 0)|
    rw [show sig (v 1) (v 2) (v 0) = sig (v 0) (v 1) (v 2) from by simp only [sig]; ring]
    exact minTri_le_012 v
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact minTri_le_123 v
  · exact minTri_le_124 v
  · show minTri v ≤ |sig (v 1) (v 3) (v 0)|
    rw [show sig (v 1) (v 3) (v 0) = sig (v 0) (v 1) (v 3) from by simp only [sig]; ring]
    exact minTri_le_013 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 1) (v 3) (v 2)|
    rw [show sig (v 1) (v 3) (v 2) = -sig (v 1) (v 2) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_123 v
  · exact absurd rfl h3
  · exact minTri_le_134 v
  · show minTri v ≤ |sig (v 1) (v 4) (v 0)|
    rw [show sig (v 1) (v 4) (v 0) = sig (v 0) (v 1) (v 4) from by simp only [sig]; ring]
    exact minTri_le_014 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 1) (v 4) (v 2)|
    rw [show sig (v 1) (v 4) (v 2) = -sig (v 1) (v 2) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_124 v
  · show minTri v ≤ |sig (v 1) (v 4) (v 3)|
    rw [show sig (v 1) (v 4) (v 3) = -sig (v 1) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_134 v
  · exact absurd rfl h3
  · exact absurd rfl h3
  · show minTri v ≤ |sig (v 2) (v 0) (v 1)|
    rw [show sig (v 2) (v 0) (v 1) = sig (v 0) (v 1) (v 2) from by simp only [sig]; ring]
    exact minTri_le_012 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 2) (v 0) (v 3)|
    rw [show sig (v 2) (v 0) (v 3) = -sig (v 0) (v 2) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_023 v
  · show minTri v ≤ |sig (v 2) (v 0) (v 4)|
    rw [show sig (v 2) (v 0) (v 4) = -sig (v 0) (v 2) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_024 v
  · show minTri v ≤ |sig (v 2) (v 1) (v 0)|
    rw [show sig (v 2) (v 1) (v 0) = -sig (v 0) (v 1) (v 2) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_012 v
  · exact absurd rfl h3
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 2) (v 1) (v 3)|
    rw [show sig (v 2) (v 1) (v 3) = -sig (v 1) (v 2) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_123 v
  · show minTri v ≤ |sig (v 2) (v 1) (v 4)|
    rw [show sig (v 2) (v 1) (v 4) = -sig (v 1) (v 2) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_124 v
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · show minTri v ≤ |sig (v 2) (v 3) (v 0)|
    rw [show sig (v 2) (v 3) (v 0) = sig (v 0) (v 2) (v 3) from by simp only [sig]; ring]
    exact minTri_le_023 v
  · show minTri v ≤ |sig (v 2) (v 3) (v 1)|
    rw [show sig (v 2) (v 3) (v 1) = sig (v 1) (v 2) (v 3) from by simp only [sig]; ring]
    exact minTri_le_123 v
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact minTri_le_234 v
  · show minTri v ≤ |sig (v 2) (v 4) (v 0)|
    rw [show sig (v 2) (v 4) (v 0) = sig (v 0) (v 2) (v 4) from by simp only [sig]; ring]
    exact minTri_le_024 v
  · show minTri v ≤ |sig (v 2) (v 4) (v 1)|
    rw [show sig (v 2) (v 4) (v 1) = sig (v 1) (v 2) (v 4) from by simp only [sig]; ring]
    exact minTri_le_124 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 2) (v 4) (v 3)|
    rw [show sig (v 2) (v 4) (v 3) = -sig (v 2) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_234 v
  · exact absurd rfl h3
  · exact absurd rfl h3
  · show minTri v ≤ |sig (v 3) (v 0) (v 1)|
    rw [show sig (v 3) (v 0) (v 1) = sig (v 0) (v 1) (v 3) from by simp only [sig]; ring]
    exact minTri_le_013 v
  · show minTri v ≤ |sig (v 3) (v 0) (v 2)|
    rw [show sig (v 3) (v 0) (v 2) = sig (v 0) (v 2) (v 3) from by simp only [sig]; ring]
    exact minTri_le_023 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 3) (v 0) (v 4)|
    rw [show sig (v 3) (v 0) (v 4) = -sig (v 0) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_034 v
  · show minTri v ≤ |sig (v 3) (v 1) (v 0)|
    rw [show sig (v 3) (v 1) (v 0) = -sig (v 0) (v 1) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_013 v
  · exact absurd rfl h3
  · show minTri v ≤ |sig (v 3) (v 1) (v 2)|
    rw [show sig (v 3) (v 1) (v 2) = sig (v 1) (v 2) (v 3) from by simp only [sig]; ring]
    exact minTri_le_123 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 3) (v 1) (v 4)|
    rw [show sig (v 3) (v 1) (v 4) = -sig (v 1) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_134 v
  · show minTri v ≤ |sig (v 3) (v 2) (v 0)|
    rw [show sig (v 3) (v 2) (v 0) = -sig (v 0) (v 2) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_023 v
  · show minTri v ≤ |sig (v 3) (v 2) (v 1)|
    rw [show sig (v 3) (v 2) (v 1) = -sig (v 1) (v 2) (v 3) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_123 v
  · exact absurd rfl h3
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 3) (v 2) (v 4)|
    rw [show sig (v 3) (v 2) (v 4) = -sig (v 2) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_234 v
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · show minTri v ≤ |sig (v 3) (v 4) (v 0)|
    rw [show sig (v 3) (v 4) (v 0) = sig (v 0) (v 3) (v 4) from by simp only [sig]; ring]
    exact minTri_le_034 v
  · show minTri v ≤ |sig (v 3) (v 4) (v 1)|
    rw [show sig (v 3) (v 4) (v 1) = sig (v 1) (v 3) (v 4) from by simp only [sig]; ring]
    exact minTri_le_134 v
  · show minTri v ≤ |sig (v 3) (v 4) (v 2)|
    rw [show sig (v 3) (v 4) (v 2) = sig (v 2) (v 3) (v 4) from by simp only [sig]; ring]
    exact minTri_le_234 v
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact absurd rfl h3
  · show minTri v ≤ |sig (v 4) (v 0) (v 1)|
    rw [show sig (v 4) (v 0) (v 1) = sig (v 0) (v 1) (v 4) from by simp only [sig]; ring]
    exact minTri_le_014 v
  · show minTri v ≤ |sig (v 4) (v 0) (v 2)|
    rw [show sig (v 4) (v 0) (v 2) = sig (v 0) (v 2) (v 4) from by simp only [sig]; ring]
    exact minTri_le_024 v
  · show minTri v ≤ |sig (v 4) (v 0) (v 3)|
    rw [show sig (v 4) (v 0) (v 3) = sig (v 0) (v 3) (v 4) from by simp only [sig]; ring]
    exact minTri_le_034 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 4) (v 1) (v 0)|
    rw [show sig (v 4) (v 1) (v 0) = -sig (v 0) (v 1) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_014 v
  · exact absurd rfl h3
  · show minTri v ≤ |sig (v 4) (v 1) (v 2)|
    rw [show sig (v 4) (v 1) (v 2) = sig (v 1) (v 2) (v 4) from by simp only [sig]; ring]
    exact minTri_le_124 v
  · show minTri v ≤ |sig (v 4) (v 1) (v 3)|
    rw [show sig (v 4) (v 1) (v 3) = sig (v 1) (v 3) (v 4) from by simp only [sig]; ring]
    exact minTri_le_134 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 4) (v 2) (v 0)|
    rw [show sig (v 4) (v 2) (v 0) = -sig (v 0) (v 2) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_024 v
  · show minTri v ≤ |sig (v 4) (v 2) (v 1)|
    rw [show sig (v 4) (v 2) (v 1) = -sig (v 1) (v 2) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_124 v
  · exact absurd rfl h3
  · show minTri v ≤ |sig (v 4) (v 2) (v 3)|
    rw [show sig (v 4) (v 2) (v 3) = sig (v 2) (v 3) (v 4) from by simp only [sig]; ring]
    exact minTri_le_234 v
  · exact absurd rfl h2
  · show minTri v ≤ |sig (v 4) (v 3) (v 0)|
    rw [show sig (v 4) (v 3) (v 0) = -sig (v 0) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_034 v
  · show minTri v ≤ |sig (v 4) (v 3) (v 1)|
    rw [show sig (v 4) (v 3) (v 1) = -sig (v 1) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_134 v
  · show minTri v ≤ |sig (v 4) (v 3) (v 2)|
    rw [show sig (v 4) (v 3) (v 2) = -sig (v 2) (v 3) (v 4) from by simp only [sig]; ring, abs_neg]
    exact minTri_le_234 v
  · exact absurd rfl h3
  · exact absurd rfl h2
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1
  · exact absurd rfl h1

end Heilbronn5
