import Heilbronn8.Survivors.Join.HullSixFerrersPropagation

/-!
# Uniqueness of the first cuts of a q-blind frontier

The positive/negative sign split in each row determines its first cut.
The second cuts and their stronger negative bounds play no role.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Positive q-blind frontiers on the same array determine the first cuts,
provided both cut functions stay within the column range. -/
theorem qBlindFrontierHolds_p_unique
    {r s : ℕ} {p p' q q' : Fin r → ℕ} {m : ℝ}
    {X : Fin r → Fin s → ℝ}
    (hm : 0 < m)
    (hp : ∀ i, p i ≤ s) (hp' : ∀ i, p' i ≤ s)
    (h : HullSixQBlindFrontierHolds p q m X)
    (h' : HullSixQBlindFrontierHolds p' q' m X) :
    p = p' := by
  rcases h with ⟨hLeft, hNeg, _hStrong⟩
  rcases h' with ⟨hLeft', hNeg', _hStrong'⟩
  funext i
  apply le_antisymm
  · by_contra hnot
    have hlt : p' i < p i := Nat.lt_of_not_ge hnot
    let j : Fin s := ⟨p' i, lt_of_lt_of_le hlt (hp i)⟩
    have hpos : m ≤ X i j := hLeft i j (by simpa [j] using hlt)
    have hneg : X i j ≤ -m := hNeg' i j (by simp [j])
    linarith
  · by_contra hnot
    have hlt : p i < p' i := Nat.lt_of_not_ge hnot
    let j : Fin s := ⟨p i, lt_of_lt_of_le hlt (hp' i)⟩
    have hpos : m ≤ X i j := hLeft' i j (by simpa [j] using hlt)
    have hneg : X i j ≤ -m := hNeg i j (by simp [j])
    linarith

end Heilbronn8
