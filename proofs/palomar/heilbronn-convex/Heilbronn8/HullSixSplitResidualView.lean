import Heilbronn8.HullSixOneFiveRotation

/-!
# A shared oriented view for the remaining hull-six sign blocks

The `1 + 5` rotation adapter already performs the only delicate Boolean
orientation transport needed after extracting a `FinSixLineSignBlock`.
This file packages the same transport once for the two remaining branches.
It deliberately stops before choosing coordinates or a Ferrers table: a
`2 + 4` or `3 + 3` scalar adapter can consume this proposition without
reimplementing the `flip = true` case.

The two explicit exterior points are retained together with a proof that
they are either `(p,q)` or `(q,p)`.  Consequently a downstream adapter can
transport the cached cross-chord facts of the compact residual, while the
`HullSixOrientedView` supplies the boundary and fan-sum facts in the selected
orientation.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The selected orientation is one of the two orientations cached by the
compact residual. -/
def HullSixIsOrientedPair (p q P Q : Fin 8) : Prop :=
  (P = p ∧ Q = q) ∨ (P = q ∧ Q = p)

/-- An oriented non-`1 + 5` sign block at a specified cut.  Positions
`0,...,last` have positive line level and the remaining positions have
negative line level. -/
def HullSixSplitResidualViewAt
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (last : Fin 3) : Prop :=
  ∃ P Q : Fin 8,
    HullSixIsOrientedPair p q P Q ∧
    HullSixOrientedView v cycle P Q ∧
    ∃ rotation : Fin 6,
      (∀ i : Fin 6, i.val ≤ last.val →
        0 < sig (v P) (v Q) (v (cycle (rotation + i)))) ∧
      (∀ i : Fin 6, last.val < i.val →
        sig (v P) (v Q) (v (cycle (rotation + i))) < 0)

/-- Shared residual view for the branches left after `1 + 5`: its cut is
either `last = 1` (`2 + 4`) or `last = 2` (`3 + 3`). -/
def HullSixNonOneSplitResidualView
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) : Prop :=
  ∃ last : Fin 3, last ≠ 0 ∧ HullSixSplitResidualViewAt R last

namespace HullSixCompactCrossChordResidual

/-- Extract the common oriented view without duplicating the rotation and
line-orientation logic in the `2 + 4` and `3 + 3` adapters. -/
theorem nonOneSplitResidualView
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    HullSixNonOneSplitResidualView R := by
  obtain ⟨rotation, flip, last, hlast, hpositive, hnegative⟩ :=
    R.lineSignBlock_witness_with_last_ne_zero
  refine ⟨last, hlast, ?_⟩
  cases flip with
  | false =>
      refine ⟨p, q, Or.inl ⟨rfl, rfl⟩, R.forwardOrientedView,
        rotation, ?_, ?_⟩
      · intro i hi
        simpa [orientedFinSixLevel] using hpositive i hi
      · intro i hi
        simpa [orientedFinSixLevel] using hnegative i hi
  | true =>
      refine ⟨q, p, Or.inr ⟨rfl, rfl⟩, R.swappedOrientedView,
        rotation, ?_, ?_⟩
      · intro i hi
        have h := hpositive i hi
        rw [sig_swap_first]
        simpa [orientedFinSixLevel] using h
      · intro i hi
        have h := hnegative i hi
        rw [sig_swap_first]
        simpa [orientedFinSixLevel] using h

/-- There are exactly two cuts left.  This is the clean branching point for
the normalized `2 + 4` and `3 + 3` scalar adapters. -/
theorem twoFour_or_threeThreeResidualView
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    HullSixSplitResidualViewAt R 1 ∨
      HullSixSplitResidualViewAt R 2 := by
  obtain ⟨last, hlast, hview⟩ := R.nonOneSplitResidualView
  fin_cases last
  · exact False.elim (hlast rfl)
  · exact Or.inl hview
  · exact Or.inr hview

end HullSixCompactCrossChordResidual

end Heilbronn8
