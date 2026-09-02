import Heilbronn8.Survivors.Join.HullSixCompletedCompactClosure
import Heilbronn8.Survivors.Join.HullSixDirectGeometricExclusion

/-!
# Completed raw hull-six bound

Source-only integration module.  This file is intended to be installed beside
`HullSixCompletedCompactClosure.lean` after the rational-cut version of
`HullSixVariationExclusion.lean` has been installed.

The compact closure theorem still exposes the two off-cycle labels because
they are part of the residual.  The public raw endpoint should not: a six-label
injective cycle in `Fin 8` has exactly two distinct omitted labels, and the
existing selector in `HullSixDirectGeometricExclusion` supplies them.

The primary theorem below is optimizer-independent.  The final theorem is only
the compatibility adapter for callers that still formulate their goal with
`Beats doubledHullArea v8`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The completed compact frontier proves the raw rational hull-six bound.
The two off-cycle labels are selected internally. -/
theorem twentyFive_minTri_le_twice_hullArea_of_hullCycleSix_completed
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6) :
    25 * minTri v <= 2 * doubledHullArea v := by
  have hc : Function.Injective (d.castGet h6) :=
    HullCycleData.castGet_injective d h6 hcycle.nodup
  obtain ⟨p, q, hpq, hpOutside, hqOutside⟩ :=
    exists_two_offCycle_finSix_finEight (d.castGet h6) hc
  exact
    twentyFive_minTri_le_twice_hullArea_of_hullCycleSix_of_compactClosed
      hullSixCompactCrossChordClosed_of_completedDirectFrontiers
      hcycle h6 p q hpq hpOutside hqOutside

/-- Compatibility only: the raw rational theorem immediately excludes an
optimizer beat because `2 / 25 < v8`. -/
theorem not_Beats_v8_of_hullCycleSix_completed
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  have hbound :=
    twentyFive_minTri_le_twice_hullArea_of_hullCycleSix_completed hcycle h6
  have hcut :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    lt_trans
      (mul_lt_mul_of_pos_right two_div_twentyFive_lt_v8 hbeat.1)
      hbeat.2
  nlinarith only [hbound, hcut]

end Heilbronn8
