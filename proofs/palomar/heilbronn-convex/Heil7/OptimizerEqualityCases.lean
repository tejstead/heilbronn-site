import Heil7.OptimizerEqualityRouting
import Heil7.Hull3Strict
import Heil7.Hull45StrictRoute
import Heil7.Hull7ContinuantStrictRoute

/-!
# Concrete non-six equality exclusions

All four non-six hull sizes are excluded by strict proved routes.  The generic
constructor below also keeps the hull-three input explicit, so the relatively
large equality-aware counting argument remains replaceable without changing
the optimizer-classification interface.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Equality cannot occur when all four non-hull points are strictly inside a
triangular hull. -/
def HullThreeStrictBound : Prop :=
  ∀ (v : Configuration7), HullCCW v 3 →
    (∀ p : Fin 7, 3 ≤ (p : ℕ) → InHullN v 3 p) →
    0 < minTri v → 9 * minTri v < fanArea v 3

/-- The complete non-six strict packet, conditional only on the equality-aware
strengthening of the hull-three counting argument. -/
theorem strictNonSixHullCaseBounds_of_h3
    (h3 : HullThreeStrictBound) : StrictNonSixHullCaseBounds where
  h3 v hm hccw hin := h3 v hccw hin hm
  h4 v hm hccw hin := hull45_strict_fields.1 v hccw hin hm
  h5 v hm hccw hin := hull45_strict_fields.2 v hccw hin hm
  h7 v hm hccw := hullSeven_continuant_strict v hccw hm

/-- The hull-three input is now supplied by the equality-aware refinement of
the nine-cell counting proof. -/
theorem hullThreeStrictBound_proved : HullThreeStrictBound :=
  fun v hccw hin _ => hullThree_counting_strict v hccw hin

/-- All four non-six hull sizes are pointwise strict. -/
theorem strictNonSixHullCaseBounds_proved : StrictNonSixHullCaseBounds :=
  strictNonSixHullCaseBounds_of_h3 hullThreeStrictBound_proved

/-- With the single hull-three strict input, exact positive-area equality is
already forced into the canonical six-hull/one-interior-point packet. -/
theorem areaEquality_relabel_hullSix_of_h3
    (h3 : HullThreeStrictBound) (v : Configuration7)
    (hm : 0 < minTri v)
    (heq : 9 * minTri v = HullBridge.doubledHullArea v) :
    ∃ σ : Equiv.Perm (Fin 7),
      GaugeEquivalent v (v ∘ σ) ∧ HullSixEqualityData (v ∘ σ) :=
  areaEquality_relabel_hullSix (strictNonSixHullCaseBounds_of_h3 h3)
    v hm heq

/-- Unconditional first-stage optimizer classification: every positive-area
equality configuration is gauge-equivalent, by relabeling alone, to a
six-hull configuration carrying exact bound equality. -/
theorem areaEquality_relabel_hullSix_proved
    (v : Configuration7) (hm : 0 < minTri v)
    (heq : 9 * minTri v = HullBridge.doubledHullArea v) :
    ∃ σ : Equiv.Perm (Fin 7),
      GaugeEquivalent v (v ∘ σ) ∧ HullSixEqualityData (v ∘ σ) :=
  areaEquality_relabel_hullSix strictNonSixHullCaseBounds_proved v hm heq

end HeilbronnChallenge.N7Upper
