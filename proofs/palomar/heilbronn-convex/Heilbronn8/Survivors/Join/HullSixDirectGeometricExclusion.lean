import Heilbronn8.GeometricHullExclusionCore
import Heilbronn8.HullSixSplitResidualView
import Heilbronn8.OrderDensity

/-!
# Direct geometric hull-six endpoint

This is the geometry-only final spine for hull size six.  It does not mention
retained records, generated routes, classifier registries, or survivor
artifacts.

The existing line-sign-block theorem closes `1 + 5` before exposing the two
remaining oriented views.  Consequently the only inputs below are honest
closures of the oriented `2 + 4` and `3 + 3` packets.  Their implementations
are intended to be the five-packet `2 + 4` dispatch and the two-top finite
bridge for `3 + 3`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Geometry-facing closure contract for every oriented `2 + 4` view. -/
def HullSixTwoFourOrientedClosed : Prop :=
  ∀ {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q),
      HullSixSplitResidualViewAt R 1 → False

/-- Geometry-facing closure contract for every oriented `3 + 3` view. -/
def HullSixThreeThreeOrientedClosed : Prop :=
  ∀ {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q),
      HullSixSplitResidualViewAt R 2 → False

/-- The two oriented packet closures finish every compact cross-chord
residual.  The `1 + 5` case has already been eliminated by
`twoFour_or_threeThreeResidualView`. -/
theorem hullSixCompactCrossChordClosed_of_orientedPackets
    (hTwoFour : HullSixTwoFourOrientedClosed)
    (hThreeThree : HullSixThreeThreeOrientedClosed) :
    HullSixCompactCrossChordClosed := by
  intro v cycle p q R
  rcases R.twoFour_or_threeThreeResidualView with h24 | h33
  · exact hTwoFour R h24
  · exact hThreeThree R h33

/-! ## Selecting the two off-cycle labels -/

/-- An injective six-label cycle in `Fin 8` omits two distinct labels. -/
theorem exists_two_offCycle_finSix_finEight
    (c : Fin 6 → Fin 8) (hc : Function.Injective c) :
    ∃ p q : Fin 8, p ≠ q ∧ p ∉ Set.range c ∧ q ∉ Set.range c := by
  have oneOff (d : Fin 7 → Fin 8) :
      ∃ x : Fin 8, x ∉ Set.range d := by
    by_contra hnone
    push_neg at hnone
    have hsurjective : Function.Surjective d := by
      intro x
      exact hnone x
    have hcard := Fintype.card_le_of_surjective d hsurjective
    norm_num at hcard
  let c0 : Fin 7 → Fin 8 := Fin.lastCases (c 0) c
  obtain ⟨p, hp0⟩ := oneOff c0
  have hp : p ∉ Set.range c := by
    rintro ⟨i, rfl⟩
    exact hp0 ⟨Fin.castSucc i, by simp [c0]⟩
  let cp : Fin 7 → Fin 8 := Fin.lastCases p c
  obtain ⟨q, hqp⟩ := oneOff cp
  have hq : q ∉ Set.range c := by
    rintro ⟨i, rfl⟩
    exact hqp ⟨Fin.castSucc i, by simp [cp]⟩
  have hpq : p ≠ q := by
    intro heq
    apply hqp
    refine ⟨Fin.last 6, ?_⟩
    change p = q
    exact heq
  exact ⟨p, q, hpq, hp, hq⟩

/-! ## The direct geometric theorem -/

/-- Oriented `2 + 4` and `3 + 3` packet closures give the actual strict
geometric hull-size-six exclusion.  Reference-domain and strict-order data
are not used: all metric information comes from the proof-relevant hull
cycle and the beating assumption. -/
theorem geometricHullSixExclusion_of_orientedPackets
    (hTwoFour : HullSixTwoFourOrientedClosed)
    (hThreeThree : HullSixThreeThreeOrientedClosed) :
    GeometricHullSizeExclusion 6 StrictXOrder := by
  intro v custody _hdomain _hstrict h6 hbeat
  let cycle : Fin 6 → Fin 8 := custody.data.castGet h6
  have hcycleInjective : Function.Injective cycle :=
    HullCycleData.castGet_injective custody.data h6 custody.hull.nodup
  obtain ⟨p, q, hpq, hpOutside, hqOutside⟩ :=
    exists_two_offCycle_finSix_finEight cycle hcycleInjective
  let R : HullSixCompactCrossChordResidual v cycle p q :=
    hullSixCompactCrossChordResidual_of_Beats
      custody.hull h6 p q hpq hpOutside hqOutside hbeat
  exact (hullSixCompactCrossChordClosed_of_orientedPackets
    hTwoFour hThreeThree) v cycle p q R

end Heilbronn8
