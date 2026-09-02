import Heilbronn8.Survivors.Join.HullSixDirectSemanticEndpoint
import Heilbronn8.Survivors.Join.HullSixThreeThreeCornerSpanningXFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP012XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP013XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP022XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP023MergedXFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP033XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP111XFrontier
import Heilbronn8.Survivors.Join.HullSixThreeThreeP112P122MergedXFrontiers
import Heilbronn8.Survivors.Join.HullSixThreeThreeP222XFrontier
import Heilbronn8.Survivors.Join.HullSixTwoFourP02MaximalQReflection
import Heilbronn8.Survivors.Join.HullSixTwoFourP03MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP04MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP11MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP12MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP13MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP22MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP23MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP33MaximalQGeometry

/-!
# Direct hull-six endpoint after the first residual frontier closures

This module composes two geometry-facing partial-`X` frontier providers
which are already unconditional:

* the maximal-q `2 + 4` fibres with first cuts `p = 02`, `p = 03`, `p = 04`,
  `p = 11`, `p = 12`, `p = 13`, `p = 22`, `p = 23`, and `p = 33`; and
* the maximal-q `3 + 3` fibres `012`, `013`, `022`, `023`, `033`, `111`,
  `112`, `122`, and `222`; and
* the five corner-spanning maximal-q `3 + 3` fibres `113`, `123`, `133`,
  `223`, and `233`.

The remaining hypotheses are still genuine partial-frontier callbacks in
the original oriented frame.  No exact-table weakening or uncustodied
table symmetry is used.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-! ## Reduced `2 + 4` frontier family -/

/-- The residual maximal-q `2 + 4` frontiers other than the completed
`p = 11` fibre.  Under legality these are exactly the eight first-cut
fibres `02`, `03`, `04`, `12`, `13`, `22`, `23`, and `33`. -/
def HullSixTwoFourIsResidualMaximalQFrontierExceptP11
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontier T ∧
    ¬HullSixTwoFourIsP11MaximalQFrontier T

/-- Add the unconditional `p = 11` provider to callbacks for the other
eight residual maximal-q `2 + 4` fibres. -/
theorem hullSixTwoFourResidualMaximalQFrontierProvider_of_exceptP11
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierExceptP11) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontier := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP11 : HullSixTwoFourIsP11MaximalQFrontier T
  · exact hullSixTwoFourP11MaximalQFrontierProvider
      F T hLegal hP11
  · exact hRemaining F T hLegal ⟨hResidual, hP11⟩

/-- After also consuming the completed `p = 03` fibre, the residual
maximal-q `2 + 4` frontiers are exactly the seven first-cut fibres
`02`, `04`, `12`, `13`, `22`, `23`, and `33`. -/
def HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontierExceptP11 T ∧
    ¬HullSixTwoFourIsP03MaximalQFrontier T

/-- Add the unconditional `p = 03` provider to callbacks for the seven
residual maximal-q `2 + 4` fibres left after `p = 11` and `p = 03`. -/
theorem hullSixTwoFourResidualExceptP11Provider_of_afterP11P03
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierExceptP11 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP03 : HullSixTwoFourIsP03MaximalQFrontier T
  · exact hullSixTwoFourP03MaximalQFrontierProvider
      F T hLegal hP03
  · exact hRemaining F T hLegal ⟨hResidual, hP03⟩

/-- After also consuming the completed `p = 04` fibre, the residual
maximal-q `2 + 4` frontiers are exactly `02`, `12`, `13`, `22`, `23`, and
`33`. -/
def HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03 T ∧
    ¬HullSixTwoFourIsP04MaximalQFrontier T

/-- Add the unconditional `p = 04` provider to callbacks for the six
residual maximal-q `2 + 4` fibres left after `p = 11` and `p = 03`. -/
theorem hullSixTwoFourResidualAfterP11P03Provider_of_afterP04
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP04 : HullSixTwoFourIsP04MaximalQFrontier T
  · exact hullSixTwoFourP04MaximalQFrontierProvider
      F T hLegal hP04
  · exact hRemaining F T hLegal ⟨hResidual, hP04⟩

/-- After also consuming the completed `p = 12` fibre, the residual
maximal-q `2 + 4` frontiers are exactly `02`, `13`, `22`, `23`, and `33`. -/
def HullSixTwoFourIsResidualMaximalQFrontierAfterP12
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04 T ∧
    ¬HullSixTwoFourIsP12MaximalQFrontier T

/-- Add the unconditional `p = 12` provider to callbacks for the five
residual maximal-q `2 + 4` fibres left after the earlier closures. -/
theorem hullSixTwoFourResidualAfterP04Provider_of_afterP12
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP12) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP12 : HullSixTwoFourIsP12MaximalQFrontier T
  · exact hullSixTwoFourP12MaximalQFrontierProvider
      F T hLegal hP12
  · exact hRemaining F T hLegal ⟨hResidual, hP12⟩

/-- After also consuming the completed `p = 33` fibre, the residual
maximal-q `2 + 4` frontiers are exactly `02`, `13`, `22`, and `23`. -/
def HullSixTwoFourIsResidualMaximalQFrontierAfterP33
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontierAfterP12 T ∧
    ¬HullSixTwoFourIsP33MaximalQFrontier T

/-- Add the unconditional `p = 33` provider to callbacks for the four
residual maximal-q `2 + 4` fibres left after the earlier closures. -/
theorem hullSixTwoFourResidualAfterP12Provider_of_afterP33
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP33) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP12 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP33 : HullSixTwoFourIsP33MaximalQFrontier T
  · exact hullSixTwoFourP33MaximalQFrontierProvider
      F T hLegal hP33
  · exact hRemaining F T hLegal ⟨hResidual, hP33⟩

/-- After also consuming the completed `p = 13` fibre, the residual
maximal-q `2 + 4` frontiers are exactly `02`, `22`, and `23`. -/
def HullSixTwoFourIsResidualMaximalQFrontierAfterP13
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontierAfterP33 T ∧
    ¬HullSixTwoFourIsP13MaximalQFrontier T

/-- Add the unconditional `p = 13` provider to callbacks for the three
residual maximal-q `2 + 4` fibres left after the earlier closures. -/
theorem hullSixTwoFourResidualAfterP33Provider_of_afterP13
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP13) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP33 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP13 : HullSixTwoFourIsP13MaximalQFrontier T
  · exact hullSixTwoFourP13MaximalQFrontierProvider
      F T hLegal hP13
  · exact hRemaining F T hLegal ⟨hResidual, hP13⟩

/-- After also consuming the completed `p = 23` fibre, the residual
maximal-q `2 + 4` frontiers are exactly `02` and `22`. -/
def HullSixTwoFourIsResidualMaximalQFrontierAfterP23
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsResidualMaximalQFrontierAfterP13 T ∧
    ¬HullSixTwoFourIsP23MaximalQFrontier T

/-- Add the unconditional `p = 23` provider to callbacks for the two
residual maximal-q `2 + 4` fibres left after the earlier closures. -/
theorem hullSixTwoFourResidualAfterP13Provider_of_afterP23
    (hRemaining : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP23) :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP13 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP23 : HullSixTwoFourIsP23MaximalQFrontier T
  · exact hullSixTwoFourP23MaximalQFrontierProvider
      F T hLegal hP23
  · exact hRemaining F T hLegal ⟨hResidual, hP23⟩

/-- The only two first-cut fibres surviving all earlier `2 + 4` providers
are `02` and `22`. -/
private theorem hullSixTwoFour_afterP23_cases :
    ∀ T : HullSixTwoFourCuts,
      HullSixTwoFourIsResidualMaximalQFrontierAfterP23 T →
        HullSixTwoFourIsP02MaximalQFrontier T ∨
          HullSixTwoFourIsP22MaximalQFrontier T := by
  intro T h
  rcases h with
    ⟨⟨⟨⟨⟨⟨⟨hResidual, hNot11⟩, hNot03⟩, hNot04⟩,
      hNot12⟩, hNot33⟩, hNot13⟩, hNot23⟩
  rcases hResidual with ⟨hMax, hFirst⟩
  rcases hFirst with h02 | h03 | h04 | h11 | h12 | h13 | h22 | h23 | h33
  · exact Or.inl ⟨hMax, h02⟩
  · exact (hNot03 ⟨hMax, h03⟩).elim
  · exact (hNot04 ⟨hMax, h04⟩).elim
  · exact (hNot11 ⟨hMax, h11⟩).elim
  · exact (hNot12 ⟨hMax, h12⟩).elim
  · exact (hNot13 ⟨hMax, h13⟩).elim
  · exact Or.inr ⟨hMax, h22⟩
  · exact (hNot23 ⟨hMax, h23⟩).elim
  · exact (hNot33 ⟨hMax, h33⟩).elim

/-- The completed `p = 22` provider supplies the sole callback needed by the
honest physical-reflection implementation of the `p = 02` provider. -/
theorem hullSixTwoFourP02MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsP02MaximalQFrontier := by
  apply hullSixTwoFourP02MaximalQFrontierProvider_of_p22
  intro cfg cycle p q R F U hLegal hP22
  exact hullSixTwoFourP22MaximalQFrontierProvider F U hLegal hP22

/-- All residual maximal-q `2 + 4` frontiers are now closed. -/
theorem hullSixTwoFourResidualAfterP23FrontierProvider :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP23 := by
  intro cfg cycle p q R F T hLegal hResidual
  rcases hullSixTwoFour_afterP23_cases T hResidual with hP02 | hP22
  · exact hullSixTwoFourP02MaximalQFrontierProvider
      F T hLegal hP02
  · exact hullSixTwoFourP22MaximalQFrontierProvider
      F T hLegal hP22

/-! ## Reduced `3 + 3` frontier family -/

/-- The remaining maximal-q `3 + 3` frontiers which are not among the five
completed corner-spanning fibres.  Under legality these are exactly
`001`, `002`, `003`, `012`, `013`, `022`, `023`, `033`, `111`, `112`,
`122`, and `222`. -/
def HullSixThreeThreeIsRemainingNonCornerSpanningFrontier
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingMaximalQFrontier T ∧
    ¬HullSixThreeThreeGeometricFrame.IsCornerSpanningRemainingFrontier T

/-- Add the unconditional five-fibre corner-spanning provider to callbacks
for the other twelve maximal-q `3 + 3` frontiers. -/
theorem hullSixThreeThreeRemainingMaximalQFrontierProvider_of_nonCorner
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingNonCornerSpanningFrontier) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingMaximalQFrontier := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hCorner :
      HullSixThreeThreeGeometricFrame.IsCornerSpanningRemainingFrontier T
  · exact hullSixThreeThreeCornerSpanningXFrontierProvider
      F T hLegal hCorner
  · exact hRemaining F T hLegal ⟨hResidual, hCorner⟩

/-- After also consuming the completed `p = 013` fibre, the remaining
maximal-q `3 + 3` frontiers are exactly `001`, `002`, `003`, `012`, `022`,
`023`, `033`, `111`, `112`, `122`, and `222`. -/
def HullSixThreeThreeIsRemainingAfterCornerAndP013
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingNonCornerSpanningFrontier T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP013RemainingFrontier T

/-- Add the unconditional `p = 013` provider to callbacks for the eleven
maximal-q `3 + 3` frontiers left after the corner-spanning family. -/
theorem hullSixThreeThreeNonCornerProvider_of_afterP013
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterCornerAndP013) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingNonCornerSpanningFrontier := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP013 :
      HullSixThreeThreeGeometricFrame.IsP013RemainingFrontier T
  · exact hullSixThreeThreeP013XFrontierProvider
      F T hLegal hP013
  · exact hRemaining F T hLegal ⟨hResidual, hP013⟩

/-- After also consuming `p = 023`, the remaining maximal-q `3 + 3`
frontiers are exactly `001`, `002`, `003`, `012`, `022`, `033`, `111`,
`112`, `122`, and `222`. -/
def HullSixThreeThreeIsRemainingAfterP013P023
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterCornerAndP013 T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP023RemainingFrontier T

/-- Add the unconditional `p = 023` provider to callbacks for the ten
maximal-q `3 + 3` frontiers left after the earlier closures. -/
theorem hullSixThreeThreeAfterP013Provider_of_afterP023
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP013P023) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterCornerAndP013 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP023 :
      HullSixThreeThreeGeometricFrame.IsP023RemainingFrontier T
  · exact hullSixThreeThreeP023MergedXFrontierProvider
      F T hLegal hP023
  · exact hRemaining F T hLegal ⟨hResidual, hP023⟩

/-- After also consuming `p = 112` and `p = 122`, the remaining maximal-q
`3 + 3` frontiers are exactly `001`, `002`, `003`, `012`, `022`, `033`,
`111`, and `222`. -/
def HullSixThreeThreeIsRemainingAfterMergedPathClosures
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterP013P023 T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP112P122RemainingFrontier T

/-- Add the unconditional `p = 112` and `p = 122` provider to callbacks
for the eight maximal-q `3 + 3` frontiers left after the merged-path
closures. -/
theorem hullSixThreeThreeAfterP023Provider_of_afterP112P122
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterMergedPathClosures) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP013P023 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP112P122 :
      HullSixThreeThreeGeometricFrame.IsP112P122RemainingFrontier T
  · exact hullSixThreeThreeP112P122MergedXFrontierProvider
      F T hLegal hP112P122
  · exact hRemaining F T hLegal ⟨hResidual, hP112P122⟩

/-- After also consuming `p = 033`, the remaining maximal-q `3 + 3`
frontiers are exactly `001`, `002`, `003`, `012`, `022`, `111`, and
`222`. -/
def HullSixThreeThreeIsRemainingAfterP033
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterMergedPathClosures T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP033RemainingFrontier T

/-- Add the unconditional `p = 033` provider to callbacks for the seven
maximal-q `3 + 3` frontiers left after the earlier closures. -/
theorem hullSixThreeThreeAfterMergedPathProvider_of_afterP033
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterMergedPathClosures := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP033 :
      HullSixThreeThreeGeometricFrame.IsP033RemainingFrontier T
  · exact hullSixThreeThreeP033XFrontierProvider
      F T hLegal hP033
  · exact hRemaining F T hLegal ⟨hResidual, hP033⟩

/-- After also consuming `p = 222`, the remaining maximal-q `3 + 3`
frontiers are exactly `001`, `002`, `003`, `012`, `022`, and `111`. -/
def HullSixThreeThreeIsRemainingAfterP033P222
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterP033 T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP222RemainingFrontier T

/-- Add the unconditional `p = 222` provider to callbacks for the six
maximal-q `3 + 3` frontiers left after the earlier closures. -/
theorem hullSixThreeThreeAfterP033Provider_of_afterP222
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033P222) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP222 :
      HullSixThreeThreeGeometricFrame.IsP222RemainingFrontier T
  · exact hullSixThreeThreeP222XFrontierProvider
      F T hLegal hP222
  · exact hRemaining F T hLegal ⟨hResidual, hP222⟩

/-- After also consuming `p = 022`, the remaining maximal-q `3 + 3`
frontiers are exactly `001`, `002`, `003`, `012`, and `111`. -/
def HullSixThreeThreeIsRemainingAfterP022
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterP033P222 T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP022RemainingFrontier T

/-- Add the unconditional `p = 022` provider to callbacks for the five
maximal-q `3 + 3` frontiers left after the earlier closures. -/
theorem hullSixThreeThreeAfterP033P222Provider_of_afterP022
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP022) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033P222 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP022 :
      HullSixThreeThreeGeometricFrame.IsP022RemainingFrontier T
  · exact hullSixThreeThreeP022XFrontierProvider
      F T hLegal hP022
  · exact hRemaining F T hLegal ⟨hResidual, hP022⟩

/-- After also consuming `p = 012`, the remaining maximal-q `3 + 3`
frontiers are exactly `001`, `002`, `003`, and `111`. -/
def HullSixThreeThreeIsRemainingAfterP012
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterP022 T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP012RemainingFrontier T

/-- Add the unconditional `p = 012` provider to callbacks for the four
maximal-q `3 + 3` frontiers left after the earlier closures. -/
theorem hullSixThreeThreeAfterP022Provider_of_afterP012
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP012) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP022 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP012 :
      HullSixThreeThreeGeometricFrame.IsP012RemainingFrontier T
  · exact hullSixThreeThreeP012XFrontierProvider
      F T hLegal hP012
  · exact hRemaining F T hLegal ⟨hResidual, hP012⟩

/-- After also consuming `p = 111`, the remaining maximal-q `3 + 3`
frontiers are exactly `001`, `002`, and `003`. -/
def HullSixThreeThreeIsRemainingAfterP111
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsRemainingAfterP012 T ∧
    ¬HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier T

/-- Add the unconditional `p = 111` provider to callbacks for the three
maximal-q `3 + 3` fibres left after all earlier closures. -/
theorem hullSixThreeThreeAfterP012Provider_of_afterP111
    (hRemaining : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP111) :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP012 := by
  intro cfg cycle p q R F T hLegal hResidual
  by_cases hP111 :
      HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier T
  · exact hullSixThreeThreeP111XFrontierProvider
      F T hLegal hP111
  · exact hRemaining F T hLegal ⟨hResidual, hP111⟩

/-! ## Refined direct endpoint -/

/-- The direct H6 endpoint after consuming the completed `p = 11`
`2 + 4` frontier and the five completed corner-spanning `3 + 3` frontiers.
The only remaining inputs are callbacks for eight and twelve honest
same-frame partial-`X` frontier fibres, respectively. -/
theorem geometricHullSixExclusion_of_reducedResidualFrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierExceptP11)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingNonCornerSpanningFrontier) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_residualFrontierProviders
    (hullSixTwoFourResidualMaximalQFrontierProvider_of_exceptP11 hTwoFour)
    (hullSixThreeThreeRemainingMaximalQFrontierProvider_of_nonCorner
      hThreeThree)

/-- Refined direct endpoint after also consuming the completed `p = 03`
`2 + 4` maximal-q frontier.  Its explicit inputs are callbacks for seven
`2 + 4` and twelve `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_furtherReducedFrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingNonCornerSpanningFrontier) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_reducedResidualFrontierProviders
    (hullSixTwoFourResidualExceptP11Provider_of_afterP11P03 hTwoFour)
    hThreeThree

/-- Current direct H6 progress endpoint.  The only remaining inputs are
callbacks for seven `2 + 4` and eleven `3 + 3` same-frame partial-`X`
frontier fibres. -/
theorem geometricHullSixExclusion_of_currentResidualFrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterCornerAndP013) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_furtherReducedFrontierProviders
    hTwoFour
    (hullSixThreeThreeNonCornerProvider_of_afterP013 hThreeThree)

/-- Direct H6 progress endpoint after the completed `p = 023` `3 + 3`
frontier.  The explicit inputs are callbacks for seven `2 + 4` and ten
`3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentResidualFrontierProvidersP023
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP013P023) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentResidualFrontierProviders
    hTwoFour
    (hullSixThreeThreeAfterP013Provider_of_afterP023 hThreeThree)

/-- Current direct H6 progress endpoint after the four completed
merged-path `3 + 3` fibres.  The explicit inputs are callbacks for seven
`2 + 4` and eight `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentMergedPathFrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterMergedPathClosures) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentResidualFrontierProvidersP023
    hTwoFour
    (hullSixThreeThreeAfterP023Provider_of_afterP112P122 hThreeThree)

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 033` `3 + 3` frontier.  The explicit inputs are callbacks for seven
`2 + 4` and seven `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP033FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentMergedPathFrontierProviders
    hTwoFour
    (hullSixThreeThreeAfterMergedPathProvider_of_afterP033 hThreeThree)

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 222` `3 + 3` frontier.  The explicit inputs are callbacks for seven
`2 + 4` and six `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP222FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033P222) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP033FrontierProviders
    hTwoFour
    (hullSixThreeThreeAfterP033Provider_of_afterP222 hThreeThree)

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 04` maximal-q `2 + 4` frontier.  The explicit inputs are callbacks for
six `2 + 4` and six `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP04FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP033P222) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP222FrontierProviders
    (hullSixTwoFourResidualAfterP11P03Provider_of_afterP04 hTwoFour)
    hThreeThree

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 022` `3 + 3` frontier.  The explicit inputs are callbacks for six
`2 + 4` and five `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP022FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP022) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP04FrontierProviders
    hTwoFour
    (hullSixThreeThreeAfterP033P222Provider_of_afterP022 hThreeThree)

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 012` `3 + 3` frontier.  The explicit inputs are callbacks for six
`2 + 4` and four `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP012FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP11P03P04)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP012) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP022FrontierProviders
    hTwoFour
    (hullSixThreeThreeAfterP022Provider_of_afterP012 hThreeThree)

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 12` maximal-q `2 + 4` frontier.  The explicit inputs are callbacks for
five `2 + 4` and four `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP12FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP12)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP012) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP012FrontierProviders
    (hullSixTwoFourResidualAfterP04Provider_of_afterP12 hTwoFour)
    hThreeThree

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 33` maximal-q `2 + 4` frontier.  The explicit inputs are callbacks for
four `2 + 4` and four `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP33FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP33)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP012) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP12FrontierProviders
    (hullSixTwoFourResidualAfterP12Provider_of_afterP33 hTwoFour)
    hThreeThree

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 13` maximal-q `2 + 4` frontier.  The explicit inputs are callbacks for
three `2 + 4` and four `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP13FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP13)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP012) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP33FrontierProviders
    (hullSixTwoFourResidualAfterP33Provider_of_afterP13 hTwoFour)
    hThreeThree

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 111` maximal-q `3 + 3` frontier.  Its only explicit inputs are callbacks
for three `2 + 4` and three `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP111FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP13)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP111) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP13FrontierProviders
    hTwoFour
    (hullSixThreeThreeAfterP012Provider_of_afterP111 hThreeThree)

/-- Current direct H6 progress endpoint after also consuming the completed
`p = 23` maximal-q `2 + 4` frontier.  Its only explicit inputs are callbacks
for two `2 + 4` and three `3 + 3` same-frame partial-`X` frontier fibres. -/
theorem geometricHullSixExclusion_of_currentP23FrontierProviders
    (hTwoFour : HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsResidualMaximalQFrontierAfterP23)
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP111) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP111FrontierProviders
    (hullSixTwoFourResidualAfterP13Provider_of_afterP23 hTwoFour)
    hThreeThree

/-- Current direct H6 progress endpoint after completing every residual
maximal-q `2 + 4` frontier.  Its only remaining input is the provider for the
three `3 + 3` fibres `001`, `002`, and `003`. -/
theorem geometricHullSixExclusion_of_currentThreeThreeFrontierProvider
    (hThreeThree : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP111) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentP23FrontierProviders
    hullSixTwoFourResidualAfterP23FrontierProvider
    hThreeThree

end Heilbronn8
