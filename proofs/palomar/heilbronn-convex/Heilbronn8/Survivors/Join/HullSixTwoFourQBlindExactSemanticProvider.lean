import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindExactGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# Sound semantic provider for the exact native `2 + 4` packets

The exact dispatcher now closes every wide table, the hard table, and all
thirteen tables with first cuts `p = (0,1)`.  Tables outside that explicit
union stay in their original geometric frame and weaken only to the partial
maximal-q `X` frontier.  No exact chamber table is transported through a
q-weakening or an unproved symmetry.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The exact fixed-orientation union implemented by the current native
geometry adapters. -/
def HullSixTwoFourIsNativeExact (T : HullSixTwoFourCuts) : Prop :=
  T.HasWideProductTwelve ∨ T.IsHard ∨ (T.p0 = 0 ∧ T.p1 = 1)

/-- The native exact geometry dispatcher supplies the semantic exact-packet
callback in every fixed frame. -/
theorem hullSixTwoFourNativeExactPacketProvider :
    HullSixTwoFourExactPacketProvider HullSixTwoFourIsNativeExact := by
  intro cfg cycle p q R F
  intro T hLegal hPacket hTable
  exact R.twoFourNativeExactAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hLegal hPacket hTable

/-- Every legal table is either consumed exactly by a native adapter or
weakens, in the same frame, to the maximal second-cut `X` frontier with its
first cuts unchanged. -/
theorem hullSixTwoFour_nativeExact_or_maximalQ_cover :
    HullSixTwoFourFixedOrientationCover
      HullSixTwoFourIsNativeExact HullSixTwoFourIsMaximalQFrontier := by
  intro T hLegal
  by_cases hExact : HullSixTwoFourIsNativeExact T
  · exact Or.inl hExact
  · right
    let U : HullSixTwoFourCuts := ⟨T.p0, T.p1, 3, 4⟩
    refine ⟨U, ?_, ?_, ?_⟩
    · rcases hLegal with ⟨hp0q0, hp1q1, hp, hq, hbound⟩
      rcases hbound with ⟨hp1, hq0⟩
      dsimp [HullSixTwoFourCuts.Weak, U]
      constructor
      · rfl
      constructor
      · rfl
      constructor <;> omega
    · rcases hLegal with ⟨hp0q0, hp1q1, hp, hq, hbound⟩
      rcases hbound with ⟨hp1, hq0⟩
      dsimp [HullSixTwoFourCuts.Legal, HullSixTwoFourCuts.Boundaries, U]
      omega
    · simp [HullSixTwoFourIsMaximalQFrontier, U]

/-- Conditional global `2 + 4` closure.  Its sole remaining metric premise
is the honest partial-X provider on the thirteen maximal-q frontiers. -/
theorem hullSixTwoFourFerrersClosed_of_nativeExact_maximalQFrontiers
    (hFrontier :
      HullSixTwoFourXFrontierProvider HullSixTwoFourIsMaximalQFrontier) :
    HullSixTwoFourFerrersClosed :=
  hullSixTwoFourFerrersClosed_of_fixedOrientationCover
    hullSixTwoFour_nativeExact_or_maximalQ_cover
    hullSixTwoFourNativeExactPacketProvider hFrontier

/-- Direct hull-six endpoint with every current exact `2 + 4` adapter wired
in.  The two explicit remaining inputs are the maximal-q partial-X provider
and an independently sound global `3 + 3` closure. -/
theorem geometricHullSixExclusion_of_nativeExact_maximalQFrontiers
    (hFrontier :
      HullSixTwoFourXFrontierProvider HullSixTwoFourIsMaximalQFrontier)
    (hThreeThree : HullSixThreeThreeFerrersClosed) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_ferrersClosed
    (hullSixTwoFourFerrersClosed_of_nativeExact_maximalQFrontiers hFrontier)
    hThreeThree

end Heilbronn8
