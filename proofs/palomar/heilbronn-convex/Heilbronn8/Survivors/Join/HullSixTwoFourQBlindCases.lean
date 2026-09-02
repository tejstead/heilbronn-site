import Heilbronn8.Survivors.Join.HullSixTwoFourFiniteBridge
import Heilbronn8.Survivors.Join.HullSixTwoFourWideProduct

/-!
# Exact second-cut cases above the `2 x 4` q-blind frontier

The finite bridge reduces the coupled `2 + 4` scalar problem to first cuts
`p = (0,1)`.  Ferrers legality leaves thirteen possible second-cut pairs.
Three of them are already covered by the wide-column product theorem; this
file records both finite alternatives with ordinary kernel `decide`.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixTwoFourCuts

private def qBlindCuts (q0 q1 : Fin 5) : HullSixTwoFourCuts :=
  ⟨0, 1, q0, q1⟩

def qBlind01 : HullSixTwoFourCuts := qBlindCuts 0 1
def qBlind02 : HullSixTwoFourCuts := qBlindCuts 0 2
def qBlind03 : HullSixTwoFourCuts := qBlindCuts 0 3
def qBlind04 : HullSixTwoFourCuts := qBlindCuts 0 4
def qBlind11 : HullSixTwoFourCuts := qBlindCuts 1 1
def qBlind12 : HullSixTwoFourCuts := qBlindCuts 1 2
def qBlind13 : HullSixTwoFourCuts := qBlindCuts 1 3
def qBlind14 : HullSixTwoFourCuts := qBlindCuts 1 4
def qBlind22 : HullSixTwoFourCuts := qBlindCuts 2 2
def qBlind23 : HullSixTwoFourCuts := qBlindCuts 2 3
def qBlind24 : HullSixTwoFourCuts := qBlindCuts 2 4
def qBlind33 : HullSixTwoFourCuts := qBlindCuts 3 3

/-- Exact classification of legal second cuts above `p=(0,1)`.  The last
case is the finite bridge's `qBlindTop`, namely cuts `(0,1,3,4)`. -/
theorem qBlind01_cases : ∀ T : HullSixTwoFourCuts,
    T.Legal → T.p0 = 0 → T.p1 = 1 →
      T = qBlind01 ∨ T = qBlind02 ∨ T = qBlind03 ∨
      T = qBlind04 ∨ T = qBlind11 ∨ T = qBlind12 ∨
      T = qBlind13 ∨ T = qBlind14 ∨ T = qBlind22 ∨
      T = qBlind23 ∨ T = qBlind24 ∨ T = qBlind33 ∨
      T = qBlindTop := by
  decide

/-- The three low-`q0` cases with `q1<4` are precisely the wide-column
subfamily inside the q-blind first-cut fibre. -/
theorem qBlind01_hasWideProductTwelve :
    qBlind01.HasWideProductTwelve := by
  decide

theorem qBlind02_hasWideProductTwelve :
    qBlind02.HasWideProductTwelve := by
  decide

theorem qBlind03_hasWideProductTwelve :
    qBlind03.HasWideProductTwelve := by
  decide

/-- After removing the wide-column cases, exactly ten q-blind sign branches
remain for the coupled scalar theorem. -/
theorem qBlind01_nonwide_cases : ∀ T : HullSixTwoFourCuts,
    T.Legal → T.p0 = 0 → T.p1 = 1 →
      ¬T.HasWideProductTwelve →
      T = qBlind04 ∨ T = qBlind11 ∨ T = qBlind12 ∨
      T = qBlind13 ∨ T = qBlind14 ∨ T = qBlind22 ∨
      T = qBlind23 ∨ T = qBlind24 ∨ T = qBlind33 ∨
      T = qBlindTop := by
  decide

/-! ## Transition packets

The ten nonwide cuts are not intended to become ten unrelated scalar
certificates.  Their `Q`-fan transitions fall into four geometric packets.
The definitions below record that compression before any metric theorem is
attached.
-/

/-- Coincident transitions in the two rows. -/
@[reducible] def IsCoincidentTransitionPacket
    (T : HullSixTwoFourCuts) : Prop :=
  T = qBlind11 ∨ T = qBlind22 ∨ T = qBlind33

/-- Adjacent staggered transitions. -/
@[reducible] def IsAdjacentStaggerPacket
    (T : HullSixTwoFourCuts) : Prop :=
  T = qBlind12 ∨ T = qBlind23 ∨ T = qBlindTop

/-- Two separated transitions, including the right-open reflected case. -/
@[reducible] def IsSeparatedTransitionPacket
    (T : HullSixTwoFourCuts) : Prop :=
  T = qBlind13 ∨ T = qBlind24

/-- Only one row has an interior transition. -/
@[reducible] def IsEndOpenTransitionPacket
    (T : HullSixTwoFourCuts) : Prop :=
  T = qBlind04 ∨ T = qBlind14

/-- Exact five-packet classification of the q-blind first-cut fibre. -/
theorem qBlind01_packet_cases : ∀ T : HullSixTwoFourCuts,
    T.Legal → T.p0 = 0 → T.p1 = 1 →
      T.HasWideProductTwelve ∨
      T.IsCoincidentTransitionPacket ∨
      T.IsAdjacentStaggerPacket ∨
      T.IsSeparatedTransitionPacket ∨
      T.IsEndOpenTransitionPacket := by
  decide

/-- The four nonwide packets are pairwise disjoint. -/
theorem qBlind01_nonwide_packets_pairwise_disjoint :
    ∀ T : HullSixTwoFourCuts,
      ¬(T.IsCoincidentTransitionPacket ∧ T.IsAdjacentStaggerPacket) ∧
      ¬(T.IsCoincidentTransitionPacket ∧ T.IsSeparatedTransitionPacket) ∧
      ¬(T.IsCoincidentTransitionPacket ∧ T.IsEndOpenTransitionPacket) ∧
      ¬(T.IsAdjacentStaggerPacket ∧ T.IsSeparatedTransitionPacket) ∧
      ¬(T.IsAdjacentStaggerPacket ∧ T.IsEndOpenTransitionPacket) ∧
      ¬(T.IsSeparatedTransitionPacket ∧ T.IsEndOpenTransitionPacket) := by
  decide

end HullSixTwoFourCuts
end Heilbronn8
