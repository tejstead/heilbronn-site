import Heilbronn8.Survivors.Join.HullSixDirectSemanticProgress
import Heilbronn8.Survivors.Join.HullSixQBlindFrontierUniqueness
import Heilbronn8.Survivors.Join.HullSixThreeThreeReflectedCustody
import Heilbronn8.Survivors.Join.HullSixThreeThreeRotateComplementResidualPackets
import Heilbronn8.Survivors.Join.HullSixThreeThreeSmallPRoute001
import Heilbronn8.Survivors.Join.HullSixThreeThreeSmallPRoute002
import Heilbronn8.Survivors.Join.HullSixThreeThreeSmallPRoute003

/-!
# The final three `3 + 3` maximal-q frontiers

The retained maximal-q `X` frontier does not itself contain the `Y` signs
needed by a table symmetry.  We therefore reconstruct the canonical exact
Ferrers table in the original geometric frame and recover its first cuts by
comparing its `X` signs with the supplied frontier.

For exact tables with first cuts `001`, `002`, or `003`, a kernel-checked
finite alternative is then acyclic:

* the high-q residual packets go to the native, physical
  rotate-complement, or complement-transpose sinks;
* every other complement-transposed packet is either native `p = 011`, or
  weakens in the transformed frame to one of the already closed maximal-q
  frontiers.

No exact table is asserted after a q-weakening, and every nontrivial table
symmetry below is carried by an explicit geometric frame construction.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

private theorem hullSixThreeThree_weak_maximalQ
    (T : HullSixThreeThreeCuts) (hLegal : T.Legal) :
    HullSixThreeThreeCuts.Weak T (hullSixThreeThreeMaximalQ T) := by
  rcases hLegal with
    ⟨_hp01, _hp12, _hq01, _hq12, _hpq0, _hpq1, _hpq2, _hp2, hq0⟩
  dsimp [HullSixThreeThreeCuts.Weak, hullSixThreeThreeMaximalQ]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> omega

private theorem hullSixThreeThree_legal_maximalQ
    (T : HullSixThreeThreeCuts) (hLegal : T.Legal) :
    (hullSixThreeThreeMaximalQ T).Legal := by
  rcases hLegal with
    ⟨hp01, hp12, _hq01, _hq12, hpq0, _hpq1, _hpq2, hp2, hq0⟩
  dsimp [HullSixThreeThreeCuts.Legal, hullSixThreeThreeMaximalQ]
  omega

/-! ## Existing maximal-q sinks as one provider -/

private theorem hullSixThreeThreeKnownSinkFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeGeometricFrame.IsKnownSinkFrontier := by
  intro cfg cycle p q R F T hLegal hPacket
  rcases hPacket with
    hCorner | h013 | h023 | h112122 | h033 | h222 | h022 | h012 | h111
  · exact hullSixThreeThreeCornerSpanningXFrontierProvider
      F T hLegal hCorner
  · exact hullSixThreeThreeP013XFrontierProvider F T hLegal h013
  · exact hullSixThreeThreeP023MergedXFrontierProvider F T hLegal h023
  · exact hullSixThreeThreeP112P122MergedXFrontierProvider
      F T hLegal h112122
  · exact hullSixThreeThreeP033XFrontierProvider F T hLegal h033
  · exact hullSixThreeThreeP222XFrontierProvider F T hLegal h222
  · exact hullSixThreeThreeP022XFrontierProvider F T hLegal h022
  · exact hullSixThreeThreeP012XFrontierProvider F T hLegal h012
  · exact hullSixThreeThreeP111XFrontierProvider F T hLegal h111

/-! ## Exact finite dispatcher -/

private theorem hullSixThreeThreeSmallPDirectExactSinkProvider :
    HullSixThreeThreeExactPacketProvider
      HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink := by
  intro cfg cycle p q R F
  intro T hLegal hPacket hTable
  rcases hPacket with hNative | hRotate | hRotateNative
  · exact hullSixThreeThreeClosedNativePacketProvider
      F T hLegal hNative hTable
  · exact hullSixThreeThreeRotateComplementResidualPacketProvider
      F T hLegal hRotate hTable
  · exact
      (hullSixThreeThreeExactPacketProvider_rotateComplement
        hullSixThreeThreeClosedNativePacketProvider)
        F T hLegal hRotateNative hTable

/-- Kernel census for all legal exact tables in the three final first-cut
fibres.  The eight high-q tables use a direct sink, possibly after honest
complement-transposition.  The other thirty-four tables transform to a
native `011` packet or to one of the previously completed maximal-q
frontiers. -/
private theorem hullSixThreeThree_smallP_exact_route :
    ∀ T : HullSixThreeThreeCuts, T.Legal →
      HullSixThreeThreeGeometricFrame.IsSmallPExactPacket T →
        HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink T ∨
        HullSixThreeThreeGeometricFrame.IsSmallPDirectExactSink
          T.complementTranspose ∨
        HullSixThreeThreeGeometricFrame.IsClosedNativePacket
          T.complementTranspose ∨
        HullSixThreeThreeGeometricFrame.IsKnownSinkFrontier
          (hullSixThreeThreeMaximalQ T.complementTranspose) := by
  rintro ⟨p0, p1, p2, q0, q1, q2⟩ hLegal hSmall
  simp only [HullSixThreeThreeGeometricFrame.IsSmallPExactPacket] at hSmall
  rcases hSmall with h001 | h002 | h003
  · rcases h001 with ⟨hp0, hp1, hp2⟩
    subst p0
    subst p1
    subst p2
    simpa only [hullSixThreeThreeSmallPRoute] using
      (hullSixThreeThree_smallP_route_001 q0 q1 q2 hLegal)
  · rcases h002 with ⟨hp0, hp1, hp2⟩
    subst p0
    subst p1
    subst p2
    simpa only [hullSixThreeThreeSmallPRoute] using
      (hullSixThreeThree_smallP_route_002 q0 q1 q2 hLegal)
  · rcases h003 with ⟨hp0, hp1, hp2⟩
    subst p0
    subst p1
    subst p2
    simpa only [hullSixThreeThreeSmallPRoute] using
      (hullSixThreeThree_smallP_route_003 q0 q1 q2 hLegal)

/-- Every exact table whose first cuts are `001`, `002`, or `003` is
closed by the acyclic native/physical-symmetry/maximal-q dispatcher. -/
theorem hullSixThreeThreeSmallPExactPacketProvider :
    HullSixThreeThreeExactPacketProvider
      HullSixThreeThreeGeometricFrame.IsSmallPExactPacket := by
  intro cfg cycle p q R F
  intro T hLegal hSmall hTable
  rcases hullSixThreeThree_smallP_exact_route T hLegal hSmall with
    hDirect | hDirectCT | hNativeCT | hKnown
  · exact hullSixThreeThreeSmallPDirectExactSinkProvider
      F T hLegal hDirect hTable
  · exact
      (hullSixThreeThreeExactPacketProvider_complementTranspose
        hullSixThreeThreeSmallPDirectExactSinkProvider)
        F T hLegal hDirectCT hTable
  · exact
      (hullSixThreeThreeExactPacketProvider_complementTranspose
        hullSixThreeThreeClosedNativePacketProvider)
        F T hLegal hNativeCT hTable
  · let S := T.complementTranspose
    let U := hullSixThreeThreeMaximalQ S
    have hSLegal : S.Legal := by
      simpa [S, HullSixThreeThreeCuts.act] using
        (HullSixThreeThreeCuts.legal_act
          HullSixThreeThreeCuts.Symmetry.complementTranspose T hLegal)
    have hULegal : U.Legal := by
      exact hullSixThreeThree_legal_maximalQ S hSLegal
    have hWeak : HullSixThreeThreeCuts.Weak S U := by
      exact hullSixThreeThree_weak_maximalQ S hSLegal
    have hSTable : F.swapRotateThree.TableHolds S := by
      simpa [S] using F.tableHolds_complementTranspose hLegal hTable
    have hUFrontier : F.swapRotateThree.XFrontierHolds U :=
      F.swapRotateThree.xFrontierHolds_of_table_weak
        hSLegal hWeak hSTable
    exact
      (hullSixThreeThreeKnownSinkFrontierProvider
        F.swapRotateThree U hULegal (by simpa [S, U] using hKnown))
        hUFrontier

/-! ## From a partial frontier back to its exact first cuts -/

private theorem hullSixThreeThree_smallP_of_exactTable_of_frontier
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (S U : HullSixThreeThreeCuts)
    (hSLegal : S.Legal)
    (hUSmall : HullSixThreeThreeGeometricFrame.IsSmallPExactPacket U)
    (hSTable : F.TableHolds S)
    (hUFrontier : F.XFrontierHolds U) :
    HullSixThreeThreeGeometricFrame.IsSmallPExactPacket S := by
  let Stop := hullSixThreeThreeMaximalQ S
  have hSWeak : HullSixThreeThreeCuts.Weak S Stop := by
    exact hullSixThreeThree_weak_maximalQ S hSLegal
  have hSFrontier : F.XFrontierHolds Stop :=
    F.xFrontierHolds_of_table_weak hSLegal hSWeak hSTable
  have hpBound : ∀ i, U.p i ≤ 3 := by
    intro i
    fin_cases i <;> simp [HullSixThreeThreeCuts.p] <;> omega
  have hStopBound : ∀ i, Stop.p i ≤ 3 := by
    intro i
    fin_cases i <;>
      simp [HullSixThreeThreeCuts.p, Stop, hullSixThreeThreeMaximalQ] <;>
      omega
  have hpEq : U.p = Stop.p :=
    qBlindFrontierHolds_p_unique R.minTri_pos hpBound hStopBound
      hUFrontier hSFrontier
  have hSp0U : S.p0 = U.p0 := by
    apply Fin.ext
    simpa [HullSixThreeThreeCuts.p, Stop,
      hullSixThreeThreeMaximalQ] using
        (congrFun hpEq (0 : Fin 3)).symm
  have hSp1U : S.p1 = U.p1 := by
    apply Fin.ext
    simpa [HullSixThreeThreeCuts.p, Stop,
      hullSixThreeThreeMaximalQ] using
        (congrFun hpEq (1 : Fin 3)).symm
  have hSp2U : S.p2 = U.p2 := by
    apply Fin.ext
    simpa [HullSixThreeThreeCuts.p, Stop,
      hullSixThreeThreeMaximalQ] using
        (congrFun hpEq (2 : Fin 3)).symm
  rcases hUSmall with h001 | h002 | h003
  · exact Or.inl
      ⟨hSp0U.trans h001.1, hSp1U.trans h001.2.1,
        hSp2U.trans h001.2.2⟩
  · exact Or.inr (Or.inl
      ⟨hSp0U.trans h002.1, hSp1U.trans h002.2.1,
        hSp2U.trans h002.2.2⟩)
  · exact Or.inr (Or.inr
      ⟨hSp0U.trans h003.1, hSp1U.trans h003.2.1,
        hSp2U.trans h003.2.2⟩)

private theorem hullSixThreeThree_afterP111_isSmallP :
    ∀ T : HullSixThreeThreeCuts, T.Legal →
      HullSixThreeThreeIsRemainingAfterP111 T →
        HullSixThreeThreeGeometricFrame.IsSmallPExactPacket T := by
  intro T hLegal hRemaining
  rcases hRemaining with ⟨hBefore111, hNot111⟩
  rcases hBefore111 with ⟨hBefore012, hNot012⟩
  rcases hBefore012 with ⟨hBefore022, hNot022⟩
  rcases hBefore022 with ⟨hBefore222, hNot222⟩
  rcases hBefore222 with ⟨hBefore033, hNot033⟩
  rcases hBefore033 with ⟨hBeforeMerged, hNotMerged⟩
  rcases hBeforeMerged with ⟨hBefore023, hNot023⟩
  rcases hBefore023 with ⟨hBefore013, hNot013⟩
  rcases hBefore013 with ⟨hBase, hNotCorner⟩
  rcases T with ⟨p0, p1, p2, q0, q1, q2⟩
  fin_cases p0 <;> fin_cases p1 <;> fin_cases p2 <;>
    simp_all [HullSixThreeThreeCuts.Legal,
      HullSixThreeThreeGeometricFrame.IsSmallPExactPacket,
      HullSixThreeThreeGeometricFrame.IsCornerSpanningRemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP013RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP023RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP112P122RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP112RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP122RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP033RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP222RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP022RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP012RemainingFrontier,
      HullSixThreeThreeGeometricFrame.IsP111RemainingFrontier,
      HullSixThreeThreeIsRemainingMaximalQFrontier,
      HullSixThreeThreeIsMaximalQFrontier,
      HullSixThreeThreeGeometricFrame.IsQBlindP011Packet]

/-- Final unconditional provider for the three maximal-q `3 + 3`
frontiers `001`, `002`, and `003`. -/
theorem hullSixThreeThreeSmallPResidualXFrontierProvider :
    HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingAfterP111 := by
  intro cfg cycle p q R F U hULegal hRemaining hUFrontier
  have hUSmall :
      HullSixThreeThreeGeometricFrame.IsSmallPExactPacket U :=
    hullSixThreeThree_afterP111_isSmallP U hULegal hRemaining
  obtain ⟨T, hTLegal, hTableRaw⟩ :=
    R.threeThreeFerrersTable_exists F.pair F.view F.rotation
      F.upper_pos F.lower_neg
  have hTTable : F.TableHolds T := by
    simpa [HullSixThreeThreeGeometricFrame.TableHolds] using hTableRaw
  have hTSmall :
      HullSixThreeThreeGeometricFrame.IsSmallPExactPacket T :=
    hullSixThreeThree_smallP_of_exactTable_of_frontier
      F T U hTLegal hUSmall hTTable hUFrontier
  exact hullSixThreeThreeSmallPExactPacketProvider
    F T hTLegal hTSmall hTTable

/-- With the `2 + 4` side already unconditional, the final small-p provider
closes the direct hull-six semantic endpoint. -/
theorem geometricHullSixExclusion_of_completedDirectFrontiers :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_currentThreeThreeFrontierProvider
    hullSixThreeThreeSmallPResidualXFrontierProvider

end Heilbronn8
