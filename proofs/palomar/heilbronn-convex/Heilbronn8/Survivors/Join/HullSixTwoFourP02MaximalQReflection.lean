import Heilbronn8.Survivors.Join.HullSixTwoFourExactOrbitSemanticProvider
import Heilbronn8.Survivors.Join.HullSixTwoFourP03MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP04MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP11MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP12MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP13MaximalQGeometry

/-!
# The maximal-q `p = (0,2)` frontier by honest reflection

An oriented frame canonically determines its actual legal exact Ferrers
table.  The retained `X` frontier forces that table to have first cuts
`p = (0,2)`.  Native exact tables are closed in place.  Every remaining
table is physically reflected using `reflectedRotateComplement`; reflected
native tables are closed there, and the six residual reflected first-cut
fibres weaken in that same reflected frame to their maximal-q providers.

The `p = (2,2)` provider is an explicit argument so this module has no
dependency on its eventual implementation.  No abstract same-frame symmetry
custody and no hidden same-frame table transport is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-- The maximal-q frontier record with first cuts `p = (0,2)`. -/
def HullSixTwoFourIsP02MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 0 ∧ T.p1 = 2

/-- Local callback predicate for the not-yet-imported `p = (2,2)` provider. -/
def HullSixTwoFourP02NeedsP22Frontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 2 ∧ T.p1 = 2

/-- Finite residual census after fixing `p = (0,2)` and removing native
tables in both physical orientations. -/
private theorem p02_reflected_residual_firstCuts :
    ∀ T : HullSixTwoFourCuts, T.Legal →
      T.p0 = 0 → T.p1 = 2 →
      ¬T.IsExactNative → ¬T.rotateComplement.IsExactNative →
      (T.rotateComplement.p0 = 0 ∧ T.rotateComplement.p1 = 3) ∨
      (T.rotateComplement.p0 = 0 ∧ T.rotateComplement.p1 = 4) ∨
      (T.rotateComplement.p0 = 1 ∧ T.rotateComplement.p1 = 1) ∨
      (T.rotateComplement.p0 = 1 ∧ T.rotateComplement.p1 = 2) ∨
      (T.rotateComplement.p0 = 1 ∧ T.rotateComplement.p1 = 3) ∨
      (T.rotateComplement.p0 = 2 ∧ T.rotateComplement.p1 = 2) := by
  letI : DecidablePred fun T : HullSixTwoFourCuts =>
      T.Legal →
      T.p0 = 0 → T.p1 = 2 →
      ¬T.IsExactNative → ¬T.rotateComplement.IsExactNative →
      (T.rotateComplement.p0 = 0 ∧ T.rotateComplement.p1 = 3) ∨
      (T.rotateComplement.p0 = 0 ∧ T.rotateComplement.p1 = 4) ∨
      (T.rotateComplement.p0 = 1 ∧ T.rotateComplement.p1 = 1) ∨
      (T.rotateComplement.p0 = 1 ∧ T.rotateComplement.p1 = 2) ∨
      (T.rotateComplement.p0 = 1 ∧ T.rotateComplement.p1 = 3) ∨
      (T.rotateComplement.p0 = 2 ∧ T.rotateComplement.p1 = 2) :=
    fun T => by
      letI : Decidable T.IsExactNative := inferInstance
      letI : Decidable T.rotateComplement.IsExactNative := inferInstance
      exact inferInstance
  decide

namespace HullSixTwoFourGeometricFrame

/-- Parameterized frame-level closure of the `p02` maximal-q frontier.
The only open callback is the reflected `p22` maximal-q provider. -/
theorem twoFourP02MaximalQAt_false_of_p22Provider
    (hP22 : HullSixTwoFourXFrontierProvider
      HullSixTwoFourP02NeedsP22Frontier)
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (W : HullSixTwoFourCuts) (hp0 : W.p0 = 0) (hp1 : W.p1 = 2)
    (hFrontier : F.XFrontierHolds W) :
    False := by
  obtain ⟨T, hTLegal, hTableRaw⟩ :=
    R.twoFourFerrersTable_exists F.pair F.view F.rotation
      F.upper_pos F.lower_neg
  have hTable : F.TableHolds T := by
    simpa [HullSixTwoFourGeometricFrame.TableHolds] using hTableRaw

  /- Recover the exact first cuts from the retained `X` signs.  Passing
  through `xFrontierHolds_of_table_weak` supplies the strong negative bound
  even when an exact cell is tagged `R`. -/
  let Ttop : HullSixTwoFourCuts := ⟨T.p0, T.p1, 3, 4⟩
  have hTWeak : HullSixTwoFourCuts.Weak T Ttop := by
    rcases hTLegal with ⟨_hp0q0, _hp1q1, _hp, _hq, hbound⟩
    rcases hbound with ⟨_hp1, hq0⟩
    dsimp [HullSixTwoFourCuts.Weak, Ttop]
    constructor
    · rfl
    constructor
    · rfl
    constructor <;> omega
  have hExactFrontier : F.XFrontierHolds Ttop :=
    F.xFrontierHolds_of_table_weak hTLegal hTWeak hTable
  change HullSixQBlindFrontierHolds W.p W.q (minTri cfg) F.X at hFrontier
  change HullSixQBlindFrontierHolds Ttop.p Ttop.q (minTri cfg) F.X at hExactFrontier
  rcases hFrontier with ⟨hGivenLeft, hGivenNeg, _hGivenStrong⟩
  rcases hExactFrontier with ⟨hExactLeft, hExactNeg, _hExactStrong⟩
  have hm : 0 < minTri cfg := R.minTri_pos

  have hTp0 : T.p0 = 0 := by
    apply Fin.ext
    have hle : T.p0.val ≤ 0 := by
      by_contra hnot
      have hpos := hExactLeft (0 : Fin 2) (0 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, Ttop]
        omega)
      have hneg := hGivenNeg (0 : Fin 2) (0 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, hp0])
      linarith
    omega
  have hTp1 : T.p1 = 2 := by
    have hge : 2 ≤ T.p1.val := by
      by_contra hnot
      have hpos := hGivenLeft (1 : Fin 2) (1 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, hp1])
      have hneg := hExactNeg (1 : Fin 2) (1 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, Ttop]
        omega)
      linarith
    have hle : T.p1.val ≤ 2 := by
      by_contra hnot
      have hpos := hExactLeft (1 : Fin 2) (2 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, Ttop]
        omega)
      have hneg := hGivenNeg (1 : Fin 2) (2 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, hp1])
      linarith
    apply Fin.ext
    omega

  by_cases hTNative : T.IsExactNative
  · exact hullSixTwoFourExactNativeProvider F T hTLegal hTNative hTable

  let F' := F.reflectedRotateComplement
  let S : HullSixTwoFourCuts := T.rotateComplement
  have hSLegal : S.Legal := by
    simpa [S] using HullSixTwoFourCuts.legal_rotateComplement T hTLegal
  have hSTable : F'.TableHolds S := by
    have h := F.tableHolds_reflectedRotateComplement hTLegal hTable
    simpa [F', S] using h

  by_cases hSNative : S.IsExactNative
  · exact hullSixTwoFourExactNativeProvider F' S hSLegal hSNative hSTable

  have hResidualCases :
      (S.p0 = 0 ∧ S.p1 = 3) ∨
      (S.p0 = 0 ∧ S.p1 = 4) ∨
      (S.p0 = 1 ∧ S.p1 = 1) ∨
      (S.p0 = 1 ∧ S.p1 = 2) ∨
      (S.p0 = 1 ∧ S.p1 = 3) ∨
      (S.p0 = 2 ∧ S.p1 = 2) := by
    simpa [S] using p02_reflected_residual_firstCuts
      T hTLegal hTp0 hTp1 hTNative (by simpa [S] using hSNative)

  let U : HullSixTwoFourCuts := ⟨S.p0, S.p1, 3, 4⟩
  have hWeak : HullSixTwoFourCuts.Weak S U := by
    rcases hSLegal with ⟨_hp0q0, _hp1q1, _hp, _hq, hbound⟩
    rcases hbound with ⟨_hp1, hq0⟩
    dsimp [HullSixTwoFourCuts.Weak, U]
    constructor
    · rfl
    constructor
    · rfl
    constructor <;> omega
  have hULegal : U.Legal := by
    rcases hSLegal with ⟨hp0q0, hp1q1, hp, _hq, hbound⟩
    rcases hbound with ⟨hp1, hq0⟩
    dsimp [HullSixTwoFourCuts.Legal, HullSixTwoFourCuts.Boundaries, U]
    omega
  have hUFrontier : F'.XFrontierHolds U :=
    F'.xFrontierHolds_of_table_weak hSLegal hWeak hSTable
  have hUMax : HullSixTwoFourIsMaximalQFrontier U := by
    simp [HullSixTwoFourIsMaximalQFrontier, U]

  rcases hResidualCases with h03 | h04 | h11 | h12 | h13 | h22
  · have hPacket : HullSixTwoFourIsP03MaximalQFrontier U := by
      exact ⟨hUMax, by simpa [U] using h03.1,
        by simpa [U] using h03.2⟩
    exact hullSixTwoFourP03MaximalQFrontierProvider
      F' U hULegal hPacket hUFrontier
  · have hPacket : HullSixTwoFourIsP04MaximalQFrontier U := by
      exact ⟨hUMax, by simpa [U] using h04.1,
        by simpa [U] using h04.2⟩
    exact hullSixTwoFourP04MaximalQFrontierProvider
      F' U hULegal hPacket hUFrontier
  · have hPacket : HullSixTwoFourIsP11MaximalQFrontier U := by
      exact ⟨hUMax, by simpa [U] using h11.1,
        by simpa [U] using h11.2⟩
    exact hullSixTwoFourP11MaximalQFrontierProvider
      F' U hULegal hPacket hUFrontier
  · have hPacket : HullSixTwoFourIsP12MaximalQFrontier U := by
      exact ⟨hUMax, by simpa [U] using h12.1,
        by simpa [U] using h12.2⟩
    exact hullSixTwoFourP12MaximalQFrontierProvider
      F' U hULegal hPacket hUFrontier
  · have hPacket : HullSixTwoFourIsP13MaximalQFrontier U := by
      exact ⟨hUMax, by simpa [U] using h13.1,
        by simpa [U] using h13.2⟩
    exact hullSixTwoFourP13MaximalQFrontierProvider
      F' U hULegal hPacket hUFrontier
  · have hPacket : HullSixTwoFourP02NeedsP22Frontier U := by
      exact ⟨hUMax, by simpa [U] using h22.1,
        by simpa [U] using h22.2⟩
    exact hP22 F' U hULegal hPacket hUFrontier

end HullSixTwoFourGeometricFrame

/-- Parameterized global provider for the maximal-q `p02` fibre. -/
theorem hullSixTwoFourP02MaximalQFrontierProvider_of_p22
    (hP22 : HullSixTwoFourXFrontierProvider
      HullSixTwoFourP02NeedsP22Frontier) :
    HullSixTwoFourXFrontierProvider HullSixTwoFourIsP02MaximalQFrontier := by
  intro cfg cycle p q R F T _hLegal hPacket hFrontier
  exact F.twoFourP02MaximalQAt_false_of_p22Provider hP22
    T hPacket.2.1 hPacket.2.2 hFrontier

end Heilbronn8
