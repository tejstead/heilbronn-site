import Heilbronn8.Survivors.Join.HullSixTwoFourP22Q22Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP11MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP12MaximalQGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourP02Q22Geometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindQ22Geometry

/-!
# The maximal-q `p = (2,2)` frontier

The retained `X` frontier recovers the first cuts of the canonical exact
Ferrers table.  There are then only five legal exact tables.  The
`2222` table is closed directly; the other four are transported through the
honestly reflected frame and consumed there by the exact `p02/q22` and
q-blind `q22` closers or weakened to the existing `p11` and `p12` maximal
frontiers.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-- The maximal-q frontier record with first cuts `p = (2,2)`. -/
def HullSixTwoFourIsP22MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 2 ∧ T.p1 = 2

/-- Finite census of legal exact tables whose first cuts are `p = (2,2)`. -/
private theorem p22_exact_cases :
    ∀ T : HullSixTwoFourCuts, T.Legal → T.p0 = 2 → T.p1 = 2 →
      T = ⟨2, 2, 2, 2⟩ ∨
      T = ⟨2, 2, 2, 3⟩ ∨
      T = ⟨2, 2, 2, 4⟩ ∨
      T = ⟨2, 2, 3, 3⟩ ∨
      T = ⟨2, 2, 3, 4⟩ := by
  decide

namespace HullSixTwoFourGeometricFrame

/-- The `p = (2,2)` maximal-q frontier is impossible.  Its actual exact
Ferrers table is reconstructed first, so every reflection transports a
complete physical table rather than a partial sign packet. -/
theorem twoFourP22MaximalQAt_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (W : HullSixTwoFourCuts) (hp0 : W.p0 = 2) (hp1 : W.p1 = 2)
    (hFrontier : F.XFrontierHolds W) :
    False := by
  obtain ⟨T, hTLegal, hTableRaw⟩ :=
    R.twoFourFerrersTable_exists F.pair F.view F.rotation
      F.upper_pos F.lower_neg
  have hTable : F.TableHolds T := by
    simpa [TableHolds] using hTableRaw

  /- Recover the exact first cuts from the retained `X` signs.  Raising only
  the second cuts to their maxima gives the exact table's strong `X`
  frontier without consulting any hidden `Y` sign. -/
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

  have hTp0 : T.p0 = 2 := by
    have hge : 2 ≤ T.p0.val := by
      by_contra hnot
      have hpos := hGivenLeft (0 : Fin 2) (1 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, hp0])
      have hneg := hExactNeg (0 : Fin 2) (1 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, Ttop]
        omega)
      linarith
    have hle : T.p0.val ≤ 2 := by
      by_contra hnot
      have hpos := hExactLeft (0 : Fin 2) (2 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, Ttop]
        omega)
      have hneg := hGivenNeg (0 : Fin 2) (2 : Fin 4) (by
        simp [HullSixTwoFourCuts.p, hp0])
      linarith
    apply Fin.ext
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

  rcases p22_exact_cases T hTLegal hTp0 hTp1 with
    h22 | h23 | h24 | h33 | h34
  · subst T
    exact F.twoFourP22Q22At_false hTable
  · subst T
    let F' := F.reflectedRotateComplement
    let S12 : HullSixTwoFourCuts := ⟨1, 2, 2, 2⟩
    let U12 : HullSixTwoFourCuts := ⟨1, 2, 3, 4⟩
    have hSourceLegal : (⟨2, 2, 2, 3⟩ : HullSixTwoFourCuts).Legal := by
      decide
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hSourceLegal hTable
    have hRotate :
        (⟨2, 2, 2, 3⟩ : HullSixTwoFourCuts).rotateComplement = S12 := by
      decide
    rw [hRotate] at hReflected
    have hSTable : F'.TableHolds S12 := by
      simpa [F'] using hReflected
    have hSLegal : S12.Legal := by decide
    have hULegal : U12.Legal := by decide
    have hWeak : HullSixTwoFourCuts.Weak S12 U12 := by decide
    have hFrontier12 : F'.XFrontierHolds U12 :=
      F'.xFrontierHolds_of_table_weak hSLegal hWeak hSTable
    have hPacket12 : HullSixTwoFourIsP12MaximalQFrontier U12 := by
      simp [HullSixTwoFourIsP12MaximalQFrontier,
        HullSixTwoFourIsMaximalQFrontier, U12]
    exact hullSixTwoFourP12MaximalQFrontierProvider
      F' U12 hULegal hPacket12 hFrontier12
  · subst T
    let F' := F.reflectedRotateComplement
    let S02 : HullSixTwoFourCuts := HullSixTwoFourP02Q22Cuts
    have hSourceLegal : (⟨2, 2, 2, 4⟩ : HullSixTwoFourCuts).Legal := by
      decide
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hSourceLegal hTable
    have hRotate :
        (⟨2, 2, 2, 4⟩ : HullSixTwoFourCuts).rotateComplement = S02 := by
      decide
    rw [hRotate] at hReflected
    have hSTable : F'.TableHolds S02 := by
      simpa [F'] using hReflected
    have hSLegal : S02.Legal := by decide
    have hPacket : HullSixTwoFourIsExactP02Q22 S02 := by
      simp [S02, HullSixTwoFourIsExactP02Q22]
    exact hullSixTwoFourP02Q22ExactPacketProvider
      F' S02 hSLegal hPacket hSTable
  · subst T
    let F' := F.reflectedRotateComplement
    let S11 : HullSixTwoFourCuts := ⟨1, 1, 2, 2⟩
    let U11 : HullSixTwoFourCuts := ⟨1, 1, 3, 4⟩
    have hSourceLegal : (⟨2, 2, 3, 3⟩ : HullSixTwoFourCuts).Legal := by
      decide
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hSourceLegal hTable
    have hRotate :
        (⟨2, 2, 3, 3⟩ : HullSixTwoFourCuts).rotateComplement = S11 := by
      decide
    rw [hRotate] at hReflected
    have hSTable : F'.TableHolds S11 := by
      simpa [F'] using hReflected
    have hSLegal : S11.Legal := by decide
    have hULegal : U11.Legal := by decide
    have hWeak : HullSixTwoFourCuts.Weak S11 U11 := by decide
    have hFrontier11 : F'.XFrontierHolds U11 :=
      F'.xFrontierHolds_of_table_weak hSLegal hWeak hSTable
    have hPacket11 : HullSixTwoFourIsP11MaximalQFrontier U11 := by
      simp [HullSixTwoFourIsP11MaximalQFrontier,
        HullSixTwoFourIsMaximalQFrontier, U11]
    exact hullSixTwoFourP11MaximalQFrontierProvider
      F' U11 hULegal hPacket11 hFrontier11
  · subst T
    let F' := F.reflectedRotateComplement
    have hSourceLegal : (⟨2, 2, 3, 4⟩ : HullSixTwoFourCuts).Legal := by
      decide
    have hReflected :=
      F.tableHolds_reflectedRotateComplement hSourceLegal hTable
    have hRotate :
        (⟨2, 2, 3, 4⟩ : HullSixTwoFourCuts).rotateComplement =
          HullSixTwoFourCuts.qBlind22 := by
      decide
    rw [hRotate] at hReflected
    have hSTable : F'.TableHolds HullSixTwoFourCuts.qBlind22 := by
      simpa [F'] using hReflected
    exact (R.reflectReverse F.rotation).twoFourQBlindQ22At_false
      F'.view F'.rotation F'.upper_pos F'.lower_neg
      (by simpa [TableHolds] using hSTable)

end HullSixTwoFourGeometricFrame

/-- Global provider for the maximal-q `p = (2,2)` fibre. -/
theorem hullSixTwoFourP22MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider
      HullSixTwoFourIsP22MaximalQFrontier := by
  intro cfg cycle p q R F T _hLegal hPacket hFrontier
  exact F.twoFourP22MaximalQAt_false
    T hPacket.2.1 hPacket.2.2 hFrontier

end Heilbronn8
