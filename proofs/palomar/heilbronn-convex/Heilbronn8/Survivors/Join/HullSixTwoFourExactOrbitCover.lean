import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCases

/-!
# Exact native and reflected `2 x 4` census

This is a finite statement only.  It records the exact tables handled by a
native adapter, their complement-rotation images, and one canonical member
of each remaining two-element orbit.  It does not assert geometric custody
or metric closure for the residual representatives.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixTwoFourCuts

/-- The exact native union supplied by wide, hard, and full `p=(0,1)`
geometry adapters. -/
@[reducible] def IsExactNative (T : HullSixTwoFourCuts) : Prop :=
  T.HasWideProductTwelve ∨ T.IsHard ∨ (T.p0 = 0 ∧ T.p1 = 1)

/-- A legal table not covered natively or by reflecting a native table. -/
@[reducible] def IsExactResidual (T : HullSixTwoFourCuts) : Prop :=
  T.Legal ∧ ¬IsExactNative T ∧ ¬IsExactNative T.rotateComplement

/-- A numeric code used only to choose one representative of a finite
complement-rotation orbit. -/
def exactOrbitCode (T : HullSixTwoFourCuts) : Nat :=
  ((T.p0.val * 5 + T.p1.val) * 5 + T.q0.val) * 5 + T.q1.val

/-- The code-minimal member of a residual complement-rotation orbit. -/
@[reducible] def IsExactResidualRep (T : HullSixTwoFourCuts) : Prop :=
  T.IsExactResidual ∧ T.exactOrbitCode ≤ T.rotateComplement.exactOrbitCode

def exactNativeTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Legal ∧ T.IsExactNative

def exactNativeOrReflectedTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦
    T.Legal ∧ (T.IsExactNative ∨ T.rotateComplement.IsExactNative)

def exactResidualTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter IsExactResidual

def exactResidualRepTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter IsExactResidualRep

/-- Exactly 36 of the 76 legal tables have native exact adapters. -/
theorem exactNativeTables_card : exactNativeTables.card = 36 := by
  decide

/-- Exact complement-rotation adds nine nonnative tables. -/
theorem exactNativeOrReflectedTables_card :
    exactNativeOrReflectedTables.card = 45 := by
  decide

/-- Thirty-one exact tables remain after the native and reflected union. -/
theorem exactResidualTables_card : exactResidualTables.card = 31 := by
  decide

/-- Those thirty-one tables form eighteen complement-rotation orbits. -/
theorem exactResidualRepTables_card : exactResidualRepTables.card = 18 := by
  decide

/-- Every legal table is native, reflected-native, a chosen residual
representative, or the reflection of one. -/
theorem exact_native_or_reflected_or_residualRep :
    ∀ T : HullSixTwoFourCuts, T.Legal →
      T.IsExactNative ∨ T.rotateComplement.IsExactNative ∨
      T.IsExactResidualRep ∨ T.rotateComplement.IsExactResidualRep := by
  letI : DecidablePred fun T : HullSixTwoFourCuts => T.Legal →
      T.IsExactNative ∨ T.rotateComplement.IsExactNative ∨
      T.IsExactResidualRep ∨ T.rotateComplement.IsExactResidualRep :=
    fun T => by
      letI : Decidable T.Legal := inferInstance
      letI : Decidable T.IsExactNative := inferInstance
      letI : Decidable T.rotateComplement.IsExactNative := inferInstance
      letI : Decidable T.IsExactResidualRep := inferInstance
      letI : Decidable T.rotateComplement.IsExactResidualRep := inferInstance
      exact inferInstance
  decide

end HullSixTwoFourCuts
end Heilbronn8
