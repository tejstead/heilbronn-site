import Heilbronn8.Survivors.Join.HullSixTwoFourFiniteCensus

/-!
# The residual `2 x 4` complement-rotation quotient

`HullSixTwoFourFiniteCensus` leaves 58 labeled tables after removing the two
adjacent product-twelve families and the separately closed hard table
`MMRR / LLMM`.  This file records the exact quotient of those 58 tables by
the complement-rotation involution.

The base-five code is injective because every cut is a member of `Fin 5`.
Choosing the smaller code in each two-element orbit gives 32 representatives:
26 representatives of paired tables and six symmetry-fixed representatives.
All cardinality statements use ordinary kernel `decide`.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixTwoFourCuts

/-- An injective base-five code for the four cuts. -/
def orbitCode (T : HullSixTwoFourCuts) : Nat :=
  ((T.p0.val * 5 + T.p1.val) * 5 + T.q0.val) * 5 + T.q1.val

/-- The canonical member of a remaining complement-rotation orbit is the
member with smaller base-five code.  A fixed point is included once. -/
@[reducible] def IsRemainingOrbitRepresentative
    (T : HullSixTwoFourCuts) : Prop :=
  T.Remaining ∧ T.orbitCode ≤ T.rotateComplement.orbitCode

/-- Canonical representatives of the remaining complement-rotation orbits. -/
def remainingOrbitRepresentatives : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.IsRemainingOrbitRepresentative

/-- Remaining tables fixed by complement-rotation. -/
def remainingFixedTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Remaining ∧ T.rotateComplement = T

/-- Remaining tables belonging to a nontrivial two-element orbit. -/
def remainingNonfixedTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Remaining ∧ T.rotateComplement ≠ T

/-- The 58 residual labeled tables form exactly 32 complement-rotation
orbits. -/
theorem remainingOrbitRepresentatives_card :
    remainingOrbitRepresentatives.card = 32 := by
  decide

/-- Six residual tables are fixed by complement-rotation. -/
theorem remainingFixedTables_card : remainingFixedTables.card = 6 := by
  decide

/-- The other 52 residual tables form 26 two-element orbits. -/
theorem remainingNonfixedTables_card : remainingNonfixedTables.card = 52 := by
  decide

/-- Burnside accounting for the residual involution. -/
theorem remaining_orbit_burnside_count :
    2 * remainingOrbitRepresentatives.card =
      remainingTables.card + remainingFixedTables.card := by
  rw [remainingOrbitRepresentatives_card, remainingTables_card,
    remainingFixedTables_card]

end HullSixTwoFourCuts
end Heilbronn8
