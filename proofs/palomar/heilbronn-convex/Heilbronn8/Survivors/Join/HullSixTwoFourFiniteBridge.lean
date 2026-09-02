import Heilbronn8.Survivors.Join.HullSixTwoFourFiniteCensus

/-!
# A one-frontier finite bridge for `2 x 4`

Fixing the first cuts and increasing the second cuts turns `R` cells into
`M` cells without changing any `X`-sign.  Modulo complement-rotation, every
legal `2 x 4` Ferrers table reaches the single table

```text
M M M R
L M M M
```

in at most two such weakening steps.  Seven explicit intermediate orbit
representatives suffice.  The theorem at the end is deliberately abstract:
once a coupled q-blind scalar lemma closes this top table, symmetry and
weakening close all 76 legal labels.  No claim about that scalar lemma is
made here.

The finite statement is checked by ordinary kernel `decide` over the 625
four-cut records; no native evaluation or external certificate is used.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8
namespace HullSixTwoFourCuts

/-- The two geometric orientations needed for the `2 x 4` bridge. -/
inductive Symmetry
  | identity
  | rotateComplement
  deriving DecidableEq, Repr

@[reducible] instance : Fintype Symmetry where
  elems := {.identity, .rotateComplement}
  complete := by
    intro g
    cases g <;> simp

/-- Action of the two orientations on cut records. -/
def act : Symmetry → HullSixTwoFourCuts → HullSixTwoFourCuts
  | .identity, T => T
  | .rotateComplement, T => T.rotateComplement

/-- Both orientations preserve legality. -/
theorem legal_act : ∀ (g : Symmetry) (T : HullSixTwoFourCuts),
    T.Legal → (act g T).Legal := by
  decide

/-- Increase only the second cuts. -/
@[reducible] def Weak (T U : HullSixTwoFourCuts) : Prop :=
  T.p0 = U.p0 ∧ T.p1 = U.p1 ∧ T.q0 ≤ U.q0 ∧ T.q1 ≤ U.q1

/-- One weakening step, allowing independent orientations at its ends. -/
@[reducible] def OrbitStep (T U : HullSixTwoFourCuts) : Prop :=
  ∃ g h : Symmetry, Weak (act g T) (act h U)

private def cuts (p0 p1 q0 q1 : Fin 5) : HullSixTwoFourCuts :=
  ⟨p0, p1, q0, q1⟩

/-- The unique q-blind top, with rows `MMMR / LMMM`. -/
def qBlindTop : HullSixTwoFourCuts := cuts 0 1 3 4

private def middleMMMRLLLL : HullSixTwoFourCuts := cuts 0 1 0 4
private def middleLMMRLLLM : HullSixTwoFourCuts := cuts 0 1 1 3
private def middleMMMRLLLM : HullSixTwoFourCuts := cuts 0 1 1 4
private def middleLLMRLLMM : HullSixTwoFourCuts := cuts 0 1 2 2
private def middleLMMRLLMM : HullSixTwoFourCuts := cuts 0 1 2 3
private def middleMMMRLLMM : HullSixTwoFourCuts := cuts 0 1 2 4
private def middleLMMRLMMM : HullSixTwoFourCuts := cuts 0 1 3 3

/-- Seven intermediate orbit representatives cover all distance-two cases. -/
@[reducible] def IsBridgeMiddle (T : HullSixTwoFourCuts) : Prop :=
  T = middleMMMRLLLL ∨ T = middleLMMRLLLM ∨
  T = middleMMMRLLLM ∨ T = middleLLMRLLMM ∨
  T = middleLMMRLLMM ∨ T = middleMMMRLLMM ∨
  T = middleLMMRLMMM

/-- The exact finite alternative used by the abstract closer. -/
@[reducible] def ReachesQBlindTop (T : HullSixTwoFourCuts) : Prop :=
  OrbitStep T qBlindTop ∨
    ∃ U, IsBridgeMiddle U ∧ OrbitStep T U ∧ OrbitStep U qBlindTop

/-- Every legal table reaches the q-blind top in at most two weakening
steps, modulo complement-rotation. -/
theorem finiteBridge : ∀ T : HullSixTwoFourCuts,
    T.Legal → T.ReachesQBlindTop := by
  decide

/-- Propagate an abstract chamber-closing predicate through one orbit step. -/
theorem closed_of_orbitStep
    (Closed : HullSixTwoFourCuts → Prop)
    (hSymmetry : ∀ g T, Closed (act g T) ↔ Closed T)
    (hWeak : ∀ T U, Weak T U → Closed U → Closed T)
    {T U : HullSixTwoFourCuts} (hstep : OrbitStep T U)
    (hU : Closed U) : Closed T := by
  obtain ⟨g, h, hweak⟩ := hstep
  have hActU : Closed (act h U) := (hSymmetry h U).2 hU
  have hActT : Closed (act g T) := hWeak _ _ hweak hActU
  exact (hSymmetry g T).1 hActT

/-- Logical endpoint: a symmetry-invariant, q-weakening-stable scalar
closure at `MMMR / LMMM` closes every legal `2 x 4` table. -/
theorem closed_of_qBlindTop
    (Closed : HullSixTwoFourCuts → Prop)
    (hSymmetry : ∀ g T, Closed (act g T) ↔ Closed T)
    (hWeak : ∀ T U, Weak T U → Closed U → Closed T)
    (hTop : Closed qBlindTop)
    (T : HullSixTwoFourCuts) (hLegal : T.Legal) : Closed T := by
  rcases finiteBridge T hLegal with hOne | hTwo
  · exact closed_of_orbitStep Closed hSymmetry hWeak hOne hTop
  · obtain ⟨U, _hMiddle, hTU, hUTop⟩ := hTwo
    have hU : Closed U :=
      closed_of_orbitStep Closed hSymmetry hWeak hUTop hTop
    exact closed_of_orbitStep Closed hSymmetry hWeak hTU hU

end HullSixTwoFourCuts
end Heilbronn8
