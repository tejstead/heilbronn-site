import Heilbronn8.Survivors.Join.HullSixFerrersSymmetry

/-!
# The finite `2 x 4` Ferrers census

This file records exactly how far the two currently available adjacent
product-twelve lemmas cover the monotone `2 x 4` chamber tables.  A row with
cuts `(p,q)` is

```text
L^p M^(q-p) R^(4-q).
```

There are 76 legal labeled tables.  The local patterns `RR / LR` and
`LR / LL`, together with the separate hard table `MMRR / LLMM`, cover only
18 of them; 58 remain.  Thus this census deliberately does not assert a
scalar closure for the remaining tables.

All finite statements below are reduced by ordinary kernel `decide`.  There
is no native evaluation and no external certificate.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The four row cuts of a `2 x 4` Ferrers table.  A cut belongs to
`{0,1,2,3,4}` by construction. -/
structure HullSixTwoFourCuts where
  p0 : Fin 5
  p1 : Fin 5
  q0 : Fin 5
  q1 : Fin 5
  deriving DecidableEq, Fintype, Repr

namespace HullSixTwoFourCuts

/-- First cuts, indexed by the two rows. -/
def p (T : HullSixTwoFourCuts) : Fin 2 → ℕ :=
  ![T.p0.val, T.p1.val]

/-- Second cuts, indexed by the two rows. -/
def q (T : HullSixTwoFourCuts) : Fin 2 → ℕ :=
  ![T.q0.val, T.q1.val]

/-- The chamber table encoded by the four cuts. -/
def table (T : HullSixTwoFourCuts) :
    Fin 2 → Fin 4 → HullSixChamberLabel :=
  hullSixFerrersLabel T.p T.q

/-- The two cyclic boundary conditions in cut form: the bottom-left cell is
`L`, while the top-right cell is `R`. -/
@[reducible] def Boundaries (T : HullSixTwoFourCuts) : Prop :=
  (1 : Fin 5) ≤ T.p1 ∧ T.q0 ≤ (3 : Fin 5)

/-- Within-row cut legality, down-row nesting, and the cyclic boundaries. -/
@[reducible] def Legal (T : HullSixTwoFourCuts) : Prop :=
  T.p0 ≤ T.q0 ∧ T.p1 ≤ T.q1 ∧
  T.p0 ≤ T.p1 ∧ T.q0 ≤ T.q1 ∧ T.Boundaries

/-- The cut boundary conditions really give the named boundary cells. -/
theorem boundary_cells : ∀ T : HullSixTwoFourCuts, T.Legal →
    T.table (1 : Fin 2) (0 : Fin 4) = HullSixChamberLabel.L ∧
    T.table (0 : Fin 2) (3 : Fin 4) = HullSixChamberLabel.R := by
  decide

private def adjacentLeft (j : Fin 3) : Fin 4 :=
  ⟨j.val, by omega⟩

private def adjacentRight (j : Fin 3) : Fin 4 :=
  ⟨j.val + 1, by omega⟩

/-- Some adjacent columns have top row `RR` and bottom row `LR`. -/
@[reducible] def RRLR (T : HullSixTwoFourCuts) : Prop :=
  ∃ j : Fin 3,
    T.table (0 : Fin 2) (adjacentLeft j) = HullSixChamberLabel.R ∧
    T.table (0 : Fin 2) (adjacentRight j) = HullSixChamberLabel.R ∧
    T.table (1 : Fin 2) (adjacentLeft j) = HullSixChamberLabel.L ∧
    T.table (1 : Fin 2) (adjacentRight j) = HullSixChamberLabel.R

/-- Some adjacent columns have top row `LR` and bottom row `LL`. -/
@[reducible] def LRLL (T : HullSixTwoFourCuts) : Prop :=
  ∃ j : Fin 3,
    T.table (0 : Fin 2) (adjacentLeft j) = HullSixChamberLabel.L ∧
    T.table (0 : Fin 2) (adjacentRight j) = HullSixChamberLabel.R ∧
    T.table (1 : Fin 2) (adjacentLeft j) = HullSixChamberLabel.L ∧
    T.table (1 : Fin 2) (adjacentRight j) = HullSixChamberLabel.L

/-- The separate hard table `MMRR / LLMM`. -/
def hard : HullSixTwoFourCuts where
  p0 := 0
  p1 := 2
  q0 := 2
  q1 := 4

/-- Recognition of the separate hard table. -/
@[reducible] def IsHard (T : HullSixTwoFourCuts) : Prop :=
  T = hard

/-- Coverage supplied at present by the two local product-twelve patterns
and the one separately designated hard table. -/
@[reducible] def CurrentlyCovered (T : HullSixTwoFourCuts) : Prop :=
  T.RRLR ∨ T.LRLL ∨ T.IsHard

/-- A legal table not belonging to the current three-way coverage. -/
@[reducible] def Remaining (T : HullSixTwoFourCuts) : Prop :=
  T.Legal ∧ ¬ T.CurrentlyCovered

/-- Exact cut characterization of the `RR / LR` adjacent pattern. -/
theorem rrlr_iff_cuts : ∀ T : HullSixTwoFourCuts, T.Legal →
    (T.RRLR ↔
      T.p1 = T.q1 ∧ T.q0 < T.p1 ∧ T.p1 < (4 : Fin 5)) := by
  decide

/-- Exact cut characterization of the `LR / LL` adjacent pattern. -/
theorem lrll_iff_cuts : ∀ T : HullSixTwoFourCuts, T.Legal →
    (T.LRLL ↔
      T.p0 = T.q0 ∧ (0 : Fin 5) < T.p0 ∧ T.p0 < T.p1) := by
  decide

/-- Exact cut characterization of all currently covered legal tables. -/
theorem currentlyCovered_iff_cuts :
    ∀ T : HullSixTwoFourCuts, T.Legal →
      (T.CurrentlyCovered ↔
        (T.p1 = T.q1 ∧ T.q0 < T.p1 ∧ T.p1 < (4 : Fin 5)) ∨
        (T.p0 = T.q0 ∧ (0 : Fin 5) < T.p0 ∧ T.p0 < T.p1) ∨
        (T.p0 = 0 ∧ T.p1 = 2 ∧ T.q0 = 2 ∧ T.q1 = 4)) := by
  decide

/-- Exact cut characterization of the legal tables still requiring a
scalar argument. -/
theorem remaining_iff_cuts : ∀ T : HullSixTwoFourCuts,
    (T.Remaining ↔
      T.Legal ∧
      ¬ (T.p1 = T.q1 ∧ T.q0 < T.p1 ∧ T.p1 < (4 : Fin 5)) ∧
      ¬ (T.p0 = T.q0 ∧ (0 : Fin 5) < T.p0 ∧ T.p0 < T.p1) ∧
      ¬ (T.p0 = 0 ∧ T.p1 = 2 ∧ T.q0 = 2 ∧ T.q1 = 4)) := by
  decide

/-- All legal cut records. -/
def legalTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Legal

/-- Legal records covered by a local product or by the hard table. -/
def currentlyCoveredTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Legal ∧ T.CurrentlyCovered

/-- Legal records not yet covered. -/
def remainingTables : Finset HullSixTwoFourCuts :=
  Finset.univ.filter fun T ↦ T.Remaining

/-- There are exactly 76 legal labeled `2 x 4` Ferrers tables. -/
theorem legalTables_card : legalTables.card = 76 := by
  decide

/-- The two local patterns and the hard table cover exactly 18 legal
tables. -/
theorem currentlyCoveredTables_card : currentlyCoveredTables.card = 18 := by
  decide

/-- Exactly 58 legal tables remain outside the current coverage. -/
theorem remainingTables_card : remainingTables.card = 58 := by
  decide

/-- Complement a cut and reverse its four columns. -/
private def reverseCut (k : Fin 5) : Fin 5 :=
  ⟨4 - k.val, by omega⟩

/-- Rotate the table by 180 degrees and exchange `L` with `R`. -/
def rotateComplement (T : HullSixTwoFourCuts) : HullSixTwoFourCuts where
  p0 := reverseCut T.q1
  p1 := reverseCut T.q0
  q0 := reverseCut T.p1
  q1 := reverseCut T.p0

/-- The cut action agrees with complement-rotation of the chamber table. -/
theorem table_rotateComplement : ∀ T : HullSixTwoFourCuts, T.Legal →
    ∀ i j, T.rotateComplement.table i j =
      HullSixChamberLabel.complement
        (T.table (hullSixReverseFinTwo i) (hullSixReverseFinFour j)) := by
  decide

/-- Complement-rotation is an involution on cut records. -/
theorem rotateComplement_involutive : ∀ T : HullSixTwoFourCuts,
    T.rotateComplement.rotateComplement = T := by
  decide

/-- Complement-rotation preserves legality and the two boundary cells. -/
theorem legal_rotateComplement : ∀ T : HullSixTwoFourCuts,
    T.Legal → T.rotateComplement.Legal := by
  decide

/-- Rotation-complement exchanges the two adjacent local patterns. -/
theorem rrlr_rotateComplement_iff_lrll : ∀ T : HullSixTwoFourCuts,
    T.Legal → (T.rotateComplement.RRLR ↔ T.LRLL) := by
  decide

/-- The hard table is fixed by rotation-complement. -/
theorem rotateComplement_hard : hard.rotateComplement = hard := by
  decide

/-- Passing to rotation-complement orbits adds no current coverage. -/
theorem currentlyCovered_rotateComplement_iff :
    ∀ T : HullSixTwoFourCuts, T.Legal →
      (T.rotateComplement.CurrentlyCovered ↔ T.CurrentlyCovered) := by
  decide

/-- Consequently the remaining family is also symmetry invariant. -/
theorem remaining_rotateComplement_iff : ∀ T : HullSixTwoFourCuts,
    (T.rotateComplement.Remaining ↔ T.Remaining) := by
  decide

/-- A symmetry-fixed uncovered example whose two rows are `MRRR / LLLM`.
All four columns are strictly decreasing in the order `L < M < R`. -/
def strictCounterexample : HullSixTwoFourCuts where
  p0 := 0
  p1 := 3
  q0 := 1
  q1 := 4

theorem strictCounterexample_remaining : strictCounterexample.Remaining := by
  decide

theorem strictCounterexample_fixed :
    strictCounterexample.rotateComplement = strictCounterexample := by
  decide

end HullSixTwoFourCuts

end Heilbronn8
