import Mathlib

/-!
# Finite occupancy combinatorics for three points in a convex pentagon

The five diagonals of a strict convex pentagon cut its interior into eleven
open regions.  For one point, record which of the three triangles in each of
the five cyclic anchored fans contains it.  In cyclic anchor order the eleven
possible words are

`21002, 11012, 10022, 10121, 00221, 11111,`
`21101, 01211, 22100, 12110, 02210`.

This module contains only the resulting finite theorem.  The geometric module
which constructs a region witness is kept separate.  Exhausting three region
labels gives four and only four outcomes: a central `300` chart, an end-zero
`210` chart, a middle-zero `210` chart, or `111` at every anchor.

The check is ordinary kernel reduction over `11^3` triples.  It uses neither
native evaluation nor generated certificates.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Heilbronn8.TriHull

/-- The eleven open cells of the five-diagonal arrangement. -/
inductive HullFivePointRegion where
  | r21002
  | r11012
  | r10022
  | r10121
  | r00221
  | r11111
  | r21101
  | r01211
  | r22100
  | r12110
  | r02210
deriving Repr, DecidableEq

/-- Explicit enumeration.  The generic `Fintype` deriving handler in the
current Lean toolchain fails on this eleven-constructor type, so keep the
small kernel enumeration visible here. -/
instance : Fintype HullFivePointRegion where
  elems := {
    .r21002, .r11012, .r10022, .r10121, .r00221, .r11111,
    .r21101, .r01211, .r22100, .r12110, .r02210 }
  complete x := by cases x <;> simp

/-- The anchored-fan cell of one region at each cyclic anchor.

Cells `0,1,2` are respectively the first ear, middle triangle, and last ear
of the fan based at that anchor. -/
def HullFivePointRegion.fanCell :
    HullFivePointRegion → Fin 5 → Fin 3
  | .r21002 => ![2, 1, 0, 0, 2]
  | .r11012 => ![1, 1, 0, 1, 2]
  | .r10022 => ![1, 0, 0, 2, 2]
  | .r10121 => ![1, 0, 1, 2, 1]
  | .r00221 => ![0, 0, 2, 2, 1]
  | .r11111 => ![1, 1, 1, 1, 1]
  | .r21101 => ![2, 1, 1, 0, 1]
  | .r01211 => ![0, 1, 2, 1, 1]
  | .r22100 => ![2, 2, 1, 0, 0]
  | .r12110 => ![1, 2, 1, 1, 0]
  | .r02210 => ![0, 2, 2, 1, 0]

/-- The sole compatibility relation between the five anchored-fan cells of
one generic point.  Cell `0` at anchor `a` and cell `2` at anchor `a + 2`
are the same open ear, with its vertices cyclically permuted. -/
def HullFiveFanProfileCompatible (cell : Fin 5 → Fin 3) : Prop :=
  ∀ a : Fin 5, cell a = 0 ↔ cell (a + 2) = 2

/-- The eleven rows above are exactly all compatible five-anchor profiles.

This is the finite seam used by the geometric adapter: geometry only has to
construct one strict fan cell at each anchor and prove the shared-ear
equivalence.  No additional diagonal-arrangement census is needed. -/
theorem hullFiveFanProfile_region :
    ∀ cell : Fin 5 → Fin 3,
      HullFiveFanProfileCompatible cell →
        ∃ region : HullFivePointRegion, cell = region.fanCell := by
  let profileDec : DecidablePred (fun cell : Fin 5 → Fin 3 =>
      HullFiveFanProfileCompatible cell →
        ∃ region : HullFivePointRegion, cell = region.fanCell) :=
    fun cell =>
      letI : Decidable (HullFiveFanProfileCompatible cell) := by
        unfold HullFiveFanProfileCompatible
        infer_instance
      letI : Decidable (∃ region : HullFivePointRegion,
          cell = region.fanCell) := by
        infer_instance
      inferInstance
  letI := profileDec
  decide

/-- Ordered populations of one cyclic anchored fan. -/
structure HullFiveRegionCounts where
  first : Nat
  middle : Nat
  last : Nat
deriving Repr, DecidableEq

private def indicator (condition : Bool) : Nat :=
  if condition then 1 else 0

/-- Population vector at one anchor for three region labels. -/
def hullFiveRegionCounts
    (P Q R : HullFivePointRegion) (anchor : Fin 5) :
    HullFiveRegionCounts :=
  let count (cell : Fin 3) :=
    indicator (P.fanCell anchor == cell) +
      indicator (Q.fanCell anchor == cell) +
        indicator (R.fanCell anchor == cell)
  ⟨count 0, count 1, count 2⟩

/-- All three points occupy the middle (central-gap-type) fan triangle. -/
def HullFiveRegionCounts.IsCentral300
    (counts : HullFiveRegionCounts) : Prop :=
  counts = ⟨0, 3, 0⟩

/-- A `210` vector whose *last* cell is empty.

The finite dispatcher can always choose this orientation; the reflected
`021`/`012` forms are unnecessary.  This matches the two homogeneous
end-zero endpoint theorems directly and removes a reflection seam. -/
def HullFiveRegionCounts.IsEnd210
    (counts : HullFiveRegionCounts) : Prop :=
  counts = ⟨2, 1, 0⟩ ∨ counts = ⟨1, 2, 0⟩

/-- The two `210` vectors whose middle fan cell is empty. -/
def HullFiveRegionCounts.IsMiddle210
    (counts : HullFiveRegionCounts) : Prop :=
  counts = ⟨2, 0, 1⟩ ∨ counts = ⟨1, 0, 2⟩

/-- One point lies in each cell of the fan. -/
def HullFiveRegionCounts.Is111
    (counts : HullFiveRegionCounts) : Prop :=
  counts = ⟨1, 1, 1⟩

/-- The four topology classes needed by the metric hull-five closers. -/
def HullFiveRegionTripleOutcome
    (P Q R : HullFivePointRegion) : Prop :=
  (∃ anchor : Fin 5,
    (hullFiveRegionCounts P Q R anchor).IsCentral300) ∨
  (∃ anchor : Fin 5,
    (hullFiveRegionCounts P Q R anchor).IsEnd210) ∨
  (∃ anchor : Fin 5,
    (hullFiveRegionCounts P Q R anchor).IsMiddle210) ∨
  (∀ anchor : Fin 5,
    (hullFiveRegionCounts P Q R anchor).Is111)

/-- Exact four-way occupancy dispatch for three points.

In particular there is no residual `300`-ear case: if an anchored fan puts
all three points in one of its end ears, another cyclic anchor exposes either
a central `300` or an end-zero `210` chart. -/
theorem hullFivePointRegions_dispatch :
    ∀ P Q R : HullFivePointRegion,
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsCentral300) ∨
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsEnd210) ∨
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsMiddle210) ∨
      (∀ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).Is111) := by
  let outcomeDec (P Q R : HullFivePointRegion) :
      Decidable (HullFiveRegionTripleOutcome P Q R) := by
    unfold HullFiveRegionTripleOutcome
    letI : DecidablePred (fun anchor : Fin 5 =>
        (hullFiveRegionCounts P Q R anchor).IsCentral300) :=
      fun _ => by unfold HullFiveRegionCounts.IsCentral300; infer_instance
    letI : Decidable (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsCentral300) :=
      Fintype.decidableExistsFintype
    letI : DecidablePred (fun anchor : Fin 5 =>
        (hullFiveRegionCounts P Q R anchor).IsEnd210) :=
      fun _ => by unfold HullFiveRegionCounts.IsEnd210; infer_instance
    letI : Decidable (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsEnd210) :=
      Fintype.decidableExistsFintype
    letI : DecidablePred (fun anchor : Fin 5 =>
        (hullFiveRegionCounts P Q R anchor).IsMiddle210) :=
      fun _ => by unfold HullFiveRegionCounts.IsMiddle210; infer_instance
    letI : Decidable (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsMiddle210) :=
      Fintype.decidableExistsFintype
    letI : DecidablePred (fun anchor : Fin 5 =>
        (hullFiveRegionCounts P Q R anchor).Is111) :=
      fun _ => by unfold HullFiveRegionCounts.Is111; infer_instance
    letI : Decidable (∀ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).Is111) :=
      Fintype.decidableForallFintype
    infer_instance
  let tripleDec : DecidablePred (fun P : HullFivePointRegion =>
      ∀ Q R : HullFivePointRegion,
        HullFiveRegionTripleOutcome P Q R) :=
    fun P =>
      letI : DecidablePred (fun Q : HullFivePointRegion =>
          ∀ R : HullFivePointRegion,
            HullFiveRegionTripleOutcome P Q R) :=
        fun Q =>
          letI : DecidablePred (fun R : HullFivePointRegion =>
              HullFiveRegionTripleOutcome P Q R) :=
            outcomeDec P Q
          Fintype.decidableForallFintype
      Fintype.decidableForallFintype
  letI := tripleDec
  change ∀ P Q R : HullFivePointRegion,
    HullFiveRegionTripleOutcome P Q R
  decide

theorem hullFivePointRegions_outcome
    (P Q R : HullFivePointRegion) :
    HullFiveRegionTripleOutcome P Q R := by
  simpa [HullFiveRegionTripleOutcome] using
    hullFivePointRegions_dispatch P Q R

#print axioms hullFivePointRegions_dispatch

end Heilbronn8.TriHull
