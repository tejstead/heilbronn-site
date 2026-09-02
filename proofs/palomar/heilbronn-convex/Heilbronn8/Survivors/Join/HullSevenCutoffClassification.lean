import Heilbronn8.HullSevenOrderTypes

/-!
# Universal finite classifier for a seven-wheel

Fix a strictly counterclockwise seven-cycle `C` and a point `P` in its
interior.  Looking forward from an anchor `C i`, the six signs

`sig (C i) (C (i+d)) P`, `d = 1, ..., 6`,

form a nonempty proper positive prefix.  Write its last positive index as
`k i ∈ {1, ..., 5}`.  Reversing a chord negates its sign, so the two
directed tests on every unordered chord have opposite Boolean values.

This file defines the purely finite cutoff language.  The compact structural
classification theorem is in `HullSevenCutoffReduction`; it reconstructs
every admissible cutoff from two Boolean masks and checks only `2^14` inputs.
No retained corpus or generated certificate enters the computation.

The geometric half is deliberately a separate seam: it must prove the
positive-prefix assertion from strict cyclicity and genuine interior
custody before applying `hullSevenCutoff_classification`.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000

/-- A value of `Fin 5` stores a cutoff in `{1, ..., 5}` after adding one. -/
def hullSevenCutoffAt (cuts : Fin 7 → Fin 5) (anchor : Nat) : Nat :=
  (cuts ⟨anchor % 7, Nat.mod_lt _ (by decide)⟩).val + 1

/-- Forward cyclic distance on seven positions. -/
def hullSevenForwardDistance (left right : Nat) : Nat :=
  (right % 7 + 7 - left % 7) % 7

/-- The directed chord `left → right` is positive precisely when its
forward distance lies in the positive prefix at `left`. -/
def hullSevenCutoffDirectedPositive
    (cuts : Fin 7 → Fin 5) (left right : Nat) : Bool :=
  decide (hullSevenForwardDistance left right ≤
    hullSevenCutoffAt cuts left)

/-- Chord reversal must complement all 42 directed signs. -/
def HullSevenCutoffComplementary (cuts : Fin 7 → Fin 5) : Prop :=
  ∀ left : Fin 7, ∀ offset : Fin 6,
    let right := left.val + offset.val + 1
    hullSevenCutoffDirectedPositive cuts left.val right ≠
      hullSevenCutoffDirectedPositive cuts right left.val

def hullSevenCutoffComplementOK (cuts : Fin 7 → Fin 5) : Bool :=
  (List.ofFn fun left : Fin 7 =>
    (List.ofFn fun offset : Fin 6 =>
      let right := left.val + offset.val + 1
      hullSevenCutoffDirectedPositive cuts left.val right !=
        hullSevenCutoffDirectedPositive cuts right left.val).all id).all id

theorem hullSevenCutoffComplementOK_eq_true_iff
    (cuts : Fin 7 → Fin 5) :
    hullSevenCutoffComplementOK cuts = true ↔
      HullSevenCutoffComplementary cuts := by
  unfold hullSevenCutoffComplementOK HullSevenCutoffComplementary
  rw [List.all_eq_true, List.forall_mem_ofFn_iff]
  constructor
  · intro h left
    have hleft := h left
    change (List.ofFn fun offset : Fin 6 =>
      let right := left.val + offset.val + 1
      hullSevenCutoffDirectedPositive cuts left.val right !=
        hullSevenCutoffDirectedPositive cuts right left.val).all id = true at hleft
    rw [List.all_eq_true, List.forall_mem_ofFn_iff] at hleft
    intro offset
    simpa using hleft offset
  · intro h left
    change (List.ofFn fun offset : Fin 6 =>
      let right := left.val + offset.val + 1
      hullSevenCutoffDirectedPositive cuts left.val right !=
        hullSevenCutoffDirectedPositive cuts right left.val).all id = true
    rw [List.all_eq_true, List.forall_mem_ofFn_iff]
    intro offset
    simpa using h left offset

/-- Vertex `index` in one of the fourteen dihedral presentations. -/
def hullSevenCutoffPresentationVertex
    (rotation index : Nat) (reflected : Bool) : Nat :=
  if reflected then (rotation + 7 - index) % 7
  else (rotation + index) % 7

/-- The normalized 21-bit key of one presentation.  Reflection reverses the
orientation of the first three vertices, hence complements every raw chord
sign in exactly the same way as `hullSevenPresentationKey`. -/
def hullSevenCutoffPresentationKey (cuts : Fin 7 → Fin 5)
    (rotation : Nat) (reflected : Bool) : List Bool :=
  hullSevenPairIndices.map fun pair =>
    let left :=
      hullSevenCutoffPresentationVertex rotation pair.1 reflected
    let right :=
      hullSevenCutoffPresentationVertex rotation pair.2 reflected
    let raw := hullSevenCutoffDirectedPositive cuts left right
    if reflected then !raw else raw

/-- Dihedral canonical key associated with a cutoff function. -/
def hullSevenCutoffOrderType (cuts : Fin 7 → Fin 5) : List Bool :=
  leastBoolList <|
    (List.range 7).flatMap fun rotation =>
      [hullSevenCutoffPresentationKey cuts rotation false,
        hullSevenCutoffPresentationKey cuts rotation true]

/-- One cutoff representative for each of the eight canonical keys.  Entries
are stored zero-based; the mathematical cutoffs are obtained by adding one.

The representatives are respectively
`1155432`, `1254432`, `1354332`, `2224443`,
`2234433`, `2324343`, `2334333`, and `3333333`. -/
def HullSevenType.cutoffRepresentative : HullSevenType → Fin 7 → Fin 5
  | .type0 => ![0, 0, 4, 4, 3, 2, 1]
  | .type1 => ![0, 1, 4, 3, 3, 2, 1]
  | .type2 => ![0, 2, 4, 3, 2, 2, 1]
  | .type3 => ![1, 1, 1, 3, 3, 3, 2]
  | .type4 => ![1, 1, 2, 3, 3, 2, 2]
  | .type5 => ![1, 2, 1, 3, 2, 3, 2]
  | .type6 => ![1, 2, 2, 3, 2, 2, 2]
  | .type7 => ![2, 2, 2, 2, 2, 2, 2]

/-- The displayed representatives satisfy every reversal constraint. -/
theorem HullSevenType.cutoffRepresentative_complementOK
    (orderType : HullSevenType) :
    hullSevenCutoffComplementOK orderType.cutoffRepresentative = true := by
  cases orderType <;> decide

/-- The representative-to-key mapping is definitionally independent of the
retained bank and checks the intended numbering of the eight constructors. -/
theorem HullSevenType.cutoffRepresentative_orderType
    (orderType : HullSevenType) :
    hullSevenCutoffOrderType orderType.cutoffRepresentative =
      orderType.key := by
  cases orderType <;> decide

/-- Number of labelled cutoff functions obeying chord reversal.  The value is
57, but the direct final route does not ask the kernel to enumerate `5^7`
functions merely to establish that census fact. -/
def hullSevenAdmissibleCutoffCount : Nat :=
  ((Finset.univ : Finset (Fin 7 → Fin 5)).filter fun cuts =>
    hullSevenCutoffComplementOK cuts = true).card

end Heilbronn8
