import Mathlib

/-!
# Finite symmetries of hull-six Ferrers tableaux

This file contains only the finite chamber-label transport.  It does not
assert that an arbitrary labeled tableau is geometrically realizable.

For a cross chord write `X` for its determinant based at `P` and `Y` for the
determinant based at `Q`.  Both geometric symmetries used in the hull-six
normalization act on a suitably reindexed cell by

```text
(X,Y) |-> (-Y,-X).
```

Thus `L` and `R` are exchanged and `M` is fixed.  On a `2 x 4` tableau,
cyclic reversal followed by orientation restoration is complement-rotation
by 180 degrees.  On a square `3 x 3` tableau, complement-transposition is the
second involution; together the two maps form the expected Klein four action.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Data-valued version of the three cross-chord chambers. -/
inductive HullSixChamberLabel
  | L
  | M
  | R
  deriving DecidableEq, Repr

namespace HullSixChamberLabel

/-- The inequalities represented by a chamber label. -/
def Holds (tag : HullSixChamberLabel) (m x y : ℝ) : Prop :=
  match tag with
  | L => m ≤ x
  | M => x ≤ -m ∧ m ≤ y
  | R => y ≤ -m

/-- Exchange the two exterior chambers. -/
def complement : HullSixChamberLabel → HullSixChamberLabel
  | L => R
  | M => M
  | R => L

@[simp] theorem complement_complement (tag : HullSixChamberLabel) :
    complement (complement tag) = tag := by
  cases tag <;> rfl

/-- Exact chamber transport under `(X,Y) |-> (-Y,-X)`. -/
theorem holds_complement_neg_swap_iff
    (tag : HullSixChamberLabel) (m x y : ℝ) :
    Holds (complement tag) m (-y) (-x) ↔ Holds tag m x y := by
  cases tag with
  | L =>
      simp only [complement, Holds]
      constructor <;> intro h <;> linarith
  | M =>
      simp only [complement, Holds]
      constructor
      · rintro ⟨hy, hx⟩
        constructor <;> linarith
      · rintro ⟨hx, hy⟩
        constructor <;> linarith
  | R =>
      simp only [complement, Holds]
      constructor <;> intro h <;> linarith

end HullSixChamberLabel

/-- Row-cut encoding `L^p M^(q-p) R^(s-q)`.  Legality and monotonicity of
the cuts are deliberately separate propositions. -/
def hullSixFerrersLabel {r s : ℕ} (p q : Fin r → ℕ)
    (i : Fin r) (j : Fin s) : HullSixChamberLabel :=
  if j.val < p i then HullSixChamberLabel.L
  else if j.val < q i then HullSixChamberLabel.M
  else HullSixChamberLabel.R

/-- The elementary within-row cut conditions. -/
def HullSixFerrersCutsLegal {r s : ℕ}
    (p q : Fin r → ℕ) : Prop :=
  ∀ i, p i ≤ q i ∧ q i ≤ s

/-- The down-row nesting condition supplied by Plucker sign propagation. -/
def HullSixFerrersCutsMonotone {r : ℕ}
    (p q : Fin r → ℕ) : Prop :=
  Monotone p ∧ Monotone q

/-- Complement-transpose, the scalar action of exchanging the two base
points and then using the opposite sign block as the upper block. -/
def hullSixComplementTranspose {r s : ℕ}
    (T : Fin r → Fin s → HullSixChamberLabel) :
    Fin s → Fin r → HullSixChamberLabel :=
  fun j i => HullSixChamberLabel.complement (T i j)

@[simp] theorem hullSixComplementTranspose_involutive
    {r s : ℕ} (T : Fin r → Fin s → HullSixChamberLabel) :
    hullSixComplementTranspose (hullSixComplementTranspose T) = T := by
  funext i j
  simp [hullSixComplementTranspose]

def hullSixReverseFinTwo (i : Fin 2) : Fin 2 :=
  ⟨1 - i.val, by omega⟩

def hullSixReverseFinThree (i : Fin 3) : Fin 3 :=
  ⟨2 - i.val, by omega⟩

def hullSixReverseFinFour (i : Fin 4) : Fin 4 :=
  ⟨3 - i.val, by omega⟩

@[simp] theorem hullSixReverseFinTwo_involutive (i : Fin 2) :
    hullSixReverseFinTwo (hullSixReverseFinTwo i) = i := by
  apply Fin.ext
  simp only [hullSixReverseFinTwo]
  omega

@[simp] theorem hullSixReverseFinThree_involutive (i : Fin 3) :
    hullSixReverseFinThree (hullSixReverseFinThree i) = i := by
  apply Fin.ext
  simp only [hullSixReverseFinThree]
  omega

@[simp] theorem hullSixReverseFinFour_involutive (i : Fin 4) :
    hullSixReverseFinFour (hullSixReverseFinFour i) = i := by
  apply Fin.ext
  simp only [hullSixReverseFinFour]
  omega

/-- The same-shape involution on a `2 x 4` chamber table. -/
def hullSixTwoFourRotateComplement
    (T : Fin 2 → Fin 4 → HullSixChamberLabel) :
    Fin 2 → Fin 4 → HullSixChamberLabel :=
  fun i j => HullSixChamberLabel.complement
    (T (hullSixReverseFinTwo i) (hullSixReverseFinFour j))

@[simp] theorem hullSixTwoFourRotateComplement_involutive
    (T : Fin 2 → Fin 4 → HullSixChamberLabel) :
    hullSixTwoFourRotateComplement
      (hullSixTwoFourRotateComplement T) = T := by
  funext i j
  simp [hullSixTwoFourRotateComplement]

/-- Complement-rotation by 180 degrees on a square table. -/
def hullSixThreeThreeRotateComplement
    (T : Fin 3 → Fin 3 → HullSixChamberLabel) :
    Fin 3 → Fin 3 → HullSixChamberLabel :=
  fun i j => HullSixChamberLabel.complement
    (T (hullSixReverseFinThree i) (hullSixReverseFinThree j))

@[simp] theorem hullSixThreeThreeRotateComplement_involutive
    (T : Fin 3 → Fin 3 → HullSixChamberLabel) :
    hullSixThreeThreeRotateComplement
      (hullSixThreeThreeRotateComplement T) = T := by
  funext i j
  simp [hullSixThreeThreeRotateComplement]

/-- Complement-transposition specialized to the square chamber. -/
abbrev hullSixThreeThreeComplementTranspose
    (T : Fin 3 → Fin 3 → HullSixChamberLabel) :
    Fin 3 → Fin 3 → HullSixChamberLabel :=
  hullSixComplementTranspose T

/-- The two square-table involutions commute. -/
theorem hullSixThreeThree_symmetry_commute
    (T : Fin 3 → Fin 3 → HullSixChamberLabel) :
    hullSixThreeThreeRotateComplement
        (hullSixThreeThreeComplementTranspose T) =
      hullSixThreeThreeComplementTranspose
        (hullSixThreeThreeRotateComplement T) := by
  funext i j
  simp [hullSixThreeThreeRotateComplement,
    hullSixThreeThreeComplementTranspose, hullSixComplementTranspose]

end Heilbronn8
