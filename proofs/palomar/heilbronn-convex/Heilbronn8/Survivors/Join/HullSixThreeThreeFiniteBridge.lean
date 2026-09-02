import Heilbronn8.Survivors.Join.HullSixFerrersSymmetry

/-!
# The finite `3 x 3` Ferrers bridge

There are 136 legal labeled `3 x 3` Ferrers tables and 42 orbits under the
two geometric involutions.  This file records the small logical bridge used
by the coupled scalar proof:

* `001 / 233` is the exceptional broad table;
* after removing it, `011 / 233` is the unique top table for fixed-first-cut
  weakening, modulo the four symmetries;
* every other orbit reaches that top in at most two weakening steps.

The census is kernel-reduced with ordinary `decide`; it does not use
native evaluation or an external certificate.  The abstract closing theorem at
the end depends only on symmetry invariance, weakening, and the two scalar
top lemmas, so it is independent of their unfinished algebraic proofs.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Heilbronn8

/-- Six row-cut digits for a `3 x 3` Ferrers table.  Each digit is in
`{0,1,2,3}` by construction. -/
structure HullSixThreeThreeCuts where
  p0 : Fin 4
  p1 : Fin 4
  p2 : Fin 4
  q0 : Fin 4
  q1 : Fin 4
  q2 : Fin 4
  deriving DecidableEq, Fintype, Repr

namespace HullSixThreeThreeCuts

/-- First row cut, as a function suitable for `hullSixFerrersLabel`. -/
def p (T : HullSixThreeThreeCuts) : Fin 3 → ℕ :=
  ![T.p0.val, T.p1.val, T.p2.val]

/-- Second row cut, as a function suitable for `hullSixFerrersLabel`. -/
def q (T : HullSixThreeThreeCuts) : Fin 3 → ℕ :=
  ![T.q0.val, T.q1.val, T.q2.val]

/-- The corresponding chamber table. -/
def table (T : HullSixThreeThreeCuts) :
    Fin 3 → Fin 3 → HullSixChamberLabel :=
  hullSixFerrersLabel T.p T.q

/-- Ferrers legality, including the two cyclic boundary cells: the bottom
left cell is `L` and the top right cell is `R`. -/
@[reducible] def Legal (T : HullSixThreeThreeCuts) : Prop :=
  T.p0 ≤ T.p1 ∧ T.p1 ≤ T.p2 ∧
  T.q0 ≤ T.q1 ∧ T.q1 ≤ T.q2 ∧
  T.p0 ≤ T.q0 ∧ T.p1 ≤ T.q1 ∧ T.p2 ≤ T.q2 ∧
  (1 : Fin 4) ≤ T.p2 ∧ T.q0 ≤ (2 : Fin 4)

private def boolCountThree (a b c : Bool) : Fin 4 :=
  ⟨(if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0), by
    cases a <;> cases b <;> cases c <;> decide⟩

private def countPGe (T : HullSixThreeThreeCuts) (k : ℕ) : Fin 4 :=
  boolCountThree (decide (k ≤ T.p0.val)) (decide (k ≤ T.p1.val))
    (decide (k ≤ T.p2.val))

private def countQGe (T : HullSixThreeThreeCuts) (k : ℕ) : Fin 4 :=
  boolCountThree (decide (k ≤ T.q0.val)) (decide (k ≤ T.q1.val))
    (decide (k ≤ T.q2.val))

private def countPLe (T : HullSixThreeThreeCuts) (k : ℕ) : Fin 4 :=
  boolCountThree (decide (T.p0.val ≤ k)) (decide (T.p1.val ≤ k))
    (decide (T.p2.val ≤ k))

private def countQLe (T : HullSixThreeThreeCuts) (k : ℕ) : Fin 4 :=
  boolCountThree (decide (T.q0.val ≤ k)) (decide (T.q1.val ≤ k))
    (decide (T.q2.val ≤ k))

/-- Anti-transposition.  On row cuts it counts entries above each reversed
column threshold. -/
def antiTranspose (T : HullSixThreeThreeCuts) : HullSixThreeThreeCuts where
  p0 := countPGe T 3
  p1 := countPGe T 2
  p2 := countPGe T 1
  q0 := countQGe T 3
  q1 := countQGe T 2
  q2 := countQGe T 1

/-- Complement-transposition.  Its first cut counts the old second-cut
entries below the new row, and conversely. -/
def complementTranspose
    (T : HullSixThreeThreeCuts) : HullSixThreeThreeCuts where
  p0 := countQLe T 0
  p1 := countQLe T 1
  p2 := countQLe T 2
  q0 := countPLe T 0
  q1 := countPLe T 1
  q2 := countPLe T 2

/-- The four-element symmetry group, represented only by the actions needed
by the finite bridge. -/
inductive Symmetry
  | identity
  | antiTranspose
  | complementTranspose
  | rotateComplement
  deriving DecidableEq, Repr

/-- Explicit four-element enumeration.  Keeping this instance transparent
avoids relying on the derived enum-list machinery in the finite census. -/
@[reducible] instance : Fintype Symmetry where
  elems := {.identity, .antiTranspose, .complementTranspose, .rotateComplement}
  complete := by
    intro g
    cases g <;> simp

/-- Action of the Klein four symmetries on row cuts. -/
def act : Symmetry → HullSixThreeThreeCuts → HullSixThreeThreeCuts
  | .identity, T => T
  | .antiTranspose, T => T.antiTranspose
  | .complementTranspose, T => T.complementTranspose
  | .rotateComplement, T => T.complementTranspose.antiTranspose

/-- The cut formula for anti-transposition agrees pointwise with the chamber
table action. -/
theorem table_antiTranspose : ∀ (T : HullSixThreeThreeCuts), T.Legal →
    ∀ i j : Fin 3, T.antiTranspose.table i j =
      T.table (hullSixReverseFinThree j) (hullSixReverseFinThree i) := by
  decide

/-- The cut formula for complement-transposition agrees pointwise with the
data-valued chamber action. -/
theorem table_complementTranspose :
    ∀ (T : HullSixThreeThreeCuts), T.Legal → ∀ i j : Fin 3,
      T.complementTranspose.table i j =
        HullSixChamberLabel.complement (T.table j i) := by
  decide

/-- The fourth cut action is complement-rotation by 180 degrees. -/
theorem table_rotateComplement :
    ∀ (T : HullSixThreeThreeCuts), T.Legal → ∀ i j : Fin 3,
      (act .rotateComplement T).table i j =
        HullSixChamberLabel.complement
          (T.table (hullSixReverseFinThree i)
            (hullSixReverseFinThree j)) := by
  decide

/-- All four finite actions preserve the Ferrers and boundary conditions. -/
theorem legal_act : ∀ (g : Symmetry) (T : HullSixThreeThreeCuts),
    T.Legal → (act g T).Legal := by
  decide

/-- Increase only the second cuts.  Geometrically this turns some `R` cells
into `M` cells while preserving the first-cut `X` signs. -/
@[reducible] def Weak (T U : HullSixThreeThreeCuts) : Prop :=
  T.p0 = U.p0 ∧ T.p1 = U.p1 ∧ T.p2 = U.p2 ∧
  T.q0 ≤ U.q0 ∧ T.q1 ≤ U.q1 ∧ T.q2 ≤ U.q2

/-- Equality up to one of the four orientations. -/
@[reducible] def OrbitEq (T U : HullSixThreeThreeCuts) : Prop :=
  ∃ g : Symmetry, act g T = U

/-- One q-weakening step, allowing independent orientations at its ends. -/
@[reducible] def OrbitStep (T U : HullSixThreeThreeCuts) : Prop :=
  ∃ g h : Symmetry, Weak (act g T) (act h U)

private def cuts (p0 p1 p2 q0 q1 q2 : Fin 4) :
    HullSixThreeThreeCuts :=
  ⟨p0, p1, p2, q0, q1, q2⟩

/-- The exceptional seven-middle-cell table `001 / 233`. -/
def broad : HullSixThreeThreeCuts := cuts 0 0 1 2 3 3

/-- The q-blind six-middle-cell frontier `011 / 233`. -/
def qBlindTop : HullSixThreeThreeCuts := cuts 0 1 1 2 3 3

private def middle012223 : HullSixThreeThreeCuts := cuts 0 1 2 2 2 3
private def middle022223 : HullSixThreeThreeCuts := cuts 0 2 2 2 2 3
private def middle111223 : HullSixThreeThreeCuts := cuts 1 1 1 2 2 3
private def middle112133 : HullSixThreeThreeCuts := cuts 1 1 2 1 3 3
private def middle111133 : HullSixThreeThreeCuts := cuts 1 1 1 1 3 3

/-- The only five intermediate orbit representatives required by the
sixteen distance-two certificates. -/
@[reducible] def IsBridgeMiddle (T : HullSixThreeThreeCuts) : Prop :=
  T = middle012223 ∨ T = middle022223 ∨ T = middle111223 ∨
  T = middle112133 ∨ T = middle111133

/-- The exact finite alternative used by the abstract closing theorem. -/
@[reducible] def ReachesTwoTops (T : HullSixThreeThreeCuts) : Prop :=
  OrbitEq T broad ∨ OrbitStep T qBlindTop ∨
    ∃ U, IsBridgeMiddle U ∧ OrbitStep T U ∧ OrbitStep U qBlindTop

/- Exhaustive finite census: every legal table is broad, reaches the
q-blind top in one step, or reaches it through one of five explicit middle
representatives.  Ordinary kernel `decide` checks 4096 six-digit records;
legality leaves the documented 136 tables. -/
set_option maxRecDepth 100000 in
theorem finiteBridge : ∀ T : HullSixThreeThreeCuts,
    T.Legal → T.ReachesTwoTops := by
  decide

/-- Abstract propagation of any chamber-closing predicate through one
orbit-weakening step. -/
theorem closed_of_orbitStep
    (Closed : HullSixThreeThreeCuts → Prop)
    (hSymmetry : ∀ g T, Closed (act g T) ↔ Closed T)
    (hWeak : ∀ T U, Weak T U → Closed U → Closed T)
    {T U : HullSixThreeThreeCuts} (hstep : OrbitStep T U)
    (hU : Closed U) : Closed T := by
  obtain ⟨g, h, hweak⟩ := hstep
  have hActU : Closed (act h U) := (hSymmetry h U).2 hU
  have hActT : Closed (act g T) := hWeak _ _ hweak hActU
  exact (hSymmetry g T).1 hActT

/-- Logical endpoint of the finite bridge.  Once the broad and q-blind top
scalar lemmas are supplied, symmetry and q-weakening close all 136 legal
Ferrers tables. -/
theorem closed_of_broad_and_qBlindTop
    (Closed : HullSixThreeThreeCuts → Prop)
    (hSymmetry : ∀ g T, Closed (act g T) ↔ Closed T)
    (hWeak : ∀ T U, Weak T U → Closed U → Closed T)
    (hBroad : Closed broad) (hQBlind : Closed qBlindTop)
    (T : HullSixThreeThreeCuts) (hLegal : T.Legal) : Closed T := by
  rcases finiteBridge T hLegal with hBroadOrbit | hOne | hTwo
  · obtain ⟨g, hg⟩ := hBroadOrbit
    have hAct : Closed (act g T) := by simpa [hg] using hBroad
    exact (hSymmetry g T).1 hAct
  · exact closed_of_orbitStep Closed hSymmetry hWeak hOne hQBlind
  · obtain ⟨U, _hMiddle, hTU, hUTop⟩ := hTwo
    have hU : Closed U :=
      closed_of_orbitStep Closed hSymmetry hWeak hUTop hQBlind
    exact closed_of_orbitStep Closed hSymmetry hWeak hTU hU

end HullSixThreeThreeCuts

end Heilbronn8
