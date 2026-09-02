import Heil6.AnchorOrder

set_option linter.style.header false

/-!
# Compact finite interface for the n=6 hull split

For six points in general position the convex hull has 3, 4, 5, or 6
vertices.  This file records the packet interface and proves the complete
relabeling theorem from the two determinant identities in `PlanarDet`.  The
finite step works on the twenty orientation bits themselves; it neither
imports nor generates an order-type database.
-/

namespace N6Scratch
namespace FiniteHullCases

open PlanarDet

/-- Coordinate form of membership in a closed triangle. -/
def InTri (p a b c : ℝ × ℝ) : Prop :=
  ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 1 ∧
    p = x • a + y • b + z • c

/-- `w` is obtained from `v` by a permutation of its six labels. -/
def Relabels (v w : Fin 6 → ℝ × ℝ) : Prop :=
  ∃ e : Equiv.Perm (Fin 6), w = fun i ↦ v (e i)

/-- The only general-position property needed by the hull classifier. -/
def NoDegenerateTriple6 (v : Fin 6 → ℝ × ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    sig (v i) (v j) (v k) ≠ 0

/-- The triangle-floor interface consumed by every scalar hull case. -/
def DistinctTriangleFloor (v : Fin 6 → ℝ × ℝ) (m : ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    m ≤ |sig (v i) (v j) (v k)|

structure Hull3Packet (w : Fin 6 → ℝ × ℝ) : Prop where
  h012 : 0 < sig (w 0) (w 1) (w 2)
  h3 : InTri (w 3) (w 0) (w 1) (w 2)
  h4 : InTri (w 4) (w 0) (w 1) (w 2)
  h5 : InTri (w 5) (w 0) (w 1) (w 2)

structure Hull4Packet (w : Fin 6 → ℝ × ℝ) : Prop where
  h012 : 0 < sig (w 0) (w 1) (w 2)
  h013 : 0 < sig (w 0) (w 1) (w 3)
  h023 : 0 < sig (w 0) (w 2) (w 3)
  h123 : 0 < sig (w 1) (w 2) (w 3)
  h4 : InTri (w 4) (w 0) (w 1) (w 2) ∨
    InTri (w 4) (w 0) (w 2) (w 3)
  h5 : InTri (w 5) (w 0) (w 1) (w 2) ∨
    InTri (w 5) (w 0) (w 2) (w 3)

structure Hull5Packet (w : Fin 6 → ℝ × ℝ) : Prop where
  hullStrict : ∀ i j k : Fin 5, i < j → j < k →
    0 < sig (w i.castSucc) (w j.castSucc) (w k.castSucc)
  fan01 : 0 < sig (w 5) (w 0) (w 1)
  fan12 : 0 < sig (w 5) (w 1) (w 2)
  fan23 : 0 < sig (w 5) (w 2) (w 3)
  fan34 : 0 < sig (w 5) (w 3) (w 4)
  fan40 : 0 < sig (w 5) (w 4) (w 0)
  /-- A finite fan witness for membership of the sixth point in the pentagon.
  Keeping this witness in the packet makes the later convex-hull volume
  adapter independent of any polygon-membership API. -/
  insideFan : InTri (w 5) (w 0) (w 1) (w 2) ∨
    InTri (w 5) (w 0) (w 2) (w 3) ∨
    InTri (w 5) (w 0) (w 3) (w 4)

structure Hull6Packet (w : Fin 6 → ℝ × ℝ) : Prop where
  strict : ∀ i j k : Fin 6, i < j → j < k →
    0 < sig (w i) (w j) (w k)

def CanonicalHullCase6 (w : Fin 6 → ℝ × ℝ) : Prop :=
  Hull3Packet w ∨ Hull4Packet w ∨ Hull5Packet w ∨ Hull6Packet w

/-! ## A compact affine-oriented-matroid classifier

There are only twenty unordered triples of six labels.  Rather than import a
polygon library (or a generated order-type database), we remember one bit for
each increasing triple.  Alternation supplies every ordered orientation.  Two
short sign axioms are forced respectively by `PlanarDet.cocycle` and
`PlanarDet.plucker`.  After choosing a supporting anchor and sorting the other
five points by slope, the ten triples through the anchor are positive.  The
kernel-checked finite lemma below therefore exhausts only the remaining ten
bits; it has no native evaluation, external certificate, or data file.
-/

/-- Increasing triples of labels.  As a subtype of a finite type this carries
a computable `Fintype`; its cardinality is twenty. -/
abbrev SortedTriple6 :=
  {t : Fin 6 × Fin 6 × Fin 6 // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

private def sortedFirst (t : SortedTriple6) : Fin 6 := t.1.1
private def sortedSecond (t : SortedTriple6) : Fin 6 := t.1.2.1
private def sortedThird (t : SortedTriple6) : Fin 6 := t.1.2.2

/-- Alternating extension of a sign table on increasing triples.  The final
branch is reached only when two labels coincide; all uses below have distinct
labels. -/
def orientPositive (χ : SortedTriple6 → Bool) (i j k : Fin 6) : Bool :=
  if h : i < j ∧ j < k then
    χ ⟨(i, j, k), h⟩
  else if h : i < k ∧ k < j then
    Bool.not (χ ⟨(i, k, j), h⟩)
  else if h : j < i ∧ i < k then
    Bool.not (χ ⟨(j, i, k), h⟩)
  else if h : j < k ∧ k < i then
    χ ⟨(j, k, i), h⟩
  else if h : k < i ∧ i < j then
    χ ⟨(k, i, j), h⟩
  else if h : k < j ∧ j < i then
    Bool.not (χ ⟨(k, j, i), h⟩)
  else
    false

def Positive (χ : SortedTriple6 → Bool) (i j k : Fin 6) : Prop :=
  orientPositive χ i j k = true

instance (χ : SortedTriple6 → Bool) (i j k : Fin 6) :
    Decidable (Positive χ i j k) := by
  unfold Positive
  infer_instance

def InsideSigns (χ : SortedTriple6 → Bool)
    (p a b c : Fin 6) : Prop :=
  Positive χ a b p ∧ Positive χ b c p ∧ Positive χ c a p

instance (χ : SortedTriple6 → Bool) (p a b c : Fin 6) :
    Decidable (InsideSigns χ p a b c) := by
  unfold InsideSigns
  infer_instance

def Distinct4 (a b c d : Fin 6) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

instance (a b c d : Fin 6) : Decidable (Distinct4 a b c d) := by
  unfold Distinct4
  infer_instance

def Distinct5 (a b c d e : Fin 6) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
  b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e

instance (a b c d e : Fin 6) : Decidable (Distinct5 a b c d e) := by
  unfold Distinct5
  infer_instance

def SameSign (χ : SortedTriple6 → Bool)
    (a b c d e f : Fin 6) : Prop :=
  (Positive χ a b c ↔ Positive χ d e f)

instance (χ : SortedTriple6 → Bool) (a b c d e f : Fin 6) :
    Decidable (SameSign χ a b c d e f) := by
  unfold SameSign
  infer_instance

/-- One sign consequence of the affine four-point cocycle
`pqs + qrs - pqr - prs = 0`. -/
def AffineCocycleClause (χ : SortedTriple6 → Bool)
    (p q r s : Fin 6) : Prop :=
  ¬ ((Positive χ p q s ∧ Positive χ q r s ∧
        ¬ Positive χ p q r ∧ ¬ Positive χ p r s) ∨
     (¬ Positive χ p q s ∧ ¬ Positive χ q r s ∧
        Positive χ p q r ∧ Positive χ p r s))

instance (χ : SortedTriple6 → Bool) (p q r s : Fin 6) :
    Decidable (AffineCocycleClause χ p q r s) := by
  unfold AffineCocycleClause
  infer_instance

/-- The fifteen cocycle clauses on the increasing four-subsets of `Fin 6`.
Writing this small list explicitly prevents the kernel checker from traversing
all `6^4` ordered tuples for every sign table. -/
def AffineCocycleSigns6 (χ : SortedTriple6 → Bool) : Prop :=
  AffineCocycleClause χ 0 1 2 3 ∧
  AffineCocycleClause χ 0 1 2 4 ∧
  AffineCocycleClause χ 0 1 2 5 ∧
  AffineCocycleClause χ 0 1 3 4 ∧
  AffineCocycleClause χ 0 1 3 5 ∧
  AffineCocycleClause χ 0 1 4 5 ∧
  AffineCocycleClause χ 0 2 3 4 ∧
  AffineCocycleClause χ 0 2 3 5 ∧
  AffineCocycleClause χ 0 2 4 5 ∧
  AffineCocycleClause χ 0 3 4 5 ∧
  AffineCocycleClause χ 1 2 3 4 ∧
  AffineCocycleClause χ 1 2 3 5 ∧
  AffineCocycleClause χ 1 2 4 5 ∧
  AffineCocycleClause χ 1 3 4 5 ∧
  AffineCocycleClause χ 2 3 4 5

instance (χ : SortedTriple6 → Bool) :
    Decidable (AffineCocycleSigns6 χ) := by
  unfold AffineCocycleSigns6
  infer_instance

/-- One sign consequence of the three-term Grassmann--Pluecker identity,
with `a` as its shared pivot. -/
def GrassmannPluckerClause (χ : SortedTriple6 → Bool)
    (a b c d e : Fin 6) : Prop :=
  let t₁ := SameSign χ a b c a d e
  let t₂ := ¬ SameSign χ a b d a c e
  let t₃ := SameSign χ a b e a c d
  ¬ ((t₁ ∧ t₂ ∧ t₃) ∨ (¬ t₁ ∧ ¬ t₂ ∧ ¬ t₃))

instance (χ : SortedTriple6 → Bool) (a b c d e : Fin 6) :
    Decidable (GrassmannPluckerClause χ a b c d e) := by
  unfold GrassmannPluckerClause
  infer_instance

/-- The twenty-five nontrivial canonical Pluecker clauses.  On each
five-subset containing the distinguished anchor `0`, the clause with pivot
`0` is tautological once all anchor triples are positive, so we retain the
other four pivots.  On `{1,2,3,4,5}` we retain all five pivots.  These clauses
alone permit exactly the 62 realizable anchored sign tables; the affine
cocycle clauses are therefore redundant in the finite decision below. -/
def GrassmannPluckerSigns6 (χ : SortedTriple6 → Bool) : Prop :=
  GrassmannPluckerClause χ 1 0 2 3 4 ∧
  GrassmannPluckerClause χ 2 0 1 3 4 ∧
  GrassmannPluckerClause χ 3 0 1 2 4 ∧
  GrassmannPluckerClause χ 4 0 1 2 3 ∧
  GrassmannPluckerClause χ 1 0 2 3 5 ∧
  GrassmannPluckerClause χ 2 0 1 3 5 ∧
  GrassmannPluckerClause χ 3 0 1 2 5 ∧
  GrassmannPluckerClause χ 5 0 1 2 3 ∧
  GrassmannPluckerClause χ 1 0 2 4 5 ∧
  GrassmannPluckerClause χ 2 0 1 4 5 ∧
  GrassmannPluckerClause χ 4 0 1 2 5 ∧
  GrassmannPluckerClause χ 5 0 1 2 4 ∧
  GrassmannPluckerClause χ 1 0 3 4 5 ∧
  GrassmannPluckerClause χ 3 0 1 4 5 ∧
  GrassmannPluckerClause χ 4 0 1 3 5 ∧
  GrassmannPluckerClause χ 5 0 1 3 4 ∧
  GrassmannPluckerClause χ 2 0 3 4 5 ∧
  GrassmannPluckerClause χ 3 0 2 4 5 ∧
  GrassmannPluckerClause χ 4 0 2 3 5 ∧
  GrassmannPluckerClause χ 5 0 2 3 4 ∧
  GrassmannPluckerClause χ 1 2 3 4 5 ∧
  GrassmannPluckerClause χ 2 1 3 4 5 ∧
  GrassmannPluckerClause χ 3 1 2 4 5 ∧
  GrassmannPluckerClause χ 4 1 2 3 5 ∧
  GrassmannPluckerClause χ 5 1 2 3 4

instance (χ : SortedTriple6 → Bool) :
    Decidable (GrassmannPluckerSigns6 χ) := by
  unfold GrassmannPluckerSigns6
  infer_instance

structure Hull3SignCase (χ : SortedTriple6 → Bool)
    (e : Equiv.Perm (Fin 6)) : Prop where
  h012 : Positive χ (e 0) (e 1) (e 2)
  h3 : InsideSigns χ (e 3) (e 0) (e 1) (e 2)
  h4 : InsideSigns χ (e 4) (e 0) (e 1) (e 2)
  h5 : InsideSigns χ (e 5) (e 0) (e 1) (e 2)

instance (χ : SortedTriple6 → Bool) (e : Equiv.Perm (Fin 6)) :
    Decidable (Hull3SignCase χ e) := by
  by_cases h012 : Positive χ (e 0) (e 1) (e 2)
  · by_cases h3 : InsideSigns χ (e 3) (e 0) (e 1) (e 2)
    · by_cases h4 : InsideSigns χ (e 4) (e 0) (e 1) (e 2)
      · by_cases h5 : InsideSigns χ (e 5) (e 0) (e 1) (e 2)
        · exact isTrue ⟨h012, h3, h4, h5⟩
        · exact isFalse (fun h ↦ h5 h.h5)
      · exact isFalse (fun h ↦ h4 h.h4)
    · exact isFalse (fun h ↦ h3 h.h3)
  · exact isFalse (fun h ↦ h012 h.h012)

structure Hull4SignCase (χ : SortedTriple6 → Bool)
    (e : Equiv.Perm (Fin 6)) : Prop where
  h012 : Positive χ (e 0) (e 1) (e 2)
  h013 : Positive χ (e 0) (e 1) (e 3)
  h023 : Positive χ (e 0) (e 2) (e 3)
  h123 : Positive χ (e 1) (e 2) (e 3)
  h4 : InsideSigns χ (e 4) (e 0) (e 1) (e 2) ∨
    InsideSigns χ (e 4) (e 0) (e 2) (e 3)
  h5 : InsideSigns χ (e 5) (e 0) (e 1) (e 2) ∨
    InsideSigns χ (e 5) (e 0) (e 2) (e 3)

instance (χ : SortedTriple6 → Bool) (e : Equiv.Perm (Fin 6)) :
    Decidable (Hull4SignCase χ e) := by
  by_cases h012 : Positive χ (e 0) (e 1) (e 2)
  · by_cases h013 : Positive χ (e 0) (e 1) (e 3)
    · by_cases h023 : Positive χ (e 0) (e 2) (e 3)
      · by_cases h123 : Positive χ (e 1) (e 2) (e 3)
        · by_cases h4 : InsideSigns χ (e 4) (e 0) (e 1) (e 2) ∨
              InsideSigns χ (e 4) (e 0) (e 2) (e 3)
          · by_cases h5 : InsideSigns χ (e 5) (e 0) (e 1) (e 2) ∨
                InsideSigns χ (e 5) (e 0) (e 2) (e 3)
            · exact isTrue ⟨h012, h013, h023, h123, h4, h5⟩
            · exact isFalse (fun h ↦ h5 h.h5)
          · exact isFalse (fun h ↦ h4 h.h4)
        · exact isFalse (fun h ↦ h123 h.h123)
      · exact isFalse (fun h ↦ h023 h.h023)
    · exact isFalse (fun h ↦ h013 h.h013)
  · exact isFalse (fun h ↦ h012 h.h012)

structure Hull5SignCase (χ : SortedTriple6 → Bool)
    (e : Equiv.Perm (Fin 6)) : Prop where
  hullStrict : ∀ i j k : Fin 5, i < j → j < k →
    Positive χ (e i.castSucc) (e j.castSucc) (e k.castSucc)
  fan01 : Positive χ (e 5) (e 0) (e 1)
  fan12 : Positive χ (e 5) (e 1) (e 2)
  fan23 : Positive χ (e 5) (e 2) (e 3)
  fan34 : Positive χ (e 5) (e 3) (e 4)
  fan40 : Positive χ (e 5) (e 4) (e 0)
  insideFan : InsideSigns χ (e 5) (e 0) (e 1) (e 2) ∨
    InsideSigns χ (e 5) (e 0) (e 2) (e 3) ∨
    InsideSigns χ (e 5) (e 0) (e 3) (e 4)

instance (χ : SortedTriple6 → Bool) (e : Equiv.Perm (Fin 6)) :
    Decidable (Hull5SignCase χ e) := by
  by_cases hs : ∀ i j k : Fin 5, i < j → j < k →
      Positive χ (e i.castSucc) (e j.castSucc) (e k.castSucc)
  · by_cases h01 : Positive χ (e 5) (e 0) (e 1)
    · by_cases h12 : Positive χ (e 5) (e 1) (e 2)
      · by_cases h23 : Positive χ (e 5) (e 2) (e 3)
        · by_cases h34 : Positive χ (e 5) (e 3) (e 4)
          · by_cases h40 : Positive χ (e 5) (e 4) (e 0)
            · by_cases hi : InsideSigns χ (e 5) (e 0) (e 1) (e 2) ∨
                  InsideSigns χ (e 5) (e 0) (e 2) (e 3) ∨
                  InsideSigns χ (e 5) (e 0) (e 3) (e 4)
              · exact isTrue ⟨hs, h01, h12, h23, h34, h40, hi⟩
              · exact isFalse (fun h ↦ hi h.insideFan)
            · exact isFalse (fun h ↦ h40 h.fan40)
          · exact isFalse (fun h ↦ h34 h.fan34)
        · exact isFalse (fun h ↦ h23 h.fan23)
      · exact isFalse (fun h ↦ h12 h.fan12)
    · exact isFalse (fun h ↦ h01 h.fan01)
  · exact isFalse (fun h ↦ hs h.hullStrict)

structure Hull6SignCase (χ : SortedTriple6 → Bool)
    (e : Equiv.Perm (Fin 6)) : Prop where
  strict : ∀ i j k : Fin 6, i < j → j < k →
    Positive χ (e i) (e j) (e k)

instance (χ : SortedTriple6 → Bool) (e : Equiv.Perm (Fin 6)) :
    Decidable (Hull6SignCase χ e) := by
  by_cases hs : ∀ i j k : Fin 6, i < j → j < k →
      Positive χ (e i) (e j) (e k)
  · exact isTrue ⟨hs⟩
  · exact isFalse (fun h ↦ hs h.strict)

def CanonicalSignCase6 (χ : SortedTriple6 → Bool)
    (e : Equiv.Perm (Fin 6)) : Prop :=
  Hull3SignCase χ e ∨ Hull4SignCase χ e ∨
    Hull5SignCase χ e ∨ Hull6SignCase χ e

instance (χ : SortedTriple6 → Bool) (e : Equiv.Perm (Fin 6)) :
    Decidable (CanonicalSignCase6 χ e) := by
  unfold CanonicalSignCase6
  infer_instance

/-- The ten increasing triples not containing the distinguished anchor `0`.
After slope sorting, all ten triples containing `0` are positive, so this is
the entire finite state that remains. -/
abbrev TailTriple6 := {t : SortedTriple6 // sortedFirst t ≠ 0}

def liftAnchorPerm (π : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 6) :=
  Equiv.Perm.decomposeFin.symm (0, π)

def anchoredSigns (τ : TailTriple6 → Bool) : SortedTriple6 → Bool :=
  fun t ↦ if h : sortedFirst t = 0 then true else τ ⟨t, h⟩

/-- The ten free signs after the anchor normalization, written without a
proof-carrying finite-function representation. -/
structure TailBits6 where
  b123 : Bool
  b124 : Bool
  b125 : Bool
  b134 : Bool
  b135 : Bool
  b145 : Bool
  b234 : Bool
  b235 : Bool
  b245 : Bool
  b345 : Bool

private def anchoredBits (b : TailBits6) : SortedTriple6 → Bool :=
  fun t ↦
    if sortedFirst t = 0 then true
    else if sortedFirst t = 1 ∧ sortedSecond t = 2 ∧ sortedThird t = 3 then b.b123
    else if sortedFirst t = 1 ∧ sortedSecond t = 2 ∧ sortedThird t = 4 then b.b124
    else if sortedFirst t = 1 ∧ sortedSecond t = 2 ∧ sortedThird t = 5 then b.b125
    else if sortedFirst t = 1 ∧ sortedSecond t = 3 ∧ sortedThird t = 4 then b.b134
    else if sortedFirst t = 1 ∧ sortedSecond t = 3 ∧ sortedThird t = 5 then b.b135
    else if sortedFirst t = 1 ∧ sortedSecond t = 4 ∧ sortedThird t = 5 then b.b145
    else if sortedFirst t = 2 ∧ sortedSecond t = 3 ∧ sortedThird t = 4 then b.b234
    else if sortedFirst t = 2 ∧ sortedSecond t = 3 ∧ sortedThird t = 5 then b.b235
    else if sortedFirst t = 2 ∧ sortedSecond t = 4 ∧ sortedThird t = 5 then b.b245
    else b.b345

private def chainNonePerm : Equiv.Perm (Fin 5) :=
  ((Equiv.swap 1 4).trans (Equiv.swap 1 3)).trans (Equiv.swap 1 2)

private def chainOnly2Perm : Equiv.Perm (Fin 5) :=
  (Equiv.swap 2 4).trans (Equiv.swap 2 3)

private def chainOnly3Perm : Equiv.Perm (Fin 5) :=
  ((Equiv.swap 1 2).trans (Equiv.swap 1 4)).trans (Equiv.swap 1 3)

private def chainOnly4Perm : Equiv.Perm (Fin 5) :=
  (Equiv.swap 1 3).trans (Equiv.swap 2 4)

private def chainTwoThreePerm : Equiv.Perm (Fin 5) :=
  Equiv.swap 3 4

private def chainTwoFourPerm : Equiv.Perm (Fin 5) :=
  (Equiv.swap 2 3).trans (Equiv.swap 2 4)

private def chainThreeFourPerm : Equiv.Perm (Fin 5) :=
  ((Equiv.swap 1 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 1 4)

private def chainAllPerm : Equiv.Perm (Fin 5) := Equiv.refl _

/-- The eight radial-chain hull cases.  Their lifted label arrays are
`015234`, `012534`, `013524`, `014523`, `012354`, `012453`, `013452`,
and `012345`; these are the eight possible subsets of the middle radial
labels `{2,3,4}` lying on the opposite hull chain. -/
private def RadialChainSignCase6 (χ : SortedTriple6 → Bool) : Prop :=
  Hull3SignCase χ (liftAnchorPerm chainNonePerm) ∨
  Hull4SignCase χ (liftAnchorPerm chainOnly2Perm) ∨
  Hull4SignCase χ (liftAnchorPerm chainOnly3Perm) ∨
  Hull4SignCase χ (liftAnchorPerm chainOnly4Perm) ∨
  Hull5SignCase χ (liftAnchorPerm chainTwoThreePerm) ∨
  Hull5SignCase χ (liftAnchorPerm chainTwoFourPerm) ∨
  Hull5SignCase χ (liftAnchorPerm chainThreeFourPerm) ∨
  Hull6SignCase χ (liftAnchorPerm chainAllPerm)

private instance (χ : SortedTriple6 → Bool) :
    Decidable (RadialChainSignCase6 χ) := by
  unfold RadialChainSignCase6
  infer_instance

private def explicitTailBits
    (b123 b124 b135 b245 b345 b125 b134 b234 b235 b145 : Bool) :
    TailBits6 where
  b123 := b123
  b124 := b124
  b125 := b125
  b134 := b134
  b135 := b135
  b145 := b145
  b234 := b234
  b235 := b235
  b245 := b245
  b345 := b345

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked finite core.  The first five signs form 32 separate tactic
branches; each ordinary `decide` call sees only the remaining 32 completions.
The antecedent has 25 canonical Pluecker rows and the conclusion tests the
eight radial-chain cases, rather than all 120 anchor-fixing permutations. -/
private theorem finite_bits32 :
    ∀ b123 b124 b135 b245 b345 b125 b134 b234 b235 b145 : Bool,
      let b := explicitTailBits b123 b124 b135 b245 b345
        b125 b134 b234 b235 b145
      GrassmannPluckerSigns6 (anchoredBits b) →
        RadialChainSignCase6 (anchoredBits b) := by
  intro b123 b124 b135 b245 b345
  cases b123 <;> cases b124 <;> cases b135 <;>
    cases b245 <;> cases b345 <;> decide

private theorem finite_tailBits_classification (b : TailBits6)
    (hgp : GrassmannPluckerSigns6 (anchoredBits b)) :
    RadialChainSignCase6 (anchoredBits b) := by
  rcases b with ⟨b123, b124, b125, b134, b135,
    b145, b234, b235, b245, b345⟩
  exact finite_bits32 b123 b124 b135 b245 b345
    b125 b134 b234 b235 b145 hgp

private def readTailBits (τ : TailTriple6 → Bool) : TailBits6 where
  b123 := τ ⟨⟨(1, 2, 3), by decide⟩, by decide⟩
  b124 := τ ⟨⟨(1, 2, 4), by decide⟩, by decide⟩
  b125 := τ ⟨⟨(1, 2, 5), by decide⟩, by decide⟩
  b134 := τ ⟨⟨(1, 3, 4), by decide⟩, by decide⟩
  b135 := τ ⟨⟨(1, 3, 5), by decide⟩, by decide⟩
  b145 := τ ⟨⟨(1, 4, 5), by decide⟩, by decide⟩
  b234 := τ ⟨⟨(2, 3, 4), by decide⟩, by decide⟩
  b235 := τ ⟨⟨(2, 3, 5), by decide⟩, by decide⟩
  b245 := τ ⟨⟨(2, 4, 5), by decide⟩, by decide⟩
  b345 := τ ⟨⟨(3, 4, 5), by decide⟩, by decide⟩

private theorem anchoredSigns_eq_anchoredBits
    (τ : TailTriple6 → Bool) :
    anchoredSigns τ = anchoredBits (readTailBits τ) := by
  funext t
  rcases t with ⟨⟨i, j, k⟩, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals simp [anchoredSigns, anchoredBits, readTailBits,
      sortedFirst, sortedSecond, sortedThird]

private theorem radialChainSignCase_exists_perm
    (χ : SortedTriple6 → Bool) (h : RadialChainSignCase6 χ) :
    ∃ π : Equiv.Perm (Fin 5),
      CanonicalSignCase6 χ (liftAnchorPerm π) := by
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨chainNonePerm, Or.inl h⟩
  · exact ⟨chainOnly2Perm, Or.inr (Or.inl h)⟩
  · exact ⟨chainOnly3Perm, Or.inr (Or.inl h)⟩
  · exact ⟨chainOnly4Perm, Or.inr (Or.inl h)⟩
  · exact ⟨chainTwoThreePerm, Or.inr (Or.inr (Or.inl h))⟩
  · exact ⟨chainTwoFourPerm, Or.inr (Or.inr (Or.inl h))⟩
  · exact ⟨chainThreeFourPerm, Or.inr (Or.inr (Or.inl h))⟩
  · exact ⟨chainAllPerm, Or.inr (Or.inr (Or.inr h))⟩

/-- Sharply normalized finite classification.  Its input has ten explicit
bits (`2^10 = 1024` tables).  GP leaves exactly 62 tables, partitioned by the
eight radial-chain cases above.  The affine premise is retained for API
compatibility but is mathematically redundant.  Ordinary kernel reduction is
used: there is no native evaluator, generated certificate, or data file. -/
theorem finite_anchored_rank3_classification :
    ∀ τ : TailTriple6 → Bool,
      AffineCocycleSigns6 (anchoredSigns τ) →
      GrassmannPluckerSigns6 (anchoredSigns τ) →
        ∃ π : Equiv.Perm (Fin 5),
          CanonicalSignCase6 (anchoredSigns τ) (liftAnchorPerm π) := by
  intro τ _haff hgp
  let b := readTailBits τ
  have heq : anchoredSigns τ = anchoredBits b := by
    simpa only [b] using anchoredSigns_eq_anchoredBits τ
  have hgp' : GrassmannPluckerSigns6 (anchoredBits b) := by
    rw [← heq]
    exact hgp
  obtain ⟨π, hcase⟩ :=
    radialChainSignCase_exists_perm _
      (finite_tailBits_classification b hgp')
  refine ⟨π, ?_⟩
  rw [heq]
  exact hcase

/-! ## Determinant signs satisfy the two finite axioms -/

noncomputable def determinantSigns (v : Fin 6 → ℝ × ℝ) :
    SortedTriple6 → Bool :=
  fun t ↦ decide (0 < sig (v (sortedFirst t))
    (v (sortedSecond t)) (v (sortedThird t)))

private theorem not_determinantSigns_iff
    (v : Fin 6 → ℝ × ℝ) (t : SortedTriple6) :
    (!determinantSigns v t) = true ↔
      ¬ 0 < sig (v (sortedFirst t))
        (v (sortedSecond t)) (v (sortedThird t)) := by
  simp only [determinantSigns, Bool.not_eq_true_eq_eq_false,
    decide_eq_false_iff_not]

private theorem positive_determinantSigns
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Positive (determinantSigns v) i j k ↔
      0 < sig (v i) (v j) (v k) := by
  unfold Positive orientPositive
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆
  · simp only [determinantSigns, sortedFirst, sortedSecond, sortedThird]
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  · have hne : sig (v i) (v k) (v j) ≠ 0 :=
      hgp i k j (ne_of_lt h₂.1) (ne_of_lt (h₂.1.trans h₂.2))
        (ne_of_lt h₂.2)
    have hs : sig (v i) (v j) (v k) = -sig (v i) (v k) (v j) :=
      sig_swap (v i) (v j) (v k)
    rw [not_determinantSigns_iff]
    simp only [sortedFirst, sortedSecond, sortedThird]
    rw [hs]
    constructor
    · intro hn
      have hneg : sig (v i) (v k) (v j) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hn) hne
      linarith
    · intro hpos
      linarith
  · have hne : sig (v j) (v i) (v k) ≠ 0 :=
      hgp j i k (ne_of_lt h₃.1) (ne_of_lt (h₃.1.trans h₃.2))
        (ne_of_lt h₃.2)
    have hs : sig (v i) (v j) (v k) = -sig (v j) (v i) (v k) := by
      simp only [sig]
      ring
    rw [not_determinantSigns_iff]
    simp only [sortedFirst, sortedSecond, sortedThird]
    rw [hs]
    constructor
    · intro hn
      have hneg : sig (v j) (v i) (v k) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hn) hne
      linarith
    · intro hpos
      linarith
  · have hs : sig (v i) (v j) (v k) = sig (v j) (v k) (v i) :=
      sig_rotate (v i) (v j) (v k)
    simp only [determinantSigns, sortedFirst, sortedSecond, sortedThird]
    rw [hs]
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  · have hs : sig (v i) (v j) (v k) = sig (v k) (v i) (v j) := by
      calc
        sig (v i) (v j) (v k) = sig (v j) (v k) (v i) :=
          sig_rotate (v i) (v j) (v k)
        _ = sig (v k) (v i) (v j) := sig_rotate (v j) (v k) (v i)
    simp only [determinantSigns, sortedFirst, sortedSecond, sortedThird]
    rw [hs]
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  · have hne : sig (v k) (v j) (v i) ≠ 0 :=
      hgp k j i (ne_of_lt h₆.1) (ne_of_lt (h₆.1.trans h₆.2))
        (ne_of_lt h₆.2)
    have hs : sig (v i) (v j) (v k) = -sig (v k) (v j) (v i) := by
      simp only [sig]
      ring
    rw [not_determinantSigns_iff]
    simp only [sortedFirst, sortedSecond, sortedThird]
    rw [hs]
    constructor
    · intro hn
      have hneg : sig (v k) (v j) (v i) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hn) hne
      linarith
    · intro hpos
      linarith
  · omega

private theorem determinantSigns_affineCocycleClause
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    {p q r s : Fin 6} (hd : Distinct4 p q r s) :
    AffineCocycleClause (determinantSigns v) p q r s := by
  unfold AffineCocycleClause
  rcases hd with ⟨hpq, hpr, hps, hqr, hqs, hrs⟩
  rw [positive_determinantSigns v hgp hpq hps hqs,
    positive_determinantSigns v hgp hqr hqs hrs,
    positive_determinantSigns v hgp hpq hpr hqr,
    positive_determinantSigns v hgp hpr hps hrs]
  intro hbad
  have h₁ne := hgp p q s hpq hps hqs
  have h₂ne := hgp q r s hqr hqs hrs
  have h₃ne := hgp p q r hpq hpr hqr
  have h₄ne := hgp p r s hpr hps hrs
  have hid := cocycle (v p) (v q) (v r) (v s)
  rcases hbad with hbad | hbad
  · rcases hbad with ⟨h₁, h₂, h₃, h₄⟩
    have h₃neg : sig (v p) (v q) (v r) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h₃) h₃ne
    have h₄neg : sig (v p) (v r) (v s) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h₄) h₄ne
    linarith
  · rcases hbad with ⟨h₁, h₂, h₃, h₄⟩
    have h₁neg : sig (v p) (v q) (v s) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h₁) h₁ne
    have h₂neg : sig (v q) (v r) (v s) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h₂) h₂ne
    linarith

theorem determinantSigns_affineCocycle
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v) :
    AffineCocycleSigns6 (determinantSigns v) := by
  unfold AffineCocycleSigns6
  exact ⟨
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide),
    determinantSigns_affineCocycleClause v hgp (by decide)⟩

private theorem mul_pos_of_pos_iff_pos {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : (0 < x ↔ 0 < y)) :
    0 < x * y := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hynpos : ¬ 0 < y := by
      intro hypos
      have hxpos' := h.mpr hypos
      linarith
    have hyneg : y < 0 :=
      lt_of_le_of_ne (le_of_not_gt hynpos) hy
    exact mul_pos_of_neg_of_neg hxneg hyneg
  · exact mul_pos hxpos (h.mp hxpos)

private theorem mul_neg_of_not_pos_iff_pos {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : ¬ (0 < x ↔ 0 < y)) :
    x * y < 0 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · exfalso
      apply h
      constructor <;> intro hpos <;> linarith
    · exact mul_neg_of_neg_of_pos hxneg hypos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · exact mul_neg_of_pos_of_neg hxpos hyneg
    · exfalso
      apply h
      exact ⟨fun _ ↦ hypos, fun _ ↦ hxpos⟩

private theorem determinantSigns_grassmannPluckerClause
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    {a b c d e : Fin 6} (hd : Distinct5 a b c d e) :
    GrassmannPluckerClause (determinantSigns v) a b c d e := by
  unfold GrassmannPluckerClause
  rcases hd with ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩
  dsimp [SameSign]
  rw [positive_determinantSigns v hgp hab hac hbc,
    positive_determinantSigns v hgp had hae hde,
    positive_determinantSigns v hgp hab had hbd,
    positive_determinantSigns v hgp hac hae hce,
    positive_determinantSigns v hgp hab hae hbe,
    positive_determinantSigns v hgp hac had hcd]
  have h₁ne := hgp a b c hab hac hbc
  have h₂ne := hgp a d e had hae hde
  have h₃ne := hgp a b d hab had hbd
  have h₄ne := hgp a c e hac hae hce
  have h₅ne := hgp a b e hab hae hbe
  have h₆ne := hgp a c d hac had hcd
  intro hbad
  have hid := plucker (v a) (v b) (v c) (v d) (v e)
  rcases hbad with hbad | hbad
  · rcases hbad with ⟨h₁, h₂, h₃⟩
    have hp₁ := mul_pos_of_pos_iff_pos h₁ne h₂ne h₁
    have hn₂ := mul_neg_of_not_pos_iff_pos h₃ne h₄ne h₂
    have hp₃ := mul_pos_of_pos_iff_pos h₅ne h₆ne h₃
    nlinarith
  · rcases hbad with ⟨h₁, h₂, h₃⟩
    have hn₁ := mul_neg_of_not_pos_iff_pos h₁ne h₂ne h₁
    have hs₂ :
        (0 < sig (v a) (v b) (v d) ↔
          0 < sig (v a) (v c) (v e)) := by
      by_contra hs
      exact h₂ hs
    have hp₂ := mul_pos_of_pos_iff_pos h₃ne h₄ne hs₂
    have hn₃ := mul_neg_of_not_pos_iff_pos h₅ne h₆ne h₃
    nlinarith

theorem determinantSigns_grassmannPlucker
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v) :
    GrassmannPluckerSigns6 (determinantSigns v) := by
  unfold GrassmannPluckerSigns6
  exact ⟨
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide),
    determinantSigns_grassmannPluckerClause v hgp (by decide)⟩

/-! ## From the finite sign normal form to the geometric packets -/

private theorem inTri_of_positive_orientations
    (p a b c : ℝ × ℝ)
    (habc : 0 < sig a b c)
    (habp : 0 < sig a b p)
    (hbcp : 0 < sig b c p)
    (hcap : 0 < sig c a p) :
    InTri p a b c := by
  have hapc : 0 < sig a p c := by
    rw [← sig_rotate (c) (a) (p)]
    exact hcap
  rcases strict_barycentric_of_orientations a b p c habc habp hapc hbcp with
    ⟨x, y, z, hx, hy, hz, hsum, hp⟩
  exact ⟨x, y, z, hx.le, hy.le, hz.le, hsum, hp⟩

private theorem positive_after_relabel
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    (e : Equiv.Perm (Fin 6)) {i j k : Fin 6}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Positive (determinantSigns v) (e i) (e j) (e k) ↔
      0 < sig (v (e i)) (v (e j)) (v (e k)) := by
  exact positive_determinantSigns v hgp
    (fun h ↦ hij (e.injective h))
    (fun h ↦ hik (e.injective h))
    (fun h ↦ hjk (e.injective h))

private theorem inTri_after_relabel
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    (e : Equiv.Perm (Fin 6)) {p a b c : Fin 6}
    (hd : Distinct4 p a b c)
    (habc : Positive (determinantSigns v) (e a) (e b) (e c))
    (hp : InsideSigns (determinantSigns v) (e p) (e a) (e b) (e c)) :
    InTri (v (e p)) (v (e a)) (v (e b)) (v (e c)) := by
  rcases hd with ⟨hpa, hpb, hpc, hab, hac, hbc⟩
  rcases hp with ⟨habp, hbcp, hcap⟩
  apply inTri_of_positive_orientations
  · exact (positive_after_relabel v hgp e hab hac hbc).mp habc
  · exact (positive_after_relabel v hgp e hab (Ne.symm hpa)
      (Ne.symm hpb)).mp habp
  · exact (positive_after_relabel v hgp e hbc (Ne.symm hpb)
      (Ne.symm hpc)).mp hbcp
  · exact (positive_after_relabel v hgp e (Ne.symm hac) (Ne.symm hpc)
      (Ne.symm hpa)).mp hcap

/-- Convert a classified determinant sign table into the corresponding
geometric packet. -/
private theorem canonicalHullCase6_of_signCase
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    (e : Equiv.Perm (Fin 6))
    (he : CanonicalSignCase6 (determinantSigns v) e) :
    CanonicalHullCase6 (fun i ↦ v (e i)) := by
  rcases he with he | he | he | he
  · left
    exact {
      h012 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.h012
      h3 := inTri_after_relabel v hgp e (by decide) he.h012 he.h3
      h4 := inTri_after_relabel v hgp e (by decide) he.h012 he.h4
      h5 := inTri_after_relabel v hgp e (by decide) he.h012 he.h5 }
  · right; left
    exact {
      h012 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.h012
      h013 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.h013
      h023 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.h023
      h123 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.h123
      h4 := by
        rcases he.h4 with h4 | h4
        · exact Or.inl (inTri_after_relabel v hgp e (by decide) he.h012 h4)
        · exact Or.inr (inTri_after_relabel v hgp e (by decide) he.h023 h4)
      h5 := by
        rcases he.h5 with h5 | h5
        · exact Or.inl (inTri_after_relabel v hgp e (by decide) he.h012 h5)
        · exact Or.inr (inTri_after_relabel v hgp e (by decide) he.h023 h5) }
  · right; right; left
    exact {
      hullStrict := by
        intro i j k hij hjk
        exact (positive_after_relabel v hgp e
          ((Fin.castSucc_injective 5).ne (ne_of_lt hij))
          ((Fin.castSucc_injective 5).ne (ne_of_lt (hij.trans hjk)))
          ((Fin.castSucc_injective 5).ne (ne_of_lt hjk))).mp
            (he.hullStrict i j k hij hjk)
      fan01 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.fan01
      fan12 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.fan12
      fan23 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.fan23
      fan34 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.fan34
      fan40 := (positive_after_relabel v hgp e (by decide) (by decide)
        (by decide)).mp he.fan40
      insideFan := by
        rcases he.insideFan with h | h | h
        · exact Or.inl (inTri_after_relabel v hgp e (by decide)
            (he.hullStrict 0 1 2 (by decide) (by decide)) h)
        · exact Or.inr (Or.inl (inTri_after_relabel v hgp e (by decide)
            (he.hullStrict 0 2 3 (by decide) (by decide)) h))
        · exact Or.inr (Or.inr (inTri_after_relabel v hgp e (by decide)
            (he.hullStrict 0 3 4 (by decide) (by decide)) h)) }
  · right; right; right
    exact {
      strict := by
        intro i j k hij hjk
        exact (positive_after_relabel v hgp e (ne_of_lt hij)
          (ne_of_lt (hij.trans hjk)) (ne_of_lt hjk)).mp
            (he.strict i j k hij hjk) }

def AnchorPositive (v : Fin 6 → ℝ × ℝ) : Prop :=
  ∀ i j : Fin 6, 0 < i → i < j → 0 < sig (v 0) (v i) (v j)

noncomputable def tailDeterminantSigns (v : Fin 6 → ℝ × ℝ) :
    TailTriple6 → Bool :=
  fun t ↦ determinantSigns v t.1

private theorem determinantSigns_eq_anchored
    (v : Fin 6 → ℝ × ℝ) (hanchor : AnchorPositive v) :
    determinantSigns v = anchoredSigns (tailDeterminantSigns v) := by
  funext t
  simp only [anchoredSigns]
  split_ifs with hzero
  · have hsecond : 0 < sortedSecond t := by
      have hlt := t.property.1
      change sortedFirst t < sortedSecond t at hlt
      rw [hzero] at hlt
      exact hlt
    have hpos := hanchor (sortedSecond t) (sortedThird t) hsecond t.property.2
    simp [determinantSigns, hzero, hpos]
  · rfl

/-- Once a supporting anchor and its slope order have been chosen, the whole
hull classification costs only the ten-bit ordinary-decision lemma above. -/
theorem canonicalHullCase6_of_anchorPositive
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    (hanchor : AnchorPositive v) :
    ∃ w, Relabels v w ∧ CanonicalHullCase6 w := by
  let τ := tailDeterminantSigns v
  have heq : determinantSigns v = anchoredSigns τ := by
    simpa only [τ] using determinantSigns_eq_anchored v hanchor
  have haff : AffineCocycleSigns6 (anchoredSigns τ) := by
    rw [← heq]
    exact determinantSigns_affineCocycle v hgp
  have hpl : GrassmannPluckerSigns6 (anchoredSigns τ) := by
    rw [← heq]
    exact determinantSigns_grassmannPlucker v hgp
  obtain ⟨π, he⟩ := finite_anchored_rank3_classification τ haff hpl
  let e := liftAnchorPerm π
  have he' : CanonicalSignCase6 (determinantSigns v) e := by
    rw [heq]
    simpa only [e] using he
  exact ⟨fun i ↦ v (e i), ⟨e, rfl⟩,
    canonicalHullCase6_of_signCase v hgp e he'⟩

/-- Thin composition form used while the analytic anchor/slope normalizer is
kept in its own module. -/
theorem canonicalHullCase6_complete_of_anchor_relabel
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v)
    (horder : ∃ e : Equiv.Perm (Fin 6),
      AnchorPositive (fun i ↦ v (e i))) :
    ∃ w, Relabels v w ∧ CanonicalHullCase6 w := by
  obtain ⟨e₀, he₀⟩ := horder
  let u : Fin 6 → ℝ × ℝ := fun i ↦ v (e₀ i)
  have hgpu : NoDegenerateTriple6 u := by
    intro i j k hij hik hjk
    exact hgp (e₀ i) (e₀ j) (e₀ k)
      (fun h ↦ hij (e₀.injective h))
      (fun h ↦ hik (e₀.injective h))
      (fun h ↦ hjk (e₀.injective h))
  obtain ⟨w, hw, hcase⟩ :=
    canonicalHullCase6_of_anchorPositive u hgpu he₀
  rcases hw with ⟨e₁, rfl⟩
  refine ⟨fun i ↦ v (e₀ (e₁ i)), ?_, hcase⟩
  exact ⟨e₁.trans e₀, rfl⟩

/-- Complete six-point planar hull classification.  A diameter endpoint and
radial slope order supply the ten positive anchor brackets; the remaining ten
signs are handled by `finite_anchored_rank3_classification`. -/
theorem canonicalHullCase6_complete
    (v : Fin 6 → ℝ × ℝ) (hgp : NoDegenerateTriple6 v) :
    ∃ w, Relabels v w ∧ CanonicalHullCase6 w := by
  apply canonicalHullCase6_complete_of_anchor_relabel v hgp
  simpa only [AnchorPositive] using
    (AnchorOrder.exists_anchor_positive_relabel v
      (by simpa only [NoDegenerateTriple6] using hgp))

/-- The elementary arithmetic split for a hull cardinality between 3 and 6. -/
theorem cardinality_three_four_five_six {h : ℕ}
    (hlo : 3 ≤ h) (hhi : h ≤ 6) :
    h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by
  omega

theorem Relabels.range_eq {v w : Fin 6 → ℝ × ℝ}
    (h : Relabels v w) : Set.range w = Set.range v := by
  rcases h with ⟨e, rfl⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

theorem Relabels.floor {v w : Fin 6 → ℝ × ℝ} {m : ℝ}
    (h : Relabels v w) (hmin : DistinctTriangleFloor v m) :
    DistinctTriangleFloor w m := by
  rcases h with ⟨e, rfl⟩
  intro i j k hij hik hjk
  apply hmin (e i) (e j) (e k)
  · exact fun heq ↦ hij (e.injective heq)
  · exact fun heq ↦ hik (e.injective heq)
  · exact fun heq ↦ hjk (e.injective heq)

theorem Relabels.noDegenerate {v w : Fin 6 → ℝ × ℝ}
    (h : Relabels v w) (hgp : NoDegenerateTriple6 v) :
    NoDegenerateTriple6 w := by
  rcases h with ⟨e, rfl⟩
  intro i j k hij hik hjk
  apply hgp (e i) (e j) (e k)
  · exact fun heq ↦ hij (e.injective heq)
  · exact fun heq ↦ hik (e.injective heq)
  · exact fun heq ↦ hjk (e.injective heq)

/-- Pure logical eliminator used by the eventual `Heil6.Upper` theorem. -/
theorem closed_of_hull_packets
    (Closed : (Fin 6 → ℝ × ℝ) → Prop)
    (h3 : ∀ w, Hull3Packet w → Closed w)
    (h4 : ∀ w, Hull4Packet w → Closed w)
    (h5 : ∀ w, Hull5Packet w → Closed w)
    (h6 : ∀ w, Hull6Packet w → Closed w)
    (w : Fin 6 → ℝ × ℝ) (hw : CanonicalHullCase6 w) : Closed w := by
  rcases hw with hw | hw | hw | hw
  · exact h3 w hw
  · exact h4 w hw
  · exact h5 w hw
  · exact h6 w hw

end FiniteHullCases
end N6Scratch
