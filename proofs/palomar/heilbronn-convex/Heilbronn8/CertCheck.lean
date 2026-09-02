import Mathlib

/-!
# Shared exact Farkas checker for Heilbronn-8 B&B leaves

This file is intended to be compiled once and imported by generated leaf
modules.  A generated replay contains integer data and a small proof such as

```
exact soundness leaf_k (by rfl) x hx
```

There is no `linarith` call per leaf.  `checkLeaf` is a plain structural
Boolean program over lists, naturals, integers, and booleans; `soundness`
supplies the ordered-field Farkas argument once for all leaves.

## Emitter contract

The source LP data are dyadic rationals, but the certificate data below are
all-integer.  For every emitted row, the emitter must multiply the entire row
(coefficients and RHS) by one positive integer that clears its denominators.
Positive row scaling preserves both `<=` and `<`.  It must then adjust the
Farkas multipliers to integers by choosing one positive common scale for the
whole weighted combination.  Positive scaling of the whole combination
preserves the contradiction.  These two positive-scaling obligations are on
the emitter; the checker verifies the resulting integer identity exactly.

## Representation and expected cost

Rows remain dense 31-entry lists.  Lists make literal generation and kernel
reduction transparent, but `List.getD` is linear in the column index.  Thus
the current coefficient check does roughly 31 times the support size in row
lookups, with a small additional factor from list indexing.  With the sample
mean support of 6.8 rows this should still be modest, but the previous
5--15 ms-per-leaf estimate is only an unmeasured target.  A representative
500--1000-leaf shard should be timed before committing the whole run.  If
lookup dominates, the next optimization should be a proved one-pass list
accumulator while retaining this public certificate format.

It is important that no rational arithmetic occur on the Boolean path.
Although `decide` is kernel checked, normalization of `Rat`/`ℚ` can reach
`Nat.gcd`; its well-founded-recursive definition need not reduce
definitionally in the kernel.  A proof such as `by decide` can therefore get
stuck even on closed rational data.  Integer signs below are inspected by
constructor matching, and all integer sums and products reduce through the
primitive natural-number operations.  Consequently both `by rfl` and
`by decide` reduce for closed leaves; the examples use the smaller and more
direct `by rfl`.  `norm_num` remains sound but would run a metaprogram and
construct an arithmetic proof separately for every leaf.
-/

namespace Heilbronn8
namespace CertCheck

/-- One integer-scaled LP row. `rel = false` means `lhs <= rhs`; `rel = true`
means `lhs < rhs`. The checker requires exactly 31 dense coefficients. -/
structure Row where
  coeffs : List ℤ
  rhs : ℤ
  rel : Bool
deriving Repr, DecidableEq

/-- Rows and their aligned nonnegative integer Farkas multipliers. -/
structure Leaf where
  rows : List Row
  multipliers : List ℤ
deriving Repr, DecidableEq

/-! ### Structurally reducing Boolean primitives -/

/-- Structural equality on naturals, used for shape checks. -/
def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ m, Nat.succ n => natEq m n
  | _, _ => false

/-- Integer sign tests as `decide` on core decidable instances: these reduce
structurally through `Nat` primitives in the kernel, and the bridging lemmas
are option-set-independent one-liners. -/
def intNonnegative (z : ℤ) : Bool := decide (0 ≤ z)

def intPositive (z : ℤ) : Bool := decide (0 < z)

def intNonpositive (z : ℤ) : Bool := decide (z ≤ 0)

def intNegative (z : ℤ) : Bool := decide (z < 0)

def intIsZero (z : ℤ) : Bool := decide (z = 0)

lemma intNonnegative_eq_true {z : ℤ} :
    intNonnegative z = true ↔ 0 ≤ z := by
  simp [intNonnegative]

lemma intPositive_eq_true {z : ℤ} :
    intPositive z = true ↔ 0 < z := by
  simp [intPositive]

lemma intNonpositive_eq_true {z : ℤ} :
    intNonpositive z = true ↔ z ≤ 0 := by
  simp [intNonpositive]

lemma intNegative_eq_true {z : ℤ} :
    intNegative z = true ↔ z < 0 := by
  simp [intNegative]

lemma intIsZero_eq_true {z : ℤ} :
    intIsZero z = true ↔ z = 0 := by
  simp [intIsZero]

/-! ### Ordered-field semantics -/

/-- Out-of-range access is zero. Valid certificates have length exactly 31,
so the default is only relevant while evaluating malformed input. -/
def Row.coeff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (r : Row) (i : Fin 31) : K :=
  Int.cast (r.coeffs.getD i.val 0)

/-- The left-hand side represented by an integer row. -/
def Row.lhs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (r : Row) (x : Fin 31 → K) : K :=
  ∑ i : Fin 31, r.coeff i * x i

def Row.satisfies {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (r : Row) (x : Fin 31 → K) : Prop :=
  if r.rel then r.lhs x < Int.cast r.rhs
  else r.lhs x ≤ Int.cast r.rhs

def satisfiesAll {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (L : Leaf) (x : Fin 31 → K) : Prop :=
  L.rows.Forall (fun r => r.satisfies x)

/-- Aligned multiplier/row pairs. The length check prevents accepted
certificates from exploiting the truncation performed by `List.zip`. -/
def Leaf.pairs (L : Leaf) : List (ℤ × Row) :=
  L.multipliers.zip L.rows

def weightedLhsPairs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x : Fin 31 → K) : K :=
  (ps.map fun p => Int.cast p.1 * p.2.lhs x).sum

def weightedRhsPairs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (ps : List (ℤ × Row)) : K :=
  (ps.map fun p => Int.cast p.1 * Int.cast p.2.rhs).sum

def pairCoeff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (i : Fin 31) : K :=
  (ps.map fun p => Int.cast p.1 * p.2.coeff i).sum

/-- Rational views retained for downstream compatibility. -/
def combinedCoeff (L : Leaf) (i : Fin 31) : ℚ :=
  pairCoeff L.pairs i

def combinedRhs (L : Leaf) : ℚ :=
  weightedRhsPairs L.pairs

/-! ### Integer checker computation -/

/-- One combined integer coefficient. This recursion, rather than a
`Finset.sum`, is what the Boolean checker evaluates. -/
def pairCoeffInt : List (ℤ × Row) → Nat → ℤ
  | [], _ => 0
  | p :: ps, i =>
      p.1 * p.2.coeffs.getD i 0 + pairCoeffInt ps i

def weightedRhsInt : List (ℤ × Row) → ℤ
  | [] => 0
  | p :: ps => p.1 * p.2.rhs + weightedRhsInt ps

/-- Strictness propagates only through a strictly positive multiplier. -/
def combinedStrict (L : Leaf) : Bool :=
  L.pairs.any fun p => intPositive p.1 && p.2.rel

/-- The theorem-side statement corresponding to relation-aware closing. -/
def relationCloses (L : Leaf) : Prop :=
  if combinedStrict L = true then combinedRhs L ≤ 0 else combinedRhs L < 0

/-- A strict combination closes at RHS zero; a weak combination needs a
negative RHS. -/
def relationClosesBool (strict : Bool) (rhs : ℤ) : Bool :=
  if strict then intNonpositive rhs else intNegative rhs

def lengthOK (L : Leaf) : Bool :=
  natEq L.rows.length L.multipliers.length

def shapeOK (L : Leaf) : Bool :=
  L.rows.all fun r => natEq r.coeffs.length 31

def multipliersOK (L : Leaf) : Bool :=
  L.multipliers.all intNonnegative

def coefficientsZero (L : Leaf) : Bool :=
  (List.range 31).all fun i => intIsZero (pairCoeffInt L.pairs i)

/-- Plain structural Boolean certificate checker. In particular, this is not
`decide` applied to a proposition. -/
def checkLeaf (L : Leaf) : Bool :=
  lengthOK L &&
  shapeOK L &&
  multipliersOK L &&
  coefficientsZero L &&
  relationClosesBool (combinedStrict L) (weightedRhsInt L.pairs)

theorem checkLeaf_eq_true (L : Leaf) :
    checkLeaf L = true ↔
      lengthOK L = true ∧
      shapeOK L = true ∧
      multipliersOK L = true ∧
      coefficientsZero L = true ∧
      relationClosesBool (combinedStrict L) (weightedRhsInt L.pairs) = true := by
  simp only [checkLeaf, Bool.and_eq_true, and_assoc]

theorem combinedStrict_iff (L : Leaf) :
    combinedStrict L = true ↔
      ∃ p ∈ L.pairs, 0 < p.1 ∧ p.2.rel = true := by
  simp [combinedStrict, intPositive_eq_true]

lemma relationClosesBool_eq_true (strict : Bool) (rhs : ℤ) :
    relationClosesBool strict rhs = true ↔
      if strict then rhs ≤ 0 else rhs < 0 := by
  cases strict <;>
    simp [relationClosesBool, intNonpositive_eq_true, intNegative_eq_true]

/-! ### One-time proof bridge -/

lemma Row.le_of_satisfies
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r : Row} {x : Fin 31 → K} (h : r.satisfies x) :
    r.lhs x ≤ Int.cast r.rhs := by
  cases hrel : r.rel with
  | false =>
      simpa [Row.satisfies, hrel] using h
  | true =>
      have hlt : r.lhs x < Int.cast r.rhs := by
        simpa [Row.satisfies, hrel] using h
      exact hlt.le

lemma pairCoeff_eq_int
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (i : Fin 31) :
    pairCoeff (K := K) ps i =
      (Int.cast (pairCoeffInt ps i.val) : K) := by
  induction ps with
  | nil =>
      simp [pairCoeff, pairCoeffInt]
  | cons p ps ih =>
      change
        Int.cast p.1 * p.2.coeff i + pairCoeff ps i =
          Int.cast
            (p.1 * p.2.coeffs.getD i.val 0 +
              pairCoeffInt ps i.val)
      rw [ih]
      simp only [Row.coeff, Int.cast_add, Int.cast_mul]

lemma weightedRhsPairs_eq_int
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) :
    weightedRhsPairs (K := K) ps =
      (Int.cast (weightedRhsInt ps) : K) := by
  induction ps with
  | nil =>
      simp [weightedRhsPairs, weightedRhsInt]
  | cons p ps ih =>
      change
        Int.cast p.1 * Int.cast p.2.rhs + weightedRhsPairs ps =
          Int.cast (p.1 * p.2.rhs + weightedRhsInt ps)
      rw [ih]
      simp only [Int.cast_add, Int.cast_mul]

/-- Distribute evaluation across the exact weighted coefficient vector. This
is the only finite-sum rearrangement needed by every leaf replay. `Finset.sum`
appears only in this once-proven theorem, never in `checkLeaf`. -/
lemma weightedLhsPairs_eq_sum_pairCoeff
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x : Fin 31 → K) :
    weightedLhsPairs ps x = ∑ i : Fin 31, pairCoeff ps i * x i := by
  induction ps with
  | nil =>
      simp [weightedLhsPairs, pairCoeff]
  | cons p ps ih =>
      change
        Int.cast p.1 * p.2.lhs x + weightedLhsPairs ps x =
          ∑ i : Fin 31,
            (Int.cast p.1 * p.2.coeff i + pairCoeff ps i) * x i
      rw [ih]
      unfold Row.lhs
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Nonnegative integer scaling and summation preserve weak row bounds. -/
lemma weightedLhsPairs_le_weightedRhsPairs
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x : Fin 31 → K)
    (hm : ∀ p ∈ ps, 0 ≤ p.1)
    (hs : ∀ p ∈ ps, p.2.satisfies x) :
    weightedLhsPairs ps x ≤ weightedRhsPairs ps := by
  unfold weightedLhsPairs weightedRhsPairs
  exact List.sum_le_sum fun p hp =>
    mul_le_mul_of_nonneg_left (Row.le_of_satisfies (hs p hp))
      (Int.cast_nonneg (hm p hp))

/-- If one strict row has positive weight, the weighted inequality is strict. -/
lemma weightedLhsPairs_lt_weightedRhsPairs
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x : Fin 31 → K)
    (hm : ∀ p ∈ ps, 0 ≤ p.1)
    (hs : ∀ p ∈ ps, p.2.satisfies x)
    (hstrict : ∃ p ∈ ps, 0 < p.1 ∧ p.2.rel = true) :
    weightedLhsPairs ps x < weightedRhsPairs ps := by
  unfold weightedLhsPairs weightedRhsPairs
  apply List.sum_lt_sum
  · intro p hp
    exact mul_le_mul_of_nonneg_left
      (Row.le_of_satisfies (hs p hp)) (Int.cast_nonneg (hm p hp))
  · rcases hstrict with ⟨p, hp, hmp, hrel⟩
    refine ⟨p, hp, ?_⟩
    apply mul_lt_mul_of_pos_left _ (Int.cast_pos.mpr hmp)
    simpa [Row.satisfies, hrel] using hs p hp

/-- One-time Farkas soundness theorem. Generated leaves supply only their
integer data, the kernel computation `checkLeaf leaf_k = true`, and row
hypotheses over any ordered field. -/
theorem soundness
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : Leaf) (hcheck : checkLeaf L = true) :
    ∀ (x : Fin 31 → K), satisfiesAll L x → False := by
  intro x hs
  rcases (checkLeaf_eq_true L).mp hcheck with
    ⟨_hlen, _hshape, hmult, hcoeff, hclose⟩

  have hm : ∀ p ∈ L.pairs, 0 ≤ p.1 := by
    intro p hp
    have hpmem : p.1 ∈ L.multipliers := (List.of_mem_zip hp).1
    exact intNonnegative_eq_true.mp
      ((List.all_eq_true.mp hmult) p.1 hpmem)

  have hs' : ∀ p ∈ L.pairs, p.2.satisfies x := by
    intro p hp
    exact (List.forall_iff_forall_mem.mp hs) p.2 (List.of_mem_zip hp).2

  have hzero : weightedLhsPairs L.pairs x = 0 := by
    rw [weightedLhsPairs_eq_sum_pairCoeff]
    apply Finset.sum_eq_zero
    intro i hi
    have hirange : i.val ∈ List.range 31 := List.mem_range.mpr i.isLt
    have hiInt : pairCoeffInt L.pairs i.val = 0 :=
      intIsZero_eq_true.mp
        ((List.all_eq_true.mp hcoeff) i.val hirange)
    have hiK : pairCoeff (K := K) L.pairs i = 0 := by
      rw [pairCoeff_eq_int, hiInt]
      exact Int.cast_zero
    simp only [hiK, zero_mul]

  have hclose' :
      if combinedStrict L then weightedRhsInt L.pairs ≤ 0
      else weightedRhsInt L.pairs < 0 :=
    (relationClosesBool_eq_true
      (combinedStrict L) (weightedRhsInt L.pairs)).mp hclose

  by_cases hstrict : combinedStrict L = true
  · have hrhsInt : weightedRhsInt L.pairs ≤ 0 := by
      simpa [hstrict] using hclose'
    have hrhs : weightedRhsPairs (K := K) L.pairs ≤ 0 := by
      rw [weightedRhsPairs_eq_int]
      exact Int.cast_nonpos.mpr hrhsInt
    have hweighted :
        weightedLhsPairs L.pairs x < weightedRhsPairs L.pairs :=
      weightedLhsPairs_lt_weightedRhsPairs L.pairs x hm hs'
        ((combinedStrict_iff L).mp hstrict)
    have hbad : (0 : K) < 0 := by
      calc
        (0 : K) = weightedLhsPairs L.pairs x := hzero.symm
        _ < weightedRhsPairs L.pairs := hweighted
        _ ≤ 0 := hrhs
    exact (lt_irrefl (0 : K)) hbad
  · have hrhsInt : weightedRhsInt L.pairs < 0 := by
      simpa [hstrict] using hclose'
    have hrhs : weightedRhsPairs (K := K) L.pairs < 0 := by
      rw [weightedRhsPairs_eq_int]
      exact Int.cast_lt_zero.mpr hrhsInt
    have hweighted :
        weightedLhsPairs L.pairs x ≤ weightedRhsPairs L.pairs :=
      weightedLhsPairs_le_weightedRhsPairs L.pairs x hm hs'
    have hbad : (0 : K) < 0 := by
      calc
        (0 : K) = weightedLhsPairs L.pairs x := hzero.symm
        _ ≤ weightedRhsPairs L.pairs := hweighted
        _ < 0 := hrhs
    exact (lt_irrefl (0 : K)) hbad

/-! ## Two exactly rescaled sample leaves -/

/-- A concise way to write a dense 31-entry integer row in this hand-written
sample. The bulk emitter may emit literal lists instead. -/
def dense31 (f : Nat → ℤ) : List ℤ :=
  (List.range 31).map f

def denseRow (f : Nat → ℤ) (rhs : ℤ) (rel : Bool) : Row :=
  { coeffs := dense31 f, rhs := rhs, rel := rel }

/-- `leaves_sample.json`, leaf 0.  Rows 38 and 39 are multiplied by 2.
After the common multiplier rescaling the multipliers are
`[4, 4, 1, 1, 2, 2]`, and the combined RHS is `-2`. -/
def leaf0 : Leaf :=
  { rows := [
      denseRow (fun
        | 4 => 1
        | 6 => -1
        | _ => 0) 0 false,
      denseRow (fun
        | 6 => 1
        | 8 => -1
        | _ => 0) 0 false,
      denseRow (fun
        | 1 => -1
        | 8 => 2
        | 17 => -2
        | _ => 0) (-1) false,
      denseRow (fun
        | 1 => 1
        | 8 => 2
        | 17 => 2
        | _ => 0) (-1) false,
      denseRow (fun
        | 4 => -1
        | 19 => -1
        | _ => 0) 0 false,
      denseRow (fun
        | 4 => -1
        | 19 => 1
        | _ => 0) 0 false
    ],
    multipliers := [4, 4, 1, 1, 2, 2] }

/-- `leaves_sample.json`, leaf 1. Rows 38 and 39 are multiplied by 4.
After the common multiplier rescaling the multipliers are
`[8, 8, 1, 1, 4, 4]`, and the combined RHS is `-2`. -/
def leaf1 : Leaf :=
  { rows := [
      denseRow (fun
        | 4 => 1
        | 6 => -1
        | _ => 0) 0 false,
      denseRow (fun
        | 6 => 1
        | 8 => -1
        | _ => 0) 0 false,
      denseRow (fun
        | 1 => -1
        | 8 => 4
        | 17 => -4
        | _ => 0) (-1) false,
      denseRow (fun
        | 1 => 1
        | 8 => 4
        | 17 => 4
        | _ => 0) (-1) false,
      denseRow (fun
        | 4 => -1
        | 19 => -1
        | _ => 0) 0 false,
      denseRow (fun
        | 4 => -1
        | 19 => 1
        | _ => 0) 0 false
    ],
    multipliers := [8, 8, 1, 1, 4, 4] }

#eval checkLeaf leaf0
#eval checkLeaf leaf1

-- `by decide` is also a reducing alternative for each closed integer leaf.
example : checkLeaf leaf0 = true := by rfl
example : checkLeaf leaf1 = true := by rfl

/-- Shape of a generated replay theorem. -/
example (x : Fin 31 → ℚ) (hx : satisfiesAll leaf0 x) : False := by
  exact soundness leaf0 (by rfl) x hx

end CertCheck
end Heilbronn8
