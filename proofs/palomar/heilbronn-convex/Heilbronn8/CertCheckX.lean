import Heilbronn8.CertCheck

/-!
# Exact robust Farkas checker for x-collapse leaves

The five x-coordinates are parameters and the five y-coordinates are the LP
variables. Each y coefficient and each right-hand side is an affine function
of x. The Boolean checker requires the five combined y coefficients to vanish
as affine polynomials and bounds only the combined affine right-hand side.

## Emitter contract

The emitter must guarantee all of the following.

* An endpoint `⟨n, e⟩` denotes the rational `n / 2^e`. Emit exactly five
  ordered lower/upper pairs. This dyadic representation is the canonical
  all-integer encoding of `xbox : 5 pairs of ℚ bounds`; `Dyadic.ratValue`
  and `Leaf.xboxRat` below expose the literal rational view.
* A row contains exactly five `yCoeffs` vectors and one `rhs` vector. Each
  of these six vectors has exactly six integer entries, ordered as constant,
  x₀, ..., x₄. The represented inequality is
  `sum_j yCoeffs[j](x) * y_j <= rhs(x)`, or `<` when `rel = true`.
  Beat rows may therefore be bilinear in `(x,y)`.
* For each source row, multiply every one of its 36 affine base coefficients
  by one positive integer clearing all rational denominators. Positive scaling
  must preserve its relation and `rel` must faithfully record strictness.
* After row scaling, rescale the rational Farkas dual by one positive common
  factor and compensate for the individual row scales, so every emitted
  multiplier is an integer. Multipliers must align with rows and be
  nonnegative. For every y-column and every affine base, their weighted
  integer sum must be exactly zero. No midpoint-only cancellation is allowed.
* The checker selects a dyadic endpoint for each coefficient of the combined
  RHS, structurally clears all powers-of-two denominators, and checks the sign
  of the resulting integer upper numerator. A weak combination needs a
  strictly negative upper numerator. A combination containing a strict row
  with positive multiplier may close at upper numerator zero. The emitter
  must not weaken `<` to `<=` before setting these flags.

The Boolean path performs only `Nat`, `Int`, list, and `Bool` computation.
In particular it never normalizes `Rat`; closed emitted leaves reduce with
`by rfl`.
-/

namespace Heilbronn8
namespace CertCheckX

abbrev ZVec := List ℤ

/-- Exact all-integer encoding of the rational `numerator / 2^exponent`. -/
structure Dyadic where
  numerator : ℤ
  exponent : Nat
deriving Repr, DecidableEq

namespace Dyadic

def denominator (d : Dyadic) : Nat :=
  2 ^ d.exponent

def value {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (d : Dyadic) : K :=
  Int.cast d.numerator / Nat.cast d.denominator

def ratValue (d : Dyadic) : ℚ :=
  d.value

lemma denominator_pos (d : Dyadic) : 0 < d.denominator := by
  simp [denominator]

end Dyadic

/-- Six affine forms: five y-coefficients followed by the RHS. -/
structure Row where
  yCoeffs : List ZVec
  rhs : ZVec
  rel : Bool
deriving Repr, DecidableEq

structure Leaf where
  xbox : List (Dyadic × Dyadic)
  rows : List Row
  multipliers : List ℤ
deriving Repr, DecidableEq

def Leaf.xboxRat (L : Leaf) : List (ℚ × ℚ) :=
  L.xbox.map fun b => (b.1.ratValue, b.2.ratValue)

def zeroDyadic : Dyadic :=
  ⟨0, 0⟩

def zeroBound : Dyadic × Dyadic :=
  (zeroDyadic, zeroDyadic)

def affineEval {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (a : ZVec) (x : Fin 5 → K) : K :=
  Int.cast (a.getD 0 0) +
    ∑ i : Fin 5, Int.cast (a.getD (i.val + 1) 0) * x i

def Row.yCoeff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (r : Row) (j : Fin 5) (x : Fin 5 → K) : K :=
  affineEval (r.yCoeffs.getD j.val []) x

def Row.rhsValue {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (r : Row) (x : Fin 5 → K) : K :=
  affineEval r.rhs x

def Row.lhs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (r : Row) (x y : Fin 5 → K) : K :=
  ∑ j : Fin 5, r.yCoeff j x * y j

def Row.satisfies {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (r : Row) (x y : Fin 5 → K) : Prop :=
  if r.rel then r.lhs x y < r.rhsValue x
  else r.lhs x y ≤ r.rhsValue x

def Leaf.inXbox {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (L : Leaf) (x : Fin 5 → K) : Prop :=
  ∀ i : Fin 5,
    (L.xbox.getD i.val zeroBound).1.value ≤ x i ∧
      x i ≤ (L.xbox.getD i.val zeroBound).2.value

def satisfiesAll {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (L : Leaf) (x y : Fin 5 → K) : Prop :=
  L.rows.Forall (fun r => r.satisfies x y)

def Leaf.pairs (L : Leaf) : List (ℤ × Row) :=
  L.multipliers.zip L.rows

def weightedLhsPairs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x y : Fin 5 → K) : K :=
  (ps.map fun p => Int.cast p.1 * p.2.lhs x y).sum

def weightedRhsPairs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x : Fin 5 → K) : K :=
  (ps.map fun p => Int.cast p.1 * p.2.rhsValue x).sum

def pairYAffine {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (j : Fin 5) (x : Fin 5 → K) : K :=
  (ps.map fun p => Int.cast p.1 * p.2.yCoeff j x).sum

/-! ### All-integer Boolean computation -/

def pairYCoeffInt : List (ℤ × Row) → Nat → Nat → ℤ
  | [], _, _ => 0
  | p :: ps, j, k =>
      p.1 * (p.2.yCoeffs.getD j []).getD k 0 +
        pairYCoeffInt ps j k

def pairRhsCoeffInt : List (ℤ × Row) → Nat → ℤ
  | [], _ => 0
  | p :: ps, k =>
      p.1 * p.2.rhs.getD k 0 + pairRhsCoeffInt ps k

def combinedStrict (L : Leaf) : Bool :=
  L.pairs.any fun p => CertCheck.intPositive p.1 && p.2.rel

def selectedEndpoint (a : ℤ) (b : Dyadic × Dyadic) : Dyadic :=
  if CertCheck.intNegative a then b.1 else b.2

/-- Positive denominator clearing all selected dyadic endpoints. -/
def upperDen : List (ℤ × Dyadic) → Nat
  | [] => 1
  | (_, d) :: ts => d.denominator * upperDen ts

/-- Numerator of `constant + sum a_i * endpoint_i` over `upperDen`. -/
def upperNum (constant : ℤ) : List (ℤ × Dyadic) → ℤ
  | [] => constant
  | (a, d) :: ts =>
      a * d.numerator * Int.ofNat (upperDen ts) +
        Int.ofNat d.denominator * upperNum constant ts

def upperValue {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (constant : ℤ) :
    List (ℤ × Dyadic) → K
  | [] => Int.cast constant
  | (a, d) :: ts =>
      Int.cast a * d.value + upperValue constant ts

def rhsTerms (L : Leaf) : List (ℤ × Dyadic) :=
  List.ofFn fun i : Fin 5 =>
    let a := pairRhsCoeffInt L.pairs (i.val + 1)
    (a, selectedEndpoint a (L.xbox.getD i.val zeroBound))

def rhsUpperNumerator (L : Leaf) : ℤ :=
  upperNum (pairRhsCoeffInt L.pairs 0) (rhsTerms L)

def dyadicLeBool (a b : Dyadic) : Bool :=
  CertCheck.intNonpositive
    (a.numerator * Int.ofNat b.denominator -
      b.numerator * Int.ofNat a.denominator)

def lengthOK (L : Leaf) : Bool :=
  CertCheck.natEq L.rows.length L.multipliers.length

def xboxOK (L : Leaf) : Bool :=
  CertCheck.natEq L.xbox.length 5 &&
    L.xbox.all fun b => dyadicLeBool b.1 b.2

def rowShapeOK (r : Row) : Bool :=
  CertCheck.natEq r.yCoeffs.length 5 &&
    r.yCoeffs.all (fun a => CertCheck.natEq a.length 6) &&
    CertCheck.natEq r.rhs.length 6

def shapeOK (L : Leaf) : Bool :=
  L.rows.all rowShapeOK

def multipliersOK (L : Leaf) : Bool :=
  L.multipliers.all CertCheck.intNonnegative

def yCoefficientsZero (L : Leaf) : Bool :=
  (List.range 5).all fun j =>
    (List.range 6).all fun k =>
      CertCheck.intIsZero (pairYCoeffInt L.pairs j k)

def relationClosesBool
    (strict : Bool) (upperNumerator : ℤ) : Bool :=
  if strict then CertCheck.intNonpositive upperNumerator
  else CertCheck.intNegative upperNumerator

/-- Kernel-reducible checker for one robust x-collapse leaf. -/
def CheckLeafX (L : Leaf) : Bool :=
  lengthOK L &&
  xboxOK L &&
  shapeOK L &&
  multipliersOK L &&
  yCoefficientsZero L &&
  relationClosesBool (combinedStrict L) (rhsUpperNumerator L)

theorem CheckLeafX_eq_true (L : Leaf) :
    CheckLeafX L = true ↔
      lengthOK L = true ∧
      xboxOK L = true ∧
      shapeOK L = true ∧
      multipliersOK L = true ∧
      yCoefficientsZero L = true ∧
      relationClosesBool
        (combinedStrict L) (rhsUpperNumerator L) = true := by
  simp only [CheckLeafX, Bool.and_eq_true, and_assoc]

theorem combinedStrict_iff (L : Leaf) :
    combinedStrict L = true ↔
      ∃ p ∈ L.pairs, 0 < p.1 ∧ p.2.rel = true := by
  simp [combinedStrict, CertCheck.intPositive_eq_true]

lemma relationClosesBool_eq_true (strict : Bool) (upper : ℤ) :
    relationClosesBool strict upper = true ↔
      if strict then upper ≤ 0 else upper < 0 := by
  cases strict <;>
    simp [relationClosesBool, CertCheck.intNonpositive_eq_true,
      CertCheck.intNegative_eq_true]

/-! ### One-time ordered-field proof -/

lemma Row.le_of_satisfies
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r : Row} {x y : Fin 5 → K} (h : r.satisfies x y) :
    r.lhs x y ≤ r.rhsValue x := by
  cases hrel : r.rel with
  | false =>
      simpa [Row.satisfies, hrel] using h
  | true =>
      have hlt : r.lhs x y < r.rhsValue x := by
        simpa [Row.satisfies, hrel] using h
      exact hlt.le

lemma mul_affine_add
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m c C : K) (a b x : Fin 5 → K) :
    m * (c + ∑ i, a i * x i) + (C + ∑ i, b i * x i) =
      (m * c + C) + ∑ i, (m * a i + b i) * x i := by
  rw [mul_add, Finset.mul_sum]
  have hsum :
      (∑ i : Fin 5, m * (a i * x i)) +
          ∑ i : Fin 5, b i * x i =
        ∑ i : Fin 5, (m * a i + b i) * x i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ = m * c + C +
        ((∑ i : Fin 5, m * (a i * x i)) +
          ∑ i : Fin 5, b i * x i) := by
      ring
    _ = _ := by rw [hsum]

lemma pairYAffine_eq_components
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (j : Fin 5) (x : Fin 5 → K) :
    pairYAffine ps j x =
      Int.cast (pairYCoeffInt ps j.val 0) +
        ∑ i : Fin 5,
          Int.cast (pairYCoeffInt ps j.val (i.val + 1)) * x i := by
  induction ps with
  | nil =>
      simp [pairYAffine, pairYCoeffInt]
  | cons p ps ih =>
      change
        Int.cast p.1 *
              (Int.cast ((p.2.yCoeffs.getD j.val []).getD 0 0) +
                ∑ i : Fin 5,
                  Int.cast
                    ((p.2.yCoeffs.getD j.val []).getD
                      (i.val + 1) 0) *
                    x i) +
            pairYAffine ps j x =
          Int.cast
                (p.1 *
                    (p.2.yCoeffs.getD j.val []).getD 0 0 +
                  pairYCoeffInt ps j.val 0) +
            ∑ i : Fin 5,
              Int.cast
                    (p.1 *
                        (p.2.yCoeffs.getD j.val []).getD
                          (i.val + 1) 0 +
                      pairYCoeffInt ps j.val (i.val + 1)) *
                x i
      rw [ih]
      simp only [Int.cast_add, Int.cast_mul]
      exact mul_affine_add _ _ _
        (fun i =>
          Int.cast
            ((p.2.yCoeffs.getD j.val []).getD (i.val + 1) 0))
        (fun i =>
          Int.cast (pairYCoeffInt ps j.val (i.val + 1)))
        x

lemma weightedRhsPairs_eq_components
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x : Fin 5 → K) :
    weightedRhsPairs ps x =
      Int.cast (pairRhsCoeffInt ps 0) +
        ∑ i : Fin 5,
          Int.cast (pairRhsCoeffInt ps (i.val + 1)) * x i := by
  induction ps with
  | nil =>
      simp [weightedRhsPairs, pairRhsCoeffInt]
  | cons p ps ih =>
      change
        Int.cast p.1 *
              (Int.cast (p.2.rhs.getD 0 0) +
                ∑ i : Fin 5,
                  Int.cast (p.2.rhs.getD (i.val + 1) 0) * x i) +
            weightedRhsPairs ps x =
          Int.cast
                (p.1 * p.2.rhs.getD 0 0 +
                  pairRhsCoeffInt ps 0) +
            ∑ i : Fin 5,
              Int.cast
                    (p.1 * p.2.rhs.getD (i.val + 1) 0 +
                      pairRhsCoeffInt ps (i.val + 1)) *
                x i
      rw [ih]
      simp only [Int.cast_add, Int.cast_mul]
      exact mul_affine_add _ _ _
        (fun i => Int.cast (p.2.rhs.getD (i.val + 1) 0))
        (fun i => Int.cast (pairRhsCoeffInt ps (i.val + 1)))
        x

lemma weightedLhsPairs_eq_sum_pairYAffine
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x y : Fin 5 → K) :
    weightedLhsPairs ps x y =
      ∑ j : Fin 5, pairYAffine ps j x * y j := by
  induction ps with
  | nil =>
      simp [weightedLhsPairs, pairYAffine]
  | cons p ps ih =>
      change
        Int.cast p.1 *
              (∑ j : Fin 5, p.2.yCoeff j x * y j) +
            weightedLhsPairs ps x y =
          ∑ j : Fin 5,
            (Int.cast p.1 * p.2.yCoeff j x +
                pairYAffine ps j x) *
              y j
      rw [ih, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring_nf

lemma weightedLhsPairs_le_weightedRhsPairs
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x y : Fin 5 → K)
    (hm : ∀ p ∈ ps, 0 ≤ p.1)
    (hs : ∀ p ∈ ps, p.2.satisfies x y) :
    weightedLhsPairs ps x y ≤ weightedRhsPairs ps x := by
  unfold weightedLhsPairs weightedRhsPairs
  exact List.sum_le_sum fun p hp =>
    mul_le_mul_of_nonneg_left
      (Row.le_of_satisfies (hs p hp))
      (Int.cast_nonneg (hm p hp))

lemma weightedLhsPairs_lt_weightedRhsPairs
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ps : List (ℤ × Row)) (x y : Fin 5 → K)
    (hm : ∀ p ∈ ps, 0 ≤ p.1)
    (hs : ∀ p ∈ ps, p.2.satisfies x y)
    (hstrict : ∃ p ∈ ps, 0 < p.1 ∧ p.2.rel = true) :
    weightedLhsPairs ps x y < weightedRhsPairs ps x := by
  unfold weightedLhsPairs weightedRhsPairs
  apply List.sum_lt_sum
  · intro p hp
    exact mul_le_mul_of_nonneg_left
      (Row.le_of_satisfies (hs p hp))
      (Int.cast_nonneg (hm p hp))
  · rcases hstrict with ⟨p, hp, hmp, hrel⟩
    refine ⟨p, hp, ?_⟩
    apply mul_lt_mul_of_pos_left _ (Int.cast_pos.mpr hmp)
    simpa [Row.satisfies, hrel] using hs p hp

lemma upperDen_pos (ts : List (ℤ × Dyadic)) :
    0 < upperDen ts := by
  induction ts with
  | nil =>
      simp [upperDen]
  | cons t ts ih =>
      rcases t with ⟨a, d⟩
      simp only [upperDen]
      exact Nat.mul_pos d.denominator_pos ih

lemma upperValue_eq_div
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (constant : ℤ) (ts : List (ℤ × Dyadic)) :
    upperValue (K := K) constant ts =
      Int.cast (upperNum constant ts) /
        Nat.cast (upperDen ts) := by
  induction ts with
  | nil =>
      simp [upperValue, upperNum, upperDen]
  | cons t ts ih =>
      rcases t with ⟨a, d⟩
      simp only [upperValue, upperNum, upperDen]
      rw [ih]
      unfold Dyadic.value
      simp only [Nat.cast_mul, Int.cast_add, Int.cast_mul,
        Int.ofNat_eq_natCast, Int.cast_natCast]
      have hd : (Nat.cast d.denominator : K) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (Nat.ne_of_gt d.denominator_pos)
      have hts : (Nat.cast (upperDen ts) : K) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (Nat.ne_of_gt (upperDen_pos ts))
      field_simp [hd, hts]

lemma upperValue_eq_sum
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (constant : ℤ) (ts : List (ℤ × Dyadic)) :
    upperValue (K := K) constant ts =
      Int.cast constant +
        (ts.map fun t => Int.cast t.1 * t.2.value).sum := by
  induction ts with
  | nil =>
      simp [upperValue]
  | cons t ts ih =>
      rcases t with ⟨a, d⟩
      simp only [upperValue, List.map_cons, List.sum_cons]
      rw [ih]
      ring

lemma mul_le_selectedEndpoint
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : ℤ) (b : Dyadic × Dyadic) (z : K)
    (hz : b.1.value ≤ z ∧ z ≤ b.2.value) :
    Int.cast a * z ≤
      Int.cast a * (selectedEndpoint a b).value := by
  cases hsign : CertCheck.intNegative a with
  | false =>
      have ha : 0 ≤ a := by
        apply le_of_not_gt
        intro hneg
        have : CertCheck.intNegative a = true :=
          CertCheck.intNegative_eq_true.mpr hneg
        simp [hsign] at this
      simp only [selectedEndpoint, hsign, Bool.false_eq_true,
        ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hz.2 (Int.cast_nonneg ha)
  | true =>
      have ha : a ≤ 0 :=
        (CertCheck.intNegative_eq_true.mp hsign).le
      simp only [selectedEndpoint, hsign, ↓reduceIte]
      exact mul_le_mul_of_nonpos_left
        hz.1 (Int.cast_nonpos.mpr ha)

lemma weightedRhsPairs_le_upperValue
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : Leaf) (x : Fin 5 → K) (hx : L.inXbox x) :
    weightedRhsPairs L.pairs x ≤
      upperValue
        (pairRhsCoeffInt L.pairs 0) (rhsTerms L) := by
  rw [weightedRhsPairs_eq_components, upperValue_eq_sum]
  simp only [rhsTerms, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_selectedEndpoint
    (pairRhsCoeffInt L.pairs (i.val + 1))
    (L.xbox.getD i.val zeroBound)
    (x i)
    (hx i)

/-- A checked robust leaf excludes every point in its x-box over any ordered
field. In particular, instantiate `K := ℝ` for the geometric replay. -/
theorem soundness
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : Leaf) (hcheck : CheckLeafX L = true) :
    ∀ (x y : Fin 5 → K),
      L.inXbox x → satisfiesAll L x y → False := by
  intro x y hx hs
  rcases (CheckLeafX_eq_true L).mp hcheck with
    ⟨_hlen, _hxbox, _hshape, hmult, hcoeff, hclose⟩

  have hm : ∀ p ∈ L.pairs, 0 ≤ p.1 := by
    intro p hp
    have hpmem : p.1 ∈ L.multipliers :=
      (List.of_mem_zip hp).1
    exact CertCheck.intNonnegative_eq_true.mp
      ((List.all_eq_true.mp hmult) p.1 hpmem)

  have hs' : ∀ p ∈ L.pairs, p.2.satisfies x y := by
    intro p hp
    exact
      (List.forall_iff_forall_mem.mp hs)
        p.2 (List.of_mem_zip hp).2

  have hbase :
      ∀ (j : Fin 5) (k : Nat), k < 6 →
        pairYCoeffInt L.pairs j.val k = 0 := by
    intro j k hk
    exact CertCheck.intIsZero_eq_true.mp
      ((List.all_eq_true.mp
          ((List.all_eq_true.mp hcoeff)
            j.val (List.mem_range.mpr j.isLt)))
        k (List.mem_range.mpr hk))

  have hpair :
      ∀ j : Fin 5, pairYAffine L.pairs j x = 0 := by
    intro j
    rw [pairYAffine_eq_components]
    rw [hbase j 0 (by omega)]
    simp only [Int.cast_zero, zero_add]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hbase j (i.val + 1) (by omega)]
    simp

  have hzero :
      weightedLhsPairs L.pairs x y = 0 := by
    rw [weightedLhsPairs_eq_sum_pairYAffine]
    apply Finset.sum_eq_zero
    intro j hj
    simp [hpair j]

  have hclose' :
      if combinedStrict L then rhsUpperNumerator L ≤ 0
      else rhsUpperNumerator L < 0 :=
    (relationClosesBool_eq_true
      (combinedStrict L) (rhsUpperNumerator L)).mp hclose

  have hrhsBound :
      weightedRhsPairs L.pairs x ≤
        upperValue
          (pairRhsCoeffInt L.pairs 0) (rhsTerms L) :=
    weightedRhsPairs_le_upperValue L x hx

  by_cases hstrict : combinedStrict L = true
  · have hnum : rhsUpperNumerator L ≤ 0 := by
      simpa [hstrict] using hclose'
    have hupper :
        upperValue (K := K)
            (pairRhsCoeffInt L.pairs 0) (rhsTerms L) ≤ 0 := by
      rw [upperValue_eq_div]
      exact div_nonpos_of_nonpos_of_nonneg
        (Int.cast_nonpos.mpr hnum)
        (Nat.cast_nonneg _)
    have hrhs : weightedRhsPairs L.pairs x ≤ 0 :=
      hrhsBound.trans hupper
    have hweighted :
        weightedLhsPairs L.pairs x y <
          weightedRhsPairs L.pairs x :=
      weightedLhsPairs_lt_weightedRhsPairs
        L.pairs x y hm hs'
        ((combinedStrict_iff L).mp hstrict)
    have hbad : (0 : K) < 0 := by
      calc
        (0 : K) =
            weightedLhsPairs L.pairs x y := hzero.symm
        _ < weightedRhsPairs L.pairs x := hweighted
        _ ≤ 0 := hrhs
    exact (lt_irrefl (0 : K)) hbad
  · have hnum : rhsUpperNumerator L < 0 := by
      simpa [hstrict] using hclose'
    have hupper :
        upperValue (K := K)
            (pairRhsCoeffInt L.pairs 0) (rhsTerms L) < 0 := by
      rw [upperValue_eq_div]
      exact div_neg_of_neg_of_pos
        (Int.cast_lt_zero.mpr hnum)
        (Nat.cast_pos.mpr (upperDen_pos (rhsTerms L)))
    have hrhs : weightedRhsPairs L.pairs x < 0 :=
      hrhsBound.trans_lt hupper
    have hweighted :
        weightedLhsPairs L.pairs x y ≤
          weightedRhsPairs L.pairs x :=
      weightedLhsPairs_le_weightedRhsPairs
        L.pairs x y hm hs'
    have hbad : (0 : K) < 0 := by
      calc
        (0 : K) =
            weightedLhsPairs L.pairs x y := hzero.symm
        _ ≤ weightedRhsPairs L.pairs x := hweighted
        _ < 0 := hrhs
    exact (lt_irrefl (0 : K)) hbad

/-! ## Small kernel-reduction examples -/

def d0 (n : ℤ) : Dyadic :=
  ⟨n, 0⟩

def halfBox : List (Dyadic × Dyadic) :=
  [ (d0 0, ⟨1, 1⟩),
    (d0 (-1), d0 1),
    (d0 (-1), d0 1),
    (d0 (-1), d0 1),
    (d0 (-1), d0 1) ]

def unitBox : List (Dyadic × Dyadic) :=
  [ (d0 (-1), d0 1),
    (d0 (-1), d0 1),
    (d0 (-1), d0 1),
    (d0 (-1), d0 1),
    (d0 (-1), d0 1) ]

def zero6 : ZVec :=
  [0, 0, 0, 0, 0, 0]

def firstY (a : ℤ) : ZVec :=
  [a, 0, 0, 0, 0, 0]

def firstOnly (a : ℤ) : List ZVec :=
  [firstY a, zero6, zero6, zero6, zero6]

/-- Combining the two weak rows gives `0 <= x₀ - 1`; on
`0 <= x₀ <= 1/2` its cleared upper numerator is `-1`. -/
def weakExample : Leaf :=
  { xbox := halfBox
    rows := [
      { yCoeffs := firstOnly 1
        rhs := [0, 1, 0, 0, 0, 0]
        rel := false },
      { yCoeffs := firstOnly (-1)
        rhs := [-1, 0, 0, 0, 0, 0]
        rel := false }
    ]
    multipliers := [1, 1] }

/-- The y and x coefficients cancel. One positive-weight row is strict, so
the resulting strict inequality `0 < 0` closes at upper numerator zero. -/
def strictExample : Leaf :=
  { xbox := unitBox
    rows := [
      { yCoeffs := firstOnly 1
        rhs := [0, 1, 0, 0, 0, 0]
        rel := true },
      { yCoeffs := firstOnly (-1)
        rhs := [0, -1, 0, 0, 0, 0]
        rel := false }
    ]
    multipliers := [1, 1] }

example : CheckLeafX weakExample = true := by
  rfl

example : CheckLeafX strictExample = true := by
  rfl

example (x y : Fin 5 → ℝ)
    (hx : weakExample.inXbox x)
    (hrows : satisfiesAll weakExample x y) : False := by
  exact soundness weakExample (by rfl) x y hx hrows

end CertCheckX
end Heilbronn8
