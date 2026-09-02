import Heilbronn8.Survivors.Join.HullSevenCutoffClassification

/-!
# Structural reduction for the seven-wheel cutoff classifier

The cutoff at each anchor is one of `1, ..., 5`.  The reversal conditions
at distances two and three contain all of the nontrivial information.  This
file records that information in two Boolean masks:

* `low i` says that the cutoff at `i` is at most two;
* `one i` says that the cutoff at `i` is one.

The distance-three condition says that high cutoffs are the translate of
the low mask.  The distance-two condition says that cutoffs equal to five
are the translate of the one mask.  Consequently the low mask is independent
under translation by three, and a one may occur only at a low position whose
predecessor is also low.  These two masks reconstruct the cutoff function.

The remaining finite theorem ranges over two Boolean masks, hence over
`2^14` inputs rather than the `5^7` cutoff functions used by the original
classifier.  It uses kernel `decide` only.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000

abbrev HullSevenCutoffMask := Fin 7 → Bool

/-- Positions whose mathematical cutoff is at most two. -/
def hullSevenCutoffLowMask (cuts : Fin 7 → Fin 5) :
    HullSevenCutoffMask :=
  fun i => decide ((cuts i).val ≤ 1)

/-- Positions whose mathematical cutoff is one. -/
def hullSevenCutoffOneMask (cuts : Fin 7 → Fin 5) :
    HullSevenCutoffMask :=
  fun i => decide ((cuts i).val = 0)

/-- The low positions contain no pair separated by three. -/
def HullSevenCutoffLowIndependent (low : HullSevenCutoffMask) : Prop :=
  ∀ i : Fin 7, low i = true → low (i + 3) = false

/-- A cutoff equal to one can occur only at a low position whose predecessor
is also low. -/
def HullSevenCutoffOneEligible
    (low one : HullSevenCutoffMask) : Prop :=
  ∀ i : Fin 7, one i = true → low i = true ∧ low (i - 1) = true

/-- Reconstruct the zero-based cutoff from its low and one masks. -/
def hullSevenCutoffDecode
    (low one : HullSevenCutoffMask) : Fin 7 → Fin 5 :=
  fun i =>
    if one i then 0
    else if low i then 1
    else if one (i - 2) then 4
    else if low (i - 3) then 3
    else 2

/-- Positions whose mathematical cutoff is at least four. -/
def hullSevenCutoffHighMask (cuts : Fin 7 → Fin 5) :
    HullSevenCutoffMask :=
  fun i => decide (3 ≤ (cuts i).val)

/-- Positions whose mathematical cutoff is five. -/
def hullSevenCutoffFiveMask (cuts : Fin 7 → Fin 5) :
    HullSevenCutoffMask :=
  fun i => decide ((cuts i).val = 4)

private lemma hullSevenCutoff_complementary_distance_two
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) (i : Fin 7) :
    decide (2 ≤ (cuts i).val + 1) ≠
      decide (5 ≤ (cuts (i + 2)).val + 1) := by
  have h := hcomp i ⟨1, by decide⟩
  fin_cases i <;>
    simpa [hullSevenCutoffDirectedPositive, hullSevenForwardDistance,
      hullSevenCutoffAt] using h

private lemma hullSevenCutoff_complementary_distance_three
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) (i : Fin 7) :
    decide (3 ≤ (cuts i).val + 1) ≠
      decide (4 ≤ (cuts (i + 3)).val + 1) := by
  have h := hcomp i ⟨2, by decide⟩
  fin_cases i <;>
    simpa [hullSevenCutoffDirectedPositive, hullSevenForwardDistance,
      hullSevenCutoffAt] using h

private lemma hullSevenCutoff_five_eq_one_local (left right : Fin 5)
    (h : decide (2 ≤ left.val + 1) ≠
      decide (5 ≤ right.val + 1)) :
    decide (right.val = 4) = decide (left.val = 0) := by
  fin_cases left <;> fin_cases right <;> simp_all

private lemma hullSevenCutoff_high_eq_low_local (left right : Fin 5)
    (h : decide (3 ≤ left.val + 1) ≠
      decide (4 ≤ right.val + 1)) :
    decide (3 ≤ right.val) = decide (left.val ≤ 1) := by
  fin_cases left <;> fin_cases right <;> simp_all

/-- Distance two translates the one mask to the positions whose cutoff is
five. -/
theorem hullSevenCutoff_five_shift
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) (i : Fin 7) :
    hullSevenCutoffFiveMask cuts (i + 2) =
      hullSevenCutoffOneMask cuts i := by
  simpa [hullSevenCutoffFiveMask, hullSevenCutoffOneMask] using
    hullSevenCutoff_five_eq_one_local (cuts i) (cuts (i + 2))
      (hullSevenCutoff_complementary_distance_two cuts hcomp i)

/-- Distance three translates the low mask to the positions whose cutoff is
at least four. -/
theorem hullSevenCutoff_high_shift
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) (i : Fin 7) :
    hullSevenCutoffHighMask cuts (i + 3) =
      hullSevenCutoffLowMask cuts i := by
  simpa [hullSevenCutoffHighMask, hullSevenCutoffLowMask] using
    hullSevenCutoff_high_eq_low_local (cuts i) (cuts (i + 3))
      (hullSevenCutoff_complementary_distance_three cuts hcomp i)

/-- The low mask extracted from complementary cutoffs is independent under
translation by three. -/
theorem hullSevenCutoff_lowIndependent
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) :
    HullSevenCutoffLowIndependent (hullSevenCutoffLowMask cuts) := by
  intro i hlow
  have hhigh : hullSevenCutoffHighMask cuts (i + 3) = true := by
    rw [hullSevenCutoff_high_shift cuts hcomp i]
    exact hlow
  simp [hullSevenCutoffHighMask] at hhigh
  simp [hullSevenCutoffLowMask]
  omega

private lemma hullSevenCutoff_one_implies_low
    (cuts : Fin 7 → Fin 5) (i : Fin 7)
    (hone : hullSevenCutoffOneMask cuts i = true) :
    hullSevenCutoffLowMask cuts i = true := by
  simp [hullSevenCutoffOneMask] at hone
  simp [hullSevenCutoffLowMask]
  omega

private lemma hullSevenCutoff_five_implies_high
    (cuts : Fin 7 → Fin 5) (i : Fin 7)
    (hfive : hullSevenCutoffFiveMask cuts i = true) :
    hullSevenCutoffHighMask cuts i = true := by
  simp [hullSevenCutoffFiveMask] at hfive
  simp [hullSevenCutoffHighMask]
  omega

private lemma finSeven_sub_one_add_three (i : Fin 7) :
    (i - 1) + 3 = i + 2 := by
  fin_cases i <;> decide

/-- The one mask extracted from complementary cutoffs is supported only on
eligible adjacent low positions. -/
theorem hullSevenCutoff_oneEligible
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) :
    HullSevenCutoffOneEligible
      (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts) := by
  intro i hone
  refine ⟨hullSevenCutoff_one_implies_low cuts i hone, ?_⟩
  have hfive : hullSevenCutoffFiveMask cuts (i + 2) = true := by
    rw [hullSevenCutoff_five_shift cuts hcomp i]
    exact hone
  have hhigh := hullSevenCutoff_five_implies_high cuts (i + 2) hfive
  have hshift := hullSevenCutoff_high_shift cuts hcomp (i - 1)
  rw [finSeven_sub_one_add_three] at hshift
  rw [← hshift]
  exact hhigh

/-- Complementary cutoffs are reconstructed exactly from their two masks. -/
theorem hullSevenCutoff_decode_low_one
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) :
    cuts = hullSevenCutoffDecode
      (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts) := by
  funext i
  have hfive : hullSevenCutoffFiveMask cuts i =
      hullSevenCutoffOneMask cuts (i - 2) := by
    simpa using hullSevenCutoff_five_shift cuts hcomp (i - 2)
  have hhigh : hullSevenCutoffHighMask cuts i =
      hullSevenCutoffLowMask cuts (i - 3) := by
    simpa using hullSevenCutoff_high_shift cuts hcomp (i - 3)
  rw [hullSevenCutoffDecode, ← hfive, ← hhigh]
  simp only [hullSevenCutoffOneMask, hullSevenCutoffLowMask,
    hullSevenCutoffFiveMask, hullSevenCutoffHighMask]
  apply Fin.ext
  have hlt : (cuts i).val < 5 := (cuts i).isLt
  by_cases hzero : (cuts i).val = 0
  · simp [hzero]
  by_cases hlow : (cuts i).val ≤ 1
  · have hone : (cuts i).val = 1 := by omega
    simp [hzero, hlow, hone]
  by_cases hfiveValue : (cuts i).val = 4
  · simp [hzero, hlow, hfiveValue]
  by_cases hhighValue : 3 ≤ (cuts i).val
  · have hthree : (cuts i).val = 3 := by omega
    simp [hzero, hlow, hfiveValue, hhighValue, hthree]
  · have htwo : (cuts i).val = 2 := by omega
    simp [hzero, hlow, hfiveValue, hhighValue, htwo]

/-- The complete structural reduction supplied by chord reversal. -/
theorem hullSevenCutoff_structuralReduction
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) :
    HullSevenCutoffLowIndependent (hullSevenCutoffLowMask cuts) ∧
      HullSevenCutoffOneEligible
        (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts) ∧
      cuts = hullSevenCutoffDecode
        (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts) := by
  exact ⟨hullSevenCutoff_lowIndependent cuts hcomp,
    hullSevenCutoff_oneEligible cuts hcomp,
    hullSevenCutoff_decode_low_one cuts hcomp⟩

/-- Explicitly construct decidability for two nested finite universal
quantifiers.  Instance search does not reliably synthesize the inner
`DecidablePred` underneath the outer binder. -/
def hullSevenDecidableForallTwo
    {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop)
    (hP : ∀ a b, Decidable (P a b)) :
    Decidable (∀ a b, P a b) := by
  let outerDec : DecidablePred (fun a : α => ∀ b : β, P a b) :=
    fun a =>
      letI : DecidablePred (fun b : β => P a b) := hP a
      Fintype.decidableForallFintype
  letI := outerDec
  exact Fintype.decidableForallFintype

/-- Decidability wrapper for the common reduced-cutoff theorem shape.  It
enumerates the two Boolean masks explicitly and installs the two structural
premise deciders at each fixed mask pair. -/
def hullSevenCutoffReducedForallDecidable
    (P : HullSevenCutoffMask → HullSevenCutoffMask → Prop)
    (hP : ∀ low one, Decidable (P low one)) :
    Decidable (∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one → P low one) := by
  refine hullSevenDecidableForallTwo
    (fun low one => HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one → P low one) ?_
  intro low one
  letI : Decidable (HullSevenCutoffLowIndependent low) := by
    unfold HullSevenCutoffLowIndependent
    letI : DecidablePred (fun i : Fin 7 =>
        low i = true → low (i + 3) = false) := fun _ => inferInstance
    exact Fintype.decidableForallFintype
  letI : Decidable (HullSevenCutoffOneEligible low one) := by
    unfold HullSevenCutoffOneEligible
    letI : DecidablePred (fun i : Fin 7 =>
        one i = true → low i = true ∧ low (i - 1) = true) :=
      fun _ => inferInstance
    exact Fintype.decidableForallFintype
  letI : Decidable (P low one) := hP low one
  infer_instance

/-- Reduced universal classification.  The kernel enumerates two Boolean
masks and filters them by independence and eligibility. -/
theorem hullSevenCutoffDecode_classification_withPresentation :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
        ∃ orderType ∈ hullSevenTypes,
          hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
              orderType.key ∧
          ∃ rotation : Fin 7, ∃ reflected : Bool,
            hullSevenCutoffPresentationKey
                (hullSevenCutoffDecode low one) rotation.val reflected =
              orderType.key := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (HullSevenCutoffLowIndependent low →
        HullSevenCutoffOneEligible low one →
          ∃ orderType ∈ hullSevenTypes,
            hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
                orderType.key ∧
            ∃ rotation : Fin 7, ∃ reflected : Bool,
              hullSevenCutoffPresentationKey
                  (hullSevenCutoffDecode low one) rotation.val reflected =
                orderType.key) := by
    letI : Decidable (HullSevenCutoffLowIndependent low) := by
      unfold HullSevenCutoffLowIndependent
      letI : DecidablePred (fun i : Fin 7 =>
          low i = true → low (i + 3) = false) := fun _ => inferInstance
      exact Fintype.decidableForallFintype
    letI : Decidable (HullSevenCutoffOneEligible low one) := by
      unfold HullSevenCutoffOneEligible
      letI : DecidablePred (fun i : Fin 7 =>
          one i = true → low i = true ∧ low (i - 1) = true) :=
        fun _ => inferInstance
      exact Fintype.decidableForallFintype
    infer_instance
  let maskDec : DecidablePred (fun low : HullSevenCutoffMask =>
      ∀ one : HullSevenCutoffMask,
        HullSevenCutoffLowIndependent low →
        HullSevenCutoffOneEligible low one →
          ∃ orderType ∈ hullSevenTypes,
            hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
                orderType.key ∧
            ∃ rotation : Fin 7, ∃ reflected : Bool,
              hullSevenCutoffPresentationKey
                  (hullSevenCutoffDecode low one) rotation.val reflected =
                orderType.key) :=
    fun low =>
      letI : DecidablePred (fun one : HullSevenCutoffMask =>
          HullSevenCutoffLowIndependent low →
          HullSevenCutoffOneEligible low one →
            ∃ orderType ∈ hullSevenTypes,
              hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
                  orderType.key ∧
              ∃ rotation : Fin 7, ∃ reflected : Bool,
                hullSevenCutoffPresentationKey
                    (hullSevenCutoffDecode low one) rotation.val reflected =
                  orderType.key) := outcomeDec low
      Fintype.decidableForallFintype
  letI := maskDec
  decide

/-- Classification with a presentation, obtained through the two-mask
structural reduction. -/
theorem hullSevenCutoff_classification_reduced_withPresentation_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts) :
    ∃ orderType ∈ hullSevenTypes,
      hullSevenCutoffOrderType cuts = orderType.key ∧
      ∃ rotation : Fin 7, ∃ reflected : Bool,
        hullSevenCutoffPresentationKey cuts rotation.val reflected =
          orderType.key := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hclassified :=
    hullSevenCutoffDecode_classification_withPresentation
      (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
      hindependent heligible
  rw [← hdecode] at hclassified
  exact hclassified

/-- The reduced classifier with the same Boolean entry condition and the
same key and presentation conclusion as the original exhaustive theorem. -/
theorem hullSevenCutoff_classification_reduced_withPresentation
    (cuts : Fin 7 → Fin 5)
    (hok : hullSevenCutoffComplementOK cuts = true) :
    ∃ orderType ∈ hullSevenTypes,
      hullSevenCutoffOrderType cuts = orderType.key ∧
      ∃ rotation : Fin 7, ∃ reflected : Bool,
        hullSevenCutoffPresentationKey cuts rotation.val reflected =
          orderType.key := by
  exact
    hullSevenCutoff_classification_reduced_withPresentation_of_complementary
      cuts ((hullSevenCutoffComplementOK_eq_true_iff cuts).mp hok)

/-- Key-only wrapper matching `hullSevenCutoff_classification`. -/
theorem hullSevenCutoff_classification_reduced
    (cuts : Fin 7 → Fin 5)
    (hok : hullSevenCutoffComplementOK cuts = true) :
    ∃ orderType ∈ hullSevenTypes,
      hullSevenCutoffOrderType cuts = orderType.key := by
  obtain ⟨orderType, htype, hkey, _rotation, _reflected, _hpresentation⟩ :=
    hullSevenCutoff_classification_reduced_withPresentation cuts hok
  exact ⟨orderType, htype, hkey⟩

end Heilbronn8
