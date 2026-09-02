import Heilbronn8.QuadHull.OrbitICoarseClassifier
import Heilbronn8.QuadHull.OrbitIIGeometry
import Heilbronn8.QuadHull.SectorGeometry

/-!
# Global four-sector dispatcher

This is the theorem-level replacement for a row-by-row hull-four corpus.  It
does three finite things only:

* chooses the four labels outside a named hull by extending its labels to a
  permutation;
* classifies the four open diagonal sectors;
* sends the resulting normalized chart to the balanced, coarse orbit-I, direct
  orbit-II, or reflected/reversed orbit-II producer.

The only exhaustive proof is the `4^4` sector lemma below.  It contains no
configuration records and no sign words.
-/

namespace Heilbronn8.QuadHull

/-! ## Off-hull label selection -/

private def hullSlot (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩

private def innerSlot (i : Fin 4) : Fin 8 :=
  ⟨4 + i.val, by omega⟩

private theorem hullSlot_injective : Function.Injective hullSlot := by
  intro i j hij
  apply Fin.ext
  simpa [hullSlot] using congrArg (fun x : Fin 8 => x.val) hij

private theorem innerSlot_injective : Function.Injective innerSlot := by
  intro i j hij
  apply Fin.ext
  simpa [innerSlot] using congrArg (fun x : Fin 8 => x.val) hij

private theorem hullSlot_ne_innerSlot (i j : Fin 4) :
    hullSlot i ≠ innerSlot j := by
  intro hij
  have hval := congrArg (fun x : Fin 8 => x.val) hij
  simp only [hullSlot, innerSlot] at hval
  omega

private theorem hullSlot_ne (i j : Fin 4) (hij : i ≠ j) :
    hullSlot i ≠ hullSlot j := by
  exact fun h => hij (hullSlot_injective h)

/-- Every slot is either one of the first four hull slots or one of the last
four inner slots.  This avoids repeatedly case-splitting an arbitrary
`Fin 8`. -/
private theorem finEight_slotCases (i : Fin 8) :
    (∃ j : Fin 4, i = hullSlot j) ∨ ∃ j : Fin 4, i = innerSlot j := by
  by_cases hlow : i.val < 4
  · left
    refine ⟨⟨i.val, hlow⟩, ?_⟩
    apply Fin.ext
    rfl
  · right
    have hge : 4 ≤ i.val := by omega
    have hlt : i.val - 4 < 4 := by omega
    refine ⟨⟨i.val - 4, hlt⟩, ?_⟩
    apply Fin.ext
    simp only [innerSlot]
    omega

/-- The proposed four hull labels as an embedding candidate. -/
def hullFourLabels (A B C D : Fin 8) : Fin 4 → Fin 8 := ![A, B, C, D]

/-- Extend the four hull labels to a permutation of all eight labels.  The
images of slots `4,5,6,7` are therefore exactly the off-hull labels. -/
noncomputable def extendHullLabels (A B C D : Fin 8)
    (hinjective : Function.Injective (hullFourLabels A B C D)) :
    Equiv.Perm (Fin 8) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    hullSlot (hullFourLabels A B C D) hullSlot_injective hinjective)

@[simp] theorem extendHullLabels_hull (A B C D : Fin 8)
    (hinjective : Function.Injective (hullFourLabels A B C D))
    (i : Fin 4) :
    extendHullLabels A B C D hinjective (hullSlot i) =
      hullFourLabels A B C D i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    hullSlot (hullFourLabels A B C D) hullSlot_injective hinjective) i

/-- The proof-selected `i`th off-hull label. -/
noncomputable def selectedOffHullLabel (A B C D : Fin 8)
    (hinjective : Function.Injective (hullFourLabels A B C D))
    (i : Fin 4) : Fin 8 :=
  extendHullLabels A B C D hinjective (innerSlot i)

/-- Hull labels followed by the selected complement form a permutation. -/
theorem selectedQuadLabels_injective (A B C D : Fin 8)
    (hinjective : Function.Injective (hullFourLabels A B C D)) :
    Function.Injective
      (quadLabels A B C D
        (selectedOffHullLabel A B C D hinjective 0)
        (selectedOffHullLabel A B C D hinjective 1)
        (selectedOffHullLabel A B C D hinjective 2)
        (selectedOffHullLabel A B C D hinjective 3)) := by
  have heq :
      quadLabels A B C D
          (selectedOffHullLabel A B C D hinjective 0)
          (selectedOffHullLabel A B C D hinjective 1)
          (selectedOffHullLabel A B C D hinjective 2)
          (selectedOffHullLabel A B C D hinjective 3) =
        extendHullLabels A B C D hinjective := by
    funext i
    rcases finEight_slotCases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hj := extendHullLabels_hull A B C D hinjective j
      fin_cases j <;>
        simpa [quadLabels, hullFourLabels, hullSlot] using hj.symm
    · fin_cases j <;>
        simp [quadLabels, selectedOffHullLabel, innerSlot]
  rw [heq]
  exact (extendHullLabels A B C D hinjective).injective

/-! ## Boundary geometry -/

/-- A strictly oriented quadrilateral together with its four remaining
labels, all strictly on the inner side of every boundary edge. -/
structure HullFourBoundaryGeometry
    (v : Fin 8 → Point) (A B C D : Fin 8) where
  inner : Fin 4 → Fin 8
  labels_injective : Function.Injective
    (quadLabels A B C D (inner 0) (inner 1) (inner 2) (inner 3))
  ccw : CCWQuad (v A) (v B) (v C) (v D)
  inner_AB : ∀ i, 0 < sig (v A) (v B) (v (inner i))
  inner_BC : ∀ i, 0 < sig (v B) (v C) (v (inner i))
  inner_CD : ∀ i, 0 < sig (v C) (v D) (v (inner i))
  inner_DA : ∀ i, 0 < sig (v D) (v A) (v (inner i))

@[simp] def HullFourBoundaryGeometry.labels
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D) : Fin 8 → Fin 8 :=
  quadLabels A B C D (h.inner 0) (h.inner 1) (h.inner 2) (h.inner 3)

@[simp] private theorem HullFourBoundaryGeometry.labels_innerSlot
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D) (i : Fin 4) :
    h.labels (innerSlot i) = h.inner i := by
  fin_cases i <;> rfl

@[simp] private theorem HullFourBoundaryGeometry.labels_hullSlot
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D) (i : Fin 4) :
    h.labels (hullSlot i) = hullFourLabels A B C D i := by
  fin_cases i <;> rfl

/-- Boundary-edge positivity and a nonzero diagonal put every off-hull point
strictly in one of the two `AC` fan triangles. -/
private theorem HullFourBoundaryGeometry.insideFan
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (hmzero : minTri v ≠ 0) (i : Fin 4) :
    TriHull.InTriStrict (v (h.inner i)) (v A) (v B) (v C) ∨
      TriHull.InTriStrict (v (h.inner i)) (v A) (v C) (v D) := by
  have hlabels : Function.Injective h.labels := by
    simpa [HullFourBoundaryGeometry.labels] using h.labels_injective
  have hiA : h.inner i ≠ A := by
    have hne := hlabels.ne (Ne.symm (hullSlot_ne_innerSlot 0 i))
    rw [h.labels_innerSlot, h.labels_hullSlot] at hne
    simpa [hullFourLabels] using hne
  have hiC : h.inner i ≠ C := by
    have hne := hlabels.ne (Ne.symm (hullSlot_ne_innerSlot 2 i))
    rw [h.labels_innerSlot, h.labels_hullSlot] at hne
    simpa [hullFourLabels] using hne
  have hAC : A ≠ C := by
    have hne := hlabels.ne (show (0 : Fin 8) ≠ 2 by decide)
    change A ≠ C at hne
    exact hne
  have hdiagNe : sig (v A) (v (h.inner i)) (v C) ≠ 0 :=
    sig_ne_zero_of_minTri_ne_zero hmzero hiA.symm hAC hiC
  by_cases hdiag : 0 < sig (v A) (v (h.inner i)) (v C)
  · apply Or.inl
    apply OrbitIIInternal.inTriStrict_of_fan_pos h.ccw.1
    · calc
        0 < sig (v B) (v C) (v (h.inner i)) := h.inner_BC i
        _ = sig (v C) (v (h.inner i)) (v B) := sig_rotate _ _ _
        _ = sig (v (h.inner i)) (v B) (v C) := sig_rotate _ _ _
    · exact hdiag
    · exact h.inner_AB i
  · apply Or.inr
    have hACD : 0 < sig (v A) (v C) (v D) := by
      calc
        0 < sig (v C) (v D) (v A) := h.ccw.2.2.1
        _ = sig (v D) (v A) (v C) := sig_rotate _ _ _
        _ = sig (v A) (v C) (v D) := sig_rotate _ _ _
    have hACi : 0 < sig (v A) (v C) (v (h.inner i)) := by
      rw [sig_swap]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hdiag) hdiagNe)
    apply OrbitIIInternal.inTriStrict_of_fan_pos hACD
    · calc
        0 < sig (v C) (v D) (v (h.inner i)) := h.inner_CD i
        _ = sig (v D) (v (h.inner i)) (v C) := sig_rotate _ _ _
        _ = sig (v (h.inner i)) (v C) (v D) := sig_rotate _ _ _
    · calc
        0 < sig (v D) (v A) (v (h.inner i)) := h.inner_DA i
        _ = sig (v A) (v (h.inner i)) (v D) := sig_rotate _ _ _
    · exact hACi

private theorem HullFourBoundaryGeometry.diagonalBD_ne
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (hmzero : minTri v ≠ 0) (i : Fin 4) :
    sig (v B) (v D) (v (h.inner i)) ≠ 0 := by
  have hlabels : Function.Injective h.labels := by
    simpa [HullFourBoundaryGeometry.labels] using h.labels_injective
  apply sig_ne_zero_of_minTri_ne_zero hmzero
  · have hne := hlabels.ne (show (1 : Fin 8) ≠ 3 by decide)
    change B ≠ D at hne
    exact hne
  · have hne := hlabels.ne (hullSlot_ne_innerSlot 1 i)
    rw [h.labels_hullSlot, h.labels_innerSlot] at hne
    simpa [hullFourLabels] using hne
  · have hne := hlabels.ne (hullSlot_ne_innerSlot 3 i)
    rw [h.labels_hullSlot, h.labels_innerSlot] at hne
    simpa [hullFourLabels] using hne

/-! ## The finite sector theorem -/

/-- Sector `offset` in the chart whose first hull vertex is shifted by `r`. -/
def cyclicSector (r : Fin 4) (offset : Nat) : Fin 4 :=
  ⟨(r.val + offset) % 4, Nat.mod_lt _ (by decide)⟩

/-- A proof-relevant normal form for the four sector assignments. -/
def SectorProducerPattern (a : SectorCensus.Assignment) : Prop :=
  (∃ (r : Fin 4) (e : Equiv.Perm (Fin 4)),
      (a (e 0) = cyclicSector r 1 ∨ a (e 0) = cyclicSector r 2) ∧
      (a (e 1) = cyclicSector r 1 ∨ a (e 1) = cyclicSector r 2) ∧
      (a (e 2) = cyclicSector r 3 ∨ a (e 2) = cyclicSector r 0) ∧
      (a (e 3) = cyclicSector r 3 ∨ a (e 3) = cyclicSector r 0)) ∨
  (∃ r : Fin 4, ∀ i : Fin 4, a i = cyclicSector r 0) ∨
  (∃ (r : Fin 4) (e : Equiv.Perm (Fin 4)),
      a (e 0) = cyclicSector r 1 ∧
      (a (e 1) = cyclicSector r 0 ∨ a (e 1) = cyclicSector r 3) ∧
      (a (e 2) = cyclicSector r 0 ∨ a (e 2) = cyclicSector r 3) ∧
      (a (e 3) = cyclicSector r 0 ∨ a (e 3) = cyclicSector r 3)) ∨
  (∃ (r : Fin 4) (e : Equiv.Perm (Fin 4)),
      a (e 0) = cyclicSector r 2 ∧
      (a (e 1) = cyclicSector r 0 ∨ a (e 1) = cyclicSector r 3) ∧
      (a (e 2) = cyclicSector r 0 ∨ a (e 2) = cyclicSector r 3) ∧
      (a (e 3) = cyclicSector r 0 ∨ a (e 3) = cyclicSector r 3))

private instance (a : SectorCensus.Assignment) :
    Decidable (SectorProducerPattern a) := by
  unfold SectorProducerPattern
  infer_instance

private theorem sectorProducerPattern_vector
    (a0 a1 a2 a3 : Fin 4) :
    SectorProducerPattern ![a0, a1, a2, a3] := by
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;>
    decide

/-- Every four-sector assignment has a normalized producer.  This is the
entire finite census used by the global theorem. -/
theorem sectorProducerPattern_exhaustive (a : SectorCensus.Assignment) :
    SectorProducerPattern a := by
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ha]
  exact sectorProducerPattern_vector _ _ _ _

/-! ## Cyclic charts and producer construction -/

private def hullLabel (A B C D : Fin 8) (i : Fin 4) : Fin 8 :=
  match i.val with
  | 0 => A
  | 1 => B
  | 2 => C
  | _ => D

private def chartHull (A B C D : Fin 8) (r i : Fin 4) : Fin 8 :=
  hullLabel A B C D (cyclicSector r i.val)

private def chartSlot (r : Fin 4) (e : Equiv.Perm (Fin 4))
    (i : Fin 8) : Fin 8 :=
  match i.val with
  | 0 => hullSlot (cyclicSector r 0)
  | 1 => hullSlot (cyclicSector r 1)
  | 2 => hullSlot (cyclicSector r 2)
  | 3 => hullSlot (cyclicSector r 3)
  | 4 => innerSlot (e 0)
  | 5 => innerSlot (e 1)
  | 6 => innerSlot (e 2)
  | _ => innerSlot (e 3)

@[simp] private theorem chartSlot_hull (r : Fin 4)
    (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    chartSlot r e (hullSlot i) = hullSlot (cyclicSector r i.val) := by
  fin_cases i <;> rfl

@[simp] private theorem chartSlot_inner (r : Fin 4)
    (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    chartSlot r e (innerSlot i) = innerSlot (e i) := by
  fin_cases i <;> rfl

private theorem cyclicSector_injective (r : Fin 4) :
    Function.Injective (fun i : Fin 4 => cyclicSector r i.val) := by
  intro i j hij
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp_all [cyclicSector]

private theorem chartSlot_injective (r : Fin 4)
    (e : Equiv.Perm (Fin 4)) : Function.Injective (chartSlot r e) := by
  intro i j hij
  rcases finEight_slotCases i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases finEight_slotCases j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have hcyclic : cyclicSector r a.val = cyclicSector r b.val :=
        hullSlot_injective (by simpa using hij)
      exact congrArg hullSlot (cyclicSector_injective r hcyclic)
    · exfalso
      exact hullSlot_ne_innerSlot (cyclicSector r a.val) (e b)
        (by simpa using hij)
  · rcases finEight_slotCases j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exfalso
      exact hullSlot_ne_innerSlot (cyclicSector r b.val) (e a)
        (by simpa using hij.symm)
    · have heq : e a = e b := innerSlot_injective (by simpa using hij)
      exact congrArg innerSlot (e.injective heq)

private theorem chartLabels_apply
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (r : Fin 4) (e : Equiv.Perm (Fin 4)) (i : Fin 8) :
    quadLabels
        (chartHull A B C D r 0) (chartHull A B C D r 1)
        (chartHull A B C D r 2) (chartHull A B C D r 3)
        (h.inner (e 0)) (h.inner (e 1))
        (h.inner (e 2)) (h.inner (e 3)) i =
      h.labels (chartSlot r e i) := by
  rcases finEight_slotCases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · fin_cases r <;> fin_cases j <;> rfl
  · fin_cases j <;>
      simp only [chartSlot_inner, h.labels_innerSlot] <;> rfl

private theorem chartLabels_injective
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (r : Fin 4) (e : Equiv.Perm (Fin 4)) :
    Function.Injective
      (quadLabels
        (chartHull A B C D r 0) (chartHull A B C D r 1)
        (chartHull A B C D r 2) (chartHull A B C D r 3)
        (h.inner (e 0)) (h.inner (e 1))
        (h.inner (e 2)) (h.inner (e 3))) := by
  intro i j hij
  apply chartSlot_injective r e
  apply h.labels_injective
  calc
    h.labels (chartSlot r e i) =
        quadLabels
          (chartHull A B C D r 0) (chartHull A B C D r 1)
          (chartHull A B C D r 2) (chartHull A B C D r 3)
          (h.inner (e 0)) (h.inner (e 1))
          (h.inner (e 2)) (h.inner (e 3)) i :=
      (chartLabels_apply h r e i).symm
    _ = quadLabels
          (chartHull A B C D r 0) (chartHull A B C D r 1)
          (chartHull A B C D r 2) (chartHull A B C D r 3)
          (h.inner (e 0)) (h.inner (e 1))
          (h.inner (e 2)) (h.inner (e 3)) j := hij
    _ = h.labels (chartSlot r e j) := chartLabels_apply h r e j

private theorem chartCCW
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D) (r : Fin 4) :
    CCWQuad
      (v (chartHull A B C D r 0)) (v (chartHull A B C D r 1))
      (v (chartHull A B C D r 2)) (v (chartHull A B C D r 3)) := by
  fin_cases r
  · simpa [chartHull, hullLabel, cyclicSector] using h.ccw
  · simpa [chartHull, hullLabel, cyclicSector] using
      (show CCWQuad (v B) (v C) (v D) (v A) from
        ⟨h.ccw.2.1, h.ccw.2.2.1, h.ccw.2.2.2, h.ccw.1⟩)
  · simpa [chartHull, hullLabel, cyclicSector] using
      (show CCWQuad (v C) (v D) (v A) (v B) from
        ⟨h.ccw.2.2.1, h.ccw.2.2.2, h.ccw.1, h.ccw.2.1⟩)
  · simpa [chartHull, hullLabel, cyclicSector] using
      (show CCWQuad (v D) (v A) (v B) (v C) from
        ⟨h.ccw.2.2.2, h.ccw.1, h.ccw.2.1, h.ccw.2.2.1⟩)

private theorem sectorInChart
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (assignment : StrictQuadSectorAssignment
      (fun i => v (h.inner i)) (v A) (v B) (v C) (v D))
    (r : Fin 4) (e : Equiv.Perm (Fin 4)) (i s : Fin 4)
    (heq : assignment.assignment (e i) = cyclicSector r s.val) :
    StrictQuadSector (v (h.inner (e i)))
      (v (chartHull A B C D r 0)) (v (chartHull A B C D r 1))
      (v (chartHull A B C D r 2)) (v (chartHull A B C D r 3)) s := by
  have hsector := assignment.realizes (e i)
  rw [heq] at hsector
  fin_cases r <;> fin_cases s <;>
    simp only [StrictQuadSector, chartHull, hullLabel, cyclicSector] at hsector ⊢ <;>
    aesop (add safe forward inTriStrict_rotate)

private theorem leftFive_injective
    {A B C D P Q R S : Fin 8}
    (h : Function.Injective (quadLabels A B C D P Q R S)) :
    Function.Injective ![B, C, D, P, Q] := by
  let slots : Fin 5 → Fin 8 := ![1, 2, 3, 4, 5]
  have hslots : Function.Injective slots := by decide
  have heq : ![B, C, D, P, Q] =
      quadLabels A B C D P Q R S ∘ slots := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h.comp hslots

private theorem rightFive_injective
    {A B C D P Q R S : Fin 8}
    (h : Function.Injective (quadLabels A B C D P Q R S)) :
    Function.Injective ![B, D, A, R, S] := by
  let slots : Fin 5 → Fin 8 := ![1, 3, 0, 6, 7]
  have hslots : Function.Injective slots := by decide
  have heq : ![B, D, A, R, S] =
      quadLabels A B C D P Q R S ∘ slots := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h.comp hslots

private theorem mirrorReverseLabels_injective
    {A B C D Q P R S : Fin 8}
    (h : Function.Injective (quadLabels A B C D Q P R S)) :
    Function.Injective (quadLabels A D C B Q P R S) := by
  let slots : Fin 8 → Fin 8 := ![0, 3, 2, 1, 4, 5, 6, 7]
  have hslots : Function.Injective slots := by decide
  have heq : quadLabels A D C B Q P R S =
      quadLabels A B C D Q P R S ∘ slots := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h.comp hslots

private theorem closureFromChart
    {v : Fin 8 → Point} {A B C D : Fin 8} (r : Fin 4)
    (certificate : HullFourClosureCertificate v
      (chartHull A B C D r 0) (chartHull A B C D r 1)
      (chartHull A B C D r 2) (chartHull A B C D r 3)) :
    HullFourClosureCertificate v A B C D := by
  fin_cases r
  · simpa [chartHull, hullLabel, cyclicSector] using certificate
  · apply HullFourClosureCertificate.rotateBack
    simpa [chartHull, hullLabel, cyclicSector] using certificate
  · apply HullFourClosureCertificate.rotateTwoBack
    simpa [chartHull, hullLabel, cyclicSector] using certificate
  · apply HullFourClosureCertificate.rotateThreeBack
    simpa [chartHull, hullLabel, cyclicSector] using certificate

private theorem closeBalanced
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (a : StrictQuadSectorAssignment
      (fun i => v (h.inner i)) (v A) (v B) (v C) (v D))
    (r : Fin 4) (e : Equiv.Perm (Fin 4))
    (h0 : a.assignment (e 0) = cyclicSector r 1 ∨
      a.assignment (e 0) = cyclicSector r 2)
    (h1 : a.assignment (e 1) = cyclicSector r 1 ∨
      a.assignment (e 1) = cyclicSector r 2)
    (h2 : a.assignment (e 2) = cyclicSector r 3 ∨
      a.assignment (e 2) = cyclicSector r 0)
    (h3 : a.assignment (e 3) = cyclicSector r 3 ∨
      a.assignment (e 3) = cyclicSector r 0) :
    HullFourClosureCertificate v A B C D := by
  let A' := chartHull A B C D r 0
  let B' := chartHull A B C D r 1
  let C' := chartHull A B C D r 2
  let D' := chartHull A B C D r 3
  have inBCD (i : Fin 4)
      (hi : a.assignment (e i) = cyclicSector r 1 ∨
        a.assignment (e i) = cyclicSector r 2) :
      TriHull.InTriStrict (v (h.inner (e i))) (v B') (v C') (v D') := by
    rcases hi with hi | hi
    · exact (sectorInChart h a r e i 1 hi).2
    · exact (sectorInChart h a r e i 2 hi).1
  have inDAB (i : Fin 4)
      (hi : a.assignment (e i) = cyclicSector r 3 ∨
        a.assignment (e i) = cyclicSector r 0) :
      TriHull.InTriStrict (v (h.inner (e i))) (v D') (v A') (v B') := by
    rcases hi with hi | hi
    · exact (sectorInChart h a r e i 3 hi).2
    · exact (sectorInChart h a r e i 0 hi).2
  have hall := chartLabels_injective h r e
  let cert : BalancedDiagonalCertificate v A' B' C' D' :=
    { P := h.inner (e 0)
      Q := h.inner (e 1)
      R := h.inner (e 2)
      S := h.inner (e 3)
      left_injective := leftFive_injective hall
      right_injective := rightFive_injective hall
      BCD_pos := (chartCCW h r).2.1
      P_in_BCD := inBCD 0 h0
      Q_in_BCD := inBCD 1 h1
      BDA_pos := by
        calc
          0 < sig (v D') (v A') (v B') := (chartCCW h r).2.2.2
          _ = sig (v A') (v B') (v D') := sig_rotate _ _ _
          _ = sig (v B') (v D') (v A') := sig_rotate _ _ _
      R_in_BDA := inTriStrict_rotateTwo (inDAB 2 h2)
      S_in_BDA := inTriStrict_rotateTwo (inDAB 3 h3) }
  apply closureFromChart r
  exact .orbit cert.orbitCertificate

private theorem closeCoarseI
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (a : StrictQuadSectorAssignment
      (fun i => v (h.inner i)) (v A) (v B) (v C) (v D))
    (hm : 0 < minTri v) (r : Fin 4)
    (hallSector : ∀ i : Fin 4, a.assignment i = cyclicSector r 0) :
    HullFourClosureCertificate v A B C D := by
  let e : Equiv.Perm (Fin 4) := Equiv.refl _
  let A' := chartHull A B C D r 0
  let B' := chartHull A B C D r 1
  let C' := chartHull A B C D r 2
  let D' := chartHull A B C D r 3
  have hs (i : Fin 4) : StrictQuadSector (v (h.inner i))
      (v A') (v B') (v C') (v D') 0 := by
    simpa [e] using sectorInChart h a r e i 0 (by simpa [e] using hallSector i)
  let cert : OrbitICoarseGeometryCertificate v A' B' C' D' :=
    { P := h.inner 0
      Q := h.inner 1
      R := h.inner 2
      S := h.inner 3
      labels_injective := by simpa [e] using chartLabels_injective h r e
      ccw := chartCCW h r
      P_in_ABC := (hs 0).1
      Q_in_ABC := (hs 1).1
      R_in_ABC := (hs 2).1
      S_in_ABC := (hs 3).1
      P_in_DAB := (hs 0).2
      Q_in_DAB := (hs 1).2
      R_in_DAB := (hs 2).2
      S_in_DAB := (hs 3).2 }
  apply closureFromChart r
  exact (cert.classifyPositive hm).toClosure

private theorem closeOrbitII
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (a : StrictQuadSectorAssignment
      (fun i => v (h.inner i)) (v A) (v B) (v C) (v D))
    (r : Fin 4) (e : Equiv.Perm (Fin 4))
    (hQ : a.assignment (e 0) = cyclicSector r 1)
    (hP : a.assignment (e 1) = cyclicSector r 0 ∨
      a.assignment (e 1) = cyclicSector r 3)
    (hR : a.assignment (e 2) = cyclicSector r 0 ∨
      a.assignment (e 2) = cyclicSector r 3)
    (hS : a.assignment (e 3) = cyclicSector r 0 ∨
      a.assignment (e 3) = cyclicSector r 3) :
    HullFourClosureCertificate v A B C D := by
  let A' := chartHull A B C D r 0
  let B' := chartHull A B C D r 1
  let C' := chartHull A B C D r 2
  let D' := chartHull A B C D r 3
  have hQsector := sectorInChart h a r e 0 1 hQ
  have inABD (i : Fin 4)
      (hi : a.assignment (e i) = cyclicSector r 0 ∨
        a.assignment (e i) = cyclicSector r 3) :
      TriHull.InTriStrict (v (h.inner (e i))) (v A') (v B') (v D') := by
    rcases hi with hi | hi
    · exact inTriStrict_rotate (sectorInChart h a r e i 0 hi).2
    · exact inTriStrict_rotate (sectorInChart h a r e i 3 hi).2
  let cert : OrbitIIGeometryCertificate v A' B' C' D' :=
    { Q := h.inner (e 0)
      P := h.inner (e 1)
      R := h.inner (e 2)
      S := h.inner (e 3)
      labels_injective := chartLabels_injective h r e
      ccw := chartCCW h r
      Q_in_ABC := hQsector.1
      Q_in_BCD := hQsector.2
      P_in_ABD := inABD 1 hP
      R_in_ABD := inABD 2 hR
      S_in_ABD := inABD 3 hS }
  apply closureFromChart r
  exact .orbit cert.orbitCertificate

private theorem closeMirrorOrbitII
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D)
    (a : StrictQuadSectorAssignment
      (fun i => v (h.inner i)) (v A) (v B) (v C) (v D))
    (r : Fin 4) (e : Equiv.Perm (Fin 4))
    (hQ : a.assignment (e 0) = cyclicSector r 2)
    (hP : a.assignment (e 1) = cyclicSector r 0 ∨
      a.assignment (e 1) = cyclicSector r 3)
    (hR : a.assignment (e 2) = cyclicSector r 0 ∨
      a.assignment (e 2) = cyclicSector r 3)
    (hS : a.assignment (e 3) = cyclicSector r 0 ∨
      a.assignment (e 3) = cyclicSector r 3) :
    HullFourClosureCertificate v A B C D := by
  let A' := chartHull A B C D r 0
  let B' := chartHull A B C D r 1
  let C' := chartHull A B C D r 2
  let D' := chartHull A B C D r 3
  have hQsector := sectorInChart h a r e 0 2 hQ
  have inABD (i : Fin 4)
      (hi : a.assignment (e i) = cyclicSector r 0 ∨
        a.assignment (e i) = cyclicSector r 3) :
      TriHull.InTriStrict (v (h.inner (e i))) (v A') (v B') (v D') := by
    rcases hi with hi | hi
    · exact inTriStrict_rotate (sectorInChart h a r e i 0 hi).2
    · exact inTriStrict_rotate (sectorInChart h a r e i 3 hi).2
  have hall := chartLabels_injective h r e
  let cert : OrbitIIGeometryCertificate
      (mirrorConfiguration v) A' D' C' B' :=
    { Q := h.inner (e 0)
      P := h.inner (e 1)
      R := h.inner (e 2)
      S := h.inner (e 3)
      labels_injective := mirrorReverseLabels_injective hall
      ccw := ccwQuad_mirrorReverse (chartCCW h r)
      Q_in_ABC := by
        simpa [mirrorConfiguration] using
          inTriStrict_swap (inTriStrict_mirrorPoint hQsector.2)
      Q_in_BCD := by
        simpa [mirrorConfiguration] using
          inTriStrict_rotate
            (inTriStrict_swap (inTriStrict_mirrorPoint hQsector.1))
      P_in_ABD := by
        simpa [mirrorConfiguration] using
          inTriStrict_swap (inTriStrict_mirrorPoint (inABD 1 hP))
      R_in_ABD := by
        simpa [mirrorConfiguration] using
          inTriStrict_swap (inTriStrict_mirrorPoint (inABD 2 hR))
      S_in_ABD := by
        simpa [mirrorConfiguration] using
          inTriStrict_swap (inTriStrict_mirrorPoint (inABD 3 hS)) }
  apply closureFromChart r
  exact (HullFourClosureCertificate.orbit cert.orbitCertificate).mirrorReverseBack

/-- Global theorem-level dispatcher.  The zero-minimum branch is immediate;
otherwise the two diagonals put every interior label in one of four strict
sectors and the finite pattern theorem selects a green producer. -/
theorem HullFourBoundaryGeometry.globalClosure
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : HullFourBoundaryGeometry v A B C D) :
    HullFourClosureCertificate v A B C D := by
  by_cases hmzero : minTri v = 0
  · exact .orbit (Or.inl hmzero)
  · have hm : 0 < minTri v :=
      lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hmzero)
    let assignment := Classical.choice
      (strictQuadSectorAssignment_exists h.ccw
        (h.insideFan hmzero) (h.diagonalBD_ne hmzero))
    rcases sectorProducerPattern_exhaustive assignment.assignment with
      hbalanced | hcoarse | horbitII | hmirror
    · rcases hbalanced with ⟨r, e, h0, h1, h2, h3⟩
      exact closeBalanced h assignment r e h0 h1 h2 h3
    · rcases hcoarse with ⟨r, hall⟩
      exact closeCoarseI h assignment hm r hall
    · rcases horbitII with ⟨r, e, hQ, hP, hR, hS⟩
      exact closeOrbitII h assignment r e hQ hP hR hS
    · rcases hmirror with ⟨r, e, hQ, hP, hR, hS⟩
      exact closeMirrorOrbitII h assignment r e hQ hP hR hS

end Heilbronn8.QuadHull
