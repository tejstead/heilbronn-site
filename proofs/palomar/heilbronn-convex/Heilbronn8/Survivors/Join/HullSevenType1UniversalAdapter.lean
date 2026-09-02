import Heilbronn8.Survivors.Join.HullSevenGeometricCutoff
import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.TriHull.HullSevenType1PointAdapter
import Heilbronn8.TriHull.HullSevenType1MirrorPointAdapter

/-!
# Universal hull-seven type 1 point adapter

Type 1 is the unique chiral retained seven-wheel.  Keeping the source hull
orientation fixed, every labelled type-1 cutoff has one of two
orientation-preserving rotations:

* the direct chart, whose negative increasing brackets are `06,16`;
* the mirror chart, whose negative increasing brackets are `05,06`.

This module proves that finite dichotomy on the reduced two-mask cutoff
domain and transports each branch to its honest actual-point packet.  No
reflection is applied to the hull cycle, so strict CCW cyclicity and the fan
area identity are preserved literally.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

noncomputable section

/-- Preferred orientation-preserving direct chart for type 1. -/
def HullSevenCutoffType1DirectPreferred
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) : Prop :=
  ∀ i j : Fin 7, i < j →
    hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val =
      decide ((i, j) ≠ ((0 : Fin 7), (6 : Fin 7)) ∧
        (i, j) ≠ ((1 : Fin 7), (6 : Fin 7)))

/-- Preferred orientation-preserving mirror chart for type 1. -/
def HullSevenCutoffType1MirrorPreferred
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) : Prop :=
  ∀ i j : Fin 7, i < j →
    hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val =
      decide ((i, j) ≠ ((0 : Fin 7), (5 : Fin 7)) ∧
        (i, j) ≠ ((0 : Fin 7), (6 : Fin 7)))

private def hullSevenCutoffType1DirectPreferredDecidable
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) :
    Decidable (HullSevenCutoffType1DirectPreferred cuts rotation) := by
  unfold HullSevenCutoffType1DirectPreferred
  apply hullSevenDecidableForallTwo
  intro i j
  infer_instance

private def hullSevenCutoffType1MirrorPreferredDecidable
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) :
    Decidable (HullSevenCutoffType1MirrorPreferred cuts rotation) := by
  unfold HullSevenCutoffType1MirrorPreferred
  apply hullSevenDecidableForallTwo
  intro i j
  infer_instance

/-- The reduced cutoff representation exposes one of the two chiral charts
without reversing the source cycle. -/
theorem hullSevenCutoffDecode_type1_direct_or_mirror :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type1.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType1DirectPreferred
              (hullSevenCutoffDecode low one) rotation ∨
            HullSevenCutoffType1MirrorPreferred
              (hullSevenCutoffDecode low one) rotation := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type1.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType1DirectPreferred
              (hullSevenCutoffDecode low one) rotation ∨
            HullSevenCutoffType1MirrorPreferred
              (hullSevenCutoffDecode low one) rotation) := by
    letI : DecidablePred (fun rotation : Fin 7 =>
        HullSevenCutoffType1DirectPreferred
            (hullSevenCutoffDecode low one) rotation ∨
          HullSevenCutoffType1MirrorPreferred
            (hullSevenCutoffDecode low one) rotation) := fun rotation => by
      letI : Decidable (HullSevenCutoffType1DirectPreferred
          (hullSevenCutoffDecode low one) rotation) :=
        hullSevenCutoffType1DirectPreferredDecidable _ rotation
      letI : Decidable (HullSevenCutoffType1MirrorPreferred
          (hullSevenCutoffDecode low one) rotation) :=
        hullSevenCutoffType1MirrorPreferredDecidable _ rotation
      infer_instance
    letI : Decidable (∃ rotation : Fin 7,
        HullSevenCutoffType1DirectPreferred
            (hullSevenCutoffDecode low one) rotation ∨
          HullSevenCutoffType1MirrorPreferred
            (hullSevenCutoffDecode low one) rotation) :=
      Fintype.decidableExistsFintype
    infer_instance
  letI := hullSevenCutoffReducedForallDecidable
    (fun low one =>
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type1.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType1DirectPreferred
              (hullSevenCutoffDecode low one) rotation ∨
            HullSevenCutoffType1MirrorPreferred
              (hullSevenCutoffDecode low one) rotation)
    outcomeDec
  decide

/-- Every complementary type-1 cutoff has a direct or mirror
orientation-preserving preferred rotation. -/
theorem hullSevenCutoff_type1_direct_or_mirror_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts)
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type1.key) :
    ∃ rotation : Fin 7,
      HullSevenCutoffType1DirectPreferred cuts rotation ∨
        HullSevenCutoffType1MirrorPreferred cuts rotation := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hkeyDecode :
      hullSevenCutoffOrderType
          (hullSevenCutoffDecode
            (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)) =
        HullSevenType.type1.key := by
    rw [← hdecode]
    exact hkey
  have hpreferred := hullSevenCutoffDecode_type1_direct_or_mirror
    (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
    hindependent heligible hkeyDecode
  rw [← hdecode] at hpreferred
  exact hpreferred

private theorem hullSevenType1Shift_injective (rotation : Fin 7) :
    Function.Injective (hullSevenShift rotation) := by
  intro i j hij
  exact add_left_cancel hij

private theorem type1_cutoffDirectedPositive_shifted_eq_decide
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (rotation i j : Fin 7) (hij : i < j) :
    hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val =
      decide (0 < sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point) := by
  let offset : Fin 6 :=
    ⟨j.val - i.val - 1, by omega⟩
  have hforward := cutoffDirectedPositive_forward X cuts hcuts
    (hullSevenShift rotation i) offset
  have hcutoff :
      hullSevenCutoffDirectedPositive cuts
          (hullSevenShift rotation i).val
          (hullSevenShift rotation j).val =
        hullSevenCutoffDirectedPositive cuts
          (hullSevenShift rotation i).val
          ((hullSevenShift rotation i).val + offset.val + 1) := by
    fin_cases rotation <;> fin_cases i <;> fin_cases j <;>
      norm_num at hij <;>
      simp [offset, hullSevenShift,
        hullSevenCutoffDirectedPositive, hullSevenForwardDistance,
        hullSevenCutoffAt]
  have hrow :
      X.row (hullSevenShift rotation i) offset =
        sig (cycle (hullSevenShift rotation i))
          (cycle (hullSevenShift rotation j)) point := by
    fin_cases rotation <;> fin_cases i <;> fin_cases j <;>
      norm_num at hij <;>
      simp [offset, StrictHullSevenInterior.row, hullSevenShift,
        hullSevenRowOffset]
  rw [hcutoff, hforward]
  by_cases hpos : 0 < X.row (hullSevenShift rotation i) offset
  · have hpos' :
        0 < sig (cycle (hullSevenShift rotation i))
          (cycle (hullSevenShift rotation j)) point := by
      rw [← hrow]
      exact hpos
    simp [hpos, hpos']
  · have hpos' :
        ¬ 0 < sig (cycle (hullSevenShift rotation i))
          (cycle (hullSevenShift rotation j)) point := by
      intro h
      apply hpos
      rwa [hrow]
    simp [hpos, hpos']

private theorem type1_shifted_chord_ne
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point)
    (rotation i j : Fin 7) (hij : i < j) :
    sig (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) point ≠ 0 := by
  let offset : Fin 6 :=
    ⟨j.val - i.val - 1, by omega⟩
  have hne := X.chord_ne (hullSevenShift rotation i) offset
  fin_cases rotation <;> fin_cases i <;> fin_cases j <;>
    norm_num at hij <;>
    simp_all [offset, hullSevenShift, hullSevenRowOffset]

/-- The polygon fan is unchanged by an orientation-preserving cyclic shift. -/
private theorem type1_fanSum_hullSevenShift
    (v : Configuration) (cycle : Fin 7 → Fin 8)
    (rotation : Fin 7) :
    fanSum v (fun i => cycle (hullSevenShift rotation i)) =
      fanSum v cycle := by
  rw [fanSum_seven_eq_boundary v
      (fun i => cycle (hullSevenShift rotation i)) (0, 0),
    fanSum_seven_eq_boundary v cycle (0, 0)]
  fin_cases rotation <;> simp [hullSevenShift] <;> ring

private theorem type1_shifted_sign_pos
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (rotation i j : Fin 7) (hij : i < j)
    (hbit : hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val = true) :
    0 < sig point (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) := by
  have hsignBit := type1_cutoffDirectedPositive_shifted_eq_decide
    X cuts hcuts rotation i j hij
  have hraw :
      0 < sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point := by
    apply of_decide_eq_true
    rw [← hsignBit, hbit]
  simpa only [
    sig_rotate (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) point,
    sig_rotate (cycle (hullSevenShift rotation j)) point
      (cycle (hullSevenShift rotation i))] using hraw

private theorem type1_shifted_sign_neg
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (rotation i j : Fin 7) (hij : i < j)
    (hbit : hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val = false) :
    sig point (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) < 0 := by
  have hsignBit := type1_cutoffDirectedPositive_shifted_eq_decide
    X cuts hcuts rotation i j hij
  have hnpos :
      ¬ 0 < sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point := by
    apply of_decide_eq_false
    rw [← hsignBit, hbit]
  have hne := type1_shifted_chord_ne X rotation i j hij
  have hraw :
      sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnpos) hne
  simpa only [
    sig_rotate (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) point,
    sig_rotate (cycle (hullSevenShift rotation j)) point
      (cycle (hullSevenShift rotation i))] using hraw

/-- Transport the direct preferred chart to the direct type-1 point packet. -/
noncomputable def StrictHullSevenInterior.toType1PointData
    {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8}
    (X : StrictHullSevenInterior
      (fun i => v (cycleLabels i)) (v pointLabel))
    (hcycleInjective : Function.Injective cycleLabels)
    (hpointOutside : pointLabel ∉ Set.range cycleLabels)
    (hmin : 0 < minTri v)
    (harea : doubledHullArea v = fanSum v cycleLabels)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (rotation : Fin 7)
    (hpreferred : HullSevenCutoffType1DirectPreferred cuts rotation) :
    TriHull.HullSevenType1PointData v := by
  refine
    { cycle := fun i => cycleLabels (hullSevenShift rotation i)
      point := pointLabel
      cycle_injective := ?_
      point_outside := ?_
      minTri_pos := hmin
      cycle_strict := ?_
      positive := ?_
      negative06 := ?_
      negative16 := ?_
      hull_area_eq := harea.trans
        (type1_fanSum_hullSevenShift v cycleLabels rotation).symm }
  · intro i j hij
    exact (hullSevenType1Shift_injective rotation) (hcycleInjective hij)
  · rintro ⟨i, hi⟩
    exact hpointOutside ⟨hullSevenShift rotation i, hi⟩
  · constructor
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).le
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).ne'
  · intro i j hpositive
    apply type1_shifted_sign_pos X cuts hcuts rotation i j hpositive.1
    rw [hpreferred i j hpositive.1]
    simp [hpositive.2.1, hpositive.2.2]
  · apply type1_shifted_sign_neg X cuts hcuts rotation 0 6 (by decide)
    rw [hpreferred 0 6 (by decide)]
    decide
  · apply type1_shifted_sign_neg X cuts hcuts rotation 1 6 (by decide)
    rw [hpreferred 1 6 (by decide)]
    decide

/-- Transport the mirror preferred chart to the mirror type-1 point packet. -/
noncomputable def StrictHullSevenInterior.toType1MirrorPointData
    {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8}
    (X : StrictHullSevenInterior
      (fun i => v (cycleLabels i)) (v pointLabel))
    (hcycleInjective : Function.Injective cycleLabels)
    (hpointOutside : pointLabel ∉ Set.range cycleLabels)
    (hmin : 0 < minTri v)
    (harea : doubledHullArea v = fanSum v cycleLabels)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (rotation : Fin 7)
    (hpreferred : HullSevenCutoffType1MirrorPreferred cuts rotation) :
    TriHull.HullSevenType1MirrorPointData v := by
  refine
    { cycle := fun i => cycleLabels (hullSevenShift rotation i)
      point := pointLabel
      cycle_injective := ?_
      point_outside := ?_
      minTri_pos := hmin
      cycle_strict := ?_
      positive := ?_
      negative05 := ?_
      negative06 := ?_
      hull_area_eq := harea.trans
        (type1_fanSum_hullSevenShift v cycleLabels rotation).symm }
  · intro i j hij
    exact (hullSevenType1Shift_injective rotation) (hcycleInjective hij)
  · rintro ⟨i, hi⟩
    exact hpointOutside ⟨hullSevenShift rotation i, hi⟩
  · constructor
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).le
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).ne'
  · intro i j hpositive
    apply type1_shifted_sign_pos X cuts hcuts rotation i j hpositive.1
    rw [hpreferred i j hpositive.1]
    simp [hpositive.2.1, hpositive.2.2]
  · apply type1_shifted_sign_neg X cuts hcuts rotation 0 5 (by decide)
    rw [hpreferred 0 5 (by decide)]
    decide
  · apply type1_shifted_sign_neg X cuts hcuts rotation 0 6 (by decide)
    rw [hpreferred 0 6 (by decide)]
    decide

/-- The complete type-1 cutoff branch produces one of its two honest point
packets, both already closed by the same scalar theorem. -/
theorem StrictHullSevenInterior.existsType1DirectOrMirrorPointData
    {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8}
    (X : StrictHullSevenInterior
      (fun i => v (cycleLabels i)) (v pointLabel))
    (hcycleInjective : Function.Injective cycleLabels)
    (hpointOutside : pointLabel ∉ Set.range cycleLabels)
    (hmin : 0 < minTri v)
    (harea : doubledHullArea v = fanSum v cycleLabels)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type1.key) :
    Nonempty (TriHull.HullSevenType1PointData v) ∨
      Nonempty (TriHull.HullSevenType1MirrorPointData v) := by
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  obtain ⟨rotation, hdirect | hmirror⟩ :=
    hullSevenCutoff_type1_direct_or_mirror_of_complementary cuts hcomp hkey
  · exact Or.inl ⟨X.toType1PointData hcycleInjective hpointOutside hmin
      harea cuts hcuts rotation hdirect⟩
  · exact Or.inr ⟨X.toType1MirrorPointData hcycleInjective hpointOutside
      hmin harea cuts hcuts rotation hmirror⟩

/-- A universal type-1 cutoff packet contradicts `Beats`, independently of
which chiral orientation occurs. -/
theorem StrictHullSevenInterior.not_beats_of_type1_cutoff
    {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8}
    (X : StrictHullSevenInterior
      (fun i => v (cycleLabels i)) (v pointLabel))
    (hcycleInjective : Function.Injective cycleLabels)
    (hpointOutside : pointLabel ∉ Set.range cycleLabels)
    (hmin : 0 < minTri v)
    (harea : doubledHullArea v = fanSum v cycleLabels)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type1.key)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  rcases X.existsType1DirectOrMirrorPointData hcycleInjective hpointOutside
      hmin harea cuts hcuts hkey with hdirect | hmirror
  · rcases hdirect with ⟨direct⟩
    exact direct.not_beats hbeat
  · rcases hmirror with ⟨mirror⟩
    exact mirror.not_beats hbeat

end

end Heilbronn8
