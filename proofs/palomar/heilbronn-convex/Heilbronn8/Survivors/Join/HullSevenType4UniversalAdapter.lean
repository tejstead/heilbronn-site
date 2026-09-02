import Heilbronn8.HullSevenCutoffExclusionCore
import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.TriHull.HullSevenType4PointAdapter

/-! # Universal hull-seven type 4 point adapter -/

namespace Heilbronn8

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

noncomputable section

/-- A cutoff presentation is preferred for type 4 when its only negative
increasing pairs are `05`, `06`, `16`, and `26`. -/
def HullSevenCutoffType4Preferred
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) : Prop :=
  ∀ i j : Fin 7, i < j →
    hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val =
      decide ((i, j) ≠ ((0 : Fin 7), (5 : Fin 7)) ∧
        (i, j) ≠ ((0 : Fin 7), (6 : Fin 7)) ∧
        (i, j) ≠ ((1 : Fin 7), (6 : Fin 7)) ∧
        (i, j) ≠ ((2 : Fin 7), (6 : Fin 7)))

private def hullSevenCutoffType4PreferredDecidable
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) :
    Decidable (HullSevenCutoffType4Preferred cuts rotation) := by
  unfold HullSevenCutoffType4Preferred
  apply hullSevenDecidableForallTwo
  intro i j
  infer_instance

/-- Every reduced type-4 cutoff has an orientation-preserving rotation with
the preferred four-negative-chord presentation. -/
theorem hullSevenCutoffDecode_type4_preferred :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type4.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType4Preferred
            (hullSevenCutoffDecode low one) rotation := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type4.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType4Preferred
            (hullSevenCutoffDecode low one) rotation) := by
    letI : DecidablePred (fun rotation : Fin 7 =>
        HullSevenCutoffType4Preferred
          (hullSevenCutoffDecode low one) rotation) :=
      fun rotation => hullSevenCutoffType4PreferredDecidable _ rotation
    letI : Decidable (∃ rotation : Fin 7,
        HullSevenCutoffType4Preferred
          (hullSevenCutoffDecode low one) rotation) :=
      Fintype.decidableExistsFintype
    infer_instance
  letI := hullSevenCutoffReducedForallDecidable
    (fun low one =>
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type4.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType4Preferred
            (hullSevenCutoffDecode low one) rotation)
    outcomeDec
  decide

/-- Every complementary type-4 cutoff admits the preferred direct rotation. -/
theorem hullSevenCutoff_type4_preferred_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts)
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type4.key) :
    ∃ rotation : Fin 7, HullSevenCutoffType4Preferred cuts rotation := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hkeyDecode :
      hullSevenCutoffOrderType
          (hullSevenCutoffDecode
            (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)) =
        HullSevenType.type4.key := by
    rw [← hdecode]
    exact hkey
  have hpreferred := hullSevenCutoffDecode_type4_preferred
    (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
    hindependent heligible hkeyDecode
  rw [← hdecode] at hpreferred
  exact hpreferred

private theorem hullSevenType4Shift_injective (rotation : Fin 7) :
    Function.Injective (hullSevenShift rotation) := by
  intro i j hij
  exact add_left_cancel hij

private theorem type4_cutoffDirectedPositive_shifted_eq_decide
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

private theorem type4_shifted_chord_ne
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

private theorem type4_fanSum_hullSevenShift
    (v : Configuration) (cycle : Fin 7 → Fin 8)
    (rotation : Fin 7) :
    fanSum v (fun i => cycle (hullSevenShift rotation i)) =
      fanSum v cycle := by
  rw [fanSum_seven_eq_boundary v
      (fun i => cycle (hullSevenShift rotation i)) (0, 0),
    fanSum_seven_eq_boundary v cycle (0, 0)]
  fin_cases rotation <;> simp [hullSevenShift] <;> ring

private theorem type4_shifted_sign_pos
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
  have hsignBit := type4_cutoffDirectedPositive_shifted_eq_decide
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

private theorem type4_shifted_sign_neg
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
  have hsignBit := type4_cutoffDirectedPositive_shifted_eq_decide
    X cuts hcuts rotation i j hij
  have hnpos :
      ¬ 0 < sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point := by
    apply of_decide_eq_false
    rw [← hsignBit, hbit]
  have hne := type4_shifted_chord_ne X rotation i j hij
  have hraw :
      sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnpos) hne
  simpa only [
    sig_rotate (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) point,
    sig_rotate (cycle (hullSevenShift rotation j)) point
      (cycle (hullSevenShift rotation i))] using hraw

/-- Transport the preferred cutoff presentation to the exact type-4 point
packet consumed by the determinant adapter. -/
noncomputable def StrictHullSevenInterior.toType4PointData
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
    (hpreferred : HullSevenCutoffType4Preferred cuts rotation) :
    TriHull.HullSevenType4PointData v := by
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
      negative16 := ?_
      negative26 := ?_
      hull_area_eq := harea.trans
        (type4_fanSum_hullSevenShift v cycleLabels rotation).symm }
  · intro i j hij
    exact (hullSevenType4Shift_injective rotation) (hcycleInjective hij)
  · rintro ⟨i, hi⟩
    exact hpointOutside ⟨hullSevenShift rotation i, hi⟩
  · constructor
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).le
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).ne'
  · intro i j hpositive
    apply type4_shifted_sign_pos X cuts hcuts rotation i j hpositive.1
    rw [hpreferred i j hpositive.1]
    apply decide_eq_true
    exact ⟨hpositive.2.1, hpositive.2.2.1,
      hpositive.2.2.2.1, hpositive.2.2.2.2⟩
  · apply type4_shifted_sign_neg X cuts hcuts rotation 0 5 (by decide)
    rw [hpreferred 0 5 (by decide)]
    decide
  · apply type4_shifted_sign_neg X cuts hcuts rotation 0 6 (by decide)
    rw [hpreferred 0 6 (by decide)]
    decide
  · apply type4_shifted_sign_neg X cuts hcuts rotation 1 6 (by decide)
    rw [hpreferred 1 6 (by decide)]
    decide
  · apply type4_shifted_sign_neg X cuts hcuts rotation 2 6 (by decide)
    rw [hpreferred 2 6 (by decide)]
    decide

/-- Universal cutoff exclusion for hull-seven type 4. -/
theorem hullSevenCutoffType4Exclusion :
    HullSevenCutoffTypeExclusion .type4 := by
  intro v cycleLabels pointLabel X hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  obtain ⟨rotation, hpreferred⟩ :=
    hullSevenCutoff_type4_preferred_of_complementary cuts hcomp hkey
  exact (X.toType4PointData hcycleInjective hpointOutside hmin harea
    cuts hcuts rotation hpreferred).not_beats hbeat

end

end Heilbronn8
