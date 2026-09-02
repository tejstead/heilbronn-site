import Heilbronn8.HullSevenCutoffExclusionCore
import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.TriHull.HullSevenC24PointAdapter

/-! # Universal hull-seven type 5 / C24 point adapter -/

namespace Heilbronn8

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

noncomputable section

/-- The eight non-boundary signs consumed by the C24 point adapter. -/
def HullSevenCutoffType5Preferred
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) : Prop :=
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 1).val (hullSevenShift rotation 3).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 2).val (hullSevenShift rotation 4).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 3).val (hullSevenShift rotation 5).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 1).val (hullSevenShift rotation 4).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 2).val (hullSevenShift rotation 5).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 0).val (hullSevenShift rotation 4).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 2).val (hullSevenShift rotation 6).val = true ∧
  hullSevenCutoffDirectedPositive cuts
      (hullSevenShift rotation 1).val (hullSevenShift rotation 5).val = false

private def hullSevenCutoffType5PreferredDecidable
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) :
    Decidable (HullSevenCutoffType5Preferred cuts rotation) := by
  unfold HullSevenCutoffType5Preferred
  infer_instance

theorem hullSevenCutoffDecode_type5_preferred :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type5.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType5Preferred
            (hullSevenCutoffDecode low one) rotation := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type5.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType5Preferred
            (hullSevenCutoffDecode low one) rotation) := by
    letI : DecidablePred (fun rotation : Fin 7 =>
        HullSevenCutoffType5Preferred
          (hullSevenCutoffDecode low one) rotation) :=
      fun rotation => hullSevenCutoffType5PreferredDecidable _ rotation
    letI : Decidable (∃ rotation : Fin 7,
        HullSevenCutoffType5Preferred
          (hullSevenCutoffDecode low one) rotation) :=
      Fintype.decidableExistsFintype
    infer_instance
  letI := hullSevenCutoffReducedForallDecidable
    (fun low one =>
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type5.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType5Preferred
            (hullSevenCutoffDecode low one) rotation)
    outcomeDec
  decide

theorem hullSevenCutoff_type5_preferred_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts)
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type5.key) :
    ∃ rotation : Fin 7, HullSevenCutoffType5Preferred cuts rotation := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hkeyDecode :
      hullSevenCutoffOrderType
          (hullSevenCutoffDecode
            (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)) =
        HullSevenType.type5.key := by
    rw [← hdecode]
    exact hkey
  have hpreferred := hullSevenCutoffDecode_type5_preferred
    (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
    hindependent heligible hkeyDecode
  rw [← hdecode] at hpreferred
  exact hpreferred

private theorem hullSevenType5Shift_injective (rotation : Fin 7) :
    Function.Injective (hullSevenShift rotation) := by
  intro i j hij
  exact add_left_cancel hij

private theorem hullSevenType5Shift_succ (rotation i : Fin 7) :
    hullSevenShift (hullSevenShift rotation i) 1 =
      hullSevenShift rotation (i + 1) := by
  fin_cases rotation <;> fin_cases i <;> rfl

private theorem type5_cutoffDirectedPositive_shifted_eq_decide
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

private theorem type5_shifted_chord_ne
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

private theorem type5_fanSum_hullSevenShift
    (v : Configuration) (cycle : Fin 7 → Fin 8)
    (rotation : Fin 7) :
    fanSum v (fun i => cycle (hullSevenShift rotation i)) =
      fanSum v cycle := by
  rw [fanSum_seven_eq_boundary v
      (fun i => cycle (hullSevenShift rotation i)) (0, 0),
    fanSum_seven_eq_boundary v cycle (0, 0)]
  fin_cases rotation <;> simp [hullSevenShift] <;> ring

private theorem type5_shifted_sign_pos
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
  have hsignBit := type5_cutoffDirectedPositive_shifted_eq_decide
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

private theorem type5_shifted_sign_neg
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
  have hsignBit := type5_cutoffDirectedPositive_shifted_eq_decide
    X cuts hcuts rotation i j hij
  have hnpos :
      ¬ 0 < sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point := by
    apply of_decide_eq_false
    rw [← hsignBit, hbit]
  have hne := type5_shifted_chord_ne X rotation i j hij
  have hraw :
      sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnpos) hne
  simpa only [
    sig_rotate (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) point,
    sig_rotate (cycle (hullSevenShift rotation j)) point
      (cycle (hullSevenShift rotation i))] using hraw

noncomputable def StrictHullSevenInterior.toType5PointData
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
    (hpreferred : HullSevenCutoffType5Preferred cuts rotation) :
    TriHull.HullSevenC24PointData v := by
  refine
    { cycle := fun i => cycleLabels (hullSevenShift rotation i)
      point := pointLabel
      cycle_injective := ?_
      point_outside := ?_
      minTri_pos := hmin
      cycle_strict := ?_
      boundary_pos := ?_
      d13_pos := type5_shifted_sign_pos X cuts hcuts rotation 1 3
        (by decide) hpreferred.1
      d24_pos := type5_shifted_sign_pos X cuts hcuts rotation 2 4
        (by decide) hpreferred.2.1
      d35_pos := type5_shifted_sign_pos X cuts hcuts rotation 3 5
        (by decide) hpreferred.2.2.1
      d14_pos := type5_shifted_sign_pos X cuts hcuts rotation 1 4
        (by decide) hpreferred.2.2.2.1
      d25_pos := type5_shifted_sign_pos X cuts hcuts rotation 2 5
        (by decide) hpreferred.2.2.2.2.1
      d04_pos := type5_shifted_sign_pos X cuts hcuts rotation 0 4
        (by decide) hpreferred.2.2.2.2.2.1
      d26_pos := type5_shifted_sign_pos X cuts hcuts rotation 2 6
        (by decide) hpreferred.2.2.2.2.2.2.1
      d15_neg := type5_shifted_sign_neg X cuts hcuts rotation 1 5
        (by decide) hpreferred.2.2.2.2.2.2.2
      hull_area_eq := harea.trans
        (type5_fanSum_hullSevenShift v cycleLabels rotation).symm }
  · intro i j hij
    exact (hullSevenType5Shift_injective rotation) (hcycleInjective hij)
  · rintro ⟨i, hi⟩
    exact hpointOutside ⟨hullSevenShift rotation i, hi⟩
  · constructor
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).le
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).ne'
  · intro i
    have hraw := X.boundary_pos (hullSevenShift rotation i)
    rw [hullSevenType5Shift_succ] at hraw
    simpa only [
      sig_rotate
        (v (cycleLabels (hullSevenShift rotation i)))
        (v (cycleLabels (hullSevenShift rotation (i + 1))))
        (v pointLabel),
      sig_rotate
        (v (cycleLabels (hullSevenShift rotation (i + 1))))
        (v pointLabel)
        (v (cycleLabels (hullSevenShift rotation i)))] using hraw

theorem hullSevenCutoffType5Exclusion :
    HullSevenCutoffTypeExclusion .type5 := by
  intro v cycleLabels pointLabel X hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  obtain ⟨rotation, hpreferred⟩ :=
    hullSevenCutoff_type5_preferred_of_complementary cuts hcomp hkey
  exact (X.toType5PointData hcycleInjective hpointOutside hmin harea
    cuts hcuts rotation hpreferred).not_beats hbeat

end

end Heilbronn8
