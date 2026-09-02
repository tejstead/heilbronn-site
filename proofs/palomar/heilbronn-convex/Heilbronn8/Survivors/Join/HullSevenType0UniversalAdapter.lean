import Heilbronn8.Survivors.Join.HullSevenGeometricCutoff
import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.TriHull.HullSevenType0PointAdapter

/-!
# Universal hull-seven type 0 point adapter

The radial classifier produces cutoff data in the source hull orientation.
For type 0, every labelled cutoff has an orientation-preserving rotation in
which `06` is the unique negative increasing chord.  This module proves that
finite statement through the reduced two-mask classifier and transports the
resulting sign packet to `HullSevenType0PointData`.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

noncomputable section

/-- A source cutoff has the preferred type 0 sign pattern after this
orientation-preserving rotation. -/
def HullSevenCutoffType0Preferred
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) : Prop :=
  ∀ i j : Fin 7, i < j →
    hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val =
      decide ((i, j) ≠ ((0 : Fin 7), (6 : Fin 7)))

private def hullSevenCutoffType0PreferredDecidable
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) :
    Decidable (HullSevenCutoffType0Preferred cuts rotation) := by
  unfold HullSevenCutoffType0Preferred
  apply hullSevenDecidableForallTwo
  intro i j
  infer_instance

/-- The reduced cutoff representation has a nonreflected preferred type 0
presentation whenever its canonical key is type 0. -/
theorem hullSevenCutoffDecode_type0_preferred :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type0.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType0Preferred
            (hullSevenCutoffDecode low one) rotation := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type0.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType0Preferred
            (hullSevenCutoffDecode low one) rotation) := by
    letI : DecidablePred (fun rotation : Fin 7 =>
        HullSevenCutoffType0Preferred
          (hullSevenCutoffDecode low one) rotation) :=
      fun rotation => hullSevenCutoffType0PreferredDecidable _ rotation
    letI : Decidable (∃ rotation : Fin 7,
        HullSevenCutoffType0Preferred
          (hullSevenCutoffDecode low one) rotation) :=
      Fintype.decidableExistsFintype
    infer_instance
  letI := hullSevenCutoffReducedForallDecidable
    (fun low one =>
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type0.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType0Preferred
            (hullSevenCutoffDecode low one) rotation)
    outcomeDec
  decide

/-- Every complementary type 0 cutoff admits the preferred nonreflected
rotation consumed by the type 0 point adapter. -/
theorem hullSevenCutoff_type0_preferred_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts)
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type0.key) :
    ∃ rotation : Fin 7, HullSevenCutoffType0Preferred cuts rotation := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hkeyDecode :
      hullSevenCutoffOrderType
          (hullSevenCutoffDecode
            (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)) =
        HullSevenType.type0.key := by
    rw [← hdecode]
    exact hkey
  have hpreferred := hullSevenCutoffDecode_type0_preferred
    (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
    hindependent heligible hkeyDecode
  rw [← hdecode] at hpreferred
  exact hpreferred

private theorem hullSevenShift_injective (rotation : Fin 7) :
    Function.Injective (hullSevenShift rotation) := by
  intro i j hij
  exact add_left_cancel hij

private theorem cutoffDirectedPositive_shifted_eq_decide
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

private theorem shifted_chord_ne
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
theorem fanSum_hullSevenShift
    (v : Configuration) (cycle : Fin 7 → Fin 8)
    (rotation : Fin 7) :
    fanSum v (fun i => cycle (hullSevenShift rotation i)) =
      fanSum v cycle := by
  rw [fanSum_seven_eq_boundary v
      (fun i => cycle (hullSevenShift rotation i)) (0, 0),
    fanSum_seven_eq_boundary v cycle (0, 0)]
  fin_cases rotation <;> simp [hullSevenShift] <;> ring

/-- Transport a preferred cutoff presentation to the exact actual point
packet consumed by the type 0 scalar theorem. -/
noncomputable def StrictHullSevenInterior.toType0PointData
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
    (hpreferred : HullSevenCutoffType0Preferred cuts rotation) :
    TriHull.HullSevenType0PointData v := by
  refine
    { cycle := fun i => cycleLabels (hullSevenShift rotation i)
      point := pointLabel
      cycle_injective := ?_
      point_outside := ?_
      minTri_pos := hmin
      cycle_strict := ?_
      positive := ?_
      negative06 := ?_
      hull_area_eq := harea.trans
        (fanSum_hullSevenShift v cycleLabels rotation).symm }
  · intro i j hij
    exact (hullSevenShift_injective rotation) (hcycleInjective hij)
  · rintro ⟨i, hi⟩
    exact hpointOutside ⟨hullSevenShift rotation i, hi⟩
  · constructor
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).le
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).ne'
  · intro i j hpositive
    have hsignBit := cutoffDirectedPositive_shifted_eq_decide
      X cuts hcuts rotation i j hpositive.1
    have hpreferredBit := hpreferred i j hpositive.1
    have hexception :
        decide ((i, j) ≠ ((0 : Fin 7), (6 : Fin 7))) = true := by
      simp [hpositive.2]
    have hdecide :
        decide (0 < sig
          (v (cycleLabels (hullSevenShift rotation i)))
          (v (cycleLabels (hullSevenShift rotation j)))
          (v pointLabel)) = true := by
      rw [← hsignBit, hpreferredBit, hexception]
    have hraw := of_decide_eq_true hdecide
    simpa only [
      sig_rotate
        (v (cycleLabels (hullSevenShift rotation i)))
        (v (cycleLabels (hullSevenShift rotation j))) (v pointLabel),
      sig_rotate
        (v (cycleLabels (hullSevenShift rotation j))) (v pointLabel)
        (v (cycleLabels (hullSevenShift rotation i)))] using hraw
  · have hsignBit := cutoffDirectedPositive_shifted_eq_decide
      X cuts hcuts rotation 0 6 (by decide)
    have hpreferredBit := hpreferred 0 6 (by decide)
    have hdecide :
        decide (0 < sig
          (v (cycleLabels (hullSevenShift rotation 0)))
          (v (cycleLabels (hullSevenShift rotation 6)))
          (v pointLabel)) = false := by
      rw [← hsignBit, hpreferredBit]
      decide
    have hnpos := of_decide_eq_false hdecide
    have hne := shifted_chord_ne X rotation 0 6 (by decide)
    have hraw :
        sig (v (cycleLabels (hullSevenShift rotation 0)))
          (v (cycleLabels (hullSevenShift rotation 6)))
          (v pointLabel) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnpos) hne
    simpa only [
      sig_rotate
        (v (cycleLabels (hullSevenShift rotation 0)))
        (v (cycleLabels (hullSevenShift rotation 6))) (v pointLabel),
      sig_rotate
        (v (cycleLabels (hullSevenShift rotation 6))) (v pointLabel)
        (v (cycleLabels (hullSevenShift rotation 0)))] using hraw

end

end Heilbronn8
