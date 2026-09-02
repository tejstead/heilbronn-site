import Heilbronn8.Survivors.Join.HullSevenGeometricCutoff
import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.HullSevenCutoffExclusionCore
import Heilbronn8.TriHull.HullSevenType7PointAdapter

/-!
# Universal hull-seven type 7 point adapter

The type-7 cutoff is the balanced word `3333333`: at every anchor the first
three forward chords are positive and the last three are negative.  This is
exactly the cyclic sign packet consumed by `HullSevenType7PointData`.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000

noncomputable section

/-- On the reduced two-mask domain, the type-7 key forces cutoff value three
at every anchor (stored as zero-based value two). -/
theorem hullSevenCutoffDecode_type7_all_three :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type7.key →
        ∀ i : Fin 7, (hullSevenCutoffDecode low one i).val = 2 := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type7.key →
        ∀ i : Fin 7, (hullSevenCutoffDecode low one i).val = 2) := by
    letI : DecidablePred (fun i : Fin 7 =>
        (hullSevenCutoffDecode low one i).val = 2) :=
      fun _ => inferInstance
    letI : Decidable (∀ i : Fin 7,
        (hullSevenCutoffDecode low one i).val = 2) :=
      Fintype.decidableForallFintype
    infer_instance
  letI := hullSevenCutoffReducedForallDecidable
    (fun low one =>
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type7.key →
        ∀ i : Fin 7, (hullSevenCutoffDecode low one i).val = 2)
    outcomeDec
  decide

theorem hullSevenCutoff_type7_all_three_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts)
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type7.key) :
    ∀ i : Fin 7, (cuts i).val = 2 := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hkeyDecode :
      hullSevenCutoffOrderType
          (hullSevenCutoffDecode
            (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)) =
        HullSevenType.type7.key := by
    rw [← hdecode]
    exact hkey
  have hall := hullSevenCutoffDecode_type7_all_three
    (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
    hindependent heligible hkeyDecode
  rw [← hdecode] at hall
  exact hall

private theorem type7_row_sign_pos
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point)
    (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (hall : ∀ i : Fin 7, (cuts i).val = 2)
    (i : Fin 7) (offset : Fin 6) (hoffset : offset.val ≤ 2) :
    0 < sig point (cycle i)
      (cycle (hullSevenShift i (hullSevenRowOffset offset))) := by
  have hbit : decide (0 < X.row i offset) = true := by
    rw [hcuts i offset]
    simp [hall i, hoffset]
  have hraw :
      0 < sig (cycle i)
        (cycle (hullSevenShift i (hullSevenRowOffset offset))) point := by
    exact of_decide_eq_true hbit
  simpa only [
    sig_rotate (cycle i)
      (cycle (hullSevenShift i (hullSevenRowOffset offset))) point,
    sig_rotate
      (cycle (hullSevenShift i (hullSevenRowOffset offset))) point
      (cycle i)] using hraw

private lemma type7_boundary_sum_eq_fanSum
    (v : Configuration) (cycle : Fin 7 → Fin 8) (point : Fin 8) :
    (∑ i : TriHull.HullSevenCycleIndex,
      sig (v point) (v (cycle i))
        (v (cycle (i + (1 : TriHull.HullSevenCycleIndex))))) =
        fanSum v cycle := by
  rw [fanSum_seven_eq_boundary v cycle (v point)]
  let f : Fin 7 → ℝ := fun i =>
    sig (v point) (v (cycle i)) (v (cycle (i + 1)))
  change (∑ i : Fin 7, f i) =
    sig (v point) (v (cycle 0)) (v (cycle 1)) +
    sig (v point) (v (cycle 1)) (v (cycle 2)) +
    sig (v point) (v (cycle 2)) (v (cycle 3)) +
    sig (v point) (v (cycle 3)) (v (cycle 4)) +
    sig (v point) (v (cycle 4)) (v (cycle 5)) +
    sig (v point) (v (cycle 5)) (v (cycle 6)) +
    sig (v point) (v (cycle 6)) (v (cycle 0))
  have hf : f = ![
      sig (v point) (v (cycle 0)) (v (cycle 1)),
      sig (v point) (v (cycle 1)) (v (cycle 2)),
      sig (v point) (v (cycle 2)) (v (cycle 3)),
      sig (v point) (v (cycle 3)) (v (cycle 4)),
      sig (v point) (v (cycle 4)) (v (cycle 5)),
      sig (v point) (v (cycle 5)) (v (cycle 6)),
      sig (v point) (v (cycle 6)) (v (cycle 0))] := by
    funext i
    fin_cases i <;> rfl
  rw [hf]
  norm_num [Fin.sum_univ_succ]
  <;> ring

/-- The balanced cutoff constructs the exact cyclic point packet. -/
noncomputable def StrictHullSevenInterior.toType7PointData
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
    (hall : ∀ i : Fin 7, (cuts i).val = 2) :
    TriHull.HullSevenType7PointData v := by
  refine
    { cycle := cycleLabels
      point := pointLabel
      cycle_injective := hcycleInjective
      point_outside := hpointOutside
      minTri_pos := hmin
      adjacent_pos := ?_
      twoStep_pos := ?_
      threeStep_pos := ?_
      hull_area_eq :=
        (type7_boundary_sum_eq_fanSum v cycleLabels pointLabel).trans
          harea.symm }
  · intro i
    have h := type7_row_sign_pos X cuts hcuts hall i 0 (by decide)
    change 0 < sig (v pointLabel) (v (cycleLabels i))
      (v (cycleLabels
        (i + (1 : TriHull.HullSevenCycleIndex)))) at h
    exact h
  · intro i
    have h := type7_row_sign_pos X cuts hcuts hall i 1 (by decide)
    change 0 < sig (v pointLabel) (v (cycleLabels i))
      (v (cycleLabels
        (i + (2 : TriHull.HullSevenCycleIndex)))) at h
    exact h
  · intro i
    have h := type7_row_sign_pos X cuts hcuts hall i 2 (by decide)
    change 0 < sig (v pointLabel) (v (cycleLabels i))
      (v (cycleLabels
        (i + (3 : TriHull.HullSevenCycleIndex)))) at h
    exact h

/-- Direct universal type-7 cutoff closer. -/
theorem hullSevenCutoffType7Exclusion :
    HullSevenCutoffTypeExclusion .type7 := by
  intro v cycleLabels pointLabel X hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  have hall :=
    hullSevenCutoff_type7_all_three_of_complementary cuts hcomp hkey
  exact (X.toType7PointData hcycleInjective hpointOutside hmin harea
    cuts hcuts hall).not_beats hbeat

end

end Heilbronn8
