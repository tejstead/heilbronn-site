import Heilbronn8.HullSevenCutoffExclusionCore
import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.TriHull.HullSevenType2HyperbolicPointAdapter

/-!
# Universal hull-seven type 2 hyperbolic adapter

The canonical type-2 key has an orientation-preserving cyclic presentation
whose only negative increasing pairs are `06`, `16`, and `26`.  This file
proves that presentation theorem directly for every reduced complementary
cutoff, transports it to the honest hyperbolic point packet, and leaves one
stable scalar-packet closer as its only input.

No older scalar module carrying the misnamed type-2 chamber is imported.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

noncomputable section

/-- A source cutoff is in the preferred honest type-2 chart after this
orientation-preserving cyclic rotation.  Its only negative increasing pairs
are `06`, `16`, and `26`. -/
def HullSevenCutoffType2HyperbolicPreferred
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) : Prop :=
  ∀ i j : Fin 7, i < j →
    hullSevenCutoffDirectedPositive cuts
        (hullSevenShift rotation i).val
        (hullSevenShift rotation j).val =
      decide ((i, j) ≠ ((0 : Fin 7), (6 : Fin 7)) ∧
        (i, j) ≠ ((1 : Fin 7), (6 : Fin 7)) ∧
        (i, j) ≠ ((2 : Fin 7), (6 : Fin 7)))

private def hullSevenCutoffType2HyperbolicPreferredDecidable
    (cuts : Fin 7 → Fin 5) (rotation : Fin 7) :
    Decidable (HullSevenCutoffType2HyperbolicPreferred cuts rotation) := by
  unfold HullSevenCutoffType2HyperbolicPreferred
  apply hullSevenDecidableForallTwo
  intro i j
  infer_instance

/-- Every reduced cutoff with the canonical type-2 key has the preferred
direct three-negative-chord presentation.  This is an exact finite theorem:
the kernel enumerates the two reduced Boolean masks. -/
theorem hullSevenCutoffDecode_type2_hyperbolic_preferred :
    ∀ low one : HullSevenCutoffMask,
      HullSevenCutoffLowIndependent low →
      HullSevenCutoffOneEligible low one →
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type2.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType2HyperbolicPreferred
            (hullSevenCutoffDecode low one) rotation := by
  let outcomeDec (low one : HullSevenCutoffMask) : Decidable
      (hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type2.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType2HyperbolicPreferred
            (hullSevenCutoffDecode low one) rotation) := by
    letI : DecidablePred (fun rotation : Fin 7 =>
        HullSevenCutoffType2HyperbolicPreferred
          (hullSevenCutoffDecode low one) rotation) :=
      fun rotation =>
        hullSevenCutoffType2HyperbolicPreferredDecidable _ rotation
    letI : Decidable (∃ rotation : Fin 7,
        HullSevenCutoffType2HyperbolicPreferred
          (hullSevenCutoffDecode low one) rotation) :=
      Fintype.decidableExistsFintype
    infer_instance
  letI := hullSevenCutoffReducedForallDecidable
    (fun low one =>
      hullSevenCutoffOrderType (hullSevenCutoffDecode low one) =
          HullSevenType.type2.key →
        ∃ rotation : Fin 7,
          HullSevenCutoffType2HyperbolicPreferred
            (hullSevenCutoffDecode low one) rotation)
    outcomeDec
  decide

/-- Every complementary cutoff with the type-2 key admits the preferred
orientation-preserving cyclic presentation. -/
theorem hullSevenCutoff_type2_hyperbolic_preferred_of_complementary
    (cuts : Fin 7 → Fin 5)
    (hcomp : HullSevenCutoffComplementary cuts)
    (hkey : hullSevenCutoffOrderType cuts = HullSevenType.type2.key) :
    ∃ rotation : Fin 7,
      HullSevenCutoffType2HyperbolicPreferred cuts rotation := by
  obtain ⟨hindependent, heligible, hdecode⟩ :=
    hullSevenCutoff_structuralReduction cuts hcomp
  have hkeyDecode :
      hullSevenCutoffOrderType
          (hullSevenCutoffDecode
            (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)) =
        HullSevenType.type2.key := by
    rw [← hdecode]
    exact hkey
  have hpreferred := hullSevenCutoffDecode_type2_hyperbolic_preferred
    (hullSevenCutoffLowMask cuts) (hullSevenCutoffOneMask cuts)
    hindependent heligible hkeyDecode
  rw [← hdecode] at hpreferred
  exact hpreferred

private theorem hullSevenType2HyperbolicShift_injective
    (rotation : Fin 7) :
    Function.Injective (hullSevenShift rotation) := by
  intro i j hij
  exact add_left_cancel hij

private theorem type2Hyperbolic_cutoffDirectedPositive_shifted_eq_decide
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

private theorem type2Hyperbolic_shifted_chord_ne
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

private theorem type2Hyperbolic_fanSum_hullSevenShift
    (v : Configuration) (cycle : Fin 7 → Fin 8)
    (rotation : Fin 7) :
    fanSum v (fun i => cycle (hullSevenShift rotation i)) =
      fanSum v cycle := by
  rw [fanSum_seven_eq_boundary v
      (fun i => cycle (hullSevenShift rotation i)) (0, 0),
    fanSum_seven_eq_boundary v cycle (0, 0)]
  fin_cases rotation <;> simp [hullSevenShift] <;> ring

private theorem type2Hyperbolic_shifted_sign_pos
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
  have hsignBit :=
    type2Hyperbolic_cutoffDirectedPositive_shifted_eq_decide
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

private theorem type2Hyperbolic_shifted_sign_neg
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
  have hsignBit :=
    type2Hyperbolic_cutoffDirectedPositive_shifted_eq_decide
      X cuts hcuts rotation i j hij
  have hnpos :
      ¬ 0 < sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point := by
    apply of_decide_eq_false
    rw [← hsignBit, hbit]
  have hne := type2Hyperbolic_shifted_chord_ne X rotation i j hij
  have hraw :
      sig (cycle (hullSevenShift rotation i))
        (cycle (hullSevenShift rotation j)) point < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnpos) hne
  simpa only [
    sig_rotate (cycle (hullSevenShift rotation i))
      (cycle (hullSevenShift rotation j)) point,
    sig_rotate (cycle (hullSevenShift rotation j)) point
      (cycle (hullSevenShift rotation i))] using hraw

/-- Transport a preferred cutoff presentation to the exact honest type-2
point packet consumed by the hyperbolic determinant adapter. -/
noncomputable def StrictHullSevenInterior.toType2HyperbolicPointData
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
    (hpreferred :
      HullSevenCutoffType2HyperbolicPreferred cuts rotation) :
    TriHull.HullSevenType2HyperbolicPointData v := by
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
      negative26 := ?_
      hull_area_eq := harea.trans
        (type2Hyperbolic_fanSum_hullSevenShift
          v cycleLabels rotation).symm }
  · intro i j hij
    exact (hullSevenType2HyperbolicShift_injective rotation)
      (hcycleInjective hij)
  · rintro ⟨i, hi⟩
    exact hpointOutside ⟨hullSevenShift rotation i, hi⟩
  · constructor
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).le
    · intro i j k hij hjk
      exact (X.shifted_cycle_pos rotation i j k hij hjk).ne'
  · intro i j hpositive
    apply type2Hyperbolic_shifted_sign_pos
      X cuts hcuts rotation i j hpositive.1
    rw [hpreferred i j hpositive.1]
    apply decide_eq_true
    exact ⟨hpositive.2.1, hpositive.2.2.1, hpositive.2.2.2⟩
  · apply type2Hyperbolic_shifted_sign_neg
      X cuts hcuts rotation 0 6 (by decide)
    rw [hpreferred 0 6 (by decide)]
    decide
  · apply type2Hyperbolic_shifted_sign_neg
      X cuts hcuts rotation 1 6 (by decide)
    rw [hpreferred 1 6 (by decide)]
    decide
  · apply type2Hyperbolic_shifted_sign_neg
      X cuts hcuts rotation 2 6 (by decide)
    rw [hpreferred 2 6 (by decide)]
    decide

/-- Stable scalar seam for the honest type-2 universal adapter.  A compact
scalar proof supplies this one proposition; the finite key theorem and all
point geometry above remain independent of that proof. -/
def HullSevenType2HyperbolicPacketCloser : Prop :=
  ∀ {H : ℝ}, TriHull.HullSevenType2HyperbolicPacket H →
    (25 : ℝ) / 2 ≤ H

namespace TriHull

/-- The rational packet bound implies the sharp `v8`-scaled bound. -/
theorem hullSeven_v8_of_type2_hyperbolic_packetCloser
    (closer : HullSevenType2HyperbolicPacketCloser)
    {H : ℝ} (D : HullSevenType2HyperbolicPacket H) :
    1 ≤ v8 * H := by
  have hH : (25 : ℝ) / 2 ≤ H := closer D
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod.le

/-- An actual preferred type-2 point packet contradicts a strict beating
row as soon as the one scalar packet closer is supplied. -/
theorem HullSevenType2HyperbolicPointData.not_beats_of_packetCloser
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v)
    (closer : HullSevenType2HyperbolicPacketCloser)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hbound := hullSeven_v8_of_type2_hyperbolic_packetCloser
    closer X.toHyperbolicPacket
  have hratio : 1 ≤ (v8 * doubledHullArea v) / minTri v := by
    calc
      1 ≤ v8 * (doubledHullArea v / minTri v) := hbound
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  have hmul : minTri v ≤ v8 * doubledHullArea v := by
    simpa using (le_div_iff₀ X.minTri_pos).1 hratio
  exact (not_lt_of_ge hmul) hbeat.2

end TriHull

/-- Universal type-2 cutoff exclusion, conditional only on the stable honest
hyperbolic scalar packet closer. -/
theorem hullSevenCutoffType2HyperbolicExclusion
    (closer : HullSevenType2HyperbolicPacketCloser) :
    HullSevenCutoffTypeExclusion .type2 := by
  intro v cycleLabels pointLabel X hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  obtain ⟨rotation, hpreferred⟩ :=
    hullSevenCutoff_type2_hyperbolic_preferred_of_complementary
      cuts hcomp hkey
  exact (X.toType2HyperbolicPointData
    hcycleInjective hpointOutside hmin harea
    cuts hcuts rotation hpreferred).not_beats_of_packetCloser closer hbeat

end

end Heilbronn8
