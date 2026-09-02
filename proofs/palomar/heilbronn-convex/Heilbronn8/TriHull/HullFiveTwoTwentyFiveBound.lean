import Heilbronn8.TriHull.HullFive300CabUniversal

/-!
# Closed rational hull-five bound

This is the equality-aware form of the table-free hull-five argument.  It
keeps the branchwise geometric proof but stops at the rational estimate

`25 * minTri v ≤ 2 * doubledHullArea v`.

In particular, the theorem below has no `Beats` or order-density hypothesis.
The only metric input is the already-proved full right-ear endpoint
`hullFive300_rightProfile_universal_bound`.

This phase-two source deliberately lives outside the frozen Palomar package.
The few private area/profile bridges from `UniversalHullFiveGeometry` are
restated here, rather than weakening their encapsulation in the active tree.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

@[simp] private lemma finFive_add_two_add_one_raw (k : Fin 5) :
    (k + 2) + 1 = k + 3 := by
  fin_cases k <;> decide

@[simp] private lemma finFive_add_two_add_three_raw (k : Fin 5) :
    (k + 2) + 3 = k := by
  fin_cases k <;> decide

private lemma doubledHullArea_eq_reindexedOccupancyFan_raw
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (e : Equiv.Perm (Fin 8))
    (hchart : ∀ i : Fin 5,
      e (hullFiveOccupancyCycleSlot i) = d.castGet h5 i)
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    let e' : Fin 8 → Fin 8 :=
      fun i ↦ e (hullFiveOccupancyReindex shift inner i)
    doubledHullArea v =
      sig (v (e' 0)) (v (e' 1)) (v (e' 4)) +
        sig (v (e' 0)) (v (e' 4)) (v (e' 2)) +
        sig (v (e' 0)) (v (e' 2)) (v (e' 3)) := by
  let e' : Fin 8 → Fin 8 :=
    fun i ↦ e (hullFiveOccupancyReindex shift inner i)
  have hcertified : doubledHullArea v = d.fanExpr v :=
    doubledHullArea_eq_of_isHullArea hcycle.isHullArea
  have hcast : fanSum v (d.castGet h5) = d.fanExpr v :=
    HullCycleData.fanSum_castGet d h5
  have hbaseFun :
      (fun i : Fin 5 ↦ e (hullFiveOccupancyCycleSlot i)) =
        d.castGet h5 :=
    funext hchart
  have hshift :
      fanSum v (fun i : Fin 5 ↦
          e' (hullFiveOccupancyCycleSlot i)) =
        fanSum v (fun i : Fin 5 ↦
          e (hullFiveOccupancyCycleSlot i)) := by
    simpa only [e'] using
      fanSum_hullFiveOccupancyReindex v e shift inner
  calc
    doubledHullArea v = d.fanExpr v := hcertified
    _ = fanSum v (d.castGet h5) := hcast.symm
    _ = fanSum v (fun i : Fin 5 ↦
        e (hullFiveOccupancyCycleSlot i)) := by rw [hbaseFun]
    _ = fanSum v (fun i : Fin 5 ↦
        e' (hullFiveOccupancyCycleSlot i)) := hshift.symm
    _ = sig (v (e' 0)) (v (e' 1)) (v (e' 4)) +
        sig (v (e' 0)) (v (e' 4)) (v (e' 2)) +
        sig (v (e' 0)) (v (e' 2)) (v (e' 3)) :=
      fanSum_hullFiveOccupancyCycleSlot v e'

private lemma doubledHullArea_eq_endReindexFan_raw
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (e : Equiv.Perm (Fin 8))
    (hchart : ∀ i : Fin 5,
      e (hullFiveOccupancyCycleSlot i) = d.castGet h5 i)
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    let f := hullFiveEndReindex e shift inner
    doubledHullArea v =
      sig (v (f 0)) (v (f 1)) (v (f 2)) +
        sig (v (f 0)) (v (f 2)) (v (f 3)) +
        sig (v (f 0)) (v (f 3)) (v (f 4)) := by
  let f := hullFiveEndReindex e shift inner
  have harea := doubledHullArea_eq_reindexedOccupancyFan_raw
    hcycle h5 e hchart shift inner
  simpa only [f, hullFiveEndReindex,
    hullFiveSequentialToOccupancy_zero,
    hullFiveSequentialToOccupancy_one,
    hullFiveSequentialToOccupancy_two,
    hullFiveSequentialToOccupancy_three,
    hullFiveSequentialToOccupancy_four, Equiv.trans_apply] using harea

private lemma hullFive111_packetFan_eq_fanSum_raw
    (v : Configuration) (e : Fin 8 → Fin 8) :
    sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 1)) (v (e 4)) (v (e 2)) +
        sig (v (e 2)) (v (e 3)) (v (e 0)) =
      fanSum v (fun i : Fin 5 ↦
        e (hullFiveOccupancyCycleSlot i)) := by
  have hfp : fanPairs 5 =
      {((1 : Fin 5), (2 : Fin 5)), (2, 3), (3, 4)} := by
    decide
  simp [fanSum, hfp, hullFiveOccupancyCycleSlot, sig]
  ring

/-- The strict UZ/VZ packet estimate, transported to the certified hull
area without passing through `Beats`. -/
theorem hullFive111_reindexedPacket_forces_twoTwentyFiveBound_of_hullCycle
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (e : Equiv.Perm (Fin 8))
    (hchart : ∀ i : Fin 5,
      e (hullFiveOccupancyCycleSlot i) = d.castGet h5 i)
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3))
    (hmin : 0 < minTri v)
    (hpacket :
      let e' : Fin 8 → Fin 8 :=
        fun i ↦ e (hullFiveOccupancyReindex shift inner i)
      HullFive111UZPacket v e' ∨ HullFive111VZPacket v e') :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  let e' : Fin 8 → Fin 8 :=
    fun i ↦ e (hullFiveOccupancyReindex shift inner i)
  have he' : Function.Injective e' :=
    e.injective.comp (hullFiveOccupancyReindex shift inner).injective
  have hbound : minTri v * 25 < 2 *
      (sig (v (e' 0)) (v (e' 1)) (v (e' 2)) +
        sig (v (e' 1)) (v (e' 4)) (v (e' 2)) +
        sig (v (e' 2)) (v (e' 3)) (v (e' 0))) := by
    rcases hpacket with huz | hvz
    · exact hullFive111_uz_packet_forces_hull_bound v e' he' hmin huz
    · exact hullFive111_vz_packet_forces_hull_bound v e' he' hmin hvz
  have hcertified : doubledHullArea v = d.fanExpr v :=
    doubledHullArea_eq_of_isHullArea hcycle.isHullArea
  have hcast : fanSum v (d.castGet h5) = d.fanExpr v :=
    HullCycleData.fanSum_castGet d h5
  have hbaseFun :
      (fun i : Fin 5 ↦ e (hullFiveOccupancyCycleSlot i)) =
        d.castGet h5 :=
    funext hchart
  have hshift :
      fanSum v (fun i : Fin 5 ↦
          e' (hullFiveOccupancyCycleSlot i)) =
        fanSum v (fun i : Fin 5 ↦
          e (hullFiveOccupancyCycleSlot i)) := by
    simpa only [e'] using
      fanSum_hullFiveOccupancyReindex v e shift inner
  have harea : doubledHullArea v =
      sig (v (e' 0)) (v (e' 1)) (v (e' 2)) +
        sig (v (e' 1)) (v (e' 4)) (v (e' 2)) +
        sig (v (e' 2)) (v (e' 3)) (v (e' 0)) := by
    calc
      doubledHullArea v = d.fanExpr v := hcertified
      _ = fanSum v (d.castGet h5) := hcast.symm
      _ = fanSum v (fun i : Fin 5 ↦
          e (hullFiveOccupancyCycleSlot i)) := by rw [hbaseFun]
      _ = fanSum v (fun i : Fin 5 ↦
          e' (hullFiveOccupancyCycleSlot i)) := hshift.symm
      _ = sig (v (e' 0)) (v (e' 1)) (v (e' 2)) +
          sig (v (e' 1)) (v (e' 4)) (v (e' 2)) +
          sig (v (e' 2)) (v (e' 3)) (v (e' 0)) :=
        (hullFive111_packetFan_eq_fanSum_raw v e').symm
  rw [harea]
  simpa [mul_comm] using hbound.le

private lemma selectedProfileMem_raw
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (regions : Fin 3 → HullFivePointRegion)
    (hmem : ∀ i : Fin 3, ∀ anchor : Fin 5,
      InHullFiveFanCell
        (v (e (hullFiveOccupancyInnerSlot i)))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor
        ((regions i).fanCell anchor))
    (inner : Equiv.Perm (Fin 3)) (i : Fin 3)
    (anchor : Fin 5) (cell : Fin 3)
    (hcell : (regions (inner i)).fanCell anchor = cell) :
    InHullFiveFanCell
      (v (e (hullFiveOccupancyInnerSlot (inner i))))
      (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor cell := by
  simpa only [hcell] using hmem (inner i) anchor

private lemma endRightProfileA_of_fullProfile_raw
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (regions : Fin 3 → HullFivePointRegion)
    (hmem : ∀ i : Fin 3, ∀ anchor : Fin 5,
      InHullFiveFanCell
        (v (e (hullFiveOccupancyInnerSlot i)))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor
        ((regions i).fanCell anchor))
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hprofile : (regions (inner i)).IsEndRightAAt k) :
    HullFiveEndRightProfileA v (hullFiveEndReindex e k inner)
      (hullFiveOccupancyInnerSlot i) := by
  have h0 : (regions (inner i)).fanCell k = 1 := by
    simpa [HullFivePointRegion.IsEndRightAAt] using hprofile 0
  have h1 : (regions (inner i)).fanCell (k + 1) = 0 := by
    simpa [HullFivePointRegion.IsEndRightAAt] using hprofile 1
  have h2 : (regions (inner i)).fanCell (k + 2) = 0 := by
    simpa [HullFivePointRegion.IsEndRightAAt] using hprofile 2
  have hm0 := selectedProfileMem_raw v e regions hmem inner i k 1 h0
  have hm1 := selectedProfileMem_raw v e regions hmem inner i (k + 1) 0 h1
  have hm2 := selectedProfileMem_raw v e regions hmem inner i (k + 2) 0 h2
  exact {
    axc := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm0
    bxc := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm1
    xcd := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm2 }

private lemma endRightProfileB_of_fullProfile_raw
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (regions : Fin 3 → HullFivePointRegion)
    (hmem : ∀ i : Fin 3, ∀ anchor : Fin 5,
      InHullFiveFanCell
        (v (e (hullFiveOccupancyInnerSlot i)))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor
        ((regions i).fanCell anchor))
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hprofile : (regions (inner i)).IsEndRightBAt k) :
    HullFiveEndRightProfileB v (hullFiveEndReindex e k inner)
      (hullFiveOccupancyInnerSlot i) := by
  have h0 : (regions (inner i)).fanCell k = 1 := by
    simpa [HullFivePointRegion.IsEndRightBAt] using hprofile 0
  have h1 : (regions (inner i)).fanCell (k + 1) = 0 := by
    simpa [HullFivePointRegion.IsEndRightBAt] using hprofile 1
  have h2 : (regions (inner i)).fanCell (k + 2) = 1 := by
    simpa [HullFivePointRegion.IsEndRightBAt] using hprofile 2
  have h4 : (regions (inner i)).fanCell (k + 4) = 1 := by
    simpa [HullFivePointRegion.IsEndRightBAt] using hprofile 4
  have hm0 := selectedProfileMem_raw v e regions hmem inner i k 1 h0
  have hm1 := selectedProfileMem_raw v e regions hmem inner i (k + 1) 0 h1
  have hm2 := selectedProfileMem_raw v e regions hmem inner i (k + 2) 1 h2
  have hm4 := selectedProfileMem_raw v e regions hmem inner i (k + 4) 1 h4
  exact {
    axc := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm0
    bxc := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm1
    xda := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm2
    dbx := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm4 }

private lemma endRightProfileC_of_fullProfile_raw
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (regions : Fin 3 → HullFivePointRegion)
    (hmem : ∀ i : Fin 3, ∀ anchor : Fin 5,
      InHullFiveFanCell
        (v (e (hullFiveOccupancyInnerSlot i)))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor
        ((regions i).fanCell anchor))
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hprofile : (regions (inner i)).IsEndRightCAt k) :
    HullFiveEndRightProfileC v (hullFiveEndReindex e k inner)
      (hullFiveOccupancyInnerSlot i) := by
  have h0 : (regions (inner i)).fanCell k = 0 := by
    simpa [HullFivePointRegion.IsEndRightCAt] using hprofile 0
  have h1 : (regions (inner i)).fanCell (k + 1) = 0 := by
    simpa [HullFivePointRegion.IsEndRightCAt] using hprofile 1
  have h4 : (regions (inner i)).fanCell (k + 4) = 1 := by
    simpa [HullFivePointRegion.IsEndRightCAt] using hprofile 4
  have hm0 := selectedProfileMem_raw v e regions hmem inner i k 0 h0
  have hm1 := selectedProfileMem_raw v e regions hmem inner i (k + 1) 0 h1
  have hm4 := selectedProfileMem_raw v e regions hmem inner i (k + 4) 1 h4
  exact {
    abx := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm0
    bxc := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm1
    dbx := by
      rw [hullFiveEndReindex_inner, hullFiveOccupancyReindex_inner]
      simpa [hullFiveEndReindex, InHullFiveFanCell,
        InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        hullFiveSequentialToOccupancy] using hm4 }

private lemma twoTwentyFiveBound_of_fanBound_raw
    {v : Configuration} {H : ℝ}
    (harea : doubledHullArea v = H)
    (hbound : minTri v * 25 ≤ 2 * H) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  rw [harea]
  simpa [mul_comm] using hbound

/-- Conditional closed hull-five estimate.  This is the branchwise rational
spine of `geometricHullFiveExclusion_of_rightEar300`, with positivity supplied
directly and with no contradiction hypothesis. -/
theorem geometricHullFive_twoTwentyFiveBound_of_rightEar300
    (hRight300 : HullFive300RightProfileUniversalBound)
    {v : Configuration} (custody : GeometricHullCustody v)
    (hmin : 0 < minTri v)
    (h5 : custody.data.cycle.length = 5) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  have hsigns : AllTripleSignsStrict v :=
    allTripleSignsStrict_of_minTri_pos v hmin
  obtain ⟨e, pRegion, qRegion, rRegion, hchart, houtcome,
      hPmem, hQmem, hRmem⟩ :=
    hullFiveThreePointProfiles_relabel_of_hullCycleOf
      hsigns custody.hull h5
  have hbaseCycle : StrictCyclicPos hullFiveOccupancyCycleSlot
      (fun i ↦ v (e i)) := by
    have hcastCycle := HullCycleData.strictCyclicPos_cast custody.data h5
      custody.hull.strictCyclicPos
    refine ⟨?_, ?_⟩
    · intro i j k hij hjk
      simpa only [hchart] using hcastCycle.1 i j k hij hjk
    · intro i j k hij hjk
      simpa only [hchart] using hcastCycle.2 i j k hij hjk
  let regions : Fin 3 → HullFivePointRegion :=
    hullFiveRegionTriple pRegion qRegion rRegion
  have hmem : ∀ i : Fin 3, ∀ anchor : Fin 5,
      InHullFiveFanCell
        (v (e (hullFiveOccupancyInnerSlot i)))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor
        ((regions i).fanCell anchor) := by
    intro i anchor
    fin_cases i
    · simpa [regions, hullFiveRegionTriple,
        hullFiveOccupancyInnerSlot, hchart] using hPmem anchor
    · simpa [regions, hullFiveRegionTriple,
        hullFiveOccupancyInnerSlot, hchart] using hQmem anchor
    · simpa [regions, hullFiveRegionTriple,
        hullFiveOccupancyInnerSlot, hchart] using hRmem anchor
  let isCentral : Prop := ∃ anchor : Fin 5,
    (hullFiveRegionCounts pRegion qRegion rRegion anchor).IsCentral300
  let isEnd : Prop := ∃ anchor : Fin 5,
    (hullFiveRegionCounts pRegion qRegion rRegion anchor).IsEnd210
  let isMiddle : Prop := ∃ anchor : Fin 5,
    (hullFiveRegionCounts pRegion qRegion rRegion anchor).IsMiddle210
  by_cases hcentral : isCentral
  · obtain ⟨k, hpCell, hqCell, hrCell⟩ :=
      hullFiveCentralRoute_of_counts pRegion qRegion rRegion hcentral
    let innerId : Equiv.Perm (Fin 3) := Equiv.refl _
    let shift : Fin 5 := k + 2
    let sigma : Equiv.Perm (Fin 8) :=
      (hullFiveOccupancyReindex shift innerId).trans e
    have hcycleSigma : StrictCyclicPos hullFiveOccupancyCycleSlot
        (fun i ↦ v (sigma i)) := by
      simpa only [sigma, shift, Equiv.trans_apply] using
        strictCyclicPos_hullFiveOccupancyReindex
          (fun i ↦ v (e i)) hbaseCycle shift innerId
    have hpRaw := hmem 0 k
    have hqRaw := hmem 1 k
    have hrRaw := hmem 2 k
    have hpABC : InTriStrict (v (sigma 5))
        (v (sigma 0)) (v (sigma 1)) (v (sigma 2)) := by
      apply inTriStrict_rotate_hullFive
      simpa [regions, hullFiveRegionTriple, hpCell, sigma, shift, innerId,
        InHullFiveFanCell, InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        finFive_add_two_add_one_raw,
        finFive_add_two_add_three_raw] using hpRaw
    have hqABC : InTriStrict (v (sigma 6))
        (v (sigma 0)) (v (sigma 1)) (v (sigma 2)) := by
      apply inTriStrict_rotate_hullFive
      simpa [regions, hullFiveRegionTriple, hqCell, sigma, shift, innerId,
        InHullFiveFanCell, InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        finFive_add_two_add_one_raw,
        finFive_add_two_add_three_raw] using hqRaw
    have hrABC : InTriStrict (v (sigma 7))
        (v (sigma 0)) (v (sigma 1)) (v (sigma 2)) := by
      apply inTriStrict_rotate_hullFive
      simpa [regions, hullFiveRegionTriple, hrCell, sigma, shift, innerId,
        InHullFiveFanCell, InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        finFive_add_two_add_one_raw,
        finFive_add_two_add_three_raw] using hrRaw
    have hbound := hullFive300_allCentral_relabel_forces_fan_bound
      v sigma hmin hcycleSigma hpABC hqABC hrABC
    have harea := doubledHullArea_eq_reindexedOccupancyFan_raw
      custody.hull h5 e hchart shift innerId
    exact twoTwentyFiveBound_of_fanBound_raw harea hbound
  · by_cases hend : isEnd
    · obtain ⟨k, inner, major, hroute, hrightRoute⟩ :=
        hullFiveEndRoute_with_rightResidual pRegion qRegion rRegion
          hcentral hend
      let f : Equiv.Perm (Fin 8) := hullFiveEndReindex e k inner
      have hcycleF : StrictCyclicPos hullFiveSequentialCycleSlot
          (fun i ↦ v (f i)) := by
        simpa only [f] using
          strictCyclicPos_hullFiveEndReindex v e hbaseCycle k inner
      have hABC : 0 < sig (v (f 0)) (v (f 1)) (v (f 3)) := by
        simpa [hullFiveSequentialCycleSlot] using
          hcycleF.pos 0 1 3 (by decide) (by decide)
      have hBXC : 0 < sig (v (f 1)) (v (f 2)) (v (f 3)) := by
        simpa [hullFiveSequentialCycleSlot] using
          hcycleF.pos 1 2 3 (by decide) (by decide)
      have hABX : 0 < sig (v (f 0)) (v (f 1)) (v (f 2)) := by
        simpa [hullFiveSequentialCycleSlot] using
          hcycleF.pos 0 1 2 (by decide) (by decide)
      have hAXC : 0 < sig (v (f 0)) (v (f 2)) (v (f 3)) := by
        simpa [hullFiveSequentialCycleSlot] using
          hcycleF.pos 0 2 3 (by decide) (by decide)
      have hACD : 0 < sig (v (f 0)) (v (f 3)) (v (f 4)) := by
        simpa [hullFiveSequentialCycleSlot] using
          hcycleF.pos 0 3 4 (by decide) (by decide)
      have harea := doubledHullArea_eq_endReindexFan_raw
        custody.hull h5 e hchart k inner
      have closeResult
          (hresult : HullFive300Cell v f ∨
            minTri v * 25 ≤ 2 *
              (sig (v (f 0)) (v (f 1)) (v (f 2)) +
                sig (v (f 0)) (v (f 2)) (v (f 3)) +
                sig (v (f 0)) (v (f 3)) (v (f 4)))) :
          25 * minTri v ≤ 2 * doubledHullArea v := by
        rcases hresult with hcell | hbound
        · cases hcell with
          | central hP hQ hR =>
              let sigma : Equiv.Perm (Fin 8) :=
                hullFiveOccupancyToSequential.trans f
              have hcycleSigma :
                  StrictCyclicPos hullFiveOccupancyCycleSlot
                    (fun i ↦ v (sigma i)) := by
                refine ⟨?_, ?_⟩
                · intro i j k hij hjk
                  simpa only [sigma, Equiv.trans_apply,
                    hullFiveOccupancyToSequential_hull] using
                      hcycleF.1 i j k hij hjk
                · intro i j k hij hjk
                  simpa only [sigma, Equiv.trans_apply,
                    hullFiveOccupancyToSequential_hull] using
                      hcycleF.2 i j k hij hjk
              have hbound' :=
                hullFive300_allCentral_relabel_forces_fan_bound
                  v sigma hmin hcycleSigma
                    (by simpa [sigma, hullFiveOccupancyToSequential] using hP)
                    (by simpa [sigma, hullFiveOccupancyToSequential] using hQ)
                    (by simpa [sigma, hullFiveOccupancyToSequential] using hR)
              apply twoTwentyFiveBound_of_fanBound_raw harea
              simpa [sigma, hullFiveOccupancyToSequential] using hbound'
          | right hP hQ hR =>
              rcases hrightRoute with himpossible | hprofiles
              · obtain ⟨i, hi⟩ := himpossible
                have hzero : InHullFiveFanCell
                    (v (e (hullFiveOccupancyInnerSlot (inner i))))
                    (fun j ↦ v (e (hullFiveOccupancyCycleSlot j)))
                    (k + 1) 0 := by
                  fin_cases i
                  · simpa [f, hullFiveEndReindex,
                      InHullFiveFanCell, InAnchoredFiveFanCell,
                      hullFiveRotate, hullFiveOccupancyCycleSlot,
                      hullFiveOccupancyInnerSlot,
                      hullFiveSequentialToOccupancy] using hP
                  · simpa [f, hullFiveEndReindex,
                      InHullFiveFanCell, InAnchoredFiveFanCell,
                      hullFiveRotate, hullFiveOccupancyCycleSlot,
                      hullFiveOccupancyInnerSlot,
                      hullFiveSequentialToOccupancy] using hQ
                  · simpa [f, hullFiveEndReindex,
                      InHullFiveFanCell, InAnchoredFiveFanCell,
                      hullFiveRotate, hullFiveOccupancyCycleSlot,
                      hullFiveOccupancyInnerSlot,
                      hullFiveSequentialToOccupancy] using hR
                have hstrictFan : HullFiveStrictCyclic
                    (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) :=
                  hullFiveStrictCyclic_of_strictCyclicPos
                    (fun j ↦ v (e j)) hullFiveOccupancyCycleSlot
                    hbaseCycle
                have heq := hullFiveFanCell_eq_zero_of_mem_zero
                  hstrictFan (k + 1)
                    ((regions (inner i)).fanCell (k + 1))
                    hzero (hmem (inner i) (k + 1))
                exact (hi heq).elim
              · cases major with
                | first =>
                    rcases hprofiles with ⟨hpC, hqC, hrA⟩
                    have hp := endRightProfileC_of_fullProfile_raw
                      v e regions hmem k inner 0 hpC
                    have hq := endRightProfileC_of_fullProfile_raw
                      v e regions hmem k inner 1 hqC
                    have hr := endRightProfileA_of_fullProfile_raw
                      v e regions hmem k inner 2 hrA
                    have hpacket : HullFive300RightProfilePacket v f :=
                      .cca
                        (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                        (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                        (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                    exact twoTwentyFiveBound_of_fanBound_raw harea
                      (hRight300 v f hmin hcycleF hpacket)
                | middle =>
                    rcases hprofiles with ⟨hrC, hpq⟩
                    have hr := endRightProfileC_of_fullProfile_raw
                      v e regions hmem k inner 2 hrC
                    rcases hpq with hpq | hpq | hpq
                    · have hp := endRightProfileA_of_fullProfile_raw
                        v e regions hmem k inner 0 hpq.1
                      have hq := endRightProfileA_of_fullProfile_raw
                        v e regions hmem k inner 1 hpq.2
                      have hpacket : HullFive300RightProfilePacket v f :=
                        .caa
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                      exact twoTwentyFiveBound_of_fanBound_raw harea
                        (hRight300 v f hmin hcycleF hpacket)
                    · have hp := endRightProfileA_of_fullProfile_raw
                        v e regions hmem k inner 0 hpq.1
                      have hq := endRightProfileB_of_fullProfile_raw
                        v e regions hmem k inner 1 hpq.2
                      have hpacket : HullFive300RightProfilePacket v f :=
                        .cab
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                      exact twoTwentyFiveBound_of_fanBound_raw harea
                        (hRight300 v f hmin hcycleF hpacket)
                    · have hp := endRightProfileB_of_fullProfile_raw
                        v e regions hmem k inner 0 hpq.1
                      have hq := endRightProfileA_of_fullProfile_raw
                        v e regions hmem k inner 1 hpq.2
                      have hpacket : HullFive300RightProfilePacket v f :=
                        .cba
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                      exact twoTwentyFiveBound_of_fanBound_raw harea
                        (hRight300 v f hmin hcycleF hpacket)
        · exact twoTwentyFiveBound_of_fanBound_raw harea hbound
      cases major with
      | first =>
          rcases hroute with ⟨hpCell, hqCell, hrCell⟩
          have hpRaw := selectedProfileMem_raw v e regions hmem
            inner 0 k 0 hpCell
          have hqRaw := selectedProfileMem_raw v e regions hmem
            inner 1 k 0 hqCell
          have hrRaw := selectedProfileMem_raw v e regions hmem
            inner 2 k 1 hrCell
          apply closeResult
          apply hullFive_endZero_ax_major_dispatch_210_minTri_reindex
            v f f.injective hmin hABC hBXC hABX hAXC hACD
          · simpa [f, hullFiveEndReindex, InHullFiveFanCell,
              InAnchoredFiveFanCell, hullFiveRotate,
              hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
              hullFiveSequentialToOccupancy] using hpRaw
          · simpa [f, hullFiveEndReindex, InHullFiveFanCell,
              InAnchoredFiveFanCell, hullFiveRotate,
              hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
              hullFiveSequentialToOccupancy] using hqRaw
          · simpa [f, hullFiveEndReindex, InHullFiveFanCell,
              InAnchoredFiveFanCell, hullFiveRotate,
              hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
              hullFiveSequentialToOccupancy] using hrRaw
      | middle =>
          rcases hroute with ⟨hpCell, hqCell, hrCell⟩
          have hpRaw := selectedProfileMem_raw v e regions hmem
            inner 0 k 1 hpCell
          have hqRaw := selectedProfileMem_raw v e regions hmem
            inner 1 k 1 hqCell
          have hrRaw := selectedProfileMem_raw v e regions hmem
            inner 2 k 0 hrCell
          apply closeResult
          apply hullFive_endZero_axc_major_dispatch_210_minTri_reindex
            v f f.injective hmin hABC hBXC hABX hAXC hACD
          · simpa [f, hullFiveEndReindex, InHullFiveFanCell,
              InAnchoredFiveFanCell, hullFiveRotate,
              hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
              hullFiveSequentialToOccupancy] using hpRaw
          · simpa [f, hullFiveEndReindex, InHullFiveFanCell,
              InAnchoredFiveFanCell, hullFiveRotate,
              hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
              hullFiveSequentialToOccupancy] using hqRaw
          · simpa [f, hullFiveEndReindex, InHullFiveFanCell,
              InAnchoredFiveFanCell, hullFiveRotate,
              hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
              hullFiveSequentialToOccupancy] using hrRaw
    · by_cases hmiddle : isMiddle
      · obtain ⟨k, inner, hroute⟩ :=
          hullFiveMiddleVZRoute_of_residual pRegion qRegion rRegion
            hcentral hend hmiddle
        have hpacket := hullFive111Packet_of_profileRoute
          v e hbaseCycle regions hmem k inner .vz (by simpa using hroute)
        exact
          hullFive111_reindexedPacket_forces_twoTwentyFiveBound_of_hullCycle
            custody.hull h5 e hchart k inner hmin hpacket
      · have h111 : ∀ anchor : Fin 5,
            (hullFiveRegionCounts pRegion qRegion rRegion anchor).Is111 := by
          rcases houtcome with hc | he | hm' | h111
          · exact False.elim (hcentral hc)
          · exact False.elim (hend he)
          · exact False.elim (hmiddle hm')
          · exact h111
        obtain ⟨k, inner, kind, hroute⟩ :=
          hullFive111Route_of_counts pRegion qRegion rRegion h111
        have hpacket := hullFive111Packet_of_profileRoute
          v e hbaseCycle regions hmem k inner kind hroute
        exact
          hullFive111_reindexedPacket_forces_twoTwentyFiveBound_of_hullCycle
            custody.hull h5 e hchart k inner hmin hpacket

/-- Concrete, import-neutral H5 provider for the equality router. -/
theorem geometricHullFive_twoTwentyFiveBound
    {v : Configuration} (custody : GeometricHullCustody v)
    (hmin : 0 < minTri v)
    (h5 : custody.data.cycle.length = 5) :
    25 * minTri v ≤ 2 * doubledHullArea v :=
  geometricHullFive_twoTwentyFiveBound_of_rightEar300
    hullFive300_rightProfile_universal_bound custody hmin h5

#print axioms hullFive111_reindexedPacket_forces_twoTwentyFiveBound_of_hullCycle
#print axioms geometricHullFive_twoTwentyFiveBound_of_rightEar300
#print axioms geometricHullFive_twoTwentyFiveBound

end Heilbronn8.TriHull
