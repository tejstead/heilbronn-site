import Heilbronn8.GeometricHullExclusionCore
import Heilbronn8.OrderDensity
import Heilbronn8.TriHull.HullFiveOccupancy111Adapter
import Heilbronn8.TriHull.HullFive210MaxFreeHomogeneous
import Heilbronn8.TriHull.HullFive300UniversalCentral

/-!
# Direct geometric hull-five exclusion

This file joins the kernel-finite eleven-region classifier to the compact
`300`, end-zero `210`, and UZ/VZ metric endpoints.  The sole remaining
metric input is stated explicitly: the right-ear `300` residual returned by
the maximality-free end-zero theorem.  Once that endpoint is supplied, no
retained word, survivor record, RootCover hypothesis, or generated
certificate occurs in the hull-five route.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8
namespace TriHull

/-- Sequential slots for a pentagon displayed as `A-B-X-C-D`. -/
def hullFiveSequentialCycleSlot : Fin 5 → Fin 8 := ![0, 1, 2, 3, 4]

/-- Convert sequential slots `A,B,X,C,D,P,Q,R` to the occupancy/packet
slots `A,B,C,D,X,P,Q,R`. -/
noncomputable def hullFiveSequentialToOccupancy : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 4, 2, 3, 5, 6, 7] (by decide)

/-- The inverse slot conversion, from packet slots to sequential slots. -/
noncomputable def hullFiveOccupancyToSequential : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 3, 4, 2, 5, 6, 7] (by decide)

@[simp] lemma hullFiveSequentialToOccupancy_apply (i : Fin 8) :
    hullFiveSequentialToOccupancy i = ![0, 1, 4, 2, 3, 5, 6, 7] i := by
  fin_cases i <;> rfl

@[simp] lemma hullFiveSequentialToOccupancy_zero :
    hullFiveSequentialToOccupancy (0 : Fin 8) = 0 := by
  rfl

@[simp] lemma hullFiveSequentialToOccupancy_one :
    hullFiveSequentialToOccupancy (1 : Fin 8) = 1 := by
  rfl

@[simp] lemma hullFiveSequentialToOccupancy_two :
    hullFiveSequentialToOccupancy (2 : Fin 8) = 4 := by
  rfl

@[simp] lemma hullFiveSequentialToOccupancy_three :
    hullFiveSequentialToOccupancy (3 : Fin 8) = 2 := by
  rfl

@[simp] lemma hullFiveSequentialToOccupancy_four :
    hullFiveSequentialToOccupancy (4 : Fin 8) = 3 := by
  rfl

@[simp] lemma hullFiveSequentialToOccupancy_inner (i : Fin 3) :
    hullFiveSequentialToOccupancy (hullFiveOccupancyInnerSlot i) =
      hullFiveOccupancyInnerSlot i := by
  fin_cases i <;> rfl

@[simp] lemma hullFiveOccupancyToSequential_apply (i : Fin 8) :
    hullFiveOccupancyToSequential i = ![0, 1, 3, 4, 2, 5, 6, 7] i := by
  fin_cases i <;> rfl

@[simp] lemma hullFiveOccupancyToSequential_hull (i : Fin 5) :
    hullFiveOccupancyToSequential (hullFiveOccupancyCycleSlot i) =
      hullFiveSequentialCycleSlot i := by
  fin_cases i <;> rfl

@[simp] private lemma finFive_add_two_add_one (k : Fin 5) :
    (k + 2) + 1 = k + 3 := by
  fin_cases k <;> decide

@[simp] private lemma finFive_add_two_add_two (k : Fin 5) :
    (k + 2) + 2 = k + 4 := by
  fin_cases k <;> decide

@[simp] private lemma finFive_add_two_add_three (k : Fin 5) :
    (k + 2) + 3 = k := by
  fin_cases k <;> decide

@[simp] private lemma finFive_add_four_add_three (k : Fin 5) :
    (k + 4) + 3 = k + 2 := by
  fin_cases k <;> decide

/-- Rotate an occupancy chart, reorder its three inner points, and expose
the result in the sequential convention required by the end-zero theorem. -/
noncomputable def hullFiveEndReindex
    (e : Equiv.Perm (Fin 8)) (shift : Fin 5)
    (inner : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 8) :=
  hullFiveSequentialToOccupancy.trans
    ((hullFiveOccupancyReindex shift inner).trans e)

@[simp] lemma hullFiveEndReindex_hull
    (e : Equiv.Perm (Fin 8)) (shift : Fin 5)
    (inner : Equiv.Perm (Fin 3)) (i : Fin 5) :
    hullFiveEndReindex e shift inner
        (hullFiveSequentialCycleSlot i) =
      e (hullFiveOccupancyReindex shift inner
        (hullFiveOccupancyCycleSlot i)) := by
  fin_cases i <;> rfl

@[simp] lemma hullFiveEndReindex_inner
    (e : Equiv.Perm (Fin 8)) (shift : Fin 5)
    (inner : Equiv.Perm (Fin 3)) (i : Fin 3) :
    hullFiveEndReindex e shift inner
        (hullFiveOccupancyInnerSlot i) =
      e (hullFiveOccupancyReindex shift inner
        (hullFiveOccupancyInnerSlot i)) := by
  fin_cases i <;> rfl

lemma strictCyclicPos_hullFiveEndReindex
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hcyc : StrictCyclicPos hullFiveOccupancyCycleSlot
      (fun i ↦ v (e i)))
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (hullFiveEndReindex e shift inner i)) := by
  have h := strictCyclicPos_hullFiveOccupancyReindex
    (fun i ↦ v (e i)) hcyc shift inner
  refine ⟨?_, ?_⟩
  · intro i j k hij hjk
    simpa only [hullFiveEndReindex_hull] using h.1 i j k hij hjk
  · intro i j k hij hjk
    simpa only [hullFiveEndReindex_hull] using h.2 i j k hij hjk

/-- Full useful memberships of the residual profile
`A = [1,0,0,2,2]`. -/
structure HullFiveEndRightProfileA
    (v : Configuration) (e : Fin 8 → Fin 8) (p : Fin 8) : Prop where
  axc : InTriStrict (v (e p)) (v (e 0)) (v (e 2)) (v (e 3))
  bxc : InTriStrict (v (e p)) (v (e 1)) (v (e 2)) (v (e 3))
  xcd : InTriStrict (v (e p)) (v (e 2)) (v (e 3)) (v (e 4))

/-- Full useful memberships of the residual profile
`B = [1,0,1,2,1]`. -/
structure HullFiveEndRightProfileB
    (v : Configuration) (e : Fin 8 → Fin 8) (p : Fin 8) : Prop where
  axc : InTriStrict (v (e p)) (v (e 0)) (v (e 2)) (v (e 3))
  bxc : InTriStrict (v (e p)) (v (e 1)) (v (e 2)) (v (e 3))
  xda : InTriStrict (v (e p)) (v (e 2)) (v (e 4)) (v (e 0))
  dbx : InTriStrict (v (e p)) (v (e 4)) (v (e 1)) (v (e 2))

/-- Full useful memberships of the residual profile
`C = [0,0,2,2,1]`. -/
structure HullFiveEndRightProfileC
    (v : Configuration) (e : Fin 8 → Fin 8) (p : Fin 8) : Prop where
  abx : InTriStrict (v (e p)) (v (e 0)) (v (e 1)) (v (e 2))
  bxc : InTriStrict (v (e p)) (v (e 1)) (v (e 2)) (v (e 3))
  dbx : InTriStrict (v (e p)) (v (e 4)) (v (e 1)) (v (e 2))

/-- The exact three residual multisets, with both CAB endpoint orders kept
explicit. -/
inductive HullFive300RightProfilePacket
    (v : Configuration) (e : Fin 8 → Fin 8) : Prop
  | cca
      (p : HullFiveEndRightProfileC v e 5)
      (q : HullFiveEndRightProfileC v e 6)
      (r : HullFiveEndRightProfileA v e 7)
  | caa
      (p : HullFiveEndRightProfileA v e 5)
      (q : HullFiveEndRightProfileA v e 6)
      (r : HullFiveEndRightProfileC v e 7)
  | cab
      (p : HullFiveEndRightProfileA v e 5)
      (q : HullFiveEndRightProfileB v e 6)
      (r : HullFiveEndRightProfileC v e 7)
  | cba
      (p : HullFiveEndRightProfileB v e 5)
      (q : HullFiveEndRightProfileA v e 6)
      (r : HullFiveEndRightProfileC v e 7)

/-- The sole remaining metric input, narrowed to the exact full-profile
right-ear packets `CCA`, `CAA`, and `CAB`. -/
def HullFive300RightProfileUniversalBound : Prop :=
  ∀ (v : Configuration) (e : Equiv.Perm (Fin 8)),
    0 < minTri v →
    StrictCyclicPos hullFiveSequentialCycleSlot (fun i ↦ v (e i)) →
    HullFive300RightProfilePacket v e →
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4)))

private lemma doubledHullArea_eq_reindexedOccupancyFan
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

private lemma doubledHullArea_eq_endReindexFan
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
  have harea := doubledHullArea_eq_reindexedOccupancyFan
    hcycle h5 e hchart shift inner
  simpa only [f, hullFiveEndReindex,
    hullFiveSequentialToOccupancy_zero,
    hullFiveSequentialToOccupancy_one,
    hullFiveSequentialToOccupancy_two,
    hullFiveSequentialToOccupancy_three,
    hullFiveSequentialToOccupancy_four, Equiv.trans_apply] using harea

private lemma false_of_hullFiveFanBound
    {v : Configuration} {H : ℝ}
    (harea : doubledHullArea v = H)
    (hbound : minTri v * 25 ≤ 2 * H)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  have hq : (2 / 25 : ℝ) < v8 :=
    lt_trans (by norm_num) v8_lb
  have hcut : (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    (mul_lt_mul_of_pos_right hq hbeat.1).trans hbeat.2
  rw [harea] at hcut
  nlinarith

private lemma selectedProfileMem
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

private lemma endRightProfileA_of_fullProfile
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
  have hm0 := selectedProfileMem v e regions hmem inner i k 1 h0
  have hm1 := selectedProfileMem v e regions hmem inner i (k + 1) 0 h1
  have hm2 := selectedProfileMem v e regions hmem inner i (k + 2) 0 h2
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

private lemma endRightProfileB_of_fullProfile
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
  have hm0 := selectedProfileMem v e regions hmem inner i k 1 h0
  have hm1 := selectedProfileMem v e regions hmem inner i (k + 1) 0 h1
  have hm2 := selectedProfileMem v e regions hmem inner i (k + 2) 1 h2
  have hm4 := selectedProfileMem v e regions hmem inner i (k + 4) 1 h4
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

private lemma endRightProfileC_of_fullProfile
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
  have hm0 := selectedProfileMem v e regions hmem inner i k 0 h0
  have hm1 := selectedProfileMem v e regions hmem inner i (k + 1) 0 h1
  have hm4 := selectedProfileMem v e regions hmem inner i (k + 4) 1 h4
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

/-- Conditional direct hull-five endpoint.  Its hypothesis is exactly the
right-ear H300 residue left by the otherwise complete compact dispatcher. -/
theorem geometricHullFiveExclusion_of_rightEar300
    (hRight300 : HullFive300RightProfileUniversalBound) :
    GeometricHullSizeExclusion 5 StrictXOrder := by
  intro v custody _hdomain _hstrict h5 hbeat
  have hm : 0 < minTri v :=
    (mul_pos v8_pos hbeat.1).trans hbeat.2
  have hsigns : AllTripleSignsStrict v :=
    allTripleSignsStrict_of_minTri_pos v hm
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
        finFive_add_two_add_one, finFive_add_two_add_three] using hpRaw
    have hqABC : InTriStrict (v (sigma 6))
        (v (sigma 0)) (v (sigma 1)) (v (sigma 2)) := by
      apply inTriStrict_rotate_hullFive
      simpa [regions, hullFiveRegionTriple, hqCell, sigma, shift, innerId,
        InHullFiveFanCell, InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        finFive_add_two_add_one, finFive_add_two_add_three] using hqRaw
    have hrABC : InTriStrict (v (sigma 7))
        (v (sigma 0)) (v (sigma 1)) (v (sigma 2)) := by
      apply inTriStrict_rotate_hullFive
      simpa [regions, hullFiveRegionTriple, hrCell, sigma, shift, innerId,
        InHullFiveFanCell, InAnchoredFiveFanCell, hullFiveRotate,
        hullFiveOccupancyCycleSlot, hullFiveOccupancyInnerSlot,
        finFive_add_two_add_one, finFive_add_two_add_three] using hrRaw
    have hbound := hullFive300_allCentral_relabel_forces_fan_bound
      v sigma hm hcycleSigma hpABC hqABC hrABC
    have harea := doubledHullArea_eq_reindexedOccupancyFan
      custody.hull h5 e hchart shift innerId
    exact false_of_hullFiveFanBound harea hbound hbeat
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
      have harea := doubledHullArea_eq_endReindexFan
        custody.hull h5 e hchart k inner
      have closeResult
          (hresult : HullFive300Cell v f ∨
            minTri v * 25 ≤ 2 *
              (sig (v (f 0)) (v (f 1)) (v (f 2)) +
                sig (v (f 0)) (v (f 2)) (v (f 3)) +
                sig (v (f 0)) (v (f 3)) (v (f 4)))) : False := by
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
              have hbound :=
                hullFive300_allCentral_relabel_forces_fan_bound
                  v sigma hm hcycleSigma
                    (by simpa [sigma, hullFiveOccupancyToSequential] using hP)
                    (by simpa [sigma, hullFiveOccupancyToSequential] using hQ)
                    (by simpa [sigma, hullFiveOccupancyToSequential] using hR)
              apply false_of_hullFiveFanBound harea _ hbeat
              simpa [sigma, hullFiveOccupancyToSequential] using hbound
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
                    have hp := endRightProfileC_of_fullProfile
                      v e regions hmem k inner 0 hpC
                    have hq := endRightProfileC_of_fullProfile
                      v e regions hmem k inner 1 hqC
                    have hr := endRightProfileA_of_fullProfile
                      v e regions hmem k inner 2 hrA
                    have hpacket : HullFive300RightProfilePacket v f :=
                      .cca
                        (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                        (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                        (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                    exact false_of_hullFiveFanBound harea
                      (hRight300 v f hm hcycleF hpacket) hbeat
                | middle =>
                    rcases hprofiles with ⟨hrC, hpq⟩
                    have hr := endRightProfileC_of_fullProfile
                      v e regions hmem k inner 2 hrC
                    rcases hpq with hpq | hpq | hpq
                    · have hp := endRightProfileA_of_fullProfile
                        v e regions hmem k inner 0 hpq.1
                      have hq := endRightProfileA_of_fullProfile
                        v e regions hmem k inner 1 hpq.2
                      have hpacket : HullFive300RightProfilePacket v f :=
                        .caa
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                      exact false_of_hullFiveFanBound harea
                        (hRight300 v f hm hcycleF hpacket) hbeat
                    · have hp := endRightProfileA_of_fullProfile
                        v e regions hmem k inner 0 hpq.1
                      have hq := endRightProfileB_of_fullProfile
                        v e regions hmem k inner 1 hpq.2
                      have hpacket : HullFive300RightProfilePacket v f :=
                        .cab
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                      exact false_of_hullFiveFanBound harea
                        (hRight300 v f hm hcycleF hpacket) hbeat
                    · have hp := endRightProfileB_of_fullProfile
                        v e regions hmem k inner 0 hpq.1
                      have hq := endRightProfileA_of_fullProfile
                        v e regions hmem k inner 1 hpq.2
                      have hpacket : HullFive300RightProfilePacket v f :=
                        .cba
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hp)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hq)
                          (by simpa [f, hullFiveOccupancyInnerSlot] using hr)
                      exact false_of_hullFiveFanBound harea
                        (hRight300 v f hm hcycleF hpacket) hbeat
        · exact false_of_hullFiveFanBound harea hbound hbeat
      cases major with
      | first =>
          rcases hroute with ⟨hpCell, hqCell, hrCell⟩
          have hpRaw := selectedProfileMem v e regions hmem
            inner 0 k 0 hpCell
          have hqRaw := selectedProfileMem v e regions hmem
            inner 1 k 0 hqCell
          have hrRaw := selectedProfileMem v e regions hmem
            inner 2 k 1 hrCell
          apply closeResult
          apply hullFive_endZero_ax_major_dispatch_210_minTri_reindex
            v f f.injective hm hABC hBXC hABX hAXC hACD
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
          have hpRaw := selectedProfileMem v e regions hmem
            inner 0 k 1 hpCell
          have hqRaw := selectedProfileMem v e regions hmem
            inner 1 k 1 hqCell
          have hrRaw := selectedProfileMem v e regions hmem
            inner 2 k 0 hrCell
          apply closeResult
          apply hullFive_endZero_axc_major_dispatch_210_minTri_reindex
            v f f.injective hm hABC hBXC hABX hAXC hACD
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
        exact (hullFive111_reindexedPacket_not_beats_of_hullCycle
          custody.hull h5 e hchart k inner hpacket) hbeat
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
        exact (hullFive111_reindexedPacket_not_beats_of_hullCycle
          custody.hull h5 e hchart k inner hpacket) hbeat

#print axioms geometricHullFiveExclusion_of_rightEar300

end TriHull
end Heilbronn8
