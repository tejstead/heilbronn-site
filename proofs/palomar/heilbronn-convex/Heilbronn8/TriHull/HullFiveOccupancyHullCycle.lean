import Heilbronn8.TriHull.HullFiveOccupancyGeometry
import Heilbronn8.HullCycleGeometric

/-!
# Hull-cycle adapter for the hull-five occupancy theorem

This file turns a semantic `HullCycleOf` certificate of length five into the
eleven-region witness used by the compact occupancy dispatcher.  It uses no
retained sign word: general position supplies line genericity, and the hull
fan cover supplies convex-hull containment.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Canonical slots for a cyclic pentagon chart `A-B-X-C-D`. -/
def hullFiveOccupancyCycleSlot : Fin 5 → Fin 8 := ![0, 1, 4, 2, 3]

/-- Canonical slots for its three off-cycle points. -/
def hullFiveOccupancyInnerSlot : Fin 3 → Fin 8 := ![5, 6, 7]

private theorem hullFiveOccupancyCycleSlot_injective :
    Function.Injective hullFiveOccupancyCycleSlot := by
  decide

private theorem hullFiveOccupancyInnerSlot_ne_cycleSlot
    (i : Fin 3) (j : Fin 5) :
    hullFiveOccupancyInnerSlot i ≠ hullFiveOccupancyCycleSlot j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Rotate the five hull slots while fixing the three inner slots. -/
noncomputable def hullFiveOccupancyCycleShift : Fin 5 → Equiv.Perm (Fin 8)
  | 0 => Equiv.ofBijective ![0, 1, 2, 3, 4, 5, 6, 7] (by decide)
  | 1 => Equiv.ofBijective ![1, 4, 3, 0, 2, 5, 6, 7] (by decide)
  | 2 => Equiv.ofBijective ![4, 2, 0, 1, 3, 5, 6, 7] (by decide)
  | 3 => Equiv.ofBijective ![2, 3, 1, 4, 0, 5, 6, 7] (by decide)
  | 4 => Equiv.ofBijective ![3, 0, 4, 2, 1, 5, 6, 7] (by decide)

@[simp] theorem hullFiveOccupancyCycleShift_hull
    (a i : Fin 5) :
    hullFiveOccupancyCycleShift a (hullFiveOccupancyCycleSlot i) =
      hullFiveOccupancyCycleSlot (a + i) := by
  fin_cases a <;> fin_cases i <;> rfl

@[simp] theorem hullFiveOccupancyCycleShift_inner
    (a : Fin 5) (i : Fin 3) :
    hullFiveOccupancyCycleShift a (hullFiveOccupancyInnerSlot i) =
      hullFiveOccupancyInnerSlot i := by
  fin_cases a <;> fin_cases i <;> rfl

private def hullFiveOccupancyInnerEmbedding : Fin 3 ↪ Fin 8 :=
  ⟨hullFiveOccupancyInnerSlot, by decide⟩

/-- Lift a permutation of the three off-cycle points, fixing all hull
slots. -/
def hullFiveOccupancyInnerReindex
    (inner : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 8) :=
  inner.viaFintypeEmbedding hullFiveOccupancyInnerEmbedding

@[simp] theorem hullFiveOccupancyInnerReindex_inner
    (inner : Equiv.Perm (Fin 3)) (i : Fin 3) :
    hullFiveOccupancyInnerReindex inner
        (hullFiveOccupancyInnerSlot i) =
      hullFiveOccupancyInnerSlot (inner i) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image
    inner hullFiveOccupancyInnerEmbedding i

@[simp] theorem hullFiveOccupancyInnerReindex_hull
    (inner : Equiv.Perm (Fin 3)) (i : Fin 5) :
    hullFiveOccupancyInnerReindex inner
        (hullFiveOccupancyCycleSlot i) =
      hullFiveOccupancyCycleSlot i := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  intro hmem
  rcases hmem with ⟨j, hj⟩
  exact hullFiveOccupancyInnerSlot_ne_cycleSlot j i hj

/-- Simultaneously rotate the hull chart and reorder the inner points. -/
noncomputable def hullFiveOccupancyReindex
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    Equiv.Perm (Fin 8) :=
  (hullFiveOccupancyCycleShift shift).trans
    (hullFiveOccupancyInnerReindex inner)

@[simp] theorem hullFiveOccupancyReindex_hull
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) (i : Fin 5) :
    hullFiveOccupancyReindex shift inner
        (hullFiveOccupancyCycleSlot i) =
      hullFiveOccupancyCycleSlot (shift + i) := by
  simp [hullFiveOccupancyReindex]

@[simp] theorem hullFiveOccupancyReindex_inner
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) (i : Fin 3) :
    hullFiveOccupancyReindex shift inner
        (hullFiveOccupancyInnerSlot i) =
      hullFiveOccupancyInnerSlot (inner i) := by
  simp [hullFiveOccupancyReindex]

/-- Cyclic hull position is invariant under the five chart rotations and
under arbitrary reordering of the three inner slots. -/
theorem strictCyclicPos_hullFiveOccupancyReindex
    (v : Fin 8 → ℝ × ℝ)
    (hcyc : StrictCyclicPos hullFiveOccupancyCycleSlot v)
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    StrictCyclicPos hullFiveOccupancyCycleSlot
      (fun i ↦ v (hullFiveOccupancyReindex shift inner i)) := by
  have hpos : ∀ i j k : Fin 5, i < j → j < k →
      0 < sig
        (v (hullFiveOccupancyReindex shift inner
          (hullFiveOccupancyCycleSlot i)))
        (v (hullFiveOccupancyReindex shift inner
          (hullFiveOccupancyCycleSlot j)))
        (v (hullFiveOccupancyReindex shift inner
          (hullFiveOccupancyCycleSlot k))) := by
    intro i j k hij hjk
    simp only [hullFiveOccupancyReindex_hull]
    fin_cases shift <;> fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals simp at hij hjk ⊢
    all_goals first
      | exact hcyc.pos _ _ _ (by decide) (by decide)
      | rw [sig_rotate]
        exact hcyc.pos _ _ _ (by decide) (by decide)
      | rw [sig_rotate, sig_rotate]
        exact hcyc.pos _ _ _ (by decide) (by decide)
  refine ⟨?_, fun i j k hij hjk ↦ (hpos i j k hij hjk).ne'⟩
  intro i j k hij hjk
  exact (hpos i j k hij hjk).le

/-- Extend the displayed five-cycle to a permutation of all eight labels. -/
noncomputable def extendHullFiveOccupancyCycle
    (cycle : Fin 5 → Fin 8) (hcycle : Function.Injective cycle) :
    Equiv.Perm (Fin 8) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    hullFiveOccupancyCycleSlot cycle
    hullFiveOccupancyCycleSlot_injective hcycle)

@[simp] theorem extendHullFiveOccupancyCycle_hull
    (cycle : Fin 5 → Fin 8) (hcycle : Function.Injective cycle)
    (i : Fin 5) :
    extendHullFiveOccupancyCycle cycle hcycle
        (hullFiveOccupancyCycleSlot i) = cycle i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    hullFiveOccupancyCycleSlot cycle
    hullFiveOccupancyCycleSlot_injective hcycle) i

lemma hullFiveStrictCyclic_of_strictCyclicPos
    (v : Fin 8 → ℝ × ℝ) (c : Fin 5 → Fin 8)
    (hcyc : StrictCyclicPos c v) :
    HullFiveStrictCyclic (fun i ↦ v (c i)) := by
  intro a i j hi hij
  fin_cases a <;> fin_cases i <;> fin_cases j
  all_goals simp [hullFiveRotate] at hi hij ⊢
  all_goals first
    | exact hcyc.pos _ _ _ (by decide) (by decide)
    | rw [sig_rotate]
      exact hcyc.pos _ _ _ (by decide) (by decide)
    | rw [sig_rotate, sig_rotate]
      exact hcyc.pos _ _ _ (by decide) (by decide)

private lemma hullFiveLineGeneric_of_strict
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v)
    (c : Fin 5 → Fin 8) (hc : Function.Injective c)
    (p : Fin 8) (hpOutside : p ∉ Set.range c) :
    HullFivePointLineGeneric (v p) (fun i ↦ v (c i)) := by
  have hsig (i j : Fin 5) (hij : i ≠ j) :
      sig (v (c i)) (v (c j)) (v p) ≠ 0 := by
    have hip : c i ≠ p := by
      intro h
      exact hpOutside ⟨i, h⟩
    have hjp : c j ≠ p := by
      intro h
      exact hpOutside ⟨j, h⟩
    exact hstrict.sig_ne_of_pairwise_ne (hc.ne hij) hip hjp
  intro a
  fin_cases a
  all_goals simp only [hullFiveRotate]
  all_goals exact
    ⟨hsig _ _ (by decide), hsig _ _ (by decide),
      hsig _ _ (by decide), hsig _ _ (by decide),
      hsig _ _ (by decide), hsig _ _ (by decide),
      hsig _ _ (by decide)⟩

private lemma mem_cycleHull_of_fanCovers
    (v : Fin 8 → ℝ × ℝ) (c : Fin 5 → Fin 8)
    (hfan : FanCovers v c) (p : Fin 8)
    (hpOutside : p ∉ Set.range c) :
    v p ∈ convexHull ℝ (Set.range (fun i ↦ v (c i))) := by
  obtain ⟨i, j, hi, hij, hp⟩ := hfan p hpOutside
  have hp' : v p ∈
      convexHull ℝ {v (c 0), v (c i), v (c j)} :=
    (inTri_iff_mem_convexHull _ _ _ _).1 hp
  apply (convexHull_mono (s := {v (c 0), v (c i), v (c j)})
    (t := Set.range (fun k ↦ v (c k))) ?_) hp'
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨i, rfl⟩
  · exact ⟨j, rfl⟩

/-- A generic labelled point strictly inside a strict five-cycle has one of
the eleven exact five-anchor fan profiles. -/
theorem hullFivePointRegion_of_strictCycle
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v)
    (c : Fin 5 → Fin 8) (hc : Function.Injective c)
    (hcyc : StrictCyclicPos c v) (hfan : FanCovers v c)
    (p : Fin 8) (hpOutside : p ∉ Set.range c) :
    ∃ region : HullFivePointRegion,
      ∀ anchor : Fin 5,
        InHullFiveFanCell (v p) (fun i ↦ v (c i)) anchor
          (region.fanCell anchor) := by
  have hcyc' := hullFiveStrictCyclic_of_strictCyclicPos v c hcyc
  have hpHull := mem_cycleHull_of_fanCovers v c hfan p hpOutside
  have hgeneric := hullFiveLineGeneric_of_strict
    v hstrict c hc p hpOutside
  exact hullFivePointRegion_of_strictInterior hcyc'
    (hullFivePointStrictInterior_of_mem_convexHull
      hcyc' hpHull hgeneric)

/-- Direct `HullCycleOf` interface at hull size five. -/
theorem hullFivePointRegion_of_hullCycleOf
    {v : Configuration} (hstrict : AllTripleSignsStrict v)
    {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (p : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h5)) :
    ∃ region : HullFivePointRegion,
      ∀ anchor : Fin 5,
        InHullFiveFanCell (v p)
          (fun i ↦ v (d.castGet h5 i)) anchor
          (region.fanCell anchor) := by
  exact hullFivePointRegion_of_strictCycle v hstrict
    (d.castGet h5)
    (HullCycleData.castGet_injective d h5 hcycle.nodup)
    (HullCycleData.strictCyclicPos_cast d h5 hcycle.strictCyclicPos)
    (HullCycleData.fanCovers_cast d h5 hcycle.fanCovers)
    p hpOutside

/-- Complete geometric-to-finite topology bridge for the three off-cycle
points of a hull-five configuration.  The outcome is exactly central `300`,
end-zero `210`, middle-zero `210`, or all-anchor `111`; there is no fifth
occupancy case. -/
theorem hullFiveThreePointProfiles_of_hullCycleOf
    {v : Configuration} (hstrict : AllTripleSignsStrict v)
    {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (P Q R : Fin 8)
    (hPOutside : P ∉ Set.range (d.castGet h5))
    (hQOutside : Q ∉ Set.range (d.castGet h5))
    (hROutside : R ∉ Set.range (d.castGet h5)) :
    ∃ pRegion qRegion rRegion : HullFivePointRegion,
      HullFiveRegionTripleOutcome pRegion qRegion rRegion ∧
      (∀ anchor : Fin 5,
        InHullFiveFanCell (v P)
          (fun i ↦ v (d.castGet h5 i)) anchor
          (pRegion.fanCell anchor)) ∧
      (∀ anchor : Fin 5,
        InHullFiveFanCell (v Q)
          (fun i ↦ v (d.castGet h5 i)) anchor
          (qRegion.fanCell anchor)) ∧
      (∀ anchor : Fin 5,
        InHullFiveFanCell (v R)
          (fun i ↦ v (d.castGet h5 i)) anchor
          (rRegion.fanCell anchor)) := by
  obtain ⟨pRegion, hP⟩ := hullFivePointRegion_of_hullCycleOf
    hstrict hcycle h5 P hPOutside
  obtain ⟨qRegion, hQ⟩ := hullFivePointRegion_of_hullCycleOf
    hstrict hcycle h5 Q hQOutside
  obtain ⟨rRegion, hR⟩ := hullFivePointRegion_of_hullCycleOf
    hstrict hcycle h5 R hROutside
  exact ⟨pRegion, qRegion, rRegion,
    hullFivePointRegions_outcome pRegion qRegion rRegion,
    hP, hQ, hR⟩

/-- Relabel a genuine hull-five custody into the canonical five hull slots
and three off-cycle slots, while retaining the exact finite region outcome.
This is the universal topology packet consumed by the metric dispatcher. -/
theorem hullFiveThreePointProfiles_relabel_of_hullCycleOf
    {v : Configuration} (hstrict : AllTripleSignsStrict v)
    {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5) :
    ∃ e : Equiv.Perm (Fin 8),
      ∃ pRegion qRegion rRegion : HullFivePointRegion,
        (∀ i : Fin 5,
          e (hullFiveOccupancyCycleSlot i) = d.castGet h5 i) ∧
        HullFiveRegionTripleOutcome pRegion qRegion rRegion ∧
        (∀ anchor : Fin 5,
          InHullFiveFanCell (v (e 5))
            (fun i ↦ v (d.castGet h5 i)) anchor
            (pRegion.fanCell anchor)) ∧
        (∀ anchor : Fin 5,
          InHullFiveFanCell (v (e 6))
            (fun i ↦ v (d.castGet h5 i)) anchor
            (qRegion.fanCell anchor)) ∧
        (∀ anchor : Fin 5,
          InHullFiveFanCell (v (e 7))
            (fun i ↦ v (d.castGet h5 i)) anchor
            (rRegion.fanCell anchor)) := by
  let c : Fin 5 → Fin 8 := d.castGet h5
  have hc : Function.Injective c :=
    HullCycleData.castGet_injective d h5 hcycle.nodup
  let e : Equiv.Perm (Fin 8) := extendHullFiveOccupancyCycle c hc
  have heHull (i : Fin 5) :
      e (hullFiveOccupancyCycleSlot i) = c i := by
    simpa only [e] using extendHullFiveOccupancyCycle_hull c hc i
  have hinnerOutside (i : Fin 3) :
      e (hullFiveOccupancyInnerSlot i) ∉ Set.range c := by
    rintro ⟨j, hj⟩
    have hne := e.injective.ne
      (hullFiveOccupancyInnerSlot_ne_cycleSlot i j)
    rw [heHull j] at hne
    exact hne hj.symm
  have hPOutside : e 5 ∉ Set.range c := by
    simpa [hullFiveOccupancyInnerSlot] using hinnerOutside 0
  have hQOutside : e 6 ∉ Set.range c := by
    simpa [hullFiveOccupancyInnerSlot] using hinnerOutside 1
  have hROutside : e 7 ∉ Set.range c := by
    simpa [hullFiveOccupancyInnerSlot] using hinnerOutside 2
  obtain ⟨pRegion, qRegion, rRegion, houtcome, hP, hQ, hR⟩ :=
    hullFiveThreePointProfiles_of_hullCycleOf hstrict hcycle h5
      (e 5) (e 6) (e 7) hPOutside hQOutside hROutside
  refine ⟨e, pRegion, qRegion, rRegion, ?_, houtcome, ?_, ?_, ?_⟩
  · intro i
    simpa only [c] using heHull i
  · simpa only [c] using hP
  · simpa only [c] using hQ
  · simpa only [c] using hR

#print axioms hullFivePointRegion_of_strictCycle
#print axioms hullFivePointRegion_of_hullCycleOf
#print axioms hullFiveThreePointProfiles_of_hullCycleOf
#print axioms hullFiveThreePointProfiles_relabel_of_hullCycleOf

end Heilbronn8.TriHull
