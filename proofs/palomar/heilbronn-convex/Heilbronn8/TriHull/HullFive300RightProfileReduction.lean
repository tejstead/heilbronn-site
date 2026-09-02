import Heilbronn8.TriHull.HullFive300RightProfiles

/-!
# Reduction of the right-ear hull-five residue to one CAB orientation

The compact area arguments close the exact `CCA` and `CAA` profiles.  The
two ordered versions of `CAB` differ only by swapping the first two inner
slots, so a theorem for `A@5, B@6, C@7` supplies both.  This leaves a single
honest metric interface for the direct geometric hull-five exclusion.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The remaining right-ear endpoint in one fixed ordering. -/
def HullFive300CABUniversalBound : Prop :=
  ∀ (v : Configuration) (e : Equiv.Perm (Fin 8)),
    0 < minTri v →
    StrictCyclicPos hullFiveSequentialCycleSlot (fun i ↦ v (e i)) →
    HullFiveEndRightProfileA v e 5 →
    HullFiveEndRightProfileB v e 6 →
    HullFiveEndRightProfileC v e 7 →
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4)))

/-- Swap only the first two inner slots of the sequential chart. -/
noncomputable def hullFiveSwapInner56 : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 2, 3, 4, 6, 5, 7] (by decide)

@[simp] lemma hullFiveSwapInner56_hull (i : Fin 5) :
    hullFiveSwapInner56 (hullFiveSequentialCycleSlot i) =
      hullFiveSequentialCycleSlot i := by
  fin_cases i <;> rfl

@[simp] lemma hullFiveSwapInner56_zero : hullFiveSwapInner56 0 = 0 := rfl
@[simp] lemma hullFiveSwapInner56_one : hullFiveSwapInner56 1 = 1 := rfl
@[simp] lemma hullFiveSwapInner56_two : hullFiveSwapInner56 2 = 2 := rfl
@[simp] lemma hullFiveSwapInner56_three : hullFiveSwapInner56 3 = 3 := rfl
@[simp] lemma hullFiveSwapInner56_four : hullFiveSwapInner56 4 = 4 := rfl
@[simp] lemma hullFiveSwapInner56_five : hullFiveSwapInner56 5 = 6 := rfl
@[simp] lemma hullFiveSwapInner56_six : hullFiveSwapInner56 6 = 5 := rfl
@[simp] lemma hullFiveSwapInner56_seven : hullFiveSwapInner56 7 = 7 := rfl

/-- `CCA` and `CAA` are already compact area theorems; a single ordered
`CAB` endpoint supplies both `CAB` and `CBA`. -/
theorem hullFive300RightProfileUniversalBound_of_cab
    (hCAB : HullFive300CABUniversalBound) :
    HullFive300RightProfileUniversalBound := by
  intro v e hm hcyc packet
  cases packet with
  | cca p q r =>
      exact hullFive300_right_cca_packet_bound v e hm hcyc p q r
  | caa p q r =>
      exact hullFive300_right_caa_packet_bound v e hm hcyc p q r
  | cab p q r =>
      exact hCAB v e hm hcyc p q r
  | cba p q r =>
      let e' : Equiv.Perm (Fin 8) := hullFiveSwapInner56.trans e
      have hcyc' : StrictCyclicPos hullFiveSequentialCycleSlot
          (fun i ↦ v (e' i)) := by
        simpa only [StrictCyclicPos, CyclicPos, e', Equiv.trans_apply,
          hullFiveSwapInner56_hull] using hcyc
      have hp' : HullFiveEndRightProfileA v e' 5 := {
        axc := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_zero, hullFiveSwapInner56_two,
            hullFiveSwapInner56_three, hullFiveSwapInner56_five] using q.axc
        bxc := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_one, hullFiveSwapInner56_two,
            hullFiveSwapInner56_three, hullFiveSwapInner56_five] using q.bxc
        xcd := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_two, hullFiveSwapInner56_three,
            hullFiveSwapInner56_four, hullFiveSwapInner56_five] using q.xcd }
      have hq' : HullFiveEndRightProfileB v e' 6 := {
        axc := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_zero, hullFiveSwapInner56_two,
            hullFiveSwapInner56_three, hullFiveSwapInner56_six] using p.axc
        bxc := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_one, hullFiveSwapInner56_two,
            hullFiveSwapInner56_three, hullFiveSwapInner56_six] using p.bxc
        xda := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_zero, hullFiveSwapInner56_two,
            hullFiveSwapInner56_four, hullFiveSwapInner56_six] using p.xda
        dbx := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_one, hullFiveSwapInner56_two,
            hullFiveSwapInner56_four, hullFiveSwapInner56_six] using p.dbx }
      have hr' : HullFiveEndRightProfileC v e' 7 := {
        abx := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_zero, hullFiveSwapInner56_one,
            hullFiveSwapInner56_two, hullFiveSwapInner56_seven] using r.abx
        bxc := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_one, hullFiveSwapInner56_two,
            hullFiveSwapInner56_three, hullFiveSwapInner56_seven] using r.bxc
        dbx := by
          simpa only [e', Equiv.trans_apply,
            hullFiveSwapInner56_one, hullFiveSwapInner56_two,
            hullFiveSwapInner56_four, hullFiveSwapInner56_seven] using r.dbx }
      have hbound := hCAB v e' hm hcyc' hp' hq' hr'
      simpa only [e', Equiv.trans_apply,
        hullFiveSwapInner56_zero, hullFiveSwapInner56_one,
        hullFiveSwapInner56_two, hullFiveSwapInner56_three,
        hullFiveSwapInner56_four] using hbound

/-- The direct geometric hull-five exclusion now needs only the ordered
`CAB` endpoint. -/
theorem geometricHullFiveExclusion_of_cab
    (hCAB : HullFive300CABUniversalBound) :
    GeometricHullSizeExclusion 5 StrictXOrder :=
  geometricHullFiveExclusion_of_rightEar300
    (hullFive300RightProfileUniversalBound_of_cab hCAB)

#print axioms hullFive300RightProfileUniversalBound_of_cab
#print axioms geometricHullFiveExclusion_of_cab

end Heilbronn8.TriHull
