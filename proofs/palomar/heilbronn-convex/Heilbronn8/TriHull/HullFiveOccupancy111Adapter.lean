import Heilbronn8.TriHull.HullFiveOccupancyHullCycle
import Heilbronn8.TriHull.HullFiveOccupancyRoutes
import Heilbronn8.TriHull.HullFive111Packets

/-!
# Region-profile adapter for the compact hull-five `111` packets

The seven membership rows in each UZ/VZ packet are seven of the fifteen
standard fan cells seen across the five cyclic anchors.  This file performs
that reindexing once and for all.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-! Keep the raw canonical slot evaluations available to `simp`.  The
generic reindex lemmas are stated through `hullFiveOccupancyCycleSlot` and
`hullFiveOccupancyInnerSlot`, whereas packet structures expose the same
slots as the numerals `0, ..., 7`. -/

@[simp] private lemma hullFiveOccupancyReindex_zero
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 0 =
      hullFiveOccupancyCycleSlot k := by
  simpa only [show hullFiveOccupancyCycleSlot 0 = 0 by rfl,
    add_zero] using hullFiveOccupancyReindex_hull k inner 0

@[simp] private lemma hullFiveOccupancyReindex_one
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 1 =
      hullFiveOccupancyCycleSlot (k + 1) := by
  simpa only [show hullFiveOccupancyCycleSlot 1 = 1 by rfl] using
    hullFiveOccupancyReindex_hull k inner 1

@[simp] private lemma hullFiveOccupancyReindex_two
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 2 =
      hullFiveOccupancyCycleSlot (k + 3) := by
  simpa only [show hullFiveOccupancyCycleSlot 3 = 2 by rfl] using
    hullFiveOccupancyReindex_hull k inner 3

@[simp] private lemma hullFiveOccupancyReindex_three
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 3 =
      hullFiveOccupancyCycleSlot (k + 4) := by
  simpa only [show hullFiveOccupancyCycleSlot 4 = 3 by rfl] using
    hullFiveOccupancyReindex_hull k inner 4

@[simp] private lemma hullFiveOccupancyReindex_four
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 4 =
      hullFiveOccupancyCycleSlot (k + 2) := by
  simpa only [show hullFiveOccupancyCycleSlot 2 = 4 by rfl] using
    hullFiveOccupancyReindex_hull k inner 2

@[simp] private lemma hullFiveOccupancyReindex_five
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 5 =
      hullFiveOccupancyInnerSlot (inner 0) := by
  simpa only [show hullFiveOccupancyInnerSlot 0 = 5 by rfl] using
    hullFiveOccupancyReindex_inner k inner 0

@[simp] private lemma hullFiveOccupancyReindex_six
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 6 =
      hullFiveOccupancyInnerSlot (inner 1) := by
  simpa only [show hullFiveOccupancyInnerSlot 1 = 6 by rfl] using
    hullFiveOccupancyReindex_inner k inner 1

@[simp] private lemma hullFiveOccupancyReindex_seven
    (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    hullFiveOccupancyReindex k inner 7 =
      hullFiveOccupancyInnerSlot (inner 2) := by
  simpa only [show hullFiveOccupancyInnerSlot 2 = 7 by rfl] using
    hullFiveOccupancyReindex_inner k inner 2

/-! `hullFiveRotate` produces nested additions.  Normalize precisely the
offsets used by the seven packet triangles; these are equalities in the
additive group `Fin 5`, hence include wraparound at five. -/

@[simp] private lemma fin5_add_one_add_one (k : Fin 5) :
    (k + 1) + 1 = k + 2 := by
  fin_cases k <;> decide

@[simp] private lemma fin5_add_one_add_two (k : Fin 5) :
    (k + 1) + 2 = k + 3 := by
  fin_cases k <;> decide

@[simp] private lemma fin5_add_one_add_three (k : Fin 5) :
    (k + 1) + 3 = k + 4 := by
  fin_cases k <;> decide

@[simp] private lemma fin5_add_three_add_two (k : Fin 5) :
    (k + 3) + 2 = k := by
  fin_cases k <;> decide

@[simp] private lemma fin5_add_three_add_three (k : Fin 5) :
    (k + 3) + 3 = k + 1 := by
  fin_cases k <;> decide

@[simp] private lemma fin5_add_four_add_one (k : Fin 5) :
    (k + 4) + 1 = k := by
  fin_cases k <;> decide

@[simp] private lemma fin5_add_four_add_two (k : Fin 5) :
    (k + 4) + 2 = k + 1 := by
  fin_cases k <;> decide

private lemma positiveChart_of_strictCycle
    (v : Configuration) (e : Fin 8 → Fin 8)
    (hcyc : StrictCyclicPos hullFiveOccupancyCycleSlot
      (fun i ↦ v (e i))) :
    HullFive111PositiveChart v e := by
  have hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 4)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 0 1 2 (by decide) (by decide)
  have hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 0 1 3 (by decide) (by decide)
  have hABD : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 0 1 4 (by decide) (by decide)
  have hAXC : 0 < sig (v (e 0)) (v (e 4)) (v (e 2)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 0 2 3 (by decide) (by decide)
  have hBXC : 0 < sig (v (e 1)) (v (e 4)) (v (e 2)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 1 2 3 (by decide) (by decide)
  have hBCD : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 1 3 4 (by decide) (by decide)
  have hACD : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveOccupancyCycleSlot] using
      hcyc.pos 0 3 4 (by decide) (by decide)
  exact {
    abc_pos := hABC
    abx_pos := hABX
    axc_pos := hAXC
    bxc_pos := hBXC
    abd_pos := hABD
    bcd_pos := hBCD
    cda_pos := by
      rw [sig_rotate (v (e 2)) (v (e 3)) (v (e 0)),
        sig_rotate (v (e 3)) (v (e 0)) (v (e 2))]
      exact hACD }

/-- Turn a finite UZ/VZ profile route into the corresponding geometric
packet.  `regions` and `hmem` refer to the original inner-slot ordering;
`inner` chooses the packet ordering. -/
theorem hullFive111Packet_of_profileRoute
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hcyc : StrictCyclicPos hullFiveOccupancyCycleSlot
      (fun i ↦ v (e i)))
    (regions : Fin 3 → HullFivePointRegion)
    (hmem : ∀ i : Fin 3, ∀ anchor : Fin 5,
      InHullFiveFanCell (v (e (hullFiveOccupancyInnerSlot i)))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j))) anchor
        ((regions i).fanCell anchor))
    (k : Fin 5) (inner : Equiv.Perm (Fin 3))
    (kind : HullFive111RouteKind)
    (hroute :
      let p := regions (inner 0)
      let q := regions (inner 1)
      let r := regions (inner 2)
      match kind with
      | .uz =>
          p.fanCell k = 0 ∧
          p.fanCell (k + 1) = 0 ∧
          q.fanCell (k + 3) = 1 ∧
          q.fanCell k = 1 ∧
          q.fanCell (k + 4) = 0 ∧
          r.fanCell (k + 1) = 1 ∧
          r.fanCell k = 2
      | .vz =>
          p.fanCell (k + 3) = 1 ∧
          p.fanCell k = 0 ∧
          p.fanCell (k + 4) = 0 ∧
          q.fanCell k = 1 ∧
          q.fanCell (k + 1) = 0 ∧
          r.fanCell (k + 1) = 1 ∧
          r.fanCell k = 2) :
    let e' : Fin 8 → Fin 8 :=
      fun i ↦ e (hullFiveOccupancyReindex k inner i)
    HullFive111UZPacket v e' ∨ HullFive111VZPacket v e' := by
  let e' : Fin 8 → Fin 8 :=
    fun i ↦ e (hullFiveOccupancyReindex k inner i)
  have hcyc' : StrictCyclicPos hullFiveOccupancyCycleSlot
      (fun i ↦ v (e' i)) := by
    simpa only [e'] using
      strictCyclicPos_hullFiveOccupancyReindex
        (fun i ↦ v (e i)) hcyc k inner
  have hpositive : HullFive111PositiveChart v e' :=
    positiveChart_of_strictCycle v e' hcyc'
  have selectedMem (i : Fin 3) (anchor : Fin 5) (cell : Fin 3)
      (hcell : (regions (inner i)).fanCell anchor = cell) :
      InHullFiveFanCell
        (v (e (hullFiveOccupancyInnerSlot (inner i))))
        (fun j ↦ v (e (hullFiveOccupancyCycleSlot j)))
        anchor cell := by
    simpa only [hcell] using hmem (inner i) anchor
  cases kind with
  | uz =>
      rcases hroute with ⟨hpU, hpE, hqT, hqV, hqW, hrZ, hrF⟩
      have hpU' := selectedMem 0 k 0 hpU
      have hpE' := selectedMem 0 (k + 1) 0 hpE
      have hqT' := selectedMem 1 (k + 3) 1 hqT
      have hqV' := selectedMem 1 k 1 hqV
      have hqW' := selectedMem 1 (k + 4) 0 hqW
      have hrZ' := selectedMem 2 (k + 1) 1 hrZ
      have hrF' := selectedMem 2 k 2 hrF
      left
      exact {
        toHullFive111PositiveChart := hpositive
        p_in_abx := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hpU'
        p_in_bxc := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hpE'
        q_in_abc := by
          apply inTriStrict_rotate_hullFive
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hqT'
        q_in_axc := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hqV'
        q_in_abd := by
          apply inTriStrict_rotate_hullFive
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hqW'
        r_in_bcd := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hrZ'
        r_in_cda := by
          apply inTriStrict_rotate_hullFive
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hrF' }
  | vz =>
      rcases hroute with ⟨hpT, hpU, hpW, hqV, hqE, hrZ, hrF⟩
      have hpT' := selectedMem 0 (k + 3) 1 hpT
      have hpU' := selectedMem 0 k 0 hpU
      have hpW' := selectedMem 0 (k + 4) 0 hpW
      have hqV' := selectedMem 1 k 1 hqV
      have hqE' := selectedMem 1 (k + 1) 0 hqE
      have hrZ' := selectedMem 2 (k + 1) 1 hrZ
      have hrF' := selectedMem 2 k 2 hrF
      right
      exact {
        toHullFive111PositiveChart := hpositive
        p_in_abc := by
          apply inTriStrict_rotate_hullFive
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hpT'
        p_in_abx := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hpU'
        p_in_abd := by
          apply inTriStrict_rotate_hullFive
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hpW'
        q_in_axc := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hqV'
        q_in_bxc := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hqE'
        r_in_bcd := by
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hrZ'
        r_in_cda := by
          apply inTriStrict_rotate_hullFive
          simpa [e', InHullFiveFanCell, InAnchoredFiveFanCell,
            hullFiveRotate, hullFiveOccupancyCycleSlot,
            hullFiveOccupancyInnerSlot] using hrF' }

lemma fanSum_hullFiveOccupancyReindex
    (v : Configuration) (e : Fin 8 → Fin 8)
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3)) :
    fanSum v (fun i : Fin 5 ↦
        e (hullFiveOccupancyReindex shift inner
          (hullFiveOccupancyCycleSlot i))) =
      fanSum v (fun i : Fin 5 ↦
        e (hullFiveOccupancyCycleSlot i)) := by
  have hfp : fanPairs 5 =
      {((1 : Fin 5), (2 : Fin 5)), (2, 3), (3, 4)} := by
    decide
  simp only [hullFiveOccupancyReindex_hull, fanSum, hfp]
  fin_cases shift <;>
    simp [hullFiveOccupancyCycleSlot, sig] <;> ring

lemma fanSum_hullFiveOccupancyCycleSlot
    (v : Configuration) (e : Fin 8 → Fin 8) :
    fanSum v (fun i : Fin 5 ↦
        e (hullFiveOccupancyCycleSlot i)) =
      sig (v (e 0)) (v (e 1)) (v (e 4)) +
        sig (v (e 0)) (v (e 4)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) := by
  have hfp : fanPairs 5 =
      {((1 : Fin 5), (2 : Fin 5)), (2, 3), (3, 4)} := by
    decide
  rw [fanSum, hfp]
  simp [hullFiveOccupancyCycleSlot, add_assoc]

private lemma hullFive111_packetFan_eq_fanSum
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

/-- A compact UZ/VZ packet may use any cyclic reanchor of the certified
five-cycle.  This wrapper transports its strict packet bound back to the
original `HullCycleOf` area, avoiding any retained-word or fixed-anchor
assumption. -/
theorem hullFive111_reindexedPacket_not_beats_of_hullCycle
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (e : Equiv.Perm (Fin 8))
    (hchart : ∀ i : Fin 5,
      e (hullFiveOccupancyCycleSlot i) = d.castGet h5 i)
    (shift : Fin 5) (inner : Equiv.Perm (Fin 3))
    (hpacket :
      let e' : Fin 8 → Fin 8 :=
        fun i ↦ e (hullFiveOccupancyReindex shift inner i)
      HullFive111UZPacket v e' ∨ HullFive111VZPacket v e') :
    ¬ Beats doubledHullArea v8 v := by
  let e' : Fin 8 → Fin 8 :=
    fun i ↦ e (hullFiveOccupancyReindex shift inner i)
  have he' : Function.Injective e' :=
    e.injective.comp (hullFiveOccupancyReindex shift inner).injective
  intro hbeat
  have hm : 0 < minTri v :=
    (mul_pos v8_pos hbeat.1).trans hbeat.2
  have hbound : minTri v * 25 < 2 *
      (sig (v (e' 0)) (v (e' 1)) (v (e' 2)) +
        sig (v (e' 1)) (v (e' 4)) (v (e' 2)) +
        sig (v (e' 2)) (v (e' 3)) (v (e' 0))) := by
    rcases hpacket with huz | hvz
    · exact hullFive111_uz_packet_forces_hull_bound v e' he' hm huz
    · exact hullFive111_vz_packet_forces_hull_bound v e' he' hm hvz
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
        (hullFive111_packetFan_eq_fanSum v e').symm
  have hq : (2 / 25 : ℝ) < v8 :=
    lt_trans (by norm_num) v8_lb
  have hcut : (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    (mul_lt_mul_of_pos_right hq hbeat.1).trans hbeat.2
  rw [harea] at hcut
  nlinarith

#print axioms hullFive111Packet_of_profileRoute
#print axioms hullFive111_reindexedPacket_not_beats_of_hullCycle

end Heilbronn8.TriHull
