import Heilbronn8.GeometricHullExclusionCore
import Heilbronn8.OrderDensity
import Heilbronn8.PolyVolumeGen
import Heilbronn8.QuadHull.GlobalSectorDispatcher

/-!
# Corpus-free geometric hull-four exclusion

This is the direct geometric-custody adapter for the global four-sector
dispatcher.  A genuine four-cycle supplies the four boundary edges and its
four complementary labels.  The sector theorem then proves the sharp
`5 / 63` scale-free bound without a sign word, production path, or generated
certificate bank.
-/

namespace Heilbronn8

private def geometricHullSlot (i : Fin 4) : Fin 8 :=
  ⟨i.val, by omega⟩

private def geometricInnerSlot (i : Fin 4) : Fin 8 :=
  ⟨4 + i.val, by omega⟩

private theorem geometricInnerSlot_ne_geometricHullSlot
    (i j : Fin 4) : geometricInnerSlot i ≠ geometricHullSlot j := by
  intro hij
  have hval := congrArg (fun x : Fin 8 => x.val) hij
  simp only [geometricInnerSlot, geometricHullSlot] at hval
  omega

private noncomputable def geometricInner
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D)) :
    Fin 4 → Fin 8 :=
  QuadHull.selectedOffHullLabel A B C D hinjective

private noncomputable def geometricLabels
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D)) :
    Fin 8 → Fin 8 :=
  QuadHull.quadLabels A B C D
    (geometricInner A B C D hinjective 0)
    (geometricInner A B C D hinjective 1)
    (geometricInner A B C D hinjective 2)
    (geometricInner A B C D hinjective 3)

@[simp] private theorem geometricLabels_inner
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D))
    (i : Fin 4) :
    geometricLabels A B C D hinjective (geometricInnerSlot i) =
      geometricInner A B C D hinjective i := by
  fin_cases i <;> rfl

@[simp] private theorem geometricLabels_hull
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D))
    (i : Fin 4) :
    geometricLabels A B C D hinjective (geometricHullSlot i) =
      QuadHull.hullFourLabels A B C D i := by
  fin_cases i <;> rfl

/-! ## Strict support of a genuine cyclic hull -/

private def GeometricCyclicAdjacent {size : Nat}
    (left right : Fin size) : Prop :=
  (left.val + 1 < size ∧ right.val = left.val + 1) ∨
    (left.val + 1 = size ∧ right.val = 0)

private lemma geometricCyclicAdjacent_ne {size : Nat} [NeZero size]
    (hthree : 3 ≤ size) {left right : Fin size}
    (hadjacent : GeometricCyclicAdjacent left right) : left ≠ right := by
  intro heq
  subst right
  rcases hadjacent with hnext | hwrap
  · omega
  · omega

private lemma geometricCyclic_edge_vertex_pos {size : Nat} [NeZero size]
    (v : Configuration) (cycle : Fin size → Fin 8)
    (hthree : 3 ≤ size) (hcyclic : StrictCyclicPos cycle v)
    (left right point : Fin size)
    (hadjacent : GeometricCyclicAdjacent left right)
    (hpointLeft : point ≠ left) (hpointRight : point ≠ right) :
    0 < sig (v (cycle left)) (v (cycle right)) (v (cycle point)) := by
  rcases hadjacent with hnext | hwrap
  · have hleftRight : left < right := by omega
    have hcases : point < left ∨ right < point := by omega
    rcases hcases with hbefore | hafter
    · have hpositive := hcyclic.pos point left right hbefore hleftRight
      rw [sig_rotate (v (cycle left)) (v (cycle right)) (v (cycle point)),
        sig_rotate (v (cycle right)) (v (cycle point)) (v (cycle left))]
      exact hpositive
    · exact hcyclic.pos left right point hleftRight hafter
  · have hright : right = 0 := Fin.ext hwrap.2
    subst right
    have hzeroPoint : (0 : Fin size) < point := by omega
    have hpointLeft' : point < left := by omega
    have hpositive := hcyclic.pos (0 : Fin size) point left
      hzeroPoint hpointLeft'
    rw [sig_rotate (v (cycle left)) (v (cycle 0)) (v (cycle point))]
    exact hpositive

private lemma geometricCyclic_edge_vertex_nonneg
    {size : Nat} [NeZero size]
    (v : Configuration) (cycle : Fin size → Fin 8)
    (hthree : 3 ≤ size) (hcyclic : StrictCyclicPos cycle v)
    (left right point : Fin size)
    (hadjacent : GeometricCyclicAdjacent left right) :
    0 ≤ sig (v (cycle left)) (v (cycle right)) (v (cycle point)) := by
  by_cases hpointLeft : point = left
  · subst point
    simp [sig]
  by_cases hpointRight : point = right
  · subst point
    simp [sig]
  exact (geometricCyclic_edge_vertex_pos v cycle hthree hcyclic
    left right point hadjacent hpointLeft hpointRight).le

/-- `FanCovers` transports a cyclic boundary half-plane to every point.
Positive `minTri` then makes it strict away from the edge endpoints. -/
private lemma geometricCyclic_edge_point_pos
    {size : Nat} [NeZero size]
    (v : Configuration) (cycle : Fin size → Fin 8)
    (hthree : 3 ≤ size) (hinjective : Function.Injective cycle)
    (hcyclic : StrictCyclicPos cycle v) (hcover : FanCovers v cycle)
    (hmin : 0 < minTri v) (left right : Fin size) (point : Fin 8)
    (hadjacent : GeometricCyclicAdjacent left right)
    (hpointLeft : point ≠ cycle left)
    (hpointRight : point ≠ cycle right) :
    0 < sig (v (cycle left)) (v (cycle right)) (v point) := by
  have hedge : cycle left ≠ cycle right :=
    hinjective.ne (geometricCyclicAdjacent_ne hthree hadjacent)
  have hnonnegative :
      0 ≤ sig (v (cycle left)) (v (cycle right)) (v point) := by
    by_cases hpointRange : point ∈ Set.range cycle
    · rcases hpointRange with ⟨position, rfl⟩
      exact geometricCyclic_edge_vertex_nonneg v cycle hthree hcyclic
        left right position hadjacent
    · obtain ⟨fanLeft, fanRight, _hzeroLeft, _hleftRight, hinside⟩ :=
        hcover point hpointRange
      rcases hinside with ⟨x, y, z, hx, hy, hz, hsum, hpoint⟩
      have hzero := geometricCyclic_edge_vertex_nonneg v cycle hthree
        hcyclic left right 0 hadjacent
      have hfanLeft := geometricCyclic_edge_vertex_nonneg v cycle hthree
        hcyclic left right fanLeft hadjacent
      have hfanRight := geometricCyclic_edge_vertex_nonneg v cycle hthree
        hcyclic left right fanRight hadjacent
      have haffine :
          sig (v (cycle left)) (v (cycle right))
              (x • v (cycle 0) + y • v (cycle fanLeft) +
                z • v (cycle fanRight)) =
            x * sig (v (cycle left)) (v (cycle right)) (v (cycle 0)) +
              y * sig (v (cycle left)) (v (cycle right))
                (v (cycle fanLeft)) +
              z * sig (v (cycle left)) (v (cycle right))
                (v (cycle fanRight)) := by
        have hz' : z = 1 - x - y := by linarith
        rw [hz']
        simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
          Prod.snd_add, smul_eq_mul]
        ring
      rw [hpoint, haffine]
      exact add_nonneg (add_nonneg (mul_nonneg hx hzero)
        (mul_nonneg hy hfanLeft)) (mul_nonneg hz hfanRight)
  have hminimum := minTri_le_abs_sig_of_pairwise_ne v
    hedge hpointLeft.symm hpointRight.symm
  have hnonzero :
      sig (v (cycle left)) (v (cycle right)) (v point) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hminimum
    linarith
  exact lt_of_le_of_ne hnonnegative (Ne.symm hnonzero)

/-! ## Geometric custody to the global-sector input -/

private noncomputable def geometricHullFourBoundary
    {v : Configuration} (custody : GeometricHullCustody v)
    (hsize : custody.data.cycle.length = 4)
    (hmin : 0 < minTri v) :
    QuadHull.HullFourBoundaryGeometry v
      (custody.data.castGet hsize 0) (custody.data.castGet hsize 1)
      (custody.data.castGet hsize 2) (custody.data.castGet hsize 3) := by
  let cycle : Fin 4 → Fin 8 := custody.data.castGet hsize
  let A := cycle 0
  let B := cycle 1
  let C := cycle 2
  let D := cycle 3
  have hcycleInjective : Function.Injective cycle :=
    HullCycleData.castGet_injective custody.data hsize custody.hull.nodup
  have hcyclic : StrictCyclicPos cycle v :=
    HullCycleData.strictCyclicPos_cast custody.data hsize
      custody.hull.strictCyclicPos
  have hcover : FanCovers v cycle :=
    HullCycleData.fanCovers_cast custody.data hsize custody.hull.fanCovers
  have hlabelsCycle : QuadHull.hullFourLabels A B C D = cycle := by
    funext i
    fin_cases i <;> rfl
  have hinjective :
      Function.Injective (QuadHull.hullFourLabels A B C D) := by
    rw [hlabelsCycle]
    exact hcycleInjective
  let inner := geometricInner A B C D hinjective
  let labels := geometricLabels A B C D hinjective
  have hlabels : Function.Injective labels := by
    simpa [labels, geometricLabels, inner, geometricInner] using
      QuadHull.selectedQuadLabels_injective A B C D hinjective
  have inner_ne_cycle (i j : Fin 4) : inner i ≠ cycle j := by
    have hne := hlabels.ne
      (geometricInnerSlot_ne_geometricHullSlot i j)
    simpa only [labels, geometricLabels_inner, geometricLabels_hull,
      inner, hlabelsCycle] using hne
  have hABC : 0 < sig (v A) (v B) (v C) :=
    hcyclic.pos 0 1 2 (by decide) (by decide)
  have hBCD : 0 < sig (v B) (v C) (v D) :=
    hcyclic.pos 1 2 3 (by decide) (by decide)
  have hCDA : 0 < sig (v C) (v D) (v A) := by
    have hACD := hcyclic.pos 0 2 3 (by decide) (by decide)
    rw [← sig_rotate (v A) (v C) (v D)]
    exact hACD
  have hDAB : 0 < sig (v D) (v A) (v B) := by
    have hABD := hcyclic.pos 0 1 3 (by decide) (by decide)
    rw [← sig_rotate (v B) (v D) (v A),
      ← sig_rotate (v A) (v B) (v D)]
    exact hABD
  refine
    { inner := inner
      labels_injective := by
        simpa [labels, geometricLabels, inner] using hlabels
      ccw := ⟨hABC, hBCD, hCDA, hDAB⟩
      inner_AB := ?_
      inner_BC := ?_
      inner_CD := ?_
      inner_DA := ?_ }
  · intro i
    apply geometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 0 1 (inner i)
        (Or.inl ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 0
    · exact inner_ne_cycle i 1
  · intro i
    apply geometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 1 2 (inner i)
        (Or.inl ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 1
    · exact inner_ne_cycle i 2
  · intro i
    apply geometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 2 3 (inner i)
        (Or.inl ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 2
    · exact inner_ne_cycle i 3
  · intro i
    apply geometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 3 0 (inner i)
        (Or.inr ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 3
    · exact inner_ne_cycle i 0

private lemma fanSum_geometricFour
    (v : Configuration) (cycle : Fin 4 → Fin 8) :
    fanSum v cycle =
      sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) +
        sig (v (cycle 0)) (v (cycle 2)) (v (cycle 3)) := by
  have hp : fanPairs 4 =
      {((1 : Fin 4), (2 : Fin 4)), (2, 3)} := by decide
  rw [fanSum, hp]
  simp

/-- Every genuine four-vertex hull obeys the global `5 / 63` bound.  The
reference-domain and extra predicates are deliberately unused. -/
theorem geometricHullFourExclusion
    (extra : Configuration → Prop) :
    GeometricHullSizeExclusion 4 extra := by
  intro v custody _hdomain _hextra hsize hbeat
  let cycle : Fin 4 → Fin 8 := custody.data.castGet hsize
  have hmin : 0 < minTri v :=
    lt_trans (mul_pos v8_pos hbeat.1) hbeat.2
  let geometry := geometricHullFourBoundary custody hsize hmin
  have hclosure := geometry.globalClosure
  have hcyclic : StrictCyclicPos cycle v :=
    HullCycleData.strictCyclicPos_cast custody.data hsize
      custody.hull.strictCyclicPos
  have hABC : 0 < sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) :=
    hcyclic.pos 0 1 2 (by decide) (by decide)
  have hACD : 0 < sig (v (cycle 0)) (v (cycle 2)) (v (cycle 3)) :=
    hcyclic.pos 0 2 3 (by decide) (by decide)
  have hquad :
      0 ≤ QuadHull.quadHullArea
        (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) (v (cycle 3)) := by
    simp only [QuadHull.quadHullArea, QuadHull.oarea]
    linarith
  have harea : doubledHullArea v =
      2 * QuadHull.quadHullArea
        (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) (v (cycle 3)) := by
    calc
      doubledHullArea v = custody.data.fanExpr v :=
        doubledHullArea_eq_of_isHullArea custody.hull.isHullArea
      _ = fanSum v cycle :=
        (HullCycleData.fanSum_castGet custody.data hsize).symm
      _ = sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) +
          sig (v (cycle 0)) (v (cycle 2)) (v (cycle 3)) :=
        fanSum_geometricFour v cycle
      _ = 2 * QuadHull.quadHullArea
          (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) (v (cycle 3)) := by
        simp only [QuadHull.quadHullArea, QuadHull.oarea]
        ring
  have hbound := hclosure.scaleFreeBound hquad
  have hbound' : minTri v ≤ (5 : ℝ) / 63 * doubledHullArea v := by
    rw [harea]
    exact hbound
  have hlevel : (5 : ℝ) / 63 < v8 :=
    lt_trans (by norm_num) v8_lb
  have hlevels := mul_lt_mul_of_pos_right hlevel hbeat.1
  exact (not_lt_of_ge hbound') (lt_trans hlevels hbeat.2)

/-- Exact strict-order endpoint requested by the geometric final spine. -/
theorem geometricHullFourStrictXOrderExclusion :
    GeometricHullSizeExclusion 4 StrictXOrder :=
  geometricHullFourExclusion StrictXOrder

#print axioms geometricHullFourExclusion
#print axioms geometricHullFourStrictXOrderExclusion

end Heilbronn8
