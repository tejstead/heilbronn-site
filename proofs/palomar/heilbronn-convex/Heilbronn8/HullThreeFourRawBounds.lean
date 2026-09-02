import Heilbronn8.GeometricHullFour
import Heilbronn8.TriHull.Bridge

/-!
# Raw `2 / 25` bounds for geometric hull sizes three and four

This module extracts the closed inequalities already proved inside the
hull-three and hull-four exclusion arguments.  It deliberately has no
`ReferenceMachineDomain`, survivor word, strict `Beats`, or `v8` hypothesis.

The two final declarations have the expanded type of
`GeometricHullSizeTwoTwentyFiveBound 3` and
`GeometricHullSizeTwoTwentyFiveBound 4`, respectively.  The shared interface
is kept out of this file so that the equality router may import this module
without an import cycle.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

noncomputable section

/-! ## Hull size three -/

private lemma h34_inTriStrict_of_fan_pos {p a b c : ℝ × ℝ}
    (hD : 0 < sig a b c)
    (h1 : 0 < sig p b c) (h2 : 0 < sig a p c)
    (h3 : 0 < sig a b p) :
    TriHull.InTriStrict p a b c := by
  have hDne : sig a b c ≠ 0 := ne_of_gt hD
  have hsum :
      sig p b c + sig a p c + sig a b p = sig a b c := by
    simp only [sig]
    ring
  refine ⟨sig p b c / sig a b c,
    sig a p c / sig a b c,
    sig a b p / sig a b c,
    div_pos h1 hD, div_pos h2 hD, div_pos h3 hD, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hDne]
  · have hx1 :
        p.1 * sig a b c =
          sig p b c * a.1 + sig a p c * b.1 + sig a b p * c.1 := by
      simp only [sig]
      ring
    have hx2 :
        p.2 * sig a b c =
          sig p b c * a.2 + sig a p c * b.2 + sig a b p * c.2 := by
      simp only [sig]
      ring
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith

private lemma h34_inTriStrict_absorb
    {x P Q R A B C : ℝ × ℝ}
    (hx : TriHull.InTriStrict x P Q R)
    (hP : TriHull.InTriStrict P A B C)
    (hQ : TriHull.InTriStrict Q A B C)
    (hR : TriHull.InTriStrict R A B C) :
    TriHull.InTriStrict x A B C := by
  obtain ⟨p, q, r, hp, hq, hr, hpqr, hxe⟩ := hx
  obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, h₁, hPe⟩ := hP
  obtain ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, h₂, hQe⟩ := hQ
  obtain ⟨a₃, b₃, c₃, ha₃, hb₃, hc₃, h₃, hRe⟩ := hR
  refine ⟨p * a₁ + q * a₂ + r * a₃,
    p * b₁ + q * b₂ + r * b₃,
    p * c₁ + q * c₂ + r * c₃,
    add_pos (add_pos (mul_pos hp ha₁) (mul_pos hq ha₂))
      (mul_pos hr ha₃),
    add_pos (add_pos (mul_pos hp hb₁) (mul_pos hq hb₂))
      (mul_pos hr hb₃),
    add_pos (add_pos (mul_pos hp hc₁) (mul_pos hq hc₂))
      (mul_pos hr hc₃),
    by linear_combination p * h₁ + q * h₂ + r * h₃ + hpqr, ?_⟩
  subst hxe hPe hQe hRe
  module

private lemma h34_inTriBySigns_strictSound
    {v : Configuration} {S : StrictSignData v}
    {p a b c : Fin 8} (h : InTriBySigns S p a b c) :
    TriHull.InTriStrict (v p) (v a) (v b) (v c) := by
  induction h with
  | direct h =>
      exact h34_inTriStrict_of_fan_pos
        (S.pos_of_eq_true _ _ _ h.abc)
        (S.pos_of_eq_true _ _ _ h.pbc)
        (S.pos_of_eq_true _ _ _ h.apc)
        (S.pos_of_eq_true _ _ _ h.abp)
  | absorb hx hp hq hr ihx ihp ihq ihr =>
      exact h34_inTriStrict_absorb ihx ihp ihq ihr

private def h34HullThreeSlot (i : Fin 3) : Fin 8 :=
  ⟨i.val, by omega⟩

private def h34InnerFiveSlot (i : Fin 5) : Fin 8 :=
  ⟨3 + i.val, by omega⟩

private theorem h34HullThreeSlot_injective :
    Function.Injective h34HullThreeSlot := by
  intro i j hij
  apply Fin.ext
  simpa [h34HullThreeSlot] using congrArg (fun x : Fin 8 => x.val) hij

private theorem h34InnerFiveSlot_ne_h34HullThreeSlot
    (i : Fin 5) (j : Fin 3) :
    h34InnerFiveSlot i ≠ h34HullThreeSlot j := by
  intro hij
  have hval := congrArg (fun x : Fin 8 => x.val) hij
  simp only [h34InnerFiveSlot, h34HullThreeSlot] at hval
  omega

private noncomputable def h34ExtendHullThreeCycle
    (cycle : Fin 3 → Fin 8) (hinjective : Function.Injective cycle) :
    Equiv.Perm (Fin 8) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    h34HullThreeSlot cycle h34HullThreeSlot_injective hinjective)

@[simp] private theorem h34ExtendHullThreeCycle_hull
    (cycle : Fin 3 → Fin 8) (hinjective : Function.Injective cycle)
    (i : Fin 3) :
    h34ExtendHullThreeCycle cycle hinjective (h34HullThreeSlot i) = cycle i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    h34HullThreeSlot cycle h34HullThreeSlot_injective hinjective) i

private lemma h34_fanSum_three
    (v : Configuration) (cycle : Fin 3 → Fin 8) :
    fanSum v cycle =
      sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) := by
  have hp : fanPairs 3 = {((1 : Fin 3), (2 : Fin 3))} := by decide
  rw [fanSum, hp]
  simp

/-- Every genuine triangular hull obeys the raw closed `2 / 25` bound. -/
theorem geometricHullThree_twentyFive_minTri_le_two_doubledHullArea
    {v : Configuration} (custody : GeometricHullCustody v)
    (hsize : custody.data.cycle.length = 3) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  let cycle : Fin 3 → Fin 8 := custody.data.castGet hsize
  have hinjective : Function.Injective cycle :=
    HullCycleData.castGet_injective custody.data hsize custody.hull.nodup
  have hcyclic : StrictCyclicPos cycle v :=
    HullCycleData.strictCyclicPos_cast custody.data hsize
      custody.hull.strictCyclicPos
  let e : Equiv.Perm (Fin 8) :=
    h34ExtendHullThreeCycle cycle hinjective
  let w : Configuration := fun i => v (e i)
  have heHull (i : Fin 3) : e (h34HullThreeSlot i) = cycle i := by
    simpa [e] using h34ExtendHullThreeCycle_hull cycle hinjective i
  have he₀ : e 0 = cycle 0 := by
    simpa [h34HullThreeSlot] using heHull 0
  have he₁ : e 1 = cycle 1 := by
    simpa [h34HullThreeSlot] using heHull 1
  have he₂ : e 2 = cycle 2 := by
    simpa [h34HullThreeSlot] using heHull 2
  have hinnerNe (i : Fin 5) (j : Fin 3) :
      e (h34InnerFiveSlot i) ≠ cycle j := by
    have hne := e.injective.ne
      (h34InnerFiveSlot_ne_h34HullThreeSlot i j)
    rw [heHull j] at hne
    exact hne
  have hin (i : Fin 5) :
      TriHull.InTriStrict (v (e (h34InnerFiveSlot i)))
        (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) := by
    have hpOutside : e (h34InnerFiveSlot i) ∉ Set.range custody.data.get := by
      rintro ⟨j, hj⟩
      have hcast : cycle (Fin.cast hsize j) = custody.data.get j := by
        rfl
      exact hinnerNe i (Fin.cast hsize j) (hj.symm.trans hcast.symm)
    obtain ⟨left, right, hleft, hlr, hsigns⟩ :=
      custody.hull.covers (e (h34InnerFiveSlot i)) hpOutside
    let left' : Fin 3 := Fin.cast hsize left
    let right' : Fin 3 := Fin.cast hsize right
    have hleft' : (0 : Fin 3) < left' := by
      exact (Fin.cast_lt_cast hsize).2 hleft
    have hlr' : left' < right' := by
      exact (Fin.cast_lt_cast hsize).2 hlr
    have hleftOne : left' = 1 := by
      apply Fin.ext
      omega
    have hrightTwo : right' = 2 := by
      apply Fin.ext
      omega
    have hgetLeft : custody.data.get left = cycle left' := by
      rfl
    have hgetRight : custody.data.get right = cycle right' := by
      rfl
    have hgetZero : custody.data.get 0 = cycle 0 := by
      rfl
    rw [hgetZero, hgetLeft, hgetRight, hleftOne, hrightTwo] at hsigns
    exact h34_inTriBySigns_strictSound hsigns
  have hpos : 0 < sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) :=
    hcyclic.pos 0 1 2 (by decide) (by decide)
  have harea : doubledHullArea v =
      sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) := by
    calc
      doubledHullArea v = custody.data.fanExpr v :=
        doubledHullArea_eq_of_isHullArea custody.hull.isHullArea
      _ = fanSum v cycle :=
        (HullCycleData.fanSum_castGet custody.data hsize).symm
      _ = sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) :=
        h34_fanSum_three v cycle
  have hcertificate :
      TriHull.StrictTriangleHullCertificate w (doubledHullArea v) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [w, he₀, he₁, he₂] using hpos
    · simpa [w, h34InnerFiveSlot, he₀, he₁, he₂] using hin 0
    · simpa [w, h34InnerFiveSlot, he₀, he₁, he₂] using hin 1
    · simpa [w, h34InnerFiveSlot, he₀, he₁, he₂] using hin 2
    · simpa [w, h34InnerFiveSlot, he₀, he₁, he₂] using hin 3
    · simpa [w, h34InnerFiveSlot, he₀, he₁, he₂] using hin 4
    · simpa [w, he₀, he₁, he₂] using harea
  have htriangle := TriHull.triangleHull8_unconditional w
    (doubledHullArea v) hcertificate
  have hmin : minTri w = minTri v := by
    simpa [w] using minTri_relabel v e
  rw [hmin] at htriangle
  calc
    25 * minTri v = minTri v * 25 := by ring
    _ ≤ 2 * doubledHullArea v := htriangle

/-- Router-shaped hull-three provider, written without importing the router. -/
theorem geometricHullThree_twoTwentyFiveBound :
    ∀ {v : Configuration} (custody : GeometricHullCustody v),
      0 < minTri v → custody.data.cycle.length = 3 →
        25 * minTri v ≤ 2 * doubledHullArea v := by
  intro v custody _hmin hsize
  exact geometricHullThree_twentyFive_minTri_le_two_doubledHullArea
    custody hsize

/-! ## Hull size four -/

private def h34GeometricHullSlot (i : Fin 4) : Fin 8 :=
  ⟨i.val, by omega⟩

private def h34GeometricInnerSlot (i : Fin 4) : Fin 8 :=
  ⟨4 + i.val, by omega⟩

private theorem h34GeometricInnerSlot_ne_h34GeometricHullSlot
    (i j : Fin 4) :
    h34GeometricInnerSlot i ≠ h34GeometricHullSlot j := by
  intro hij
  have hval := congrArg (fun x : Fin 8 => x.val) hij
  simp only [h34GeometricInnerSlot, h34GeometricHullSlot] at hval
  omega

private noncomputable def h34GeometricInner
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D)) :
    Fin 4 → Fin 8 :=
  QuadHull.selectedOffHullLabel A B C D hinjective

private noncomputable def h34GeometricLabels
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D)) :
    Fin 8 → Fin 8 :=
  QuadHull.quadLabels A B C D
    (h34GeometricInner A B C D hinjective 0)
    (h34GeometricInner A B C D hinjective 1)
    (h34GeometricInner A B C D hinjective 2)
    (h34GeometricInner A B C D hinjective 3)

@[simp] private theorem h34GeometricLabels_inner
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D))
    (i : Fin 4) :
    h34GeometricLabels A B C D hinjective (h34GeometricInnerSlot i) =
      h34GeometricInner A B C D hinjective i := by
  fin_cases i <;> rfl

@[simp] private theorem h34GeometricLabels_hull
    (A B C D : Fin 8)
    (hinjective : Function.Injective (QuadHull.hullFourLabels A B C D))
    (i : Fin 4) :
    h34GeometricLabels A B C D hinjective (h34GeometricHullSlot i) =
      QuadHull.hullFourLabels A B C D i := by
  fin_cases i <;> rfl

private def H34GeometricCyclicAdjacent {size : Nat}
    (left right : Fin size) : Prop :=
  (left.val + 1 < size ∧ right.val = left.val + 1) ∨
    (left.val + 1 = size ∧ right.val = 0)

private lemma h34GeometricCyclicAdjacent_ne {size : Nat} [NeZero size]
    (hthree : 3 ≤ size) {left right : Fin size}
    (hadjacent : H34GeometricCyclicAdjacent left right) : left ≠ right := by
  intro heq
  subst right
  rcases hadjacent with hnext | hwrap
  · omega
  · omega

private lemma h34GeometricCyclic_edge_vertex_pos
    {size : Nat} [NeZero size]
    (v : Configuration) (cycle : Fin size → Fin 8)
    (hthree : 3 ≤ size) (hcyclic : StrictCyclicPos cycle v)
    (left right point : Fin size)
    (hadjacent : H34GeometricCyclicAdjacent left right)
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

private lemma h34GeometricCyclic_edge_vertex_nonneg
    {size : Nat} [NeZero size]
    (v : Configuration) (cycle : Fin size → Fin 8)
    (hthree : 3 ≤ size) (hcyclic : StrictCyclicPos cycle v)
    (left right point : Fin size)
    (hadjacent : H34GeometricCyclicAdjacent left right) :
    0 ≤ sig (v (cycle left)) (v (cycle right)) (v (cycle point)) := by
  by_cases hpointLeft : point = left
  · subst point
    simp [sig]
  by_cases hpointRight : point = right
  · subst point
    simp [sig]
  exact (h34GeometricCyclic_edge_vertex_pos v cycle hthree hcyclic
    left right point hadjacent hpointLeft hpointRight).le

private lemma h34GeometricCyclic_edge_point_pos
    {size : Nat} [NeZero size]
    (v : Configuration) (cycle : Fin size → Fin 8)
    (hthree : 3 ≤ size) (hinjective : Function.Injective cycle)
    (hcyclic : StrictCyclicPos cycle v) (hcover : FanCovers v cycle)
    (hmin : 0 < minTri v) (left right : Fin size) (point : Fin 8)
    (hadjacent : H34GeometricCyclicAdjacent left right)
    (hpointLeft : point ≠ cycle left)
    (hpointRight : point ≠ cycle right) :
    0 < sig (v (cycle left)) (v (cycle right)) (v point) := by
  have hedge : cycle left ≠ cycle right :=
    hinjective.ne (h34GeometricCyclicAdjacent_ne hthree hadjacent)
  have hnonnegative :
      0 ≤ sig (v (cycle left)) (v (cycle right)) (v point) := by
    by_cases hpointRange : point ∈ Set.range cycle
    · rcases hpointRange with ⟨position, rfl⟩
      exact h34GeometricCyclic_edge_vertex_nonneg v cycle hthree hcyclic
        left right position hadjacent
    · obtain ⟨fanLeft, fanRight, _hzeroLeft, _hleftRight, hinside⟩ :=
        hcover point hpointRange
      rcases hinside with ⟨x, y, z, hx, hy, hz, hsum, hpoint⟩
      have hzero := h34GeometricCyclic_edge_vertex_nonneg v cycle hthree
        hcyclic left right 0 hadjacent
      have hfanLeft := h34GeometricCyclic_edge_vertex_nonneg v cycle hthree
        hcyclic left right fanLeft hadjacent
      have hfanRight := h34GeometricCyclic_edge_vertex_nonneg v cycle hthree
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

private noncomputable def h34GeometricHullFourBoundary
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
  let inner := h34GeometricInner A B C D hinjective
  let labels := h34GeometricLabels A B C D hinjective
  have hlabels : Function.Injective labels := by
    simpa [labels, h34GeometricLabels, inner, h34GeometricInner] using
      QuadHull.selectedQuadLabels_injective A B C D hinjective
  have inner_ne_cycle (i j : Fin 4) : inner i ≠ cycle j := by
    have hne := hlabels.ne
      (h34GeometricInnerSlot_ne_h34GeometricHullSlot i j)
    simpa only [labels, h34GeometricLabels_inner,
      h34GeometricLabels_hull, inner, hlabelsCycle] using hne
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
        simpa [labels, h34GeometricLabels, inner] using hlabels
      ccw := ⟨hABC, hBCD, hCDA, hDAB⟩
      inner_AB := ?_
      inner_BC := ?_
      inner_CD := ?_
      inner_DA := ?_ }
  · intro i
    apply h34GeometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 0 1 (inner i)
        (Or.inl ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 0
    · exact inner_ne_cycle i 1
  · intro i
    apply h34GeometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 1 2 (inner i)
        (Or.inl ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 1
    · exact inner_ne_cycle i 2
  · intro i
    apply h34GeometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 2 3 (inner i)
        (Or.inl ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 2
    · exact inner_ne_cycle i 3
  · intro i
    apply h34GeometricCyclic_edge_point_pos v cycle (by decide)
      hcycleInjective hcyclic hcover hmin 3 0 (inner i)
        (Or.inr ⟨by decide, rfl⟩)
    · exact inner_ne_cycle i 3
    · exact inner_ne_cycle i 0

private lemma h34_fanSum_geometricFour
    (v : Configuration) (cycle : Fin 4 → Fin 8) :
    fanSum v cycle =
      sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) +
        sig (v (cycle 0)) (v (cycle 2)) (v (cycle 3)) := by
  have hp : fanPairs 4 =
      {((1 : Fin 4), (2 : Fin 4)), (2, 3)} := by decide
  rw [fanSum, hp]
  simp

/-- The stronger native hull-four estimate, before rational weakening. -/
theorem geometricHullFour_fiveSixtyThreeBound
    {v : Configuration} (custody : GeometricHullCustody v)
    (hmin : 0 < minTri v)
    (hsize : custody.data.cycle.length = 4) :
    minTri v ≤ (5 : ℝ) / 63 * doubledHullArea v := by
  let cycle : Fin 4 → Fin 8 := custody.data.castGet hsize
  let geometry := h34GeometricHullFourBoundary custody hsize hmin
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
        h34_fanSum_geometricFour v cycle
      _ = 2 * QuadHull.quadHullArea
          (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) (v (cycle 3)) := by
        simp only [QuadHull.quadHullArea, QuadHull.oarea]
        ring
  have hbound := hclosure.scaleFreeBound hquad
  rw [harea]
  exact hbound

/-- Every genuine four-vertex hull obeys the raw closed `2 / 25` bound. -/
theorem geometricHullFour_twentyFive_minTri_le_two_doubledHullArea
    {v : Configuration} (custody : GeometricHullCustody v)
    (hmin : 0 < minTri v)
    (hsize : custody.data.cycle.length = 4) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  have hbound := geometricHullFour_fiveSixtyThreeBound custody hmin hsize
  have harea : 0 ≤ doubledHullArea v := doubledHullArea_nonneg v
  calc
    25 * minTri v ≤ 25 * ((5 : ℝ) / 63 * doubledHullArea v) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (25 * ((5 : ℝ) / 63)) * doubledHullArea v := by ring
    _ ≤ 2 * doubledHullArea v :=
      mul_le_mul_of_nonneg_right (by norm_num) harea

/-- Router-shaped hull-four provider, written without importing the router. -/
theorem geometricHullFour_twoTwentyFiveBound :
    ∀ {v : Configuration} (custody : GeometricHullCustody v),
      0 < minTri v → custody.data.cycle.length = 4 →
        25 * minTri v ≤ 2 * doubledHullArea v := by
  intro v custody hmin hsize
  exact geometricHullFour_twentyFive_minTri_le_two_doubledHullArea
    custody hmin hsize

end

end Heilbronn8
