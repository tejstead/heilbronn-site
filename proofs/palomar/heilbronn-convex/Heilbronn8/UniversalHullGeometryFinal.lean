import Heilbronn8.GeometricHullExclusionCore
import Heilbronn8.Survivors.OrderDensityDense
import Heilbronn8.Survivors.Join.HullEightOctagon
import Heilbronn8.GlobalAssembly
import Heilbronn8.TriHull.Bridge

/-!
# Direct final theorem from geometric hull custody

This module removes the production-path layer from the universal hull-size
route.  A beating configuration has positive minimum triangle area, so the
geometric hull-cycle existence theorem supplies its strict sign data, literal
hull cycle, and proof-relevant hull witness directly.  Universal geometry for
hull sizes four through seven then closes the strict reference-machine domain.
One global order-density step and the affine normalization spine give the final
equality.
-/

namespace Heilbronn8

/-! ## Unconditional hull-three geometry -/

private lemma inTriStrict_of_fan_pos {p a b c : ℝ × ℝ}
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

/-- Strict barycentric containment is transitive through a triangle. -/
private lemma inTriStrict_absorb
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

/-- A sign-derived containment tree is strict because every direct leaf stores
four positive oriented areas. -/
private lemma inTriBySigns_strictSound
    {v : Configuration} {S : StrictSignData v}
    {p a b c : Fin 8} (h : InTriBySigns S p a b c) :
    TriHull.InTriStrict (v p) (v a) (v b) (v c) := by
  induction h with
  | direct h =>
      exact inTriStrict_of_fan_pos
        (S.pos_of_eq_true _ _ _ h.abc)
        (S.pos_of_eq_true _ _ _ h.pbc)
        (S.pos_of_eq_true _ _ _ h.apc)
        (S.pos_of_eq_true _ _ _ h.abp)
  | absorb hx hp hq hr ihx ihp ihq ihr =>
      exact inTriStrict_absorb ihx ihp ihq ihr

private def hullThreeSlot (i : Fin 3) : Fin 8 :=
  ⟨i.val, by omega⟩

private def innerFiveSlot (i : Fin 5) : Fin 8 :=
  ⟨3 + i.val, by omega⟩

private theorem hullThreeSlot_injective :
    Function.Injective hullThreeSlot := by
  intro i j hij
  apply Fin.ext
  simpa [hullThreeSlot] using congrArg (fun x : Fin 8 => x.val) hij

private theorem innerFiveSlot_ne_hullThreeSlot (i : Fin 5) (j : Fin 3) :
    innerFiveSlot i ≠ hullThreeSlot j := by
  intro hij
  have hval := congrArg (fun x : Fin 8 => x.val) hij
  simp only [innerFiveSlot, hullThreeSlot] at hval
  omega

/-- Extend the labelled hull triangle to a permutation of all eight labels. -/
private noncomputable def extendHullThreeCycle
    (cycle : Fin 3 → Fin 8) (hinjective : Function.Injective cycle) :
    Equiv.Perm (Fin 8) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    hullThreeSlot cycle hullThreeSlot_injective hinjective)

@[simp] private theorem extendHullThreeCycle_hull
    (cycle : Fin 3 → Fin 8) (hinjective : Function.Injective cycle)
    (i : Fin 3) :
    extendHullThreeCycle cycle hinjective (hullThreeSlot i) = cycle i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    hullThreeSlot cycle hullThreeSlot_injective hinjective) i

private lemma fanSum_three
    (v : Configuration) (cycle : Fin 3 → Fin 8) :
    fanSum v cycle =
      sig (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) := by
  have hp : fanPairs 3 = {((1 : Fin 3), (2 : Fin 3))} := by decide
  rw [fanSum, hp]
  simp

/-- Every genuine triangular hull obeys the unconditional triangle-hull
bound, independently of the additional predicate. -/
theorem geometricHullThreeExclusion
    (extra : Configuration → Prop) :
    GeometricHullSizeExclusion 3 extra := by
  intro v custody _hdomain _hextra hsize hbeat
  let cycle : Fin 3 → Fin 8 := custody.data.castGet hsize
  have hinjective : Function.Injective cycle :=
    HullCycleData.castGet_injective custody.data hsize custody.hull.nodup
  have hcyclic : StrictCyclicPos cycle v :=
    HullCycleData.strictCyclicPos_cast custody.data hsize
      custody.hull.strictCyclicPos
  let e : Equiv.Perm (Fin 8) := extendHullThreeCycle cycle hinjective
  let w : Configuration := fun i => v (e i)
  have heHull (i : Fin 3) : e (hullThreeSlot i) = cycle i := by
    simpa [e] using extendHullThreeCycle_hull cycle hinjective i
  have he₀ : e 0 = cycle 0 := by
    simpa [hullThreeSlot] using heHull 0
  have he₁ : e 1 = cycle 1 := by
    simpa [hullThreeSlot] using heHull 1
  have he₂ : e 2 = cycle 2 := by
    simpa [hullThreeSlot] using heHull 2
  have hinnerNe (i : Fin 5) (j : Fin 3) :
      e (innerFiveSlot i) ≠ cycle j := by
    have hne := e.injective.ne (innerFiveSlot_ne_hullThreeSlot i j)
    rw [heHull j] at hne
    exact hne
  have hin (i : Fin 5) :
      TriHull.InTriStrict (v (e (innerFiveSlot i)))
        (v (cycle 0)) (v (cycle 1)) (v (cycle 2)) := by
    have hpOutside : e (innerFiveSlot i) ∉ Set.range custody.data.get := by
      rintro ⟨j, hj⟩
      have hcast : cycle (Fin.cast hsize j) = custody.data.get j := by
        rfl
      exact hinnerNe i (Fin.cast hsize j) (hj.symm.trans hcast.symm)
    obtain ⟨left, right, hleft, hlr, hsigns⟩ :=
      custody.hull.covers (e (innerFiveSlot i)) hpOutside
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
    exact inTriBySigns_strictSound hsigns
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
        fanSum_three v cycle
  have hcertificate :
      TriHull.StrictTriangleHullCertificate w (doubledHullArea v) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [w, he₀, he₁, he₂] using hpos
    · simpa [w, innerFiveSlot, he₀, he₁, he₂] using hin 0
    · simpa [w, innerFiveSlot, he₀, he₁, he₂] using hin 1
    · simpa [w, innerFiveSlot, he₀, he₁, he₂] using hin 2
    · simpa [w, innerFiveSlot, he₀, he₁, he₂] using hin 3
    · simpa [w, innerFiveSlot, he₀, he₁, he₂] using hin 4
    · simpa [w, he₀, he₁, he₂] using harea
  have htriangle := TriHull.triangleHull8_unconditional w
    (doubledHullArea v) hcertificate
  have hmin : minTri w = minTri v := by
    simpa [w] using minTri_relabel v e
  rw [hmin] at htriangle
  have hbound : minTri v ≤ (2 : ℝ) / 25 * doubledHullArea v := by
    nlinarith
  have hq : (2 : ℝ) / 25 < v8 :=
    lt_trans (by norm_num) v8_lb
  have hlevels := mul_lt_mul_of_pos_right hq hbeat.1
  exact (not_lt_of_ge hbound) (lt_trans hlevels hbeat.2)

/-! ## Unconditional hull-eight geometry -/

/-- Every genuine eight-vertex hull obeys the unconditional octagon bound. -/
theorem geometricHullEightExclusion
    (extra : Configuration → Prop) :
    GeometricHullSizeExclusion 8 extra := by
  intro v custody _hdomain _hextra hsize hbeat
  have hq : (2 : ℝ) / 25 < v8 :=
    lt_trans (by norm_num) v8_lb
  have hinjective : Function.Injective (custody.data.castGet hsize) :=
    HullCycleData.castGet_injective custody.data hsize custody.hull.nodup
  have hcyclic : StrictCyclicPos (custody.data.castGet hsize) v :=
    HullCycleData.strictCyclicPos_cast custody.data hsize
      custody.hull.strictCyclicPos
  exact (strictOctagon_not_Beats_of_two_div_twentyFive_lt
    hq hinjective hcyclic) hbeat

/-! ## Six-way geometric dispatch -/

/-- One exclusion for each possible geometric hull size excludes every beating
configuration carrying the corresponding reference-domain and extra facts. -/
theorem notBeats_of_geometricHullSizes
    {extra : Configuration → Prop}
    (h3 : GeometricHullSizeExclusion 3 extra)
    (h4 : GeometricHullSizeExclusion 4 extra)
    (h5 : GeometricHullSizeExclusion 5 extra)
    (h6 : GeometricHullSizeExclusion 6 extra)
    (h7 : GeometricHullSizeExclusion 7 extra)
    (h8 : GeometricHullSizeExclusion 8 extra)
    (v : Configuration) (hdomain : ReferenceMachineDomain v)
    (hextra : extra v) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  obtain ⟨custody⟩ := geometricHullCustody_exists_of_Beats hbeat
  have hsizes :
      custody.data.cycle.length = 3 ∨
      custody.data.cycle.length = 4 ∨
      custody.data.cycle.length = 5 ∨
      custody.data.cycle.length = 6 ∨
      custody.data.cycle.length = 7 ∨
      custody.data.cycle.length = 8 := by
    have hlower := custody.data.length_ge_three
    have hupper := custody.data.length_le_eight
    omega
  rcases hsizes with hsize | hsize | hsize | hsize | hsize | hsize
  · exact h3 custody hdomain hextra hsize hbeat
  · exact h4 custody hdomain hextra hsize hbeat
  · exact h5 custody hdomain hextra hsize hbeat
  · exact h6 custody hdomain hextra hsize hbeat
  · exact h7 custody hdomain hextra hsize hbeat
  · exact h8 custody hdomain hextra hsize hbeat

/-! ## Density and final upper-bound spine -/

private lemma referenceMachineDomain_of_strictBase
    {v : Configuration} (hv : v ∈ StrictOrderRegion ReferenceMachineBase) :
    ReferenceMachineDomain v :=
  mem_weakOrderRegion_referenceMachineBase_iff.mp
    ⟨hv.1, hv.2.monotone⟩

private theorem one_le_doubledHullArea_of_gaugeNormalized
    (v : Configuration) (hgauge : GaugeNormalized v) :
    1 ≤ doubledHullArea v := by
  have htriangle : |sig (v 0) (v 1) (v 2)| = 1 := by
    rw [hgauge.map_zero, hgauge.map_one, hgauge.map_two]
    norm_num [sig]
  rw [← htriangle]
  exact abs_sig_le_doubledHullArea v 0 1 2

private theorem hasSmallTriangle_of_positive_notBeats
    {L : ℝ} {v : Configuration}
    (harea : 0 < doubledHullArea v)
    (hnot : ¬ Beats doubledHullArea L v) :
    HasSmallTriangle L v := by
  have hsmall : minTri v ≤ L * doubledHullArea v := by
    apply le_of_not_gt
    intro hlarge
    exact hnot ⟨harea, hlarge⟩
  obtain ⟨t, ht, hmin⟩ := Finset.exists_mem_eq_inf' triples_nonempty
    (fun t : Fin 8 × (Fin 8 × Fin 8) ↦
      |sig (v t.1) (v t.2.1) (v t.2.2)|)
  refine ⟨t, ht, ?_⟩
  rw [← hmin]
  exact hsmall

/-- The four open size theorems exclude the strict reference-machine domain. -/
theorem strictReferenceMachine_notBeats_of_geometricHullSizes
    (h4 : GeometricHullSizeExclusion 4 StrictXOrder)
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder)
    (v : Configuration) (hdomain : ReferenceMachineDomain v)
    (hstrict : StrictXOrder v) :
    ¬ Beats doubledHullArea v8 v :=
  notBeats_of_geometricHullSizes
    (geometricHullThreeExclusion StrictXOrder) h4 h5 h6 h7
    (geometricHullEightExclusion StrictXOrder) v hdomain hstrict

/-- Strict geometric exclusion supplies the closed small-triangle predicate. -/
theorem strictReferenceMachine_hasSmallTriangle_of_geometricHullSizes
    (h4 : GeometricHullSizeExclusion 4 StrictXOrder)
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) :
    ∀ v ∈ StrictOrderRegion ReferenceMachineBase,
      HasSmallTriangle v8 v := by
  intro v hv
  have hdomain := referenceMachineDomain_of_strictBase hv
  have harea : 0 < doubledHullArea v :=
    lt_of_lt_of_le zero_lt_one
      (one_le_doubledHullArea_of_gaugeNormalized v hv.1.1)
  exact hasSmallTriangle_of_positive_notBeats harea
    (strictReferenceMachine_notBeats_of_geometricHullSizes
      h4 h5 h6 h7 v hdomain hv.2)

/-- Density extends the strict geometric result to weak x-order. -/
theorem weakReferenceMachine_hasSmallTriangle_of_geometricHullSizes
    (h4 : GeometricHullSizeExclusion 4 StrictXOrder)
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) :
    ∀ v ∈ WeakOrderRegion ReferenceMachineBase,
      HasSmallTriangle v8 v :=
  orderDensity_real_of_dense ReferenceMachineBase
    referenceMachineBase_weakOrderDense v8 v8_pos.le
    (strictReferenceMachine_hasSmallTriangle_of_geometricHullSizes h4 h5 h6 h7)

/-- Global reference-machine closure from the four geometric size theorems. -/
theorem referenceMachine_notBeats_of_geometricHullSizes
    (h4 : GeometricHullSizeExclusion 4 StrictXOrder)
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder)
    (v : Configuration) (hdomain : ReferenceMachineDomain v) :
    ¬ Beats doubledHullArea v8 v := by
  have hweak : v ∈ WeakOrderRegion ReferenceMachineBase :=
    mem_weakOrderRegion_referenceMachineBase_iff.mpr hdomain
  exact
    (weakReferenceMachine_hasSmallTriangle_of_geometricHullSizes
      h4 h5 h6 h7 v hweak).not_Beats

/-- The analytic upper-bound step, parameterized only by global closure of the
reference-machine domain. -/
private lemma areaRatio_le_of_not_Beats
    {H : Configuration → ℝ} {v : Configuration}
    (hH : 0 < H v) (hnot : ¬ Beats H v8 v) : areaRatio H v ≤ v8 := by
  rw [areaRatio, div_le_iff₀ hH]
  exact le_of_not_gt fun h => hnot ⟨hH, h⟩

/-- The analytic upper-bound step, parameterized only by global closure of the
reference-machine domain. -/
theorem upperBound_of_referenceMachineClosure
    (closed : ∀ v : Configuration, ReferenceMachineDomain v →
      ¬ Beats doubledHullArea v8 v)
    : UpperBoundStatement := by
  intro p hp
  have hparea : doubledHullArea p = 2 :=
    doubledHullArea_eq_two_of_volume_one hp
  have hratio : areaRatio doubledHullArea p ≤ v8 := by
    apply doubledHullArea_gauge_wlog v8 v8_pos.le
    · intro u hu hupos
      obtain ⟨w, hdomain, _hmin, harea, hratio⟩ :=
        exists_referenceMachineDomain_representative u hu
      have hwpos : 0 < doubledHullArea w := by
        rwa [harea]
      have hwbound : areaRatio doubledHullArea w ≤ v8 :=
        areaRatio_le_of_not_Beats hwpos (closed w hdomain)
      rw [← hratio]
      exact hwbound
    · rw [hparea]
      norm_num
  rw [areaRatio, hparea] at hratio
  nlinarith

/-- Direct upper bound from geometric hull-size exclusions four through seven. -/
theorem upperBound_of_geometricHullSizes
    (h4 : GeometricHullSizeExclusion 4 StrictXOrder)
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) : UpperBoundStatement :=
  upperBound_of_referenceMachineClosure
    (referenceMachine_notBeats_of_geometricHullSizes h4 h5 h6 h7)

/-- Final equality from four production-free geometric hull-size theorems. -/
theorem heilbronn_eight_final_of_geometricHullSizes
    (h4 : GeometricHullSizeExclusion 4 StrictXOrder)
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) :
    h_convex 8 = v8 :=
  h_convex_eight_eq_v8_of_upper_bound
    (upperBound_of_geometricHullSizes h4 h5 h6 h7)

#print axioms geometricHullCustody_exists_of_Beats
#print axioms geometricHullThreeExclusion
#print axioms geometricHullEightExclusion
#print axioms heilbronn_eight_final_of_geometricHullSizes

end Heilbronn8
