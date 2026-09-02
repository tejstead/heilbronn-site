import Heilbronn8.CoverGeometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.Sequences
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Density of strict free-coordinate order

This module closes a weakly ordered root from coverage of every strictly
ordered point in that same root. The level is not fixed globally. The main
theorem takes an arbitrary nonnegative rational level, so each certificate
family can supply its own level.

The finite-witness step is expressed as closedness of a finite union, one
closed set for each member of `triples`. For the hull term, the needed
one-sided limit statement is proved from the definition of
`doubledHullArea`: uniformly close vertices put one convex hull inside a
small thickening of the other, and volumes of thickenings of a compact set
converge to its volume. This applies without a fixed combinatorial hull type.
-/

open Filter Set
open scoped Topology

namespace Heilbronn8

/-- Weak order `x3 <= x4 <= x5 <= x6 <= x7`. -/
def WeakXOrder (v : Configuration) : Prop :=
  Monotone (xCoordsOf v)

/-- Strict order `x3 < x4 < x5 < x6 < x7`. -/
def StrictXOrder (v : Configuration) : Prop :=
  StrictMono (xCoordsOf v)

/-- The weakly ordered part of one root. -/
def WeakOrderRegion (R : Set Configuration) : Set Configuration :=
  {v | v ∈ R ∧ WeakXOrder v}

/-- The strictly ordered part of one root. -/
def StrictOrderRegion (R : Set Configuration) : Set Configuration :=
  {v | v ∈ R ∧ StrictXOrder v}

/-- The segment from `p` to `z`, parametrized by `t`. -/
noncomputable def orderSegment
    (p z : Configuration) (t : ℝ) : Configuration :=
  (1 - t) • p + t • z

/-- A positive segment step from weak order toward strict order is strict and
stays in the same convex root. -/
lemma orderSegment_mem_strictOrderRegion
    {R : Set Configuration} (hR : Convex ℝ R)
    {p z : Configuration} (hp : p ∈ WeakOrderRegion R)
    (hz : z ∈ StrictOrderRegion R)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    orderSegment p z t ∈ StrictOrderRegion R := by
  constructor
  · have hmem := hR.lineMap_mem hp.1 hz.1
      (show t ∈ Set.Icc (0 : ℝ) 1 from ⟨ht0.le, ht1⟩)
    simpa only [orderSegment, AffineMap.lineMap_apply_module] using hmem
  · intro i j hij
    have hpij := hp.2 hij.le
    have hzij := hz.2 hij
    dsimp [StrictXOrder, WeakXOrder, orderSegment, xCoordsOf] at hpij hzij ⊢
    nlinarith

/-- Every weakly ordered point of a convex root is a limit of strictly
ordered points of that root, provided the strict part is nonempty. -/
lemma weakOrderRegion_subset_closure_strictOrderRegion
    {R : Set Configuration} (hR : Convex ℝ R)
    (hstrictNonempty : (StrictOrderRegion R).Nonempty) :
    WeakOrderRegion R ⊆ closure (StrictOrderRegion R) := by
  intro p hp
  rcases hstrictNonempty with ⟨z, hz⟩
  rw [mem_closure_iff_seq_limit]
  let t : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let u : ℕ → Configuration := fun n => orderSegment p z (t n)
  refine ⟨u, ?_, ?_⟩
  · intro n
    exact orderSegment_mem_strictOrderRegion hR hp hz
      (by dsimp [t]; positivity)
      (by
        dsimp [t]
        simpa using
          (Nat.one_div_le_one_div (α := ℝ) (Nat.zero_le n)))
  · have ht : Tendsto t atTop (𝓝 0) := by
      simpa only [t] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcontinuous : Continuous (fun r : ℝ => orderSegment p z r) := by
      unfold orderSegment
      fun_prop
    have hu := hcontinuous.continuousAt.tendsto.comp ht
    simpa only [u, Function.comp_def, orderSegment, sub_zero,
      one_smul, zero_smul, add_zero] using hu

/-! ## Closedness of the finite small-triangle predicate -/

/-- A uniform vertex perturbation puts the perturbed convex hull in a
slightly larger open thickening of the original hull. -/
lemma convexHull_range_subset_thickening_of_uniformDist
    (v w : Configuration) {eps delta : ℝ}
    (hlt : eps < delta)
    (hdist : ∀ i, dist (w i) (v i) ≤ eps) :
    convexHull ℝ (Set.range w) ⊆
      Metric.thickening delta (convexHull ℝ (Set.range v)) := by
  intro x hx
  rw [convexHull_range_eq_exists_affineCombination] at hx
  rcases hx with ⟨s, a, ha, hsum, rfl⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨s.affineCombination ℝ v a,
    affineCombination_mem_convexHull ha hsum, ?_⟩
  rw [dist_eq_norm,
    s.affineCombination_eq_linear_combination w a hsum,
    s.affineCombination_eq_linear_combination v a hsum,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ s, (a i • w i - a i • v i)‖
        = ‖∑ i ∈ s, a i • (w i - v i)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_sub]
    _ ≤ ∑ i ∈ s, ‖a i • (w i - v i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, a i * dist (w i) (v i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i hi),
            dist_eq_norm]
    _ ≤ ∑ i ∈ s, a i * eps := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hdist i) (ha i hi)
    _ = eps := by rw [← Finset.sum_mul, hsum, one_mul]
    _ < delta := hlt

/-- The hull inclusion gives the upper bound on doubled hull area needed at
the limit. -/
lemma doubledHullArea_le_thickening_of_uniformDist
    (v w : Configuration) {eps delta : ℝ}
    (hlt : eps < delta)
    (hdist : ∀ i, dist (w i) (v i) ≤ eps) :
    doubledHullArea w ≤
      2 * (MeasureTheory.volume
        (Metric.thickening delta
          (convexHull ℝ (Set.range v)))).toReal := by
  have hsubset :=
    convexHull_range_subset_thickening_of_uniformDist v w hlt hdist
  have hbounded : Bornology.IsBounded
      (Metric.thickening delta (convexHull ℝ (Set.range v))) :=
    (finite_range_isCompact_convexHull v).isBounded.thickening
  have hfinite : MeasureTheory.volume
      (Metric.thickening delta (convexHull ℝ (Set.range v))) ≠ ⊤ :=
    hbounded.measure_lt_top.ne
  unfold doubledHullArea
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hfinite (MeasureTheory.measure_mono hsubset))
    (by norm_num)

/-- The actual convex-hull functional is upper semicontinuous. This is the
direction needed to preserve `triangle area <= L * hull area` at a limit for
nonnegative `L`. -/
theorem doubledHullArea_upperSemicontinuous :
    UpperSemicontinuous doubledHullArea := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro a
  apply IsSeqClosed.isClosed
  intro u v hu hlim
  change a ≤ doubledHullArea v
  have hbound (delta : ℝ) (hdelta : 0 < delta) :
      a ≤ 2 * (MeasureTheory.volume
        (Metric.thickening delta
          (convexHull ℝ (Set.range v)))).toReal := by
    have hevent : ∀ᶠ n in atTop,
        ∀ i : Fin 8, dist (u n i) (v i) ≤ delta / 2 := by
      have hall : ∀ i ∈ (Finset.univ : Finset (Fin 8)),
          ∀ᶠ n in atTop, dist (u n i) (v i) < delta / 2 := by
        intro i hi
        have hi_lim : Tendsto (fun n => u n i) atTop (𝓝 (v i)) :=
          tendsto_pi_nhds.mp hlim i
        have hball : Metric.ball (v i) (delta / 2) ∈ 𝓝 (v i) :=
          Metric.ball_mem_nhds _ (by linarith)
        simpa only [Metric.mem_ball, dist_comm] using
          hi_lim.eventually hball
      rw [← Finset.eventually_all] at hall
      filter_upwards [hall] with n hn
      intro i
      exact (hn i (Finset.mem_univ i)).le
    obtain ⟨n, hn⟩ := hevent.exists
    exact (hu n).trans
      (doubledHullArea_le_thickening_of_uniformDist v (u n)
        (by linarith) hn)
  have hcompact := finite_range_isCompact_convexHull v
  have hfinite : ∃ R > 0,
      MeasureTheory.volume
        (Metric.thickening R (convexHull ℝ (Set.range v))) ≠ ⊤ :=
    ⟨1, zero_lt_one,
      hcompact.isBounded.thickening.measure_lt_top.ne⟩
  have hmeasure := tendsto_measure_thickening_of_isClosed
    hfinite hcompact.isClosed
  have hreal :=
    (ENNReal.tendsto_toReal (volume_convexHull_ne_top v)).comp hmeasure
  have hscaled : Tendsto
      (fun delta => 2 * (MeasureTheory.volume
        (Metric.thickening delta
          (convexHull ℝ (Set.range v)))).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (doubledHullArea v)) := by
    simpa only [doubledHullArea, Function.comp_apply] using
      tendsto_const_nhds.mul hreal
  apply ge_of_tendsto hscaled
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact hbound delta hdelta

/-- Closedness for one fixed triangle witness. The determinant term is
continuous, while the hull term uses the thickening estimate above. -/
lemma triangleWitnessSet_isClosed (L : ℝ) (hL : 0 ≤ L)
    (t : Fin 8 × Fin 8 × Fin 8) :
    IsClosed {v : Configuration |
      |sig (v t.1) (v t.2.1) (v t.2.2)| ≤ L * doubledHullArea v} := by
  apply IsSeqClosed.isClosed
  intro u v hu hlim
  have hsig : Tendsto
      (fun n => |sig (u n t.1) (u n t.2.1) (u n t.2.2)|)
      atTop (𝓝 |sig (v t.1) (v t.2.1) (v t.2.2)|) := by
    have hcontinuous : Continuous (fun w : Configuration =>
        |sig (w t.1) (w t.2.1) (w t.2.2)|) := by
      unfold sig
      fun_prop
    exact hcontinuous.continuousAt.tendsto.comp hlim
  have hbound (delta : ℝ) (hdelta : 0 < delta) :
      |sig (v t.1) (v t.2.1) (v t.2.2)| ≤
        L * (2 * (MeasureTheory.volume
          (Metric.thickening delta
            (convexHull ℝ (Set.range v)))).toReal) := by
    have hevent : ∀ᶠ n in atTop,
        ∀ i : Fin 8, dist (u n i) (v i) ≤ delta / 2 := by
      have hall : ∀ i ∈ (Finset.univ : Finset (Fin 8)),
          ∀ᶠ n in atTop, dist (u n i) (v i) < delta / 2 := by
        intro i hi
        have hi_lim : Tendsto (fun n => u n i) atTop (𝓝 (v i)) :=
          tendsto_pi_nhds.mp hlim i
        have hball : Metric.ball (v i) (delta / 2) ∈ 𝓝 (v i) :=
          Metric.ball_mem_nhds _ (by linarith)
        simpa only [Metric.mem_ball, dist_comm] using
          hi_lim.eventually hball
      rw [← Finset.eventually_all] at hall
      filter_upwards [hall] with n hn
      intro i
      exact (hn i (Finset.mem_univ i)).le
    have hevent_bound : ∀ᶠ n in atTop,
        |sig (u n t.1) (u n t.2.1) (u n t.2.2)| ≤
          L * (2 * (MeasureTheory.volume
            (Metric.thickening delta
              (convexHull ℝ (Set.range v)))).toReal) := by
      filter_upwards [hevent] with n hn
      exact (hu n).trans (mul_le_mul_of_nonneg_left
        (doubledHullArea_le_thickening_of_uniformDist v (u n)
          (by linarith) hn) hL)
    exact le_of_tendsto hsig hevent_bound
  have hcompact := finite_range_isCompact_convexHull v
  have hfinite : ∃ R > 0,
      MeasureTheory.volume
        (Metric.thickening R (convexHull ℝ (Set.range v))) ≠ ⊤ :=
    ⟨1, zero_lt_one,
      hcompact.isBounded.thickening.measure_lt_top.ne⟩
  have hmeasure := tendsto_measure_thickening_of_isClosed
    hfinite hcompact.isClosed
  have hreal :=
    (ENNReal.tendsto_toReal (volume_convexHull_ne_top v)).comp hmeasure
  have hscaled : Tendsto
      (fun delta => L * (2 * (MeasureTheory.volume
        (Metric.thickening delta
          (convexHull ℝ (Set.range v)))).toReal))
      (𝓝[>] (0 : ℝ))
      (𝓝 (L * doubledHullArea v)) := by
    simpa only [doubledHullArea, Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hreal)
  change |sig (v t.1) (v t.2.1) (v t.2.2)| ≤ L * doubledHullArea v
  apply ge_of_tendsto hscaled
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact hbound delta hdelta

/-- Some one of the 56 increasing triples is small at level `L`. -/
def HasSmallTriangle (L : ℝ) (v : Configuration) : Prop :=
  ∃ t ∈ triples,
    |sig (v t.1) (v t.2.1) (v t.2.2)| ≤ L * doubledHullArea v

/-- The finite union over the 56 possible witnesses is closed. This is the
fixed-witness subsequence argument in closed-set form. -/
lemma hasSmallTriangle_isClosed (L : ℝ) (hL : 0 ≤ L) :
    IsClosed {v : Configuration | HasSmallTriangle L v} := by
  have hclosed : IsClosed
      (⋃ t ∈ triples, {v : Configuration |
        |sig (v t.1) (v t.2.1) (v t.2.2)| ≤
          L * doubledHullArea v}) := by
    apply isClosed_biUnion_finset
    intro t ht
    exact triangleWitnessSet_isClosed L hL t
  convert hclosed using 1
  ext v
  simp only [HasSmallTriangle, Set.mem_ofPred_eq, Set.mem_iUnion,
    exists_prop]

/-- Real-level form of the density theorem. Its coverage hypothesis ranges
over every strict-order point of the root, not merely a selected collection
of strict terminal boxes. -/
theorem orderDensity_real
    (R : Set Configuration) (hR : Convex ℝ R)
    (L : ℝ) (hL : 0 ≤ L)
    (hstrictNonempty : (StrictOrderRegion R).Nonempty)
    (hstrictCoverage : ∀ v ∈ StrictOrderRegion R,
      HasSmallTriangle L v) :
    ∀ p ∈ WeakOrderRegion R, HasSmallTriangle L p := by
  intro p hp
  have hpclosure :=
    weakOrderRegion_subset_closure_strictOrderRegion hR hstrictNonempty hp
  have hsubset : StrictOrderRegion R ⊆
      {v : Configuration | HasSmallTriangle L v} := by
    intro v hv
    exact hstrictCoverage v hv
  exact (closure_minimal hsubset (hasSmallTriangle_isClosed L hL)) hpclosure

/-- Rational per-certificate form of the exact order-density obligation. -/
theorem orderDensity
    (R : Set Configuration) (hR : Convex ℝ R)
    (L : ℚ) (hL : 0 ≤ L)
    (hstrictNonempty : (StrictOrderRegion R).Nonempty)
    (hstrictCoverage : ∀ v ∈ StrictOrderRegion R,
      HasSmallTriangle (L : ℝ) v) :
    ∀ p ∈ WeakOrderRegion R, HasSmallTriangle (L : ℝ) p := by
  exact orderDensity_real R hR (L : ℝ)
    (by exact_mod_cast hL) hstrictNonempty hstrictCoverage

/-- Adapter used by the survivor assembly: a non-strict small-triangle
witness contradicts the strict orientation of `Beats`. -/
lemma HasSmallTriangle.not_Beats
    {L : ℝ} {v : Configuration} (h : HasSmallTriangle L v) :
    ¬ Beats doubledHullArea L v := by
  rintro ⟨_harea, hbeat⟩
  rcases h with ⟨t, ht, hsmall⟩
  have hmin : minTri v ≤
      |sig (v t.1) (v t.2.1) (v t.2.2)| := by
    unfold minTri
    exact Finset.inf'_le _ ht
  exact (not_lt_of_ge (hmin.trans hsmall)) hbeat

#print axioms orderSegment_mem_strictOrderRegion
#print axioms doubledHullArea_upperSemicontinuous
#print axioms hasSmallTriangle_isClosed
#print axioms orderDensity
#print axioms HasSmallTriangle.not_Beats

end Heilbronn8
