import Heilbronn8.OrderDensity
import Heilbronn8.ReferenceQuotient
import Heilbronn8.ConvexSigBound

open Filter Set
open scoped Topology

/-!
# Order density without convexity

`orderDensity` asks the caller for `Convex ℝ R`, and every `RootGeometry` and
`ClosedRoot` carries that field.  For the region that actually makes
`strictCovered` true the field is false: the terminals cover a sixteenth of the
largest root box, so `R` cannot be the root box, and the region carved out by the
branch sign conditions is cut by multilinear orientation polynomials rather than
half-spaces.

Convexity is used in exactly one step, `weakOrderRegion_subset_closure_strictOrderRegion`,
to conclude that every weakly ordered point is a limit of strictly ordered ones.
That conclusion is strictly weaker than convexity and is what the argument needs,
so it is taken as the hypothesis here.  `orderDensity_of_convex` re-derives the
old statement from the new one, which is what makes this a retyping rather than a
change of theorem.
-/

namespace Heilbronn8

/-- Every weakly ordered point of `R` is a limit of strictly ordered points of
`R`.  Convexity implies this; a sign-carved region can satisfy it directly. -/
def WeakOrderDense (R : Set Configuration) : Prop :=
  WeakOrderRegion R ⊆ closure (StrictOrderRegion R)

/-! ## Global density of the reference-machine domain

The base below deliberately omits the weak x-order.  Intersecting it with
`WeakOrderRegion` recovers `ReferenceMachineDomain`; intersecting it with
`StrictOrderRegion` gives the strict configurations checked by the open-cell
machinery.  This is a global statement, not a density claim inside any one
sign root.
-/

/-- Gauge normalization together with the five reference-quotient chamber
inequalities, before imposing an order on the five free x-coordinates. -/
def ReferenceMachineBase : Set Configuration :=
  {v | GaugeNormalized v ∧ GaugeQuotientChamber v}

theorem mem_weakOrderRegion_referenceMachineBase_iff
    {v : Configuration} :
    v ∈ WeakOrderRegion ReferenceMachineBase ↔ ReferenceMachineDomain v := by
  simp only [WeakOrderRegion, ReferenceMachineBase, WeakXOrder,
    ReferenceMachineDomain, Set.mem_ofPred_eq]
  tauto

/-- A fixed strictly x-ordered configuration inside the reference triangle. -/
noncomputable def referenceOrderAnchor : Configuration :=
  ![((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1),
    (1 / 6, 0), (2 / 6, 0), (3 / 6, 0), (4 / 6, 0), (5 / 6, 0)]

@[simp] lemma referenceOrderAnchor_zero :
    referenceOrderAnchor 0 = ((0 : ℝ), (0 : ℝ)) := by rfl

@[simp] lemma referenceOrderAnchor_one :
    referenceOrderAnchor 1 = ((1 : ℝ), (0 : ℝ)) := by rfl

@[simp] lemma referenceOrderAnchor_two :
    referenceOrderAnchor 2 = ((0 : ℝ), (1 : ℝ)) := by rfl

@[simp] lemma referenceOrderAnchor_freeSlot (i : Fin 5) :
    referenceOrderAnchor (freeSlot i) =
      ![((1 / 6 : ℝ), (0 : ℝ)), (2 / 6, 0), (3 / 6, 0),
        (4 / 6, 0), (5 / 6, 0)] i := by
  fin_cases i <;> rfl

private def referenceTriangleVertices : Set (ℝ × ℝ) :=
  {((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)),
    ((0 : ℝ), (1 : ℝ))}

private lemma referenceTriangleVertices_abs_sig
    (x : ℝ × ℝ) (hx : x ∈ referenceTriangleVertices)
    (y : ℝ × ℝ) (hy : y ∈ referenceTriangleVertices)
    (z : ℝ × ℝ) (hz : z ∈ referenceTriangleVertices) :
    |sig x y z| ≤ (1 : ℝ) := by
  simp only [referenceTriangleVertices, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;> norm_num [sig]

private lemma referenceOrderAnchor_mem_referenceTriangle (i : Fin 8) :
    referenceOrderAnchor i ∈ convexHull ℝ referenceTriangleVertices := by
  have hzero : ((0 : ℝ), (0 : ℝ)) ∈ referenceTriangleVertices := by
    simp [referenceTriangleVertices]
  have hone : ((1 : ℝ), (0 : ℝ)) ∈ referenceTriangleVertices := by
    simp [referenceTriangleVertices]
  have htwo : ((0 : ℝ), (1 : ℝ)) ∈ referenceTriangleVertices := by
    simp [referenceTriangleVertices]
  have hedge (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AffineMap.lineMap ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) t ∈
        convexHull ℝ referenceTriangleVertices :=
    segment_subset_convexHull (𝕜 := ℝ) hzero hone
      (lineMap_mem_segment ℝ _ _ ht)
  fin_cases i
  · exact subset_convexHull ℝ _ hzero
  · exact subset_convexHull ℝ _ hone
  · exact subset_convexHull ℝ _ htwo
  · simpa [referenceOrderAnchor, AffineMap.lineMap_apply_module] using
      hedge (1 / 6) (by norm_num)
  · simpa [referenceOrderAnchor, AffineMap.lineMap_apply_module] using
      hedge (2 / 6) (by norm_num)
  · simpa [referenceOrderAnchor, AffineMap.lineMap_apply_module] using
      hedge (3 / 6) (by norm_num)
  · simpa [referenceOrderAnchor, AffineMap.lineMap_apply_module] using
      hedge (4 / 6) (by norm_num)
  · simpa [referenceOrderAnchor, AffineMap.lineMap_apply_module] using
      hedge (5 / 6) (by norm_num)

theorem referenceOrderAnchor_gaugeNormalized :
    GaugeNormalized referenceOrderAnchor := by
  have hhull := abs_sig_le_on_convexHull referenceTriangleVertices (1 : ℝ)
    referenceTriangleVertices_abs_sig
  have hmax : ∀ a b c : Fin 8,
      |sig (referenceOrderAnchor a) (referenceOrderAnchor b)
        (referenceOrderAnchor c)| ≤ 1 := by
    intro a b c
    exact hhull _ (referenceOrderAnchor_mem_referenceTriangle a)
      _ (referenceOrderAnchor_mem_referenceTriangle b)
      _ (referenceOrderAnchor_mem_referenceTriangle c)
  exact ⟨by rfl, by rfl, by rfl, hmax,
    inMaximalityBox_of_normalized referenceOrderAnchor 0 1 2
      (by rfl) (by rfl) (by rfl) hmax⟩

theorem referenceOrderAnchor_strictXOrder :
    StrictXOrder referenceOrderAnchor := by
  intro i j hij
  change (referenceOrderAnchor (freeSlot i)).1 <
    (referenceOrderAnchor (freeSlot j)).1
  rw [referenceOrderAnchor_freeSlot i, referenceOrderAnchor_freeSlot j]
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num

theorem referenceOrderAnchor_chamber :
    GaugeQuotientChamber referenceOrderAnchor := by
  have hx : freeXSum referenceOrderAnchor = (5 / 2 : ℝ) := by
    norm_num [freeXSum, Fin.sum_univ_succ]
  have hy : freeYSum referenceOrderAnchor = (0 : ℝ) := by
    norm_num [freeYSum, Fin.sum_univ_succ]
  norm_num [GaugeQuotientChamber, hx, hy]

theorem referenceOrderAnchor_mem_strictOrderRegion :
    referenceOrderAnchor ∈ StrictOrderRegion ReferenceMachineBase :=
  ⟨⟨referenceOrderAnchor_gaugeNormalized,
      referenceOrderAnchor_chamber⟩,
    referenceOrderAnchor_strictXOrder⟩

/-- Every anchor vertex belongs to the convex hull of any gauge-normalized
configuration: the gauge corners occur in that configuration, and the five
free anchor vertices lie on the bottom reference edge. -/
lemma referenceOrderAnchor_mem_convexHull_range
    (p : Configuration) (hp : GaugeNormalized p) (i : Fin 8) :
    referenceOrderAnchor i ∈ convexHull ℝ (Set.range p) := by
  have hzero : p 0 ∈ Set.range p := ⟨0, rfl⟩
  have hone : p 1 ∈ Set.range p := ⟨1, rfl⟩
  have htwo : p 2 ∈ Set.range p := ⟨2, rfl⟩
  have hedge (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AffineMap.lineMap (p 0) (p 1) t ∈
        convexHull ℝ (Set.range p) :=
    segment_subset_convexHull (𝕜 := ℝ) hzero hone
      (lineMap_mem_segment ℝ (p 0) (p 1) ht)
  fin_cases i
  · simpa [referenceOrderAnchor, hp.map_zero] using
      (subset_convexHull ℝ (Set.range p) hzero)
  · simpa [referenceOrderAnchor, hp.map_one] using
      (subset_convexHull ℝ (Set.range p) hone)
  · simpa [referenceOrderAnchor, hp.map_two] using
      (subset_convexHull ℝ (Set.range p) htwo)
  · have h := hedge (1 / 6) (by norm_num)
    simpa [referenceOrderAnchor, hp.map_zero, hp.map_one,
      AffineMap.lineMap_apply_module] using h
  · have h := hedge (2 / 6) (by norm_num)
    simpa [referenceOrderAnchor, hp.map_zero, hp.map_one,
      AffineMap.lineMap_apply_module] using h
  · have h := hedge (3 / 6) (by norm_num)
    simpa [referenceOrderAnchor, hp.map_zero, hp.map_one,
      AffineMap.lineMap_apply_module] using h
  · have h := hedge (4 / 6) (by norm_num)
    simpa [referenceOrderAnchor, hp.map_zero, hp.map_one,
      AffineMap.lineMap_apply_module] using h
  · have h := hedge (5 / 6) (by norm_num)
    simpa [referenceOrderAnchor, hp.map_zero, hp.map_one,
      AffineMap.lineMap_apply_module] using h

/-- The free-coordinate sums are affine along `orderSegment`. -/
lemma freeXSum_orderSegment (p z : Configuration) (t : ℝ) :
    freeXSum (orderSegment p z t) =
      (1 - t) * freeXSum p + t * freeXSum z := by
  simp only [freeXSum, orderSegment, Pi.add_apply, Pi.smul_apply,
    Prod.smul_fst, Prod.fst_add, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]

lemma freeYSum_orderSegment (p z : Configuration) (t : ℝ) :
    freeYSum (orderSegment p z t) =
      (1 - t) * freeYSum p + t * freeYSum z := by
  simp only [freeYSum, orderSegment, Pi.add_apply, Pi.smul_apply,
    Prod.smul_snd, Prod.snd_add, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]

/-- The quotient chamber is closed under ordinary line segments. -/
lemma GaugeQuotientChamber.orderSegment
    {p z : Configuration} (hp : GaugeQuotientChamber p)
    (hz : GaugeQuotientChamber z) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    GaugeQuotientChamber (orderSegment p z t) := by
  rw [GaugeQuotientChamber,
    freeXSum_orderSegment, freeYSum_orderSegment]
  rcases hp with ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩
  rcases hz with ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Interpolation toward the fixed anchor preserves gauge normalization.
The maximality proof puts every interpolated vertex in `convexHull (range p)`
and then invokes the separate-affinity signed-area bound. -/
lemma GaugeNormalized.orderSegment_referenceOrderAnchor
    {p : Configuration} (hp : GaugeNormalized p) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    GaugeNormalized (orderSegment p referenceOrderAnchor t) := by
  have hzero :
      orderSegment p referenceOrderAnchor t 0 = ((0 : ℝ), (0 : ℝ)) := by
    change (1 - t) • p 0 + t • referenceOrderAnchor 0 = _
    rw [hp.map_zero]
    simp
  have hone :
      orderSegment p referenceOrderAnchor t 1 = ((1 : ℝ), (0 : ℝ)) := by
    change (1 - t) • p 1 + t • referenceOrderAnchor 1 = _
    rw [hp.map_one]
    ext <;> simp
  have htwo :
      orderSegment p referenceOrderAnchor t 2 = ((0 : ℝ), (1 : ℝ)) := by
    change (1 - t) • p 2 + t • referenceOrderAnchor 2 = _
    rw [hp.map_two]
    ext <;> simp
  have hsource : ∀ x ∈ Set.range p, ∀ y ∈ Set.range p,
      ∀ z ∈ Set.range p, |sig x y z| ≤ (1 : ℝ) := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ z ⟨c, rfl⟩
    exact hp.maximal a b c
  have hhull := abs_sig_le_on_convexHull (Set.range p) (1 : ℝ) hsource
  have hpoint (i : Fin 8) :
      orderSegment p referenceOrderAnchor t i ∈
        convexHull ℝ (Set.range p) := by
    have hp_mem : p i ∈ convexHull ℝ (Set.range p) :=
      subset_convexHull ℝ (Set.range p) ⟨i, rfl⟩
    have hz_mem := referenceOrderAnchor_mem_convexHull_range p hp i
    have hline := (convex_convexHull ℝ (Set.range p)).lineMap_mem
      hp_mem hz_mem ⟨ht0, ht1⟩
    change (1 - t) • p i + t • referenceOrderAnchor i ∈
      convexHull ℝ (Set.range p)
    simpa only [AffineMap.lineMap_apply_module] using hline
  have hmax : ∀ a b c : Fin 8,
      |sig (orderSegment p referenceOrderAnchor t a)
        (orderSegment p referenceOrderAnchor t b)
        (orderSegment p referenceOrderAnchor t c)| ≤ 1 := by
    intro a b c
    exact hhull _ (hpoint a) _ (hpoint b) _ (hpoint c)
  exact ⟨hzero, hone, htwo, hmax,
    inMaximalityBox_of_normalized
      (orderSegment p referenceOrderAnchor t) 0 1 2
      hzero hone htwo hmax⟩

/-- Every positive segment step from a weakly ordered global machine point
toward the anchor is strictly ordered and remains in the global base. -/
lemma orderSegment_mem_strictReferenceMachineBase
    {p : Configuration}
    (hp : p ∈ WeakOrderRegion ReferenceMachineBase)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    orderSegment p referenceOrderAnchor t ∈
      StrictOrderRegion ReferenceMachineBase := by
  constructor
  · exact ⟨hp.1.1.orderSegment_referenceOrderAnchor ht0.le ht1,
      hp.1.2.orderSegment referenceOrderAnchor_chamber ht0.le ht1⟩
  · intro i j hij
    have hpij := hp.2 hij.le
    have hzij := referenceOrderAnchor_strictXOrder hij
    dsimp [StrictXOrder, WeakXOrder, orderSegment, xCoordsOf] at hpij hzij ⊢
    nlinarith

/-- The whole reference-machine base has dense strict x-order.  No assertion
is made here about retaining a survivor root or an orientation-sign cell. -/
theorem referenceMachineBase_weakOrderDense :
    WeakOrderDense ReferenceMachineBase := by
  intro p hp
  rw [mem_closure_iff_seq_limit]
  let t : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let u : ℕ → Configuration :=
    fun n => orderSegment p referenceOrderAnchor (t n)
  refine ⟨u, ?_, ?_⟩
  · intro n
    exact orderSegment_mem_strictReferenceMachineBase hp
      (by dsimp [t]; positivity)
      (by
        dsimp [t]
        simpa using
          (Nat.one_div_le_one_div (α := ℝ) (Nat.zero_le n)))
  · have ht : Tendsto t atTop (nhds 0) := by
      simpa only [t] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcontinuous : Continuous
        (fun r : ℝ => orderSegment p referenceOrderAnchor r) := by
      unfold orderSegment
      fun_prop
    have hu := hcontinuous.continuousAt.tendsto.comp ht
    simpa only [u, Function.comp_def, orderSegment, sub_zero,
      one_smul, zero_smul, add_zero] using hu

theorem weakOrderDense_of_convex {R : Set Configuration} (hR : Convex ℝ R)
    (hstrictNonempty : (StrictOrderRegion R).Nonempty) :
    WeakOrderDense R :=
  weakOrderRegion_subset_closure_strictOrderRegion hR hstrictNonempty

/-! ## The density theorem on the hypothesis it uses

`hstrictNonempty` is gone: it existed only to build the approximating sequence
out of convexity, and the density hypothesis already carries that. -/

theorem orderDensity_real_of_dense
    (R : Set Configuration) (hdense : WeakOrderDense R)
    (L : ℝ) (hL : 0 ≤ L)
    (hstrictCoverage : ∀ v ∈ StrictOrderRegion R, HasSmallTriangle L v) :
    ∀ p ∈ WeakOrderRegion R, HasSmallTriangle L p := by
  intro p hp
  have hsubset : StrictOrderRegion R ⊆
      {v : Configuration | HasSmallTriangle L v} := hstrictCoverage
  exact (closure_minimal hsubset (hasSmallTriangle_isClosed L hL)) (hdense hp)

theorem orderDensity_of_dense
    (R : Set Configuration) (hdense : WeakOrderDense R)
    (L : ℚ) (hL : 0 ≤ L)
    (hstrictCoverage : ∀ v ∈ StrictOrderRegion R,
      HasSmallTriangle (L : ℝ) v) :
    ∀ p ∈ WeakOrderRegion R, HasSmallTriangle (L : ℝ) p :=
  orderDensity_real_of_dense R hdense (L : ℝ) (by exact_mod_cast hL) hstrictCoverage

/-! ## The convexity form is a corollary

Nothing downstream has to change at once: a root that really does carry a convex
region keeps working through this route. -/

theorem orderDensity_of_convex
    (R : Set Configuration) (hR : Convex ℝ R)
    (L : ℚ) (hL : 0 ≤ L)
    (hstrictNonempty : (StrictOrderRegion R).Nonempty)
    (hstrictCoverage : ∀ v ∈ StrictOrderRegion R,
      HasSmallTriangle (L : ℝ) v) :
    ∀ p ∈ WeakOrderRegion R, HasSmallTriangle (L : ℝ) p :=
  orderDensity_of_dense R (weakOrderDense_of_convex hR hstrictNonempty) L hL
    hstrictCoverage

#print axioms weakOrderDense_of_convex
#print axioms orderDensity_real_of_dense
#print axioms orderDensity_of_dense
#print axioms orderDensity_of_convex

end Heilbronn8
