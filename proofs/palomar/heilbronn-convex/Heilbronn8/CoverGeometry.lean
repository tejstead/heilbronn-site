import Heilbronn8.Gauge
import Heilbronn8.HullArea
import Heilbronn8.Collinear

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Heilbronn8

abbrev Configuration := Fin 8 -> Prod Real Real

noncomputable def areaRatio
    (H : Configuration -> Real) (v : Configuration) : Real :=
  minTri v / H v

/-- A configuration beats `q` exactly when its positive-area ratio exceeds `q`. -/
def Beats
    (H : Configuration -> Real) (q : Real) (v : Configuration) : Prop :=
  0 < H v ∧ q * H v < minTri v

/-! ## WLOG layer -/

/-- Both the absolute signed areas and their finite minimum scale by `T.det`. -/
lemma minTri_posAffine (T : PosAffine) (v : Configuration) :
    minTri (fun i => T.map (v i)) = T.det * minTri v := by
  apply le_antisymm
  · obtain ⟨t, ht, hmin⟩ :=
      Finset.exists_mem_eq_inf' triples_nonempty
        (fun t : Prod (Fin 8) (Prod (Fin 8) (Fin 8)) =>
          |sig (v t.1) (v t.2.1) (v t.2.2)|)
    calc
      minTri (fun i => T.map (v i))
          <= |sig (T.map (v t.1)) (T.map (v t.2.1))
              (T.map (v t.2.2))| := by
            unfold minTri
            exact Finset.inf'_le _ ht
      _ = T.det * |sig (v t.1) (v t.2.1) (v t.2.2)| := by
            rw [sig_posAffine, abs_mul, abs_of_pos T.det_pos']
      _ = T.det * minTri v := by
            rw [← hmin]
            rfl
  · apply le_minTri
    intro i j k hij hjk
    rw [sig_posAffine, abs_mul, abs_of_pos T.det_pos']
    exact
      mul_le_mul_of_nonneg_left
        (minTri_le v hij hjk) T.det_pos'.le

/--
If `H` has the same positive-affine scaling law as doubled area, then
`minTri / H` is invariant. The future hull-area bridge supplies `hH`.
-/
lemma areaRatio_posAffine
    (H : Configuration -> Real)
    (hH : ∀ (T : PosAffine) (v : Configuration),
      H (fun i => T.map (v i)) = T.det * H v)
    (T : PosAffine) (v : Configuration) :
    areaRatio H (fun i => T.map (v i)) = areaRatio H v := by
  simp only [areaRatio, minTri_posAffine, hH]
  exact mul_div_mul_left _ _ (ne_of_gt T.det_pos')

/-- `minTri` also bounds a triple presented in any ordering. -/
lemma minTri_le_abs_sig_of_pairwise_ne (v : Configuration)
    {a b c : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    minTri v <= |sig (v a) (v b) (v c)| := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
    · exact minTri_le v hablt hbclt
    · rcases lt_or_gt_of_ne hac with haclt | hcalt
      · calc
          minTri v <= |sig (v a) (v c) (v b)| :=
            minTri_le v haclt hcblt
          _ = |sig (v a) (v b) (v c)| := by
            rw [sig_swap, abs_neg]
      · calc
          minTri v <= |sig (v c) (v a) (v b)| :=
            minTri_le v hcalt hablt
          _ = |sig (v a) (v b) (v c)| := by
            rw [sig_rotate, sig_rotate]
  · rcases lt_or_gt_of_ne hac with haclt | hcalt
    · calc
        minTri v <= |sig (v b) (v a) (v c)| :=
          minTri_le v hbalt haclt
        _ = |sig (v a) (v b) (v c)| := by
          have heq :
              sig (v a) (v b) (v c) =
                -sig (v b) (v a) (v c) := by
            simp only [sig]
            ring1
          rw [heq, abs_neg]
    · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
      · calc
          minTri v <= |sig (v b) (v c) (v a)| :=
            minTri_le v hbclt hcalt
          _ = |sig (v a) (v b) (v c)| := by
            rw [← sig_rotate]
      · calc
          minTri v <= |sig (v c) (v b) (v a)| :=
            minTri_le v hcblt hbalt
          _ = |sig (v a) (v b) (v c)| := by
            have heq :
                sig (v a) (v b) (v c) =
                  -sig (v c) (v b) (v a) := by
              simp only [sig]
              ring1
            rw [heq, abs_neg]

/-- Coincident labelled points are routed to the zero-minimum branch. -/
lemma minTri_eq_zero_of_coincident (v : Configuration)
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcoincident : v i = v j) : minTri v = 0 := by
  have hsig : sig (v i) (v j) (v k) = 0 := by
    rw [hcoincident]
    simp [sig]
  apply le_antisymm
  · calc
      minTri v ≤ |sig (v i) (v j) (v k)| :=
        minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
      _ = 0 := by rw [hsig, abs_zero]
  · exact minTri_nonneg v

/-- The degenerate arm of the top-level dispatcher is below every
nonnegative target, independently of the hull functional. -/
lemma areaRatio_le_of_hasZeroTriple
    (H : Configuration → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (v : Configuration) (hzero : HasZeroTriple v) :
    areaRatio H v ≤ q := by
  rw [areaRatio, minTri_eq_zero_of_hasZeroTriple v hzero, zero_div]
  exact hq

/-- A zero triple cannot be a strict beating configuration at a
nonnegative target. -/
lemma not_Beats_of_hasZeroTriple
    (H : Configuration → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (v : Configuration) (hzero : HasZeroTriple v) :
    ¬ Beats H q v := by
  rintro ⟨hH, hbeat⟩
  have hratio := areaRatio_le_of_hasZeroTriple H hq v hzero
  rw [areaRatio, div_le_iff₀ hH] at hratio
  exact (not_lt_of_ge hratio) hbeat

lemma minTri_le_relabel
    (v : Configuration) (sigma : Equiv.Perm (Fin 8)) :
    minTri v <= minTri (fun i => v (sigma i)) := by
  apply le_minTri
  intro i j k hij hjk
  apply minTri_le_abs_sig_of_pairwise_ne v
  · exact sigma.injective.ne (ne_of_lt hij)
  · exact sigma.injective.ne (ne_of_lt (lt_trans hij hjk))
  · exact sigma.injective.ne (ne_of_lt hjk)

lemma minTri_relabel
    (v : Configuration) (sigma : Equiv.Perm (Fin 8)) :
    minTri (fun i => v (sigma i)) = minTri v := by
  apply le_antisymm
  · have h :=
      minTri_le_relabel (fun i => v (sigma i)) sigma.symm
    simpa only [sigma.apply_symm_apply] using h
  · exact minTri_le_relabel v sigma

/--
The normalization consumed by the B&B layer. Slots `0,1,2` are the oriented
maximum-area carrier, not necessarily the original points named `0,1,2`.
-/
structure GaugeNormalized (v : Configuration) : Prop where
  map_zero : v 0 = (0, 0)
  map_one : v 1 = (1, 0)
  map_two : v 2 = (0, 1)
  maximal : ∀ a b c : Fin 8, |sig (v a) (v b) (v c)| <= 1
  box : ∀ i : Fin 8, InMaximalityBox (v i)

lemma maxGauge_slots_injective {v : Configuration} (g : MaxGauge v) :
    Function.Injective ![g.A, g.B, g.C] := by
  have hAB : g.A ≠ g.B := by
    rcases g.oriented_order with
      ⟨hA, hB, _⟩ | ⟨hA, hB, _⟩
    · rw [hA, hB]
      exact ne_of_lt g.hij
    · rw [hA, hB]
      exact ne_of_lt (lt_trans g.hij g.hjk)
  have hAC : g.A ≠ g.C := by
    rcases g.oriented_order with
      ⟨hA, _, hC⟩ | ⟨hA, _, hC⟩
    · rw [hA, hC]
      exact ne_of_lt (lt_trans g.hij g.hjk)
    · rw [hA, hC]
      exact ne_of_lt g.hij
  have hBC : g.B ≠ g.C := by
    rcases g.oriented_order with
      ⟨_, hB, hC⟩ | ⟨_, hB, hC⟩
    · rw [hB, hC]
      exact ne_of_lt g.hjk
    · rw [hB, hC]
      exact ne_of_gt g.hjk
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/--
Extend `0,1,2 ↦ g.A,g.B,g.C` to a permutation before applying the gauge.
This is the slotting step missing if one assumes the maximum triple was
already named `0,1,2`.
-/
lemma maxGauge_relabel {v : Configuration} (g : MaxGauge v) :
    ∃ sigma : Equiv.Perm (Fin 8),
      (∀ s : Fin 3,
        sigma (Fin.castAdd 5 s) = ![g.A, g.B, g.C] s) ∧
      GaugeNormalized (fun i => g.T.map (v (sigma i))) := by
  obtain ⟨sigma, hsigma⟩ :=
    Equiv.Perm.exists_extending_pair
      (fun s : Fin 3 => Fin.castAdd 5 s)
      ![g.A, g.B, g.C]
      (Fin.castAddEmb 5).injective
      (maxGauge_slots_injective g)
  refine ⟨sigma, hsigma, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change
      g.T.map (v (sigma (Fin.castAdd 5 (0 : Fin 3)))) = (0, 0)
    rw [hsigma]
    exact g.map_A
  · change
      g.T.map (v (sigma (Fin.castAdd 5 (1 : Fin 3)))) = (1, 0)
    rw [hsigma]
    exact g.map_B
  · change
      g.T.map (v (sigma (Fin.castAdd 5 (2 : Fin 3)))) = (0, 1)
    rw [hsigma]
    exact g.map_C
  · intro a b c
    exact g.transformed_bound (sigma a) (sigma b) (sigma c)
  · intro i
    exact g.box (sigma i)

lemma areaRatio_relabel
    (H : Configuration -> Real)
    (hH : ∀ (v : Configuration) (sigma : Equiv.Perm (Fin 8)),
      H (fun i => v (sigma i)) = H v)
    (v : Configuration) (sigma : Equiv.Perm (Fin 8)) :
    areaRatio H (fun i => v (sigma i)) = areaRatio H v := by
  simp only [areaRatio, minTri_relabel, hH]

/-- A positive-area, noncollinear configuration has a gauge-normalized
representative with the same abstract area ratio. -/
lemma exists_gaugeRepresentative
    (H : Configuration → Real)
    (hHaffine : ∀ (T : PosAffine) (v : Configuration),
      H (fun i ↦ T.map (v i)) = T.det * H v)
    (hHrelabel : ∀ (v : Configuration)
      (sigma : Equiv.Perm (Fin 8)),
      H (fun i ↦ v (sigma i)) = H v)
    (v : Configuration) (hHv : 0 < H v) (hnc : NotAllCollinear v) :
    ∃ u : Configuration,
      GaugeNormalized u ∧ 0 < H u ∧ areaRatio H u = areaRatio H v := by
  obtain ⟨g⟩ := exists_maxGauge v hnc
  obtain ⟨sigma, _hsigma, hu⟩ := maxGauge_relabel g
  let w : Configuration := fun i ↦ g.T.map (v i)
  let u : Configuration := fun i ↦ w (sigma i)
  have hHw : 0 < H w := by
    rw [hHaffine]
    exact mul_pos g.T.det_pos' hHv
  have hHu : 0 < H u := by
    rw [hHrelabel]
    exact hHw
  refine ⟨u, hu, hHu, ?_⟩
  calc
    areaRatio H u = areaRatio H w :=
      areaRatio_relabel H hHrelabel w sigma
    _ = areaRatio H v := areaRatio_posAffine H hHaffine g.T v

/-- The actual convex hull supplies every hypothesis of the abstract gauge
representative theorem. -/
lemma exists_doubledHullArea_gaugeRepresentative
    (v : Configuration) (harea : 0 < doubledHullArea v) :
    ∃ u : Configuration,
      GaugeNormalized u ∧ 0 < doubledHullArea u ∧
        areaRatio doubledHullArea u = areaRatio doubledHullArea v :=
  exists_gaugeRepresentative doubledHullArea
    doubledHullArea_posAffine doubledHullArea_relabel v harea
    (notAllCollinear_of_doubledHullArea_pos v harea)

/-- A unit-hull configuration therefore has a machine-domain representative
whose ratio is its ordinary minimum triangle area. -/
lemma doubledHullArea_normalizedRepresentative
    (v : Configuration)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1) :
    ∃ u : Configuration,
      GaugeNormalized u ∧ 0 < doubledHullArea u ∧
        areaRatio doubledHullArea u = minTri v / 2 := by
  have harea : doubledHullArea v = 2 :=
    doubledHullArea_eq_two_of_volume_one hvolume
  obtain ⟨u, hu, hupos, hratio⟩ :=
    exists_doubledHullArea_gaugeRepresentative v (by linarith)
  refine ⟨u, hu, hupos, ?_⟩
  rw [hratio, areaRatio, harea]

/--
Reduction of the global ratio bound to gauge-normalized configurations.

The future hull-area layer supplies `hHaffine` and `hHrelabel`. The
collinear case exits through `minTri_eq_zero_of_sig_zero`.
-/
lemma gauge_wlog
    (H : Configuration -> Real)
    (hHaffine : ∀ (T : PosAffine) (v : Configuration),
      H (fun i => T.map (v i)) = T.det * H v)
    (hHrelabel : ∀ (v : Configuration)
      (sigma : Equiv.Perm (Fin 8)),
      H (fun i => v (sigma i)) = H v)
    (q : Real) (hq : 0 <= q)
    (hnormalized : ∀ u : Configuration,
      GaugeNormalized u -> 0 < H u -> areaRatio H u <= q)
    (v : Configuration) (hHv : 0 < H v) :
    areaRatio H v <= q := by
  by_cases hnc : NotAllCollinear v
  · obtain ⟨u, hu, hHu, hratio⟩ :=
      exists_gaugeRepresentative H hHaffine hHrelabel v hHv hnc
    rw [← hratio]
    exact hnormalized u hu hHu
  · have hzero : sig (v 0) (v 1) (v 2) = 0 := by
      by_contra h
      apply hnc
      exact ⟨0, 1, 2, by decide, by decide, h⟩
    have hmin : minTri v = 0 :=
      minTri_eq_zero_of_sig_zero
        v hzero (by decide) (by decide)
    simp [areaRatio, hmin, hq]

/-- Concrete composition of the arbitrary convex-hull bridge with
`gauge_wlog`. -/
lemma doubledHullArea_gauge_wlog
    (q : Real) (hq : 0 ≤ q)
    (hnormalized : ∀ u : Configuration,
      GaugeNormalized u → 0 < doubledHullArea u →
        areaRatio doubledHullArea u ≤ q)
    (v : Configuration) (harea : 0 < doubledHullArea v) :
    areaRatio doubledHullArea v ≤ q :=
  gauge_wlog doubledHullArea doubledHullArea_posAffine
    doubledHullArea_relabel q hq hnormalized v harea

/-- Inclusion of the five free slots `3,...,7`. -/
def freeSlot : Fin 5 ↪ Fin 8 where
  toFun i := Fin.natAdd 3 i
  inj' := by
    intro a b h
    exact (Fin.natAdd_inj 3).mp h

/-- The symmetric linear functional used by `bnb_pilot_codex3.py`. -/
noncomputable def pilotFunctional (v : Configuration) : Real :=
  ∑ i : Fin 5,
    ((2 : Real) * (v (freeSlot i)).1 +
      5 * (v (freeSlot i)).2)

/--
Relabel the five free slots into nondecreasing x-order while fixing the three
gauge slots pointwise. Hence it also fixes them setwise.
-/
lemma exists_sorted_x_relabel
    (H : Configuration -> Real)
    (hHrelabel : ∀ (v : Configuration)
      (sigma : Equiv.Perm (Fin 8)),
      H (fun i => v (sigma i)) = H v)
    (v : Configuration) (hv : GaugeNormalized v) :
    ∃ sigma : Equiv.Perm (Fin 8),
      (∀ i : Fin 8, i.val < 3 -> sigma i = i) ∧
      GaugeNormalized (fun i => v (sigma i)) ∧
      Monotone
        (fun i : Fin 5 => (v (sigma (freeSlot i))).1) ∧
      areaRatio H (fun i => v (sigma i)) =
        areaRatio H v := by
  let key : Fin 5 -> Real :=
    fun i => (v (freeSlot i)).1
  let tau : Equiv.Perm (Fin 5) := Tuple.sort key
  let sigma : Equiv.Perm (Fin 8) :=
    tau.viaFintypeEmbedding freeSlot
  have hfix :
      ∀ i : Fin 8, i.val < 3 -> sigma i = i := by
    intro i hi
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨j, hj⟩
    have hvj := congrArg Fin.val hj
    change 3 + j.val = i.val at hvj
    omega
  have hnorm :
      GaugeNormalized (fun i => v (sigma i)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hfix 0 (by decide)]
      exact hv.map_zero
    · rw [hfix 1 (by decide)]
      exact hv.map_one
    · rw [hfix 2 (by decide)]
      exact hv.map_two
    · intro a b c
      exact hv.maximal (sigma a) (sigma b) (sigma c)
    · intro i
      exact hv.box (sigma i)
  refine
    ⟨sigma, hfix, hnorm, ?_,
      areaRatio_relabel H hHrelabel v sigma⟩
  intro i j hij
  have hmono := Tuple.monotone_sort key hij
  simpa only [
    Function.comp_apply, key, sigma, tau, freeSlot,
    Equiv.Perm.viaFintypeEmbedding_apply_image
  ] using hmono

lemma referenceTriangleSymmetry_card :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  norm_num [Fintype.card_perm]

/--
Abstract finite-group quotient lemma. Instantiate `G` with
`Equiv.Perm (Fin 3)`, whose cardinality is six, and `f` with
`pilotFunctional`. Stability of normalization under the reference-triangle
action is supplied by the concrete action module.
-/
theorem exists_orbit_functional_minimizer
    {G X A : Type*}
    [Group G] [Fintype G] [MulAction G X] [LinearOrder A]
    (Normalized : X -> Prop)
    (hstable : ∀ (g : G) (x : X),
      Normalized x -> Normalized (g • x))
    (f : X -> A) (x : X) (hx : Normalized x) :
    ∃ g : G,
      Normalized (g • x) ∧
      ∀ h : G, f (g • x) <= f (h • (g • x)) := by
  obtain ⟨g, _hgmem, hg⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset G)
      (fun h => f (h • x))
      Finset.univ_nonempty
  refine ⟨g, hstable g x hx, fun h => ?_⟩
  simpa only [mul_smul] using
    hg (h * g) (Finset.mem_univ _)

/-! ## Exact x/y gauge coordinates -/

/-- The five free x-coordinates in pilot order: `x₃,...,x₇`. -/
def xCoordsOf (v : Configuration) : Fin 5 -> Real :=
  fun i => (v (freeSlot i)).1

/-- The five free y-coordinates in pilot order: `y₃,...,y₇`. -/
def yCoordsOf (v : Configuration) : Fin 5 -> Real :=
  fun i => (v (freeSlot i)).2

end Heilbronn8
