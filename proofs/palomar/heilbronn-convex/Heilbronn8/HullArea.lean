import Heilbronn8.Attain
import Heilbronn8.Gauge
import Heilbronn8.TriVolume

namespace Heilbronn8

/-! ## The actual hull-area functional

`doubledHullArea` is defined for every configuration, independently of a
combinatorial hull certificate.  The constructors of `IsHullArea` below are
the Layer-3 bridge used by generated sign cells; `volume_of_isHullArea` in
`PolyVolumeGen` proves that a certified fan computes this same convex-hull
volume.
-/

/-- The doubled Lebesgue area of the convex hull of an arbitrary finite
configuration. -/
noncomputable def doubledHullArea (v : Fin 8 → ℝ × ℝ) : ℝ :=
  2 * (MeasureTheory.volume (convexHull ℝ (Set.range v))).toReal

lemma finite_range_isCompact_convexHull (v : Fin 8 → ℝ × ℝ) :
    IsCompact (convexHull ℝ (Set.range v)) :=
  Set.finite_range v |>.isCompact_convexHull ℝ

lemma volume_convexHull_ne_top (v : Fin 8 → ℝ × ℝ) :
    MeasureTheory.volume (convexHull ℝ (Set.range v)) ≠ ⊤ :=
  (finite_range_isCompact_convexHull v).measure_ne_top

lemma doubledHullArea_nonneg (v : Fin 8 → ℝ × ℝ) :
    0 ≤ doubledHullArea v := by
  exact mul_nonneg (by norm_num) ENNReal.toReal_nonneg

/-- The concrete linear part of a positive affine map. -/
noncomputable def PosAffine.linear (T : PosAffine) :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![T.a, T.b; T.c, T.d]

lemma PosAffine.linear_apply (T : PosAffine) (p : ℝ × ℝ) :
    T.linear p =
      (T.a * p.1 + T.b * p.2, T.c * p.1 + T.d * p.2) := by
  rw [PosAffine.linear, Matrix.toLin_finTwoProd_apply]

lemma PosAffine.det_linear (T : PosAffine) :
    LinearMap.det T.linear = T.det := by
  simp [PosAffine.linear, PosAffine.det, Matrix.det_fin_two]

/-- The bundled affine map underlying `PosAffine.map`. -/
noncomputable def PosAffine.affine (T : PosAffine) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  T.linear.toAffineMap + AffineMap.const ℝ (ℝ × ℝ) (T.e, T.f)

lemma PosAffine.affine_apply (T : PosAffine) (p : ℝ × ℝ) :
    T.affine p = T.map p := by
  simp [PosAffine.affine, PosAffine.linear_apply, PosAffine.map]

lemma range_posAffine (T : PosAffine) (v : Fin 8 → ℝ × ℝ) :
    Set.range (fun i ↦ T.map (v i)) = T.affine '' Set.range v := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨v i, ⟨i, rfl⟩, T.affine_apply (v i)⟩
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (T.affine_apply (v i)).symm⟩

lemma PosAffine.affine_image_eq (T : PosAffine) (s : Set (ℝ × ℝ)) :
    T.affine '' s =
      (fun x ↦ (T.e, T.f) + x) '' (T.linear '' s) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨T.linear q, ⟨q, hq, rfl⟩, ?_⟩
    rw [T.affine_apply, PosAffine.map, PosAffine.linear_apply]
    ext <;> dsimp <;> ring
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨r, hr, ?_⟩
    rw [T.affine_apply, PosAffine.map, PosAffine.linear_apply]
    ext <;> dsimp <;> ring

lemma volume_convexHull_posAffine (T : PosAffine)
    (v : Fin 8 → ℝ × ℝ) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (fun i ↦ T.map (v i)))) =
      ENNReal.ofReal T.det *
        MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  rw [range_posAffine, ← T.affine.image_convexHull]
  rw [T.affine_image_eq, Set.image_add_left,
    MeasureTheory.measure_preimage_add]
  rw [MeasureTheory.Measure.addHaar_image_linearMap, T.det_linear,
    abs_of_pos T.det_pos']

/-- Convex-hull area has the same determinant scaling law as every triangle. -/
lemma doubledHullArea_posAffine (T : PosAffine)
    (v : Fin 8 → ℝ × ℝ) :
    doubledHullArea (fun i ↦ T.map (v i)) =
      T.det * doubledHullArea v := by
  rw [doubledHullArea, volume_convexHull_posAffine,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal T.det_pos'.le,
    doubledHullArea]
  ring

lemma range_relabel (v : Fin 8 → ℝ × ℝ)
    (sigma : Equiv.Perm (Fin 8)) :
    Set.range (fun i ↦ v (sigma i)) = Set.range v := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨sigma i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨sigma.symm i, by simp⟩

/-- Convex-hull area is independent of point labels. -/
lemma doubledHullArea_relabel (v : Fin 8 → ℝ × ℝ)
    (sigma : Equiv.Perm (Fin 8)) :
    doubledHullArea (fun i ↦ v (sigma i)) = doubledHullArea v := by
  simp only [doubledHullArea, range_relabel v sigma]

lemma doubledHullArea_eq_two_of_volume_one
    {v : Fin 8 → ℝ × ℝ}
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1) :
    doubledHullArea v = 2 := by
  simp [doubledHullArea, hvolume]

/-- Every triangle spanned by the configuration lies in its convex hull, so
its doubled area is at most the doubled hull area. -/
lemma abs_sig_le_doubledHullArea (v : Fin 8 → ℝ × ℝ)
    (i j k : Fin 8) :
    |sig (v i) (v j) (v k)| ≤ doubledHullArea v := by
  have hsubset :
      convexHull ℝ {v i, v j, v k} ⊆
        convexHull ℝ (Set.range v) := by
    apply convexHull_mono
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff,
      Set.mem_range]
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩⟩
  have hmeasure :
      MeasureTheory.volume (convexHull ℝ {v i, v j, v k}) ≤
        MeasureTheory.volume (convexHull ℝ (Set.range v)) :=
    MeasureTheory.measure_mono hsubset
  have hreal := ENNReal.toReal_mono (volume_convexHull_ne_top v) hmeasure
  rw [volume_convexHull_triple,
    ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (by norm_num))] at hreal
  rw [doubledHullArea]
  linarith

lemma minTri_le_doubledHullArea (v : Fin 8 → ℝ × ℝ) :
    minTri v ≤ doubledHullArea v :=
  le_trans (minTri_le v (by decide : (0 : Fin 8) < 1) (by decide : (1 : Fin 8) < 2))
    (abs_sig_le_doubledHullArea v 0 1 2)

private lemma sig_swap_left (p q r : ℝ × ℝ) :
    sig q p r = -sig p q r := by
  simp only [sig]
  ring

private lemma sig_reverse (p q r : ℝ × ℝ) :
    sig r q p = -sig p q r := by
  simp only [sig]
  ring

/-- A nonzero signed area in any labeling order supplies the increasing
triple required by `NotAllCollinear`. -/
lemma notAllCollinear_of_sig_ne_zero (v : Fin 8 → ℝ × ℝ)
    {a b c : Fin 8} (h : sig (v a) (v b) (v c) ≠ 0) :
    NotAllCollinear v := by
  have hab : a ≠ b := by
    rintro rfl
    simp [sig] at h
  have hac : a ≠ c := by
    rintro rfl
    simp [sig] at h
  have hbc : b ≠ c := by
    rintro rfl
    simp [sig] at h
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
    · exact ⟨a, b, c, hablt, hbclt, h⟩
    · rcases lt_or_gt_of_ne hac with haclt | hcalt
      · refine ⟨a, c, b, haclt, hcblt, ?_⟩
        rw [sig_swap]
        exact neg_ne_zero.mpr h
      · refine ⟨c, a, b, hcalt, hablt, ?_⟩
        rwa [← sig_rotate, ← sig_rotate]
  · rcases lt_or_gt_of_ne hac with haclt | hcalt
    · refine ⟨b, a, c, hbalt, haclt, ?_⟩
      rw [sig_swap_left]
      exact neg_ne_zero.mpr h
    · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
      · refine ⟨b, c, a, hbclt, hcalt, ?_⟩
        rwa [← sig_rotate]
      · refine ⟨c, b, a, hcblt, hbalt, ?_⟩
        rw [sig_reverse]
        exact neg_ne_zero.mpr h

lemma sig_eq_zero_of_not_notAllCollinear
    (v : Fin 8 → ℝ × ℝ) (h : ¬NotAllCollinear v)
    (a b c : Fin 8) :
    sig (v a) (v b) (v c) = 0 := by
  by_contra hsig
  exact h (notAllCollinear_of_sig_ne_zero v hsig)

private lemma eq_smul_vsub_of_sig_eq_zero
    {a b x : ℝ × ℝ} (hab : a ≠ b) (h : sig a b x = 0) :
    ∃ r : ℝ, x = r • (b -ᵥ a) +ᵥ a := by
  have hcoord : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hab
    apply Prod.ext
    · exact (sub_eq_zero.mp hn.1).symm
    · exact (sub_eq_zero.mp hn.2).symm
  rcases hcoord with hx | hy
  · refine ⟨(x.1 - a.1) / (b.1 - a.1), ?_⟩
    apply Prod.ext
    · dsimp
      field_simp [hx]
      <;> ring
    · dsimp [sig] at h ⊢
      field_simp [hx]
      nlinarith
  · refine ⟨(x.2 - a.2) / (b.2 - a.2), ?_⟩
    apply Prod.ext
    · dsimp [sig] at h ⊢
      field_simp [hy]
      nlinarith
    · dsimp
      field_simp [hy]
      <;> ring

lemma collinear_range_of_not_notAllCollinear
    (v : Fin 8 → ℝ × ℝ) (h : ¬NotAllCollinear v) :
    Collinear ℝ (Set.range v) := by
  apply (collinear_iff_of_mem (k := ℝ) (s := Set.range v)
    (p₀ := v 0) (⟨0, rfl⟩ : v 0 ∈ Set.range v)).2
  by_cases hex : ∃ j : Fin 8, v j ≠ v 0
  · obtain ⟨j, hj⟩ := hex
    refine ⟨v j -ᵥ v 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact eq_smul_vsub_of_sig_eq_zero hj.symm
      (sig_eq_zero_of_not_notAllCollinear v h 0 j i)
  · push_neg at hex
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    refine ⟨0, ?_⟩
    simp [hex i]

lemma affineSpan_range_ne_top_of_not_notAllCollinear
    (v : Fin 8 → ℝ × ℝ) (h : ¬NotAllCollinear v) :
    affineSpan ℝ (Set.range v) ≠ ⊤ := by
  intro htop
  have hcol := collinear_range_of_not_notAllCollinear v h
  have hle := hcol.finrank_le_one
  have hvector : vectorSpan ℝ (Set.range v) = ⊤ := by
    rw [← direction_affineSpan, htop]
    simp
  have hle' := hle
  rw [hvector, finrank_top] at hle'
  norm_num [Module.finrank_prod] at hle'

/-- Positive convex-hull area forces the existence of a noncollinear triple.
This is the arbitrary finite-set hull-existence bridge needed by the gauge. -/
lemma notAllCollinear_of_doubledHullArea_pos
    (v : Fin 8 → ℝ × ℝ) (harea : 0 < doubledHullArea v) :
    NotAllCollinear v := by
  by_contra h
  have hspan := affineSpan_range_ne_top_of_not_notAllCollinear v h
  have hzero :
      MeasureTheory.volume (convexHull ℝ (Set.range v)) = 0 :=
    MeasureTheory.measure_mono_null
      (convexHull_subset_affineSpan (Set.range v))
      (MeasureTheory.Measure.addHaar_affineSubspace
        MeasureTheory.volume (affineSpan ℝ (Set.range v)) hspan)
  rw [doubledHullArea, hzero] at harea
  norm_num at harea

/--
Strict cyclic position, formulated as the existing weak `CyclicPos`
certificate together with exclusion of collinear cyclic triples.
-/
def StrictCyclicPos {m : ℕ} (c : Fin m → Fin 8)
    (v : Fin 8 → ℝ × ℝ) : Prop :=
  CyclicPos c v ∧
    ∀ i j k : Fin m, i < j → j < k →
      sig (v (c i)) (v (c j)) (v (c k)) ≠ 0

lemma StrictCyclicPos.cyclicPos {m : ℕ} {c : Fin m → Fin 8}
    {v : Fin 8 → ℝ × ℝ} (h : StrictCyclicPos c v) :
    CyclicPos c v :=
  h.1

lemma StrictCyclicPos.pos {m : ℕ} {c : Fin m → Fin 8}
    {v : Fin 8 → ℝ × ℝ} (h : StrictCyclicPos c v)
    (i j k : Fin m) (hij : i < j) (hjk : j < k) :
    0 < sig (v (c i)) (v (c j)) (v (c k)) :=
  lt_of_le_of_ne
    (h.1 i j k hij hjk)
    (Ne.symm (h.2 i j k hij hjk))

/--
The consecutive pairs `(1,2), ..., (m-2,m-1)` in the fan based at
cycle vertex zero.
-/
def fanPairs (m : ℕ) [NeZero m] : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun t =>
    (0 : Fin m) < t.1 ∧ t.1.val + 1 = t.2.val

/-- Doubled shoelace area of the cyclic polygon, written as a fan sum. -/
noncomputable def fanSum {m : ℕ} [NeZero m]
    (v : Fin 8 → ℝ × ℝ) (c : Fin m → Fin 8) : ℝ :=
  ∑ t ∈ fanPairs m,
    sig (v (c 0)) (v (c t.1)) (v (c t.2))

/--
Every point not listed by the cycle is contained in a triangle based at
the fan vertex `c 0` whose other two vertices occur later in the cycle.

The two later vertices need not be consecutive: this is exactly the
strength needed to certify containment in the convex polygon and allows
the existing witness `w_interior`, at cycle positions `0,2,5`, to be used
directly. The shoelace sum itself uses the consecutive `fanPairs`.
-/
def FanCovers {m : ℕ} [NeZero m]
    (v : Fin 8 → ℝ × ℝ) (c : Fin m → Fin 8) : Prop :=
  ∀ p : Fin 8, p ∉ Set.range c →
    ∃ i j : Fin m,
      (0 : Fin m) < i ∧ i < j ∧
      InTri (v p) (v (c 0)) (v (c i)) (v (c j))

lemma fanSum_nonneg {m : ℕ} [NeZero m]
    {v : Fin 8 → ℝ × ℝ} {c : Fin m → Fin 8}
    (h : StrictCyclicPos c v) :
    0 ≤ fanSum v c := by
  unfold fanSum
  apply Finset.sum_nonneg
  intro t ht
  simp only [fanPairs, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  exact (h.pos 0 t.1 t.2 ht.1 (by omega)).le

/--
`H` is the doubled area of a certified convex hull cycle.

This is the combinatorial certificate interface used by sign cells.  An
arbitrary configuration already has the actual hull functional
`doubledHullArea` above; no claim is made that a degenerate configuration has
one of these strict cyclic certificates.
-/
inductive IsHullArea (v : Fin 8 → ℝ × ℝ) (H : ℝ) : Prop
  | hull3 (c : Fin 3 → Fin 8) (hc : Function.Injective c)
      (hpos : StrictCyclicPos c v) (hcover : FanCovers v c)
      (hH : H = fanSum v c) :
      IsHullArea v H
  | hull4 (c : Fin 4 → Fin 8) (hc : Function.Injective c)
      (hpos : StrictCyclicPos c v) (hcover : FanCovers v c)
      (hH : H = fanSum v c) :
      IsHullArea v H
  | hull5 (c : Fin 5 → Fin 8) (hc : Function.Injective c)
      (hpos : StrictCyclicPos c v) (hcover : FanCovers v c)
      (hH : H = fanSum v c) :
      IsHullArea v H
  | hull6 (c : Fin 6 → Fin 8) (hc : Function.Injective c)
      (hpos : StrictCyclicPos c v) (hcover : FanCovers v c)
      (hH : H = fanSum v c) :
      IsHullArea v H
  | hull7 (c : Fin 7 → Fin 8) (hc : Function.Injective c)
      (hpos : StrictCyclicPos c v) (hcover : FanCovers v c)
      (hH : H = fanSum v c) :
      IsHullArea v H
  | hull8 (c : Fin 8 → Fin 8) (hc : Function.Injective c)
      (hpos : StrictCyclicPos c v) (hcover : FanCovers v c)
      (hH : H = fanSum v c) :
      IsHullArea v H

lemma IsHullArea_nonneg {v : Fin 8 → ℝ × ℝ} {H : ℝ}
    (h : IsHullArea v H) :
    0 ≤ H := by
  cases h with
  | hull3 c hc hp hcover hH =>
      rw [hH]
      exact fanSum_nonneg hp
  | hull4 c hc hp hcover hH =>
      rw [hH]
      exact fanSum_nonneg hp
  | hull5 c hc hp hcover hH =>
      rw [hH]
      exact fanSum_nonneg hp
  | hull6 c hc hp hcover hH =>
      rw [hH]
      exact fanSum_nonneg hp
  | hull7 c hc hp hcover hH =>
      rw [hH]
      exact fanSum_nonneg hp
  | hull8 c hc hp hcover hH =>
      rw [hH]
      exact fanSum_nonneg hp

lemma hullCycle_injective : Function.Injective hullCycle := by
  decide

set_option maxHeartbeats 500000 in
lemma w_strictHullCyclePos : StrictCyclicPos hullCycle w := by
  refine ⟨w_hullCyclePos, ?_⟩
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp only [Fin.mk_lt_mk] at hij hjk
  all_goals try omega
  · exact hull_sig_w_012_pos.ne'
  · exact hull_sig_w_013_pos.ne'
  · exact hull_sig_w_014_pos.ne'
  · exact hull_sig_w_015_pos.ne'
  · exact hull_sig_w_016_pos.ne'
  · exact hull_sig_w_023_pos.ne'
  · exact hull_sig_w_024_pos.ne'
  · exact hull_sig_w_025_pos.ne'
  · exact hull_sig_w_026_pos.ne'
  · exact hull_sig_w_034_pos.ne'
  · exact hull_sig_w_035_pos.ne'
  · exact hull_sig_w_036_pos.ne'
  · exact hull_sig_w_045_pos.ne'
  · exact hull_sig_w_046_pos.ne'
  · exact hull_sig_w_056_pos.ne'
  · exact hull_sig_w_123_pos.ne'
  · exact hull_sig_w_124_pos.ne'
  · exact hull_sig_w_125_pos.ne'
  · exact hull_sig_w_126_pos.ne'
  · exact hull_sig_w_134_pos.ne'
  · exact hull_sig_w_135_pos.ne'
  · exact hull_sig_w_136_pos.ne'
  · exact hull_sig_w_145_pos.ne'
  · exact hull_sig_w_146_pos.ne'
  · exact hull_sig_w_156_pos.ne'
  · exact hull_sig_w_234_pos.ne'
  · exact hull_sig_w_235_pos.ne'
  · exact hull_sig_w_236_pos.ne'
  · exact hull_sig_w_245_pos.ne'
  · exact hull_sig_w_246_pos.ne'
  · exact hull_sig_w_256_pos.ne'
  · exact hull_sig_w_345_pos.ne'
  · exact hull_sig_w_346_pos.ne'
  · exact hull_sig_w_356_pos.ne'
  · exact hull_sig_w_456_pos.ne'

lemma w_fanCovers : FanCovers w hullCycle := by
  intro p hp
  fin_cases p
  · exact False.elim (hp ⟨3, rfl⟩)
  · exact False.elim (hp ⟨4, rfl⟩)
  · exact False.elim (hp ⟨2, rfl⟩)
  · exact False.elim (hp ⟨5, rfl⟩)
  · exact False.elim (hp ⟨1, rfl⟩)
  · refine ⟨2, 5, by decide, by decide, ?_⟩
    show InTri (w 5)
      (w (hullCycle 0)) (w (hullCycle 2)) (w (hullCycle 5))
    simpa [hullCycle] using w_interior
  · exact False.elim (hp ⟨6, rfl⟩)
  · exact False.elim (hp ⟨0, rfl⟩)

lemma fanSum_w_hullCycle :
    fanSum w hullCycle = H2w := by
  have hfp : fanPairs 7 =
      {((1 : Fin 7), (2 : Fin 7)), (2, 3), (3, 4), (4, 5), (5, 6)} := by
    decide
  rw [fanSum, hfp]
  simp [H2w, H2, hullCycle]
  ring

lemma IsHullArea_w : IsHullArea w H2w := by
  exact IsHullArea.hull7 hullCycle hullCycle_injective
    w_strictHullCyclePos w_fanCovers fanSum_w_hullCycle.symm

end Heilbronn8
