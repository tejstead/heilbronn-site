import Heilbronn8.HullArea
import Heilbronn8.TriVolume

namespace Heilbronn8

/-! ## The measure-theoretic fan bridge -/

/--
A finite family of fan triangles has volume equal to the sum of its
triangle volumes when it covers the hull and is pairwise a.e. disjoint.
-/
theorem volume_convexHull_eq_sum_fan
    {ι : Type*} [Fintype ι]
    (s : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (a b : ι → ℝ × ℝ)
    (hunion : convexHull ℝ s =
      ⋃ i : ι, convexHull ℝ {p, a i, b i})
    (hpair : ∀ ⦃i j : ι⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (convexHull ℝ {p, a i, b i})
        (convexHull ℝ {p, a j, b j})) :
    MeasureTheory.volume (convexHull ℝ s) =
      ∑ i : ι, ENNReal.ofReal (|sig p (a i) (b i)| / 2) := by
  rw [hunion, MeasureTheory.measure_iUnion₀ hpair]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro i hi
    exact volume_convexHull_triple p (a i) (b i)
  · intro i
    exact (convex_convexHull ℝ _).nullMeasurableSet
      MeasureTheory.volume

/-! ## Determinant geometry used by the strict fan -/

private lemma sig_affine_third
    (p q a b c : ℝ × ℝ) (x y z : ℝ)
    (hxyz : x + y + z = 1) :
    sig p q (x • a + y • b + z • c) =
      x * sig p q a + y * sig p q b + z * sig p q c := by
  rw [← sig_rotate (x • a + y • b + z • c) p q,
    sig_affine_fst a b c p q x y z hxyz,
    sig_rotate a p q, sig_rotate b p q, sig_rotate c p q]

private lemma sig_affine_third_two
    (p q a b : ℝ × ℝ) (x y : ℝ) (hxy : x + y = 1) :
    sig p q (x • a + y • b) =
      x * sig p q a + y * sig p q b := by
  have h := sig_affine_third p q a b b x y 0 (by linarith)
  simpa using h

private lemma sig_reverse (p q x : ℝ × ℝ) :
    sig q p x = -sig p q x := by
  simp only [sig]
  ring

private lemma sig_nonneg_on_convexHull
    (p q : ℝ × ℝ) (s : Set (ℝ × ℝ))
    (h : ∀ x ∈ s, 0 ≤ sig p q x) :
    ∀ x ∈ convexHull ℝ s, 0 ≤ sig p q x := by
  apply convexHull_min h
  rintro x hx y hy u v hu hv huv
  change 0 ≤ sig p q x at hx
  change 0 ≤ sig p q y at hy
  change 0 ≤ sig p q (u • x + v • y)
  rw [sig_affine_third_two p q x y u v huv]
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)

private lemma mem_triangle_iff_orientations
    (x a b c : ℝ × ℝ) (habc : 0 < sig a b c) :
    x ∈ convexHull ℝ {a, b, c} ↔
      0 ≤ sig a b x ∧ 0 ≤ sig b c x ∧ 0 ≤ sig c a x := by
  rw [← inTri_iff_mem_convexHull]
  constructor
  · rintro ⟨u, v, t, hu, hv, ht, huv, rfl⟩
    have h₁ := sig_affine_third a b a b c u v t huv
    have h₂ := sig_affine_third b c a b c u v t huv
    have h₃ := sig_affine_third c a a b c u v t huv
    have h₁' :
        sig a b (u • a + v • b + t • c) =
          t * sig a b c := by
      rw [h₁]
      simp [sig]
    have h₂' :
        sig b c (u • a + v • b + t • c) =
          u * sig a b c := by
      rw [h₂]
      have hcyc : sig b c a = sig a b c := by
        simp only [sig]
        ring
      rw [hcyc]
      simp [sig]
    have h₃' :
        sig c a (u • a + v • b + t • c) =
          v * sig a b c := by
      rw [h₃]
      have hcyc : sig c a b = sig a b c := by
        simp only [sig]
        ring
      rw [hcyc]
      simp [sig]
    rw [h₁', h₂', h₃']
    exact ⟨mul_nonneg ht habc.le, mul_nonneg hu habc.le,
      mul_nonneg hv habc.le⟩
  · rintro ⟨h₁, h₂, h₃⟩
    let D := sig a b c
    refine ⟨sig b c x / D, sig c a x / D, sig a b x / D,
      div_nonneg h₂ habc.le, div_nonneg h₃ habc.le,
      div_nonneg h₁ habc.le, ?_, ?_⟩
    · dsimp [D]
      field_simp [habc.ne']
      simp only [sig]
      ring
    · dsimp [D]
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add, smul_eq_mul]
      · field_simp [habc.ne']
        simp only [sig]
        ring
      · field_simp [habc.ne']
        simp only [sig]
        ring

private lemma strictCCW_consecutive_halfplane
    {n : ℕ} (pts : Fin n → ℝ × ℝ)
    (hpos : ∀ i j k : Fin n, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k))
    (i j : Fin n) (hij : i.val + 1 = j.val) :
    ∀ k : Fin n, 0 ≤ sig (pts i) (pts j) (pts k) := by
  intro k
  have hij' : i < j := by omega
  by_cases hki : k < i
  · rw [← sig_rotate (pts k) (pts i) (pts j)]
    exact (hpos k i j hki hij').le
  by_cases hki' : k = i
  · subst k
    simp [sig]
  by_cases hkj : k = j
  · subst k
    simp [sig]
  have hjk : j < k := by omega
  exact (hpos i j k hij' hjk).le

private lemma strictCCW7_closing_halfplane
    (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    ∀ k : Fin 7, 0 ≤ sig (pts 6) (pts 0) (pts k) := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [sig]
  by_cases hk6 : k = 6
  · subst k
    simp [sig]
  have h0k : (0 : Fin 7) < k :=
    Fin.pos_iff_ne_zero.mpr hk0
  have hk6' : k < (6 : Fin 7) := by omega
  calc
    0 ≤ sig (pts 0) (pts k) (pts 6) :=
      (hpos 0 k 6 h0k hk6').le
    _ = sig (pts 6) (pts 0) (pts k) := by
      rw [sig_rotate (pts 0) (pts k) (pts 6),
        sig_rotate (pts k) (pts 6) (pts 0)]

private def fanLeft7
    (pts : Fin 7 → ℝ × ℝ) : Fin 5 → ℝ × ℝ :=
  ![pts 1, pts 2, pts 3, pts 4, pts 5]

private def fanRight7
    (pts : Fin 7 → ℝ × ℝ) : Fin 5 → ℝ × ℝ :=
  ![pts 2, pts 3, pts 4, pts 5, pts 6]

private def fanCell7
    (pts : Fin 7 → ℝ × ℝ) (i : Fin 5) : Set (ℝ × ℝ) :=
  convexHull ℝ {pts 0, fanLeft7 pts i, fanRight7 pts i}

/-! ## Set decomposition of a strict seven-point cycle -/

private lemma strictCCW7_fan_decomposition
    (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 5, fanCell7 pts i := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 :=
      strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 :=
      strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 :=
      strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 :=
      strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h45 :=
      strictCCW_consecutive_halfplane pts hpos 4 5 (by decide)
    have h56 :=
      strictCCW_consecutive_halfplane pts hpos 5 6 (by decide)
    have h60 := strictCCW7_closing_halfplane pts hpos
    have h01x := sig_nonneg_on_convexHull (pts 0) (pts 1)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := sig_nonneg_on_convexHull (pts 1) (pts 2)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := sig_nonneg_on_convexHull (pts 2) (pts 3)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h34x := sig_nonneg_on_convexHull (pts 3) (pts 4)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h34 k) x hx
    have h45x := sig_nonneg_on_convexHull (pts 4) (pts 5)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h45 k) x hx
    have h56x := sig_nonneg_on_convexHull (pts 5) (pts 6)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h56 k) x hx
    have h60x := sig_nonneg_on_convexHull (pts 6) (pts 0)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h60 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
    have hp045 := hpos 0 4 5 (by decide) (by decide)
    have hp056 := hpos 0 5 6 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    by_cases h03 : sig (pts 0) (pts 3) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      apply (mem_triangle_iff_orientations x _ _ _ hp023).2
      rw [sig_reverse (pts 0) (pts 3) x]
      exact ⟨le_of_not_ge h02, h23x, neg_nonneg.mpr h03⟩
    by_cases h04 : sig (pts 0) (pts 4) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨2, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 3, pts 4}
      apply (mem_triangle_iff_orientations x _ _ _ hp034).2
      rw [sig_reverse (pts 0) (pts 4) x]
      exact ⟨le_of_not_ge h03, h34x, neg_nonneg.mpr h04⟩
    by_cases h05 : sig (pts 0) (pts 5) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨3, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 4, pts 5}
      apply (mem_triangle_iff_orientations x _ _ _ hp045).2
      rw [sig_reverse (pts 0) (pts 5) x]
      exact ⟨le_of_not_ge h04, h45x, neg_nonneg.mpr h05⟩
    · refine Set.mem_iUnion.2 ⟨4, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 5, pts 6}
      exact (mem_triangle_iff_orientations x _ _ _ hp056).2
        ⟨le_of_not_ge h05, h56x, h60x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    apply (convexHull_mono
      (s := {pts 0, fanLeft7 pts i, fanRight7 pts i})
      (t := Set.range pts) ?_) hi
    fin_cases i
    all_goals
      rw [Set.insert_subset_iff, Set.insert_subset_iff,
        Set.singleton_subset_iff]
    · exact ⟨⟨0, rfl⟩, ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨3, rfl⟩, ⟨4, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨4, rfl⟩, ⟨5, rfl⟩⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨⟨5, rfl⟩, ⟨6, rfl⟩⟩⟩

/-! ## Null overlaps -/

private lemma adjacent_inter_subset_segment
    (p a b c : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) :
    convexHull ℝ {p, a, b} ∩ convexHull ℝ {p, b, c} ⊆
      segment ℝ p b := by
  intro x hx
  have hleft :=
    (mem_triangle_iff_orientations x p a b hpab).1 hx.1
  have hright :=
    (mem_triangle_iff_orientations x p b c hpbc).1 hx.2
  have hrev := sig_reverse b p x
  have hzero : sig p b x = 0 := by
    nlinarith [hleft.2.2, hright.1]
  have hxright : InTri x p b c :=
    (inTri_iff_mem_convexHull x p b c).2 hx.2
  rcases hxright with ⟨u, v, t, hu, hv, ht, huv, hxe⟩
  have hsig : sig p b x = t * sig p b c := by
    rw [hxe, sig_affine_third p b p b c u v t huv]
    simp [sig]
  have htzero : t = 0 := by nlinarith
  have hin : InTri x p b b := by
    refine ⟨u, v, 0, hu, hv, by positivity, by linarith, ?_⟩
    simpa [htzero] using hxe
  rw [← convexHull_pair]
  have hconv := (inTri_iff_mem_convexHull x p b b).1 hin
  simpa using hconv

private lemma separated_inter_subset_singleton
    (p a b c d : ℝ × ℝ)
    (hpab : 0 < sig p a b)
    (hpbc : 0 < sig p b c) (hpbd : 0 < sig p b d) :
    convexHull ℝ {p, a, b} ∩ convexHull ℝ {p, c, d} ⊆ {p} := by
  intro x hx
  have hleft :=
    (mem_triangle_iff_orientations x p a b hpab).1 hx.1
  have hrev := sig_reverse b p x
  have hxright : InTri x p c d :=
    (inTri_iff_mem_convexHull x p c d).2 hx.2
  rcases hxright with ⟨u, v, t, hu, hv, ht, huv, hxe⟩
  have hsig : sig p b x =
      v * sig p b c + t * sig p b d := by
    rw [hxe, sig_affine_third p b p c d u v t huv]
    simp [sig]
  have hvzero : v = 0 := by nlinarith
  have htzero : t = 0 := by nlinarith
  have huone : u = 1 := by linarith
  rw [Set.mem_singleton_iff, hxe, hvzero, htzero, huone]
  module

private lemma adjacent_triangles_aeDisjoint
    (p a b c : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {p, a, b})
      (convexHull ℝ {p, b, c}) := by
  exact MeasureTheory.measure_mono_null
    (adjacent_inter_subset_segment p a b c hpab hpbc)
    (volume_segment_eq_zero p b)

private lemma separated_triangles_aeDisjoint
    (p a b c d : ℝ × ℝ)
    (hpab : 0 < sig p a b)
    (hpbc : 0 < sig p b c) (hpbd : 0 < sig p b d) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {p, a, b})
      (convexHull ℝ {p, c, d}) := by
  exact MeasureTheory.measure_mono_null
    (separated_inter_subset_singleton p a b c d hpab hpbc hpbd)
    (by simp)

private lemma strictCCW7_fan_pairwise
    (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    ∀ ⦃i j : Fin 5⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (fanCell7 pts i) (fanCell7 pts j) := by
  have haux : ∀ {i j : Fin 5}, i < j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (fanCell7 pts i) (fanCell7 pts j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp only [Fin.mk_lt_mk] at hij
    all_goals try omega
    · exact adjacent_triangles_aeDisjoint
        (pts 0) (pts 1) (pts 2) (pts 3)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 3 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint
        (pts 0) (pts 1) (pts 2) (pts 3) (pts 4)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 2 4 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint
        (pts 0) (pts 1) (pts 2) (pts 4) (pts 5)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 4 (by decide) (by decide))
        (hpos 0 2 5 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint
        (pts 0) (pts 1) (pts 2) (pts 5) (pts 6)
        (hpos 0 1 2 (by decide) (by decide))
        (hpos 0 2 5 (by decide) (by decide))
        (hpos 0 2 6 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint
        (pts 0) (pts 2) (pts 3) (pts 4)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint
        (pts 0) (pts 2) (pts 3) (pts 4) (pts 5)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 3 5 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint
        (pts 0) (pts 2) (pts 3) (pts 5) (pts 6)
        (hpos 0 2 3 (by decide) (by decide))
        (hpos 0 3 5 (by decide) (by decide))
        (hpos 0 3 6 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint
        (pts 0) (pts 3) (pts 4) (pts 5)
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 4 5 (by decide) (by decide))
    · exact separated_triangles_aeDisjoint
        (pts 0) (pts 3) (pts 4) (pts 5) (pts 6)
        (hpos 0 3 4 (by decide) (by decide))
        (hpos 0 4 5 (by decide) (by decide))
        (hpos 0 4 6 (by decide) (by decide))
    · exact adjacent_triangles_aeDisjoint
        (pts 0) (pts 4) (pts 5) (pts 6)
        (hpos 0 4 5 (by decide) (by decide))
        (hpos 0 5 6 (by decide) (by decide))
  intro i j hij
  by_cases hlt : i < j
  · exact haux hlt
  · exact (haux
      (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm

/--
The five-triangle fan formula for a strict CCW seven-cycle.
-/
theorem volume_convexHull_strictCCW7
    (pts : Fin 7 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    MeasureTheory.volume (convexHull ℝ (Set.range pts)) =
      ∑ i : Fin 5, ENNReal.ofReal
        (|sig (pts 0) (fanLeft7 pts i) (fanRight7 pts i)| / 2) := by
  exact volume_convexHull_eq_sum_fan
    (Set.range pts) (pts 0) (fanLeft7 pts) (fanRight7 pts)
    (strictCCW7_fan_decomposition pts hpos)
    (strictCCW7_fan_pairwise pts hpos)

/-! ## The verified seven-gon witness -/

private lemma convexHull_range_w_eq_cycle :
    convexHull ℝ (Set.range w) =
      convexHull ℝ (Set.range (w ∘ hullCycle)) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · apply subset_convexHull ℝ
        exact ⟨3, by simp [hullCycle]⟩
      · apply subset_convexHull ℝ
        exact ⟨4, by simp [hullCycle]⟩
      · apply subset_convexHull ℝ
        exact ⟨2, by simp [hullCycle]⟩
      · apply subset_convexHull ℝ
        exact ⟨5, by simp [hullCycle]⟩
      · apply subset_convexHull ℝ
        exact ⟨1, by simp [hullCycle]⟩
      · have hw5 :
            w 5 ∈ convexHull ℝ {w 7, w 2, w 3} :=
          (inTri_iff_mem_convexHull
            (w 5) (w 7) (w 2) (w 3)).1 w_interior
        apply (convexHull_mono (s := {w 7, w 2, w 3})
          (t := Set.range (w ∘ hullCycle)) ?_) hw5
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact ⟨0, by simp [hullCycle]⟩
        · exact ⟨2, by simp [hullCycle]⟩
        · exact ⟨5, by simp [hullCycle]⟩
      · apply subset_convexHull ℝ
        exact ⟨6, by simp [hullCycle]⟩
      · apply subset_convexHull ℝ
        exact ⟨0, by simp [hullCycle]⟩
    · exact convex_convexHull ℝ _
  · apply convexHull_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨hullCycle i, rfl⟩

theorem volume_convexHull_w :
    MeasureTheory.volume (convexHull ℝ (Set.range w)) =
      ENNReal.ofReal (H2w / 2) := by
  rw [convexHull_range_w_eq_cycle]
  let pts : Fin 7 → ℝ × ℝ := w ∘ hullCycle
  have hpos : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact w_strictHullCyclePos.pos i j k hij hjk
  rw [volume_convexHull_strictCCW7 pts hpos]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    have h012 := hpos 0 1 2 (by decide) (by decide)
    have h023 := hpos 0 2 3 (by decide) (by decide)
    have h034 := hpos 0 3 4 (by decide) (by decide)
    have h045 := hpos 0 4 5 (by decide) (by decide)
    have h056 := hpos 0 5 6 (by decide) (by decide)
    rw [Fin.sum_univ_five]
    change
      |sig (pts 0) (pts 1) (pts 2)| / 2 +
        |sig (pts 0) (pts 2) (pts 3)| / 2 +
        |sig (pts 0) (pts 3) (pts 4)| / 2 +
        |sig (pts 0) (pts 4) (pts 5)| / 2 +
        |sig (pts 0) (pts 5) (pts 6)| / 2 = H2w / 2
    rw [abs_of_pos h012, abs_of_pos h023, abs_of_pos h034,
      abs_of_pos h045, abs_of_pos h056]
    dsimp [pts]
    simp only [H2w, H2]
    ring
  · intro i hi
    positivity

end Heilbronn8
