import Heilbronn8.PolyVolume

namespace Heilbronn8

private lemma gen_sig_affine_third
    (p q a b c : ℝ × ℝ) (x y z : ℝ)
    (hxyz : x + y + z = 1) :
    sig p q (x • a + y • b + z • c) =
      x * sig p q a + y * sig p q b + z * sig p q c := by
  rw [← sig_rotate (x • a + y • b + z • c) p q,
    sig_affine_fst a b c p q x y z hxyz,
    sig_rotate a p q, sig_rotate b p q, sig_rotate c p q]

private lemma gen_sig_affine_third_two
    (p q a b : ℝ × ℝ) (x y : ℝ) (hxy : x + y = 1) :
    sig p q (x • a + y • b) =
      x * sig p q a + y * sig p q b := by
  have h := gen_sig_affine_third p q a b b x y 0 (by linarith)
  simpa using h

private lemma gen_sig_reverse (p q x : ℝ × ℝ) :
    sig q p x = -sig p q x := by
  simp only [sig]
  ring

private lemma gen_sig_nonneg_on_convexHull
    (p q : ℝ × ℝ) (s : Set (ℝ × ℝ))
    (h : ∀ x ∈ s, 0 ≤ sig p q x) :
    ∀ x ∈ convexHull ℝ s, 0 ≤ sig p q x := by
  apply convexHull_min h
  rintro x hx y hy u w hu hw huw
  change 0 ≤ sig p q x at hx
  change 0 ≤ sig p q y at hy
  change 0 ≤ sig p q (u • x + w • y)
  rw [gen_sig_affine_third_two p q x y u w huw]
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hw hy)

private lemma gen_mem_triangle_iff_orientations
    (x a b c : ℝ × ℝ) (habc : 0 < sig a b c) :
    x ∈ convexHull ℝ {a, b, c} ↔
      0 ≤ sig a b x ∧ 0 ≤ sig b c x ∧ 0 ≤ sig c a x := by
  rw [← inTri_iff_mem_convexHull]
  constructor
  · rintro ⟨u, w, t, hu, hw, ht, huw, rfl⟩
    have h₁ := gen_sig_affine_third a b a b c u w t huw
    have h₂ := gen_sig_affine_third b c a b c u w t huw
    have h₃ := gen_sig_affine_third c a a b c u w t huw
    have h₁' :
        sig a b (u • a + w • b + t • c) =
          t * sig a b c := by
      rw [h₁]
      simp [sig]
    have h₂' :
        sig b c (u • a + w • b + t • c) =
          u * sig a b c := by
      rw [h₂]
      have hcyc : sig b c a = sig a b c := by
        simp only [sig]
        ring
      rw [hcyc]
      simp [sig]
    have h₃' :
        sig c a (u • a + w • b + t • c) =
          w * sig a b c := by
      rw [h₃]
      have hcyc : sig c a b = sig a b c := by
        simp only [sig]
        ring
      rw [hcyc]
      simp [sig]
    rw [h₁', h₂', h₃']
    exact ⟨mul_nonneg ht habc.le, mul_nonneg hu habc.le,
      mul_nonneg hw habc.le⟩
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

private lemma gen_strictCCW_consecutive_halfplane
    {m : ℕ} (pts : Fin m → ℝ × ℝ)
    (hpos : ∀ i j k : Fin m, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k))
    (i j : Fin m) (hij : i.val + 1 = j.val) :
    ∀ k : Fin m, 0 ≤ sig (pts i) (pts j) (pts k) := by
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

private lemma gen_strictCCW_closing_halfplane
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (pts : Fin m → ℝ × ℝ)
    (hpos : ∀ i j k : Fin m, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    ∀ k : Fin m,
      0 ≤ sig (pts ⟨m - 1, by omega⟩) (pts 0) (pts k) := by
  intro k
  let last : Fin m := ⟨m - 1, by omega⟩
  change 0 ≤ sig (pts last) (pts 0) (pts k)
  by_cases hk0 : k = 0
  · subst k
    simp [sig]
  by_cases hklast : k = last
  · subst k
    simp [sig]
  have h0k : (0 : Fin m) < k := Fin.pos_iff_ne_zero.mpr hk0
  have hklast' : k < last := by
    have hk_le : k.val ≤ m - 1 := by omega
    have hk_ne : k.val ≠ m - 1 := by
      intro hk
      apply hklast
      exact Fin.ext hk
    change k.val < m - 1
    omega
  calc
    0 ≤ sig (pts 0) (pts k) (pts last) :=
      (hpos 0 k last h0k hklast').le
    _ = sig (pts last) (pts 0) (pts k) := by
      rw [sig_rotate (pts 0) (pts k) (pts last),
        sig_rotate (pts k) (pts last) (pts 0)]

def fanLeftGen {m : ℕ} (pts : Fin m → ℝ × ℝ)
    (i : Fin (m - 2)) : ℝ × ℝ :=
  pts ⟨i.val + 1, by omega⟩

def fanRightGen {m : ℕ} (pts : Fin m → ℝ × ℝ)
    (i : Fin (m - 2)) : ℝ × ℝ :=
  pts ⟨i.val + 2, by omega⟩

private def fanCellGen {m : ℕ} [NeZero m]
    (pts : Fin m → ℝ × ℝ) (i : Fin (m - 2)) : Set (ℝ × ℝ) :=
  convexHull ℝ {pts 0, fanLeftGen pts i, fanRightGen pts i}

private lemma gen_adjacent_inter_subset_segment
    (p a b c : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) :
    convexHull ℝ {p, a, b} ∩ convexHull ℝ {p, b, c} ⊆
      segment ℝ p b := by
  intro x hx
  have hleft :=
    (gen_mem_triangle_iff_orientations x p a b hpab).1 hx.1
  have hright :=
    (gen_mem_triangle_iff_orientations x p b c hpbc).1 hx.2
  have hrev := gen_sig_reverse b p x
  have hzero : sig p b x = 0 := by
    nlinarith [hleft.2.2, hright.1]
  have hxright : InTri x p b c :=
    (inTri_iff_mem_convexHull x p b c).2 hx.2
  rcases hxright with ⟨u, w, t, hu, hw, ht, huw, hxe⟩
  have hsig : sig p b x = t * sig p b c := by
    rw [hxe, gen_sig_affine_third p b p b c u w t huw]
    simp [sig]
  have htzero : t = 0 := by nlinarith
  have hin : InTri x p b b := by
    refine ⟨u, w, 0, hu, hw, by positivity, by linarith, ?_⟩
    simpa [htzero] using hxe
  rw [← convexHull_pair]
  have hconv := (inTri_iff_mem_convexHull x p b b).1 hin
  simpa using hconv

private lemma gen_separated_inter_subset_singleton
    (p a b c d : ℝ × ℝ)
    (hpab : 0 < sig p a b)
    (hpbc : 0 < sig p b c) (hpbd : 0 < sig p b d) :
    convexHull ℝ {p, a, b} ∩ convexHull ℝ {p, c, d} ⊆ {p} := by
  intro x hx
  have hleft :=
    (gen_mem_triangle_iff_orientations x p a b hpab).1 hx.1
  have hrev := gen_sig_reverse b p x
  have hxright : InTri x p c d :=
    (inTri_iff_mem_convexHull x p c d).2 hx.2
  rcases hxright with ⟨u, w, t, hu, hw, ht, huw, hxe⟩
  have hsig : sig p b x =
      w * sig p b c + t * sig p b d := by
    rw [hxe, gen_sig_affine_third p b p c d u w t huw]
    simp [sig]
  have hwzero : w = 0 := by nlinarith
  have htzero : t = 0 := by nlinarith
  have huone : u = 1 := by linarith
  rw [Set.mem_singleton_iff, hxe, hwzero, htzero, huone]
  module

private lemma gen_adjacent_triangles_aeDisjoint
    (p a b c : ℝ × ℝ)
    (hpab : 0 < sig p a b) (hpbc : 0 < sig p b c) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {p, a, b})
      (convexHull ℝ {p, b, c}) := by
  exact MeasureTheory.measure_mono_null
    (gen_adjacent_inter_subset_segment p a b c hpab hpbc)
    (volume_segment_eq_zero p b)

private lemma gen_separated_triangles_aeDisjoint
    (p a b c d : ℝ × ℝ)
    (hpab : 0 < sig p a b)
    (hpbc : 0 < sig p b c) (hpbd : 0 < sig p b d) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {p, a, b})
      (convexHull ℝ {p, c, d}) := by
  exact MeasureTheory.measure_mono_null
    (gen_separated_inter_subset_singleton p a b c d hpab hpbc hpbd)
    (by simp)

private lemma gen_fan_pairwise
    {m : ℕ} [NeZero m] (pts : Fin m → ℝ × ℝ)
    (hpos : ∀ i j : Fin m, (0 : Fin m) < i → i < j →
      0 < sig (pts 0) (pts i) (pts j)) :
    ∀ ⦃i j : Fin (m - 2)⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (fanCellGen pts i) (fanCellGen pts j) := by
  have haux : ∀ {i j : Fin (m - 2)}, i < j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (fanCellGen pts i) (fanCellGen pts j) := by
    intro i j hij
    let i1 : Fin m := ⟨i.val + 1, by omega⟩
    let i2 : Fin m := ⟨i.val + 2, by omega⟩
    let j1 : Fin m := ⟨j.val + 1, by omega⟩
    let j2 : Fin m := ⟨j.val + 2, by omega⟩
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (convexHull ℝ {pts 0, pts i1, pts i2})
      (convexHull ℝ {pts 0, pts j1, pts j2})
    have hp_i : 0 < sig (pts 0) (pts i1) (pts i2) :=
      hpos i1 i2
        (by change 0 < i.val + 1; omega)
        (by change i.val + 1 < i.val + 2; omega)
    have hp_j : 0 < sig (pts 0) (pts j1) (pts j2) :=
      hpos j1 j2
        (by change 0 < j.val + 1; omega)
        (by change j.val + 1 < j.val + 2; omega)
    by_cases hadj : i.val + 1 = j.val
    · have hi2j1 : i2 = j1 := by
        apply Fin.ext
        change i.val + 2 = j.val + 1
        omega
      rw [← hi2j1]
      exact gen_adjacent_triangles_aeDisjoint
        (pts 0) (pts i1) (pts i2) (pts j2) hp_i
        (by simpa [hi2j1] using hp_j)
    · have hp_i2j1 : 0 < sig (pts 0) (pts i2) (pts j1) :=
        hpos i2 j1
          (by change 0 < i.val + 2; omega)
          (by change i.val + 2 < j.val + 1; omega)
      have hp_i2j2 : 0 < sig (pts 0) (pts i2) (pts j2) :=
        hpos i2 j2
          (by change 0 < i.val + 2; omega)
          (by change i.val + 2 < j.val + 2; omega)
      exact gen_separated_triangles_aeDisjoint
        (pts 0) (pts i1) (pts i2) (pts j1) (pts j2)
        hp_i hp_i2j1 hp_i2j2
  intro i j hij
  by_cases hlt : i < j
  · exact haux hlt
  · exact (haux
      (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm

private lemma gen_fanCell_subset_cycleHull
    {m : ℕ} [NeZero m] (pts : Fin m → ℝ × ℝ)
    (i : Fin (m - 2)) :
    fanCellGen pts i ⊆ convexHull ℝ (Set.range pts) := by
  intro x hx
  apply (convexHull_mono
    (s := {pts 0, fanLeftGen pts i, fanRightGen pts i})
    (t := Set.range pts) ?_) hx
  rw [Set.insert_subset_iff, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  exact ⟨⟨0, rfl⟩,
    ⟨⟨i.val + 1, by omega⟩, rfl⟩,
    ⟨⟨i.val + 2, by omega⟩, rfl⟩⟩

private lemma gen_fan_decomposition3
    (pts : Fin 3 → ℝ × ℝ) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 1, fanCellGen pts i := by
  have hrange : Set.range pts = {pts 0, pts 1, pts 2} := by
    apply Set.Subset.antisymm
    · rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [hrange]
  ext x
  simp [fanCellGen, fanLeftGen, fanRightGen]

private lemma gen_fan_decomposition4
    (pts : Fin 4 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 4, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 2, fanCellGen pts i := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 :=
      gen_strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 :=
      gen_strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 :=
      gen_strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h30 := gen_strictCCW_closing_halfplane (by decide) pts hpos
    have h01x := gen_sig_nonneg_on_convexHull (pts 0) (pts 1)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := gen_sig_nonneg_on_convexHull (pts 1) (pts 2)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := gen_sig_nonneg_on_convexHull (pts 2) (pts 3)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h30x := gen_sig_nonneg_on_convexHull (pts 3) (pts 0)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h30 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [gen_sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      exact (gen_mem_triangle_iff_orientations x _ _ _ hp023).2
        ⟨le_of_not_ge h02, h23x, h30x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    exact gen_fanCell_subset_cycleHull pts i hi

private lemma gen_fan_decomposition5
    (pts : Fin 5 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 5, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 3, fanCellGen pts i := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 :=
      gen_strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 :=
      gen_strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 :=
      gen_strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 :=
      gen_strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h40 := gen_strictCCW_closing_halfplane (by decide) pts hpos
    have h01x := gen_sig_nonneg_on_convexHull (pts 0) (pts 1)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := gen_sig_nonneg_on_convexHull (pts 1) (pts 2)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := gen_sig_nonneg_on_convexHull (pts 2) (pts 3)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h34x := gen_sig_nonneg_on_convexHull (pts 3) (pts 4)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h34 k) x hx
    have h40x := gen_sig_nonneg_on_convexHull (pts 4) (pts 0)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h40 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [gen_sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    by_cases h03 : sig (pts 0) (pts 3) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp023).2
      rw [gen_sig_reverse (pts 0) (pts 3) x]
      exact ⟨le_of_not_ge h02, h23x, neg_nonneg.mpr h03⟩
    · refine Set.mem_iUnion.2 ⟨2, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 3, pts 4}
      exact (gen_mem_triangle_iff_orientations x _ _ _ hp034).2
        ⟨le_of_not_ge h03, h34x, h40x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    exact gen_fanCell_subset_cycleHull pts i hi

private lemma gen_fan_decomposition6
    (pts : Fin 6 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 6, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 4, fanCellGen pts i := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 :=
      gen_strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 :=
      gen_strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 :=
      gen_strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 :=
      gen_strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h45 :=
      gen_strictCCW_consecutive_halfplane pts hpos 4 5 (by decide)
    have h50 := gen_strictCCW_closing_halfplane (by decide) pts hpos
    have h01x := gen_sig_nonneg_on_convexHull (pts 0) (pts 1)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := gen_sig_nonneg_on_convexHull (pts 1) (pts 2)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := gen_sig_nonneg_on_convexHull (pts 2) (pts 3)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h34x := gen_sig_nonneg_on_convexHull (pts 3) (pts 4)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h34 k) x hx
    have h45x := gen_sig_nonneg_on_convexHull (pts 4) (pts 5)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h45 k) x hx
    have h50x := gen_sig_nonneg_on_convexHull (pts 5) (pts 0)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h50 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
    have hp045 := hpos 0 4 5 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [gen_sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    by_cases h03 : sig (pts 0) (pts 3) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp023).2
      rw [gen_sig_reverse (pts 0) (pts 3) x]
      exact ⟨le_of_not_ge h02, h23x, neg_nonneg.mpr h03⟩
    by_cases h04 : sig (pts 0) (pts 4) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨2, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 3, pts 4}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp034).2
      rw [gen_sig_reverse (pts 0) (pts 4) x]
      exact ⟨le_of_not_ge h03, h34x, neg_nonneg.mpr h04⟩
    · refine Set.mem_iUnion.2 ⟨3, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 4, pts 5}
      exact (gen_mem_triangle_iff_orientations x _ _ _ hp045).2
        ⟨le_of_not_ge h04, h45x, h50x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    exact gen_fanCell_subset_cycleHull pts i hi

private lemma gen_fan_decomposition8
    (pts : Fin 8 → ℝ × ℝ)
    (hpos : ∀ i j k : Fin 8, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k)) :
    convexHull ℝ (Set.range pts) =
      ⋃ i : Fin 6, fanCellGen pts i := by
  apply Set.Subset.antisymm
  · intro x hx
    have h01 :=
      gen_strictCCW_consecutive_halfplane pts hpos 0 1 (by decide)
    have h12 :=
      gen_strictCCW_consecutive_halfplane pts hpos 1 2 (by decide)
    have h23 :=
      gen_strictCCW_consecutive_halfplane pts hpos 2 3 (by decide)
    have h34 :=
      gen_strictCCW_consecutive_halfplane pts hpos 3 4 (by decide)
    have h45 :=
      gen_strictCCW_consecutive_halfplane pts hpos 4 5 (by decide)
    have h56 :=
      gen_strictCCW_consecutive_halfplane pts hpos 5 6 (by decide)
    have h67 :=
      gen_strictCCW_consecutive_halfplane pts hpos 6 7 (by decide)
    have h70 := gen_strictCCW_closing_halfplane (by decide) pts hpos
    have h01x := gen_sig_nonneg_on_convexHull (pts 0) (pts 1)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h01 k) x hx
    have h12x := gen_sig_nonneg_on_convexHull (pts 1) (pts 2)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h12 k) x hx
    have h23x := gen_sig_nonneg_on_convexHull (pts 2) (pts 3)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h23 k) x hx
    have h34x := gen_sig_nonneg_on_convexHull (pts 3) (pts 4)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h34 k) x hx
    have h45x := gen_sig_nonneg_on_convexHull (pts 4) (pts 5)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h45 k) x hx
    have h56x := gen_sig_nonneg_on_convexHull (pts 5) (pts 6)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h56 k) x hx
    have h67x := gen_sig_nonneg_on_convexHull (pts 6) (pts 7)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h67 k) x hx
    have h70x := gen_sig_nonneg_on_convexHull (pts 7) (pts 0)
      (Set.range pts) (by rintro _ ⟨k, rfl⟩; exact h70 k) x hx
    have hp012 := hpos 0 1 2 (by decide) (by decide)
    have hp023 := hpos 0 2 3 (by decide) (by decide)
    have hp034 := hpos 0 3 4 (by decide) (by decide)
    have hp045 := hpos 0 4 5 (by decide) (by decide)
    have hp056 := hpos 0 5 6 (by decide) (by decide)
    have hp067 := hpos 0 6 7 (by decide) (by decide)
    by_cases h02 : sig (pts 0) (pts 2) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 1, pts 2}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp012).2
      rw [gen_sig_reverse (pts 0) (pts 2) x]
      exact ⟨h01x, h12x, neg_nonneg.mpr h02⟩
    by_cases h03 : sig (pts 0) (pts 3) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 2, pts 3}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp023).2
      rw [gen_sig_reverse (pts 0) (pts 3) x]
      exact ⟨le_of_not_ge h02, h23x, neg_nonneg.mpr h03⟩
    by_cases h04 : sig (pts 0) (pts 4) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨2, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 3, pts 4}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp034).2
      rw [gen_sig_reverse (pts 0) (pts 4) x]
      exact ⟨le_of_not_ge h03, h34x, neg_nonneg.mpr h04⟩
    by_cases h05 : sig (pts 0) (pts 5) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨3, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 4, pts 5}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp045).2
      rw [gen_sig_reverse (pts 0) (pts 5) x]
      exact ⟨le_of_not_ge h04, h45x, neg_nonneg.mpr h05⟩
    by_cases h06 : sig (pts 0) (pts 6) x ≤ 0
    · refine Set.mem_iUnion.2 ⟨4, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 5, pts 6}
      apply (gen_mem_triangle_iff_orientations x _ _ _ hp056).2
      rw [gen_sig_reverse (pts 0) (pts 6) x]
      exact ⟨le_of_not_ge h05, h56x, neg_nonneg.mpr h06⟩
    · refine Set.mem_iUnion.2 ⟨5, ?_⟩
      change x ∈ convexHull ℝ {pts 0, pts 6, pts 7}
      exact (gen_mem_triangle_iff_orientations x _ _ _ hp067).2
        ⟨le_of_not_ge h06, h67x, h70x⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    exact gen_fanCell_subset_cycleHull pts i hi

private theorem gen_volume_of_fan_decomposition
    {m : ℕ} [NeZero m] (pts : Fin m → ℝ × ℝ)
    (hpos : ∀ i j k : Fin m, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k))
    (hdecomp : convexHull ℝ (Set.range pts) =
      ⋃ i : Fin (m - 2), fanCellGen pts i) :
    MeasureTheory.volume (convexHull ℝ (Set.range pts)) =
      ∑ i : Fin (m - 2), ENNReal.ofReal
        (|sig (pts 0) (fanLeftGen pts i) (fanRightGen pts i)| / 2) := by
  exact volume_convexHull_eq_sum_fan
    (Set.range pts) (pts 0) (fanLeftGen pts) (fanRightGen pts)
    hdecomp (gen_fan_pairwise pts (fun i j hi hij => hpos 0 i j hi hij))

private lemma gen_convexHull_range_eq_cycle
    {m : ℕ} [NeZero m] (v : Fin 8 → ℝ × ℝ)
    (c : Fin m → Fin 8) (hcover : FanCovers v c) :
    convexHull ℝ (Set.range v) =
      convexHull ℝ (Set.range (v ∘ c)) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨p, rfl⟩
      by_cases hp : p ∈ Set.range c
      · rcases hp with ⟨i, rfl⟩
        apply subset_convexHull ℝ
        exact ⟨i, rfl⟩
      · rcases hcover p hp with ⟨i, j, hi, hij, htri⟩
        have hmem :
            v p ∈ convexHull ℝ {v (c 0), v (c i), v (c j)} :=
          htri.mem_convexHull
        apply (convexHull_mono
          (s := {v (c 0), v (c i), v (c j)})
          (t := Set.range (v ∘ c)) ?_) hmem
        rw [Set.insert_subset_iff, Set.insert_subset_iff,
          Set.singleton_subset_iff]
        exact ⟨⟨0, rfl⟩, ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩⟩
    · exact convex_convexHull ℝ _
  · apply convexHull_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨c i, rfl⟩

private lemma gen_fanSum3
    (v : Fin 8 → ℝ × ℝ) (c : Fin 3 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) := by
  have hfp : fanPairs 3 =
      {((1 : Fin 3), (2 : Fin 3))} := by decide
  rw [fanSum, hfp]
  simp

private lemma gen_fanSum4
    (v : Fin 8 → ℝ × ℝ) (c : Fin 4 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) := by
  have hfp : fanPairs 4 =
      {((1 : Fin 4), (2 : Fin 4)), (2, 3)} := by decide
  rw [fanSum, hfp]
  simp

private lemma gen_fanSum5
    (v : Fin 8 → ℝ × ℝ) (c : Fin 5 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) := by
  have hfp : fanPairs 5 =
      {((1 : Fin 5), (2 : Fin 5)), (2, 3), (3, 4)} := by decide
  rw [fanSum, hfp]
  simp [add_assoc]

private lemma gen_fanSum6
    (v : Fin 8 → ℝ × ℝ) (c : Fin 6 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) +
      sig (v (c 0)) (v (c 4)) (v (c 5)) := by
  have hfp : fanPairs 6 =
      {((1 : Fin 6), (2 : Fin 6)), (2, 3), (3, 4), (4, 5)} := by decide
  rw [fanSum, hfp]
  simp [add_assoc]

private lemma gen_fanSum7
    (v : Fin 8 → ℝ × ℝ) (c : Fin 7 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) +
      sig (v (c 0)) (v (c 4)) (v (c 5)) +
      sig (v (c 0)) (v (c 5)) (v (c 6)) := by
  have hfp : fanPairs 7 =
      {((1 : Fin 7), (2 : Fin 7)), (2, 3), (3, 4), (4, 5), (5, 6)} := by decide
  rw [fanSum, hfp]
  simp [add_assoc]

private lemma gen_fanSum8
    (v : Fin 8 → ℝ × ℝ) (c : Fin 8 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) +
      sig (v (c 0)) (v (c 4)) (v (c 5)) +
      sig (v (c 0)) (v (c 5)) (v (c 6)) +
      sig (v (c 0)) (v (c 6)) (v (c 7)) := by
  have hfp : fanPairs 8 =
      {((1 : Fin 8), (2 : Fin 8)), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)} := by decide
  rw [fanSum, hfp]
  simp [add_assoc]

private theorem gen_volume_cycle3
    (v : Fin 8 → ℝ × ℝ) (c : Fin 3 → Fin 8)
    (hpos : StrictCyclicPos c v) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (v ∘ c))) =
      ENNReal.ofReal (fanSum v c / 2) := by
  let pts : Fin 3 → ℝ × ℝ := v ∘ c
  have hp : ∀ i j k : Fin 3, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact hpos.pos i j k hij hjk
  rw [gen_volume_of_fan_decomposition pts hp
    (gen_fan_decomposition3 pts)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Fin.sum_univ_one]
    change |sig (v (c 0)) (v (c 1)) (v (c 2))| / 2 =
      fanSum v c / 2
    rw [abs_of_pos (hpos.pos 0 1 2 (by decide) (by decide)),
      gen_fanSum3]
  · intro i hi
    positivity

private theorem gen_volume_cycle4
    (v : Fin 8 → ℝ × ℝ) (c : Fin 4 → Fin 8)
    (hpos : StrictCyclicPos c v) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (v ∘ c))) =
      ENNReal.ofReal (fanSum v c / 2) := by
  let pts : Fin 4 → ℝ × ℝ := v ∘ c
  have hp : ∀ i j k : Fin 4, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact hpos.pos i j k hij hjk
  rw [gen_volume_of_fan_decomposition pts hp
    (gen_fan_decomposition4 pts hp)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Fin.sum_univ_two]
    change
      |sig (v (c 0)) (v (c 1)) (v (c 2))| / 2 +
        |sig (v (c 0)) (v (c 2)) (v (c 3))| / 2 =
      fanSum v c / 2
    rw [abs_of_pos (hpos.pos 0 1 2 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 2 3 (by decide) (by decide)),
      gen_fanSum4]
    ring
  · intro i hi
    positivity

private theorem gen_volume_cycle5
    (v : Fin 8 → ℝ × ℝ) (c : Fin 5 → Fin 8)
    (hpos : StrictCyclicPos c v) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (v ∘ c))) =
      ENNReal.ofReal (fanSum v c / 2) := by
  let pts : Fin 5 → ℝ × ℝ := v ∘ c
  have hp : ∀ i j k : Fin 5, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact hpos.pos i j k hij hjk
  rw [gen_volume_of_fan_decomposition pts hp
    (gen_fan_decomposition5 pts hp)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Fin.sum_univ_three]
    change
      |sig (v (c 0)) (v (c 1)) (v (c 2))| / 2 +
        |sig (v (c 0)) (v (c 2)) (v (c 3))| / 2 +
        |sig (v (c 0)) (v (c 3)) (v (c 4))| / 2 =
      fanSum v c / 2
    rw [abs_of_pos (hpos.pos 0 1 2 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 2 3 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 3 4 (by decide) (by decide)),
      gen_fanSum5]
    ring
  · intro i hi
    positivity

private theorem gen_volume_cycle6
    (v : Fin 8 → ℝ × ℝ) (c : Fin 6 → Fin 8)
    (hpos : StrictCyclicPos c v) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (v ∘ c))) =
      ENNReal.ofReal (fanSum v c / 2) := by
  let pts : Fin 6 → ℝ × ℝ := v ∘ c
  have hp : ∀ i j k : Fin 6, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact hpos.pos i j k hij hjk
  rw [gen_volume_of_fan_decomposition pts hp
    (gen_fan_decomposition6 pts hp)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Fin.sum_univ_four]
    change
      |sig (v (c 0)) (v (c 1)) (v (c 2))| / 2 +
        |sig (v (c 0)) (v (c 2)) (v (c 3))| / 2 +
        |sig (v (c 0)) (v (c 3)) (v (c 4))| / 2 +
        |sig (v (c 0)) (v (c 4)) (v (c 5))| / 2 =
      fanSum v c / 2
    rw [abs_of_pos (hpos.pos 0 1 2 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 2 3 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 3 4 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 4 5 (by decide) (by decide)),
      gen_fanSum6]
    ring
  · intro i hi
    positivity

private theorem gen_volume_cycle7
    (v : Fin 8 → ℝ × ℝ) (c : Fin 7 → Fin 8)
    (hpos : StrictCyclicPos c v) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (v ∘ c))) =
      ENNReal.ofReal (fanSum v c / 2) := by
  let pts : Fin 7 → ℝ × ℝ := v ∘ c
  have hp : ∀ i j k : Fin 7, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact hpos.pos i j k hij hjk
  rw [volume_convexHull_strictCCW7 pts hp]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Fin.sum_univ_five]
    change
      |sig (v (c 0)) (v (c 1)) (v (c 2))| / 2 +
        |sig (v (c 0)) (v (c 2)) (v (c 3))| / 2 +
        |sig (v (c 0)) (v (c 3)) (v (c 4))| / 2 +
        |sig (v (c 0)) (v (c 4)) (v (c 5))| / 2 +
        |sig (v (c 0)) (v (c 5)) (v (c 6))| / 2 =
      fanSum v c / 2
    rw [abs_of_pos (hpos.pos 0 1 2 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 2 3 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 3 4 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 4 5 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 5 6 (by decide) (by decide)),
      gen_fanSum7]
    ring
  · intro i hi
    positivity

private theorem gen_volume_cycle8
    (v : Fin 8 → ℝ × ℝ) (c : Fin 8 → Fin 8)
    (hpos : StrictCyclicPos c v) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (v ∘ c))) =
      ENNReal.ofReal (fanSum v c / 2) := by
  let pts : Fin 8 → ℝ × ℝ := v ∘ c
  have hp : ∀ i j k : Fin 8, i < j → j < k →
      0 < sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    exact hpos.pos i j k hij hjk
  rw [gen_volume_of_fan_decomposition pts hp
    (gen_fan_decomposition8 pts hp)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Fin.sum_univ_six]
    change
      |sig (v (c 0)) (v (c 1)) (v (c 2))| / 2 +
        |sig (v (c 0)) (v (c 2)) (v (c 3))| / 2 +
        |sig (v (c 0)) (v (c 3)) (v (c 4))| / 2 +
        |sig (v (c 0)) (v (c 4)) (v (c 5))| / 2 +
        |sig (v (c 0)) (v (c 5)) (v (c 6))| / 2 +
        |sig (v (c 0)) (v (c 6)) (v (c 7))| / 2 =
      fanSum v c / 2
    rw [abs_of_pos (hpos.pos 0 1 2 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 2 3 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 3 4 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 4 5 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 5 6 (by decide) (by decide)),
      abs_of_pos (hpos.pos 0 6 7 (by decide) (by decide)),
      gen_fanSum8]
    ring
  · intro i hi
    positivity

/-! ## Lower bounds from disjoint subfans -/

/-- Two configuration triangles on opposite sides of a directed edge have
disjoint interiors.  Their two positive oriented areas therefore give a
lower bound for the doubled area of the full convex hull. -/
theorem oppositeSideFan_le_doubledHullArea
    (v : Fin 8 → ℝ × ℝ) (a b c d : Fin 8)
    (hc : 0 < sig (v a) (v b) (v c))
    (hd : sig (v a) (v b) (v d) < 0) :
    sig (v a) (v b) (v c) - sig (v a) (v b) (v d) ≤
      doubledHullArea v := by
  let left : Set (ℝ × ℝ) := convexHull ℝ {v a, v b, v c}
  let right : Set (ℝ × ℝ) := convexHull ℝ {v a, v b, v d}
  have hadb : 0 < sig (v a) (v d) (v b) := by
    rw [sig_swap]
    linarith
  have hdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume left right := by
    have h := gen_adjacent_triangles_aeDisjoint
      (v a) (v d) (v b) (v c) hadb hc
    have hright : {v a, v d, v b} = ({v a, v b, v d} : Set (ℝ × ℝ)) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hright] at h
    exact h.symm
  have hsubset : left ∪ right ⊆ convexHull ℝ (Set.range v) := by
    intro x hx
    rcases hx with hx | hx
    · apply (convexHull_mono (s := {v a, v b, v c})
        (t := Set.range v) ?_) hx
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff,
        Set.mem_range]
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩
    · apply (convexHull_mono (s := {v a, v b, v d})
        (t := Set.range v) ?_) hx
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff,
        Set.mem_range]
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨d, rfl⟩⟩
  have hunion : MeasureTheory.volume (left ∪ right) =
      MeasureTheory.volume left + MeasureTheory.volume right :=
    MeasureTheory.measure_union₀
      ((convex_convexHull ℝ {v a, v b, v d}).nullMeasurableSet
        MeasureTheory.volume) hdisjoint
  have hmeasure : MeasureTheory.volume (left ∪ right) ≤
      MeasureTheory.volume (convexHull ℝ (Set.range v)) :=
    MeasureTheory.measure_mono hsubset
  have hreal := ENNReal.toReal_mono (volume_convexHull_ne_top v) hmeasure
  rw [hunion] at hreal
  rw [ENNReal.toReal_add (by simp [left, volume_convexHull_triple])
    (by simp [right, volume_convexHull_triple])] at hreal
  simp only [left, right, volume_convexHull_triple,
    abs_of_pos hc, abs_of_neg hd] at hreal
  rw [ENNReal.toReal_ofReal (div_nonneg hc.le (by norm_num)),
    ENNReal.toReal_ofReal (div_nonneg (neg_nonneg.mpr hd.le) (by norm_num))]
    at hreal
  rw [doubledHullArea]
  linarith

/-- A finite fan whose rays occur in strict positive order has pairwise
a.e.-disjoint triangle cells.  Since every cell uses configuration vertices,
their positive oriented-area sum is bounded by the full doubled hull area. -/
theorem anchoredFanSum_le_doubledHullArea
    {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (v : Fin 8 → ℝ × ℝ) (c : Fin m → Fin 8)
    (hpos : ∀ i j : Fin m, (0 : Fin m) < i → i < j →
      0 < sig (v (c 0)) (v (c i)) (v (c j))) :
    (∑ i : Fin (m - 2),
      sig (v (c 0)) (fanLeftGen (v ∘ c) i)
        (fanRightGen (v ∘ c) i)) ≤ doubledHullArea v := by
  let pts : Fin m → ℝ × ℝ := v ∘ c
  let cells : Fin (m - 2) → Set (ℝ × ℝ) := fanCellGen pts
  have hpair : ∀ ⦃i j : Fin (m - 2)⦄, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume (cells i) (cells j) := by
    exact gen_fan_pairwise pts (by
      intro i j hi hij
      exact hpos i j hi hij)
  have hcell (i : Fin (m - 2)) :
      MeasureTheory.volume (cells i) = ENNReal.ofReal
        (sig (v (c 0)) (fanLeftGen (v ∘ c) i)
          (fanRightGen (v ∘ c) i) / (2 : ℝ)) := by
    simp only [cells, fanCellGen, pts, fanLeftGen, fanRightGen,
      Function.comp_apply]
    rw [volume_convexHull_triple]
    rw [abs_of_pos (hpos
      ⟨i.val + 1, by omega⟩ ⟨i.val + 2, by omega⟩
      (by change 0 < i.val + 1; omega)
      (by change i.val + 1 < i.val + 2; omega))]
  have hterm (i : Fin (m - 2)) : 0 ≤
      sig (v (c 0)) (fanLeftGen (v ∘ c) i)
        (fanRightGen (v ∘ c) i) / (2 : ℝ) := by
    apply div_nonneg
    · simp only [fanLeftGen, fanRightGen, Function.comp_apply]
      exact (hpos
      ⟨i.val + 1, by omega⟩ ⟨i.val + 2, by omega⟩
      (by change 0 < i.val + 1; omega)
      (by change i.val + 1 < i.val + 2; omega)).le
    · norm_num
  have hunion : MeasureTheory.volume (⋃ i, cells i) =
      ∑ i : Fin (m - 2), MeasureTheory.volume (cells i) := by
    rw [MeasureTheory.measure_iUnion₀ hpair]
    · rw [tsum_fintype]
    · intro i
      exact (convex_convexHull ℝ _).nullMeasurableSet
        MeasureTheory.volume
  have hsubset : (⋃ i, cells i) ⊆ convexHull ℝ (Set.range v) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    have hcycle : cells i ⊆ convexHull ℝ (Set.range pts) :=
      gen_fanCell_subset_cycleHull pts i
    apply (convexHull_mono (s := Set.range pts) (t := Set.range v) ?_)
      (hcycle hi)
    rintro _ ⟨j, rfl⟩
    exact ⟨c j, rfl⟩
  have hmeasure : MeasureTheory.volume (⋃ i, cells i) ≤
      MeasureTheory.volume (convexHull ℝ (Set.range v)) :=
    MeasureTheory.measure_mono hsubset
  have hreal := ENNReal.toReal_mono (volume_convexHull_ne_top v) hmeasure
  rw [hunion] at hreal
  rw [ENNReal.toReal_sum (fun i _ => by rw [hcell]; exact ENNReal.ofReal_ne_top)]
    at hreal
  simp_rw [hcell] at hreal
  simp_rw [ENNReal.toReal_ofReal (hterm _)] at hreal
  rw [doubledHullArea]
  rw [← Finset.sum_div] at hreal
  linarith

/--
The volume of the convex hull of any configuration carrying an
IsHullArea certificate is half its certified doubled hull area.
-/
theorem volume_of_isHullArea
    {v : Fin 8 → ℝ × ℝ} {H : ℝ} (h : IsHullArea v H) :
    MeasureTheory.volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (H / 2) := by
  cases h with
  | hull3 c hc hpos hcover hH =>
      rw [hH, gen_convexHull_range_eq_cycle v c hcover]
      exact gen_volume_cycle3 v c hpos
  | hull4 c hc hpos hcover hH =>
      rw [hH, gen_convexHull_range_eq_cycle v c hcover]
      exact gen_volume_cycle4 v c hpos
  | hull5 c hc hpos hcover hH =>
      rw [hH, gen_convexHull_range_eq_cycle v c hcover]
      exact gen_volume_cycle5 v c hpos
  | hull6 c hc hpos hcover hH =>
      rw [hH, gen_convexHull_range_eq_cycle v c hcover]
      exact gen_volume_cycle6 v c hpos
  | hull7 c hc hpos hcover hH =>
      rw [hH, gen_convexHull_range_eq_cycle v c hcover]
      exact gen_volume_cycle7 v c hpos
  | hull8 c hc hpos hcover hH =>
      rw [hH, gen_convexHull_range_eq_cycle v c hcover]
      exact gen_volume_cycle8 v c hpos

/-- Layer-3 bridge: every certified fan sum is exactly the arbitrary
convex-hull functional used by the analytic gauge layer. -/
theorem doubledHullArea_eq_of_isHullArea
    {v : Fin 8 → ℝ × ℝ} {H : ℝ} (h : IsHullArea v H) :
    doubledHullArea v = H := by
  have hnonneg : 0 ≤ H := IsHullArea_nonneg h
  rw [doubledHullArea, volume_of_isHullArea h,
    ENNReal.toReal_ofReal (div_nonneg hnonneg (by norm_num))]
  ring

end Heilbronn8
