/-
n = 4: h_convex 4 = 1/2.

Four points are either in convex position, in one of six cyclic orders, or one
of them lies in the triangle of the other three (Radon). In convex position the
hull splits into two fan triangles whose doubled areas sum to 2 and each of
which is at least `minTri`, so `minTri ≤ 1`. In the interior case the hull is a
triangle of doubled area 2 that the interior point cuts into three cells, so
`3 * minTri ≤ 2`. The unit square attains 1.
-/
import Solution.Common

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-! ## Convex position: the fan identity -/

/-- If `p i0, p i1, p i2, p i3` is a strictly convex cyclic order covering all
four indices, the two fan triangles have doubled areas summing to 2. -/
lemma quad_convex_fan (p : Fin 4 → ℝ × ℝ) (i0 i1 i2 i3 : Fin 4)
    (hcover : ∀ k : Fin 4, k = i0 ∨ k = i1 ∨ k = i2 ∨ k = i3)
    (h1 : 0 < sig (p i0) (p i1) (p i2)) (h2 : 0 < sig (p i0) (p i1) (p i3))
    (h3 : 0 < sig (p i0) (p i2) (p i3)) (h4 : 0 < sig (p i1) (p i2) (p i3))
    (hvol : volume (convexHull ℝ (Set.range p)) = 1) :
    sig (p i0) (p i1) (p i2) + sig (p i0) (p i2) (p i3) = 2 := by
  rw [set4_perm p i0 i1 i2 i3 hcover,
    HullBridge.volume_convexHull_quad (p i0) (p i1) (p i2) (p i3) h1 h2 h3 h4]
    at hvol
  have h := ENNReal.ofReal_eq_one.mp hvol
  simp only [← sig_eq] at h
  linarith

/-- Convex-position branch of the bound. -/
lemma quad_case_bound (p : Fin 4 → ℝ × ℝ) (hpos : 0 < minTri p)
    (hvol : volume (convexHull ℝ (Set.range p)) = 1) (i0 i1 i2 i3 : Fin 4)
    (hcover : ∀ k : Fin 4, k = i0 ∨ k = i1 ∨ k = i2 ∨ k = i3)
    (d01 : i0 ≠ i1) (d02 : i0 ≠ i2) (d03 : i0 ≠ i3)
    (d12 : i1 ≠ i2) (d13 : i1 ≠ i3) (d23 : i2 ≠ i3)
    (hq : HullBridge.QuadCCW (p i0) (p i1) (p i2) (p i3)) :
    minTri p ≤ 1 := by
  obtain ⟨c1, c2, c3, c4⟩ := hq
  have hne := sig_ne_zero_of_distinct p hpos
  have hs1 : 0 < sig (p i0) (p i1) (p i2) :=
    lt_of_le_of_ne c1 (Ne.symm (hne i0 i1 i2 d01 d02 d12))
  have hs2 : 0 < sig (p i0) (p i1) (p i3) :=
    lt_of_le_of_ne c2 (Ne.symm (hne i0 i1 i3 d01 d03 d13))
  have hs3 : 0 < sig (p i0) (p i2) (p i3) :=
    lt_of_le_of_ne c3 (Ne.symm (hne i0 i2 i3 d02 d03 d23))
  have hs4 : 0 < sig (p i1) (p i2) (p i3) :=
    lt_of_le_of_ne c4 (Ne.symm (hne i1 i2 i3 d12 d13 d23))
  have hsum := quad_convex_fan p i0 i1 i2 i3 hcover hs1 hs2 hs3 hs4 hvol
  have b1 : minTri p ≤ sig (p i0) (p i1) (p i2) := by
    have h := minTri_le_of_distinct p i0 i1 i2 d01 d02 d12
    rwa [abs_of_pos hs1] at h
  have b2 : minTri p ≤ sig (p i0) (p i2) (p i3) := by
    have h := minTri_le_of_distinct p i0 i2 i3 d02 d03 d23
    rwa [abs_of_pos hs3] at h
  linarith

/-! ## Interior point: the three-cell split -/

/-- Interior branch of the bound: `p i3` inside the triangle `p i0 p i1 p i2`.
-/
lemma inTri_case_bound (p : Fin 4 → ℝ × ℝ)
    (hvol : volume (convexHull ℝ (Set.range p)) = 1) (i0 i1 i2 i3 : Fin 4)
    (hcover : ∀ k : Fin 4, k = i0 ∨ k = i1 ∨ k = i2 ∨ k = i3)
    (d01 : i0 ≠ i1) (d02 : i0 ≠ i2) (d03 : i0 ≠ i3)
    (d12 : i1 ≠ i2) (d13 : i1 ≠ i3) (d23 : i2 ≠ i3)
    (hin : HullBridge.InTri (p i3) (p i0) (p i1) (p i2)) :
    3 * minTri p ≤ 2 := by
  have hmem : p i3 ∈ convexHull ℝ ({p i0, p i1, p i2} : Set (ℝ × ℝ)) :=
    (HullBridge.inTri_iff_mem_convexHull (p i3) (p i0) (p i1) (p i2)).mp hin
  have hsub : Set.range p ⊆ convexHull ℝ ({p i0, p i1, p i2} : Set (ℝ × ℝ)) := by
    rintro x ⟨k, rfl⟩
    rcases hcover k with hk | hk | hk | hk
    · rw [hk]; exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · rw [hk]
      exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · rw [hk]
      exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl))
    · rw [hk]; exact hmem
  have hhull : convexHull ℝ (Set.range p)
      = convexHull ℝ ({p i0, p i1, p i2} : Set (ℝ × ℝ)) :=
    HullBridge.convexHull_eq_triangle_of_inTri (Set.range p) (p i0) (p i1)
      (p i2) hsub ⟨i0, rfl⟩ ⟨i1, rfl⟩ ⟨i2, rfl⟩
  rw [hhull, HullBridge.volume_triangle] at hvol
  have h := ENNReal.ofReal_eq_one.mp hvol
  simp only [← sig_eq] at h
  have hbig : |sig (p i0) (p i1) (p i2)| = 2 := by linarith
  have hsplit := abs_sig_sum_of_inTri (p i0) (p i1) (p i2) (p i3) hin
  rw [hbig] at hsplit
  have b1 : minTri p ≤ |sig (p i0) (p i1) (p i3)| :=
    minTri_le_of_distinct p i0 i1 i3 d01 d03 d13
  have b2 : minTri p ≤ |sig (p i1) (p i2) (p i3)| :=
    minTri_le_of_distinct p i1 i2 i3 d12 d13 d23
  have b3 : minTri p ≤ |sig (p i2) (p i0) (p i3)| :=
    minTri_le_of_distinct p i2 i0 i3 (Ne.symm d02) d23 d03
  linarith

/-! ## The bound -/

theorem minTri_four_le_one (p : Fin 4 → ℝ × ℝ)
    (hvol : volume (convexHull ℝ (Set.range p)) = 1) : minTri p ≤ 1 := by
  rcases le_or_gt (minTri p) 0 with hz | hpos
  · linarith
  rcases HullBridge.radon4 (p 0) (p 1) (p 2) (p 3) with hconv | hint
  · rcases hconv with hq | hq | hq | hq | hq | hq
    · exact quad_case_bound p hpos hvol 0 1 2 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hq
    · exact quad_case_bound p hpos hvol 0 1 3 2 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hq
    · exact quad_case_bound p hpos hvol 0 2 1 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hq
    · exact quad_case_bound p hpos hvol 0 3 2 1 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hq
    · exact quad_case_bound p hpos hvol 0 2 3 1 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hq
    · exact quad_case_bound p hpos hvol 0 3 1 2 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hq
  · rcases hint with hin | hin | hin | hin
    · have h := inTri_case_bound p hvol 1 2 3 0 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      linarith
    · have h := inTri_case_bound p hvol 0 2 3 1 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      linarith
    · have h := inTri_case_bound p hvol 0 1 3 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      linarith
    · have h := inTri_case_bound p hvol 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      linarith

/-! ## Witness: the unit square -/

noncomputable def cfg4 : Fin 4 → ℝ × ℝ := ![(0, 0), (1, 0), (1, 1), (0, 1)]

private lemma cfg4_pts : cfg4 0 = ((0 : ℝ), (0 : ℝ)) ∧ cfg4 1 = ((1 : ℝ), (0 : ℝ))
    ∧ cfg4 2 = ((1 : ℝ), (1 : ℝ)) ∧ cfg4 3 = ((0 : ℝ), (1 : ℝ)) :=
  ⟨by simp [cfg4], by simp [cfg4], by simp [cfg4], by simp [cfg4]⟩

theorem cfg4_s012 : sig (cfg4 0) (cfg4 1) (cfg4 2) = 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := cfg4_pts
  rw [e0, e1, e2]; simp only [sig]; norm_num

theorem cfg4_s013 : sig (cfg4 0) (cfg4 1) (cfg4 3) = 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := cfg4_pts
  rw [e0, e1, e3]; simp only [sig]; norm_num

theorem cfg4_s023 : sig (cfg4 0) (cfg4 2) (cfg4 3) = 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := cfg4_pts
  rw [e0, e2, e3]; simp only [sig]; norm_num

theorem cfg4_s123 : sig (cfg4 1) (cfg4 2) (cfg4 3) = 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := cfg4_pts
  rw [e1, e2, e3]; simp only [sig]; norm_num

theorem cfg4_volume : volume (convexHull ℝ (Set.range cfg4)) = 1 := by
  rw [volume_hull_fin4_strict cfg4 (by rw [cfg4_s012]; norm_num)
      (by rw [cfg4_s013]; norm_num) (by rw [cfg4_s023]; norm_num)
      (by rw [cfg4_s123]; norm_num), cfg4_s012, cfg4_s023]
  rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, ENNReal.ofReal_one]

/-- The four ordered triples of `Fin 4` all have the same absolute doubled
area, so that value is `minTri`. -/
theorem minTri_four_eq (v : Fin 4 → ℝ × ℝ) (c : ℝ)
    (h1 : |sig (v 0) (v 1) (v 2)| = c) (h2 : |sig (v 0) (v 1) (v 3)| = c)
    (h3 : |sig (v 0) (v 2) (v 3)| = c) (h4 : |sig (v 1) (v 2) (v 3)| = c) :
    minTri v = c := by
  apply le_antisymm
  · rw [← h1]
    exact minTri_le v 0 1 2 (by decide) (by decide)
  · apply le_minTri
    intro t ht
    have hmem : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    rcases triple_cases4 t.1 t.2.1 t.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩
    · rw [q0, q1, q2, h1]
    · rw [q0, q1, q2, h2]
    · rw [q0, q1, q2, h3]
    · rw [q0, q1, q2, h4]

theorem cfg4_minTri : minTri cfg4 = 2 * v4 := by
  rw [show (2 : ℝ) * v4 = 1 by rw [v4]; norm_num]
  refine minTri_four_eq cfg4 1 ?_ ?_ ?_ ?_
  · rw [cfg4_s012]; exact abs_one
  · rw [cfg4_s013]; exact abs_one
  · rw [cfg4_s023]; exact abs_one
  · rw [cfg4_s123]; exact abs_one

/-! ## Challenge theorems -/

theorem heilbronn_convex_four_attained :
    ∃ p : Fin 4 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v4 :=
  ⟨cfg4, cfg4_volume, cfg4_minTri⟩

theorem heilbronn_convex_four : h_convex 4 = v4 := by
  apply h_convex_eq
  · exact ⟨by norm_num [v4], by norm_num [v4], heilbronn_convex_four_attained⟩
  · rintro r ⟨_, _, p, hvol, hmin⟩
    have hb := minTri_four_le_one p hvol
    rw [hmin] at hb
    rw [v4]
    linarith

noncomputable def witness4 : Fin 4 → ℝ × ℝ :=
  heilbronn_convex_four_attained.choose

theorem witness4_spec :
    MeasureTheory.volume (convexHull ℝ (Set.range witness4)) = 1 ∧
      minTri witness4 = 2 * v4 :=
  heilbronn_convex_four_attained.choose_spec

/-! ## Uniqueness

An optimal 4-point configuration is a parallelogram of area 1. Convex position
forces the two fan triangles to have doubled area 1 each, and the cocycle
identity forces the other diagonal's two triangles to do the same; four equal
triangles is exactly the parallelogram condition. Two parallelograms are
related by the affine map matching three of their vertices, since the fourth
vertex is determined by the other three. -/

/-- Three doubled areas equal to 1 force the parallelogram relation. -/
lemma parallelogram_of_sigs (a b c d : ℝ × ℝ) (h1 : sig a b c = 1)
    (h2 : sig a c d = 1) (h3 : sig a b d = 1) : c = b + d - a := by
  simp only [sig] at h1 h2 h3
  have hx : c.1 - b.1 - d.1 + a.1 = 0 := by
    linear_combination (d.1 - a.1) * h1 + (b.1 - a.1) * h2 - (c.1 - a.1) * h3
  have hy : c.2 - b.2 - d.2 + a.2 = 0 := by
    linear_combination (d.2 - a.2) * h1 + (b.2 - a.2) * h2 - (c.2 - a.2) * h3
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.fst_sub]; linarith
  · simp only [Prod.snd_add, Prod.snd_sub]; linarith

/-- Affine maps preserve the parallelogram relation. -/
lemma affMap_parallelogram (a b c d e f : ℝ) (w0 w1 w2 : ℝ × ℝ) :
    HullBridge.affMap a b c d e f (w1 + w2 - w0)
      = HullBridge.affMap a b c d e f w1 + HullBridge.affMap a b c d e f w2
        - HullBridge.affMap a b c d e f w0 := by
  simp only [HullBridge.affMap, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor <;> ring

/-- A permutation of `Fin 4` from a function and its explicit inverse. -/
private def permOf (f g : Fin 4 → Fin 4) (h1 : ∀ x, g (f x) = x)
    (h2 : ∀ x, f (g x) = x) : Equiv.Perm (Fin 4) :=
  ⟨f, g, h1, h2⟩

/-- In an optimal configuration every fan triangle of the convex order has
doubled area exactly 1. -/
lemma quad_case_optimal (v : Fin 4 → ℝ × ℝ)
    (hvol : volume (convexHull ℝ (Set.range v)) = 1) (hmin : minTri v = 1)
    (i0 i1 i2 i3 : Fin 4)
    (hcover : ∀ k : Fin 4, k = i0 ∨ k = i1 ∨ k = i2 ∨ k = i3)
    (d01 : i0 ≠ i1) (d02 : i0 ≠ i2) (d03 : i0 ≠ i3)
    (d12 : i1 ≠ i2) (d13 : i1 ≠ i3) (d23 : i2 ≠ i3)
    (hq : HullBridge.QuadCCW (v i0) (v i1) (v i2) (v i3)) :
    sig (v i0) (v i1) (v i2) = 1 ∧ sig (v i0) (v i2) (v i3) = 1 ∧
      sig (v i0) (v i1) (v i3) = 1 := by
  have hpos : 0 < minTri v := by rw [hmin]; norm_num
  obtain ⟨c1, c2, c3, c4⟩ := hq
  have hne := sig_ne_zero_of_distinct v hpos
  have hs1 : 0 < sig (v i0) (v i1) (v i2) :=
    lt_of_le_of_ne c1 (Ne.symm (hne i0 i1 i2 d01 d02 d12))
  have hs2 : 0 < sig (v i0) (v i1) (v i3) :=
    lt_of_le_of_ne c2 (Ne.symm (hne i0 i1 i3 d01 d03 d13))
  have hs3 : 0 < sig (v i0) (v i2) (v i3) :=
    lt_of_le_of_ne c3 (Ne.symm (hne i0 i2 i3 d02 d03 d23))
  have hs4 : 0 < sig (v i1) (v i2) (v i3) :=
    lt_of_le_of_ne c4 (Ne.symm (hne i1 i2 i3 d12 d13 d23))
  have hsum := quad_convex_fan v i0 i1 i2 i3 hcover hs1 hs2 hs3 hs4 hvol
  have b1 : 1 ≤ sig (v i0) (v i1) (v i2) := by
    have h := minTri_le_of_distinct v i0 i1 i2 d01 d02 d12
    rwa [abs_of_pos hs1, hmin] at h
  have b2 : 1 ≤ sig (v i0) (v i2) (v i3) := by
    have h := minTri_le_of_distinct v i0 i2 i3 d02 d03 d23
    rwa [abs_of_pos hs3, hmin] at h
  have b3 : 1 ≤ sig (v i0) (v i1) (v i3) := by
    have h := minTri_le_of_distinct v i0 i1 i3 d01 d03 d13
    rwa [abs_of_pos hs2, hmin] at h
  have b4 : 1 ≤ sig (v i1) (v i2) (v i3) := by
    have h := minTri_le_of_distinct v i1 i2 i3 d12 d13 d23
    rwa [abs_of_pos hs4, hmin] at h
  have hcoc : sig (v i1) (v i2) (v i3) - sig (v i0) (v i2) (v i3)
      + sig (v i0) (v i1) (v i3) - sig (v i0) (v i1) (v i2) = 0 :=
    HullBridge.cocycle (v i0) (v i1) (v i2) (v i3)
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Every optimal configuration is a labelled parallelogram. -/
lemma four_optimal_structure (v : Fin 4 → ℝ × ℝ)
    (hvol : volume (convexHull ℝ (Set.range v)) = 1) (hmin : minTri v = 1) :
    ∃ σ : Equiv.Perm (Fin 4),
      sig (v (σ 0)) (v (σ 1)) (v (σ 2)) = 1 ∧
      sig (v (σ 0)) (v (σ 2)) (v (σ 3)) = 1 ∧
      sig (v (σ 0)) (v (σ 1)) (v (σ 3)) = 1 ∧
      v (σ 2) = v (σ 1) + v (σ 3) - v (σ 0) := by
  rcases HullBridge.radon4 (v 0) (v 1) (v 2) (v 3) with hconv | hint
  · rcases hconv with hq | hq | hq | hq | hq | hq
    · obtain ⟨e1, e2, e3⟩ := quad_case_optimal v hvol hmin 0 1 2 3 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq
      exact ⟨permOf ![0, 1, 2, 3] ![0, 1, 2, 3] (by decide) (by decide), e1, e2,
        e3, parallelogram_of_sigs _ _ _ _ e1 e2 e3⟩
    · obtain ⟨e1, e2, e3⟩ := quad_case_optimal v hvol hmin 0 1 3 2 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq
      exact ⟨permOf ![0, 1, 3, 2] ![0, 1, 3, 2] (by decide) (by decide), e1, e2,
        e3, parallelogram_of_sigs _ _ _ _ e1 e2 e3⟩
    · obtain ⟨e1, e2, e3⟩ := quad_case_optimal v hvol hmin 0 2 1 3 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq
      exact ⟨permOf ![0, 2, 1, 3] ![0, 2, 1, 3] (by decide) (by decide), e1, e2,
        e3, parallelogram_of_sigs _ _ _ _ e1 e2 e3⟩
    · obtain ⟨e1, e2, e3⟩ := quad_case_optimal v hvol hmin 0 3 2 1 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq
      exact ⟨permOf ![0, 3, 2, 1] ![0, 3, 2, 1] (by decide) (by decide), e1, e2,
        e3, parallelogram_of_sigs _ _ _ _ e1 e2 e3⟩
    · obtain ⟨e1, e2, e3⟩ := quad_case_optimal v hvol hmin 0 2 3 1 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq
      exact ⟨permOf ![0, 2, 3, 1] ![0, 3, 1, 2] (by decide) (by decide), e1, e2,
        e3, parallelogram_of_sigs _ _ _ _ e1 e2 e3⟩
    · obtain ⟨e1, e2, e3⟩ := quad_case_optimal v hvol hmin 0 3 1 2 (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq
      exact ⟨permOf ![0, 3, 1, 2] ![0, 2, 3, 1] (by decide) (by decide), e1, e2,
        e3, parallelogram_of_sigs _ _ _ _ e1 e2 e3⟩
  · exfalso
    rcases hint with hin | hin | hin | hin
    · have h := inTri_case_bound v hvol 1 2 3 0 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      rw [hmin] at h; norm_num at h
    · have h := inTri_case_bound v hvol 0 2 3 1 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      rw [hmin] at h; norm_num at h
    · have h := inTri_case_bound v hvol 0 1 3 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      rw [hmin] at h; norm_num at h
    · have h := inTri_case_bound v hvol 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hin
      rw [hmin] at h; norm_num at h

theorem heilbronn_convex_four_unique_from_witness
    (p : Fin 4 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hatt : minTri p = 2 * v4) :
    GaugeEquivalent witness4 p := by
  have h2v4 : (2 : ℝ) * v4 = 1 := by rw [v4]; norm_num
  obtain ⟨hwvol, hwatt⟩ := witness4_spec
  rw [h2v4] at hatt hwatt
  obtain ⟨sw, w1, w2, w3, wpar⟩ := four_optimal_structure witness4 hwvol hwatt
  obtain ⟨sp, p1, p2, p3, ppar⟩ := four_optimal_structure p hvol hatt
  have hwne : sig (witness4 (sw 0)) (witness4 (sw 1)) (witness4 (sw 3)) ≠ 0 := by
    rw [w3]; norm_num
  have hratio : 0 < sig (p (sp 0)) (p (sp 1)) (p (sp 3))
      / sig (witness4 (sw 0)) (witness4 (sw 1)) (witness4 (sw 3)) := by
    rw [w3, p3]; norm_num
  obtain ⟨a, b, c, d, e, f, hdet, h0, h1, h3⟩ :=
    HullBridge.exists_affMap_triangle (witness4 (sw 0)) (witness4 (sw 1))
      (witness4 (sw 3)) (p (sp 0)) (p (sp 1)) (p (sp 3)) hwne hratio
  have key : ∀ j : Fin 4, p (sp j) = HullBridge.affMap a b c d e f (witness4 (sw j)) := by
    intro j
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · exact h0.symm
    · exact h1.symm
    · rw [wpar, affMap_parallelogram, h0, h1, h3]
      exact ppar
    · exact h3.symm
  refine ⟨sp.symm.trans sw, ⟨a, b, c, d, e, f, hdet⟩, ?_⟩
  funext i
  have hj := key (sp.symm i)
  rw [Equiv.apply_symm_apply] at hj
  rw [Equiv.trans_apply]
  exact hj

end HeilbronnChallenge
