/-
Cases 1 and 2 of the convex Heilbronn n = 5 proof (PROOF.md): the hull is a
triangle with two interior points, or a quadrilateral with one. Both bounds
come from fan splits whose parts are triangles of the configuration.
-/
import Heil5.Ident

namespace Heilbronn5

lemma sig_eq12 (p q : ℝ × ℝ) : sig p p q = 0 := by simp only [sig]; ring
lemma sig_eq13 (p q : ℝ × ℝ) : sig p q p = 0 := by simp only [sig]; ring
lemma sig_eq23 (p q : ℝ × ℝ) : sig p q q = 0 := by simp only [sig]; ring

lemma sig_affine_thd (p q a b c : ℝ × ℝ) (x y z : ℝ) (hxyz : x + y + z = 1) :
    sig p q (x • a + y • b + z • c)
      = x * sig p q a + y * sig p q b + z * sig p q c := by
  have hz : z = 1 - x - y := by linarith
  subst hz
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  ring

lemma sig_affine_fst4 (a b c d q r : ℝ × ℝ) (x y z t : ℝ)
    (h : x + y + z + t = 1) :
    sig (x • a + y • b + z • c + t • d) q r
      = x * sig a q r + y * sig b q r + z * sig c q r + t * sig d q r := by
  have ht : t = 1 - x - y - z := by linarith
  subst ht
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  ring

/-- Case 2: quadrilateral hull `v0 v1 v2 v3` (CCW) with `v4` in it. -/
theorem quad_case (v : Fin 5 → ℝ × ℝ) (hq : QuadPos v)
    (h4 : ∃ x y z t : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ t ∧ x + y + z + t = 1 ∧
      v 4 = x • v 0 + y • v 1 + z • v 2 + t • v 3) :
    4 * minTri v ≤ quadArea v := by
  obtain ⟨x, y, z, t, hx, hy, hz, ht, hs, hv4⟩ := h4
  obtain ⟨h012, h013, h023, h123⟩ := hq
  -- the four fan parts around v4, expanded through the convex combination
  have e01 : sig (v 4) (v 0) (v 1)
      = z * sig (v 0) (v 1) (v 2) + t * sig (v 0) (v 1) (v 3) := by
    rw [hv4, sig_affine_fst4 _ _ _ _ _ _ x y z t hs, sig_eq12,
      sig_eq13 (v 1) (v 0), sig_rotate (v 2) (v 0) (v 1),
      sig_rotate (v 3) (v 0) (v 1)]
    ring
  have e12 : sig (v 4) (v 1) (v 2)
      = x * sig (v 0) (v 1) (v 2) + t * sig (v 1) (v 2) (v 3) := by
    rw [hv4, sig_affine_fst4 _ _ _ _ _ _ x y z t hs, sig_eq12,
      sig_eq13 (v 2) (v 1), sig_rotate (v 3) (v 1) (v 2)]
    ring
  have e23 : sig (v 4) (v 2) (v 3)
      = x * sig (v 0) (v 2) (v 3) + y * sig (v 1) (v 2) (v 3) := by
    rw [hv4, sig_affine_fst4 _ _ _ _ _ _ x y z t hs, sig_eq12,
      sig_eq13 (v 3) (v 2)]
    ring
  have e30 : sig (v 4) (v 3) (v 0)
      = y * sig (v 0) (v 1) (v 3) + z * sig (v 0) (v 2) (v 3) := by
    rw [hv4, sig_affine_fst4 _ _ _ _ _ _ x y z t hs, sig_eq13 (v 0) (v 3),
      sig_eq12]
    have r1 : sig (v 1) (v 3) (v 0) = sig (v 0) (v 1) (v 3) := by
      rw [sig_rotate (v 1) (v 3) (v 0), sig_rotate (v 3) (v 0) (v 1)]
    have r2 : sig (v 2) (v 3) (v 0) = sig (v 0) (v 2) (v 3) := by
      rw [sig_rotate (v 2) (v 3) (v 0), sig_rotate (v 3) (v 0) (v 2)]
    rw [r1, r2]; ring
  -- nonnegativity of the parts
  have p01 : 0 ≤ sig (v 4) (v 0) (v 1) := by
    rw [e01]; exact add_nonneg (mul_nonneg hz h012) (mul_nonneg ht h013)
  have p12 : 0 ≤ sig (v 4) (v 1) (v 2) := by
    rw [e12]; exact add_nonneg (mul_nonneg hx h012) (mul_nonneg ht h123)
  have p23 : 0 ≤ sig (v 4) (v 2) (v 3) := by
    rw [e23]; exact add_nonneg (mul_nonneg hx h023) (mul_nonneg hy h123)
  have p30 : 0 ≤ sig (v 4) (v 3) (v 0) := by
    rw [e30]; exact add_nonneg (mul_nonneg hy h013) (mul_nonneg hz h023)
  -- each part dominates minTri (it is |sig| of a triple of the points)
  have m01 : minTri v ≤ sig (v 4) (v 0) (v 1) := by
    have h := minTri_le_014 v
    have : sig (v 0) (v 1) (v 4) = sig (v 4) (v 0) (v 1) := by
      simp only [sig]; ring
    rwa [this, abs_of_nonneg p01] at h
  have m12 : minTri v ≤ sig (v 4) (v 1) (v 2) := by
    have h := minTri_le_124 v
    have : sig (v 1) (v 2) (v 4) = sig (v 4) (v 1) (v 2) := by
      simp only [sig]; ring
    rwa [this, abs_of_nonneg p12] at h
  have m23 : minTri v ≤ sig (v 4) (v 2) (v 3) := by
    have h := minTri_le_234 v
    have : sig (v 2) (v 3) (v 4) = sig (v 4) (v 2) (v 3) := by
      simp only [sig]; ring
    rwa [this, abs_of_nonneg p23] at h
  have m30 : minTri v ≤ sig (v 4) (v 3) (v 0) := by
    have h := minTri_le_034 v
    have habs : |sig (v 0) (v 3) (v 4)| = |sig (v 4) (v 3) (v 0)| := by
      have : sig (v 0) (v 3) (v 4) = -sig (v 4) (v 3) (v 0) := by
        simp only [sig]; ring
      rw [this, abs_neg]
    rwa [habs, abs_of_nonneg p30] at h
  -- the fan split identity
  have hsplit := split4 (v 4) (v 0) (v 1) (v 2) (v 3)
  unfold quadArea
  linarith [m01, m12, m23, m30, hsplit]

/-- Cyclic sign selection: three reals with a vanishing nonnegative convex
combination contain a cyclically consecutive pair `(s_i >= 0, s_j <= 0)`. -/
lemma cyclic_select (s0 s1 s2 m0 m1 m2 : ℝ) (h0 : 0 ≤ m0) (h1 : 0 ≤ m1)
    (h2 : 0 ≤ m2) (hs : m0 + m1 + m2 = 1)
    (hz : m0 * s0 + m1 * s1 + m2 * s2 = 0) :
    (0 ≤ s0 ∧ s1 ≤ 0) ∨ (0 ≤ s1 ∧ s2 ≤ 0) ∨ (0 ≤ s2 ∧ s0 ≤ 0) := by
  have hbig : 1 / 3 ≤ m0 ∨ 1 / 3 ≤ m1 ∨ 1 / 3 ≤ m2 := by
    by_contra h
    push_neg at h
    linarith [h.1, h.2.1, h.2.2]
  rcases le_total 0 s0 with hs0 | hs0 <;>
    rcases le_total 0 s1 with hs1 | hs1 <;>
      rcases le_total 0 s2 with hs2 | hs2
  -- (≥,≥,≥): the heavyweight coordinate vanishes downward
  · rcases hbig with hb | hb | hb
    · have hzero : s0 ≤ 0 := by
        nlinarith [mul_nonneg h1 hs1, mul_nonneg h2 hs2,
          mul_le_mul_of_nonneg_right hb hs0]
      exact Or.inr (Or.inr ⟨hs2, hzero⟩)
    · have hzero : s1 ≤ 0 := by
        nlinarith [mul_nonneg h0 hs0, mul_nonneg h2 hs2,
          mul_le_mul_of_nonneg_right hb hs1]
      exact Or.inl ⟨hs0, hzero⟩
    · have hzero : s2 ≤ 0 := by
        nlinarith [mul_nonneg h0 hs0, mul_nonneg h1 hs1,
          mul_le_mul_of_nonneg_right hb hs2]
      exact Or.inr (Or.inl ⟨hs1, hzero⟩)
  · exact Or.inr (Or.inl ⟨hs1, hs2⟩)
  · exact Or.inl ⟨hs0, hs1⟩
  · exact Or.inl ⟨hs0, hs1⟩
  · exact Or.inr (Or.inr ⟨hs2, hs0⟩)
  · exact Or.inr (Or.inl ⟨hs1, hs2⟩)
  · exact Or.inr (Or.inr ⟨hs2, hs0⟩)
  -- (≤,≤,≤): the heavyweight coordinate vanishes upward
  · rcases hbig with hb | hb | hb
    · have hzero : 0 ≤ s0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hs1,
          mul_nonpos_of_nonneg_of_nonpos h2 hs2,
          mul_le_mul_of_nonpos_right hb hs0]
      exact Or.inl ⟨hzero, hs1⟩
    · have hzero : 0 ≤ s1 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h0 hs0,
          mul_nonpos_of_nonneg_of_nonpos h2 hs2,
          mul_le_mul_of_nonpos_right hb hs1]
      exact Or.inr (Or.inl ⟨hzero, hs2⟩)
    · have hzero : 0 ≤ s2 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h0 hs0,
          mul_nonpos_of_nonneg_of_nonpos h1 hs1,
          mul_le_mul_of_nonpos_right hb hs2]
      exact Or.inr (Or.inr ⟨hzero, hs0⟩)

/-- Case 1: triangle hull `v0 v1 v2` (CCW) with `v3` and `v4` in it. -/
theorem tri_case (v : Fin 5 → ℝ × ℝ) (h012 : 0 ≤ sig (v 0) (v 1) (v 2))
    (h3 : InTri (v 3) (v 0) (v 1) (v 2))
    (h4 : InTri (v 4) (v 0) (v 1) (v 2)) :
    5 * minTri v ≤ sig (v 0) (v 1) (v 2) := by
  obtain ⟨a, b, c, ha, hb, hc, habc, hv3⟩ := h3
  obtain ⟨x, y, z, hx, hy, hz, hxyz, hv4⟩ := h4
  -- first split: the parts of the hull triangle around v3
  have eP0 : sig (v 3) (v 0) (v 1) = c * sig (v 0) (v 1) (v 2) := by
    rw [hv3, sig_affine_fst _ _ _ _ _ a b c habc, sig_eq12,
      sig_eq13 (v 1) (v 0), sig_rotate (v 2) (v 0) (v 1)]
    ring
  have eP1 : sig (v 3) (v 1) (v 2) = a * sig (v 0) (v 1) (v 2) := by
    rw [hv3, sig_affine_fst _ _ _ _ _ a b c habc, sig_eq12,
      sig_eq13 (v 2) (v 1)]
    ring
  have eP2 : sig (v 3) (v 2) (v 0) = b * sig (v 0) (v 1) (v 2) := by
    rw [hv3, sig_affine_fst _ _ _ _ _ a b c habc, sig_eq13 (v 0) (v 2),
      sig_eq12]
    have r : sig (v 1) (v 2) (v 0) = sig (v 0) (v 1) (v 2) := by
      rw [sig_rotate (v 1) (v 2) (v 0), sig_rotate (v 2) (v 0) (v 1)]
    rw [r]; ring
  -- the same expansions for v4
  have eQ0 : sig (v 4) (v 0) (v 1) = z * sig (v 0) (v 1) (v 2) := by
    rw [hv4, sig_affine_fst _ _ _ _ _ x y z hxyz, sig_eq12,
      sig_eq13 (v 1) (v 0), sig_rotate (v 2) (v 0) (v 1)]
    ring
  have eQ1 : sig (v 4) (v 1) (v 2) = x * sig (v 0) (v 1) (v 2) := by
    rw [hv4, sig_affine_fst _ _ _ _ _ x y z hxyz, sig_eq12,
      sig_eq13 (v 2) (v 1)]
    ring
  have eQ2 : sig (v 4) (v 2) (v 0) = y * sig (v 0) (v 1) (v 2) := by
    rw [hv4, sig_affine_fst _ _ _ _ _ x y z hxyz, sig_eq13 (v 0) (v 2),
      sig_eq12]
    have r : sig (v 1) (v 2) (v 0) = sig (v 0) (v 1) (v 2) := by
      rw [sig_rotate (v 1) (v 2) (v 0), sig_rotate (v 2) (v 0) (v 1)]
    rw [r]; ring
  -- bounds for the first-split parts
  have hP0 : 0 ≤ sig (v 3) (v 0) (v 1) := by
    rw [eP0]; exact mul_nonneg hc h012
  have hP1 : 0 ≤ sig (v 3) (v 1) (v 2) := by
    rw [eP1]; exact mul_nonneg ha h012
  have hP2 : 0 ≤ sig (v 3) (v 2) (v 0) := by
    rw [eP2]; exact mul_nonneg hb h012
  have mP0 : minTri v ≤ sig (v 3) (v 0) (v 1) := by
    have h := minTri_le_013 v
    have e : sig (v 0) (v 1) (v 3) = sig (v 3) (v 0) (v 1) := by
      simp only [sig]; ring
    rwa [e, abs_of_nonneg hP0] at h
  have mP1 : minTri v ≤ sig (v 3) (v 1) (v 2) := by
    have h := minTri_le_123 v
    have e : sig (v 1) (v 2) (v 3) = sig (v 3) (v 1) (v 2) := by
      simp only [sig]; ring
    rwa [e, abs_of_nonneg hP1] at h
  have mP2 : minTri v ≤ sig (v 3) (v 2) (v 0) := by
    have h := minTri_le_023 v
    have e : sig (v 0) (v 2) (v 3) = -sig (v 3) (v 2) (v 0) := by
      simp only [sig]; ring
    rw [e, abs_neg] at h
    rwa [abs_of_nonneg hP2] at h
  have hsplitP := split3 (v 3) (v 0) (v 1) (v 2)
  -- second stage: locate v4 relative to the rays from v3
  have hzero : a * sig (v 4) (v 3) (v 0) + b * sig (v 4) (v 3) (v 1)
      + c * sig (v 4) (v 3) (v 2) = 0 := by
    have h := sig_affine_thd (v 4) (v 3) (v 0) (v 1) (v 2) a b c habc
    rw [← hv3, sig_eq23] at h
    linarith
  rcases cyclic_select (sig (v 4) (v 3) (v 0)) (sig (v 4) (v 3) (v 1))
      (sig (v 4) (v 3) (v 2)) a b c ha hb hc habc hzero with
    ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  -- v4 in subtriangle (v3, v0, v1)
  · have hA : 0 ≤ sig (v 4) (v 3) (v 0) := hi
    have hB : 0 ≤ sig (v 4) (v 0) (v 1) := by
      rw [eQ0]; exact mul_nonneg hz h012
    have hC : 0 ≤ sig (v 4) (v 1) (v 3) := by
      have e : sig (v 4) (v 1) (v 3) = -sig (v 4) (v 3) (v 1) := by
        simp only [sig]; ring
      rw [e]; linarith
    have mA : minTri v ≤ sig (v 4) (v 3) (v 0) := by
      have h := minTri_le_034 v
      have e : sig (v 0) (v 3) (v 4) = -sig (v 4) (v 3) (v 0) := by
        simp only [sig]; ring
      rw [e, abs_neg] at h
      rwa [abs_of_nonneg hA] at h
    have mB : minTri v ≤ sig (v 4) (v 0) (v 1) := by
      have h := minTri_le_014 v
      have e : sig (v 0) (v 1) (v 4) = sig (v 4) (v 0) (v 1) := by
        simp only [sig]; ring
      rwa [e, abs_of_nonneg hB] at h
    have mC : minTri v ≤ sig (v 4) (v 1) (v 3) := by
      have h := minTri_le_134 v
      have e : sig (v 1) (v 3) (v 4) = sig (v 4) (v 1) (v 3) := by
        simp only [sig]; ring
      rwa [e, abs_of_nonneg hC] at h
    have hsplitQ := split3 (v 4) (v 3) (v 0) (v 1)
    -- 3m <= sig (v3) (v0) (v1), plus m each from the other two parts
    linarith [mA, mB, mC, mP1, mP2, hsplitP, hsplitQ]
  -- v4 in subtriangle (v3, v1, v2)
  · have hA : 0 ≤ sig (v 4) (v 3) (v 1) := hi
    have hB : 0 ≤ sig (v 4) (v 1) (v 2) := by
      rw [eQ1]; exact mul_nonneg hx h012
    have hC : 0 ≤ sig (v 4) (v 2) (v 3) := by
      have e : sig (v 4) (v 2) (v 3) = -sig (v 4) (v 3) (v 2) := by
        simp only [sig]; ring
      rw [e]; linarith
    have mA : minTri v ≤ sig (v 4) (v 3) (v 1) := by
      have h := minTri_le_134 v
      have e : sig (v 1) (v 3) (v 4) = -sig (v 4) (v 3) (v 1) := by
        simp only [sig]; ring
      rw [e, abs_neg] at h
      rwa [abs_of_nonneg hA] at h
    have mB : minTri v ≤ sig (v 4) (v 1) (v 2) := by
      have h := minTri_le_124 v
      have e : sig (v 1) (v 2) (v 4) = sig (v 4) (v 1) (v 2) := by
        simp only [sig]; ring
      rwa [e, abs_of_nonneg hB] at h
    have mC : minTri v ≤ sig (v 4) (v 2) (v 3) := by
      have h := minTri_le_234 v
      have e : sig (v 2) (v 3) (v 4) = sig (v 4) (v 2) (v 3) := by
        simp only [sig]; ring
      rwa [e, abs_of_nonneg hC] at h
    have hsplitQ := split3 (v 4) (v 3) (v 1) (v 2)
    linarith [mA, mB, mC, mP0, mP2, hsplitP, hsplitQ]
  -- v4 in subtriangle (v3, v2, v0)
  · have hA : 0 ≤ sig (v 4) (v 3) (v 2) := hi
    have hB : 0 ≤ sig (v 4) (v 2) (v 0) := by
      rw [eQ2]; exact mul_nonneg hy h012
    have hC : 0 ≤ sig (v 4) (v 0) (v 3) := by
      have e : sig (v 4) (v 0) (v 3) = -sig (v 4) (v 3) (v 0) := by
        simp only [sig]; ring
      rw [e]; linarith
    have mA : minTri v ≤ sig (v 4) (v 3) (v 2) := by
      have h := minTri_le_234 v
      have e : sig (v 2) (v 3) (v 4) = -sig (v 4) (v 3) (v 2) := by
        simp only [sig]; ring
      rw [e, abs_neg] at h
      rwa [abs_of_nonneg hA] at h
    have mB : minTri v ≤ sig (v 4) (v 2) (v 0) := by
      have h := minTri_le_024 v
      have e : sig (v 0) (v 2) (v 4) = -sig (v 4) (v 2) (v 0) := by
        simp only [sig]; ring
      rw [e, abs_neg] at h
      rwa [abs_of_nonneg hB] at h
    have mC : minTri v ≤ sig (v 4) (v 0) (v 3) := by
      have h := minTri_le_034 v
      have e : sig (v 0) (v 3) (v 4) = sig (v 4) (v 0) (v 3) := by
        simp only [sig]; ring
      rwa [e, abs_of_nonneg hC] at h
    have hsplitQ := split3 (v 4) (v 3) (v 2) (v 0)
    linarith [mA, mB, mC, mP0, mP1, hsplitP, hsplitQ]

end Heilbronn5
