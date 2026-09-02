/-
Planar 4-point Radon dichotomy: four points are either in convex position
(one of the six labelings of a CCW quadrilateral) or one lies in the
triangle of the other three.
-/
import Heilbronn8.Ident

namespace Heilbronn8

/-- The quadrilateral `q0 q1 q2 q3` is convex and CCW in the weak
orientation formulation. -/
def QuadCCW (q0 q1 q2 q3 : ℝ × ℝ) : Prop :=
  0 ≤ sig q0 q1 q2 ∧
  0 ≤ sig q0 q1 q3 ∧
  0 ≤ sig q0 q2 q3 ∧
  0 ≤ sig q1 q2 q3

/-- Barycentric criterion for a positively oriented triangle. -/
lemma inTri_of_sig (x A B C : ℝ × ℝ) (hD : 0 < sig A B C)
    (h1 : 0 ≤ sig x B C) (h2 : 0 ≤ sig A x C)
    (h3 : 0 ≤ sig A B x) :
    InTri x A B C := by
  have hDne : sig A B C ≠ 0 := ne_of_gt hD
  have hsum :
      sig x B C + sig A x C + sig A B x = sig A B C := by
    simp only [sig]
    ring
  refine
    ⟨sig x B C / sig A B C,
      sig A x C / sig A B C,
      sig A B x / sig A B C,
      div_nonneg h1 hD.le,
      div_nonneg h2 hD.le,
      div_nonneg h3 hD.le, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hDne]
  · have hx1 :
        x.1 * sig A B C
          =
        sig x B C * A.1 + sig A x C * B.1 + sig A B x * C.1 := by
      simp only [sig]
      ring
    have hx2 :
        x.2 * sig A B C
          =
        sig x B C * A.2 + sig A x C * B.2 + sig A B x * C.2 := by
      simp only [sig]
      ring
    have hxx : x = (x.1, x.2) := rfl
    rw [hxx, Prod.ext_iff]
    constructor
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linarith [hx1]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith [hx2]

/-- Mirror of `inTri_of_sig` for a negatively oriented triangle. -/
lemma inTri_of_sig_neg (x A B C : ℝ × ℝ) (hD : sig A B C < 0)
    (h1 : sig x B C ≤ 0) (h2 : sig A x C ≤ 0)
    (h3 : sig A B x ≤ 0) :
    InTri x A B C := by
  have hD' : 0 < sig A C B := by
    rw [sig_swap A C B]
    linarith
  have h1' : 0 ≤ sig x C B := by
    rw [sig_swap x C B]
    linarith
  have h2' : 0 ≤ sig A x B := by
    rw [sig_swap A x B]
    linarith
  have h3' : 0 ≤ sig A C x := by
    rw [sig_swap A C x]
    linarith
  obtain ⟨a, b, c, ha, hb, hc, hsum, hx⟩ :=
    inTri_of_sig x A C B hD' h1' h2' h3'
  exact ⟨a, c, b, ha, hc, hb, by linarith, by rw [hx]; module⟩

/-- A point between `A` and `B` is in every triangle `A B C`. -/
lemma inTri_of_between (x A B C : ℝ × ℝ) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hx : x = t • A + (1 - t) • B) :
    InTri x A B C := by
  refine ⟨t, 1 - t, 0, h0, by linarith, le_refl 0, by ring, ?_⟩
  simpa using hx

/-- Radon dichotomy for four points in the plane. -/
theorem radon4 (p0 p1 p2 p3 : ℝ × ℝ) :
    (QuadCCW p0 p1 p2 p3 ∨
      QuadCCW p0 p1 p3 p2 ∨
      QuadCCW p0 p2 p1 p3 ∨
      QuadCCW p0 p3 p2 p1 ∨
      QuadCCW p0 p2 p3 p1 ∨
      QuadCCW p0 p3 p1 p2) ∨
    (InTri p0 p1 p2 p3 ∨
      InTri p1 p0 p2 p3 ∨
      InTri p2 p0 p1 p3 ∨
      InTri p3 p0 p1 p2) := by
  have hc := cocycle p0 p1 p2 p3
  have e021 : sig p0 p2 p1 = -sig p0 p1 p2 := by
    simp only [sig]
    ring
  have e031 : sig p0 p3 p1 = -sig p0 p1 p3 := by
    simp only [sig]
    ring
  have e032 : sig p0 p3 p2 = -sig p0 p2 p3 := by
    simp only [sig]
    ring
  have e132 : sig p1 p3 p2 = -sig p1 p2 p3 := by
    simp only [sig]
    ring
  have e213 : sig p2 p1 p3 = -sig p1 p2 p3 := by
    simp only [sig]
    ring
  have e231 : sig p2 p3 p1 = sig p1 p2 p3 := by
    simp only [sig]
    ring
  have e312 : sig p3 p1 p2 = sig p1 p2 p3 := by
    simp only [sig]
    ring
  have e321 : sig p3 p2 p1 = -sig p1 p2 p3 := by
    simp only [sig]
    ring
  have e103 : sig p1 p0 p3 = -sig p0 p1 p3 := by
    simp only [sig]
    ring
  have e120 : sig p1 p2 p0 = sig p0 p1 p2 := by
    simp only [sig]
    ring
  rcases le_or_gt 0 (sig p0 p1 p2) with h1 | h1 <;>
    rcases le_or_gt 0 (sig p0 p1 p3) with h2 | h2 <;>
    rcases le_or_gt 0 (sig p0 p2 p3) with h3 | h3 <;>
    rcases le_or_gt 0 (sig p1 p2 p3) with h4 | h4
  -- (≥,≥,≥,≥): convex, as labeled
  · exact Or.inl (Or.inl ⟨h1, h2, h3, h4⟩)
  -- (≥,≥,≥,<): p2 inside p0 p1 p3
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (inTri_of_sig p2 p0 p1 p3 (by linarith)
        (by linarith) h3 h1))))
  -- (≥,≥,<,≥): p3 inside p0 p1 p2
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (inTri_of_sig p3 p0 p1 p2 (by linarith)
        (by linarith) (by linarith) h2))))
  -- (≥,≥,<,<): convex in order p0 p1 p3 p2
  · exact Or.inl
      (Or.inr (Or.inl ⟨h2, h1, by linarith, by linarith⟩))
  -- (≥,<,≥,≥): p0 inside p1 p2 p3
  · exact Or.inr (Or.inl
      (inTri_of_sig p0 p1 p2 p3 (by linarith)
        h3 (by linarith) (by linarith)))
  -- (≥,<,≥,<): contradicts the cocycle
  · exfalso
    linarith
  -- (≥,<,<,≥): convex in order p0 p3 p1 p2
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by linarith, by linarith, h1, by linarith⟩)))))
  -- (≥,<,<,<): p1 inside p0 p2 p3, negative orientation
  · exact Or.inr (Or.inr (Or.inl
      (inTri_of_sig_neg p1 p0 p2 p3 h3 h4.le h2.le
        (by linarith))))
  -- (<,≥,≥,≥): p1 inside p0 p2 p3
  · exact Or.inr (Or.inr (Or.inl
      (inTri_of_sig p1 p0 p2 p3 (by linarith)
        h4 h2 (by linarith))))
  -- (<,≥,≥,<): convex in order p0 p2 p1 p3
  · exact Or.inl
      (Or.inr (Or.inr
        (Or.inl ⟨by linarith, h3, h2, by linarith⟩)))
  -- (<,≥,<,≥): contradicts the cocycle
  · exfalso
    linarith
  -- (<,≥,<,<): p0 inside p1 p2 p3, negative orientation
  · exact Or.inr (Or.inl
      (inTri_of_sig_neg p0 p1 p2 p3 h4 h3.le
        (by linarith) (by linarith)))
  -- (<,<,≥,≥): convex in order p0 p2 p3 p1
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h3, by linarith, by linarith, by linarith⟩)))))
  -- (<,<,≥,<): p3 inside p0 p1 p2, negative orientation
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (inTri_of_sig_neg p3 p0 p1 p2 h1
        (by linarith) (by linarith) h2.le))))
  -- (<,<,<,≥): p2 inside p0 p1 p3, negative orientation
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (inTri_of_sig_neg p2 p0 p1 p3 h2
        (by linarith) h3.le h1.le))))
  -- (<,<,<,<): convex in reversed order p0 p3 p2 p1
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by linarith, by linarith, by linarith, by linarith⟩))))

end Heilbronn8
