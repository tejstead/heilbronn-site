/-
Inserting a fifth point into a strictly convex CCW quadrilateral. The
Grassmann-Pluecker certificates (verified in sympy first) show: a point
seeing exactly one edge inserts into the cyclic order with all ten signed
areas positive; seeing two adjacent edges puts the shared vertex inside a
triangle; seeing two opposite edges is impossible.
-/
import Heil5.Radon

namespace Heilbronn5

/-- Pivot-r0 Grassmann-Pluecker instance. -/
lemma gp_r0 (r0 r1 r2 r3 x : ℝ × ℝ) :
    sig r0 r1 r3 * sig r0 r2 x + sig r0 r1 r2 * sig r3 r0 x
      - sig r0 r1 x * sig r0 r2 r3 = 0 := by
  simp only [sig]; ring

/-- Pivot-r3 Grassmann-Pluecker instance. -/
lemma gp_r3 (r0 r1 r2 r3 x : ℝ × ℝ) :
    sig r0 r2 r3 * sig r1 r3 x + sig r3 r0 x * sig r1 r2 r3
      - sig r2 r3 x * sig r0 r1 r3 = 0 := by
  simp only [sig]; ring

/-- Pivot-r1 Grassmann-Pluecker instance. -/
lemma gp_r1 (r0 r1 r2 r3 x : ℝ × ℝ) :
    sig r0 r1 r2 * sig r1 r3 x - sig r1 r2 x * sig r0 r1 r3
      + sig r1 r2 r3 * sig r0 r1 x = 0 := by
  simp only [sig]; ring

/-- If all four edge signs are nonnegative, the point is in one of the two
diagonal triangles of the quadrilateral. -/
lemma in_quad_of_edges (r0 r1 r2 r3 x : ℝ × ℝ)
    (hc1 : 0 < sig r0 r1 r2) (hc3 : 0 < sig r0 r2 r3)
    (he0 : 0 ≤ sig r0 r1 x) (he1 : 0 ≤ sig r1 r2 x)
    (he2 : 0 ≤ sig r2 r3 x) (he3 : 0 ≤ sig r3 r0 x) :
    InTri x r0 r1 r2 ∨ InTri x r0 r2 r3 := by
  rcases le_total 0 (sig r0 r2 x) with hd | hd
  · refine Or.inr (inTri_of_sig x r0 r2 r3 hc3 ?_ ?_ hd)
    · rw [show sig x r2 r3 = sig r2 r3 x from by simp only [sig]; ring]
      exact he2
    · rw [show sig r0 x r3 = sig r3 r0 x from by simp only [sig]; ring]
      exact he3
  · refine Or.inl (inTri_of_sig x r0 r1 r2 hc1 ?_ ?_ he0)
    · rw [show sig x r1 r2 = sig r1 r2 x from by simp only [sig]; ring]
      exact he1
    · rw [show sig r0 x r2 = -sig r0 r2 x from by simp only [sig]; ring]
      linarith

/-- Two adjacent negative edge signs put the shared vertex inside the
triangle of its neighbors and the external point. -/
lemma vertex_in_adj (r0 r1 r2 x : ℝ × ℝ) (hc1 : 0 < sig r0 r1 r2)
    (he0 : sig r0 r1 x < 0) (he1 : sig r1 r2 x < 0) :
    InTri r1 r0 r2 x := by
  have hd : sig r0 r2 x < 0 := by
    have hcc := cocycle r0 r1 r2 x
    linarith
  refine inTri_of_sig_neg r1 r0 r2 x hd he1.le he0.le ?_
  rw [show sig r0 r2 r1 = -sig r0 r1 r2 from by simp only [sig]; ring]
  linarith

/-- Two opposite negative edge signs (with the other two positive) are
impossible for a strictly convex CCW quadrilateral. -/
lemma opposite_false (r0 r1 r2 r3 x : ℝ × ℝ)
    (hc1 : 0 < sig r0 r1 r2) (hc2 : 0 < sig r0 r1 r3)
    (hc3 : 0 < sig r0 r2 r3) (hc4 : 0 < sig r1 r2 r3)
    (he0 : sig r0 r1 x < 0) (he1 : 0 < sig r1 r2 x)
    (he2 : sig r2 r3 x < 0) (he3 : 0 < sig r3 r0 x) : False := by
  have hA := gp_r1 r0 r1 r2 r3 x
  have hB := gp_r3 r0 r1 r2 r3 x
  nlinarith [hA, hB, hc1, hc3,
    mul_pos (mul_pos he1 hc2) hc3,
    mul_pos (mul_pos hc4 (neg_pos.mpr he0)) hc3,
    mul_pos (mul_pos he3 hc4) hc1,
    mul_pos (mul_pos (neg_pos.mpr he2) hc2) hc1]

/-- First skip triple of the insertion pentagon. -/
lemma skip1_pos (r0 r1 r2 r3 x : ℝ × ℝ)
    (hc1 : 0 < sig r0 r1 r2) (hc2 : 0 < sig r0 r1 r3)
    (hc3 : 0 < sig r0 r2 r3)
    (he0 : 0 < sig r0 r1 x) (he3 : sig r3 r0 x < 0) :
    0 < sig r0 r2 x := by
  have h := gp_r0 r0 r1 r2 r3 x
  nlinarith [h, hc2, mul_pos he0 hc3, mul_pos hc1 (neg_pos.mpr he3)]

/-- Second skip triple of the insertion pentagon. -/
lemma skip2_pos (r0 r1 r2 r3 x : ℝ × ℝ)
    (hc2 : 0 < sig r0 r1 r3) (hc3 : 0 < sig r0 r2 r3)
    (hc4 : 0 < sig r1 r2 r3)
    (he2 : 0 < sig r2 r3 x) (he3 : sig r3 r0 x < 0) :
    0 < sig r1 r3 x := by
  have h := gp_r3 r0 r1 r2 r3 x
  nlinarith [h, hc3, mul_pos he2 hc2, mul_pos (neg_pos.mpr he3) hc4]

/-- Inserting a point that sees exactly the edge `r3 r0` yields a strictly
convex counterclockwise pentagon `(r0, r1, r2, r3, x)`. -/
theorem insertion (r0 r1 r2 r3 x : ℝ × ℝ)
    (hc1 : 0 < sig r0 r1 r2) (hc2 : 0 < sig r0 r1 r3)
    (hc3 : 0 < sig r0 r2 r3) (hc4 : 0 < sig r1 r2 r3)
    (he0 : 0 < sig r0 r1 x) (he1 : 0 < sig r1 r2 x)
    (he2 : 0 < sig r2 r3 x) (he3 : sig r3 r0 x < 0) :
    ConvexPos ![r0, r1, r2, r3, x] := by
  have hd1 := skip1_pos r0 r1 r2 r3 x hc1 hc2 hc3 he0 he3
  have hd2 := skip2_pos r0 r1 r2 r3 x hc2 hc3 hc4 he2 he3
  have h03x : 0 < sig r0 r3 x := by
    rw [show sig r0 r3 x = -sig r3 r0 x from by simp only [sig]; ring]
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]
  exacts [hc1.le, hc2.le, he0.le, hc3.le, hd1.le, h03x.le, hc4.le, he1.le,
    hd2.le, he2.le]

/-- Sixteen-way edge-sign analysis: given a strictly convex CCW quad, a
fifth point with nonzero edge signs that is in no diagonal triangle and
absorbs no vertex, one of the four cyclic insertions is a convex pentagon. -/
theorem insert_or_absorb (q0 q1 q2 q3 x : ℝ × ℝ)
    (hc1 : 0 < sig q0 q1 q2) (hc2 : 0 < sig q0 q1 q3)
    (hc3 : 0 < sig q0 q2 q3) (hc4 : 0 < sig q1 q2 q3)
    (hne0 : sig q0 q1 x ≠ 0) (hne1 : sig q1 q2 x ≠ 0)
    (hne2 : sig q2 q3 x ≠ 0) (hne3 : sig q3 q0 x ≠ 0)
    (hni1 : ¬ InTri x q0 q1 q2) (hni2 : ¬ InTri x q0 q2 q3)
    (hnv0 : ¬ InTri q1 q0 q2 x) (hnv1 : ¬ InTri q2 q1 q3 x)
    (hnv2 : ¬ InTri q3 q2 q0 x) (hnv3 : ¬ InTri q0 q3 q1 x) :
    ConvexPos ![q0, q1, q2, q3, x] ∨ ConvexPos ![q1, q2, q3, q0, x]
      ∨ ConvexPos ![q2, q3, q0, q1, x] ∨ ConvexPos ![q3, q0, q1, q2, x] := by
  -- rotated quad positivity facts
  have rc1 : 0 < sig q1 q2 q0 := by
    rw [show sig q1 q2 q0 = sig q0 q1 q2 from by simp only [sig]; ring]; exact hc1
  have rc2 : 0 < sig q1 q3 q0 := by
    rw [show sig q1 q3 q0 = sig q0 q1 q3 from by simp only [sig]; ring]; exact hc2
  have rc3 : 0 < sig q2 q3 q0 := by
    rw [show sig q2 q3 q0 = sig q0 q2 q3 from by simp only [sig]; ring]; exact hc3
  have rc4 : 0 < sig q2 q0 q1 := by
    rw [show sig q2 q0 q1 = sig q0 q1 q2 from by simp only [sig]; ring]; exact hc1
  have rc5 : 0 < sig q3 q0 q1 := by
    rw [show sig q3 q0 q1 = sig q0 q1 q3 from by simp only [sig]; ring]; exact hc2
  have rc6 : 0 < sig q3 q1 q2 := by
    rw [show sig q3 q1 q2 = sig q1 q2 q3 from by simp only [sig]; ring]; exact hc4
  have rc7 : 0 < sig q3 q0 q2 := by
    rw [show sig q3 q0 q2 = sig q0 q2 q3 from by simp only [sig]; ring]; exact hc3
  have rc8 : 0 < sig q2 q3 q1 := by
    rw [show sig q2 q3 q1 = sig q1 q2 q3 from by simp only [sig]; ring]; exact hc4
  rcases lt_or_gt_of_ne hne0 with e0 | e0 <;>
    rcases lt_or_gt_of_ne hne1 with e1 | e1 <;>
      rcases lt_or_gt_of_ne hne2 with e2 | e2 <;>
        rcases lt_or_gt_of_ne hne3 with e3 | e3
  -- (-,-,-,-): adjacent pair (e0, e1)
  · exact absurd (vertex_in_adj q0 q1 q2 x hc1 e0 e1) hnv0
  -- (-,-,-,+): adjacent (e0, e1)
  · exact absurd (vertex_in_adj q0 q1 q2 x hc1 e0 e1) hnv0
  -- (-,-,+,-): adjacent (e0, e1)
  · exact absurd (vertex_in_adj q0 q1 q2 x hc1 e0 e1) hnv0
  -- (-,-,+,+): adjacent (e0, e1)
  · exact absurd (vertex_in_adj q0 q1 q2 x hc1 e0 e1) hnv0
  -- (-,+,-,-): adjacent (e2, e3)
  · exact absurd (vertex_in_adj q2 q3 q0 x rc3 e2 e3) hnv2
  -- (-,+,-,+): opposite (e0, e2)
  · exact absurd (opposite_false q0 q1 q2 q3 x hc1 hc2 hc3 hc4 e0 e1 e2 e3) id
  -- (-,+,+,-): adjacent (e3, e0)
  · exact absurd (vertex_in_adj q3 q0 q1 x rc5 e3 e0) hnv3
  -- (-,+,+,+): single negative at e0, tuple (q1,q2,q3,q0,x)
  · exact Or.inr (Or.inl (insertion q1 q2 q3 q0 x hc4 rc1 rc2 rc3 e1 e2 e3 e0))
  -- (+,-,-,-): adjacent (e1, e2)
  · exact absurd (vertex_in_adj q1 q2 q3 x hc4 e1 e2) hnv1
  -- (+,-,-,+): adjacent (e1, e2)
  · exact absurd (vertex_in_adj q1 q2 q3 x hc4 e1 e2) hnv1
  -- (+,-,+,-): opposite (e1, e3), rotated
  · exact absurd (opposite_false q1 q2 q3 q0 x hc4 rc1 rc2 rc3 e1 e2 e3 e0) id
  -- (+,-,+,+): single negative at e1, tuple (q2,q3,q0,q1,x)
  · exact Or.inr (Or.inr (Or.inl
      (insertion q2 q3 q0 q1 x rc3 rc8 rc4 rc5 e2 e3 e0 e1)))
  -- (+,+,-,-): adjacent (e2, e3)
  · exact absurd (vertex_in_adj q2 q3 q0 x rc3 e2 e3) hnv2
  -- (+,+,-,+): single negative at e2, tuple (q3,q0,q1,q2,x)
  · exact Or.inr (Or.inr (Or.inr
      (insertion q3 q0 q1 q2 x rc5 rc7 rc6 hc1 e3 e0 e1 e2)))
  -- (+,+,+,-): single negative at e3, tuple (q0,q1,q2,q3,x)
  · exact Or.inl (insertion q0 q1 q2 q3 x hc1 hc2 hc3 hc4 e0 e1 e2 e3)
  -- (+,+,+,+): x inside the quad
  · rcases in_quad_of_edges q0 q1 q2 q3 x hc1 hc3 e0.le e1.le e2.le e3.le with
      h | h
    · exact absurd h hni1
    · exact absurd h hni2

end Heilbronn5
