/-
Polynomial identities of doubled signed areas, and the ear-domination
(unimodality) lemma they imply. Everything here is `ring` plus `nlinarith`.
-/
import Heil5.Defs

namespace Heilbronn5

/-- Grassmann-Pluecker three-term relation with pivot `a`. -/
lemma gp (a b c d e : ℝ × ℝ) :
    sig a b c * sig a d e - sig a b d * sig a c e + sig a b e * sig a c d = 0 := by
  simp only [sig]; ring

/-- Cocycle identity for four points. -/
lemma cocycle (a b c d : ℝ × ℝ) :
    sig a b c - sig a b d + sig a c d - sig b c d = 0 := by
  simp only [sig]; ring

/-- Fan split of a triangle by an arbitrary point. -/
lemma split3 (p a b c : ℝ × ℝ) :
    sig p a b + sig p b c + sig p c a = sig a b c := by
  simp only [sig]; ring

/-- Fan split of a quadrilateral by an arbitrary point. -/
lemma split4 (p a b c d : ℝ × ℝ) :
    sig p a b + sig p b c + sig p c d + sig p d a = sig a b c + sig a c d := by
  simp only [sig]; ring

/-- Ear domination: under the seven positivity hypotheses below (which hold
in particular for five points in strictly convex CCW position), the triangle
on side `ab` with the middle apex `d` is at least as large as the smaller of
the two ear triangles on that side (apexes `c` and `e`). -/
lemma mid_ge (a b c d e : ℝ × ℝ)
    (habc : 0 < sig a b c) (habd : 0 < sig a b d) (habe : 0 < sig a b e)
    (hacd : 0 < sig a c d) (hace : 0 < sig a c e) (hade : 0 < sig a d e)
    (hcde : 0 < sig c d e) :
    min (sig a b c) (sig a b e) ≤ sig a b d := by
  by_contra hlt
  push_neg at hlt
  have h1 : sig a b d < sig a b c := lt_of_lt_of_le hlt (min_le_left _ _)
  have h2 : sig a b d < sig a b e := lt_of_lt_of_le hlt (min_le_right _ _)
  have hgp := gp a b c d e
  have hcc := cocycle a c d e
  nlinarith [mul_pos habd hcde,
    mul_lt_mul_of_pos_right h1 hade,
    mul_lt_mul_of_pos_right h2 hacd]

end Heilbronn5
