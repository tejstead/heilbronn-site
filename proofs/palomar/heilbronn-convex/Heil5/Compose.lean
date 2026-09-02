/-
Convex-combination composition lemmas used by the hull trichotomy:
vertices lie in their own triangle, and membership is absorbed through
triangles whose vertices all lie in a common triangle.
-/
import Heil5.Defs

namespace Heilbronn5

lemma inTri_vertexA (A B C : ℝ × ℝ) : InTri A A B C :=
  ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩

lemma inTri_vertexB (A B C : ℝ × ℝ) : InTri B A B C :=
  ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩

lemma inTri_vertexC (A B C : ℝ × ℝ) : InTri C A B C :=
  ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩

/-- Hull absorption: if `x` lies in triangle `PQR` and each of `P`, `Q`, `R`
lies in triangle `ABC`, then `x` lies in triangle `ABC`. -/
lemma inTri_absorb {x P Q R A B C : ℝ × ℝ}
    (hx : InTri x P Q R) (hP : InTri P A B C) (hQ : InTri Q A B C)
    (hR : InTri R A B C) : InTri x A B C := by
  obtain ⟨p, q, r, hp, hq, hr, hpqr, hxe⟩ := hx
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, h1, hPe⟩ := hP
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, h2, hQe⟩ := hQ
  obtain ⟨a3, b3, c3, ha3, hb3, hc3, h3, hRe⟩ := hR
  refine ⟨p * a1 + q * a2 + r * a3, p * b1 + q * b2 + r * b3,
    p * c1 + q * c2 + r * c3,
    add_nonneg (add_nonneg (mul_nonneg hp ha1) (mul_nonneg hq ha2))
      (mul_nonneg hr ha3),
    add_nonneg (add_nonneg (mul_nonneg hp hb1) (mul_nonneg hq hb2))
      (mul_nonneg hr hb3),
    add_nonneg (add_nonneg (mul_nonneg hp hc1) (mul_nonneg hq hc2))
      (mul_nonneg hr hc3),
    by linear_combination p * h1 + q * h2 + r * h3 + hpqr, ?_⟩
  subst hxe hPe hQe hRe
  module

end Heilbronn5
