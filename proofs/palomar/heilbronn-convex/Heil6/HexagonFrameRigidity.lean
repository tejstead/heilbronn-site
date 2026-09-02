import Mathlib

set_option linter.style.header false

/-!
# Affine-frame rigidity for the hull-six equality table

`HexagonScalar.cycle_rigidity` returns the determinant values occurring at
equality.  Only seven of them are needed to reconstruct the last three
vertices from the first three.  This file records that reconstruction without
depending on either of the currently incompatible n=6 APIs.
-/

namespace N6Scratch
namespace HexagonFrameRigidity

/-- The doubled signed area used by both n=6 developments. -/
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

/-- Affine coordinates `alpha,beta` relative to the frame `A,B,C`. -/
def framePoint (A B C : ℝ × ℝ) (alpha beta : ℝ) : ℝ × ℝ :=
  ((1 - alpha - beta) * A.1 + alpha * B.1 + beta * C.1,
   (1 - alpha - beta) * A.2 + alpha * B.2 + beta * C.2)

theorem sig_four_point (p q r s : ℝ × ℝ) :
    sig p q s + sig q r s = sig p q r + sig p r s := by
  simp only [sig]
  ring

/-- Two signed areas against a nondegenerate affine frame determine a point. -/
theorem eq_framePoint_of_sigs
    (A B C X : ℝ × ℝ) (m alpha beta : ℝ)
    (hm : m ≠ 0)
    (hABC : sig A B C = m)
    (hABX : sig A B X = beta * m)
    (hACX : sig A C X = -alpha * m) :
    X = framePoint A B C alpha beta := by
  have hxIdentity :
      sig A B C * (X.1 - A.1) =
        -(B.1 - A.1) * sig A C X + (C.1 - A.1) * sig A B X := by
    simp only [sig]
    ring
  have hyIdentity :
      sig A B C * (X.2 - A.2) =
        -(B.2 - A.2) * sig A C X + (C.2 - A.2) * sig A B X := by
    simp only [sig]
    ring
  rw [hABC, hABX, hACX] at hxIdentity hyIdentity
  have hxZero :
      m * (X.1 - ((1 - alpha - beta) * A.1 + alpha * B.1 + beta * C.1)) = 0 := by
    nlinarith [hxIdentity]
  have hyZero :
      m * (X.2 - ((1 - alpha - beta) * A.2 + alpha * B.2 + beta * C.2)) = 0 := by
    nlinarith [hyIdentity]
  have hx : X.1 = (framePoint A B C alpha beta).1 := by
    rcases mul_eq_zero.mp hxZero with hzero | hzero
    · exact False.elim (hm hzero)
    · simpa only [framePoint] using sub_eq_zero.mp hzero
  have hy : X.2 = (framePoint A B C alpha beta).2 := by
    rcases mul_eq_zero.mp hyZero with hzero | hzero
    · exact False.elim (hm hzero)
    · simpa only [framePoint] using sub_eq_zero.mp hzero
  exact Prod.ext hx hy

/-- A cyclic hexagon written in affine coordinates of its first three points.
These are precisely the coordinates of an affine image of the regular
hexagon in the orientation used by the existing `Heilbronn6.regHex`. -/
def IsAffineRegularFrame
    (v0 v1 v2 v3 v4 v5 : ℝ × ℝ) : Prop :=
  v3 = framePoint v0 v1 v2 (-2) 2 ∧
  v4 = framePoint v0 v1 v2 (-3) 2 ∧
  v5 = framePoint v0 v1 v2 (-2) 1

/-- The equality determinant table reconstructs the affine-regular hexagon.

The `013` value needed for `v3` follows from the four-point cocycle; the
other coordinates are read directly from the two frame determinants. -/
theorem determinant_table_rigid
    (v0 v1 v2 v3 v4 v5 : ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (h012 : sig v0 v1 v2 = m)
    (h023 : sig v0 v2 v3 = 2 * m)
    (h123 : sig v1 v2 v3 = m)
    (h014 : sig v0 v1 v4 = 2 * m)
    (h024 : sig v0 v2 v4 = 3 * m)
    (h015 : sig v0 v1 v5 = m)
    (h025 : sig v0 v2 v5 = 2 * m) :
    IsAffineRegularFrame v0 v1 v2 v3 v4 v5 := by
  have h013 : sig v0 v1 v3 = 2 * m := by
    have h := sig_four_point v0 v1 v2 v3
    nlinarith
  have hmne : m ≠ 0 := ne_of_gt hm
  have hv3 : v3 = framePoint v0 v1 v2 (-2) 2 := by
    apply eq_framePoint_of_sigs v0 v1 v2 v3 m (-2) 2 hmne h012
    · simpa using h013
    · simpa using h023
  have hv4 : v4 = framePoint v0 v1 v2 (-3) 2 := by
    apply eq_framePoint_of_sigs v0 v1 v2 v4 m (-3) 2 hmne h012
    · simpa using h014
    · simpa using h024
  have hv5 : v5 = framePoint v0 v1 v2 (-2) 1 := by
    apply eq_framePoint_of_sigs v0 v1 v2 v5 m (-2) 1 hmne h012
    · simpa using h015
    · simpa using h025
  exact ⟨hv3, hv4, hv5⟩

end HexagonFrameRigidity
end N6Scratch
