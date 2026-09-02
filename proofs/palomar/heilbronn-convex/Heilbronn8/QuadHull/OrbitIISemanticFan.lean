import Heilbronn8.QuadHull.OrbitIISemanticPrimitive

/-!
# The QAB/QDA semantic fan lemma for coarse Orbit II
-/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-!
For `X ∈ ABD`, two fan-side determinants have fixed positive signs.  The
nonzero determinant `sig Q A X` therefore selects exactly one of `QAB` and
`QDA`.
-/
lemma in_QAB_or_QDA
    {Q A B D X : Point}
    (hα : 0 < sig Q A B) (hδ : 0 < sig Q D A)
    (hv : 0 < sig Q D B)
    (hABD : 0 < sig A B D)
    (hX : TriHull.InTriStrict X A B D)
    (hne : sig Q A X ≠ 0) :
    TriHull.InTriStrict X Q A B ∨
      TriHull.InTriStrict X Q D A := by
  obtain ⟨_, hXDA, hXAB⟩ := TriHull.inTriStrict_fan_pos hABD hX
  obtain ⟨x, y, z, hx, hy, hz, hsum, hXeq⟩ := hX
  have hABQ : 0 < sig A B Q := by
    calc
      0 < sig Q A B := hα
      _ = sig A B Q := sig_rotate _ _ _
  have hDBQ : 0 < sig D B Q := by
    calc
      0 < sig Q D B := hv
      _ = sig D B Q := sig_rotate _ _ _
  have hAQD : 0 < sig A Q D := by
    calc
      0 < sig Q D A := hδ
      _ = sig D A Q := sig_rotate _ _ _
      _ = sig A Q D := sig_rotate _ _ _
  have hBQD : 0 < sig B Q D := by
    calc
      0 < sig Q D B := hv
      _ = sig D B Q := sig_rotate _ _ _
      _ = sig B Q D := sig_rotate _ _ _
  have hXBQ : 0 < sig X B Q := by
    have hidentity :
        sig X B Q = x * sig A B Q + z * sig D B Q := by
      rw [hXeq,
        sig_affine_fst A B D B Q x y z hsum]
      simp only [sig_eq12, mul_zero]
      ring
    rw [hidentity]
    exact add_pos (mul_pos hx hABQ) (mul_pos hz hDBQ)
  have hBQX : 0 < sig B Q X := by
    calc
      0 < sig X B Q := hXBQ
      _ = sig B Q X := sig_rotate _ _ _
  have hXQD : 0 < sig X Q D := by
    have hidentity :
        sig X Q D = x * sig A Q D + y * sig B Q D := by
      rw [hXeq,
        sig_affine_fst A B D Q D x y z hsum]
      simp only [sig_eq13, mul_zero]
      ring
    rw [hidentity]
    exact add_pos (mul_pos hx hAQD) (mul_pos hy hBQD)
  have hQDX : 0 < sig Q D X := by
    calc
      0 < sig X Q D := hXQD
      _ = sig Q D X := sig_rotate _ _ _
  by_cases hQAX : 0 < sig Q A X
  · left
    apply inTriStrict_of_fan_pos hα hXAB
    · calc
        0 < sig B Q X := hBQX
        _ = sig Q X B := sig_rotate _ _ _
    · exact hQAX
  · right
    have hQAXneg : sig Q A X < 0 :=
      lt_of_le_of_ne (le_of_not_gt hQAX) hne
    apply inTriStrict_of_fan_pos hδ hXDA
    · calc
        0 < -sig Q A X := neg_pos.mpr hQAXneg
        _ = sig Q X A := (sig_swap _ _ _).symm
    · exact hQDX

end OrbitIIInternal
end Heilbronn8.QuadHull
