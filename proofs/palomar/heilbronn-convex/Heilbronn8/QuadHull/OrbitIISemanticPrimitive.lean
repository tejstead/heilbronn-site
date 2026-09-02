import Heilbronn8.QuadHull.OrbitIICommon

/-!
# Primitive semantic lemmas for coarse Orbit II
-/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-- Converse to `inTriStrict_fan_pos`, kept local to this producer. -/
lemma inTriStrict_of_fan_pos {p a b c : Point}
    (hD : 0 < sig a b c)
    (h1 : 0 < sig p b c) (h2 : 0 < sig a p c)
    (h3 : 0 < sig a b p) :
    TriHull.InTriStrict p a b c := by
  have hDne : sig a b c ≠ 0 := ne_of_gt hD
  have hsum :
      sig p b c + sig a p c + sig a b p = sig a b c := by
    simp only [sig]
    ring
  refine ⟨sig p b c / sig a b c,
    sig a p c / sig a b c,
    sig a b p / sig a b c,
    div_pos h1 hD, div_pos h2 hD, div_pos h3 hD, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hDne]
  · have hx1 :
        p.1 * sig a b c =
          sig p b c * a.1 + sig a p c * b.1 + sig a b p * c.1 := by
      simp only [sig]
      ring
    have hx2 :
        p.2 * sig a b c =
          sig p b c * a.2 + sig a p c * b.2 + sig a b p * c.2 := by
      simp only [sig]
      ring
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith

/-- A nonzero minimum triangle area makes every pairwise-distinct labelled
triangle nondegenerate. -/
lemma sig_ne_zero_of_minTri_ne_zero
    {v : Fin 8 → Point} {i j k : Fin 8}
    (hm : minTri v ≠ 0)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  apply hm
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [hzero, abs_zero] at hmin
  exact le_antisymm hmin (minTri_nonneg v)

end OrbitIIInternal
end Heilbronn8.QuadHull
