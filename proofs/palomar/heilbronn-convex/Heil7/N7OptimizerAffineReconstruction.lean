import Solution.N7Family

/-!
# Affine reconstruction of the seven-point optimizer normal form

This module is the final, coordinate-only seam in the equality-case
classification.  It consumes the public arbitrary-determinant
`NonsingularAffine` and `AffineEquivalent` API while leaving the existing
`PosAffine` and `GaugeEquivalent` API unchanged.

The input packet is the exact normal form produced by the hull-six equality
analysis.  If `m > 0` and `3/2 <= lambda <= 2`, its six hull rays and its
interior point are

```
(1,0), (0,m), (-2,lambda*m), (-3/lambda,m),
(1,-lambda*m), (3/lambda,-2*m), (0,0).
```

The positive-determinant map below sends this packet, label for label, to
`cfg7Family (2/lambda)`.  The second result records the orientation-reversing
involution `t |-> 4/(3*t)` on the full parameter interval `[1,4/3]`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge

namespace N7Upper

/-- `cfg7Family` is the implementation of the public real-parameter family. -/
lemma cfg7Family_eq_sevenFamilyAt (t : ℝ) :
    cfg7Family t = sevenFamilyAt t := rfl

/-- Exact coordinate packet supplied by the sharp hull-six equality case.
The labelling begins at a small boundary sector and follows the CCW hull;
label six is the unique interior point. -/
structure Hull6TightNormalForm
    (v : Fin 7 → ℝ × ℝ) (m lambda : ℝ) : Prop where
  m_pos : 0 < m
  lambda_lower : (3 : ℝ) / 2 ≤ lambda
  lambda_upper : lambda ≤ 2
  p0 : v 0 = ((1 : ℝ), 0)
  p1 : v 1 = (0, m)
  p2 : v 2 = (-2, lambda * m)
  p3 : v 3 = (-3 / lambda, m)
  p4 : v 4 = (1, -lambda * m)
  p5 : v 5 = (3 / lambda, -2 * m)
  p6 : v 6 = (0, 0)

/-- The family parameter associated to the tight normal-form parameter. -/
noncomputable def hull6TightFamilyParameter (lambda : ℝ) : ℝ := 2 / lambda

lemma Hull6TightNormalForm.parameter_mem
    {v : Fin 7 → ℝ × ℝ} {m lambda : ℝ}
    (h : Hull6TightNormalForm v m lambda) :
    1 ≤ hull6TightFamilyParameter lambda ∧
      hull6TightFamilyParameter lambda ≤ 4 / 3 := by
  have hlambda : 0 < lambda :=
    lt_of_lt_of_le (by norm_num) h.lambda_lower
  unfold hull6TightFamilyParameter
  constructor
  · exact (le_div_iff₀ hlambda).2 (by linarith only [h.lambda_upper])
  · exact (div_le_iff₀ hlambda).2 (by
      nlinarith only [h.lambda_lower])

/-- The explicit positive-determinant linear map from a normal form at floor
`m` to the unit-area family at parameter `t`.

Its standard-basis columns are
`(-2/(3t),-2/3)` and `(-1/(3m),-2t/(3m))`; at the unit-area floor
`m=2/9`, the second column is `(-3/2,-3t)`. -/
noncomputable def hull6TightNormalToFamilyAffine
    (m t : ℝ) (hm : 0 < m) (ht : 0 < t) : PosAffine where
  a := -2 / (3 * t)
  b := -1 / (3 * m)
  c := -2 / 3
  d := -(2 * t) / (3 * m)
  tx := 0
  ty := 0
  det_pos := by
    have hdet :
        (-2 / (3 * t)) * (-(2 * t) / (3 * m)) -
            (-1 / (3 * m)) * (-2 / 3) = 2 / (9 * m) := by
      field_simp [hm.ne', ht.ne']
      <;> ring
    rw [hdet]
    positivity

/-- A tight normal-form packet is already in the positive-determinant gauge
orbit of the full optimizer family.  In particular no extra Boolean mirror
parameter is needed for membership in the family indexed by `[1,4/3]`. -/
theorem Hull6TightNormalForm.gaugeEquivalent_cfg7Family
    {v : Fin 7 → ℝ × ℝ} {m lambda : ℝ}
    (h : Hull6TightNormalForm v m lambda) :
    GaugeEquivalent v (cfg7Family (hull6TightFamilyParameter lambda)) := by
  have hlambda : 0 < lambda :=
    lt_of_lt_of_le (by norm_num) h.lambda_lower
  let t : ℝ := hull6TightFamilyParameter lambda
  have ht : 0 < t := by
    dsimp [t, hull6TightFamilyParameter]
    positivity
  let T : PosAffine := hull6TightNormalToFamilyAffine m t h.m_pos ht
  refine ⟨Equiv.refl _, T, ?_⟩
  funext i
  fin_cases i <;>
    simp [T, hull6TightNormalToFamilyAffine, t,
      hull6TightFamilyParameter, h.p0, h.p1, h.p2, h.p3,
      h.p4, h.p5, h.p6, PosAffine.map] <;>
    field_simp [h.m_pos.ne', hlambda.ne']
  all_goals try ring_nf
  all_goals simp

/-- Arbitrary-determinant version of the coordinate reconstruction. -/
theorem Hull6TightNormalForm.affineEquivalent_cfg7Family
    {v : Fin 7 → ℝ × ℝ} {m lambda : ℝ}
    (h : Hull6TightNormalForm v m lambda) :
    AffineEquivalent v (cfg7Family (hull6TightFamilyParameter lambda)) :=
  affineEquivalent_of_gaugeEquivalent h.gaugeEquivalent_cfg7Family

/-- Final orientation used by the optimizer-classification theorem: a member
of the public family is mapped to the arbitrary optimizer normal form. -/
theorem Hull6TightNormalForm.sevenFamilyAt_affineEquivalent
    {v : Fin 7 → ℝ × ℝ} {m lambda : ℝ}
    (h : Hull6TightNormalForm v m lambda) :
    AffineEquivalent (sevenFamilyAt (hull6TightFamilyParameter lambda)) v := by
  rw [← cfg7Family_eq_sevenFamilyAt]
  exact affineEquivalent_symm h.affineEquivalent_cfg7Family

/-- Packaged E4 conclusion in the exact existential shape required by the
optimizer-classification theorem. -/
theorem Hull6TightNormalForm.exists_family_affineEquivalent
    {v : Fin 7 → ℝ × ℝ} {m lambda : ℝ}
    (h : Hull6TightNormalForm v m lambda) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 4 / 3 ∧ AffineEquivalent (sevenFamilyAt t) v := by
  refine ⟨hull6TightFamilyParameter lambda, h.parameter_mem.1,
    h.parameter_mem.2, ?_⟩
  exact h.sevenFamilyAt_affineEquivalent

/-! ## The mirror involution on the family -/

noncomputable def hull6TightMirrorParameter (t : ℝ) : ℝ := 4 / (3 * t)

lemma hull6TightMirrorParameter_mem {t : ℝ}
    (ht : 1 ≤ t ∧ t ≤ (4 : ℝ) / 3) :
    1 ≤ hull6TightMirrorParameter t ∧
      hull6TightMirrorParameter t ≤ 4 / 3 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hden : 0 < 3 * t := mul_pos (by norm_num) htpos
  unfold hull6TightMirrorParameter
  constructor
  · exact (le_div_iff₀ hden).2 (by nlinarith only [ht.2])
  · exact (div_le_iff₀ hden).2 (by nlinarith only [ht.1])

lemma hull6TightMirrorParameter_involutive {t : ℝ} (ht : t ≠ 0) :
    hull6TightMirrorParameter (hull6TightMirrorParameter t) = t := by
  unfold hull6TightMirrorParameter
  field_simp [ht]
  <;> ring

/-- The hull-order reversal used by the explicit reflection. -/
def cfg7FamilyMirrorPerm : Equiv.Perm (Fin 7) where
  toFun := ![1, 0, 5, 4, 3, 2, 6]
  invFun := ![1, 0, 5, 4, 3, 2, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- A determinant-minus-one map realizing the parameter involution. -/
noncomputable def cfg7FamilyMirrorAffine
    (t : ℝ) (ht : t ≠ 0) : NonsingularAffine where
  a := -t / 2
  b := 1
  c := 2 / 3
  d := 2 / (3 * t)
  tx := 0
  ty := 0
  det_ne := by
    have hdet :
        (-t / 2) * (2 / (3 * t)) - 1 * (2 / 3) = (-1 : ℝ) := by
      field_simp [ht]
      <;> ring
    rw [hdet]
    norm_num

lemma cfg7FamilyMirrorAffine_det (t : ℝ) (ht : t ≠ 0) :
    (cfg7FamilyMirrorAffine t ht).det = -1 := by
  simp only [cfg7FamilyMirrorAffine, NonsingularAffine.det]
  field_simp [ht]
  <;> ring

/-- Reflection identifies the two parameters `t` and `4/(3t)` once arbitrary
nonsingular affine maps are admitted.  The map has determinant `-1`; hence
this theorem intentionally uses `AffineEquivalent`, not `GaugeEquivalent`. -/
theorem cfg7Family_affineEquivalent_mirrorParameter
    (t : ℝ) (ht : 0 < t) :
    AffineEquivalent (cfg7Family t)
      (cfg7Family (hull6TightMirrorParameter t)) := by
  let T : NonsingularAffine := cfg7FamilyMirrorAffine t ht.ne'
  refine ⟨cfg7FamilyMirrorPerm, T, ?_⟩
  funext i
  fin_cases i <;>
    simp [cfg7FamilyMirrorPerm, T, cfg7FamilyMirrorAffine,
      hull6TightMirrorParameter, NonsingularAffine.map] <;>
    field_simp [ht.ne'] <;>
    ring_nf <;> simp

/-- Public-family form of the same orientation-reversing equivalence. -/
theorem sevenFamilyAt_affineEquivalent_mirrorParameter
    (t : ℝ) (ht : 0 < t) :
    AffineEquivalent (sevenFamilyAt t)
      (sevenFamilyAt (hull6TightMirrorParameter t)) := by
  simpa only [cfg7Family_eq_sevenFamilyAt] using
    cfg7Family_affineEquivalent_mirrorParameter t ht

end N7Upper

end HeilbronnChallenge
