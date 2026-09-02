import Solution.N7Family
import Heil7.RationalOptimizerFamily

/-!
# Arbitrary-affine classification of the seven-point family

This source targets the revised public definitions
`HeilbronnChallenge.NonsingularAffine` and
`HeilbronnChallenge.AffineEquivalent`.  Those definitions currently live in
`work/unified/HeilbronnChallenge.lean`; their identical proof-side copies and
common algebra live in `Solution.AffineDefs`, imported transitively by
`Solution.N7Family`.  They are intentionally not duplicated here.

For parameters in `[1,4/3]`, two family members are affinely equivalent if
and only if their parameters are equal or have product `4/3`.  The second
case is realized by an explicit determinant-minus-one reflection.  The
converse follows from a symmetric sum of squared triangle determinants.
-/

set_option linter.style.header false

namespace HeilbronnChallenge

/-! ## Public-family coordinate bridge -/

lemma sevenFamilyAt_eq_cfg7Family (t : Real) :
    sevenFamilyAt t = cfg7Family t := rfl

/-- The parameter involution induced by reflection. -/
noncomputable def sevenFamilyMirrorParameter (t : Real) : Real := 4 / (3 * t)

lemma sevenFamilyMirrorParameter_mem {t : Real}
    (ht : 1 <= t ∧ t <= (4 : Real) / 3) :
    1 <= sevenFamilyMirrorParameter t ∧
      sevenFamilyMirrorParameter t <= 4 / 3 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hden : 0 < 3 * t := mul_pos (by norm_num) htpos
  unfold sevenFamilyMirrorParameter
  constructor
  · exact (le_div_iff₀ hden).2 (by nlinarith only [ht.2])
  · exact (div_le_iff₀ hden).2 (by nlinarith only [ht.1])

lemma sevenFamilyMirrorParameter_involutive {t : Real} (ht : t ≠ 0) :
    sevenFamilyMirrorParameter (sevenFamilyMirrorParameter t) = t := by
  unfold sevenFamilyMirrorParameter
  field_simp [ht]

/-- Reversal of the six hull vertices, fixing the interior point. -/
def sevenFamilyMirrorPerm : Equiv.Perm (Fin 7) where
  toFun := ![1, 0, 5, 4, 3, 2, 6]
  invFun := ![1, 0, 5, 4, 3, 2, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The determinant-minus-one affine map realizing the parameter
involution. -/
noncomputable def sevenFamilyMirrorAffine
    (t : Real) (ht : t ≠ 0) : NonsingularAffine where
  a := -t / 2
  b := 1
  c := 2 / 3
  d := 2 / (3 * t)
  tx := 0
  ty := 0
  det_ne := by
    have hdet :
        (-t / 2) * (2 / (3 * t)) - 1 * (2 / 3) = (-1 : Real) := by
      field_simp [ht]
      ring
    rw [hdet]
    norm_num

lemma sevenFamilyMirrorAffine_det
    (t : Real) (ht : t ≠ 0) :
    (sevenFamilyMirrorAffine t ht).a * (sevenFamilyMirrorAffine t ht).d -
        (sevenFamilyMirrorAffine t ht).b *
          (sevenFamilyMirrorAffine t ht).c = -1 := by
  simp only [sevenFamilyMirrorAffine]
  field_simp [ht]
  ring

/-- Reflection identifies `t` with `4/(3*t)` under arbitrary nonsingular
affine equivalence. -/
theorem sevenFamilyAt_affineEquivalent_mirror
    (t : Real) (ht : 0 < t) :
    AffineEquivalent (sevenFamilyAt t)
      (sevenFamilyAt (sevenFamilyMirrorParameter t)) := by
  let T : NonsingularAffine := sevenFamilyMirrorAffine t ht.ne'
  refine ⟨sevenFamilyMirrorPerm, T, ?_⟩
  funext i
  fin_cases i <;>
    simp [sevenFamilyAt, sevenFamilyMirrorPerm, T,
      sevenFamilyMirrorAffine, sevenFamilyMirrorParameter,
      NonsingularAffine.map] <;>
    field_simp [ht.ne'] <;>
    ring_nf <;>
    simp

/-! ## Symmetric determinant invariant -/

/-- Sum of squared signed determinants over all ordered triples. -/
def sevenFamilyTriangleSquareSum (v : Fin 7 -> Real × Real) : Real :=
  ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
    sig (v i) (v j) (v k) ^ 2

lemma sevenFamilyTriangleSquareSum_relabel
    (v : Fin 7 -> Real × Real) (sigma : Equiv.Perm (Fin 7)) :
    sevenFamilyTriangleSquareSum (v ∘ sigma) =
      sevenFamilyTriangleSquareSum v := by
  simp only [sevenFamilyTriangleSquareSum, Function.comp_apply]
  calc
    (∑ i, ∑ j, ∑ k,
        sig (v (sigma i)) (v (sigma j)) (v (sigma k)) ^ 2) =
        ∑ i, ∑ j, ∑ k,
          sig (v (sigma i)) (v (sigma j)) (v k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simpa only using
        (Equiv.sum_comp sigma
          (fun k : Fin 7 =>
            sig (v (sigma i)) (v (sigma j)) (v k) ^ 2))
    _ = ∑ i, ∑ j, ∑ k,
          sig (v (sigma i)) (v j) (v k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only using
        (Equiv.sum_comp sigma
          (fun j : Fin 7 =>
            ∑ k : Fin 7, sig (v (sigma i)) (v j) (v k) ^ 2))
    _ = ∑ i, ∑ j, ∑ k,
          sig (v i) (v j) (v k) ^ 2 := by
      simpa only using
        (Equiv.sum_comp sigma
          (fun i : Fin 7 =>
            ∑ j : Fin 7, ∑ k : Fin 7, sig (v i) (v j) (v k) ^ 2))

lemma sevenFamilyTriangleSquareSum_nonsingularAffine
    (T : NonsingularAffine) (v : Fin 7 -> Real × Real) :
    sevenFamilyTriangleSquareSum (fun i => T.map (v i)) =
      T.det ^ 2 * sevenFamilyTriangleSquareSum v := by
  simp only [sevenFamilyTriangleSquareSum]
  simp_rw [sig_nonsingularAffine T, mul_pow]
  simp only [← Finset.mul_sum]

/-- Closed form of the symmetric determinant invariant. -/
theorem sevenFamilyTriangleSquareSum_value (t : Real) (ht : t ≠ 0) :
    sevenFamilyTriangleSquareSum (sevenFamilyAt t) =
      14 * (3 * t ^ 2 + 4) ^ 2 / (9 * t ^ 2) := by
  change N7Upper.orderedTriangleSquareSum (sevenFamilyAt t) = _
  rw [N7Upper.orderedTriangleSquareSum_eq_moments]
  have hx : (∑ i : Fin 7, (sevenFamilyAt t i).1) = 0 := by
    rw [sevenFamilyAt_eq_cfg7Family]
    simp [Fin.sum_univ_succ, cfg7Family]
    field_simp [ht] <;> ring
  have hy : (∑ i : Fin 7, (sevenFamilyAt t i).2) = 0 := by
    rw [sevenFamilyAt_eq_cfg7Family]
    simp [Fin.sum_univ_succ, cfg7Family]
    field_simp [ht] <;> ring
  have hxx : (∑ i : Fin 7, (sevenFamilyAt t i).1 ^ 2) =
      2 * (3 * t ^ 2 + 4) / (9 * t ^ 2) := by
    rw [sevenFamilyAt_eq_cfg7Family]
    simp [Fin.sum_univ_succ, cfg7Family]
    field_simp [ht] <;> ring
  have hyy : (∑ i : Fin 7, (sevenFamilyAt t i).2 ^ 2) =
      2 * (3 * t ^ 2 + 4) / 9 := by
    rw [sevenFamilyAt_eq_cfg7Family]
    simp [Fin.sum_univ_succ, cfg7Family]
    ring
  have hxy : (∑ i : Fin 7,
      (sevenFamilyAt t i).1 * (sevenFamilyAt t i).2) =
      (3 * t ^ 2 + 4) / (9 * t) := by
    rw [sevenFamilyAt_eq_cfg7Family]
    simp [Fin.sum_univ_succ, cfg7Family]
    field_simp [ht] <;> ring
  rw [hx, hy, hxx, hyy, hxy]
  field_simp [ht] <;> ring

lemma sevenFamilyTriangleSquareSum_formula_sub (s t : Real)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    14 * (3 * s ^ 2 + 4) ^ 2 / (9 * s ^ 2) -
        14 * (3 * t ^ 2 + 4) ^ 2 / (9 * t ^ 2) =
      14 * (s - t) * (s + t) * (3 * s * t - 4) *
        (3 * s * t + 4) / (9 * s ^ 2 * t ^ 2) := by
  field_simp [hs, ht]
  ring

private lemma sevenFamilyAt_affineEquivalent_refl (t : Real) :
    AffineEquivalent (sevenFamilyAt t) (sevenFamilyAt t) := by
  let T : NonsingularAffine :=
    { a := 1
      b := 0
      c := 0
      d := 1
      tx := 0
      ty := 0
      det_ne := by norm_num }
  refine ⟨Equiv.refl _, T, ?_⟩
  funext i
  simp [T, NonsingularAffine.map]

/-! ## Exact parameter classification -/

/-- Full-domain classification of affine equivalence inside the displayed
family. -/
theorem sevenFamilyAt_affineEquivalent_iff {s t : Real}
    (hs : 1 <= s ∧ s <= 4 / 3) (ht : 1 <= t ∧ t <= 4 / 3) :
    AffineEquivalent (sevenFamilyAt s) (sevenFamilyAt t) ↔
      s = t ∨ 3 * s * t = 4 := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs.1
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  constructor
  · intro hequiv
    rcases hequiv with ⟨sigma, T, hmap⟩
    have hmin :
        minTri (sevenFamilyAt t) =
          |T.det| * minTri (sevenFamilyAt s) := by
      rw [hmap, minTri7_nonsingularAffine]
      rw [show (fun i => sevenFamilyAt s (sigma i)) =
          sevenFamilyAt s ∘ sigma by rfl, minTri7_perm]
    rw [sevenFamilyAt_eq_cfg7Family t, sevenFamilyAt_eq_cfg7Family s,
      minTri_cfg7Family t ht, minTri_cfg7Family s hs] at hmin
    have habsdet : |T.det| = 1 := by
      nlinarith only [hmin]
    have hdetsq : T.det ^ 2 = 1 := by
      rcases le_total 0 T.det with hdet | hdet
      · rw [abs_of_nonneg hdet] at habsdet
        rw [habsdet]
        norm_num
      · rw [abs_of_nonpos hdet] at habsdet
        have hdet' : T.det = -1 := by
          linarith only [habsdet]
        rw [hdet']
        norm_num
    have hsum :
        sevenFamilyTriangleSquareSum (sevenFamilyAt t) =
          T.det ^ 2 *
            sevenFamilyTriangleSquareSum (sevenFamilyAt s) := by
      rw [hmap, sevenFamilyTriangleSquareSum_nonsingularAffine]
      rw [show (fun i => sevenFamilyAt s (sigma i)) =
          sevenFamilyAt s ∘ sigma by rfl,
        sevenFamilyTriangleSquareSum_relabel]
    rw [sevenFamilyTriangleSquareSum_value t htpos.ne',
      sevenFamilyTriangleSquareSum_value s hspos.ne',
      hdetsq, one_mul] at hsum
    have hzero :
        14 * (3 * s ^ 2 + 4) ^ 2 / (9 * s ^ 2) -
            14 * (3 * t ^ 2 + 4) ^ 2 / (9 * t ^ 2) = 0 := by
      linarith only [hsum]
    rw [sevenFamilyTriangleSquareSum_formula_sub
      s t hspos.ne' htpos.ne'] at hzero
    have hfactor :
        ((s - t) * (s + t)) *
            ((3 * s * t - 4) * (3 * s * t + 4)) = 0 := by
      field_simp [hspos.ne', htpos.ne'] at hzero
      nlinarith only [hzero]
    rcases mul_eq_zero.mp hfactor with hleft | hright
    · rcases mul_eq_zero.mp hleft with heq | hsumzero
      · exact Or.inl (sub_eq_zero.mp heq)
      · exfalso
        nlinarith only [hspos, htpos, hsumzero]
    · rcases mul_eq_zero.mp hright with hmirror | himpossible
      · exact Or.inr (sub_eq_zero.mp hmirror)
      · have hstpos : 0 < s * t := mul_pos hspos htpos
        exfalso
        nlinarith only [hstpos, himpossible]
  · rintro (rfl | hmirror)
    · exact sevenFamilyAt_affineEquivalent_refl s
    · have hiota : sevenFamilyMirrorParameter s = t := by
        unfold sevenFamilyMirrorParameter
        apply (div_eq_iff (mul_ne_zero (by norm_num) hspos.ne')).2
        nlinarith only [hmirror]
      rw [← hiota]
      exact sevenFamilyAt_affineEquivalent_mirror s hspos

/-- The selected real subinterval is injective modulo every nonsingular
affine map.  Its mirror interval is disjoint from it. -/
theorem heilbronn_convex_seven_real_family_inequivalent
    (s t : Real)
    (hs : 6 / 5 <= s ∧ s <= 5 / 4)
    (ht : 6 / 5 <= t ∧ t <= 5 / 4) :
    AffineEquivalent (sevenFamilyAt s) (sevenFamilyAt t) → s = t := by
  intro hequiv
  have hs' : 1 <= s ∧ s <= 4 / 3 := by
    constructor <;> nlinarith only [hs.1, hs.2]
  have ht' : 1 <= t ∧ t <= 4 / 3 := by
    constructor <;> nlinarith only [ht.1, ht.2]
  rcases (sevenFamilyAt_affineEquivalent_iff hs' ht').mp hequiv with
    heq | hmirror
  · exact heq
  · have hprod :
        ((6 : Real) / 5) * (6 / 5) <= s * t :=
      mul_le_mul hs.1 ht.1 (by norm_num)
        (by nlinarith only [hs.1])
    exfalso
    nlinarith only [hprod, hmirror]

/-! ## Countable-family integration helper -/

lemma sevenFamilyParameter_bounds_affine (k : Nat) :
    6 / 5 <= sevenFamilyParameter k ∧
      sevenFamilyParameter k <= 5 / 4 := by
  simpa only [sevenFamilyParameter, cfg7Parameter] using
    cfg7Parameter_bounds k

/-- The existing public sequence remains injective after the equivalence
relation is enlarged to arbitrary nonsingular affine maps. -/
theorem sevenFamily_eq_of_affineEquivalent {m n : Nat}
    (h : AffineEquivalent (sevenFamily m) (sevenFamily n)) :
    m = n := by
  have hparam := heilbronn_convex_seven_real_family_inequivalent
    (sevenFamilyParameter m) (sevenFamilyParameter n)
    (sevenFamilyParameter_bounds_affine m)
    (sevenFamilyParameter_bounds_affine n)
  have heq : sevenFamilyParameter m = sevenFamilyParameter n := by
    apply hparam
    simpa only [sevenFamily] using h
  apply cfg7Parameter_injective
  simpa only [sevenFamilyParameter, cfg7Parameter] using heq

end HeilbronnChallenge
