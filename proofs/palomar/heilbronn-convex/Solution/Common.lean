/-
Shared plumbing between the challenge statements and the measure bridge.

`HeilbronnChallenge.sig` and `HullBridge.sig` have the same body, so they are
the same function; `sig_eq` records that and every cross-namespace step below
is definitional.
-/
import HullBridge
import Solution.Defs

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

lemma sig_eq (p q r : ℝ × ℝ) : sig p q r = HullBridge.sig p q r := rfl

/-! ## `minTri` as an infimum over triples -/

lemma mem_triples {n : Nat} {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    (i, j, k) ∈ triples n := by
  simp only [triples, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hij, hjk⟩

lemma minTri_le {n : Nat} [Fact ((triples n).Nonempty)] (v : Fin n → ℝ × ℝ)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    minTri v ≤ |sig (v i) (v j) (v k)| :=
  Finset.inf'_le _ (mem_triples hij hjk)

lemma le_minTri {n : Nat} [Fact ((triples n).Nonempty)] (v : Fin n → ℝ × ℝ)
    (r : ℝ) (h : ∀ t ∈ triples n, r ≤ |sig (v t.1) (v t.2.1) (v t.2.2)|) :
    r ≤ minTri v :=
  Finset.le_inf' _ _ h

lemma minTri_nonneg {n : Nat} [Fact ((triples n).Nonempty)]
    (v : Fin n → ℝ × ℝ) : 0 ≤ minTri v :=
  le_minTri v 0 fun _ _ => abs_nonneg _

/-- If the minimum triangle is positive, no ordered triple is degenerate. -/
lemma sig_ne_zero_of_minTri_pos {n : Nat} [Fact ((triples n).Nonempty)]
    (v : Fin n → ℝ × ℝ) (h : 0 < minTri v) (i j k : Fin n)
    (hij : i < j) (hjk : j < k) : sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  have := minTri_le v i j k hij hjk
  rw [hzero, abs_zero] at this
  linarith

/-! ## Attaining the supremum -/

lemma h_convex_eq {n : Nat} [Fact ((triples n).Nonempty)] (val : ℝ)
    (hmem : AdmissibleScore n val)
    (hub : ∀ r : ℝ, AdmissibleScore n r → r ≤ val) :
    h_convex n = val :=
  IsGreatest.csSup_eq ⟨hmem, fun _ hr => hub _ hr⟩

/-- A pointwise unit-hull bound and an attaining configuration determine the
supremum exactly. -/
lemma h_convex_eq_of_pointwise_upper
    {n : Nat} [Fact ((triples n).Nonempty)] (val : ℝ)
    (hval0 : 0 ≤ val) (hval1 : val ≤ 1)
    (hatt : ∃ p : Fin n → ℝ × ℝ,
      volume (convexHull ℝ (Set.range p)) = 1 ∧ minTri p = 2 * val)
    (hub : ∀ p : Fin n → ℝ × ℝ,
      volume (convexHull ℝ (Set.range p)) = 1 → minTri p ≤ 2 * val) :
    h_convex n = val := by
  apply h_convex_eq val
  · exact ⟨hval0, hval1, hatt⟩
  · rintro r ⟨_, _, p, hvol, hmin⟩
    have h := hub p hvol
    rw [hmin] at h
    linarith

/-! ## Absolute values of permuted `sig`s -/

lemma abs_sig_swap (a b c : ℝ × ℝ) : |sig a c b| = |sig a b c| := by
  rw [show sig a c b = -sig a b c by simp only [sig]; ring, abs_neg]

lemma abs_sig_rotate (a b c : ℝ × ℝ) : |sig b c a| = |sig a b c| := by
  rw [show sig b c a = sig a b c by simp only [sig]; ring]

lemma abs_sig_swap12 (a b c : ℝ × ℝ) : |sig b a c| = |sig a b c| := by
  rw [show sig b a c = -sig a b c by simp only [sig]; ring, abs_neg]

lemma abs_sig_reverse (a b c : ℝ × ℝ) : |sig c b a| = |sig a b c| := by
  rw [show sig c b a = -sig a b c by simp only [sig]; ring, abs_neg]

/-- `minTri` bounds every triple of *distinct* indices, in any order: the
absolute doubled area does not depend on the order of the three points. -/
lemma minTri_le_of_distinct {n : Nat} [Fact ((triples n).Nonempty)]
    (v : Fin n → ℝ × ℝ) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : minTri v ≤ |sig (v i) (v j) (v k)| := by
  rcases lt_trichotomy i j with hij' | he | hij'
  · rcases lt_trichotomy j k with hjk' | he | hjk'
    · exact minTri_le v i j k hij' hjk'
    · exact absurd he hjk
    · rcases lt_trichotomy i k with hik' | he | hik'
      · -- i < k < j
        exact le_of_le_of_eq (minTri_le v i k j hik' hjk')
          (abs_sig_swap (v i) (v j) (v k))
      · exact absurd he hik
      · -- k < i < j
        exact le_of_le_of_eq (minTri_le v k i j hik' hij')
          (abs_sig_rotate (v k) (v i) (v j)).symm
  · exact absurd he hij
  · rcases lt_trichotomy i k with hik' | he | hik'
    · -- j < i < k
      exact le_of_le_of_eq (minTri_le v j i k hij' hik')
        (abs_sig_swap12 (v i) (v j) (v k))
    · exact absurd he hik
    · rcases lt_trichotomy j k with hjk' | he | hjk'
      · -- j < k < i
        exact le_of_le_of_eq (minTri_le v j k i hjk' hik')
          (abs_sig_rotate (v i) (v j) (v k))
      · exact absurd he hjk
      · -- k < j < i
        exact le_of_le_of_eq (minTri_le v k j i hjk' hij')
          (abs_sig_reverse (v i) (v j) (v k))

/-- If the minimum triangle is positive, no triple of distinct indices is
degenerate, whatever order the indices are listed in. -/
lemma sig_ne_zero_of_distinct {n : Nat} [Fact ((triples n).Nonempty)]
    (v : Fin n → ℝ × ℝ) (h : 0 < minTri v) (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  have hle := minTri_le_of_distinct v i j k hij hik hjk
  rw [hzero, abs_zero] at hle
  linarith

/-! ## Index enumeration -/

lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

lemma fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

lemma fin5_cases (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  revert i; decide

lemma fin6_cases (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

lemma fin7_cases (i : Fin 7) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  revert i; decide

/-! ## Enumeration of ordered triples -/

lemma triple_cases3 (i j k : Fin 3) (hij : i < j) (hjk : j < k) :
    i = 0 ∧ j = 1 ∧ k = 2 := by
  revert i j k
  decide

lemma triple_cases4 (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3) := by
  revert i j k
  decide

lemma triple_cases5 (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 1 ∧ k = 4) ∨ (i = 0 ∧ j = 2 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 4) ∨ (i = 0 ∧ j = 3 ∧ k = 4) ∨
      (i = 1 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 4) ∨
      (i = 1 ∧ j = 3 ∧ k = 4) ∨ (i = 2 ∧ j = 3 ∧ k = 4) := by
  revert i j k
  decide

-- Twenty disjuncts nest `Or.decidable` deeper than the default instance-size
-- budget allows, so the `Decidable` instance for the quantified statement has to
-- be given more room than `triple_cases5` needed.
set_option synthInstance.maxSize 4000 in
lemma triple_cases6 (i j k : Fin 6) (hij : i < j) (hjk : j < k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 1 ∧ k = 4) ∨ (i = 0 ∧ j = 1 ∧ k = 5) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 0 ∧ j = 2 ∧ k = 4) ∨
      (i = 0 ∧ j = 2 ∧ k = 5) ∨ (i = 0 ∧ j = 3 ∧ k = 4) ∨
      (i = 0 ∧ j = 3 ∧ k = 5) ∨ (i = 0 ∧ j = 4 ∧ k = 5) ∨
      (i = 1 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 4) ∨
      (i = 1 ∧ j = 2 ∧ k = 5) ∨ (i = 1 ∧ j = 3 ∧ k = 4) ∨
      (i = 1 ∧ j = 3 ∧ k = 5) ∨ (i = 1 ∧ j = 4 ∧ k = 5) ∨
      (i = 2 ∧ j = 3 ∧ k = 4) ∨ (i = 2 ∧ j = 3 ∧ k = 5) ∨
      (i = 2 ∧ j = 4 ∧ k = 5) ∨ (i = 3 ∧ j = 4 ∧ k = 5) := by
  revert i j k
  decide

-- Thirty-five disjuncts; the `Decidable` instance for the
-- quantified statement needs correspondingly more room.
set_option synthInstance.maxSize 8000 in
lemma triple_cases7 (i j k : Fin 7) (hij : i < j) (hjk : j < k) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 1 ∧ k = 4) ∨ (i = 0 ∧ j = 1 ∧ k = 5) ∨
      (i = 0 ∧ j = 1 ∧ k = 6) ∨ (i = 0 ∧ j = 2 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 4) ∨ (i = 0 ∧ j = 2 ∧ k = 5) ∨
      (i = 0 ∧ j = 2 ∧ k = 6) ∨ (i = 0 ∧ j = 3 ∧ k = 4) ∨
      (i = 0 ∧ j = 3 ∧ k = 5) ∨ (i = 0 ∧ j = 3 ∧ k = 6) ∨
      (i = 0 ∧ j = 4 ∧ k = 5) ∨ (i = 0 ∧ j = 4 ∧ k = 6) ∨
      (i = 0 ∧ j = 5 ∧ k = 6) ∨ (i = 1 ∧ j = 2 ∧ k = 3) ∨
      (i = 1 ∧ j = 2 ∧ k = 4) ∨ (i = 1 ∧ j = 2 ∧ k = 5) ∨
      (i = 1 ∧ j = 2 ∧ k = 6) ∨ (i = 1 ∧ j = 3 ∧ k = 4) ∨
      (i = 1 ∧ j = 3 ∧ k = 5) ∨ (i = 1 ∧ j = 3 ∧ k = 6) ∨
      (i = 1 ∧ j = 4 ∧ k = 5) ∨ (i = 1 ∧ j = 4 ∧ k = 6) ∨
      (i = 1 ∧ j = 5 ∧ k = 6) ∨ (i = 2 ∧ j = 3 ∧ k = 4) ∨
      (i = 2 ∧ j = 3 ∧ k = 5) ∨ (i = 2 ∧ j = 3 ∧ k = 6) ∨
      (i = 2 ∧ j = 4 ∧ k = 5) ∨ (i = 2 ∧ j = 4 ∧ k = 6) ∨
      (i = 2 ∧ j = 5 ∧ k = 6) ∨ (i = 3 ∧ j = 4 ∧ k = 5) ∨
      (i = 3 ∧ j = 4 ∧ k = 6) ∨ (i = 3 ∧ j = 5 ∧ k = 6) ∨
      (i = 4 ∧ j = 5 ∧ k = 6) := by
  revert i j k
  decide

/-! ## Hull volume in terms of `sig` -/

lemma volume_hull_fin3 (p : Fin 3 → ℝ × ℝ) :
    volume (convexHull ℝ (Set.range p)) =
      ENNReal.ofReal (|sig (p 0) (p 1) (p 2)| / 2) := by
  have h := HullBridge.volume_triangle (p 0) (p 1) (p 2)
  rw [HullBridge.range_fin3]
  exact h

/-- The range of a 4-point family, listed in any order that covers all four
indices. -/
lemma set4_perm (p : Fin 4 → ℝ × ℝ) (i0 i1 i2 i3 : Fin 4)
    (hcover : ∀ k : Fin 4, k = i0 ∨ k = i1 ∨ k = i2 ∨ k = i3) :
    Set.range p = ({p i0, p i1, p i2, p i3} : Set (ℝ × ℝ)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    rcases hcover k with hk | hk | hk | hk
    · rw [hk]; exact Set.mem_insert _ _
    · rw [hk]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [hk]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · rw [hk]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl))
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨i0, rfl⟩
    · exact ⟨i1, rfl⟩
    · exact ⟨i2, rfl⟩
    · exact ⟨i3, rfl⟩

/-- Strict convex position of an indexed 4-tuple, in the form the fan formula
wants. -/
lemma strict_of_sigs4 (v : Fin 4 → ℝ × ℝ)
    (h1 : 0 < sig (v 0) (v 1) (v 2)) (h2 : 0 < sig (v 0) (v 1) (v 3))
    (h3 : 0 < sig (v 0) (v 2) (v 3)) (h4 : 0 < sig (v 1) (v 2) (v 3)) :
    ∀ i j k : Fin 4, i < j → j < k →
      0 < HullBridge.sig (v i) (v j) (v k) := by
  intro i j k hij hjk
  rcases triple_cases4 i j k hij hjk with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h1
  · exact h2
  · exact h3
  · exact h4

lemma volume_hull_fin4_strict (v : Fin 4 → ℝ × ℝ)
    (h1 : 0 < sig (v 0) (v 1) (v 2)) (h2 : 0 < sig (v 0) (v 1) (v 3))
    (h3 : 0 < sig (v 0) (v 2) (v 3)) (h4 : 0 < sig (v 1) (v 2) (v 3)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal ((sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)) / 2) :=
  HullBridge.volume_convexHull_strictCCW4 v (strict_of_sigs4 v h1 h2 h3 h4)

lemma strict_of_sigs5 (v : Fin 5 → ℝ × ℝ)
    (h012 : 0 < sig (v 0) (v 1) (v 2)) (h013 : 0 < sig (v 0) (v 1) (v 3))
    (h014 : 0 < sig (v 0) (v 1) (v 4)) (h023 : 0 < sig (v 0) (v 2) (v 3))
    (h024 : 0 < sig (v 0) (v 2) (v 4)) (h034 : 0 < sig (v 0) (v 3) (v 4))
    (h123 : 0 < sig (v 1) (v 2) (v 3)) (h124 : 0 < sig (v 1) (v 2) (v 4))
    (h134 : 0 < sig (v 1) (v 3) (v 4)) (h234 : 0 < sig (v 2) (v 3) (v 4)) :
    ∀ i j k : Fin 5, i < j → j < k →
      0 < HullBridge.sig (v i) (v j) (v k) := by
  intro i j k hij hjk
  rcases triple_cases5 i j k hij hjk with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h012
  · exact h013
  · exact h014
  · exact h023
  · exact h024
  · exact h034
  · exact h123
  · exact h124
  · exact h134
  · exact h234

lemma volume_hull_fin5_strict (v : Fin 5 → ℝ × ℝ)
    (h012 : 0 < sig (v 0) (v 1) (v 2)) (h013 : 0 < sig (v 0) (v 1) (v 3))
    (h014 : 0 < sig (v 0) (v 1) (v 4)) (h023 : 0 < sig (v 0) (v 2) (v 3))
    (h024 : 0 < sig (v 0) (v 2) (v 4)) (h034 : 0 < sig (v 0) (v 3) (v 4))
    (h123 : 0 < sig (v 1) (v 2) (v 3)) (h124 : 0 < sig (v 1) (v 2) (v 4))
    (h134 : 0 < sig (v 1) (v 3) (v 4)) (h234 : 0 < sig (v 2) (v 3) (v 4)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal ((sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)
        + sig (v 0) (v 3) (v 4)) / 2) :=
  HullBridge.volume_convexHull_strictCCW5 v
    (strict_of_sigs5 v h012 h013 h014 h023 h024 h034 h123 h124 h134 h234)

/-! ## Splitting a triangle at an interior point -/

/-- If `x` lies in the triangle `a b c`, the three cells it cuts out have
absolute doubled areas summing to that of `a b c`. -/
lemma abs_sig_sum_of_inTri (a b c x : ℝ × ℝ) (h : HullBridge.InTri x a b c) :
    |sig a b x| + |sig b c x| + |sig c a x| = |sig a b c| := by
  obtain ⟨al, be, ga, hal, hbe, hga, hsum, hx⟩ := h
  have hal' : al = 1 - be - ga := by linarith
  subst hal'
  have h1 : sig a b x = ga * sig a b c := by
    rw [hx]
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    ring
  have h2 : sig b c x = (1 - be - ga) * sig a b c := by
    rw [hx]
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    ring
  have h3 : sig c a x = be * sig a b c := by
    rw [hx]
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    ring
  rw [h1, h2, h3, abs_mul, abs_mul, abs_mul, abs_of_nonneg hga,
    abs_of_nonneg hal, abs_of_nonneg hbe]
  ring

end HeilbronnChallenge
