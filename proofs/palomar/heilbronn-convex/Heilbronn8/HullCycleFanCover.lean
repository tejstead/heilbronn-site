import Heilbronn8.HullArea
import Heilbronn8.Compose
import Heilbronn8.Radon
import Heilbronn8.TriVolume
import Mathlib.Analysis.Convex.Caratheodory

/-!
# A generic fan-cover lemma for a strict planar hull cycle

This file contains the geometric reduction needed to construct
`FanCovers` without a generated containment table.  The central observation
is a diagonal split.  If `A` is the fan anchor, `i < j < k` are later cycle
vertices, and `p` is in `triangle (i,j,k)`, put

`D = sig A (c j) p`.

For `D <= 0`, the barycentric determinant identities put `p` in
`triangle (A,i,j)`.  For `0 <= D`, they put it in
`triangle (A,j,k)`.  Thus every Caratheodory triangle made from cycle
vertices reduces to one anchored fan triangle.

The first theorem is the algebraic heart of the argument.  The final
Caratheodory-to-`FanCovers` assembly is kept separate so its finite indexing
plumbing can be reused by the hull-cycle existence construction.
-/

namespace Heilbronn8

private lemma sig_affine_second (a b c p r : ℝ × ℝ) (x y z : ℝ)
    (hxyz : x + y + z = 1) :
    sig p (x • a + y • b + z • c) r =
      x * sig p a r + y * sig p b r + z * sig p c r := by
  have hz : z = 1 - x - y := by
    linarith
  subst z
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

private lemma sig_affine_third (a b c p q : ℝ × ℝ) (x y z : ℝ)
    (hxyz : x + y + z = 1) :
    sig p q (x • a + y • b + z • c) =
      x * sig p q a + y * sig p q b + z * sig p q c := by
  have hz : z = 1 - x - y := by
    linarith
  subst z
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

/--
A triangle on three vertices after the fan anchor is covered by one of the
two fan triangles cut out by its middle vertex.

This statement deliberately uses weak `InTri` membership.  It therefore
also handles points on the splitting diagonal and on polygon edges.
-/
theorem inTri_tail_triangle_split_at_anchor
    {m : ℕ} [NeZero m]
    (v : Fin 8 → ℝ × ℝ) (c : Fin m → Fin 8)
    (hcyc : StrictCyclicPos c v)
    (i j k : Fin m)
    (hi : (0 : Fin m) < i) (hij : i < j) (hjk : j < k)
    (p : ℝ × ℝ)
    (hp : InTri p (v (c i)) (v (c j)) (v (c k))) :
    InTri p (v (c 0)) (v (c i)) (v (c j)) ∨
      InTri p (v (c 0)) (v (c j)) (v (c k)) := by
  let A := v (c 0)
  let B := v (c i)
  let C := v (c j)
  let D := v (c k)
  have hABC : 0 < sig A B C := by
    simpa [A, B, C] using hcyc.pos 0 i j hi hij
  have hABD : 0 < sig A B D := by
    simpa [A, B, D] using hcyc.pos 0 i k hi (hij.trans hjk)
  have hACD : 0 < sig A C D := by
    simpa [A, C, D] using hcyc.pos 0 j k (hi.trans hij) hjk
  have hBCD : 0 < sig B C D := by
    simpa [B, C, D] using hcyc.pos i j k hij hjk
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := hp
  let P : ℝ × ℝ := x • B + y • C + z • D
  have hP : x • B + y • C + z • D = P := rfl
  rcases le_total (sig A C P) 0 with hdiag | hdiag
  · left
    apply inTri_of_sig P A B C hABC
    · have heq : sig P B C = z * sig B C D := by
        rw [← hP, sig_affine_fst B C D B C x y z hsum]
        simp only [sig]
        ring
      rw [heq]
      exact mul_nonneg hz hBCD.le
    · rw [sig_swap A P C]
      exact neg_nonneg.mpr hdiag
    · have heq : sig A B P =
          y * sig A B C + z * sig A B D := by
        rw [← hP, sig_affine_third B C D A B x y z hsum]
        simp only [sig]
        ring
      rw [heq]
      exact add_nonneg (mul_nonneg hy hABC.le) (mul_nonneg hz hABD.le)
  · right
    apply inTri_of_sig P A C D hACD
    · have heq : sig P C D = x * sig B C D := by
        rw [← hP, sig_affine_fst B C D C D x y z hsum]
        simp only [sig]
        ring
      rw [heq]
      exact mul_nonneg hx hBCD.le
    · have heq : sig A P D =
          x * sig A B D + y * sig A C D := by
        rw [← hP, sig_affine_second B C D A D x y z hsum]
        simp only [sig]
        ring
      rw [heq]
      exact add_nonneg (mul_nonneg hx hABD.le) (mul_nonneg hy hACD.le)
    · exact hdiag

/-- Every cycle vertex belongs to every anchored fan triangle in which it is
one of the three displayed vertices. -/
private lemma fan_triangle_vertices
    {m : ℕ} [NeZero m]
    (v : Fin 8 → ℝ × ℝ) (c : Fin m → Fin 8)
    (i j : Fin m) :
    InTri (v (c 0)) (v (c 0)) (v (c i)) (v (c j)) ∧
      InTri (v (c i)) (v (c 0)) (v (c i)) (v (c j)) ∧
      InTri (v (c j)) (v (c 0)) (v (c i)) (v (c j)) := by
  exact ⟨inTri_vertexA _ _ _, inTri_vertexB _ _ _, inTri_vertexC _ _ _⟩

private lemma inTri_swap_first_two {p a b c : ℝ × ℝ}
    (h : InTri p a b c) : InTri p b a c := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hp⟩ := h
  refine ⟨y, x, z, hy, hx, hz, by linarith, ?_⟩
  rw [hp]
  module

private lemma inTri_swap_last_two {p a b c : ℝ × ℝ}
    (h : InTri p a b c) : InTri p a c b := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hp⟩ := h
  refine ⟨x, z, y, hx, hz, hy, by linarith, ?_⟩
  rw [hp]
  module

/-- With at least three indices, every one index can be included in an
anchored pair of positive positions. -/
private lemma exists_fan_pair_containing_one
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (r : Fin m) :
    ∃ i j : Fin m, (0 : Fin m) < i ∧ i < j ∧
      (r = 0 ∨ r = i ∨ r = j) := by
  let one : Fin m := ⟨1, by omega⟩
  let two : Fin m := ⟨2, by omega⟩
  by_cases hr0 : r = 0
  · exact ⟨one, two, by change (0 : Nat) < 1; omega,
      by change (1 : Nat) < 2; omega, Or.inl hr0⟩
  by_cases hr1 : r = one
  · exact ⟨one, two, by change (0 : Nat) < 1; omega,
      by change (1 : Nat) < 2; omega, Or.inr (Or.inl hr1)⟩
  let before : Fin m := ⟨r.val - 1, by omega⟩
  refine ⟨before, r, ?_, ?_, Or.inr (Or.inr rfl)⟩
  · change 0 < r.val - 1
    have hrval0 : r.val ≠ 0 := by
      intro h
      exact hr0 (Fin.ext h)
    have hrval1 : r.val ≠ 1 := by
      intro h
      apply hr1
      exact Fin.ext h
    omega
  · change r.val - 1 < r.val
    have : 0 < r.val := by
      exact (Fin.pos_iff_ne_zero' r).2 hr0
    omega

/-- With at least three indices, any two indices can simultaneously be
included among the anchor and two positive fan positions. -/
private lemma exists_fan_pair_containing_two
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (r s : Fin m) :
    ∃ i j : Fin m, (0 : Fin m) < i ∧ i < j ∧
      (r = 0 ∨ r = i ∨ r = j) ∧
      (s = 0 ∨ s = i ∨ s = j) := by
  by_cases hr0 : r = 0
  · obtain ⟨i, j, hi, hij, hs⟩ := exists_fan_pair_containing_one hm s
    exact ⟨i, j, hi, hij, Or.inl hr0, hs⟩
  by_cases hs0 : s = 0
  · obtain ⟨i, j, hi, hij, hr⟩ := exists_fan_pair_containing_one hm r
    exact ⟨i, j, hi, hij, hr, Or.inl hs0⟩
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · exact ⟨r, s, (Fin.pos_iff_ne_zero' r).2 hr0, hrs,
      Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · subst s
    obtain ⟨i, j, hi, hij, hr⟩ := exists_fan_pair_containing_one hm r
    exact ⟨i, j, hi, hij, hr, hr⟩
  · exact ⟨s, r, (Fin.pos_iff_ne_zero' s).2 hs0, hrs,
      Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩

/-- Planar Caratheodory, in the exact three-point form used below. -/
private lemma exists_inTri_of_mem_convexHull_range
    {m : ℕ} [NeZero m] (z : Fin m → ℝ × ℝ)
    {p : ℝ × ℝ}
    (hp : p ∈ convexHull ℝ (Set.range z)) :
    ∃ a b c : Fin m, InTri p (z a) (z b) (z c) := by
  rw [convexHull_eq_union] at hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨t, htRange, htIndependent, hpt⟩ := hp
  have hcard : t.card ≤ 3 := by
    calc
      t.card = Fintype.card t := by simp
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → ℝ × ℝ))) + 1 :=
        htIndependent.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (ℝ × ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = 3 := by norm_num [Module.finrank_prod]
  have hcases : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 ∨ t.card = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · have ht : t = ∅ := Finset.card_eq_zero.mp h0
    subst t
    exfalso
    simpa using hpt
  · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨a, ha⟩ := htRange
      (show q ∈ ((↑({q} : Finset (ℝ × ℝ))) : Set (ℝ × ℝ)) by simp)
    refine ⟨a, a, a, ?_⟩
    apply (inTri_iff_mem_convexHull _ _ _ _).2
    have hpa : p ∈ convexHull ℝ ({z a} : Set (ℝ × ℝ)) := by
      simpa [ha] using hpt
    simpa using hpa
  · obtain ⟨q, r, _hqr, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨a, ha⟩ := htRange
      (show q ∈ ((↑({q, r} : Finset (ℝ × ℝ))) : Set (ℝ × ℝ)) by simp)
    obtain ⟨b, hb⟩ := htRange
      (show r ∈ ((↑({q, r} : Finset (ℝ × ℝ))) : Set (ℝ × ℝ)) by simp)
    refine ⟨a, b, b, ?_⟩
    apply (inTri_iff_mem_convexHull _ _ _ _).2
    have hpab : p ∈ convexHull ℝ ({z a, z b} : Set (ℝ × ℝ)) := by
      simpa [ha, hb] using hpt
    simpa using hpab
  · obtain ⟨q, r, s, _hqr, _hqs, _hrs, rfl⟩ :=
      Finset.card_eq_three.mp h3
    obtain ⟨a, ha⟩ := htRange
      (show q ∈ ((↑({q, r, s} : Finset (ℝ × ℝ))) : Set (ℝ × ℝ)) by simp)
    obtain ⟨b, hb⟩ := htRange
      (show r ∈ ((↑({q, r, s} : Finset (ℝ × ℝ))) : Set (ℝ × ℝ)) by simp)
    obtain ⟨c, hc⟩ := htRange
      (show s ∈ ((↑({q, r, s} : Finset (ℝ × ℝ))) : Set (ℝ × ℝ)) by simp)
    refine ⟨a, b, c, ?_⟩
    apply (inTri_iff_mem_convexHull _ _ _ _).2
    simpa [ha, hb, hc] using hpt

/--
Strict cyclic position plus convex-hull containment implies the semantic
`FanCovers` certificate.  No sign word and no generated containment payload
is used.

The injectivity hypothesis is part of the intended hull-cycle interface.  It
is not needed by the diagonal reduction itself, since the strict cyclic
determinants already separate all cycle points used in a triangle.
-/
theorem fanCovers_of_strictCyclicPos_of_convexHull
    {m : ℕ} [NeZero m]
    (v : Fin 8 → ℝ × ℝ) (c : Fin m → Fin 8)
    (hm : 3 ≤ m) (_hc : Function.Injective c)
    (hcyc : StrictCyclicPos c v)
    (hcontain : Set.range v ⊆ convexHull ℝ (Set.range (v ∘ c))) :
    FanCovers v c := by
  intro p _hpOutside
  have hpHull : v p ∈ convexHull ℝ (Set.range (v ∘ c)) :=
    hcontain ⟨p, rfl⟩
  obtain ⟨a, b, d, hp⟩ :=
    exists_inTri_of_mem_convexHull_range (v ∘ c) hpHull
  have finish (i j k : Fin m) (hij : i < j) (hjk : j < k)
      (htri : InTri (v p) (v (c i)) (v (c j)) (v (c k))) :
      ∃ u w : Fin m, (0 : Fin m) < u ∧ u < w ∧
        InTri (v p) (v (c 0)) (v (c u)) (v (c w)) := by
    by_cases hi0 : i = 0
    · subst i
      exact ⟨j, k, hij, hjk, htri⟩
    · have hi : (0 : Fin m) < i := (Fin.pos_iff_ne_zero' i).2 hi0
      rcases inTri_tail_triangle_split_at_anchor
          v c hcyc i j k hi hij hjk (v p) htri with h | h
      · exact ⟨i, j, hi, hij, h⟩
      · exact ⟨j, k, hi.trans hij, hjk, h⟩
  by_cases hab : a = b
  · subst b
    by_cases had : a = d
    · subst d
      obtain ⟨i, j, hi, hij, ha⟩ := exists_fan_pair_containing_one hm a
      refine ⟨i, j, hi, hij, ?_⟩
      apply inTri_absorb hp
      all_goals rcases ha with h | h | h <;> subst a
      all_goals first
        | exact inTri_vertexA _ _ _
        | exact inTri_vertexB _ _ _
        | exact inTri_vertexC _ _ _
    · obtain ⟨i, j, hi, hij, ha, hd⟩ :=
        exists_fan_pair_containing_two hm a d
      refine ⟨i, j, hi, hij, ?_⟩
      apply inTri_absorb hp
      · rcases ha with h | h | h <;> subst a
        · exact inTri_vertexA _ _ _
        · exact inTri_vertexB _ _ _
        · exact inTri_vertexC _ _ _
      · rcases ha with h | h | h <;> subst a
        · exact inTri_vertexA _ _ _
        · exact inTri_vertexB _ _ _
        · exact inTri_vertexC _ _ _
      · rcases hd with h | h | h <;> subst d
        · exact inTri_vertexA _ _ _
        · exact inTri_vertexB _ _ _
        · exact inTri_vertexC _ _ _
  · by_cases had : a = d
    · subst d
      obtain ⟨i, j, hi, hij, ha, hb⟩ :=
        exists_fan_pair_containing_two hm a b
      refine ⟨i, j, hi, hij, ?_⟩
      apply inTri_absorb hp
      · rcases ha with h | h | h <;> subst a
        · exact inTri_vertexA _ _ _
        · exact inTri_vertexB _ _ _
        · exact inTri_vertexC _ _ _
      · rcases hb with h | h | h <;> subst b
        · exact inTri_vertexA _ _ _
        · exact inTri_vertexB _ _ _
        · exact inTri_vertexC _ _ _
      · rcases ha with h | h | h <;> subst a
        · exact inTri_vertexA _ _ _
        · exact inTri_vertexB _ _ _
        · exact inTri_vertexC _ _ _
    · by_cases hbd : b = d
      · subst d
        obtain ⟨i, j, hi, hij, ha, hb⟩ :=
          exists_fan_pair_containing_two hm a b
        refine ⟨i, j, hi, hij, ?_⟩
        apply inTri_absorb hp
        · rcases ha with h | h | h <;> subst a
          · exact inTri_vertexA _ _ _
          · exact inTri_vertexB _ _ _
          · exact inTri_vertexC _ _ _
        · rcases hb with h | h | h <;> subst b
          · exact inTri_vertexA _ _ _
          · exact inTri_vertexB _ _ _
          · exact inTri_vertexC _ _ _
        · rcases hb with h | h | h <;> subst b
          · exact inTri_vertexA _ _ _
          · exact inTri_vertexB _ _ _
          · exact inTri_vertexC _ _ _
      · rcases lt_or_gt_of_ne hab with hablt | hbalt
        · rcases lt_or_gt_of_ne hbd with hbdlt | hdblt
          · exact finish a b d hablt hbdlt hp
          · rcases lt_or_gt_of_ne had with hadlt | hdalt
            · exact finish a d b hadlt hdblt
                (inTri_swap_last_two hp)
            · exact finish d a b hdalt hablt
                (inTri_swap_first_two (inTri_swap_last_two hp))
        · rcases lt_or_gt_of_ne had with hadlt | hdalt
          · exact finish b a d hbalt hadlt
              (inTri_swap_first_two hp)
          · rcases lt_or_gt_of_ne hbd with hbdlt | hdblt
            · exact finish b d a hbdlt hdalt
                (inTri_swap_last_two (inTri_swap_first_two hp))
            · exact finish d b a hdblt hbalt
                (inTri_swap_first_two
                  (inTri_swap_last_two (inTri_swap_first_two hp)))

end Heilbronn8
