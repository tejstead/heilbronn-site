import Heilbronn8.HullArea
import Heilbronn8.Collinear
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.KreinMilman

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-!
# A finite irredundant carrier for the planar convex hull

This is the non-combinatorial first half of hull-cycle existence.  The
carrier consists of the extreme points of the actual finite convex hull,
pulled back to the original labels.  Krein-Milman has no closure cost here:
the extreme-point set is finite, hence its convex hull is closed.
-/

/-- Data needed by the purely planar ordering argument. -/
structure StrictHullCarrier (v : Fin 8 → ℝ × ℝ) where
  labels : Finset (Fin 8)
  card_ge_three : 3 ≤ labels.card
  card_le_eight : labels.card ≤ 8
  covers : ∀ p : Fin 8,
    v p ∈ convexHull ℝ (v '' (↑labels : Set (Fin 8)))
  irredundant : ∀ q ∈ labels,
    v q ∉ convexHull ℝ (v '' (↑(labels.erase q) : Set (Fin 8)))

private lemma sig_ne_zero_of_strict
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v)
    (a b c : Fin 8) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    sig (v a) (v b) (v c) ≠ 0 := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
    · exact hstrict a b c hablt hbclt
    · rcases lt_or_gt_of_ne hac with haclt | hcalt
      · have h := hstrict a c b haclt hcblt
        intro hzero
        apply h
        rw [sig_swap]
        simp [hzero]
      · have h := hstrict c a b hcalt hablt
        intro hzero
        apply h
        rwa [← sig_rotate, ← sig_rotate]
  · rcases lt_or_gt_of_ne hac with haclt | hcalt
    · have h := hstrict b a c hbalt haclt
      intro hzero
      apply h
      simp only [sig] at hzero ⊢
      linear_combination -hzero
    · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
      · have h := hstrict b c a hbclt hcalt
        intro hzero
        apply h
        rwa [← sig_rotate]
      · have h := hstrict c b a hcblt hbalt
        intro hzero
        apply h
        simp only [sig] at hzero ⊢
        linear_combination -hzero

private lemma injective_of_allTripleSignsStrict
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v) :
    Function.Injective v := by
  intro i j hij
  by_contra hne
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  have hsig := sig_ne_zero_of_strict v hstrict i j k hne
    hki.symm hkj.symm
  apply hsig
  rw [hij]
  simp [sig]

private lemma sig_eq_zero_of_collinear_triple
    {a b c : ℝ × ℝ}
    (h : Collinear ℝ ({a, b, c} : Set (ℝ × ℝ))) :
    sig a b c = 0 := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p, w, hw⟩ := h
  obtain ⟨ra, hra⟩ := hw a (by simp)
  obtain ⟨rb, hrb⟩ := hw b (by simp)
  obtain ⟨rc, hrc⟩ := hw c (by simp)
  rw [hra, hrb, hrc]
  simp [sig]
  ring

/-- Every strict eight-point configuration has a finite convex-independent
label carrier of size between three and eight whose convex hull contains all
eight points. -/
noncomputable def strictHullCarrier_exists
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v) :
    StrictHullCarrier v := by
  classical
  let K : Set (ℝ × ℝ) := convexHull ℝ (Set.range v)
  let E : Set (ℝ × ℝ) := K.extremePoints ℝ
  let labels : Finset (Fin 8) :=
    Finset.univ.filter fun i ↦ v i ∈ E

  have hKcompact : IsCompact K := by
    simpa [K] using finite_range_isCompact_convexHull v
  have hKconvex : Convex ℝ K := by
    simpa [K] using convex_convexHull ℝ (Set.range v)
  have hEsubset : E ⊆ Set.range v := by
    simpa [E, K] using
      (extremePoints_convexHull_subset
        (𝕜 := ℝ) (A := Set.range v))
  have hEfinite : E.Finite :=
    (Set.finite_range v).subset hEsubset
  have hEK : convexHull ℝ E = K := by
    have hKM := closure_convexHull_extremePoints hKcompact hKconvex
    have hclosed : IsClosed (convexHull ℝ E) :=
      hEfinite.isClosed_convexHull ℝ
    rw [hclosed.closure_eq] at hKM
    exact hKM
  have himage : v '' (↑labels : Set (Fin 8)) = E := by
    apply Set.Subset.antisymm
    · rintro _ ⟨i, hi, rfl⟩
      simpa [labels] using hi
    · intro x hx
      obtain ⟨i, rfl⟩ := hEsubset hx
      exact ⟨i, by simpa [labels] using hx, rfl⟩
  have hcover : ∀ p : Fin 8,
      v p ∈ convexHull ℝ (v '' (↑labels : Set (Fin 8))) := by
    intro p
    rw [himage, hEK]
    exact subset_convexHull ℝ (Set.range v) ⟨p, rfl⟩

  have hvInjective : Function.Injective v :=
    injective_of_allTripleSignsStrict v hstrict
  have hEindependent : ConvexIndependent ℝ ((↑) : E → ℝ × ℝ) :=
    hKconvex.convexIndependent_extremePoints
  have hEirredundant : ∀ x ∈ E,
      x ∉ convexHull ℝ (E \ {x}) :=
    convexIndependent_set_iff_notMem_convexHull_sdiff.mp hEindependent
  have hirredundant : ∀ q ∈ labels,
      v q ∉ convexHull ℝ
        (v '' (↑(labels.erase q) : Set (Fin 8))) := by
    intro q hq hbad
    have hvqE : v q ∈ E := by simpa [labels] using hq
    apply hEirredundant (v q) hvqE
    apply (convexHull_mono ?_) hbad
    rintro _ ⟨i, hi, rfl⟩
    have hiErase : i ∈ labels.erase q := by
      simpa [Finset.mem_erase, and_comm] using hi
    have hiLabels : i ∈ labels := Finset.mem_of_mem_erase hiErase
    have hiq : i ≠ q := Finset.ne_of_mem_erase hiErase
    refine ⟨?_, ?_⟩
    · simpa [labels] using hiLabels
    · intro heq
      exact hiq (hvInjective heq)

  have hcard_le : labels.card ≤ 8 := by
    simpa using Finset.card_le_univ labels
  have hcard_ge : 3 ≤ labels.card := by
    by_contra hnot
    have hle : labels.card ≤ 2 := by omega
    have hsizes : labels.card = 0 ∨ labels.card = 1 ∨
        labels.card = 2 := by omega
    have h012 : sig (v 0) (v 1) (v 2) ≠ 0 :=
      hstrict 0 1 2 (by decide) (by decide)
    rcases hsizes with hzero | hone | htwo
    · have hlabels : labels = ∅ := Finset.card_eq_zero.mp hzero
      have h := hcover 0
      simp [hlabels] at h
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
      have h0 : v 0 = v a := by
        have := hcover 0
        simpa [ha] using this
      have h1 : v 1 = v a := by
        have := hcover 1
        simpa [ha] using this
      apply h012
      rw [h0, h1]
      simp [sig]
    · obtain ⟨a, b, hab, habLabels⟩ := Finset.card_eq_two.mp htwo
      have hline : ∀ p : Fin 8, v p ∈ affineSpan ℝ ({v a, v b} : Set (ℝ × ℝ)) := by
        intro p
        apply convexHull_subset_affineSpan (𝕜 := ℝ)
          ({v a, v b} : Set (ℝ × ℝ))
        have := hcover p
        have himage :
            v '' (↑labels : Set (Fin 8)) =
              ({v a, v b} : Set (ℝ × ℝ)) := by
          ext z
          simp [habLabels, eq_comm]
        rw [himage] at this
        simpa only [convexHull_pair] using this
      have hcol : Collinear ℝ ({v 0, v 1, v 2} : Set (ℝ × ℝ)) :=
        collinear_triple_of_mem_affineSpan_pair
          (hline 0) (hline 1) (hline 2)
      exact h012 (sig_eq_zero_of_collinear_triple hcol)
  exact ⟨labels, hcard_ge, hcard_le, hcover, hirredundant⟩

end Heilbronn8
