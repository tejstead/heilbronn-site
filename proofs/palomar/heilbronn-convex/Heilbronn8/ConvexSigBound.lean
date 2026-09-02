import Heilbronn8.Defs

namespace Heilbronn8

/-!
# Signed-area bounds on convex hulls

The signed-area form is separately affine in each point.  Consequently, an
absolute bound that holds for every ordered triple from a set also holds when
each of the three points is allowed to range over the set's convex hull.
-/

/-- Separate affinity of `sig` in its first argument, for two summands. -/
lemma sig_affine_fst_two (p₁ p₂ q r : ℝ × ℝ) (u v : ℝ)
    (huv : u + v = 1) :
    sig (u • p₁ + v • p₂) q r =
      u * sig p₁ q r + v * sig p₂ q r := by
  simpa using sig_affine_fst p₁ p₂ p₂ q r u v 0 (by linarith)

/-- Separate affinity of `sig` in its second argument, for two summands. -/
lemma sig_affine_snd_two (p q₁ q₂ r : ℝ × ℝ) (u v : ℝ)
    (huv : u + v = 1) :
    sig p (u • q₁ + v • q₂) r =
      u * sig p q₁ r + v * sig p q₂ r := by
  calc
    sig p (u • q₁ + v • q₂) r =
        sig (u • q₁ + v • q₂) r p := sig_rotate _ _ _
    _ = u * sig q₁ r p + v * sig q₂ r p :=
      sig_affine_fst_two q₁ q₂ r p u v huv
    _ = u * sig p q₁ r + v * sig p q₂ r := by
      rw [← sig_rotate p q₁ r, ← sig_rotate p q₂ r]

/-- Separate affinity of `sig` in its third argument, for two summands. -/
lemma sig_affine_third_two (p q r₁ r₂ : ℝ × ℝ) (u v : ℝ)
    (huv : u + v = 1) :
    sig p q (u • r₁ + v • r₂) =
      u * sig p q r₁ + v * sig p q r₂ := by
  calc
    sig p q (u • r₁ + v • r₂) =
        sig q (u • r₁ + v • r₂) p := sig_rotate _ _ _
    _ = sig (u • r₁ + v • r₂) p q := sig_rotate _ _ _
    _ = u * sig r₁ p q + v * sig r₂ p q :=
      sig_affine_fst_two r₁ r₂ p q u v huv
    _ = u * sig p q r₁ + v * sig p q r₂ := by
      rw [sig_rotate r₁ p q, sig_rotate r₂ p q]

private lemma abs_weighted_le {a b C u v : ℝ}
    (ha : |a| ≤ C) (hb : |b| ≤ C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    |u * a + v * b| ≤ C := by
  rw [abs_le] at ha hb ⊢
  constructor
  · calc
      -C = u * (-C) + v * (-C) := by rw [← add_mul, huv, one_mul]
      _ ≤ u * a + v * b := add_le_add
        (mul_le_mul_of_nonneg_left ha.1 hu)
        (mul_le_mul_of_nonneg_left hb.1 hv)
  · calc
      u * a + v * b ≤ u * C + v * C := add_le_add
        (mul_le_mul_of_nonneg_left ha.2 hu)
        (mul_le_mul_of_nonneg_left hb.2 hv)
      _ = C := by rw [← add_mul, huv, one_mul]

/--
An absolute signed-area bound on all ordered triples from `s` extends to all
ordered triples from `convexHull ℝ s`.

This is the three-variable convexity principle used to replace certificate
checks on interior points by checks on the generating set.
-/
theorem abs_sig_le_on_convexHull (s : Set (ℝ × ℝ)) (C : ℝ)
    (h : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, |sig p q r| ≤ C) :
    ∀ p ∈ convexHull ℝ s, ∀ q ∈ convexHull ℝ s,
      ∀ r ∈ convexHull ℝ s, |sig p q r| ≤ C := by
  apply convexHull_min
  · intro p hp
    apply convexHull_min
    · intro q hq
      apply convexHull_min
      · exact h p hp q hq
      · rintro r₁ hr₁ r₂ hr₂ u v hu hv huv
        change |sig p q r₁| ≤ C at hr₁
        change |sig p q r₂| ≤ C at hr₂
        change |sig p q (u • r₁ + v • r₂)| ≤ C
        rw [sig_affine_third_two p q r₁ r₂ u v huv]
        exact abs_weighted_le hr₁ hr₂ hu hv huv
    · rintro q₁ hq₁ q₂ hq₂ u v hu hv huv
      intro r hr
      have hq₁' := hq₁ r hr
      have hq₂' := hq₂ r hr
      change |sig p q₁ r| ≤ C at hq₁'
      change |sig p q₂ r| ≤ C at hq₂'
      change |sig p (u • q₁ + v • q₂) r| ≤ C
      rw [sig_affine_snd_two p q₁ q₂ r u v huv]
      exact abs_weighted_le hq₁' hq₂' hu hv huv
  · rintro p₁ hp₁ p₂ hp₂ u v hu hv huv
    intro q hq r hr
    have hp₁' := hp₁ q hq r hr
    have hp₂' := hp₂ q hq r hr
    change |sig p₁ q r| ≤ C at hp₁'
    change |sig p₂ q r| ≤ C at hp₂'
    change |sig (u • p₁ + v • p₂) q r| ≤ C
    rw [sig_affine_fst_two p₁ p₂ q r u v huv]
    exact abs_weighted_le hp₁' hp₂' hu hv huv

end Heilbronn8
