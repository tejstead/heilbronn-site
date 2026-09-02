/-
Coordinate-level definitions for the convex Heilbronn n = 5 theorem.

Everything is phrased through the doubled signed area
  sig p q r = det (q - p, r - p),
the minimum of the ten |sig| values, and case-wise shoelace hull areas.
-/
import Mathlib

namespace Heilbronn5

/-- Doubled signed area of the triangle `p q r` (the 2x2 determinant). -/
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

lemma sig_rotate (p q r : ℝ × ℝ) : sig p q r = sig q r p := by
  simp only [sig]; ring

lemma sig_swap (p q r : ℝ × ℝ) : sig p q r = -sig p r q := by
  simp only [sig]; ring

/-- `sig` is affine in its first argument: evaluating at a convex/affine
combination expands linearly. Stated for a 3-term combination. -/
lemma sig_affine_fst (a b c q r : ℝ × ℝ) (x y z : ℝ) (hxyz : x + y + z = 1) :
    sig (x • a + y • b + z • c) q r
      = x * sig a q r + y * sig b q r + z * sig c q r := by
  have hz : z = 1 - x - y := by linarith
  subst hz
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  ring

/-- Doubled minimal triangle area: the minimum of |sig| over the ten
unordered triples, written as an explicit min-chain over a canonical
ordered list. -/
noncomputable def minTri (v : Fin 5 → ℝ × ℝ) : ℝ :=
  min (min (min (|sig (v 0) (v 1) (v 2)|) (|sig (v 0) (v 1) (v 3)|))
    (min (|sig (v 0) (v 1) (v 4)|) (|sig (v 0) (v 2) (v 3)|)))
    (min (min (min (|sig (v 0) (v 2) (v 4)|) (|sig (v 0) (v 3) (v 4)|))
      (min (|sig (v 1) (v 2) (v 3)|) (|sig (v 1) (v 2) (v 4)|)))
      (min (|sig (v 1) (v 3) (v 4)|) (|sig (v 2) (v 3) (v 4)|)))

lemma minTri_nonneg (v : Fin 5 → ℝ × ℝ) : 0 ≤ minTri v := by
  unfold minTri
  positivity

lemma minTri_le_012 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 0) (v 1) (v 2)| := by
  unfold minTri
  exact le_trans (min_le_left _ _) (by
    exact le_trans (min_le_left _ _) (min_le_left _ _))

lemma minTri_le_013 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 0) (v 1) (v 3)| := by
  unfold minTri
  exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))

lemma minTri_le_014 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 0) (v 1) (v 4)| := by
  unfold minTri
  exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

lemma minTri_le_023 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 0) (v 2) (v 3)| := by
  unfold minTri
  exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

lemma minTri_le_024 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 0) (v 2) (v 4)| := by
  unfold minTri
  exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))

lemma minTri_le_034 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 0) (v 3) (v 4)| := by
  unfold minTri
  exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))

lemma minTri_le_123 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 1) (v 2) (v 3)| := by
  unfold minTri
  exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))

lemma minTri_le_124 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 1) (v 2) (v 4)| := by
  unfold minTri
  exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))

lemma minTri_le_134 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 1) (v 3) (v 4)| := by
  unfold minTri
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

lemma minTri_le_234 (v : Fin 5 → ℝ × ℝ) : minTri v ≤ |sig (v 2) (v 3) (v 4)| := by
  unfold minTri
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

/-- Convex position with counterclockwise labeling: all ten canonical
triples positively oriented (weak form allows boundary degeneracies). -/
def ConvexPos (v : Fin 5 → ℝ × ℝ) : Prop :=
  0 ≤ sig (v 0) (v 1) (v 2) ∧ 0 ≤ sig (v 0) (v 1) (v 3) ∧
  0 ≤ sig (v 0) (v 1) (v 4) ∧ 0 ≤ sig (v 0) (v 2) (v 3) ∧
  0 ≤ sig (v 0) (v 2) (v 4) ∧ 0 ≤ sig (v 0) (v 3) (v 4) ∧
  0 ≤ sig (v 1) (v 2) (v 3) ∧ 0 ≤ sig (v 1) (v 2) (v 4) ∧
  0 ≤ sig (v 1) (v 3) (v 4) ∧ 0 ≤ sig (v 2) (v 3) (v 4)

/-- Doubled shoelace area of the pentagon `v0 ... v4` (fan from `v0`). -/
def penArea (v : Fin 5 → ℝ × ℝ) : ℝ :=
  sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) + sig (v 0) (v 3) (v 4)

/-- Doubled shoelace area of the quadrilateral `v0 v1 v2 v3`. -/
def quadArea (v : Fin 5 → ℝ × ℝ) : ℝ :=
  sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)

/-- CCW convex position for the first four points (weak form). -/
def QuadPos (v : Fin 5 → ℝ × ℝ) : Prop :=
  0 ≤ sig (v 0) (v 1) (v 2) ∧ 0 ≤ sig (v 0) (v 1) (v 3) ∧
  0 ≤ sig (v 0) (v 2) (v 3) ∧ 0 ≤ sig (v 1) (v 2) (v 3)

/-- Membership in the convex hull of three points, coordinate form. -/
def InTri (p a b c : ℝ × ℝ) : Prop :=
  ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 1 ∧
    p = x • a + y • b + z • c

/-- The golden reference pentagon `(0,0), (1,0), (φ,1), (1,φ), (0,1)`;
an affine image of the regular pentagon (verified in verify.py and in
`Basic.lean`), used as the canonical affinely regular pentagon. -/
noncomputable def golden : Fin 5 → ℝ × ℝ :=
  ![((0 : ℝ), (0 : ℝ)), (1, 0), ((1 + Real.sqrt 5) / 2, 1),
    (1, (1 + Real.sqrt 5) / 2), (0, 1)]

/-- `v` is an affinely regular pentagon: an invertible affine image of the
golden pentagon, up to relabeling. -/
def IsAffineRegular (v : Fin 5 → ℝ × ℝ) : Prop :=
  ∃ (ρ : Equiv.Perm (Fin 5)) (a b c d e f : ℝ),
    a * d - b * c ≠ 0 ∧
    ∀ i, v (ρ i) = (a * (golden i).1 + b * (golden i).2 + e,
                    c * (golden i).1 + d * (golden i).2 + f)

end Heilbronn5
