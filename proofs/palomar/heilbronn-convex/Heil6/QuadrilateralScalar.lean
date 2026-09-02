import Mathlib

set_option linter.style.header false

/-!
# Equality obstruction for the split-diagonal quadrilateral case

When the two interior points lie on opposite sides of a hull diagonal,
equality in the counting bound makes them the centroids of the two triangular
halves.  Three remaining triangle floors then contradict one another.  This
module packages that calculation independently of the hull-case adapter.
-/

namespace N6Scratch
namespace QuadrilateralScalar

def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

noncomputable def centroid (p q r : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + q.1 + r.1) / 3, (p.2 + q.2 + r.2) / 3)

private theorem area_APQ
    (A B C D : ℝ × ℝ) :
    9 * sig A (centroid A B C) (centroid A C D) =
      sig A B C + sig A B D + sig A C D := by
  simp only [sig, centroid]
  ring

private theorem area_PCQ
    (A B C D : ℝ × ℝ) :
    9 * sig (centroid A B C) C (centroid A C D) =
      2 * sig A B C + 2 * sig A C D - sig A B D := by
  simp only [sig, centroid]
  ring

private theorem area_BPQ
    (A B C D : ℝ × ℝ) :
    9 * sig B (centroid A B C) (centroid A C D) =
      sig A B C + sig A C D - 2 * sig A B D := by
  simp only [sig, centroid]
  ring

/-- Two centroidal points in opposite diagonal halves cannot coexist with all
triangle areas at least `m` when both halves have area `3m`. -/
theorem opposite_centroids_impossible
    (A B C D : ℝ × ℝ) (m : ℝ)
    (hm : 0 < m)
    (hABC : sig A B C = 3 * m)
    (hACD : sig A C D = 3 * m)
    (hAPQ : m ≤ sig A (centroid A B C) (centroid A C D))
    (hPCQ : m ≤ sig (centroid A B C) C (centroid A C D))
    (hBPQ : m ≤ |sig B (centroid A B C) (centroid A C D)|) :
    False := by
  have h1 := area_APQ A B C D
  have h2 := area_PCQ A B C D
  have h3 := area_BPQ A B C D
  have hABD : sig A B D = 3 * m := by
    nlinarith
  have hzero : sig B (centroid A B C) (centroid A C D) = 0 := by
    nlinarith
  rw [hzero, abs_zero] at hBPQ
  linarith

/-- Scalar endpoint for the case in which both interior points lie in the
same diagonal half.  Equality in a five-cell refinement of the containing
triangle gives the displayed barycentric-area data.  The two `PQ` faces force
`pA = pB = 2m`, after which the third `PQ` triangle has zero area. -/
theorem same_side_barycentric_impossible
    (m t pA pB pC qA qB qC CPQ : ℝ)
    (hm : 0 < m)
    (ht : t = 5 * m)
    (_hpSum : pA + pB + pC = t)
    (hqSum : qA + qB + qC = t)
    (hpC : pC = m) (hqA : qA = m) (hqB : qB = m)
    (hAPQ : t * m = pB * qC - pC * qB)
    (hBPQ : t * m = pA * qC - pC * qA)
    (hCPQ : t * CPQ = pA * qB - pB * qA)
    (hCPQFloor : m ≤ |CPQ|) :
    False := by
  have hqC : qC = 3 * m := by linarith
  rw [ht, hpC, hqB, hqC] at hAPQ
  rw [ht, hpC, hqA, hqC] at hBPQ
  rw [ht, hqA, hqB] at hCPQ
  have hpB : pB = 2 * m := by
    have hz : (pB - 2 * m) * m = 0 := by nlinarith [hAPQ]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith
    · exact False.elim ((ne_of_gt hm) hz)
  have hpA : pA = 2 * m := by
    have hz : (pA - 2 * m) * m = 0 := by nlinarith [hBPQ]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith
    · exact False.elim ((ne_of_gt hm) hz)
  rw [hpA, hpB] at hCPQ
  have hzero : CPQ = 0 := by
    have hz : m * CPQ = 0 := by nlinarith [hCPQ]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact False.elim ((ne_of_gt hm) hz)
    · exact hz
  rw [hzero, abs_zero] at hCPQFloor
  linarith

end QuadrilateralScalar
end N6Scratch
