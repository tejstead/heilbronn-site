import Heilbronn8.QuadHull.OrbitICoarseNormalization

/-!
# Exhaustive coarse orbit-I classifier

The pointwise geometric trichotomy has only `3^3 = 27` ordered leaves.
This module converts those leaves to the nine count-based scalar rows, with
the all-`delta` leaf retained as the existing common orbit-I certificate.
No generated sign corpus is involved.
-/

namespace Heilbronn8.QuadHull

/-- The finite ordered fan assignment is either one of the nine direct count
rows or the unique all-`delta` residual. -/
theorem OrbitISideFanAssignment.dispatch
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitISideMinimalGeometryCertificate v A B C D}
    (a : OrbitISideFanAssignment h) (hm : 0 < minTri v) :
    OrbitICoarseDirectBounds (h.coarseFan hm) ∨
      ∀ i : Fin 3, a.cell i = .delta := by
  let f := h.coarseFan hm
  have oneAlpha (i : Fin 3) (hi : a.cell i = .alpha) :
      3 ≤ f.alpha := by
    simpa only [f, h.coarseFan_alpha,
      OrbitISideFanCell.normalizedArea] using
      a.onePointFloor hm hi
  have oneGamma (i : Fin 3) (hi : a.cell i = .gamma) :
      3 ≤ f.gamma := by
    simpa only [f, h.coarseFan_gamma,
      OrbitISideFanCell.normalizedArea] using
      a.onePointFloor hm hi
  have oneDelta (i : Fin 3) (hi : a.cell i = .delta) :
      3 ≤ f.delta := by
    simpa only [f, h.coarseFan_delta,
      OrbitISideFanCell.normalizedArea] using
      a.onePointFloor hm hi
  have twoAlpha (i j : Fin 3) (hij : i ≠ j)
      (hi : a.cell i = .alpha) (hj : a.cell j = .alpha) :
      (149 : ℝ) / 20 < f.alpha := by
    simpa only [f, h.coarseFan_alpha,
      OrbitISideFanCell.normalizedArea] using
      a.twoPointFloor hm hij hi hj
  have twoGamma (i j : Fin 3) (hij : i ≠ j)
      (hi : a.cell i = .gamma) (hj : a.cell j = .gamma) :
      (149 : ℝ) / 20 < f.gamma := by
    simpa only [f, h.coarseFan_gamma,
      OrbitISideFanCell.normalizedArea] using
      a.twoPointFloor hm hij hi hj
  have twoDelta (i j : Fin 3) (hij : i ≠ j)
      (hi : a.cell i = .delta) (hj : a.cell j = .delta) :
      (149 : ℝ) / 20 < f.delta := by
    simpa only [f, h.coarseFan_delta,
      OrbitISideFanCell.normalizedArea] using
      a.twoPointFloor hm hij hi hj
  have threeAlpha
      (h0 : a.cell 0 = .alpha) (h1 : a.cell 1 = .alpha)
      (h2 : a.cell 2 = .alpha) :
      (17 : ℝ) / 2 ≤ f.alpha := by
    simpa only [f, h.coarseFan_alpha,
      OrbitISideFanCell.normalizedArea] using
      a.threePointFloor hm h0 h1 h2
  have threeGamma
      (h0 : a.cell 0 = .gamma) (h1 : a.cell 1 = .gamma)
      (h2 : a.cell 2 = .gamma) :
      (17 : ℝ) / 2 ≤ f.gamma := by
    simpa only [f, h.coarseFan_gamma,
      OrbitISideFanCell.normalizedArea] using
      a.threePointFloor hm h0 h1 h2
  generalize hc0 : a.cell 0 = c0
  generalize hc1 : a.cell 1 = c1
  generalize hc2 : a.cell 2 = c2
  cases c0 with
  | alpha =>
      cases c1 with
      | alpha =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c300 (threeAlpha hc0 hc1 hc2))
          | gamma =>
              exact Or.inl (.c210
                (twoAlpha 0 1 (by decide) hc0 hc1)
                (oneGamma 2 hc2))
          | delta =>
              exact Or.inl (.c201
                (twoAlpha 0 1 (by decide) hc0 hc1)
                (oneDelta 2 hc2))
      | gamma =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c210
                (twoAlpha 0 2 (by decide) hc0 hc2)
                (oneGamma 1 hc1))
          | gamma =>
              exact Or.inl (.c120
                (oneAlpha 0 hc0)
                (twoGamma 1 2 (by decide) hc1 hc2))
          | delta =>
              exact Or.inl (.c111
                (oneAlpha 0 hc0) (oneGamma 1 hc1)
                (oneDelta 2 hc2))
      | delta =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c201
                (twoAlpha 0 2 (by decide) hc0 hc2)
                (oneDelta 1 hc1))
          | gamma =>
              exact Or.inl (.c111
                (oneAlpha 0 hc0) (oneGamma 2 hc2)
                (oneDelta 1 hc1))
          | delta =>
              exact Or.inl (.c102
                (oneAlpha 0 hc0)
                (twoDelta 1 2 (by decide) hc1 hc2))
  | gamma =>
      cases c1 with
      | alpha =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c210
                (twoAlpha 1 2 (by decide) hc1 hc2)
                (oneGamma 0 hc0))
          | gamma =>
              exact Or.inl (.c120
                (oneAlpha 1 hc1)
                (twoGamma 0 2 (by decide) hc0 hc2))
          | delta =>
              exact Or.inl (.c111
                (oneAlpha 1 hc1) (oneGamma 0 hc0)
                (oneDelta 2 hc2))
      | gamma =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c120
                (oneAlpha 2 hc2)
                (twoGamma 0 1 (by decide) hc0 hc1))
          | gamma =>
              exact Or.inl (.c030 (threeGamma hc0 hc1 hc2))
          | delta =>
              exact Or.inl (.c021
                (twoGamma 0 1 (by decide) hc0 hc1)
                (oneDelta 2 hc2))
      | delta =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c111
                (oneAlpha 2 hc2) (oneGamma 0 hc0)
                (oneDelta 1 hc1))
          | gamma =>
              exact Or.inl (.c021
                (twoGamma 0 2 (by decide) hc0 hc2)
                (oneDelta 1 hc1))
          | delta =>
              exact Or.inl (.c012
                (oneGamma 0 hc0)
                (twoDelta 1 2 (by decide) hc1 hc2))
  | delta =>
      cases c1 with
      | alpha =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c201
                (twoAlpha 1 2 (by decide) hc1 hc2)
                (oneDelta 0 hc0))
          | gamma =>
              exact Or.inl (.c111
                (oneAlpha 1 hc1) (oneGamma 2 hc2)
                (oneDelta 0 hc0))
          | delta =>
              exact Or.inl (.c102
                (oneAlpha 1 hc1)
                (twoDelta 0 2 (by decide) hc0 hc2))
      | gamma =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c111
                (oneAlpha 2 hc2) (oneGamma 1 hc1)
                (oneDelta 0 hc0))
          | gamma =>
              exact Or.inl (.c021
                (twoGamma 1 2 (by decide) hc1 hc2)
                (oneDelta 0 hc0))
          | delta =>
              exact Or.inl (.c012
                (oneGamma 1 hc1)
                (twoDelta 0 2 (by decide) hc0 hc2))
      | delta =>
          cases c2 with
          | alpha =>
              exact Or.inl (.c102
                (oneAlpha 2 hc2)
                (twoDelta 0 1 (by decide) hc0 hc1))
          | gamma =>
              exact Or.inl (.c012
                (oneGamma 2 hc2)
                (twoDelta 0 1 (by decide) hc0 hc1))
          | delta =>
              apply Or.inr
              intro i
              fin_cases i
              · exact hc0
              · exact hc1
              · exact hc2

/-- Positive-minimum coarse orbit I closes either directly or through the
existing repaired common-geometry backend. -/
theorem OrbitICoarseGeometryCertificate.classifyPositive
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D)
    (hm : 0 < minTri v) : OrbitIClassificationOutcome v A B C D := by
  let s := h.sideMinimal
  let a := s.fanAssignment hm.ne'
  rcases a.dispatch hm with hdirect | hdelta
  · apply Or.inl
    unfold DirectHullFourBound
    have hK := hdirect.bound
    have hscale := orbitINormalizedHull_scale v A B C D hm.ne'
    rw [hscale]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hK (by linarith : 0 ≤ minTri v / 2))
  · exact Or.inr ⟨a.commonOfAllDelta hdelta⟩

end Heilbronn8.QuadHull
