import Solution.N8
import Solution.AffineDefs
import Heilbronn8.Gauge
import Heilbronn8.HullBoundaryRouterConcrete

/-!
# Thin Palomar wrapper for the internal n=8 boundary classification

Phase-two scratch source.  This module deliberately abstracts over the
internal classification theorem, so it can be reviewed independently of the
hull-size refactors.  It also avoids identifying the challenge's choice-based
`witness8` with a particular hard-coded witness: both chosen witness and the
arbitrary attainer are fed to the pairwise boundary theorem.
-/

set_option relaxedAutoImplicit false

namespace HeilbronnChallenge

noncomputable section

/-- Exact raw interface exported by `HullBoundaryRouter`: any two positive
`v8`-boundary configurations differ by relabeling and a positive affine map.
-/
def InternalN8PairwiseBoundaryUnique : Prop :=
  ∀ {v u : Heilbronn8.Configuration},
    0 < Heilbronn8.doubledHullArea v →
    0 < Heilbronn8.doubledHullArea u →
    Heilbronn8.v8 * Heilbronn8.doubledHullArea v ≤
      Heilbronn8.minTri v →
    Heilbronn8.v8 * Heilbronn8.doubledHullArea u ≤
      Heilbronn8.minTri u →
    ∃ (sigma : Equiv.Perm (Fin 8)) (T : Heilbronn8.PosAffine),
      u = fun i ↦ T.map (v (sigma i))

theorem internalN8PairwiseBoundaryUnique_proved :
    InternalN8PairwiseBoundaryUnique := by
  intro v u hvArea huArea hvBoundary huBoundary
  exact Heilbronn8.pairwise_gauge_unique_of_v8_boundary_unconditional
    hvArea huArea hvBoundary huBoundary

noncomputable def witness8 : Fin 8 → ℝ × ℝ :=
  heilbronn_convex_eight_attained.choose

/-- Any two normalized optimizers are gauge equivalent.  This is the direct
pairwise public form of the internal boundary classification; no chosen
witness or transitivity argument is involved. -/
theorem heilbronn_convex_eight_pairwise_unique_of_internalBoundary
    (unique : InternalN8PairwiseBoundaryUnique)
    (p q : Fin 8 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v8)
    (hqopt : minTri q = 2 * v8) :
    GaugeEquivalent p q := by
  have hpArea : Heilbronn8.doubledHullArea p = 2 :=
    Heilbronn8.doubledHullArea_eq_two_of_volume_one hpvol
  have hqArea : Heilbronn8.doubledHullArea q = 2 :=
    Heilbronn8.doubledHullArea_eq_two_of_volume_one hqvol
  have hpMin : Heilbronn8.minTri p = 2 * Heilbronn8.v8 := by
    calc
      Heilbronn8.minTri p = minTri p := minTri_eq_eight p
      _ = 2 * v8 := hpopt
      _ = 2 * Heilbronn8.v8 := by rw [v8_eq_eight]
  have hqMin : Heilbronn8.minTri q = 2 * Heilbronn8.v8 := by
    calc
      Heilbronn8.minTri q = minTri q := minTri_eq_eight q
      _ = 2 * v8 := hqopt
      _ = 2 * Heilbronn8.v8 := by rw [v8_eq_eight]
  have hpAreaPos : 0 < Heilbronn8.doubledHullArea p := by
    rw [hpArea]
    norm_num
  have hqAreaPos : 0 < Heilbronn8.doubledHullArea q := by
    rw [hqArea]
    norm_num
  have hpBoundary :
      Heilbronn8.v8 * Heilbronn8.doubledHullArea p ≤
        Heilbronn8.minTri p := by
    rw [hpArea, hpMin]
    nlinarith
  have hqBoundary :
      Heilbronn8.v8 * Heilbronn8.doubledHullArea q ≤
        Heilbronn8.minTri q := by
    rw [hqArea, hqMin]
    nlinarith
  obtain ⟨sigma, T, hT⟩ :=
    unique hpAreaPos hqAreaPos hpBoundary hqBoundary
  let T' : PosAffine :=
    { a := T.a
      b := T.b
      c := T.c
      d := T.d
      tx := T.e
      ty := T.f
      det_pos := T.det_pos }
  refine ⟨sigma, T', ?_⟩
  simpa [T', PosAffine.map, Heilbronn8.PosAffine.map] using hT

/-- Exact phase-two target: arbitrary normalized optimizers are equivalent by
relabeling and a nonsingular affine map.  The internal theorem is stronger:
its affine map has positive determinant. -/
theorem heilbronn_convex_eight_unique
    (p q : Fin 8 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v8)
    (hqopt : minTri q = 2 * v8) :
    AffineEquivalent p q := by
  apply affineEquivalent_of_gaugeEquivalent
  exact heilbronn_convex_eight_pairwise_unique_of_internalBoundary
    internalN8PairwiseBoundaryUnique_proved
    p q hpvol hqvol hpopt hqopt

/-- The challenge's chosen-witness spelling is an immediate specialization of
the direct pairwise theorem. -/
theorem heilbronn_convex_eight_unique_of_internalBoundary
    (unique : InternalN8PairwiseBoundaryUnique)
    (p : Fin 8 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hatt : minTri p = 2 * v8) :
    GaugeEquivalent witness8 p := by
  have hwSpec := heilbronn_convex_eight_attained.choose_spec
  exact heilbronn_convex_eight_pairwise_unique_of_internalBoundary unique
    witness8 p hwSpec.1 hvol hwSpec.2 hatt

end

end HeilbronnChallenge
