import Heilbronn8.HullSevenGeometricExclusion

/-!
# Equality-aware hull-seven cutoff routing

Scratch source for the phase-two optimizer classification.  The production
hull-seven endpoint deliberately weakens seven rationally separated chambers
to `1 <= v8 * H`.  This file retains the strict inequality and shows that a
non-strict `v8` boundary configuration must be the sharp type-5/C24 chamber.

This file is intentionally outside the frozen Palomar tree until the active
verification run finishes.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

noncomputable section

namespace TriHull

private theorem one_lt_v8_mul_of_twentyFive_halves_le
    {H : ℝ} (hH : (25 : ℝ) / 2 ≤ H) :
    1 < v8 * H := by
  have hv : (2 / 25 : ℝ) < v8 := lt_trans (by norm_num) v8_lb
  have hprod : (2 / 25 : ℝ) * (25 / 2) < v8 * H :=
    mul_lt_mul hv hH (by norm_num) v8_pos.le
  norm_num at hprod ⊢
  exact hprod

private theorem minTri_lt_v8_hullArea_of_normalized
    {v : Configuration} (hm : 0 < minTri v)
    (h : 1 < v8 * (doubledHullArea v / minTri v)) :
    minTri v < v8 * doubledHullArea v := by
  have h' : 1 < (v8 * doubledHullArea v) / minTri v := by
    calc
      1 < v8 * (doubledHullArea v / minTri v) := h
      _ = (v8 * doubledHullArea v) / minTri v := by ring
  simpa using (lt_div_iff₀ hm).1 h'

theorem HullSevenType0PointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType0PointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSevenType0_area_gt_of_chord
    X.toBracketData.toChordInput).le

theorem HullSevenType1PointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType1PointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSevenType1_area_gt_of_chord
    X.toBracketData.toChordInput).le

theorem HullSevenType1MirrorPointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType1MirrorPointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSevenType1_area_gt_of_chord
    X.toBracketData.toChordInput).le

theorem HullSevenType2HyperbolicPointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType2HyperbolicPointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact hullSevenType2HyperbolicPacketCloser_checked X.toHyperbolicPacket

theorem HullSevenType3PointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType3PointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSevenType3_area_gt_of_chord X.toChordInput).le

theorem HullSevenType4PointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType4PointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSeven_type4_area_gt X.toBracketData).le

theorem HullSevenType6PointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType6PointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSeven_type6_raw_reflection_area
    X.toBracketData.toRawReflectionData).le

theorem HullSevenType7PointData.strictly_below_v8
    {v : Configuration} (X : HullSevenType7PointData v) :
    minTri v < v8 * doubledHullArea v := by
  apply minTri_lt_v8_hullArea_of_normalized X.minTri_pos
  apply one_lt_v8_mul_of_twentyFive_halves_le
  exact (hullSeven_type7_area_gt X.toBracketData.toCyclicData).le

end TriHull

private theorem boundary_contradiction
    {v : Configuration}
    (hboundary : v8 * doubledHullArea v ≤ minTri v)
    (hstrict : minTri v < v8 * doubledHullArea v) : False := by
  linarith

/-!
The arguments intentionally match `StrictHullSevenInterior.not_beats_of_cutoffExclusions`.
Unlike that theorem, no `Beats` hypothesis is consumed and the type-5 branch
returns its concrete C24 point packet.
-/
theorem StrictHullSevenInterior.c24_of_v8_boundary
    {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8}
    (X : StrictHullSevenInterior
      (fun i ↦ v (cycleLabels i)) (v pointLabel))
    (hcycleInjective : Function.Injective cycleLabels)
    (hpointOutside : pointLabel ∉ Set.range cycleLabels)
    (hmin : 0 < minTri v)
    (harea : doubledHullArea v = fanSum v cycleLabels)
    (hboundary : v8 * doubledHullArea v ≤ minTri v) :
    Nonempty (TriHull.HullSevenC24PointData v) := by
  obtain ⟨cuts, orderType, _htype, hkey, hcuts⟩ := X.exists_orderType
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  cases orderType with
  | type0 =>
      obtain ⟨rotation, hpreferred⟩ :=
        hullSevenCutoff_type0_preferred_of_complementary cuts hcomp hkey
      have P := X.toType0PointData hcycleInjective hpointOutside hmin harea
        cuts hcuts rotation hpreferred
      exact (boundary_contradiction hboundary P.strictly_below_v8).elim
  | type1 =>
      rcases X.existsType1DirectOrMirrorPointData hcycleInjective
          hpointOutside hmin harea cuts hcuts hkey with hdirect | hmirror
      · rcases hdirect with ⟨P⟩
        exact (boundary_contradiction hboundary P.strictly_below_v8).elim
      · rcases hmirror with ⟨P⟩
        exact (boundary_contradiction hboundary P.strictly_below_v8).elim
  | type2 =>
      obtain ⟨rotation, hpreferred⟩ :=
        hullSevenCutoff_type2_hyperbolic_preferred_of_complementary
          cuts hcomp hkey
      have P := X.toType2HyperbolicPointData hcycleInjective hpointOutside
        hmin harea cuts hcuts rotation hpreferred
      exact (boundary_contradiction hboundary P.strictly_below_v8).elim
  | type3 =>
      obtain ⟨rotation, hpreferred⟩ :=
        hullSevenCutoff_type3_preferred_of_complementary cuts hcomp hkey
      have P := X.toType3PointData hcycleInjective hpointOutside hmin harea
        cuts hcuts rotation hpreferred
      exact (boundary_contradiction hboundary P.strictly_below_v8).elim
  | type4 =>
      obtain ⟨rotation, hpreferred⟩ :=
        hullSevenCutoff_type4_preferred_of_complementary cuts hcomp hkey
      have P := X.toType4PointData hcycleInjective hpointOutside hmin harea
        cuts hcuts rotation hpreferred
      exact (boundary_contradiction hboundary P.strictly_below_v8).elim
  | type5 =>
      obtain ⟨rotation, hpreferred⟩ :=
        hullSevenCutoff_type5_preferred_of_complementary cuts hcomp hkey
      exact ⟨X.toType5PointData hcycleInjective hpointOutside hmin harea
        cuts hcuts rotation hpreferred⟩
  | type6 =>
      obtain ⟨rotation, hpreferred⟩ :=
        hullSevenCutoff_type6_preferred_of_complementary cuts hcomp hkey
      have P := X.toType6PointData hcycleInjective hpointOutside hmin harea
        cuts hcuts rotation hpreferred
      exact (boundary_contradiction hboundary P.strictly_below_v8).elim
  | type7 =>
      have hall :=
        hullSevenCutoff_type7_all_three_of_complementary cuts hcomp hkey
      have P := X.toType7PointData hcycleInjective hpointOutside hmin harea
        cuts hcuts hall
      exact (boundary_contradiction hboundary P.strictly_below_v8).elim

end

end Heilbronn8
