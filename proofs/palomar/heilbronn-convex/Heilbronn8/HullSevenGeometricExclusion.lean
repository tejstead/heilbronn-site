import Heilbronn8.GeometricHullExclusionCore
import Heilbronn8.HullSevenCutoffExclusionCore
import Heilbronn8.OrderDensity
import Heilbronn8.PolyVolumeGen
import Heilbronn8.Survivors.Join.HullSevenType0UniversalAdapter
import Heilbronn8.Survivors.Join.HullSevenType1UniversalAdapter
import Heilbronn8.Survivors.Join.HullSevenType2HyperbolicFinal
import Heilbronn8.Survivors.Join.HullSevenType3UniversalAdapter
import Heilbronn8.Survivors.Join.HullSevenType4UniversalAdapter
import Heilbronn8.Survivors.Join.HullSevenType5UniversalAdapter
import Heilbronn8.Survivors.Join.HullSevenType6UniversalAdapter
import Heilbronn8.Survivors.Join.HullSevenType7UniversalAdapter

/-!
# Direct geometry-only hull-seven exclusion

A genuine seven-cycle produces one strict radial cutoff packet.  The reduced
classifier assigns one of the eight pure `HullSevenType` keys, and a
type-specific closer contradicts `Beats`.  The entire interface is geometric:
there is no survivor word, retained record, production custody, class tag, or
registry.
-/

namespace Heilbronn8

noncomputable section

/-- One direct geometric closer for each universal seven-wheel type. -/
structure HullSevenCutoffExclusions : Prop where
  type0 : HullSevenCutoffTypeExclusion .type0
  type1 : HullSevenCutoffTypeExclusion .type1
  type2 : HullSevenCutoffTypeExclusion .type2
  type3 : HullSevenCutoffTypeExclusion .type3
  type4 : HullSevenCutoffTypeExclusion .type4
  type5 : HullSevenCutoffTypeExclusion .type5
  type6 : HullSevenCutoffTypeExclusion .type6
  type7 : HullSevenCutoffTypeExclusion .type7

/-- Type 0 is already closed from its preferred direct rotation. -/
theorem hullSevenCutoffType0Exclusion :
    HullSevenCutoffTypeExclusion .type0 := by
  intro v cycleLabels pointLabel X hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat
  have hcomp : HullSevenCutoffComplementary cuts :=
    X.cutoffs_complementary cuts hcuts
  obtain ⟨rotation, hpreferred⟩ :=
    hullSevenCutoff_type0_preferred_of_complementary cuts hcomp hkey
  exact (X.toType0PointData hcycleInjective hpointOutside hmin harea
    cuts hcuts rotation hpreferred).not_beats hbeat

/-- Type 1 is already closed in both chiral orientations. -/
theorem hullSevenCutoffType1Exclusion :
    HullSevenCutoffTypeExclusion .type1 := by
  intro v cycleLabels pointLabel X hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat
  exact X.not_beats_of_type1_cutoff hcycleInjective hpointOutside hmin
    harea cuts hcuts hkey hbeat

/-- Type 2 is closed by the honest hyperbolic product-ear theorem and its
small ordinary-kernel two-variable interval check. -/
theorem hullSevenCutoffType2Exclusion :
    HullSevenCutoffTypeExclusion .type2 :=
  hullSevenCutoffType2HyperbolicExclusion
    hullSevenType2HyperbolicPacketCloser_checked

/-- Compatibility interface allowing an alternate type-2 closer to be
installed into the otherwise complete direct cutoff table. -/
structure HullSevenMiddleCutoffExclusions : Prop where
  type2 : HullSevenCutoffTypeExclusion .type2

/-- Install the honest type-2 hyperbolic packet closer into the last open
slot of the direct hull-seven cutoff table. -/
def HullSevenMiddleCutoffExclusions.ofType2HyperbolicPacketCloser
    (closer : HullSevenType2HyperbolicPacketCloser) :
    HullSevenMiddleCutoffExclusions where
  type2 := hullSevenCutoffType2HyperbolicExclusion closer

def HullSevenMiddleCutoffExclusions.toAll
    (middle : HullSevenMiddleCutoffExclusions) :
    HullSevenCutoffExclusions where
  type0 := hullSevenCutoffType0Exclusion
  type1 := hullSevenCutoffType1Exclusion
  type2 := middle.type2
  type3 := hullSevenCutoffType3Exclusion
  type4 := hullSevenCutoffType4Exclusion
  type5 := hullSevenCutoffType5Exclusion
  type6 := hullSevenCutoffType6Exclusion
  type7 := hullSevenCutoffType7Exclusion

/-- Dispatch a classified strict wheel through the exact eight closer table. -/
theorem StrictHullSevenInterior.not_beats_of_cutoffExclusions
    {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8}
    (X : StrictHullSevenInterior
      (fun i => v (cycleLabels i)) (v pointLabel))
    (closers : HullSevenCutoffExclusions)
    (hcycleInjective : Function.Injective cycleLabels)
    (hpointOutside : pointLabel ∉ Set.range cycleLabels)
    (hmin : 0 < minTri v)
    (harea : doubledHullArea v = fanSum v cycleLabels)
    (hbeat : Beats doubledHullArea v8 v) : False := by
  obtain ⟨cuts, orderType, _htype, hkey, hcuts⟩ := X.exists_orderType
  cases orderType with
  | type0 =>
      exact closers.type0 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type1 =>
      exact closers.type1 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type2 =>
      exact closers.type2 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type3 =>
      exact closers.type3 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type4 =>
      exact closers.type4 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type5 =>
      exact closers.type5 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type6 =>
      exact closers.type6 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat
  | type7 =>
      exact closers.type7 X hcycleInjective hpointOutside hmin harea
        cuts hcuts hkey hbeat

/-- The direct final hull-seven theorem.  Once the eight compact cutoff
closers are supplied, no production or retained-corpus layer remains. -/
theorem geometricHullSevenExclusion_of_cutoffExclusions
    (closers : HullSevenCutoffExclusions) :
    GeometricHullSizeExclusion 7 StrictXOrder := by
  intro v custody _hdomain _hstrict h7 hbeat
  have hmin : 0 < minTri v :=
    lt_trans (mul_pos v8_pos hbeat.1) hbeat.2
  obtain ⟨pointLabel, hpointOutside, X⟩ :=
    exists_strictHullSevenInterior_geometric custody.hull h7 hmin
  have hcycleInjective :
      Function.Injective (custody.data.castGet h7) :=
    HullCycleData.castGet_injective custody.data h7 custody.hull.nodup
  have harea :
      doubledHullArea v = fanSum v (custody.data.castGet h7) := by
    calc
      doubledHullArea v = custody.data.fanExpr v :=
        doubledHullArea_eq_of_isHullArea custody.hull.isHullArea
      _ = fanSum v (custody.data.castGet h7) :=
        (HullCycleData.fanSum_castGet custody.data h7).symm
  exact X.not_beats_of_cutoffExclusions closers hcycleInjective
    hpointOutside hmin harea hbeat

/-- Compatibility seam for supplying an alternate type-2 cutoff closer. -/
theorem geometricHullSevenExclusion_of_middleCutoffExclusions
    (middle : HullSevenMiddleCutoffExclusions) :
    GeometricHullSizeExclusion 7 StrictXOrder :=
  geometricHullSevenExclusion_of_cutoffExclusions middle.toAll

/-- Direct geometry-only hull-seven exclusion, conditional on exactly the
honest type-2 scalar packet bound.  The compact product-ear theorem discharges
this final scalar input. -/
theorem geometricHullSevenExclusion_of_type2HyperbolicPacketCloser
    (closer : HullSevenType2HyperbolicPacketCloser) :
    GeometricHullSizeExclusion 7 StrictXOrder :=
  geometricHullSevenExclusion_of_middleCutoffExclusions
    (.ofType2HyperbolicPacketCloser closer)

/-- Unconditional, geometry-only hull-seven exclusion.  All eight universal
seven-wheel types are installed internally; there is no retained-corpus or
production-certificate hypothesis. -/
theorem geometricHullSevenExclusion :
    GeometricHullSizeExclusion 7 StrictXOrder :=
  geometricHullSevenExclusion_of_type2HyperbolicPacketCloser
    hullSevenType2HyperbolicPacketCloser_checked

end

end Heilbronn8
