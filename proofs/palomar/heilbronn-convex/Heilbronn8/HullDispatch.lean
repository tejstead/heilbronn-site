import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Cover

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Heilbronn8

/-!
## Cover-side generated-data contract

This replaces the former direct implication

`Beats H q v → satisfiesAll leaf ...`

with two separately checked obligations:

1. `dispatch` verifies the declared cycle and proves that its exact fan is
   the `H v` appearing in `Beats`;
2. `replay` maps a beat inequality written against that declared fan into the
   stored certificate rows.

Consequently `toFarkasGeneratedData` must rewrite through the hull equality
before it can construct the row hypotheses.
-/

structure HullFarkasGeneratedData
    (H : Configuration → ℝ) (q : ℝ)
    (root : Box) (T : SplitTree)
    (certificates : Nat → CertCheckX.Leaf)
    (hulls : Nat → HullCycleData) : Prop where
  dispatch : ∀ (ref : Nat) (v : Configuration),
    GaugeNormalized v →
    Beats H q v →
    LeafRegion root T
      (xCoordsOf v) (yCoordsOf v) (.farkas ref) →
    ∃ S : StrictSignData v,
      HullCycleOf S (hulls ref) ∧
      H v = (hulls ref).fanExpr v
  replay : ∀ (ref : Nat) (v : Configuration),
    GaugeNormalized v →
    LeafRegion root T
      (xCoordsOf v) (yCoordsOf v) (.farkas ref) →
    ∀ S : StrictSignData v,
      HullCycleOf S (hulls ref) →
      q * (hulls ref).fanExpr v < minTri v →
      CertCheckX.CheckLeafX (certificates ref) = true ∧
        (certificates ref).inXbox (xCoordsOf v) ∧
        CertCheckX.satisfiesAll
          (certificates ref)
          (xCoordsOf v) (yCoordsOf v)

/--
Forget the hull annotation only after the beat threshold has been rewritten
from the actual `H v` to the verified leaf fan.
-/
lemma HullFarkasGeneratedData.toFarkasGeneratedData
    {H : Configuration → ℝ} {q : ℝ}
    {root : Box} {T : SplitTree}
    {certificates : Nat → CertCheckX.Leaf}
    {hulls : Nat → HullCycleData}
    (g : HullFarkasGeneratedData
      H q root T certificates hulls) :
    FarkasGeneratedData H q root T certificates := by
  intro ref v hv hbeat hregion
  obtain ⟨S, hcycle, hH⟩ :=
    g.dispatch ref v hv hbeat hregion
  have hfan :
      q * (hulls ref).fanExpr v < minTri v := by
    rw [← hH]
    exact hbeat.2
  exact g.replay ref v hv hregion S hcycle hfan

/--
The same annotation proves that the `H` consumed by the leaf really is a
doubled hull area according to `IsHullArea`.
-/
lemma HullFarkasGeneratedData.actualHullArea
    {H : Configuration → ℝ} {q : ℝ}
    {root : Box} {T : SplitTree}
    {certificates : Nat → CertCheckX.Leaf}
    {hulls : Nat → HullCycleData}
    (g : HullFarkasGeneratedData
      H q root T certificates hulls)
    (ref : Nat) (v : Configuration)
    (hv : GaugeNormalized v)
    (hbeat : Beats H q v)
    (hregion : LeafRegion root T
      (xCoordsOf v) (yCoordsOf v) (.farkas ref)) :
    IsHullArea v (H v) := by
  obtain ⟨S, hcycle, hH⟩ :=
    g.dispatch ref v hv hbeat hregion
  rw [hH]
  exact hcycle.isHullArea

/-- Final Cover wrapper using hull-annotated Farkas leaves. -/
theorem main_bound_hull_skeleton
    (H : Configuration → ℝ) (q : ℝ)
    (root : Box) (T : SplitTree)
    (certificates : Nat → CertCheckX.Leaf)
    (hulls : Nat → HullCycleData)
    (hRoot : ∀ v : Configuration,
      GaugeNormalized v → root.Mem (xCoordsOf v))
    (generatedFarkas :
      HullFarkasGeneratedData
        H q root T certificates hulls)
    (incumbentNeighborhood :
      IncumbentDischarge H q root T) :
    ∀ v : Configuration,
      GaugeNormalized v → ¬ Beats H q v := by
  exact main_bound_skeleton
    H q root T certificates hRoot
    generatedFarkas.toFarkasGeneratedData
    incumbentNeighborhood

end Heilbronn8
