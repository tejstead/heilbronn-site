import Heilbronn8.Survivors.Join.HullSevenGeometricCutoff
import Heilbronn8.V8

/-! # Semantic closer interface for one pure seven-wheel cutoff type -/

namespace Heilbronn8

/-- Exact geometry-only obligation for one of the eight cutoff keys. -/
def HullSevenCutoffTypeExclusion (orderType : HullSevenType) : Prop :=
  ∀ {v : Configuration} {cycleLabels : Fin 7 → Fin 8}
    {pointLabel : Fin 8},
    (X : StrictHullSevenInterior
      (fun i => v (cycleLabels i)) (v pointLabel)) →
    Function.Injective cycleLabels →
    pointLabel ∉ Set.range cycleLabels →
    0 < minTri v →
    doubledHullArea v = fanSum v cycleLabels →
    (cuts : Fin 7 → Fin 5) →
    (∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val)) →
    hullSevenCutoffOrderType cuts = orderType.key →
    Beats doubledHullArea v8 v → False

end Heilbronn8
