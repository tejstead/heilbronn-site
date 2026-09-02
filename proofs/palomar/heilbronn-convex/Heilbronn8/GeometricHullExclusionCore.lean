import Heilbronn8.HullCycleCertificateExistence
import Heilbronn8.ReferenceQuotient
import Heilbronn8.V8

/-!
# Geometry-only hull exclusion interface

This is the small common interface between canonical convex-hull custody and
the size-specific geometric closers.  It deliberately contains no survivor
word, corpus record, production route, or registry.
-/

namespace Heilbronn8

/-- A geometry-only hull packet. -/
structure GeometricHullCustody (v : Configuration) where
  signs : StrictSignData v
  data : HullCycleData
  hull : HullCycleOf signs data

/-- Semantic exclusion for one actual geometric hull size. -/
def GeometricHullSizeExclusion
    (size : Nat) (extra : Configuration → Prop) : Prop :=
  ∀ {v : Configuration} (custody : GeometricHullCustody v),
    ReferenceMachineDomain v → extra v →
      custody.data.cycle.length = size →
        Beats doubledHullArea v8 v → False

/-- A beating configuration is in strict general position and therefore has
a canonical geometry-only hull packet. -/
theorem geometricHullCustody_exists_of_Beats
    {v : Configuration} (hbeat : Beats doubledHullArea v8 v) :
    Nonempty (GeometricHullCustody v) := by
  have hmin : 0 < minTri v :=
    lt_trans (mul_pos v8_pos hbeat.1) hbeat.2
  obtain ⟨data, hull⟩ := exists_hullCycleOf_of_minTri_pos v hmin
  exact ⟨
    { signs := StrictSignData.ofAllTripleSignsStrict v
        (allTripleSignsStrict_of_minTri_pos v hmin)
      data := data
      hull := hull }⟩

end Heilbronn8
