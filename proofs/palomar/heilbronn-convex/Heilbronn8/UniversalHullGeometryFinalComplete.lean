import Heilbronn8.UniversalHullGeometryFinalH5CAB
import Heilbronn8.Survivors.Join.HullSixThreeThreeSmallPResidualXFrontier
import Heilbronn8.HullSevenGeometricExclusion

/-!
# Unconditional geometric final theorem

The geometry-only hull-size route is now closed for every size.  Hull sizes
three and eight are discharged by `UniversalHullGeometryFinal`, hull size four
by `GeometricHullFour`, hull size five by the table-free CAB endpoint, hull
size six by the completed direct-frontier endpoint, and hull size seven by its
unconditional cutoff classification.

This leaf deliberately bypasses the production partition, retained-record
corpus, and survivor-root interfaces.  Those conditional routes remain
available as compatibility entry points in their existing modules.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The unconditional eight-point Heilbronn equality obtained from the four
completed geometry-only hull-size exclusions. -/
theorem heilbronn_eight_final_unconditional : h_convex 8 = v8 :=
  heilbronn_eight_final_of_geometricHullSizes_six_seven
    geometricHullSixExclusion_of_completedDirectFrontiers
    geometricHullSevenExclusion

#print axioms heilbronn_eight_final_unconditional

end Heilbronn8
