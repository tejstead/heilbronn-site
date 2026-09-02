import Heilbronn8.GeometricHullFour
import Heilbronn8.UniversalHullGeometryFinal

/-!
# Direct final theorem with hull size four discharged

The compact geometric hull-four theorem is unconditional on this route, so
only hull sizes five through seven remain as hypotheses.
-/

namespace Heilbronn8

/-- Final equality from the three remaining geometric hull-size exclusions. -/
theorem heilbronn_eight_final_of_geometricHullSizes_five_six_seven
    (h5 : GeometricHullSizeExclusion 5 StrictXOrder)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) :
    h_convex 8 = v8 :=
  heilbronn_eight_final_of_geometricHullSizes
    geometricHullFourStrictXOrderExclusion h5 h6 h7

#print axioms heilbronn_eight_final_of_geometricHullSizes_five_six_seven

end Heilbronn8
