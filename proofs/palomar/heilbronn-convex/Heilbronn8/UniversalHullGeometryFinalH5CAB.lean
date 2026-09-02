import Heilbronn8.TriHull.HullFive300CabUniversal
import Heilbronn8.UniversalHullGeometryFinalH4

/-!
# Direct final theorem with hull five reduced to CAB

Hull size four is unconditional.  The direct eleven-region hull-five
classifier and compact metric endpoints reduce hull size five to the single
ordered right-ear profile `A@5, B@6, C@7`.  The modular theorem exposes that
CAB endpoint explicitly; the completed table-free H5 theorem discharges it,
leaving only the hull-six and hull-seven geometric exclusions.

This route contains no production sign partition, retained-word registry,
survivor bank, or generated certificate.
-/

namespace Heilbronn8

/-- Final equality from the canonical hull-five CAB endpoint and the two
remaining geometric hull-size exclusions. -/
theorem heilbronn_eight_final_of_cab_six_seven
    (hCAB : TriHull.HullFive300CABUniversalBound)
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) :
    h_convex 8 = v8 :=
  heilbronn_eight_final_of_geometricHullSizes_five_six_seven
    (TriHull.geometricHullFiveExclusion_of_cab hCAB) h6 h7

/-- Final equality with hull size five discharged by the direct table-free
geometric classification.  Only the hull-six and hull-seven exclusions remain
as inputs. -/
theorem heilbronn_eight_final_of_geometricHullSizes_six_seven
    (h6 : GeometricHullSizeExclusion 6 StrictXOrder)
    (h7 : GeometricHullSizeExclusion 7 StrictXOrder) :
    h_convex 8 = v8 :=
  heilbronn_eight_final_of_geometricHullSizes_five_six_seven
    TriHull.geometricHullFiveExclusion_tableFree h6 h7

#print axioms heilbronn_eight_final_of_cab_six_seven
#print axioms heilbronn_eight_final_of_geometricHullSizes_six_seven

end Heilbronn8
