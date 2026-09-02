import Heilbronn8.TriHull.HullSevenType2Scalar

/-!
# Type-4 scalar seam

The preferred rotated type-4 determinant chart satisfies exactly the scalar
packet already closed in `HullSevenType2Scalar`.  This tiny wrapper keeps the
public semantic name type-specific while sharing the frozen scalar proof.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The type-4 chart uses the same reflection-GM scalar packet as type 2. -/
abbrev HullSevenType4ScalarData := HullSevenType2ScalarData

/-- Shared scalar closure, exposed under its type-4 semantic name. -/
theorem hullSevenType4_area_gt {H : ℝ}
    (h : HullSevenType4ScalarData H) : (25 : ℝ) / 2 < H :=
  hullSevenType2_area_gt h

end Heilbronn8.TriHull
