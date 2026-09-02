import Heilbronn8.TriHull.HullSevenType2ProductFinal
import Heilbronn8.Survivors.Join.HullSevenType2HyperbolicUniversalAdapter

/-!
# Checked universal closer for hull-seven type 2

This tiny join exposes the exact proposition consumed by the universal
geometric exclusion layer while keeping that layer independent of the scalar
proof implementation.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The checked product-ear theorem supplies the stable universal type-2
hyperbolic packet closer. -/
theorem hullSevenType2HyperbolicPacketCloser_checked :
    HullSevenType2HyperbolicPacketCloser := by
  intro H D
  exact (TriHull.hullSevenType2Hyperbolic_area_gt D).le

end Heilbronn8
