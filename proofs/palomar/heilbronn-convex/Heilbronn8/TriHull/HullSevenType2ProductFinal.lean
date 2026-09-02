import Heilbronn8.TriHull.HullSevenType2TwoVarInterval

/-!
# Unconditional product-ear closer for hull-seven type 2

This is the cycle-free join between the human product-ear reduction and the
ordinary-kernel two-variable interval certificate.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Every honest type-2 hyperbolic packet has normalized area strictly larger
than `25 / 2`. -/
theorem hullSevenType2Hyperbolic_area_gt {H : ℝ}
    (D : HullSevenType2HyperbolicPacket H) : (25 : ℝ) / 2 < H :=
  D.product_not_beats hullSevenType2_twoVar_interval_bound

end Heilbronn8.TriHull
