import Heilbronn8.TriHull.HullSevenType2ProductScalar
import Heilbronn8.TriHull.HullSevenType2TwoVarCertificate

/-!
# Unconditional two-variable bound for hull-seven type 2

This is the cycle-free bridge between the human product-ear reduction and the
ordinary kernel interval certificate.  `HullSevenType2ProductScalar` owns the
small public proposition consumed by the reduction; the certificate supplies
its two fields here.

The imported root checks use ordinary kernel `decide`.  This file uses no
native evaluator, added assumption, generated binary payload, or external
numerical trust.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The exact interval checker supplies both branches required by the compact
type-2 product-ear reduction. -/
theorem hullSevenType2_twoVar_interval_bound : HullSevenType2TwoVarBound :=
  hullSevenType2TwoVarBound_checked

end Heilbronn8.TriHull
