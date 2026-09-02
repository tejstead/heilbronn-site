import Heilbronn8.TriHull.HullFive300CabProfileAdapter
import Heilbronn8.TriHull.HullFive300Cab717Geometry

/-!
# Complete table-free right-ear CAB endpoint

The full right-ear profiles first reduce the canonical `CAB` packet to
either a same-sector configuration or the unique type-717 sign cell.  The
same-sector branch is already closed by the compact central theorem, while
`HullFive300Cab717Geometry` closes all three possible outer-sign branches
of the exceptional cell.  This module composes those two independent
adapters and then invokes the existing `CCA`/`CAA`/inner-swap reduction.

No retained-word table or generated certificate is imported here.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The census-facing and metric-facing descriptions of type 717 contain
the same ten signs.  Keep the conversion explicit so the two modules can
remain independently usable. -/
private def cab717InnerSigns_of_signs
    {v : Configuration} {e : Equiv.Perm (Fin 8)}
    (h : HullFive300Cab717Signs v e) :
    HullFive300Cab717InnerSigns v e := {
  bpq_pos := h.bpq_pos
  xpq_neg := h.xpq_neg
  cpq_pos := h.cpq_pos
  bpr_pos := h.bpr_pos
  xpr_neg := h.xpr_neg
  cpr_neg := h.cpr_neg
  bqr_pos := h.bqr_pos
  xqr_pos := h.xqr_pos
  cqr_neg := h.cqr_neg
  pqr_pos := h.pqr_pos }

/-- The complete ordered `CAB` endpoint, with the same-sector/type-717
dispatch and all outer determinant signs discharged internally. -/
theorem hullFive300_cab_universal_bound : HullFive300CABUniversalBound :=
  hullFive300CABUniversalBound_of_717 (by
    intro v e hm hcyc q r p h717
    exact hullFive300_cab717_packet_bound v e hm hcyc p q r
      (cab717InnerSigns_of_signs h717))

/-- All exact right-ear `300` residual packets (`CCA`, `CAA`, `CAB`, and
the inner-swapped `CBA`) satisfy the required pentagon fan bound. -/
theorem hullFive300_rightProfile_universal_bound :
    HullFive300RightProfileUniversalBound :=
  hullFive300RightProfileUniversalBound_of_cab
    hullFive300_cab_universal_bound

/-- Final table-free geometric exclusion for a five-vertex hull. -/
theorem geometricHullFiveExclusion_tableFree :
    GeometricHullSizeExclusion 5 StrictXOrder :=
  geometricHullFiveExclusion_of_cab hullFive300_cab_universal_bound

#print axioms hullFive300_cab_universal_bound
#print axioms hullFive300_rightProfile_universal_bound
#print axioms geometricHullFiveExclusion_tableFree

end Heilbronn8.TriHull
