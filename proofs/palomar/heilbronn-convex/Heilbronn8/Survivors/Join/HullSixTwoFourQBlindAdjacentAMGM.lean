import Heilbronn8.Survivors.Join.HullSixTwoFourAdjacentQ12Scratch
import Heilbronn8.Survivors.Join.HullSixTwoFourAdjacentQ23Scratch
import Heilbronn8.Survivors.Join.HullSixTwoFourAdjacentQ34Scratch

/-!
# Compact scalar closures for adjacent q-blind `2 + 4` transitions

This umbrella module exposes the three exact source-only AM--GM closures for
the adjacent q-blind chambers `q = 12`, `q = 23`, and `q = 34`:

* `hullSixTwoFour_q12_scalar`
* `hullSixTwoFourQ23_scalar`
* `hullSixTwoFourQ34_scalar`

Each theorem retains its raw signed-cell identities and lower-ear premises,
so a geometry adapter can invoke it without a finite chamber certificate.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
