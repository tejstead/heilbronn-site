import Heilbronn8.Defs
import Heilbronn8.Survivors.Join.HullSixTwoFourWideProduct

/-!
# Small geometry identities for the wide `2 + 4` adapter

These are the only retriangulation identities needed to turn a wide lower
chord into the eight-face scalar seam.  Each proof involves at most five
points and deliberately avoids one large coordinate expansion.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Splitting the opposite cross-cap triangle at the second interior point. -/
theorem hullSixTwoFour_crossCap_split
    (P Q U0 L3 : ℝ × ℝ) :
    sig P L3 U0 =
      sig P L3 Q + sig Q L3 U0 + sig P Q U0 := by
  simp only [sig]
  ring

/-- Retriangulate the first lower quadrilateral along `L0-L2`. -/
theorem hullSixTwoFour_lower_retriangulation_02
    (P L0 L1 L2 L3 : ℝ × ℝ) :
    sig P L0 L1 + sig P L1 L2 + sig P L2 L3 =
      sig P L0 L2 + sig L0 L1 L2 + sig P L2 L3 := by
  simp only [sig]
  ring

/-- Retriangulate the second lower quadrilateral along `L1-L3`. -/
theorem hullSixTwoFour_lower_retriangulation_13
    (P L0 L1 L2 L3 : ℝ × ℝ) :
    sig P L0 L1 + sig P L1 L2 + sig P L2 L3 =
      sig P L1 L3 + sig P L0 L1 + sig L1 L2 L3 := by
  simp only [sig]
  ring

/-- Retriangulate the full lower pentagon with the long face `P-L0-L3` and
the lower diagonal `L0-L2`. -/
theorem hullSixTwoFour_lower_retriangulation_03
    (P L0 L1 L2 L3 : ℝ × ℝ) :
    sig P L0 L1 + sig P L1 L2 + sig P L2 L3 =
      sig P L0 L3 + sig L0 L1 L2 + sig L0 L2 L3 := by
  simp only [sig]
  ring

end Heilbronn8
