/-
Unified solution root for the convex Heilbronn challenge. The Comparator
selects the complete twenty-nine-theorem surface for n = 3 through n = 8 from
this module.

Proved here, all in namespace `HeilbronnChallenge`:

  root support   P5_root_existsUnique, P8_root_existsUnique
  n = 3 through 6   pointwise upper bounds, attainment, exact values and uniqueness
  n = 7      pointwise upper bound, attainment, exact value, the full real
             optimizer family and its exhaustive affine classification
  n = 8      pointwise upper bound, attainment, exact value and uniqueness

The n = 7 optimum is attained by a real one-parameter family. The solution
classifies every optimizer into that family up to relabeling and an arbitrary
nonsingular affine map, identifies the reflection-induced parameter
involution, and exhibits a continuum-parameterized subfamily of inequivalent
optimizer orbits. The n = 8 solution includes the proved global upper bound
and pairwise optimizer uniqueness.

Layers underneath:

  HullBridge      shared measure-theory bridge, general `n`; turns
                  `volume (convexHull ℝ (Set.range p)) = 1` into a shoelace
                  identity on coordinates
  Heil5           the n = 5 upper bound, attainment and rigidity
  Heil6           the n = 6 upper bound, attainment and rigidity
  Heil7           the n = 7 upper bound and optimizer classification
  Heilbronn8      the n = 8 witness, upper bound and boundary classification
  Solution.Defs   the challenge definitions, transcribed
  Solution.Common shared plumbing between the two namespaces
-/
import Solution.Defs
import Solution.Common
import Solution.N3
import Solution.N4
import Solution.N5
import Solution.N5Unique
import Solution.SmallNWrappers
import Heil6
import Heil7
import Solution.N8UpperFinal
import Solution.N8UniqueFinal
