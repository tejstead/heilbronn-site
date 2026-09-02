import Heilbronn8.TriHull.Main
import Heilbronn8.TriHull.Surcharge

namespace Heilbronn8.TriHull

theorem surcharge1_holds : Surcharge1Statement := by
  unfold Surcharge1Statement
  intro A B C P Q R hABC hP hQ hR hmin
  exact th8_lemma2_part1 hABC hP hQ hR hmin

theorem surcharge2_holds : Surcharge2Statement := by
  unfold Surcharge2Statement
  intro A B C P Q R hABC hP hQ hR hmin hγ
  exact th8_lemma2_part2 hABC hP hQ hR hmin hγ

theorem threePointTriangle_normalized_lower_bound_unconditional
    (v : Fin 8 → Point) (e : Fin 6 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    (17 : ℝ) / 2 ≤
      sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v :=
  threePointTriangle_normalized_lower_bound surcharge1_holds
    v e he hm hpos hP hQ hR

theorem triangleHull8_unconditional
    (v : Fin 8 → Point) (H : ℝ)
    (hHull : StrictTriangleHullCertificate v H) :
    minTri v * 25 ≤ 2 * H :=
  triangleHull8 surcharge1_holds surcharge2_holds v H hHull

end Heilbronn8.TriHull
