import Heilbronn8.QuadHull.OrbitIICommon

/-! # Injection custody for the Orbit II permutation S,P,R -/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

private def sprCycle : Equiv.Perm (Fin 8) :=
  Equiv.swap 5 6 * Equiv.swap 5 7

private lemma sprLabels_apply
    (A B C D Q P R S : Fin 8) (i : Fin 8) :
    orbitIILabels A B C D Q S P R i =
      orbitIILabels A B C D Q P R S (sprCycle i) := by
  fin_cases i <;> rfl

/-- Injection custody for the permutation S,P,R. -/
lemma labels_SPR_injective
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D) :
    Function.Injective
      (orbitIILabels A B C D h.Q h.S h.P h.R) := by
  intro i j hij
  apply sprCycle.injective
  apply h.labels_injective
  exact
    (sprLabels_apply A B C D h.Q h.P h.R h.S i).symm.trans
      (hij.trans (sprLabels_apply A B C D h.Q h.P h.R h.S j))

end OrbitIIInternal
end Heilbronn8.QuadHull
