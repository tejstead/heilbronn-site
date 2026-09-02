import Heilbronn8.QuadHull.OrbitIICommon

/-! # Injection custody for the Orbit II permutation R,S,P -/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

private def rspCycle : Equiv.Perm (Fin 8) :=
  Equiv.swap 5 7 * Equiv.swap 5 6

private lemma rspLabels_apply
    (A B C D Q P R S : Fin 8) (i : Fin 8) :
    orbitIILabels A B C D Q R S P i =
      orbitIILabels A B C D Q P R S (rspCycle i) := by
  fin_cases i <;> rfl

/-- Injection custody for the permutation R,S,P. -/
lemma labels_RSP_injective
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D) :
    Function.Injective
      (orbitIILabels A B C D h.Q h.R h.S h.P) := by
  intro i j hij
  apply rspCycle.injective
  apply h.labels_injective
  exact
    (rspLabels_apply A B C D h.Q h.P h.R h.S i).symm.trans
      (hij.trans (rspLabels_apply A B C D h.Q h.P h.R h.S j))

end OrbitIIInternal
end Heilbronn8.QuadHull
