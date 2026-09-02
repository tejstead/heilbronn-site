import Heilbronn8.QuadHull.OrbitIICommon

/-! # Injection custody for the Orbit II permutation R,P,S -/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

private def rpsSwap : Equiv.Perm (Fin 8) :=
  Equiv.swap 5 6

private lemma rpsLabels_apply
    (A B C D Q P R S : Fin 8) (i : Fin 8) :
    orbitIILabels A B C D Q R P S i =
      orbitIILabels A B C D Q P R S (rpsSwap i) := by
  fin_cases i <;> rfl

/-- Injection custody for the permutation R,P,S. -/
lemma labels_RPS_injective
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D) :
    Function.Injective
      (orbitIILabels A B C D h.Q h.R h.P h.S) := by
  intro i j hij
  apply rpsSwap.injective
  apply h.labels_injective
  exact
    (rpsLabels_apply A B C D h.Q h.P h.R h.S i).symm.trans
      (hij.trans (rpsLabels_apply A B C D h.Q h.P h.R h.S j))

end OrbitIIInternal
end Heilbronn8.QuadHull
