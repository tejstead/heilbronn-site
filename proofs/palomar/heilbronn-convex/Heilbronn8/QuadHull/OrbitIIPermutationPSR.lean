import Heilbronn8.QuadHull.OrbitIICommon

/-! # Injection custody for the Orbit II permutation P,S,R -/

namespace Heilbronn8.QuadHull
namespace OrbitIIInternal

/-- The compact library permutation that exchanges slots six and seven. -/
private def psrSwap : Equiv.Perm (Fin 8) :=
  Equiv.swap 6 7

/-- A pointwise lookup fact is substantially cheaper than equality of the two
length-eight vector functions.  In particular, no `funext` term is retained. -/
private lemma psrLabels_apply
    (A B C D Q P R S : Fin 8) (i : Fin 8) :
    orbitIILabels A B C D Q P S R i =
      orbitIILabels A B C D Q P R S (psrSwap i) := by
  fin_cases i <;> rfl

/-- Injection custody for the permutation P,S,R. -/
lemma labels_PSR_injective
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitIIGeometryCertificate v A B C D) :
    Function.Injective
      (orbitIILabels A B C D h.Q h.P h.S h.R) := by
  intro i j hij
  apply psrSwap.injective
  apply h.labels_injective
  exact
    (psrLabels_apply A B C D h.Q h.P h.R h.S i).symm.trans
      (hij.trans (psrLabels_apply A B C D h.Q h.P h.R h.S j))

end OrbitIIInternal
end Heilbronn8.QuadHull
