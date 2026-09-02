import Heil6.FiniteHullCases
import Solution.Defs

set_option linter.style.header false

/-!
# Elementary algebra for positive-affine gauge equivalence

The challenge definition packages a positive-determinant affine map, but does
not yet record the identity, composition, or inverse operations.  They are
proved here directly from the six scalar fields.  In particular,
`GaugeEquivalent` is an equivalence relation and a relabelling on the target
can be absorbed into its permutation witness.
-/

namespace N6Scratch
namespace GaugeAlgebra

open HeilbronnChallenge

def posAffineId : PosAffine where
  a := 1
  b := 0
  c := 0
  d := 1
  tx := 0
  ty := 0
  det_pos := by norm_num

/-- `S ∘ T`, with the convention that `T` acts first. -/
def posAffineComp (S T : PosAffine) : PosAffine where
  a := S.a * T.a + S.b * T.c
  b := S.a * T.b + S.b * T.d
  c := S.c * T.a + S.d * T.c
  d := S.c * T.b + S.d * T.d
  tx := S.a * T.tx + S.b * T.ty + S.tx
  ty := S.c * T.tx + S.d * T.ty + S.ty
  det_pos := by
    have hdet :
        (S.a * T.a + S.b * T.c) * (S.c * T.b + S.d * T.d) -
            (S.a * T.b + S.b * T.d) * (S.c * T.a + S.d * T.c) =
          (S.a * S.d - S.b * S.c) * (T.a * T.d - T.b * T.c) := by
      ring
    rw [hdet]
    exact mul_pos S.det_pos T.det_pos

theorem posAffineId_map (p : ℝ × ℝ) : posAffineId.map p = p := by
  ext <;> simp only [posAffineId, PosAffine.map] <;> ring

theorem posAffineComp_map (S T : PosAffine) (p : ℝ × ℝ) :
    (posAffineComp S T).map p = S.map (T.map p) := by
  ext <;> simp only [posAffineComp, PosAffine.map] <;> ring

/-- Inverse of a positive-determinant affine map. -/
noncomputable def posAffineInv (T : PosAffine) : PosAffine where
  a := T.d / (T.a * T.d - T.b * T.c)
  b := -T.b / (T.a * T.d - T.b * T.c)
  c := -T.c / (T.a * T.d - T.b * T.c)
  d := T.a / (T.a * T.d - T.b * T.c)
  tx := (T.b * T.ty - T.d * T.tx) / (T.a * T.d - T.b * T.c)
  ty := (T.c * T.tx - T.a * T.ty) / (T.a * T.d - T.b * T.c)
  det_pos := by
    let δ := T.a * T.d - T.b * T.c
    have hδ : 0 < δ := by simpa only [δ] using T.det_pos
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hid :
        (T.d / δ) * (T.a / δ) - (-T.b / δ) * (-T.c / δ) =
          1 / δ := by
      field_simp [hδne]
      ring
    rw [hid]
    exact one_div_pos.mpr hδ

theorem posAffineInv_map (T : PosAffine) (p : ℝ × ℝ) :
    (posAffineInv T).map (T.map p) = p := by
  have hdet : T.a * T.d - T.b * T.c ≠ 0 := ne_of_gt T.det_pos
  have hdet_comm : T.d * T.a - T.b * T.c ≠ 0 := by
    rw [show T.d * T.a - T.b * T.c =
      T.a * T.d - T.b * T.c by ring]
    exact hdet
  have hdet_alt : -(T.c * T.b) + T.a * T.d ≠ 0 := by
    rw [show -(T.c * T.b) + T.a * T.d =
      T.a * T.d - T.b * T.c by ring]
    exact hdet
  ext <;> simp only [posAffineInv, PosAffine.map]
  · field_simp [hdet, hdet_comm, hdet_alt]
    ring
  · field_simp [hdet, hdet_comm, hdet_alt]
    have hcancel := mul_inv_cancel₀ hdet_alt
    linear_combination p.2 * hcancel

theorem gaugeEquivalent_refl {n : Nat} (v : Fin n → ℝ × ℝ) :
    GaugeEquivalent v v := by
  refine ⟨Equiv.refl _, posAffineId, ?_⟩
  funext i
  simpa only [Equiv.refl_apply] using (posAffineId_map (v i)).symm

theorem gaugeEquivalent_symm {n : Nat} {v u : Fin n → ℝ × ℝ}
    (h : GaugeEquivalent v u) : GaugeEquivalent u v := by
  rcases h with ⟨σ, T, hT⟩
  refine ⟨σ.symm, posAffineInv T, ?_⟩
  funext i
  have hi := congrFun hT (σ.symm i)
  rw [σ.apply_symm_apply] at hi
  rw [hi]
  exact (posAffineInv_map T (v i)).symm

theorem gaugeEquivalent_trans {n : Nat}
    {v u z : Fin n → ℝ × ℝ}
    (hvu : GaugeEquivalent v u) (huz : GaugeEquivalent u z) :
    GaugeEquivalent v z := by
  rcases hvu with ⟨σ, T, hT⟩
  rcases huz with ⟨τ, S, hS⟩
  refine ⟨τ.trans σ, posAffineComp S T, ?_⟩
  funext i
  have hSi := congrFun hS i
  have hTi := congrFun hT (τ i)
  rw [hSi, hTi]
  simpa only [Equiv.trans_apply] using
    (posAffineComp_map S T (v (σ (τ i)))).symm

/-- A permutation used to define the target family can be absorbed into the
permutation field of gauge equivalence. -/
theorem gaugeEquivalent_of_relabels_right
    {u v w : Fin 6 → ℝ × ℝ}
    (hrel : FiniteHullCases.Relabels v w)
    (h : GaugeEquivalent u w) : GaugeEquivalent u v := by
  rcases hrel with ⟨e, rfl⟩
  rcases h with ⟨σ, T, hT⟩
  refine ⟨e.symm.trans σ, T, ?_⟩
  funext i
  have hi := congrFun hT (e.symm i)
  simpa only [e.apply_symm_apply, Equiv.trans_apply] using hi

end GaugeAlgebra
end N6Scratch
