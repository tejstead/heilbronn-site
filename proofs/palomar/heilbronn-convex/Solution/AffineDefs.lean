/-
Solution-side staging copy of the public nonsingular-affine definitions.

Copy this file to `Solution/AffineDefs.lean` during final integration. The
Challenge and Solution roots compile separately, so these declarations must
match the Challenge definitions exactly.
-/
import HullBridge
import Solution.Defs

namespace HeilbronnChallenge

/-- A nonsingular affine map of the plane. -/
structure NonsingularAffine where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  tx : ℝ
  ty : ℝ
  det_ne : a * d - b * c ≠ 0

def NonsingularAffine.map (T : NonsingularAffine) (p : ℝ × ℝ) : ℝ × ℝ :=
  (T.a * p.1 + T.b * p.2 + T.tx,
    T.c * p.1 + T.d * p.2 + T.ty)

/-- Equivalence by arbitrary relabeling and any nonsingular affine map. -/
def AffineEquivalent {n : Nat} (v u : Fin n → ℝ × ℝ) : Prop :=
  ∃ (sigma : Equiv.Perm (Fin n)) (T : NonsingularAffine),
    u = fun i ↦ T.map (v (sigma i))

/-- Determinant of the linear part. -/
def NonsingularAffine.det (T : NonsingularAffine) : ℝ :=
  T.a * T.d - T.b * T.c

lemma NonsingularAffine.det_ne' (T : NonsingularAffine) : T.det ≠ 0 := by
  simpa only [NonsingularAffine.det] using T.det_ne

/-- Convex-hull volume scales by the absolute determinant under an arbitrary
nonsingular affine map. -/
theorem volume_convexHull_nonsingularAffine {n : ℕ}
    (T : NonsingularAffine) (v : Fin n → ℝ × ℝ) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (fun i ↦ T.map (v i)))) =
      ENNReal.ofReal |T.det| *
        MeasureTheory.volume (convexHull ℝ (Set.range v)) := by
  have hrange : Set.range (fun i : Fin n ↦ T.map (v i)) =
      HullBridge.affMap T.a T.b T.c T.d T.tx T.ty '' Set.range v := by
    simpa only [NonsingularAffine.map, HullBridge.affMap] using
      (HullBridge.range_affMap (n := n)
        T.a T.b T.c T.d T.tx T.ty v)
  rw [hrange]
  simpa only [NonsingularAffine.det] using
    (HullBridge.volume_convexHull_image_affMap_abs
      T.a T.b T.c T.d T.tx T.ty (Set.range v))

/-- Explicit inverse affine map. -/
noncomputable def NonsingularAffine.inverse
    (T : NonsingularAffine) : NonsingularAffine where
  a := T.d / T.det
  b := -T.b / T.det
  c := -T.c / T.det
  d := T.a / T.det
  tx := (T.b * T.ty - T.d * T.tx) / T.det
  ty := (T.c * T.tx - T.a * T.ty) / T.det
  det_ne := by
    have hdet :
        (T.d / T.det) * (T.a / T.det) -
            (-T.b / T.det) * (-T.c / T.det) = 1 / T.det := by
      field_simp [T.det_ne']
      <;> simp only [NonsingularAffine.det]
      <;> ring
    rw [hdet]
    exact one_div_ne_zero T.det_ne'

@[simp] lemma NonsingularAffine.inverse_map_map
    (T : NonsingularAffine) (p : ℝ × ℝ) :
    T.inverse.map (T.map p) = p := by
  apply Prod.ext <;>
    simp [NonsingularAffine.inverse, NonsingularAffine.map] <;>
    field_simp [T.det_ne'] <;>
    simp only [NonsingularAffine.det] <;>
    ring

/-- Symmetry of arbitrary nonsingular affine equivalence. -/
theorem affineEquivalent_symm {n : Nat}
    {v u : Fin n → ℝ × ℝ} (h : AffineEquivalent v u) :
    AffineEquivalent u v := by
  rcases h with ⟨sigma, T, rfl⟩
  refine ⟨sigma.symm, T.inverse, ?_⟩
  funext i
  simp only [Equiv.apply_symm_apply]
  exact (T.inverse_map_map (v i)).symm

/-- Forget the orientation field of a positive-determinant affine map. -/
def PosAffine.toNonsingularAffine (T : PosAffine) : NonsingularAffine where
  a := T.a
  b := T.b
  c := T.c
  d := T.d
  tx := T.tx
  ty := T.ty
  det_ne := T.det_pos.ne'

@[simp] lemma PosAffine.toNonsingularAffine_map
    (T : PosAffine) (p : ℝ × ℝ) :
    T.toNonsingularAffine.map p = T.map p := rfl

/-- The arbitrary-determinant relation contains the existing positive-
determinant gauge relation. -/
lemma affineEquivalent_of_gaugeEquivalent {n : Nat}
    {v u : Fin n → ℝ × ℝ} (h : GaugeEquivalent v u) :
    AffineEquivalent v u := by
  rcases h with ⟨sigma, T, rfl⟩
  exact ⟨sigma, T.toNonsingularAffine, rfl⟩

/-- Composition of nonsingular affine maps, with `S.comp T` applying `T`
first and then `S`. -/
def NonsingularAffine.comp
    (S T : NonsingularAffine) : NonsingularAffine where
  a := S.a * T.a + S.b * T.c
  b := S.a * T.b + S.b * T.d
  c := S.c * T.a + S.d * T.c
  d := S.c * T.b + S.d * T.d
  tx := S.a * T.tx + S.b * T.ty + S.tx
  ty := S.c * T.tx + S.d * T.ty + S.ty
  det_ne := by
    have hid :
        (S.a * T.a + S.b * T.c) * (S.c * T.b + S.d * T.d) -
            (S.a * T.b + S.b * T.d) * (S.c * T.a + S.d * T.c) =
          (S.a * S.d - S.b * S.c) *
            (T.a * T.d - T.b * T.c) := by ring
    rw [hid]
    exact mul_ne_zero S.det_ne T.det_ne

@[simp] lemma NonsingularAffine.comp_map
    (S T : NonsingularAffine) (p : ℝ × ℝ) :
    (S.comp T).map p = S.map (T.map p) := by
  apply Prod.ext <;>
    simp [NonsingularAffine.comp, NonsingularAffine.map] <;> ring

/-- Transitivity of arbitrary nonsingular-affine equivalence. -/
theorem affineEquivalent_trans {n : Nat}
    {u v w : Fin n → ℝ × ℝ}
    (huv : AffineEquivalent u v) (hvw : AffineEquivalent v w) :
    AffineEquivalent u w := by
  rcases huv with ⟨sigma, T, huv⟩
  rcases hvw with ⟨tau, S, hvw⟩
  refine ⟨tau.trans sigma, S.comp T, ?_⟩
  funext i
  rw [congrFun hvw i, congrFun huv (tau i)]
  simp only [Equiv.trans_apply, NonsingularAffine.comp_map]

end HeilbronnChallenge
