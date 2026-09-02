import Heilbronn8.TriHull.HullSevenC24BracketRigidity

/-!
# Pairwise gauge uniqueness of capped C24 boundary packets

Phase-two scratch source.  This module does not compare either packet to a
hard-coded witness.  Instead it gauges the off-hull point and the first two
cycle rays to `(0,0),(1,0),(0,1)`.  The two canonical determinant rows from
`HullSevenC24BracketRigidity` then give all seven remaining coordinates.
Consequently any two capped boundary packets are related by a relabeling and
a positive-determinant affine map.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Gauge based at the off-cycle point and the first oriented boundary cell. -/
noncomputable def HullSevenC24PointData.frameGauge
    {v : Configuration} (X : HullSevenC24PointData v) : PosAffine :=
  gaugeAffine (v X.point) (v (X.cycle 0)) (v (X.cycle 1)) (by
    simpa using X.boundary_pos 0)

@[simp] lemma HullSevenC24PointData.frameGauge_map_point
    {v : Configuration} (X : HullSevenC24PointData v) :
    X.frameGauge.map (v X.point) = (0, 0) := by
  unfold HullSevenC24PointData.frameGauge
  apply gaugeAffine_map_A

@[simp] lemma HullSevenC24PointData.frameGauge_map_cycle_zero
    {v : Configuration} (X : HullSevenC24PointData v) :
    X.frameGauge.map (v (X.cycle 0)) = (1, 0) := by
  unfold HullSevenC24PointData.frameGauge
  apply gaugeAffine_map_B

@[simp] lemma HullSevenC24PointData.frameGauge_map_cycle_one
    {v : Configuration} (X : HullSevenC24PointData v) :
    X.frameGauge.map (v (X.cycle 1)) = (0, 1) := by
  unfold HullSevenC24PointData.frameGauge
  apply gaugeAffine_map_C

/-- The two bracket rows are literally the coordinates in the frame gauge. -/
lemma HullSevenC24PointData.frameGauge_map_cycle
    {v : Configuration} (X : HullSevenC24PointData v)
    (hanchor : X.bracket 0 1 = 1) (i : Fin 7) :
    X.frameGauge.map (v (X.cycle i)) =
      (-X.bracket 1 i, X.bracket 0 i) := by
  have hsigAnchor :
      sig (v X.point) (v (X.cycle 0)) (v (X.cycle 1)) = minTri v := by
    unfold HullSevenC24PointData.bracket at hanchor
    field_simp [X.minTri_pos.ne'] at hanchor
    nlinarith
  have hdet : X.frameGauge.det = 1 / minTri v := by
    unfold HullSevenC24PointData.frameGauge
    rw [gaugeAffine_det, hsigAnchor]
  have hzero := X.frameGauge_map_point
  have hc0 := X.frameGauge_map_cycle_zero
  have hc1 := X.frameGauge_map_cycle_one
  have htrans0 := sig_posAffine X.frameGauge
    (v X.point) (v (X.cycle 0)) (v (X.cycle i))
  have htrans1 := sig_posAffine X.frameGauge
    (v X.point) (v (X.cycle 1)) (v (X.cycle i))
  rw [hzero, hc0, hdet] at htrans0
  rw [hzero, hc1, hdet] at htrans1
  have hright0 :
      (1 / minTri v) *
          sig (v X.point) (v (X.cycle 0)) (v (X.cycle i)) =
        X.bracket 0 i := by
    unfold HullSevenC24PointData.bracket
    field_simp [X.minTri_pos.ne']
  have hright1 :
      (1 / minTri v) *
          sig (v X.point) (v (X.cycle 1)) (v (X.cycle i)) =
        X.bracket 1 i := by
    unfold HullSevenC24PointData.bracket
    field_simp [X.minTri_pos.ne']
  rw [hright0] at htrans0
  rw [hright1] at htrans1
  apply Prod.ext
  · simp only [sig, Prod.fst, Prod.snd, sub_zero, zero_mul, one_mul,
      zero_sub, neg_mul, mul_zero, add_zero] at htrans1
    linarith
  · simpa [sig] using htrans0

/-- Every cycle vertex has the same normalized coordinate at a capped C24
boundary, independently of the original configuration. -/
theorem HullSevenC24PointData.frameGauge_cycle_canonical
    {v : Configuration} (X : HullSevenC24PointData v)
    (S : HullSevenCappedSurrogate X.toChordInput)
    (hupper : v8 * (doubledHullArea v / minTri v) ≤ 1)
    (i : Fin 7) :
    X.frameGauge.map (v (X.cycle i)) =
      (-hullSevenC24CanonicalRow1 i, hullSevenC24CanonicalRow0 i) := by
  obtain ⟨hrow0, hrow1⟩ := X.frame_rows_rigid S hupper
  rw [X.frameGauge_map_cycle (by
    simpa [hullSevenC24CanonicalRow0] using hrow0 1) i,
    hrow0 i, hrow1 i]

/-! ## The eight-label presentation -/

/-- List the seven cycle labels first and the off-cycle label last. -/
def HullSevenC24PointData.presentation
    {v : Configuration} (X : HullSevenC24PointData v) : Fin 8 → Fin 8 :=
  Fin.lastCases X.point X.cycle

@[simp] lemma HullSevenC24PointData.presentation_castSucc
    {v : Configuration} (X : HullSevenC24PointData v) (i : Fin 7) :
    X.presentation i.castSucc = X.cycle i := by
  simp [HullSevenC24PointData.presentation]

@[simp] lemma HullSevenC24PointData.presentation_last
    {v : Configuration} (X : HullSevenC24PointData v) :
    X.presentation (Fin.last 7) = X.point := by
  unfold HullSevenC24PointData.presentation
  exact Fin.lastCases_last

lemma HullSevenC24PointData.presentation_injective
    {v : Configuration} (X : HullSevenC24PointData v) :
    Function.Injective X.presentation := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · have hc : X.cycle i = X.cycle j := by simpa using hij
      have : i = j := X.cycle_injective hc
      simpa [this]
    · exfalso
      apply X.point_outside
      exact ⟨i, calc
        X.cycle i = X.presentation i.castSucc :=
          (X.presentation_castSucc i).symm
        _ = X.presentation (Fin.last 7) := hij
        _ = X.point := X.presentation_last⟩
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · exfalso
      apply X.point_outside
      exact ⟨j, calc
        X.cycle j = X.presentation j.castSucc :=
          (X.presentation_castSucc j).symm
        _ = X.presentation (Fin.last 7) := hij.symm
        _ = X.point := X.presentation_last⟩
    · rfl

/-- The C24 presentation is a relabeling of all eight point labels. -/
noncomputable def HullSevenC24PointData.presentationEquiv
    {v : Configuration} (X : HullSevenC24PointData v) :
    Equiv.Perm (Fin 8) :=
  Equiv.ofBijective X.presentation
    ⟨X.presentation_injective,
      Finite.surjective_of_injective X.presentation_injective⟩

@[simp] lemma HullSevenC24PointData.presentationEquiv_apply
    {v : Configuration} (X : HullSevenC24PointData v) (i : Fin 8) :
    X.presentationEquiv i = X.presentation i := rfl

/-! ## Small local positive-affine group operations -/

private def c24ComposePosAffine (outer inner : PosAffine) : PosAffine :=
  ⟨outer.a * inner.a + outer.b * inner.c,
    outer.a * inner.b + outer.b * inner.d,
    outer.c * inner.a + outer.d * inner.c,
    outer.c * inner.b + outer.d * inner.d,
    outer.a * inner.e + outer.b * inner.f + outer.e,
    outer.c * inner.e + outer.d * inner.f + outer.f, by
      have ho := outer.det_pos'
      have hi := inner.det_pos'
      simp only [PosAffine.det] at ho hi
      nlinarith [mul_pos ho hi]⟩

@[simp] private lemma c24ComposePosAffine_map
    (outer inner : PosAffine) (p : ℝ × ℝ) :
    (c24ComposePosAffine outer inner).map p = outer.map (inner.map p) := by
  apply Prod.ext <;> simp [c24ComposePosAffine, PosAffine.map] <;> ring

private noncomputable def c24InversePosAffine (T : PosAffine) : PosAffine :=
  ⟨T.d / T.det, -T.b / T.det, -T.c / T.det, T.a / T.det,
    (T.b * T.f - T.d * T.e) / T.det,
    (T.c * T.e - T.a * T.f) / T.det, by
      have hdet := T.det_pos'
      have hne : T.det ≠ 0 := ne_of_gt hdet
      have heq :
          T.d / T.det * (T.a / T.det) -
              (-T.b / T.det) * (-T.c / T.det) = 1 / T.det := by
        field_simp [hne]
        simp only [PosAffine.det]
        ring
      rw [heq]
      exact one_div_pos.mpr hdet⟩

@[simp] private lemma c24InversePosAffine_map
    (T : PosAffine) (p : ℝ × ℝ) :
    (c24InversePosAffine T).map (T.map p) = p := by
  have hne : T.det ≠ 0 := ne_of_gt T.det_pos'
  apply Prod.ext <;>
    simp only [c24InversePosAffine, PosAffine.map, Prod.fst, Prod.snd] <;>
    field_simp [hne] <;> simp only [PosAffine.det] <;> ring

/-- Raw pairwise uniqueness statement, intentionally independent of the
phase-four wrapper's private `GaugeEquivalent` namespace. -/
theorem hullSevenC24_pairwise_gauge_unique
    {v u : Configuration}
    (X : HullSevenC24PointData v) (Y : HullSevenC24PointData u)
    (SX : HullSevenCappedSurrogate X.toChordInput)
    (SY : HullSevenCappedSurrogate Y.toChordInput)
    (hv : v8 * (doubledHullArea v / minTri v) ≤ 1)
    (hu : v8 * (doubledHullArea u / minTri u) ≤ 1) :
    ∃ (sigma : Equiv.Perm (Fin 8)) (T : PosAffine),
      u = fun i ↦ T.map (v (sigma i)) := by
  let TX := X.frameGauge
  let TY := Y.frameGauge
  let ex := X.presentationEquiv
  let ey := Y.presentationEquiv
  have hframe : ∀ k : Fin 8,
      TX.map (v (ex k)) = TY.map (u (ey k)) := by
    intro k
    change X.frameGauge.map (v (X.presentationEquiv k)) =
      Y.frameGauge.map (u (Y.presentationEquiv k))
    rw [X.presentationEquiv_apply, Y.presentationEquiv_apply]
    refine Fin.lastCases ?_ (fun i ↦ ?_) k
    · rw [X.presentation_last, Y.presentation_last,
        X.frameGauge_map_point, Y.frameGauge_map_point]
    · rw [X.presentation_castSucc, Y.presentation_castSucc,
        X.frameGauge_cycle_canonical SX hv i,
        Y.frameGauge_cycle_canonical SY hu i]
  let sigma : Equiv.Perm (Fin 8) := ey.symm.trans ex
  let T : PosAffine := c24ComposePosAffine (c24InversePosAffine TY) TX
  refine ⟨sigma, T, ?_⟩
  funext j
  let k : Fin 8 := ey.symm j
  have hj : ey k = j := by simp [k]
  have hf := hframe k
  have hsource : sigma j = ex k := by simp [sigma, k]
  rw [hsource]
  change u j = (c24ComposePosAffine (c24InversePosAffine TY) TX).map
    (v (ex k))
  rw [c24ComposePosAffine_map]
  calc
    u j = u (ey k) := by rw [hj]
    _ = (c24InversePosAffine TY).map (TY.map (u (ey k))) := by simp
    _ = (c24InversePosAffine TY).map (TX.map (v (ex k))) := by rw [hf]

end Heilbronn8.TriHull
