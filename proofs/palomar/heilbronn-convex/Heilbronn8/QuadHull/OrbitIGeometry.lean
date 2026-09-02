import Heilbronn8.QuadHull.Main
import Heilbronn8.QuadHull.OrbitIGeometryRows
import Heilbronn8.TriHull.Bridge

/-!
# A geometric producer for the non-cyclic orbit-I leaves

This file is deliberately independent of the generated stratum corpus.  Its
input is the common coarse placement which occurs in orbit I: `P,S,T,R` are
in the common `ABC`/`DAB` sector and, after choosing `P` extremally, the other
three points are in both `PCA` and `PDA`.

The residual leaf is not stored as a generated scalar packet.  Instead it is
selected by subtriangle membership.  Thus a sign-word checker can use a
Boolean disjunction of the constructors of `OrbitIEasyGeometryCase`.

The genuinely cyclic constructor is kept separate: in addition to its ten
one-point memberships it needs the determinant/orientation bridge into
`CyclicLeaf`.  Nothing in this file postulates one of those inequalities.
-/

namespace Heilbronn8.QuadHull

private def orbitScaleFirst (r : ℝ) (p : Point) : Point :=
  (r * p.1, p.2)

private lemma sig_orbitScaleFirst (r : ℝ) (p q s : Point) :
    sig (orbitScaleFirst r p) (orbitScaleFirst r q)
        (orbitScaleFirst r s) = r * sig p q s := by
  simp only [orbitScaleFirst, sig]
  ring

private lemma inTriStrict_orbitScaleFirst (r : ℝ) {P A B C : Point}
    (hP : TriHull.InTriStrict P A B C) :
    TriHull.InTriStrict (orbitScaleFirst r P)
      (orbitScaleFirst r A) (orbitScaleFirst r B)
      (orbitScaleFirst r C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hPe⟩ := hP
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hPe]
  simp only [orbitScaleFirst, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul]
  apply Prod.ext <;> simp <;> ring

private lemma orbit_normalized_minimum (v : Fin 8 → Point)
    (hm : 0 < minTri v) :
    TriHull.AllTrianglesMinAreaOne
      (fun i ↦ orbitScaleFirst (2 / minTri v) (v i)) := by
  intro i j k hij hik hjk
  have hle := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  have hrpos : 0 < 2 / minTri v := div_pos (by norm_num) hm
  have hrm : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hrm.symm
    _ ≤ (2 / minTri v) * |sig (v i) (v j) (v k)| :=
      mul_le_mul_of_nonneg_left hle hrpos.le
    _ = |sig
        (orbitScaleFirst (2 / minTri v) (v i))
        (orbitScaleFirst (2 / minTri v) (v j))
        (orbitScaleFirst (2 / minTri v) (v k))| := by
      rw [sig_orbitScaleFirst, abs_mul, abs_of_pos hrpos]

private theorem onePointTriangle_normalized_lower_bound
    (v : Fin 8 → Point) (e : Fin 4 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : TriHull.InTriStrict (v (e 3))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    3 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
  obtain ⟨h1, h2, h3⟩ := TriHull.inTriStrict_fan_pos hpos hP
  have unit_of_pos (i j k : Fin 4)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hp : 0 < sig (v (e i)) (v (e j)) (v (e k))) :
      1 ≤ sig (v (e i)) (v (e j)) (v (e k)) / minTri v := by
    have hmin := minTri_le_abs_sig_of_pairwise_ne v
      (he.ne hij) (he.ne hik) (he.ne hjk)
    rw [abs_of_pos hp] at hmin
    rw [le_div_iff₀ hm]
    simpa using hmin
  have hu1 := unit_of_pos 3 1 2 (by decide) (by decide) (by decide) h1
  have hu2 := unit_of_pos 3 2 0 (by decide) (by decide) (by decide) h2
  have hu3 := unit_of_pos 3 0 1 (by decide) (by decide) (by decide) h3
  have hfan :
      sig (v (e 3)) (v (e 1)) (v (e 2)) +
          sig (v (e 3)) (v (e 2)) (v (e 0)) +
          sig (v (e 3)) (v (e 0)) (v (e 1)) =
        sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simp only [sig]
    ring
  rw [← hfan, add_div, add_div]
  linarith

private theorem fourPointTriangle_normalized_lower_bound
    (v : Fin 8 → Point) (e : Fin 7 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : TriHull.InTriStrict (v (e 3))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : TriHull.InTriStrict (v (e 4))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hR : TriHull.InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hS : TriHull.InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    (21 : ℝ) / 2 ≤
      sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
  let r : ℝ := 2 / minTri v
  let w8 : Fin 8 → Point := fun i ↦ orbitScaleFirst r (v i)
  let w : Fin 7 → Point := fun i ↦ w8 (e i)
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have hw8min : TriHull.AllTrianglesMinAreaOne w8 := by
    simpa [w8, r] using orbit_normalized_minimum v hm
  have hwmin : TriHull.AllTrianglesMinAreaOne w := by
    exact hw8min.comp e he
  have hwpos : 0 < sig (w 0) (w 1) (w 2) := by
    simpa only [w, w8, sig_orbitScaleFirst] using mul_pos hrpos hpos
  have hwP : TriHull.InTriStrict (w 3) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitScaleFirst r hP
  have hwQ : TriHull.InTriStrict (w 4) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitScaleFirst r hQ
  have hwR : TriHull.InTriStrict (w 5) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitScaleFirst r hR
  have hwS : TriHull.InTriStrict (w 6) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitScaleFirst r hS
  have hb := TriHull.th8_lemma4 TriHull.surcharge1_holds
    TriHull.surcharge2_holds w hwpos hwP hwQ hwR hwS hwmin
  have hscale :
      sig (w 0) (w 1) (w 2) =
        r * sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simp only [w, w8, sig_orbitScaleFirst]
  calc
    (21 : ℝ) / 2 ≤ sig (w 0) (w 1) (w 2) / 2 := hb
    _ = sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
      rw [hscale]
      dsimp [r]
      field_simp [ne_of_gt hm]

/-- The common selected placement for orbit I. -/
structure OrbitICommonGeometryCertificate
    (v : Fin 8 → Point) (A B C D : Fin 8) where
  P : Fin 8
  S : Fin 8
  T : Fin 8
  R : Fin 8
  labels_injective : Function.Injective
    (quadLabels A B C D P S T R)
  ccw : CCWQuad (v A) (v B) (v C) (v D)
  P_in_ABC : TriHull.InTriStrict (v P) (v A) (v B) (v C)
  S_in_ABC : TriHull.InTriStrict (v S) (v A) (v B) (v C)
  T_in_ABC : TriHull.InTriStrict (v T) (v A) (v B) (v C)
  R_in_ABC : TriHull.InTriStrict (v R) (v A) (v B) (v C)
  P_in_DAB : TriHull.InTriStrict (v P) (v D) (v A) (v B)
  S_in_DAB : TriHull.InTriStrict (v S) (v D) (v A) (v B)
  T_in_DAB : TriHull.InTriStrict (v T) (v D) (v A) (v B)
  R_in_DAB : TriHull.InTriStrict (v R) (v D) (v A) (v B)
  S_in_PCA : TriHull.InTriStrict (v S) (v P) (v C) (v A)
  T_in_PCA : TriHull.InTriStrict (v T) (v P) (v C) (v A)
  R_in_PCA : TriHull.InTriStrict (v R) (v P) (v C) (v A)
  S_in_PDA : TriHull.InTriStrict (v S) (v P) (v D) (v A)
  T_in_PDA : TriHull.InTriStrict (v T) (v P) (v D) (v A)
  R_in_PDA : TriHull.InTriStrict (v R) (v P) (v D) (v A)

def OrbitICommonGeometryCertificate.labels
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) : Fin 8 → Fin 8 :=
  quadLabels A B C D h.P h.S h.T h.R

/-- The five easy residual shapes (with the two `DP` alternatives). -/
inductive OrbitIEasyGeometryCase
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) : Prop
  | shared
      (S_in_PRA : TriHull.InTriStrict (v h.S) (v h.P) (v h.R) (v A))
      (T_in_PRA : TriHull.InTriStrict (v h.T) (v h.P) (v h.R) (v A))
  | p_common
      (S_in_PCR : TriHull.InTriStrict (v h.S) (v h.P) (v C) (v h.R))
      (T_in_PCR : TriHull.InTriStrict (v h.T) (v h.P) (v C) (v h.R))
      (S_in_PDR : TriHull.InTriStrict (v h.S) (v h.P) (v D) (v h.R))
      (T_in_PDR : TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.R))
  | a_common
      (S_in_RCA : TriHull.InTriStrict (v h.S) (v h.R) (v C) (v A))
      (T_in_RCA : TriHull.InTriStrict (v h.T) (v h.R) (v C) (v A))
      (S_in_RDA : TriHull.InTriStrict (v h.S) (v h.R) (v D) (v A))
      (T_in_RDA : TriHull.InTriStrict (v h.T) (v h.R) (v D) (v A))
  | d_p_split
      (S_in_PCR : TriHull.InTriStrict (v h.S) (v h.P) (v C) (v h.R))
      (T_in_RCA : TriHull.InTriStrict (v h.T) (v h.R) (v C) (v A))
      (S_in_PDR : TriHull.InTriStrict (v h.S) (v h.P) (v D) (v h.R))
      (T_in_PDR : TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.R))
  | d_p_opposite
      (S_in_RCA : TriHull.InTriStrict (v h.S) (v h.R) (v C) (v A))
      (T_in_RCA : TriHull.InTriStrict (v h.T) (v h.R) (v C) (v A))
      (S_in_PDR : TriHull.InTriStrict (v h.S) (v h.P) (v D) (v h.R))
      (T_in_PDR : TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.R))
  | c_a_d_split
      (S_in_RCA : TriHull.InTriStrict (v h.S) (v h.R) (v C) (v A))
      (T_in_RCA : TriHull.InTriStrict (v h.T) (v h.R) (v C) (v A))
      (S_in_PDR : TriHull.InTriStrict (v h.S) (v h.P) (v D) (v h.R))
      (T_in_RDA : TriHull.InTriStrict (v h.T) (v h.R) (v D) (v A))

private lemma F2_lt_of_twoPoint {z : ℝ}
    (h : 4 + 2 * Real.sqrt 3 ≤ z) : F2 < z := by
  norm_num [F2] at ⊢
  nlinarith [TriHull.sixty_nine_fortieths_lt_sqrt_three]

/-- The normalized doubled quadrilateral area used by every orbit-I leaf. -/
noncomputable def orbitINormalizedHull
    (v : Fin 8 → Point) (A B C D : Fin 8) : ℝ :=
  (sig (v A) (v B) (v C) + sig (v A) (v C) (v D)) / minTri v

/-- The common orbit-I placement supplies the scalar residual core shared by
both the five easy leaves and the cyclic leaf. -/
noncomputable def OrbitICommonGeometryCertificate.residualGeometry
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    OrbitIResidualGeometry (orbitINormalizedHull v A B C D) := by
  let α : ℝ := sig (v h.P) (v A) (v B) / minTri v
  let β : ℝ := sig (v h.P) (v B) (v C) / minTri v
  let γ : ℝ := sig (v h.P) (v C) (v D) / minTri v
  let δ : ℝ := sig (v h.P) (v D) (v A) / minTri v
  let u : ℝ := sig (v h.P) (v C) (v A) / minTri v
  let t : ℝ := sig (v h.P) (v B) (v D) / minTri v
  let w : ℝ := sig (v A) (v C) (v D) / minTri v
  let labels : Fin 8 → Fin 8 := h.labels
  have hlabels : Function.Injective labels := by
    simpa [labels, OrbitICommonGeometryCertificate.labels] using
      h.labels_injective
  have unit_of_pos (i j k : Fin 8)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpos : 0 < sig (v (labels i)) (v (labels j)) (v (labels k))) :
      1 ≤ sig (v (labels i)) (v (labels j)) (v (labels k)) / minTri v := by
    have hmin := minTri_le_abs_sig_of_pairwise_ne v
      (hlabels.ne hij) (hlabels.ne hik) (hlabels.ne hjk)
    rw [abs_of_pos hpos] at hmin
    rw [le_div_iff₀ hm]
    simpa using hmin
  have hβpos : 0 < sig (v h.P) (v B) (v C) :=
    (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).1
  have hupos : 0 < sig (v h.P) (v C) (v A) :=
    (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).2.1
  have hαpos : 0 < sig (v h.P) (v A) (v B) :=
    (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).2.2
  have htpos : 0 < sig (v h.P) (v B) (v D) :=
    (TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB).2.1
  have hδpos : 0 < sig (v h.P) (v D) (v A) :=
    (TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB).2.2
  have hACDpos : 0 < sig (v A) (v C) (v D) := by
    calc
      0 < sig (v C) (v D) (v A) := h.ccw.2.2.1
      _ = sig (v A) (v C) (v D) := by
        simp only [sig]
        ring
  have hγpos : 0 < sig (v h.P) (v C) (v D) := by
    obtain ⟨px, py, pz, hpx, hpy, hpz, hpsum, hPeq⟩ := h.P_in_DAB
    rw [hPeq,
      sig_affine_fst (v D) (v A) (v B) (v C) (v D)
        px py pz hpsum]
    simp only [sig_eq13, mul_zero, zero_add]
    exact add_pos (mul_pos hpy hACDpos) (mul_pos hpz h.ccw.2.1)
  have hABCfour :
      (21 : ℝ) / 2 ≤ sig (v A) (v B) (v C) / minTri v := by
    simpa [labels] using fourPointTriangle_normalized_lower_bound v
      ![A, B, C, h.P, h.S, h.T, h.R]
      (by
        have hs : Function.Injective (![0, 1, 2, 4, 5, 6, 7] :
            Fin 7 → Fin 8) := by decide
        convert hlabels.comp hs using 1 <;>
          funext i <;> fin_cases i <;> rfl) hm h.ccw.1
      h.P_in_ABC h.S_in_ABC h.T_in_ABC h.R_in_ABC
  have hDABfour :
      (21 : ℝ) / 2 ≤ sig (v D) (v A) (v B) / minTri v := by
    simpa [labels] using fourPointTriangle_normalized_lower_bound v
      ![D, A, B, h.P, h.S, h.T, h.R]
      (by
        have hs : Function.Injective (![3, 0, 1, 4, 5, 6, 7] :
            Fin 7 → Fin 8) := by decide
        convert hlabels.comp hs using 1 <;>
          funext i <;> fin_cases i <;> rfl) hm h.ccw.2.2.2
      h.P_in_DAB h.S_in_DAB h.T_in_DAB h.R_in_DAB
  have hδthree :
      (17 : ℝ) / 2 ≤ sig (v h.P) (v D) (v A) / minTri v := by
    let slots : Fin 6 → Fin 8 := ![4, 3, 0, 5, 6, 7]
    have hslots : Function.Injective slots := by decide
    let e : Fin 6 → Fin 8 := fun i ↦ labels (slots i)
    have he : Function.Injective e := by
      convert hlabels.comp hslots using 1 <;>
        funext i <;> fin_cases i <;> rfl
    simpa [e, slots, labels, OrbitICommonGeometryCertificate.labels] using
      TriHull.threePointTriangle_normalized_lower_bound_unconditional
        v e he hm hδpos h.S_in_PDA h.T_in_PDA h.R_in_PDA
  refine
    { α := α, β := β, γ := γ, δ := δ, u := u, t := t, w := w
      hull_eq := ?_
      α_unit := by
        simpa [α, labels, OrbitICommonGeometryCertificate.labels] using
          unit_of_pos 4 0 1 (by decide) (by decide) (by decide) hαpos
      β_unit := by
        simpa [β, labels, OrbitICommonGeometryCertificate.labels] using
          unit_of_pos 4 1 2 (by decide) (by decide) (by decide) hβpos
      γ_unit := by
        simpa [γ, labels, OrbitICommonGeometryCertificate.labels] using
          unit_of_pos 4 2 3 (by decide) (by decide) (by decide) hγpos
      δ_three := by simpa [δ] using hδthree
      u_unit := by
        simpa [u, labels, OrbitICommonGeometryCertificate.labels] using
          unit_of_pos 4 2 0 (by decide) (by decide) (by decide) hupos
      t_unit := by
        simpa [t, labels, OrbitICommonGeometryCertificate.labels] using
          unit_of_pos 4 1 3 (by decide) (by decide) (by decide) htpos
      plucker := ?_
      diagonal_AC := ?_
      diagonal_BD := ?_
      w_eq := ?_
      w_unit := by
        simpa [w, labels, OrbitICommonGeometryCertificate.labels] using
          unit_of_pos 0 2 3 (by decide) (by decide) (by decide) hACDpos }
  · dsimp [orbitINormalizedHull, α, β, γ, δ]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  · dsimp [α, β, γ, δ, u, t]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  · have hid : sig (v A) (v B) (v C) / minTri v = α + β + u := by
      dsimp [α, β, u]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    linarith
  · have hid : sig (v D) (v A) (v B) / minTri v = α + δ + t := by
      dsimp [α, δ, t]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    linarith
  · dsimp [w, γ, δ, u]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring

@[simp] lemma OrbitICommonGeometryCertificate.residualGeometry_u
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.residualGeometry hm).u = normalizedSig v h.P C A := by
  simp [OrbitICommonGeometryCertificate.residualGeometry, normalizedSig]

@[simp] lemma OrbitICommonGeometryCertificate.residualGeometry_delta
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.residualGeometry hm).δ = normalizedSig v h.P D A := by
  simp [OrbitICommonGeometryCertificate.residualGeometry, normalizedSig]

@[simp] lemma OrbitICommonGeometryCertificate.residualGeometry_gamma
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.residualGeometry hm).γ = normalizedSig v h.P C D := by
  simp [OrbitICommonGeometryCertificate.residualGeometry, normalizedSig]

@[simp] lemma OrbitICommonGeometryCertificate.residualGeometry_w
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.residualGeometry hm).w = normalizedSig v A C D := by
  simp [OrbitICommonGeometryCertificate.residualGeometry, normalizedSig]

lemma orbitINormalizedHull_scale
    (v : Fin 8 → Point) (A B C D : Fin 8)
    (hm : minTri v ≠ 0) :
    quadHullArea (v A) (v B) (v C) (v D) =
      minTri v / 2 * orbitINormalizedHull v A B C D := by
  dsimp [quadHullArea, oarea, orbitINormalizedHull]
  field_simp [hm]

/--
The generic producer for every non-cyclic orbit-I leaf.  All areas in the
scalar leaf are signed areas after the standard `2 / minTri` affine scaling,
so the `Point` equalities in `CrossApexFan` are genuine equalities rather than
an implicit normalization convention.
-/
theorem OrbitICommonGeometryCertificate.easyOrbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hcase : OrbitIEasyGeometryCase h) :
    OrbitCertificate v A B C D := by
  by_cases hmzero : minTri v = 0
  · exact Or.inl hmzero
  · have hm : 0 < minTri v :=
      lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hmzero)
    let labels : Fin 8 → Fin 8 := h.labels
    have hlabels : Function.Injective labels := by
      simpa [labels, OrbitICommonGeometryCertificate.labels] using
        h.labels_injective
    have unit_of_pos (i j k : Fin 8)
        (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
        (hpos : 0 < sig (v (labels i)) (v (labels j)) (v (labels k))) :
        1 ≤ sig (v (labels i)) (v (labels j)) (v (labels k)) /
          minTri v := by
      have hmin := minTri_le_abs_sig_of_pairwise_ne v
        (hlabels.ne hij) (hlabels.ne hik) (hlabels.ne hjk)
      rw [abs_of_pos hpos] at hmin
      rw [le_div_iff₀ hm]
      simpa using hmin
    obtain ⟨hβpos, hupos, hαpos⟩ :=
      TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC
    obtain ⟨hαpos', htpos, hδpos⟩ :=
      TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB
    have hACDpos : 0 < sig (v A) (v C) (v D) := by
      calc
        0 < sig (v C) (v D) (v A) := h.ccw.2.2.1
        _ = sig (v A) (v C) (v D) := by
          simp only [sig]
          ring
    have hγpos : 0 < sig (v h.P) (v C) (v D) := by
      obtain ⟨px, py, pz, hpx, hpy, hpz, hpsum, hPeq⟩ := h.P_in_DAB
      rw [hPeq,
        sig_affine_fst (v D) (v A) (v B) (v C) (v D)
          px py pz hpsum]
      simp only [sig_eq13, mul_zero, zero_add]
      exact add_pos (mul_pos hpy hACDpos) (mul_pos hpz h.ccw.2.1)
    have hABCfour :
        (21 : ℝ) / 2 ≤ sig (v A) (v B) (v C) / minTri v := by
      simpa [labels] using fourPointTriangle_normalized_lower_bound v
        ![A, B, C, h.P, h.S, h.T, h.R]
        (by
          have hs : Function.Injective (![0, 1, 2, 4, 5, 6, 7] :
              Fin 7 → Fin 8) := by decide
          convert hlabels.comp hs using 1 <;>
            funext i <;> fin_cases i <;> rfl) hm h.ccw.1
        h.P_in_ABC h.S_in_ABC h.T_in_ABC h.R_in_ABC
    have hDABfour :
        (21 : ℝ) / 2 ≤ sig (v D) (v A) (v B) / minTri v := by
      simpa [labels] using fourPointTriangle_normalized_lower_bound v
        ![D, A, B, h.P, h.S, h.T, h.R]
        (by
          have hs : Function.Injective (![3, 0, 1, 4, 5, 6, 7] :
              Fin 7 → Fin 8) := by decide
          convert hlabels.comp hs using 1 <;>
            funext i <;> fin_cases i <;> rfl) hm h.ccw.2.2.2
        h.P_in_DAB h.S_in_DAB h.T_in_DAB h.R_in_DAB
    have hδthree :
        (17 : ℝ) / 2 ≤ sig (v h.P) (v D) (v A) / minTri v := by
      let slots : Fin 6 → Fin 8 := ![4, 3, 0, 5, 6, 7]
      have hslots : Function.Injective slots := by decide
      let e : Fin 6 → Fin 8 := fun i ↦ labels (slots i)
      have he : Function.Injective e := by
        convert hlabels.comp hslots using 1 <;>
          funext i <;> fin_cases i <;> rfl
      simpa [e, slots, labels, OrbitICommonGeometryCertificate.labels] using
        TriHull.threePointTriangle_normalized_lower_bound_unconditional
          v e he hm hδpos h.S_in_PDA h.T_in_PDA h.R_in_PDA
    let H : ℝ :=
      (sig (v A) (v B) (v C) + sig (v A) (v C) (v D)) / minTri v
    let α : ℝ := sig (v h.P) (v A) (v B) / minTri v
    let β : ℝ := sig (v h.P) (v B) (v C) / minTri v
    let γ : ℝ := sig (v h.P) (v C) (v D) / minTri v
    let δ : ℝ := sig (v h.P) (v D) (v A) / minTri v
    let u : ℝ := sig (v h.P) (v C) (v A) / minTri v
    let t : ℝ := sig (v h.P) (v B) (v D) / minTri v
    let w : ℝ := sig (v A) (v C) (v D) / minTri v
    let hcore : OrbitIResidualGeometry H := by
      refine
        { α := α, β := β, γ := γ, δ := δ, u := u, t := t, w := w
          hull_eq := ?_
          α_unit := by
            simpa [α, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 0 1 (by decide) (by decide) (by decide) hαpos
          β_unit := by
            simpa [β, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 1 2 (by decide) (by decide) (by decide) hβpos
          γ_unit := by
            simpa [γ, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 2 3 (by decide) (by decide) (by decide) hγpos
          δ_three := by simpa [δ] using hδthree
          u_unit := by
            simpa [u, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 2 0 (by decide) (by decide) (by decide) hupos
          t_unit := by
            simpa [t, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 1 3 (by decide) (by decide) (by decide) htpos
          plucker := ?_
          diagonal_AC := ?_
          diagonal_BD := ?_
          w_eq := ?_
          w_unit := by
            simpa [w, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 0 2 3 (by decide) (by decide) (by decide) hACDpos }
      · dsimp [H, α, β, γ, δ]
        field_simp [ne_of_gt hm]
        simp only [sig]
        ring
      · dsimp [α, β, γ, δ, u, t]
        field_simp [ne_of_gt hm]
        simp only [sig]
        ring
      · have hid : sig (v A) (v B) (v C) / minTri v = α + β + u := by
          dsimp [α, β, u]
          field_simp [ne_of_gt hm]
          simp only [sig]
          ring
        linarith
      · have hid : sig (v D) (v A) (v B) / minTri v = α + δ + t := by
          dsimp [α, δ, t]
          field_simp [ne_of_gt hm]
          simp only [sig]
          ring
        linarith
      · dsimp [w, γ, δ, u]
        field_simp [ne_of_gt hm]
        simp only [sig]
        ring
    let x : ℝ := sig (v h.P) (v C) (v h.R) / minTri v
    let x' : ℝ := sig (v h.P) (v D) (v h.R) / minTri v
    let y : ℝ := sig (v h.R) (v C) (v A) / minTri v
    let y' : ℝ := sig (v h.R) (v D) (v A) / minTri v
    let k : ℝ := sig (v h.P) (v h.R) (v A) / minTri v
    obtain ⟨hypos, hkpos_raw, hxpos_raw⟩ :=
      TriHull.inTriStrict_fan_pos hupos h.R_in_PCA
    obtain ⟨hy'pos, hkpos'_raw, hx'pos_raw⟩ :=
      TriHull.inTriStrict_fan_pos hδpos h.R_in_PDA
    have hkpos : 0 < sig (v h.P) (v h.R) (v A) := by
      simpa only [sig_rotate (v h.R) (v A) (v h.P),
        sig_rotate (v A) (v h.P) (v h.R)] using hkpos_raw
    have hxpos : 0 < sig (v h.P) (v C) (v h.R) := by
      simpa only [sig_rotate (v h.R) (v h.P) (v C)] using hxpos_raw
    have hkpos' : 0 < sig (v h.P) (v h.R) (v A) := by
      simpa only [sig_rotate (v h.R) (v A) (v h.P),
        sig_rotate (v A) (v h.P) (v h.R)] using hkpos'_raw
    have hx'pos : 0 < sig (v h.P) (v D) (v h.R) := by
      simpa only [sig_rotate (v h.R) (v h.P) (v D)] using hx'pos_raw
    let scale : ℝ := 2 / minTri v
    let sv : Fin 8 → Point := fun i ↦ orbitScaleFirst scale (v i)
    let hfan : CrossApexFan hcore := by
      refine
        { P := sv h.P, A := sv A, C := sv C, D := sv D, R := sv h.R
          x := x, x' := x', y := y, y' := y', k := k
          x_area := ?_, x'_area := ?_, y_area := ?_, y'_area := ?_,
          k_area := ?_, u_area := ?_, δ_area := ?_, γ_area := ?_, w_area := ?_
          u_decomp := ?_, δ_decomp := ?_
          x_unit := by
            simpa [x, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 2 7 (by decide) (by decide) (by decide) hxpos
          x'_unit := by
            simpa [x', labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 3 7 (by decide) (by decide) (by decide) hx'pos
          y_unit := by
            simpa [y, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 7 2 0 (by decide) (by decide) (by decide) hypos
          y'_unit := by
            simpa [y', labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 7 3 0 (by decide) (by decide) (by decide) hy'pos
          k_unit := by
            simpa [k, labels, OrbitICommonGeometryCertificate.labels] using
              unit_of_pos 4 7 0 (by decide) (by decide) (by decide) hkpos }
      all_goals
        dsimp [hcore, x, x', y, y', k, u, δ, γ, w, sv, scale, oarea]
      all_goals try simp only [sig_orbitScaleFirst]
      all_goals field_simp [ne_of_gt hm]
      all_goals simp only [sig]
      all_goals ring
    have one_lower
        (e : Fin 4 → Fin 8) (he : Function.Injective e)
        (hp : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
        (hq : TriHull.InTriStrict (v (e 3))
          (v (e 0)) (v (e 1)) (v (e 2))) :
        3 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v :=
      onePointTriangle_normalized_lower_bound v e he hm hp hq
    have two_lower
        (e : Fin 5 → Fin 8) (he : Function.Injective e)
        (hp : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
        (hq : TriHull.InTriStrict (v (e 3))
          (v (e 0)) (v (e 1)) (v (e 2)))
        (hr : TriHull.InTriStrict (v (e 4))
          (v (e 0)) (v (e 1)) (v (e 2))) :
        F2 < sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
      exact F2_lt_of_twoPoint
        (TriHull.twoPointTriangle_normalized_lower_bound v e he hm hp hq hr)
    refine Or.inr ⟨H, ?_, .residual ?_⟩
    · dsimp [H, quadHullArea, oarea]
      field_simp [ne_of_gt hm]
    · cases hcase with
      | shared hS hT =>
          apply ResidualCase.shared
          refine { core := hcore, fan := hfan, common_large := ?_ }
          change F2 < k
          simpa [k] using two_lower ![h.P, h.R, A, h.S, h.T]
            (by
              have hs : Function.Injective (![4, 7, 0, 5, 6] :
                  Fin 5 → Fin 8) := by decide
              convert hlabels.comp hs using 1 <;>
                funext i <;> fin_cases i <;> rfl) hkpos hS hT
      | p_common hSC hTC hSD hTD =>
          apply ResidualCase.p_common
          refine { core := hcore, fan := hfan, x_large := ?_, x'_large := ?_ }
          · change F2 < x
            simpa [x] using two_lower ![h.P, C, h.R, h.S, h.T]
              (by
                have hs : Function.Injective (![4, 2, 7, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hxpos hSC hTC
          · change F2 < x'
            simpa [x'] using two_lower ![h.P, D, h.R, h.S, h.T]
              (by
                have hs : Function.Injective (![4, 3, 7, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hx'pos hSD hTD
      | a_common hSC hTC hSD hTD =>
          apply ResidualCase.a_common
          refine { core := hcore, fan := hfan, y_large := ?_, y'_large := ?_ }
          · change F2 < y
            simpa [y] using two_lower ![h.R, C, A, h.S, h.T]
              (by
                have hs : Function.Injective (![7, 2, 0, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hypos hSC hTC
          · change F2 < y'
            simpa [y'] using two_lower ![h.R, D, A, h.S, h.T]
              (by
                have hs : Function.Injective (![7, 3, 0, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hy'pos hSD hTD
      | d_p_split hSC hTC hSD hTD =>
          apply ResidualCase.d_p_common_residual
          refine { core := hcore, fan := hfan, kind := .split ?_ ?_ ?_ }
          · change (3 : ℝ) ≤ x
            simpa [x] using one_lower ![h.P, C, h.R, h.S]
              (by
                have hs : Function.Injective (![4, 2, 7, 5] :
                    Fin 4 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hxpos hSC
          · change (3 : ℝ) ≤ y
            simpa [y] using one_lower ![h.R, C, A, h.T]
              (by
                have hs : Function.Injective (![7, 2, 0, 6] :
                    Fin 4 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hypos hTC
          · change F2 < x'
            simpa [x'] using two_lower ![h.P, D, h.R, h.S, h.T]
              (by
                have hs : Function.Injective (![4, 3, 7, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hx'pos hSD hTD
      | d_p_opposite hSC hTC hSD hTD =>
          apply ResidualCase.d_p_common_residual
          refine { core := hcore, fan := hfan, kind := .opposite ?_ ?_ }
          · change F2 < y
            simpa [y] using two_lower ![h.R, C, A, h.S, h.T]
              (by
                have hs : Function.Injective (![7, 2, 0, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hypos hSC hTC
          · change F2 < x'
            simpa [x'] using two_lower ![h.P, D, h.R, h.S, h.T]
              (by
                have hs : Function.Injective (![4, 3, 7, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hx'pos hSD hTD
      | c_a_d_split hSC hTC hSD hTD =>
          apply ResidualCase.c_a_common_d_split
          refine
            { core := hcore, fan := hfan, y_large := ?_,
              x'_three := ?_, y'_three := ?_ }
          · change F2 < y
            simpa [y] using two_lower ![h.R, C, A, h.S, h.T]
              (by
                have hs : Function.Injective (![7, 2, 0, 5, 6] :
                    Fin 5 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hypos hSC hTC
          · change (3 : ℝ) ≤ x'
            simpa [x'] using one_lower ![h.P, D, h.R, h.S]
              (by
                have hs : Function.Injective (![4, 3, 7, 5] :
                    Fin 4 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hx'pos hSD
          · change (3 : ℝ) ≤ y'
            simpa [y'] using one_lower ![h.R, D, A, h.T]
              (by
                have hs : Function.Injective (![7, 3, 0, 6] :
                    Fin 4 → Fin 8) := by decide
                convert hlabels.comp hs using 1 <;>
                  funext i <;> fin_cases i <;> rfl) hy'pos hTD

/-- The common placement and the two finite cyclic witness packets construct
the complete analytic cyclic leaf. -/
noncomputable def OrbitICommonGeometryCertificate.cyclicLeaf
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hm : 0 < minTri v)
    (hlower : OrbitICyclicLowerWitnesses
      v h.P C A D h.S h.T h.R)
    (horient : OrbitICyclicOrientationWitnesses
      v h.P C A D h.S h.T h.R) :
    CyclicLeaf (orbitINormalizedHull v A B C D) := by
  have hcyclicLabels : Function.Injective
      (orbitICyclicLabels h.P C A D h.S h.T h.R) := by
    have heq : orbitICyclicLabels h.P C A D h.S h.T h.R =
        fun i ↦ h.labels (orbitICyclicSlots i) := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact h.labels_injective.comp orbitICyclicSlots_injective
  obtain ⟨_, hPCA, _⟩ :=
    TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC
  obtain ⟨_, _, hPDA⟩ :=
    TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB
  exact cyclicLeaf_of_geometryRows (h.residualGeometry hm) hm
    hcyclicLabels hPCA hPDA
    h.S_in_PCA h.T_in_PCA h.R_in_PCA
    h.S_in_PDA h.T_in_PDA h.R_in_PDA
    h.ccw h.S_in_DAB h.T_in_DAB h.R_in_DAB
    (h.residualGeometry_u hm) (h.residualGeometry_delta hm)
    (h.residualGeometry_gamma hm) (h.residualGeometry_w hm)
    hlower horient

/-- A cyclic orbit-I packet enters the existing unconditional quadrilateral
closure through `OrbitCertificate`. -/
theorem OrbitICommonGeometryCertificate.cyclicOrbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hlower : OrbitICyclicLowerWitnesses
      v h.P C A D h.S h.T h.R)
    (horient : OrbitICyclicOrientationWitnesses
      v h.P C A D h.S h.T h.R) :
    OrbitCertificate v A B C D := by
  by_cases hmzero : minTri v = 0
  · exact Or.inl hmzero
  · have hm : 0 < minTri v :=
      lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hmzero)
    exact orbitCertificate_of_cyclicLeaf
      (orbitINormalizedHull_scale v A B C D hmzero)
      (h.cyclicLeaf hm hlower horient)

end Heilbronn8.QuadHull
