import Heilbronn8.TriHull.HullSevenC24PointAdapter
import Heilbronn8.TriHull.HullSevenCappedChordRigidity

/-!
# The two-row determinant frame of a boundary C24 packet

Phase-two scratch source.  A capped C24 boundary packet has the rigid fifteen
chord variables proved in `HullSevenCappedRigidity`.  Four Pluecker rows then
recover every bracket based at cycle vertices 0 and 1.  These two rows are
enough to reconstruct every ray from the off-hull point up to a unique
positive linear map.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private lemma HullSevenC24PointData.bracket_skew_public
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j : HullSevenC24Index) : X.bracket i j = -X.bracket j i := by
  unfold HullSevenC24PointData.bracket
  rw [sig_swap]
  ring

private lemma HullSevenC24PointData.bracket_plucker_public
    {v : Configuration} (X : HullSevenC24PointData v)
    (i j k l : HullSevenC24Index) :
    X.bracket i j * X.bracket k l -
        X.bracket i k * X.bracket j l +
        X.bracket i l * X.bracket j k = 0 := by
  have hp := gp (v X.point) (v (X.cycle i)) (v (X.cycle j))
    (v (X.cycle k)) (v (X.cycle l))
  unfold HullSevenC24PointData.bracket
  field_simp [X.minTri_pos.ne'] <;> nlinarith [hp]

noncomputable def hullSevenC24FrameA : ℝ := hullSevenCoreRoot + 1
noncomputable def hullSevenC24FrameQ : ℝ :=
  1 + 2 / hullSevenCoreRoot
noncomputable def hullSevenC24FrameL : ℝ :=
  1 + hullSevenC24FrameQ / hullSevenC24FrameA
noncomputable def hullSevenC24FrameB : ℝ :=
  1 + 1 / hullSevenCoreRoot
noncomputable def hullSevenC24FrameP : ℝ :=
  hullSevenC24FrameA + 1 / hullSevenCoreRoot

/-- Canonical values of `bracket 0 i`, for `i=0,...,6`. -/
noncomputable def hullSevenC24CanonicalRow0 : Fin 7 → ℝ :=
  ![0, 1, hullSevenC24FrameA, hullSevenC24FrameA, 1,
    -(hullSevenC24FrameA + 1) / hullSevenC24FrameL,
    -(hullSevenCoreRoot ^ 2)]

/-- Canonical values of `bracket 1 i`, for `i=0,...,6`. -/
noncomputable def hullSevenC24CanonicalRow1 : Fin 7 → ℝ :=
  ![-1, 0, hullSevenC24FrameA, hullSevenC24FrameP,
    hullSevenC24FrameL, -1,
    -(hullSevenC24FrameA + 1) / hullSevenC24FrameL]

private lemma hullSevenC24FrameA_pos : 0 < hullSevenC24FrameA := by
  unfold hullSevenC24FrameA
  linarith [hullSevenCoreRoot_pos]

private lemma hullSevenC24FrameQ_pos : 0 < hullSevenC24FrameQ := by
  unfold hullSevenC24FrameQ
  have hdiv : 0 < 2 / hullSevenCoreRoot :=
    div_pos (by norm_num) hullSevenCoreRoot_pos
  linarith

private lemma hullSevenC24FrameL_pos : 0 < hullSevenC24FrameL := by
  unfold hullSevenC24FrameL
  have hdiv : 0 < hullSevenC24FrameQ / hullSevenC24FrameA :=
    div_pos hullSevenC24FrameQ_pos hullSevenC24FrameA_pos
  linarith

private lemma hullSevenC24FrameLA :
    hullSevenC24FrameL * hullSevenC24FrameA =
      hullSevenC24FrameA + hullSevenC24FrameQ := by
  unfold hullSevenC24FrameL
  field_simp [hullSevenC24FrameA_pos.ne']

/-- The first two bracket rows are canonical at a capped C24 boundary. -/
theorem HullSevenC24PointData.frame_rows_rigid
    {v : Configuration} (X : HullSevenC24PointData v)
    (S : HullSevenCappedSurrogate X.toChordInput)
    (hupper : v8 * (doubledHullArea v / minTri v) ≤ 1) :
    (∀ i, X.bracket 0 i = hullSevenC24CanonicalRow0 i) ∧
      (∀ i, X.bracket 1 i = hullSevenC24CanonicalRow1 i) := by
  have R := HullSevenCappedSurrogate.chordInput_rigid_of_v8_upper
    X.toChordInput S hupper
  have ha0 : X.bracket 0 1 = 1 := by
    change X.toChordInput.a0 = 1
    exact R.a0_eq
  have hA : X.bracket 1 2 = hullSevenC24FrameA := by
    change X.toChordInput.A = hullSevenC24FrameA
    simpa [hullSevenC24FrameA] using R.A_eq
  have hB : X.bracket 2 3 = hullSevenC24FrameB := by
    change X.toChordInput.B = hullSevenC24FrameB
    simpa [hullSevenC24FrameB] using R.B_eq
  have hC : X.bracket 3 4 = hullSevenC24FrameB := by
    change X.toChordInput.C = hullSevenC24FrameB
    simpa [hullSevenC24FrameB] using R.C_eq
  have hD : X.bracket 4 5 = hullSevenC24FrameA := by
    change X.toChordInput.D = hullSevenC24FrameA
    simpa [hullSevenC24FrameA] using R.D_eq
  have ha5 : X.bracket 5 6 = 1 := by
    change X.toChordInput.a5 = 1
    exact R.a5_eq
  have hG : X.bracket 6 0 = hullSevenCoreRoot ^ 2 := by
    change X.toChordInput.G = hullSevenCoreRoot ^ 2
    exact R.G_eq
  have hp : X.bracket 1 3 = hullSevenC24FrameP := by
    change X.toChordInput.p = hullSevenC24FrameP
    simpa [hullSevenC24FrameP, hullSevenC24FrameA] using R.p_eq
  have hq : X.bracket 2 4 = hullSevenC24FrameQ := by
    change X.toChordInput.q = hullSevenC24FrameQ
    simpa [hullSevenC24FrameQ] using R.q_eq
  have hr : X.bracket 3 5 = hullSevenC24FrameP := by
    change X.toChordInput.r = hullSevenC24FrameP
    simpa [hullSevenC24FrameP, hullSevenC24FrameA] using R.r_eq
  have hL : X.bracket 1 4 = hullSevenC24FrameL := by
    change X.toChordInput.L = hullSevenC24FrameL
    simpa [hullSevenC24FrameL, hullSevenC24FrameQ,
      hullSevenC24FrameA] using R.L_eq
  have hR : X.bracket 2 5 = hullSevenC24FrameL := by
    change X.toChordInput.R = hullSevenC24FrameL
    simpa [hullSevenC24FrameL, hullSevenC24FrameQ,
      hullSevenC24FrameA] using R.R_eq
  have hc : X.bracket 1 5 = -1 := by
    have h := R.c_eq
    change -X.bracket 1 5 = 1 at h
    linarith
  have hl : X.bracket 0 4 = 1 := by
    change X.toChordInput.l = 1
    exact R.l_eq
  have hm : X.bracket 2 6 = 1 := by
    change X.toChordInput.m = 1
    exact R.m_eq

  have h02 : X.bracket 0 2 = hullSevenC24FrameA := by
    have hpl := X.bracket_plucker_public 0 1 2 4
    rw [ha0, hq, hL, hl, hA] at hpl
    have hLA := hullSevenC24FrameLA
    nlinarith [hullSevenC24FrameL_pos]
  have hCp :
      hullSevenC24FrameB + hullSevenC24FrameP =
        hullSevenC24FrameA + hullSevenC24FrameQ := by
    unfold hullSevenC24FrameB hullSevenC24FrameP
    unfold hullSevenC24FrameQ
    ring
  have h03 : X.bracket 0 3 = hullSevenC24FrameA := by
    have hpl := X.bracket_plucker_public 0 1 3 4
    rw [ha0, hC, hL, hl, hp] at hpl
    have hLA := hullSevenC24FrameLA
    nlinarith [hullSevenC24FrameL_pos]
  have h05 : X.bracket 0 5 =
      -(hullSevenC24FrameA + 1) / hullSevenC24FrameL := by
    have hpl := X.bracket_plucker_public 0 1 4 5
    rw [ha0, hD, hl, hc, hL] at hpl
    apply (eq_div_iff hullSevenC24FrameL_pos.ne').2
    nlinarith
  have h16 : X.bracket 1 6 =
      -(hullSevenC24FrameA + 1) / hullSevenC24FrameL := by
    have hpl := X.bracket_plucker_public 1 2 5 6
    rw [hA, ha5, hc, hm, hR] at hpl
    apply (eq_div_iff hullSevenC24FrameL_pos.ne').2
    nlinarith
  have h00 : X.bracket 0 0 = 0 := by
    simp [HullSevenC24PointData.bracket, sig]
  have h11 : X.bracket 1 1 = 0 := by
    simp [HullSevenC24PointData.bracket, sig]
  have h10 : X.bracket 1 0 = -1 := by
    rw [X.bracket_skew_public, ha0]
  have h06 : X.bracket 0 6 = -(hullSevenCoreRoot ^ 2) := by
    rw [X.bracket_skew_public, hG]
  have h05' : X.bracket 0 5 =
      (-1 + -hullSevenC24FrameA) / hullSevenC24FrameL := by
    simpa only [neg_add_rev] using h05
  have h16' : X.bracket 1 6 =
      (-1 + -hullSevenC24FrameA) / hullSevenC24FrameL := by
    simpa only [neg_add_rev] using h16
  constructor
  · intro i
    fin_cases i <;> simp [hullSevenC24CanonicalRow0] <;> assumption
  · intro i
    fin_cases i <;> simp [hullSevenC24CanonicalRow1] <;> assumption

end Heilbronn8.TriHull
