import Heilbronn8.V8

/-!
# The sharp algebraic core of the hull-seven route

This file isolates the part of the seven-hull-one-interior argument which is
already independent of geometry.  After the two endpoint fan cells, five
ears, and the two outer long chords have been tightened, the seven fan cells
are

`1, s + 1, 1 + 1 / s, 1 + 1 / u, u + 1, 1, s * u`.

The remaining long-chord condition is `hullSevenCoreF s u >= 0`.  The theorem
`hullSeven_tight_core_v8` proves the sharp `v8` estimate for this core.  The
geometric monotone-transfer statement needed to reach this core is kept as an
explicit hypothesis in `hullSeven_v8_of_tight_transfer`.
-/

namespace Heilbronn8.TriHull

/-- The one-variable polynomial at the symmetric hull-seven endpoint. -/
def hullSevenCoreQ (x : ℝ) : ℝ :=
  x ^ 5 + 2 * x ^ 4 - 4 * x ^ 2 - 4 * x - 2

/-- The denominator whose reciprocal ratio is the sharp normalized area. -/
def hullSevenCoreDen (x : ℝ) : ℝ :=
  x ^ 3 + 2 * x ^ 2 + 6 * x + 2

/-- The last long-chord inequality after all transfer equalities are imposed. -/
def hullSevenCoreF (s u : ℝ) : ℝ :=
  s ^ 3 * u ^ 3 + s ^ 3 * u ^ 2 + s ^ 2 * u ^ 3
    - 2 * s ^ 2 * u - 2 * s * u ^ 2 - 4 * s * u - s - u

/-- The normalized doubled hull area of the tightened fan. -/
noncomputable def hullSevenCoreH (s u : ℝ) : ℝ :=
  6 + s + u + s * u + 1 / s + 1 / u

lemma hullSevenCoreQ_left_neg :
    hullSevenCoreQ (147 / 100) < 0 := by
  norm_num [hullSevenCoreQ]

lemma hullSevenCoreQ_right_pos :
    0 < hullSevenCoreQ (3 / 2) := by
  norm_num [hullSevenCoreQ]

/-- The divided difference of `hullSevenCoreQ` is positive on `[1,∞)`. -/
lemma hullSevenCoreQ_slope_pos {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    0 <
      y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4
        + 2 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
        - 4 * (y + x) - 4 := by
  let a := x - 1
  let b := y - 1
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hid :
      y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4
          + 2 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
          - 4 * (y + x) - 4 =
        1 + 18 * a + 18 * b
          + 18 * a ^ 2 + 18 * a * b + 18 * b ^ 2
          + 7 * a ^ 3 + 7 * a ^ 2 * b + 7 * a * b ^ 2 + 7 * b ^ 3
          + a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4 := by
    dsimp [a, b]
    ring
  rw [hid]
  positivity

lemma hullSevenCoreQ_strictMonoOn :
    StrictMonoOn hullSevenCoreQ (Set.Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  have hS := hullSevenCoreQ_slope_pos hx hy
  have hfactor :
      hullSevenCoreQ y - hullSevenCoreQ x =
        (y - x) *
          (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4
            + 2 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
            - 4 * (y + x) - 4) := by
    unfold hullSevenCoreQ
    ring
  nlinarith [mul_pos (sub_pos.mpr hxy) hS]

theorem hullSevenCoreRoot_existsUnique :
    ∃! x : ℝ,
      x ∈ Set.Icc (147 / 100 : ℝ) (3 / 2) ∧ hullSevenCoreQ x = 0 := by
  have hcont :
      ContinuousOn hullSevenCoreQ (Set.Icc (147 / 100 : ℝ) (3 / 2)) := by
    apply Continuous.continuousOn
    unfold hullSevenCoreQ
    fun_prop
  have hsub := intermediate_value_Icc
    (by norm_num : (147 / 100 : ℝ) ≤ 3 / 2) hcont
  have hzero :
      (0 : ℝ) ∈
        Set.Icc (hullSevenCoreQ (147 / 100)) (hullSevenCoreQ (3 / 2)) :=
    ⟨hullSevenCoreQ_left_neg.le, hullSevenCoreQ_right_pos.le⟩
  obtain ⟨x, hx, hQx⟩ := hsub hzero
  refine ⟨x, ⟨hx, hQx⟩, ?_⟩
  rintro y ⟨hy, hQy⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmono := hullSevenCoreQ_strictMonoOn
      (show (1 : ℝ) ≤ y from
        le_trans (by norm_num : (1 : ℝ) ≤ 147 / 100) hy.1)
      (show (1 : ℝ) ≤ x from
        le_trans (by norm_num : (1 : ℝ) ≤ 147 / 100) hx.1) h
    rw [hQx, hQy] at hmono
    exact lt_irrefl 0 hmono
  · have hmono := hullSevenCoreQ_strictMonoOn
      (show (1 : ℝ) ≤ x from
        le_trans (by norm_num : (1 : ℝ) ≤ 147 / 100) hx.1)
      (show (1 : ℝ) ≤ y from
        le_trans (by norm_num : (1 : ℝ) ≤ 147 / 100) hy.1) h
    rw [hQx, hQy] at hmono
    exact lt_irrefl 0 hmono

/-- The unique symmetric endpoint parameter in `[1.47,1.5]`. -/
noncomputable def hullSevenCoreRoot : ℝ :=
  Classical.choose hullSevenCoreRoot_existsUnique.exists

lemma hullSevenCoreRoot_spec :
    hullSevenCoreRoot ∈ Set.Icc (147 / 100 : ℝ) (3 / 2) ∧
      hullSevenCoreQ hullSevenCoreRoot = 0 :=
  Classical.choose_spec hullSevenCoreRoot_existsUnique.exists

lemma hullSevenCoreRoot_mem :
    hullSevenCoreRoot ∈ Set.Icc (147 / 100 : ℝ) (3 / 2) :=
  hullSevenCoreRoot_spec.1

lemma hullSevenCoreRoot_eq_zero :
    hullSevenCoreQ hullSevenCoreRoot = 0 :=
  hullSevenCoreRoot_spec.2

lemma hullSevenCoreDen_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < hullSevenCoreDen x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  unfold hullSevenCoreDen
  positivity

/-- On the short root bracket, `x / hullSevenCoreDen x` lies in the
defining bracket for `v8`. -/
lemma hullSevenCore_ratio_mem {x : ℝ}
    (hxlo : 147 / 100 ≤ x) (hxhi : x ≤ 3 / 2) :
    x / hullSevenCoreDen x ∈
      Set.Icc (79 / 1000 : ℝ) (81 / 1000) := by
  have hx0 : 0 ≤ x := by linarith
  have hD : 0 < hullSevenCoreDen x :=
    hullSevenCoreDen_pos (by linarith)

  have hx2u : x ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi) (by linarith : 0 ≤ 3 / 2 + x)]
  have hx2u' : x ^ 2 ≤ (9 / 4 : ℝ) := by
    norm_num at hx2u ⊢
    exact hx2u
  have hx3u : x ^ 3 ≤ (9 / 4 : ℝ) * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2u') hx0]
  have hx2term_u : 2 * x ^ 2 ≤ 3 * x := by
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 3 - 2 * x)]
  have hconst_u : (2 : ℝ) ≤ (200 / 147) * x := by
    nlinarith
  have hlow_cross :
      79 * hullSevenCoreDen x ≤ 1000 * x := by
    unfold hullSevenCoreDen
    nlinarith

  have hx2l : (147 / 100 : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxlo) (by linarith : 0 ≤ x + 147 / 100)]
  have hx3l : (147 / 100 : ℝ) ^ 2 * x ≤ x ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2l) hx0]
  have hx2term_l : (294 / 100 : ℝ) * x ≤ 2 * x ^ 2 := by
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 2 * x - 294 / 100)]
  have hconst_l : (4 / 3 : ℝ) * x ≤ 2 := by
    nlinarith
  have hupp_cross :
      1000 * x ≤ 81 * hullSevenCoreDen x := by
    unfold hullSevenCoreDen
    nlinarith

  constructor
  · apply (le_div_iff₀ hD).2
    nlinarith
  · apply (div_le_iff₀ hD).2
    nlinarith

/-- The endpoint ratio is exactly the already-defined quintic root `v8`. -/
lemma hullSevenCoreRoot_ratio_eq_v8 :
    hullSevenCoreRoot / hullSevenCoreDen hullSevenCoreRoot = v8 := by
  let r := hullSevenCoreRoot
  have hrmem := hullSevenCoreRoot_mem
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [hrmem.1]
  have hD : 0 < hullSevenCoreDen r := hullSevenCoreDen_pos hr1
  have hid :
      hullSevenCoreDen r ^ 5 * P (r / hullSevenCoreDen r) =
        hullSevenCoreQ r *
          (16 - 48 * r ^ 2 - 136 * r ^ 3 - 180 * r ^ 4
            - 178 * r ^ 5 - 128 * r ^ 6 - 70 * r ^ 7
            - 28 * r ^ 8 - 8 * r ^ 9 - r ^ 10) := by
    unfold hullSevenCoreDen hullSevenCoreQ P
    field_simp [hD.ne']
    ring
  have hzero :
      hullSevenCoreDen r ^ 5 * P (r / hullSevenCoreDen r) = 0 := by
    rw [hid]
    dsimp [r]
    rw [hullSevenCoreRoot_eq_zero]
    ring
  have hP : P (r / hullSevenCoreDen r) = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 5 hD.ne')
  apply v8_unique
  · exact hullSevenCore_ratio_mem hrmem.1 hrmem.2
  · exact hP

lemma hullSevenCoreRoot_le_of_Q_nonneg {x : ℝ}
    (hx : 1 ≤ x) (hQ : 0 ≤ hullSevenCoreQ x) :
    hullSevenCoreRoot ≤ x := by
  by_contra hnot
  have hlt : x < hullSevenCoreRoot := lt_of_not_ge hnot
  have hmono := hullSevenCoreQ_strictMonoOn
    (show x ∈ Set.Ici (1 : ℝ) from hx)
    (show (1 : ℝ) ≤ hullSevenCoreRoot from
      le_trans (by norm_num : (1 : ℝ) ≤ 147 / 100)
        hullSevenCoreRoot_mem.1) hlt
  rw [hullSevenCoreRoot_eq_zero] at hmono
  linarith

lemma hullSevenCoreRoot_v8_phi :
    v8 *
      (6 + hullSevenCoreRoot ^ 2 + 2 * hullSevenCoreRoot
        + 2 / hullSevenCoreRoot) = 1 := by
  have hr1 : 1 ≤ hullSevenCoreRoot := by
    linarith [hullSevenCoreRoot_mem.1]
  have hr0 : 0 < hullSevenCoreRoot := lt_of_lt_of_le (by norm_num) hr1
  have hD : 0 < hullSevenCoreDen hullSevenCoreRoot :=
    hullSevenCoreDen_pos hr1
  rw [← hullSevenCoreRoot_ratio_eq_v8]
  unfold hullSevenCoreDen
  field_simp [hr0.ne', hD.ne']
  ring

/-- Sharp two-variable algebraic estimate for the tightened hull-seven fan. -/
theorem hullSeven_tight_core_v8 {s u : ℝ}
    (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hF : 0 ≤ hullSevenCoreF s u) :
    1 ≤ v8 * hullSevenCoreH s u := by
  let X := s + u
  let Y := s * u
  let rho := Real.sqrt Y
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hY1 : 1 ≤ Y := by
    dsimp [Y]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hu)]
  have hY0 : 0 ≤ Y := le_trans (by norm_num) hY1
  have hrho0 : 0 ≤ rho := Real.sqrt_nonneg Y
  have hrhosq : rho ^ 2 = Y := by
    dsimp [rho]
    exact Real.sq_sqrt hY0
  have hrho1 : 1 ≤ rho := by nlinarith
  have hrhopos : 0 < rho := lt_of_lt_of_le (by norm_num) hrho1

  have hX : 2 * rho ≤ X := by
    have hsq := sq_nonneg (s - u)
    by_contra hnot
    have hlt : X < 2 * rho := lt_of_not_ge hnot
    have hsumpos : 0 < X + 2 * rho := by
      dsimp [X]
      positivity
    have hprod : (X - 2 * rho) * (X + 2 * rho) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hsumpos
    dsimp [X] at hlt hsumpos hprod ⊢
    dsimp [Y] at hrhosq
    nlinarith [hsq, hprod, hrhosq]

  have hFxy :
      hullSevenCoreF s u =
        Y ^ 3 - 4 * Y + X * (Y ^ 2 - 2 * Y - 1) := by
    dsimp [X, Y]
    unfold hullSevenCoreF
    ring

  have hrho_ge_root : hullSevenCoreRoot ≤ rho := by
    by_cases hA : 0 ≤ Y ^ 2 - 2 * Y - 1
    · have hrho15 : (3 / 2 : ℝ) ≤ rho := by
        by_contra hnot
        have hlt : rho < 3 / 2 := lt_of_not_ge hnot
        have hsq_lt : rho ^ 2 < (3 / 2 : ℝ) ^ 2 := by
          have hp : 0 < (3 / 2 - rho) * (3 / 2 + rho) :=
            mul_pos (sub_pos.mpr hlt) (by nlinarith)
          nlinarith
        have hYlt : Y < 9 / 4 := by nlinarith
        have hp : (Y - 9 / 4) * (Y + 1 / 4) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        nlinarith
      exact le_trans hullSevenCoreRoot_mem.2 hrho15
    · have hAneg : Y ^ 2 - 2 * Y - 1 < 0 := lt_of_not_ge hA
      have hmul :
          X * (Y ^ 2 - 2 * Y - 1) ≤
            (2 * rho) * (Y ^ 2 - 2 * Y - 1) :=
        mul_le_mul_of_nonpos_right hX hAneg.le
      have hsym :
          0 ≤ Y ^ 3 - 4 * Y +
            (2 * rho) * (Y ^ 2 - 2 * Y - 1) := by
        rw [hFxy] at hF
        linarith
      have hQid :
          Y ^ 3 - 4 * Y + (2 * rho) * (Y ^ 2 - 2 * Y - 1) =
            rho * hullSevenCoreQ rho := by
        unfold hullSevenCoreQ
        rw [← hrhosq]
        ring
      have hQrho : 0 ≤ hullSevenCoreQ rho := by
        rw [hQid] at hsym
        by_contra hneg
        have hneg' : hullSevenCoreQ rho < 0 := lt_of_not_ge hneg
        exact (not_lt_of_ge hsym) (mul_neg_of_pos_of_neg hrhopos hneg')
      exact hullSevenCoreRoot_le_of_Q_nonneg hrho1 hQrho

  have hrecip : 2 / rho ≤ 1 / s + 1 / u := by
    have hrecip_id : 1 / s + 1 / u = X / Y := by
      dsimp [X, Y]
      field_simp [hs0.ne', hu0.ne']
      ring
    rw [hrecip_id]
    apply (div_le_div_iff₀ hrhopos (lt_of_lt_of_le (by norm_num) hY1)).2
    have hmul := mul_le_mul_of_nonneg_right hX hrho0
    nlinarith

  have hHrho :
      6 + rho ^ 2 + 2 * rho + 2 / rho ≤ hullSevenCoreH s u := by
    unfold hullSevenCoreH
    dsimp [X, Y] at hX hrhosq
    nlinarith

  have hroot1 : 1 ≤ hullSevenCoreRoot := by
    linarith [hullSevenCoreRoot_mem.1]
  have hrootpos : 0 < hullSevenCoreRoot :=
    lt_of_lt_of_le (by norm_num) hroot1
  have hprod1 : 1 ≤ rho * hullSevenCoreRoot := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrho1)
      (sub_nonneg.mpr hroot1)]
  have hfrac : 2 / (rho * hullSevenCoreRoot) ≤ 2 := by
    apply (div_le_iff₀ (mul_pos hrhopos hrootpos)).2
    nlinarith
  have hbracket :
      0 ≤ rho + hullSevenCoreRoot + 2 -
        2 / (rho * hullSevenCoreRoot) := by
    linarith
  have hphi_diff :
      (6 + rho ^ 2 + 2 * rho + 2 / rho) -
          (6 + hullSevenCoreRoot ^ 2 + 2 * hullSevenCoreRoot
            + 2 / hullSevenCoreRoot) =
        (rho - hullSevenCoreRoot) *
          (rho + hullSevenCoreRoot + 2 -
            2 / (rho * hullSevenCoreRoot)) := by
    field_simp [hrhopos.ne', hrootpos.ne']
    ring
  have hphi :
      6 + hullSevenCoreRoot ^ 2 + 2 * hullSevenCoreRoot
          + 2 / hullSevenCoreRoot ≤
        6 + rho ^ 2 + 2 * rho + 2 / rho := by
    nlinarith [hphi_diff,
      mul_nonneg (sub_nonneg.mpr hrho_ge_root) hbracket]
  have htotal :
      6 + hullSevenCoreRoot ^ 2 + 2 * hullSevenCoreRoot
          + 2 / hullSevenCoreRoot ≤ hullSevenCoreH s u :=
    le_trans hphi hHrho
  have hmul := mul_le_mul_of_nonneg_left htotal v8_pos.le
  rw [hullSevenCoreRoot_v8_phi] at hmul
  exact hmul

/-- Explicit seam for the still-geometric part of the hull-seven proof.

The future transfer theorem only has to supply `s,u`, the tight long-chord
inequality, and the comparison from the tight fan area to the original hull
area. -/
theorem hullSeven_v8_of_tight_transfer {H s u : ℝ}
    (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hF : 0 ≤ hullSevenCoreF s u)
    (htransfer : hullSevenCoreH s u ≤ H) :
    1 ≤ v8 * H := by
  have hcore := hullSeven_tight_core_v8 hs hu hF
  have hmul := mul_le_mul_of_nonneg_left htransfer v8_pos.le
  linarith

end Heilbronn8.TriHull
