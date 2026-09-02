import Heilbronn8.QuadHull.OrbitICoarseGeometry
import Heilbronn8.QuadHull.OrbitIGeometryRows

/-!
# Normalization and cell floors for coarse orbit I

This module converts a side-minimal geometric packet into the scalar record
checked by `OrbitICoarseScalar`.  The four-point triangle estimate is kept as
a local wrapper because its existing occurrence in `OrbitIGeometry` is
private; changing that green downstream file would force an unnecessary
rebuild of the repaired common selector.
-/

namespace Heilbronn8.QuadHull

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_zero
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) :
    h.toOrbitICoarseGeometryCertificate.labels 0 = A := by rfl

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_one
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) :
    h.toOrbitICoarseGeometryCertificate.labels 1 = B := by rfl

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_two
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) :
    h.toOrbitICoarseGeometryCertificate.labels 2 = C := by rfl

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_three
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) :
    h.toOrbitICoarseGeometryCertificate.labels 3 = D := by rfl

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_four
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) :
    h.toOrbitICoarseGeometryCertificate.labels 4 = h.P := by rfl

private def orbitICoarseScaleFirst (r : ℝ) (p : Point) : Point :=
  (r * p.1, p.2)

private lemma sig_orbitICoarseScaleFirst (r : ℝ) (p q s : Point) :
    sig (orbitICoarseScaleFirst r p) (orbitICoarseScaleFirst r q)
        (orbitICoarseScaleFirst r s) = r * sig p q s := by
  simp only [orbitICoarseScaleFirst, sig]
  ring

private lemma inTriStrict_orbitICoarseScaleFirst
    (r : ℝ) {P A B C : Point}
    (hP : TriHull.InTriStrict P A B C) :
    TriHull.InTriStrict (orbitICoarseScaleFirst r P)
      (orbitICoarseScaleFirst r A) (orbitICoarseScaleFirst r B)
      (orbitICoarseScaleFirst r C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hPe⟩ := hP
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hPe]
  simp only [orbitICoarseScaleFirst, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul]
  apply Prod.ext <;> simp <;> ring

private lemma orbitICoarse_normalized_minimum
    (v : Fin 8 → Point) (hm : 0 < minTri v) :
    TriHull.AllTrianglesMinAreaOne
      (fun i ↦ orbitICoarseScaleFirst (2 / minTri v) (v i)) := by
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
        (orbitICoarseScaleFirst (2 / minTri v) (v i))
        (orbitICoarseScaleFirst (2 / minTri v) (v j))
        (orbitICoarseScaleFirst (2 / minTri v) (v k))| := by
      rw [sig_orbitICoarseScaleFirst, abs_mul, abs_of_pos hrpos]

/-- Public local wrapper: a positive triangle containing four of the other
labels has normalized doubled area at least `21/2`. -/
theorem fourPointTriangle_normalized_lower_bound_coarse
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
  let w8 : Fin 8 → Point := fun i ↦ orbitICoarseScaleFirst r (v i)
  let w : Fin 7 → Point := fun i ↦ w8 (e i)
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have hw8min : TriHull.AllTrianglesMinAreaOne w8 := by
    simpa [w8, r] using orbitICoarse_normalized_minimum v hm
  have hwmin : TriHull.AllTrianglesMinAreaOne w := hw8min.comp e he
  have hwpos : 0 < sig (w 0) (w 1) (w 2) := by
    simpa only [w, w8, sig_orbitICoarseScaleFirst] using
      mul_pos hrpos hpos
  have hwP : TriHull.InTriStrict (w 3) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitICoarseScaleFirst r hP
  have hwQ : TriHull.InTriStrict (w 4) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitICoarseScaleFirst r hQ
  have hwR : TriHull.InTriStrict (w 5) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitICoarseScaleFirst r hR
  have hwS : TriHull.InTriStrict (w 6) (w 0) (w 1) (w 2) := by
    simpa only [w, w8] using inTriStrict_orbitICoarseScaleFirst r hS
  have hb := TriHull.th8_lemma4 TriHull.surcharge1_holds
    TriHull.surcharge2_holds w hwpos hwP hwQ hwR hwS hwmin
  have hscale : sig (w 0) (w 1) (w 2) =
      r * sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simp only [w, w8, sig_orbitICoarseScaleFirst]
  calc
    (21 : ℝ) / 2 ≤ sig (w 0) (w 1) (w 2) / 2 := hb
    _ = sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
      rw [hscale]
      dsimp [r]
      field_simp [ne_of_gt hm]

/-- The complete scalar packet before the three fan-cell occupancies are
counted. -/
noncomputable def OrbitISideMinimalGeometryCertificate.coarseFan
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    OrbitICoarseFan (orbitINormalizedHull v A B C D) := by
  let alpha := normalizedSig v h.P A B
  let beta := normalizedSig v h.P B C
  let gamma := normalizedSig v h.P C D
  let delta := normalizedSig v h.P D A
  let u := normalizedSig v h.P C A
  let t := normalizedSig v h.P B D
  let labels := h.toOrbitICoarseGeometryCertificate.labels
  have hlabels : Function.Injective labels := by
    simpa [labels, OrbitICoarseGeometryCertificate.labels] using
      h.labels_injective
  have unit_of_slots (i j k : Fin 8)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpos : 0 < sig (v (labels i)) (v (labels j)) (v (labels k))) :
      1 ≤ normalizedSig v (labels i) (labels j) (labels k) :=
    one_le_normalizedSig_of_pos v (labels i) (labels j) (labels k) hm
      (hlabels.ne hij) (hlabels.ne hik) (hlabels.ne hjk) hpos
  have hABCfan := TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC
  have hbetaPos := hABCfan.1
  have huPos := hABCfan.2.1
  have halphaPos := hABCfan.2.2
  have hDABfan := TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB
  have htPos := hDABfan.2.1
  have hdeltaPos := hDABfan.2.2
  have hgammaPos : 0 < sig (v h.P) (v C) (v D) := by
    rw [sig_rotate (v h.P) (v C) (v D)]
    exact orbitI_CD_pos_of_in_DAB h.ccw h.P_in_DAB
  have hABCfour :
      (21 : ℝ) / 2 ≤ sig (v A) (v B) (v C) / minTri v := by
    simpa [labels] using fourPointTriangle_normalized_lower_bound_coarse v
      ![A, B, C, h.P, h.Q, h.R, h.S]
      (by
        have hs : Function.Injective (![0, 1, 2, 4, 5, 6, 7] :
            Fin 7 → Fin 8) := by decide
        convert hlabels.comp hs using 1 <;>
          funext i <;> fin_cases i <;> rfl)
      hm h.ccw.1 h.P_in_ABC h.Q_in_ABC h.R_in_ABC h.S_in_ABC
  have hDABfour :
      (21 : ℝ) / 2 ≤ sig (v D) (v A) (v B) / minTri v := by
    simpa [labels] using fourPointTriangle_normalized_lower_bound_coarse v
      ![D, A, B, h.P, h.Q, h.R, h.S]
      (by
        have hs : Function.Injective (![3, 0, 1, 4, 5, 6, 7] :
            Fin 7 → Fin 8) := by decide
        convert hlabels.comp hs using 1 <;>
          funext i <;> fin_cases i <;> rfl)
      hm h.ccw.2.2.2 h.P_in_DAB h.Q_in_DAB h.R_in_DAB h.S_in_DAB
  refine
    { alpha := alpha, beta := beta, gamma := gamma, delta := delta
      u := u, t := t
      hull_eq := ?_
      alpha_unit := ?_
      beta_unit := ?_
      gamma_unit := ?_
      delta_unit := ?_
      u_unit := ?_
      t_unit := ?_
      plucker := ?_
      diagonal_AC := ?_
      diagonal_BD := ?_ }
  · dsimp [orbitINormalizedHull, normalizedSig, alpha, beta, gamma, delta]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  · simpa [alpha, labels] using
      unit_of_slots 4 0 1 (by decide) (by decide) (by decide) halphaPos
  · simpa [beta, labels] using
      unit_of_slots 4 1 2 (by decide) (by decide) (by decide) hbetaPos
  · simpa [gamma, labels] using
      unit_of_slots 4 2 3 (by decide) (by decide) (by decide) hgammaPos
  · simpa [delta, labels] using
      unit_of_slots 4 3 0 (by decide) (by decide) (by decide) hdeltaPos
  · simpa [u, labels] using
      unit_of_slots 4 2 0 (by decide) (by decide) (by decide) huPos
  · simpa [t, labels] using
      unit_of_slots 4 1 3 (by decide) (by decide) (by decide) htPos
  · dsimp [alpha, beta, gamma, delta, u, t, normalizedSig]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  · have hid : sig (v A) (v B) (v C) / minTri v =
        alpha + beta + u := by
      dsimp [alpha, beta, u, normalizedSig]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    linarith
  · have hid : sig (v D) (v A) (v B) / minTri v =
        alpha + delta + t := by
      dsimp [alpha, delta, t, normalizedSig]
      field_simp [ne_of_gt hm]
      simp only [sig]
      ring
    linarith

@[simp] lemma OrbitISideMinimalGeometryCertificate.coarseFan_alpha
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.coarseFan hm).alpha = normalizedSig v h.P A B := by
  simp [OrbitISideMinimalGeometryCertificate.coarseFan]

@[simp] lemma OrbitISideMinimalGeometryCertificate.coarseFan_gamma
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.coarseFan hm).gamma = normalizedSig v h.P C D := by
  simp [OrbitISideMinimalGeometryCertificate.coarseFan]

@[simp] lemma OrbitISideMinimalGeometryCertificate.coarseFan_delta
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (hm : 0 < minTri v) :
    (h.coarseFan hm).delta = normalizedSig v h.P D A := by
  simp [OrbitISideMinimalGeometryCertificate.coarseFan]

/-! ## Normalized floors from proof-relevant fan occupancy -/

private def orbitISideCellSlot
    (cell : OrbitISideFanCell) : Fin 3 → Fin 8 :=
  match cell with
  | .alpha => ![4, 0, 1]
  | .gamma => ![4, 2, 3]
  | .delta => ![4, 3, 0]

private def orbitISideCandidateSlot (i : Fin 3) : Fin 8 :=
  ⟨5 + i.val, by omega⟩

private def orbitISideOneSlots
    (cell : OrbitISideFanCell) (i : Fin 3) : Fin 4 → Fin 8 :=
  fun n ↦
    match n.val with
    | 0 => orbitISideCellSlot cell 0
    | 1 => orbitISideCellSlot cell 1
    | 2 => orbitISideCellSlot cell 2
    | _ => orbitISideCandidateSlot i

private def orbitISideTwoSlots
    (cell : OrbitISideFanCell) (i j : Fin 3) : Fin 5 → Fin 8 :=
  fun n ↦
    match n.val with
    | 0 => orbitISideCellSlot cell 0
    | 1 => orbitISideCellSlot cell 1
    | 2 => orbitISideCellSlot cell 2
    | 3 => orbitISideCandidateSlot i
    | _ => orbitISideCandidateSlot j

private def orbitISideThreeSlots
    (cell : OrbitISideFanCell) : Fin 6 → Fin 8 :=
  fun n ↦
    match n.val with
    | 0 => orbitISideCellSlot cell 0
    | 1 => orbitISideCellSlot cell 1
    | 2 => orbitISideCellSlot cell 2
    | 3 => orbitISideCandidateSlot 0
    | 4 => orbitISideCandidateSlot 1
    | _ => orbitISideCandidateSlot 2

private lemma orbitISideOneSlots_injective
    (cell : OrbitISideFanCell) (i : Fin 3) :
    Function.Injective (orbitISideOneSlots cell i) := by
  fin_cases cell <;> fin_cases i <;> decide

private lemma orbitISideTwoSlots_injective
    (cell : OrbitISideFanCell) {i j : Fin 3} (hij : i ≠ j) :
    Function.Injective (orbitISideTwoSlots cell i j) := by
  fin_cases cell <;> fin_cases i <;> fin_cases j <;>
    simp_all [orbitISideTwoSlots, orbitISideCellSlot,
      orbitISideCandidateSlot] <;> decide

private lemma orbitISideThreeSlots_injective
    (cell : OrbitISideFanCell) :
    Function.Injective (orbitISideThreeSlots cell) := by
  fin_cases cell <;> decide

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_candidateSlot
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) (i : Fin 3) :
    h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCandidateSlot i) = h.candidate i := by
  fin_cases i <;> rfl

@[simp] private lemma OrbitISideMinimalGeometryCertificate.labels_cellSlot
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (cell : OrbitISideFanCell) (i : Fin 3) :
    h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell i) =
      match cell, i.val with
      | .alpha, 0 => h.P
      | .alpha, 1 => A
      | .alpha, _ => B
      | .gamma, 0 => h.P
      | .gamma, 1 => C
      | .gamma, _ => D
      | .delta, 0 => h.P
      | .delta, 1 => D
      | .delta, _ => A := by
  fin_cases cell <;> fin_cases i <;> rfl

/-- The normalized area of one of the three surviving fan cells. -/
noncomputable def OrbitISideFanCell.normalizedArea
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (cell : OrbitISideFanCell) : ℝ :=
  match cell with
  | .alpha => normalizedSig v h.P A B
  | .gamma => normalizedSig v h.P C D
  | .delta => normalizedSig v h.P D A

private lemma OrbitISideMinimalGeometryCertificate.cell_pos
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (cell : OrbitISideFanCell) :
    0 < sig
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell 0)))
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell 1)))
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell 2))) := by
  fin_cases cell
  · change 0 < sig (v h.P) (v A) (v B)
    exact (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).2.2
  · change 0 < sig (v h.P) (v C) (v D)
    rw [sig_rotate (v h.P) (v C) (v D)]
    exact orbitI_CD_pos_of_in_DAB h.ccw h.P_in_DAB
  · change 0 < sig (v h.P) (v D) (v A)
    exact (TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB).2.2

private lemma OrbitISideFanAssignment.realizes_as_slots
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitISideMinimalGeometryCertificate v A B C D}
    (a : OrbitISideFanAssignment h) {i : Fin 3}
    {cell : OrbitISideFanCell} (hi : a.cell i = cell) :
    TriHull.InTriStrict
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCandidateSlot i)))
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell 0)))
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell 1)))
      (v (h.toOrbitICoarseGeometryCertificate.labels
        (orbitISideCellSlot cell 2))) := by
  have hr := a.realizes i
  rw [hi] at hr
  fin_cases cell <;>
    simpa [OrbitISideFanCell.Holds] using hr

/-- One point in a fan cell gives the normalized floor `3`. -/
theorem OrbitISideFanAssignment.onePointFloor
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitISideMinimalGeometryCertificate v A B C D}
    (a : OrbitISideFanAssignment h) (hm : 0 < minTri v)
    {cell : OrbitISideFanCell} {i : Fin 3}
    (hi : a.cell i = cell) :
    3 ≤ cell.normalizedArea h := by
  let labels := h.toOrbitICoarseGeometryCertificate.labels
  let slots := orbitISideOneSlots cell i
  let e : Fin 4 → Fin 8 := fun n ↦ labels (slots n)
  have hlabels : Function.Injective labels := by
    simpa [labels, OrbitICoarseGeometryCertificate.labels] using
      h.labels_injective
  have he : Function.Injective e :=
    hlabels.comp (orbitISideOneSlots_injective cell i)
  let w : OrbitIOnePointWitness v (e 0) (e 1) (e 2) :=
    { q := e 3
      labels_injective := by
        intro x y hxy
        apply he
        fin_cases x <;> fin_cases y <;>
          simpa [e, slots, orbitIOnePointLabels] using hxy
      q_in_triangle := by
        simpa [e, slots, orbitISideOneSlots, labels] using
          a.realizes_as_slots hi }
  have hb := w.three_le hm (by
    simpa [e, slots, orbitISideOneSlots, labels] using h.cell_pos cell)
  fin_cases cell <;>
    simpa [OrbitISideFanCell.normalizedArea, e, slots,
      orbitISideOneSlots, labels] using hb

/-- Two points in a fan cell give the strict rational floor `149/20`. -/
theorem OrbitISideFanAssignment.twoPointFloor
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitISideMinimalGeometryCertificate v A B C D}
    (a : OrbitISideFanAssignment h) (hm : 0 < minTri v)
    {cell : OrbitISideFanCell} {i j : Fin 3} (hij : i ≠ j)
    (hi : a.cell i = cell) (hj : a.cell j = cell) :
    (149 : ℝ) / 20 < cell.normalizedArea h := by
  let labels := h.toOrbitICoarseGeometryCertificate.labels
  let slots := orbitISideTwoSlots cell i j
  let e : Fin 5 → Fin 8 := fun n ↦ labels (slots n)
  have hlabels : Function.Injective labels := by
    simpa [labels, OrbitICoarseGeometryCertificate.labels] using
      h.labels_injective
  have he : Function.Injective e :=
    hlabels.comp (orbitISideTwoSlots_injective cell hij)
  have hb := TriHull.twoPointTriangle_normalized_lower_bound v e he hm
    (by simpa [e, slots, orbitISideTwoSlots, labels] using h.cell_pos cell)
    (by simpa [e, slots, orbitISideTwoSlots, labels] using
      a.realizes_as_slots hi)
    (by simpa [e, slots, orbitISideTwoSlots, labels] using
      a.realizes_as_slots hj)
  have hsqrt := TriHull.sixty_nine_fortieths_lt_sqrt_three
  have hb' : 4 + 2 * Real.sqrt 3 ≤ cell.normalizedArea h := by
    fin_cases cell <;>
      simpa [OrbitISideFanCell.normalizedArea, e, slots,
        orbitISideTwoSlots, labels, normalizedSig] using hb
  norm_num at hsqrt ⊢
  nlinarith

/-- All three points in one fan cell give the normalized floor `17/2`. -/
theorem OrbitISideFanAssignment.threePointFloor
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitISideMinimalGeometryCertificate v A B C D}
    (a : OrbitISideFanAssignment h) (hm : 0 < minTri v)
    {cell : OrbitISideFanCell}
    (h0 : a.cell 0 = cell) (h1 : a.cell 1 = cell)
    (h2 : a.cell 2 = cell) :
    (17 : ℝ) / 2 ≤ cell.normalizedArea h := by
  let labels := h.toOrbitICoarseGeometryCertificate.labels
  let slots := orbitISideThreeSlots cell
  let e : Fin 6 → Fin 8 := fun n ↦ labels (slots n)
  have hlabels : Function.Injective labels := by
    simpa [labels, OrbitICoarseGeometryCertificate.labels] using
      h.labels_injective
  have he : Function.Injective e :=
    hlabels.comp (orbitISideThreeSlots_injective cell)
  have hb := TriHull.threePointTriangle_normalized_lower_bound_unconditional
    v e he hm
    (by simpa [e, slots, orbitISideThreeSlots, labels] using h.cell_pos cell)
    (by simpa [e, slots, orbitISideThreeSlots, labels] using
      a.realizes_as_slots h0)
    (by simpa [e, slots, orbitISideThreeSlots, labels] using
      a.realizes_as_slots h1)
    (by simpa [e, slots, orbitISideThreeSlots, labels] using
      a.realizes_as_slots h2)
  fin_cases cell <;>
    simpa [OrbitISideFanCell.normalizedArea, e, slots,
      orbitISideThreeSlots, labels, normalizedSig] using hb

end Heilbronn8.QuadHull
