import Heilbronn8.QuadHull.ClassificationInterface
import Heilbronn8.QuadHull.SectorGeometry
import Heilbronn8.QuadHull.OrbitICoarseScalar
import Heilbronn8.TriHull.Bridge

/-!
# Geometric reduction for coarse orbit I

This module begins the producer for sector census `(4,0,0,0)`.  It performs
the finite side-minimal relabelling, proves strict descent inside `PBC`, and
assigns each of the other three points to one of the only three possible fan
cells `PAB`, `PCD`, `PDA`.  The scalar nine-row dispatcher lives in
`OrbitICoarseScalar`.

The global four-hull label selection and the early `minTri = 0` branch are
intentionally outside this module.
-/

namespace Heilbronn8.QuadHull

/-! ## Relabelling the four coarse inner points -/

@[simp] def OrbitICoarseGeometryCertificate.inner
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D) : Fin 4 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => h.P
    | 1 => h.Q
    | 2 => h.R
    | _ => h.S

def OrbitICoarseGeometryCertificate.labels
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D) : Fin 8 → Fin 8 :=
  quadLabels A B C D h.P h.Q h.R h.S

private def orbitICoarseInnerSlot (i : Fin 4) : Fin 8 :=
  ⟨4 + i.val, by omega⟩

private def orbitICoarseRelabelSlot
    (e : Equiv.Perm (Fin 4)) : Fin 8 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => orbitICoarseInnerSlot (e 0)
    | 5 => orbitICoarseInnerSlot (e 1)
    | 6 => orbitICoarseInnerSlot (e 2)
    | _ => orbitICoarseInnerSlot (e 3)

@[simp] private lemma orbitICoarseRelabelSlot_inner
    (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    orbitICoarseRelabelSlot e (orbitICoarseInnerSlot i) =
      orbitICoarseInnerSlot (e i) := by
  fin_cases i <;> rfl

private lemma orbitICoarseRelabelSlot_leftInverse
    (e : Equiv.Perm (Fin 4)) (i : Fin 8) :
    orbitICoarseRelabelSlot e.symm (orbitICoarseRelabelSlot e i) = i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change orbitICoarseRelabelSlot e.symm
      (orbitICoarseInnerSlot (e 0)) = _
    rw [orbitICoarseRelabelSlot_inner, Equiv.symm_apply_apply]
    rfl
  · change orbitICoarseRelabelSlot e.symm
      (orbitICoarseInnerSlot (e 1)) = _
    rw [orbitICoarseRelabelSlot_inner, Equiv.symm_apply_apply]
    rfl
  · change orbitICoarseRelabelSlot e.symm
      (orbitICoarseInnerSlot (e 2)) = _
    rw [orbitICoarseRelabelSlot_inner, Equiv.symm_apply_apply]
    rfl
  · change orbitICoarseRelabelSlot e.symm
      (orbitICoarseInnerSlot (e 3)) = _
    rw [orbitICoarseRelabelSlot_inner, Equiv.symm_apply_apply]
    rfl

private lemma orbitICoarseRelabelSlot_injective
    (e : Equiv.Perm (Fin 4)) :
    Function.Injective (orbitICoarseRelabelSlot e) := by
  intro i j hij
  have h := congrArg (orbitICoarseRelabelSlot e.symm) hij
  simpa only [orbitICoarseRelabelSlot_leftInverse] using h

@[simp] private lemma OrbitICoarseGeometryCertificate.labels_innerSlot
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D) (i : Fin 4) :
    h.labels (orbitICoarseInnerSlot i) = h.inner i := by
  fin_cases i <;> rfl

private lemma orbitICoarseRelabelLabels_apply
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D)
    (e : Equiv.Perm (Fin 4)) (i : Fin 8) :
    quadLabels A B C D (h.inner (e 0)) (h.inner (e 1))
        (h.inner (e 2)) (h.inner (e 3)) i =
      h.labels (orbitICoarseRelabelSlot e i) := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change h.inner (e 0) = h.labels (orbitICoarseInnerSlot (e 0))
    exact (h.labels_innerSlot (e 0)).symm
  · change h.inner (e 1) = h.labels (orbitICoarseInnerSlot (e 1))
    exact (h.labels_innerSlot (e 1)).symm
  · change h.inner (e 2) = h.labels (orbitICoarseInnerSlot (e 2))
    exact (h.labels_innerSlot (e 2)).symm
  · change h.inner (e 3) = h.labels (orbitICoarseInnerSlot (e 3))
    exact (h.labels_innerSlot (e 3)).symm

private lemma OrbitICoarseGeometryCertificate.inner_in_ABC
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D) (i : Fin 4) :
    TriHull.InTriStrict (v (h.inner i)) (v A) (v B) (v C) := by
  fin_cases i
  · exact h.P_in_ABC
  · exact h.Q_in_ABC
  · exact h.R_in_ABC
  · exact h.S_in_ABC

private lemma OrbitICoarseGeometryCertificate.inner_in_DAB
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D) (i : Fin 4) :
    TriHull.InTriStrict (v (h.inner i)) (v D) (v A) (v B) := by
  fin_cases i
  · exact h.P_in_DAB
  · exact h.Q_in_DAB
  · exact h.R_in_DAB
  · exact h.S_in_DAB

/-- Relabel all four inner points by a finite permutation. -/
def OrbitICoarseGeometryCertificate.relabel
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D)
    (e : Equiv.Perm (Fin 4)) :
    OrbitICoarseGeometryCertificate v A B C D where
  P := h.inner (e 0)
  Q := h.inner (e 1)
  R := h.inner (e 2)
  S := h.inner (e 3)
  labels_injective := by
    intro i j hij
    have hij' :
        h.labels (orbitICoarseRelabelSlot e i) =
          h.labels (orbitICoarseRelabelSlot e j) := by
      rw [← orbitICoarseRelabelLabels_apply h e i,
        ← orbitICoarseRelabelLabels_apply h e j]
      exact hij
    exact orbitICoarseRelabelSlot_injective e
      (h.labels_injective hij')
  ccw := h.ccw
  P_in_ABC := h.inner_in_ABC (e 0)
  Q_in_ABC := h.inner_in_ABC (e 1)
  R_in_ABC := h.inner_in_ABC (e 2)
  S_in_ABC := h.inner_in_ABC (e 3)
  P_in_DAB := h.inner_in_DAB (e 0)
  Q_in_DAB := h.inner_in_DAB (e 1)
  R_in_DAB := h.inner_in_DAB (e 2)
  S_in_DAB := h.inner_in_DAB (e 3)

/-! ## Side-minimal selection and strict descent -/

/-- A coarse packet whose distinguished point minimizes the `PBC` fan
area among the four inner labels. -/
structure OrbitISideMinimalGeometryCertificate
    (v : Fin 8 → Point) (A B C D : Fin 8)
    extends OrbitICoarseGeometryCertificate v A B C D where
  min_Q : sig (v P) (v B) (v C) ≤ sig (v Q) (v B) (v C)
  min_R : sig (v P) (v B) (v C) ≤ sig (v R) (v B) (v C)
  min_S : sig (v P) (v B) (v C) ≤ sig (v S) (v B) (v C)

/-- Every coarse packet admits a side-minimal relabelling. -/
noncomputable def OrbitICoarseGeometryCertificate.sideMinimal
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICoarseGeometryCertificate v A B C D) :
    OrbitISideMinimalGeometryCertificate v A B C D := by
  classical
  let hexists :=
    Finset.exists_min_image
      (Finset.univ : Finset (Fin 4))
      (fun i ↦ sig (v (h.inner i)) (v B) (v C))
      Finset.univ_nonempty
  let p : Fin 4 := Classical.choose hexists
  have hpmin : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      sig (v (h.inner p)) (v B) (v C) ≤
        sig (v (h.inner i)) (v B) (v C) :=
    (Classical.choose_spec hexists).2
  let e : Equiv.Perm (Fin 4) := Equiv.swap 0 p
  let g := h.relabel e
  have he0 : e 0 = p := by simp [e]
  refine
    { g with
      min_Q := ?_
      min_R := ?_
      min_S := ?_ }
  · simpa only [g, OrbitICoarseGeometryCertificate.relabel, he0] using
      hpmin (e 1) (Finset.mem_univ _)
  · simpa only [g, OrbitICoarseGeometryCertificate.relabel, he0] using
      hpmin (e 2) (Finset.mem_univ _)
  · simpa only [g, OrbitICoarseGeometryCertificate.relabel, he0] using
      hpmin (e 3) (Finset.mem_univ _)

/-- A strict point of `PBC` has strictly smaller `BC`-fan area than `P`. -/
theorem sig_BC_lt_of_in_PBC {X P B C : Point}
    (hPBC : 0 < sig P B C)
    (hX : TriHull.InTriStrict X P B C) :
    sig X B C < sig P B C := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hXe⟩ := hX
  have hxlt : x < 1 := by linarith
  rw [hXe, sig_affine_fst P B C B C x y z hsum]
  simp only [sig_eq12, sig_eq13, mul_zero, add_zero]
  nlinarith

@[simp] def OrbitISideMinimalGeometryCertificate.candidate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) :
    Fin 3 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => h.Q
    | 1 => h.R
    | _ => h.S

private lemma OrbitISideMinimalGeometryCertificate.candidate_in_ABC
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) (i : Fin 3) :
    TriHull.InTriStrict (v (h.candidate i)) (v A) (v B) (v C) := by
  fin_cases i
  · exact h.Q_in_ABC
  · exact h.R_in_ABC
  · exact h.S_in_ABC

private lemma OrbitISideMinimalGeometryCertificate.candidate_in_DAB
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) (i : Fin 3) :
    TriHull.InTriStrict (v (h.candidate i)) (v D) (v A) (v B) := by
  fin_cases i
  · exact h.Q_in_DAB
  · exact h.R_in_DAB
  · exact h.S_in_DAB

private lemma OrbitISideMinimalGeometryCertificate.candidate_min
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) (i : Fin 3) :
    sig (v h.P) (v B) (v C) ≤
      sig (v (h.candidate i)) (v B) (v C) := by
  fin_cases i
  · exact h.min_Q
  · exact h.min_R
  · exact h.min_S

/-- Side minimality rules out the `PBC` fan cell for every other point. -/
theorem OrbitISideMinimalGeometryCertificate.candidate_not_in_PBC
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) (i : Fin 3) :
    ¬ TriHull.InTriStrict (v (h.candidate i))
      (v h.P) (v B) (v C) := by
  intro hin
  have hPBC : 0 < sig (v h.P) (v B) (v C) :=
    (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).1
  exact (not_lt_of_ge (h.candidate_min i))
    (sig_BC_lt_of_in_PBC hPBC hin)

/-! ## The three surviving fan cells -/

inductive OrbitISideFanCell where
  | alpha
  | gamma
  | delta
  deriving DecidableEq

@[reducible] instance : Fintype OrbitISideFanCell where
  elems := {.alpha, .gamma, .delta}
  complete := by
    intro cell
    cases cell <;> simp

def OrbitISideFanCell.Holds
    (cell : OrbitISideFanCell)
    (X P A B C D : Point) : Prop :=
  match cell with
  | .alpha => TriHull.InTriStrict X P A B
  | .gamma => TriHull.InTriStrict X P C D
  | .delta => TriHull.InTriStrict X P D A

/-- Every remaining point has a proof-relevant assignment to `alpha`,
`gamma`, or `delta`.  The intermediate `PCA` witness is retained in the
`delta` branch, which is exactly what the common residual later needs. -/
theorem OrbitISideMinimalGeometryCertificate.fanCell_exists
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) (i : Fin 3) :
    ∃ cell : OrbitISideFanCell,
      OrbitISideFanCell.Holds cell (v (h.candidate i))
        (v h.P) (v A) (v B) (v C) (v D) ∧
      (cell = .delta →
        TriHull.InTriStrict (v (h.candidate i))
          (v h.P) (v C) (v A)) := by
  let X := h.candidate i
  have hlabels : Function.Injective h.toOrbitICoarseGeometryCertificate.labels := by
    simpa [OrbitICoarseGeometryCertificate.labels] using h.labels_injective
  have hP_ne_A : h.P ≠ A := by
    exact hlabels.ne (show (4 : Fin 8) ≠ 0 by decide)
  have hP_ne_B : h.P ≠ B := by
    exact hlabels.ne (show (4 : Fin 8) ≠ 1 by decide)
  have hP_ne_C : h.P ≠ C := by
    exact hlabels.ne (show (4 : Fin 8) ≠ 2 by decide)
  have hP_ne_D : h.P ≠ D := by
    exact hlabels.ne (show (4 : Fin 8) ≠ 3 by decide)
  have hX_ne_P : X ≠ h.P := by
    fin_cases i
    · exact hlabels.ne (show (5 : Fin 8) ≠ 4 by decide)
    · exact hlabels.ne (show (6 : Fin 8) ≠ 4 by decide)
    · exact hlabels.ne (show (7 : Fin 8) ≠ 4 by decide)
  have hX_ne_A : X ≠ A := by
    fin_cases i
    · exact hlabels.ne (show (5 : Fin 8) ≠ 0 by decide)
    · exact hlabels.ne (show (6 : Fin 8) ≠ 0 by decide)
    · exact hlabels.ne (show (7 : Fin 8) ≠ 0 by decide)
  have hX_ne_B : X ≠ B := by
    fin_cases i
    · exact hlabels.ne (show (5 : Fin 8) ≠ 1 by decide)
    · exact hlabels.ne (show (6 : Fin 8) ≠ 1 by decide)
    · exact hlabels.ne (show (7 : Fin 8) ≠ 1 by decide)
  have hX_ne_C : X ≠ C := by
    fin_cases i
    · exact hlabels.ne (show (5 : Fin 8) ≠ 2 by decide)
    · exact hlabels.ne (show (6 : Fin 8) ≠ 2 by decide)
    · exact hlabels.ne (show (7 : Fin 8) ≠ 2 by decide)
  have hX_ne_D : X ≠ D := by
    fin_cases i
    · exact hlabels.ne (show (5 : Fin 8) ≠ 3 by decide)
    · exact hlabels.ne (show (6 : Fin 8) ≠ 3 by decide)
    · exact hlabels.ne (show (7 : Fin 8) ≠ 3 by decide)
  have hPAX : sig (v h.P) (v A) (v X) ≠ 0 :=
    sig_ne_zero_of_minTri_ne_zero hmzero hP_ne_A
      hX_ne_P.symm hX_ne_A.symm
  have hPBX : sig (v h.P) (v B) (v X) ≠ 0 :=
    sig_ne_zero_of_minTri_ne_zero hmzero hP_ne_B
      hX_ne_P.symm hX_ne_B.symm
  have hPCXne : sig (v h.P) (v C) (v X) ≠ 0 :=
    sig_ne_zero_of_minTri_ne_zero hmzero hP_ne_C
      hX_ne_P.symm hX_ne_C.symm
  have hPDXne : sig (v h.P) (v D) (v X) ≠ 0 :=
    sig_ne_zero_of_minTri_ne_zero hmzero hP_ne_D
      hX_ne_P.symm hX_ne_D.symm
  rcases TriHull.strict_fan_partition h.P_in_ABC (h.candidate_in_ABC i)
      hPAX hPBX hPCXne with hbeta | hPCA | halpha
  · exact False.elim ((h.candidate_not_in_PBC i) hbeta)
  · have hPCApos : 0 < sig (v h.P) (v C) (v A) :=
      (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).2.1
    obtain ⟨hXCA, hXAP, hXPC⟩ :=
      TriHull.inTriStrict_fan_pos hPCApos hPCA
    have hPXA : 0 < sig (v h.P) (v X) (v A) := by
      calc
        0 < sig (v X) (v A) (v h.P) := hXAP
        _ = sig (v A) (v h.P) (v X) := sig_rotate _ _ _
        _ = sig (v h.P) (v X) (v A) := sig_rotate _ _ _
    have hPCX : 0 < sig (v h.P) (v C) (v X) := by
      calc
        0 < sig (v X) (v h.P) (v C) := hXPC
        _ = sig (v h.P) (v C) (v X) := sig_rotate _ _ _
    have hPDApos : 0 < sig (v h.P) (v D) (v A) :=
      (TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB).2.2
    obtain ⟨_, _, hXDA⟩ :=
      TriHull.inTriStrict_fan_pos h.ccw.2.2.2 (h.candidate_in_DAB i)
    by_cases hPDX : 0 < sig (v h.P) (v D) (v X)
    · have hPDA : TriHull.InTriStrict (v X)
          (v h.P) (v D) (v A) :=
        OrbitIIInternal.inTriStrict_of_fan_pos
          hPDApos hXDA hPXA hPDX
      exact ⟨.delta, hPDA, fun _ ↦ hPCA⟩
    · have hPDXneg : sig (v h.P) (v D) (v X) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hPDX) hPDXne
      have hPXD : 0 < sig (v h.P) (v X) (v D) := by
        rw [sig_swap]
        linarith
      have hACDpos : 0 < sig (v A) (v C) (v D) := by
        calc
          0 < sig (v C) (v D) (v A) := h.ccw.2.2.1
          _ = sig (v D) (v A) (v C) := sig_rotate _ _ _
          _ = sig (v A) (v C) (v D) := sig_rotate _ _ _
      have hPCDpos : 0 < sig (v h.P) (v C) (v D) := by
        obtain ⟨px, py, pz, _hpx, hpy, hpz, hpsum, hPe⟩ := h.P_in_DAB
        rw [hPe, sig_affine_fst (v D) (v A) (v B)
          (v C) (v D) px py pz hpsum]
        simp only [sig_eq13, mul_zero, zero_add]
        exact add_pos (mul_pos hpy hACDpos) (mul_pos hpz h.ccw.2.1)
      have hXCD : 0 < sig (v X) (v C) (v D) := by
        obtain ⟨xx, xy, xz, _hxx, hxy, hxz, hxsum, hXe⟩ :=
          h.candidate_in_DAB i
        rw [hXe, sig_affine_fst (v D) (v A) (v B)
          (v C) (v D) xx xy xz hxsum]
        simp only [sig_eq13, mul_zero, zero_add]
        exact add_pos (mul_pos hxy hACDpos) (mul_pos hxz h.ccw.2.1)
      have hPCD : TriHull.InTriStrict (v X)
          (v h.P) (v C) (v D) :=
        OrbitIIInternal.inTriStrict_of_fan_pos
          hPCDpos hXCD hPXD hPCX
      exact ⟨.gamma, hPCD, by simp⟩
  · exact ⟨.alpha, halpha, by simp⟩

/-- The three pointwise fan choices, with their geometric witnesses retained
for the scalar floor constructors and for the all-`delta` residual. -/
structure OrbitISideFanAssignment
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D) where
  cell : Fin 3 → OrbitISideFanCell
  realizes : ∀ i : Fin 3,
    OrbitISideFanCell.Holds (cell i) (v (h.candidate i))
      (v h.P) (v A) (v B) (v C) (v D)
  delta_in_PCA : ∀ i : Fin 3, cell i = .delta →
    TriHull.InTriStrict (v (h.candidate i))
      (v h.P) (v C) (v A)

/-- Package the three pointwise trichotomies into one finite assignment. -/
noncomputable def OrbitISideMinimalGeometryCertificate.fanAssignment
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitISideMinimalGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) : OrbitISideFanAssignment h := by
  classical
  have hex : ∀ i : Fin 3, ∃ cell : OrbitISideFanCell,
      OrbitISideFanCell.Holds cell (v (h.candidate i))
          (v h.P) (v A) (v B) (v C) (v D) ∧
        (cell = .delta →
          TriHull.InTriStrict (v (h.candidate i))
            (v h.P) (v C) (v A)) :=
    fun i ↦ h.fanCell_exists hmzero i
  choose cell hcell using hex
  exact
    { cell := cell
      realizes := fun i ↦ (hcell i).1
      delta_in_PCA := fun i ↦ (hcell i).2 }

/-- The sole non-direct fan row `(0,0,3)` is exactly the already-supported
common orbit-I geometry packet. -/
def OrbitISideFanAssignment.commonOfAllDelta
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitISideMinimalGeometryCertificate v A B C D}
    (a : OrbitISideFanAssignment h)
    (hall : ∀ i : Fin 3, a.cell i = .delta) :
    OrbitICommonGeometryCertificate v A B C D where
  P := h.P
  S := h.Q
  T := h.R
  R := h.S
  labels_injective := h.labels_injective
  ccw := h.ccw
  P_in_ABC := h.P_in_ABC
  S_in_ABC := h.Q_in_ABC
  T_in_ABC := h.R_in_ABC
  R_in_ABC := h.S_in_ABC
  P_in_DAB := h.P_in_DAB
  S_in_DAB := h.Q_in_DAB
  T_in_DAB := h.R_in_DAB
  R_in_DAB := h.S_in_DAB
  S_in_PCA := a.delta_in_PCA 0 (hall 0)
  T_in_PCA := a.delta_in_PCA 1 (hall 1)
  R_in_PCA := a.delta_in_PCA 2 (hall 2)
  S_in_PDA := by
    have hr := a.realizes 0
    simpa [OrbitISideFanCell.Holds, hall 0] using hr
  T_in_PDA := by
    have hr := a.realizes 1
    simpa [OrbitISideFanCell.Holds, hall 1] using hr
  R_in_PDA := by
    have hr := a.realizes 2
    simpa [OrbitISideFanCell.Holds, hall 2] using hr

end Heilbronn8.QuadHull
