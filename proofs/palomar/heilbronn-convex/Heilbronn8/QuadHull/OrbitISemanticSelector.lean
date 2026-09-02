import Heilbronn8.QuadHull.OrbitIGeometry
import Heilbronn8.QuadHull.OrbitIGeometryRows

/-!
# Compact semantic selector for Orbit I

The three residual points of the common Orbit I packet lie in each of the
two triangles `PCA` and `PDA`.  This file proves, without a generated case
table, that they can be relabelled into either one of the existing easy
geometric cases or the single cyclic case.

For one fan, write the three positive area coordinates of a point as
`(x,j,y)` and order the points by `x / j`.  An ordered pair has only three
possible reciprocal fan types.  If no point sees the other two in a common
cell, local cell distinctness leaves five triples of pair types.  Four give
a strict cycle in `y / j` or `x / y`; the remaining triple is the cyclic
order.  Passing from the `C` fan to the `D` fan preserves the `x` and `j`
cells, while a `y` cell splits into `x'` or `y'`.  One `x'` outcome is easy,
the reciprocal one is impossible, and the remaining outcome supplies the
ten one-point memberships of the analytic cyclic leaf.
-/

namespace Heilbronn8.QuadHull

private lemma inTriStrict_rotate {Q A B C : Point}
    (h : TriHull.InTriStrict Q A B C) :
    TriHull.InTriStrict Q B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hQ⟩ := h
  refine ⟨y, z, x, hy, hz, hx, by linarith, ?_⟩
  rw [hQ]
  module

private lemma inTriStrict_rotate_two {Q A B C : Point}
    (h : TriHull.InTriStrict Q A B C) :
    TriHull.InTriStrict Q C A B :=
  inTriStrict_rotate (inTriStrict_rotate h)

private lemma inTriStrict_of_fan_pos {Q A B C : Point}
    (hABC : 0 < sig A B C)
    (hQBC : 0 < sig Q B C)
    (hQCA : 0 < sig Q C A)
    (hQAB : 0 < sig Q A B) :
    TriHull.InTriStrict Q A B C := by
  have hne : sig A B C ≠ 0 := ne_of_gt hABC
  have hsum : sig Q B C + sig Q C A + sig Q A B = sig A B C := by
    simp only [sig]
    ring
  refine ⟨sig Q B C / sig A B C,
    sig Q C A / sig A B C,
    sig Q A B / sig A B C,
    div_pos hQBC hABC, div_pos hQCA hABC, div_pos hQAB hABC,
    ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hne]
  · apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp [hne]
      simp only [sig]
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp [hne]
      simp only [sig]
      ring

/-! ## Relabelling the three residual candidates -/

@[simp] def OrbitICommonGeometryCertificate.candidate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) : Fin 3 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => h.S
    | 1 => h.T
    | _ => h.R

private def orbitICandidateSlot : Fin 3 → Fin 8 :=
  fun i ↦ ⟨5 + i.val, by omega⟩

private def orbitIRelabelSlot
    (e : Equiv.Perm (Fin 3)) : Fin 8 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => orbitICandidateSlot (e 0)
    | 6 => orbitICandidateSlot (e 1)
    | _ => orbitICandidateSlot (e 2)

@[simp] private lemma orbitIRelabelSlot_candidate
    (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    orbitIRelabelSlot e (orbitICandidateSlot i) =
      orbitICandidateSlot (e i) := by
  fin_cases i <;> rfl

private lemma orbitIRelabelSlot_leftInverse
    (e : Equiv.Perm (Fin 3)) (i : Fin 8) :
    orbitIRelabelSlot e.symm (orbitIRelabelSlot e i) = i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change orbitIRelabelSlot e.symm (orbitICandidateSlot (e 0)) = _
    rw [orbitIRelabelSlot_candidate, Equiv.symm_apply_apply]
    rfl
  · change orbitIRelabelSlot e.symm (orbitICandidateSlot (e 1)) = _
    rw [orbitIRelabelSlot_candidate, Equiv.symm_apply_apply]
    rfl
  · change orbitIRelabelSlot e.symm (orbitICandidateSlot (e 2)) = _
    rw [orbitIRelabelSlot_candidate, Equiv.symm_apply_apply]
    rfl

private lemma orbitIRelabelSlot_injective
    (e : Equiv.Perm (Fin 3)) : Function.Injective (orbitIRelabelSlot e) := by
  intro i j hij
  have h := congrArg (orbitIRelabelSlot e.symm) hij
  simpa only [orbitIRelabelSlot_leftInverse] using h

@[simp] private lemma OrbitICommonGeometryCertificate.labels_candidateSlot
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) (i : Fin 3) :
    h.labels (orbitICandidateSlot i) = h.candidate i := by
  fin_cases i <;> rfl

private lemma orbitIRelabelLabels_apply
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (e : Equiv.Perm (Fin 3)) (i : Fin 8) :
    quadLabels A B C D h.P (h.candidate (e 0))
        (h.candidate (e 1)) (h.candidate (e 2)) i =
      h.labels (orbitIRelabelSlot e i) := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change h.candidate (e 0) = h.labels (orbitICandidateSlot (e 0))
    exact (h.labels_candidateSlot (e 0)).symm
  · change h.candidate (e 1) = h.labels (orbitICandidateSlot (e 1))
    exact (h.labels_candidateSlot (e 1)).symm
  · change h.candidate (e 2) = h.labels (orbitICandidateSlot (e 2))
    exact (h.labels_candidateSlot (e 2)).symm

private lemma OrbitICommonGeometryCertificate.candidate_in_ABC
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) (i : Fin 3) :
    TriHull.InTriStrict (v (h.candidate i)) (v A) (v B) (v C) := by
  fin_cases i
  · exact h.S_in_ABC
  · exact h.T_in_ABC
  · exact h.R_in_ABC

private lemma OrbitICommonGeometryCertificate.candidate_in_DAB
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) (i : Fin 3) :
    TriHull.InTriStrict (v (h.candidate i)) (v D) (v A) (v B) := by
  fin_cases i
  · exact h.S_in_DAB
  · exact h.T_in_DAB
  · exact h.R_in_DAB

private lemma OrbitICommonGeometryCertificate.candidate_in_PCA
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) (i : Fin 3) :
    TriHull.InTriStrict (v (h.candidate i)) (v h.P) (v C) (v A) := by
  fin_cases i
  · exact h.S_in_PCA
  · exact h.T_in_PCA
  · exact h.R_in_PCA

private lemma OrbitICommonGeometryCertificate.candidate_in_PDA
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) (i : Fin 3) :
    TriHull.InTriStrict (v (h.candidate i)) (v h.P) (v D) (v A) := by
  fin_cases i
  · exact h.S_in_PDA
  · exact h.T_in_PDA
  · exact h.R_in_PDA

/-- Relabel only the three residual candidates, keeping the selected point
`P` and the hull labels fixed. -/
def OrbitICommonGeometryCertificate.relabel
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (e : Equiv.Perm (Fin 3)) :
    OrbitICommonGeometryCertificate v A B C D where
  P := h.P
  S := h.candidate (e 0)
  T := h.candidate (e 1)
  R := h.candidate (e 2)
  labels_injective := by
    intro i j hij
    have hij' :
        h.labels (orbitIRelabelSlot e i) =
          h.labels (orbitIRelabelSlot e j) := by
      rw [← orbitIRelabelLabels_apply h e i,
        ← orbitIRelabelLabels_apply h e j]
      exact hij
    exact orbitIRelabelSlot_injective e (h.labels_injective hij')
  ccw := h.ccw
  P_in_ABC := h.P_in_ABC
  S_in_ABC := h.candidate_in_ABC (e 0)
  T_in_ABC := h.candidate_in_ABC (e 1)
  R_in_ABC := h.candidate_in_ABC (e 2)
  P_in_DAB := h.P_in_DAB
  S_in_DAB := h.candidate_in_DAB (e 0)
  T_in_DAB := h.candidate_in_DAB (e 1)
  R_in_DAB := h.candidate_in_DAB (e 2)
  S_in_PCA := h.candidate_in_PCA (e 0)
  T_in_PCA := h.candidate_in_PCA (e 1)
  R_in_PCA := h.candidate_in_PCA (e 2)
  S_in_PDA := h.candidate_in_PDA (e 0)
  T_in_PDA := h.candidate_in_PDA (e 1)
  R_in_PDA := h.candidate_in_PDA (e 2)

/-! The six orders are named explicitly so that later relabellings reduce
without retaining a vector-valued permutation term. -/

def orbitIOrder012 : Equiv.Perm (Fin 3) := Equiv.refl _
def orbitIOrder021 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def orbitIOrder102 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def orbitIOrder120 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
def orbitIOrder201 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1
def orbitIOrder210 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

@[simp] lemma orbitIOrder012_apply (i : Fin 3) : orbitIOrder012 i = i := rfl

@[simp] lemma orbitIOrder021_zero : orbitIOrder021 0 = 0 := rfl
@[simp] lemma orbitIOrder021_one : orbitIOrder021 1 = 2 := rfl
@[simp] lemma orbitIOrder021_two : orbitIOrder021 2 = 1 := rfl

@[simp] lemma orbitIOrder102_zero : orbitIOrder102 0 = 1 := rfl
@[simp] lemma orbitIOrder102_one : orbitIOrder102 1 = 0 := rfl
@[simp] lemma orbitIOrder102_two : orbitIOrder102 2 = 2 := rfl

@[simp] lemma orbitIOrder120_zero : orbitIOrder120 0 = 1 := rfl
@[simp] lemma orbitIOrder120_one : orbitIOrder120 1 = 2 := rfl
@[simp] lemma orbitIOrder120_two : orbitIOrder120 2 = 0 := rfl

@[simp] lemma orbitIOrder201_zero : orbitIOrder201 0 = 2 := rfl
@[simp] lemma orbitIOrder201_one : orbitIOrder201 1 = 0 := rfl
@[simp] lemma orbitIOrder201_two : orbitIOrder201 2 = 1 := rfl

@[simp] lemma orbitIOrder210_zero : orbitIOrder210 0 = 2 := rfl
@[simp] lemma orbitIOrder210_one : orbitIOrder210 1 = 1 := rfl
@[simp] lemma orbitIOrder210_two : orbitIOrder210 2 = 0 := rfl

/-! ## One-fan coordinates and reciprocal pair types -/

private noncomputable def fanX (P C X : Point) : ℝ := sig P C X
private noncomputable def fanJ (P A X : Point) : ℝ := sig P X A
private noncomputable def fanY (C A X : Point) : ℝ := sig X C A

private noncomputable def fanSlope (P C A X : Point) : ℝ :=
  fanX P C X / fanJ P A X

private noncomputable def fanB (P C A X : Point) : ℝ :=
  fanY C A X / fanJ P A X

private noncomputable def fanC (P C A X : Point) : ℝ :=
  fanX P C X / fanY C A X

private lemma fan_coordinates_pos {P C A X : Point}
    (hPCA : 0 < sig P C A)
    (hX : TriHull.InTriStrict X P C A) :
    0 < fanX P C X ∧ 0 < fanJ P A X ∧ 0 < fanY C A X := by
  obtain ⟨hy, hj, hx⟩ := TriHull.inTriStrict_fan_pos hPCA hX
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [fanX]
    calc
      0 < sig X P C := hx
      _ = sig P C X := sig_rotate _ _ _
  · dsimp only [fanJ]
    calc
      0 < sig X A P := hj
      _ = sig A P X := sig_rotate _ _ _
      _ = sig P X A := sig_rotate _ _ _
  · simpa only [fanY] using hy

private lemma fan_gap_P (P C A L H : Point) :
    fanX P C H * fanJ P A L - fanJ P A H * fanX P C L =
      sig P C A * sig P L H := by
  simp only [fanX, fanJ, sig]
  ring

private lemma fan_gap_A (P C A L H : Point) :
    fanJ P A H * fanY C A L - fanY C A H * fanJ P A L =
      sig P C A * sig A L H := by
  simp only [fanJ, fanY, sig]
  ring

private lemma fan_gap_C (P C A L H : Point) :
    fanY C A H * fanX P C L - fanX P C H * fanY C A L =
      sig P C A * sig C L H := by
  simp only [fanX, fanY, sig]
  ring

private lemma sig_PLH_pos_of_slope_lt {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (hslope : fanSlope P C A L < fanSlope P C A H) :
    0 < sig P L H := by
  obtain ⟨_, hjL, _⟩ := fan_coordinates_pos hPCA hL
  obtain ⟨_, hjH, _⟩ := fan_coordinates_pos hPCA hH
  have hcross :
      fanX P C L * fanJ P A H < fanX P C H * fanJ P A L := by
    exact (div_lt_div_iff₀ hjL hjH).mp hslope
  have hid := fan_gap_P P C A L H
  nlinarith

inductive OrbitIFanCell where
  | x
  | j
  | y
deriving DecidableEq, Repr

def OrbitIFanCell.Holds
    (cell : OrbitIFanCell) (Q X P Z A : Point) : Prop :=
  match cell with
  | .x => TriHull.InTriStrict Q P Z X
  | .j => TriHull.InTriStrict Q P X A
  | .y => TriHull.InTriStrict Q X Z A

inductive OrbitIFanPairTag where
  | A
  | B
  | C
deriving DecidableEq, Repr

/-- The three possible reciprocal cell patterns for a pair `L < H` in
`x / j` order. -/
inductive OrbitIFanPairType (P C A L H : Point) : Type
  | A
      (high_j : TriHull.InTriStrict H P L A)
      (low_x : TriHull.InTriStrict L P C H)
  | B
      (high_j : TriHull.InTriStrict H P L A)
      (low_y : TriHull.InTriStrict L H C A)
  | C
      (high_y : TriHull.InTriStrict H L C A)
      (low_x : TriHull.InTriStrict L P C H)

def OrbitIFanPairType.tag {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) : OrbitIFanPairTag :=
  match p with
  | .A _ _ => .A
  | .B _ _ => .B
  | .C _ _ => .C

def OrbitIFanPairTag.lowCell : OrbitIFanPairTag → OrbitIFanCell
  | .A => .j
  | .B => .j
  | .C => .y

def OrbitIFanPairTag.highCell : OrbitIFanPairTag → OrbitIFanCell
  | .A => .x
  | .B => .y
  | .C => .x

lemma OrbitIFanPairType.low_mem {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) :
    p.tag.lowCell.Holds H L P C A := by
  cases p with
  | A h _ => exact h
  | B h _ => exact h
  | C h _ => exact h

lemma OrbitIFanPairType.high_mem {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) :
    p.tag.highCell.Holds L H P C A := by
  cases p with
  | A _ h => exact h
  | B _ h => exact h
  | C _ h => exact h

private theorem ordered_pair_type_nonempty {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (hLPH : sig L P H ≠ 0)
    (hLCH : sig L C H ≠ 0)
    (hLAH : sig L A H ≠ 0)
    (hslope : fanSlope P C A L < fanSlope P C A H) :
    Nonempty (OrbitIFanPairType P C A L H) := by
  have hPLH := sig_PLH_pos_of_slope_lt hPCA hL hH hslope
  have high_not_x : ¬ TriHull.InTriStrict H P C L := by
    intro hcell
    have hPCL := (fan_coordinates_pos hPCA hL).1
    obtain ⟨_, hHLP, _⟩ := TriHull.inTriStrict_fan_pos hPCL hcell
    simp only [sig] at hHLP hPLH
    linarith
  have low_not_j : ¬ TriHull.InTriStrict L P H A := by
    intro hcell
    have hPHA := (fan_coordinates_pos hPCA hH).2.1
    obtain ⟨_, _, hLPH'⟩ := TriHull.inTriStrict_fan_pos hPHA hcell
    simp only [sig] at hLPH' hPLH
    linarith
  rcases TriHull.strict_fan_partition hL hH hLPH hLCH hLAH with
      hhighY | hhighJ | hhighX
  · rcases TriHull.strict_fan_partition hH hL
        (by
          intro hz
          apply hLPH
          simp only [sig] at hz ⊢
          linarith)
        (by
          intro hz
          apply hLCH
          simp only [sig] at hz ⊢
          linarith)
        (by
          intro hz
          apply hLAH
          simp only [sig] at hz ⊢
          linarith) with
        hlowY | hlowJ | hlowX
    · exfalso
      obtain ⟨_, hHAL, _⟩ :=
        TriHull.inTriStrict_fan_pos (fan_coordinates_pos hPCA hL).2.2 hhighY
      obtain ⟨_, hLAH', _⟩ :=
        TriHull.inTriStrict_fan_pos (fan_coordinates_pos hPCA hH).2.2 hlowY
      simp only [sig] at hHAL hLAH'
      linarith
    · exact False.elim (low_not_j (inTriStrict_rotate_two hlowJ))
    · exact ⟨.C hhighY (inTriStrict_rotate hlowX)⟩
  · have hhighJ' := inTriStrict_rotate_two hhighJ
    rcases TriHull.strict_fan_partition hH hL
        (by
          intro hz
          apply hLPH
          simp only [sig] at hz ⊢
          linarith)
        (by
          intro hz
          apply hLCH
          simp only [sig] at hz ⊢
          linarith)
        (by
          intro hz
          apply hLAH
          simp only [sig] at hz ⊢
          linarith) with
        hlowY | hlowJ | hlowX
    · exact ⟨.B hhighJ' hlowY⟩
    · exact False.elim (low_not_j (inTriStrict_rotate_two hlowJ))
    · exact ⟨.A hhighJ' (inTriStrict_rotate hlowX)⟩
  · exact False.elim (high_not_x (inTriStrict_rotate hhighX))

private noncomputable def ordered_pair_type {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (hLPH : sig L P H ≠ 0)
    (hLCH : sig L C H ≠ 0)
    (hLAH : sig L A H ≠ 0)
    (hslope : fanSlope P C A L < fanSlope P C A H) :
    OrbitIFanPairType P C A L H :=
  Classical.choice
    (ordered_pair_type_nonempty hPCA hL hH hLPH hLCH hLAH hslope)

private lemma OrbitIFanPairType.b_forward {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (p : OrbitIFanPairType P C A L H)
    (htag : p.tag ≠ .C) : fanB P C A L < fanB P C A H := by
  obtain ⟨_, hjL, _⟩ := fan_coordinates_pos hPCA hL
  obtain ⟨_, hjH, _⟩ := fan_coordinates_pos hPCA hH
  have hALH : sig A L H < 0 := by
    cases p with
    | A hJ _ =>
        obtain ⟨hHLA, _, _⟩ :=
          TriHull.inTriStrict_fan_pos
            (fan_coordinates_pos hPCA hL).2.1 hJ
        simp only [OrbitIFanPairType.tag, sig] at hHLA ⊢
        linarith
    | B hJ _ =>
        obtain ⟨hHLA, _, _⟩ :=
          TriHull.inTriStrict_fan_pos
            (fan_coordinates_pos hPCA hL).2.1 hJ
        simp only [OrbitIFanPairType.tag, sig] at hHLA ⊢
        linarith
    | C _ _ => exact (htag rfl).elim
  change fanY C A L / fanJ P A L < fanY C A H / fanJ P A H
  apply (div_lt_div_iff₀ hjL hjH).2
  have hid := fan_gap_A P C A L H
  nlinarith

private lemma OrbitIFanPairType.b_backward {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (p : OrbitIFanPairType P C A L H)
    (htag : p.tag = .C) : fanB P C A H < fanB P C A L := by
  obtain ⟨_, hjL, _⟩ := fan_coordinates_pos hPCA hL
  obtain ⟨_, hjH, _⟩ := fan_coordinates_pos hPCA hH
  have hALH : 0 < sig A L H := by
    cases p with
    | A _ _ => cases htag
    | B _ _ => cases htag
    | C hY _ =>
        obtain ⟨_, hHAL, _⟩ :=
          TriHull.inTriStrict_fan_pos
            (fan_coordinates_pos hPCA hL).2.2 hY
        calc
          0 < sig H A L := hHAL
          _ = sig A L H := sig_rotate _ _ _
  change fanY C A H / fanJ P A H < fanY C A L / fanJ P A L
  apply (div_lt_div_iff₀ hjH hjL).2
  have hid := fan_gap_A P C A L H
  nlinarith

private lemma OrbitIFanPairType.c_forward {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (p : OrbitIFanPairType P C A L H)
    (htag : p.tag ≠ .B) : fanC P C A L < fanC P C A H := by
  obtain ⟨_, _, hyL⟩ := fan_coordinates_pos hPCA hL
  obtain ⟨_, _, hyH⟩ := fan_coordinates_pos hPCA hH
  have hCLH : sig C L H < 0 := by
    cases p with
    | A _ hX =>
        obtain ⟨hLCH, _, _⟩ :=
          TriHull.inTriStrict_fan_pos
            (fan_coordinates_pos hPCA hH).1 hX
        simp only [OrbitIFanPairType.tag, sig] at hLCH ⊢
        linarith
    | B _ _ => exact (htag rfl).elim
    | C _ hX =>
        obtain ⟨hLCH, _, _⟩ :=
          TriHull.inTriStrict_fan_pos
            (fan_coordinates_pos hPCA hH).1 hX
        simp only [OrbitIFanPairType.tag, sig] at hLCH ⊢
        linarith
  change fanX P C L / fanY C A L < fanX P C H / fanY C A H
  apply (div_lt_div_iff₀ hyL hyH).2
  have hid := fan_gap_C P C A L H
  nlinarith

private lemma OrbitIFanPairType.c_backward {P C A L H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hH : TriHull.InTriStrict H P C A)
    (p : OrbitIFanPairType P C A L H)
    (htag : p.tag = .B) : fanC P C A H < fanC P C A L := by
  obtain ⟨_, _, hyL⟩ := fan_coordinates_pos hPCA hL
  obtain ⟨_, _, hyH⟩ := fan_coordinates_pos hPCA hH
  have hCLH : 0 < sig C L H := by
    cases p with
    | A _ _ => cases htag
    | B _ hY =>
        obtain ⟨_, _, hLHC⟩ :=
          TriHull.inTriStrict_fan_pos
            (fan_coordinates_pos hPCA hH).2.2 hY
        calc
          0 < sig L H C := hLHC
          _ = sig H C L := sig_rotate _ _ _
          _ = sig C L H := sig_rotate _ _ _
    | C _ _ => cases htag
  change fanX P C H / fanY C A H < fanX P C L / fanY C A L
  apply (div_lt_div_iff₀ hyH hyL).2
  have hid := fan_gap_C P C A L H
  nlinarith

/-! ## The five-pattern selector -/

private theorem five_pair_patterns
    (lm lh mh : OrbitIFanPairTag)
    (hL : lm.lowCell ≠ lh.lowCell)
    (hH : lh.highCell ≠ mh.highCell)
    (hM : lm.highCell ≠ mh.lowCell) :
    (lm = .A ∧ lh = .C ∧ mh = .B) ∨
    (lm = .B ∧ lh = .C ∧ mh = .B) ∨
    (lm = .C ∧ lh = .B ∧ mh = .A) ∨
    (lm = .C ∧ lh = .B ∧ mh = .C) ∨
    (lm = .C ∧ lh = .A ∧ mh = .B) := by
  cases lm <;> cases lh <;> cases mh <;>
    simp_all [OrbitIFanPairTag.lowCell, OrbitIFanPairTag.highCell]

private lemma OrbitIFanPairType.high_j_of_tag_A {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) (htag : p.tag = .A) :
    TriHull.InTriStrict H P L A := by
  cases p with
  | A h _ => exact h
  | B _ _ => cases htag
  | C _ _ => cases htag

private lemma OrbitIFanPairType.high_j_of_tag_B {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) (htag : p.tag = .B) :
    TriHull.InTriStrict H P L A := by
  cases p with
  | A _ _ => cases htag
  | B h _ => exact h
  | C _ _ => cases htag

private lemma OrbitIFanPairType.high_y_of_tag_C {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) (htag : p.tag = .C) :
    TriHull.InTriStrict H L C A := by
  cases p with
  | A _ _ => cases htag
  | B _ _ => cases htag
  | C h _ => exact h

private lemma OrbitIFanPairType.low_x_of_tag_A {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) (htag : p.tag = .A) :
    TriHull.InTriStrict L P C H := by
  cases p with
  | A _ h => exact h
  | B _ _ => cases htag
  | C _ _ => cases htag

private lemma OrbitIFanPairType.low_y_of_tag_B {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) (htag : p.tag = .B) :
    TriHull.InTriStrict L H C A := by
  cases p with
  | A _ _ => cases htag
  | B _ h => exact h
  | C _ _ => cases htag

private lemma OrbitIFanPairType.low_x_of_tag_C {P C A L H : Point}
    (p : OrbitIFanPairType P C A L H) (htag : p.tag = .C) :
    TriHull.InTriStrict L P C H := by
  cases p with
  | A _ _ => cases htag
  | B _ _ => cases htag
  | C _ h => exact h

/-! ## Cross-fan transport -/

private lemma orbitI_CD_pos_of_in_DAB_points
    {A B C D X : Point}
    (hccw : CCWQuad A B C D)
    (hX : TriHull.InTriStrict X D A B) :
    0 < sig C D X := by
  obtain ⟨dx, ax, bx, hdx, hax, hbx, hsum, hXeq⟩ := hX
  have hACD : 0 < sig A C D := by
    calc
      0 < sig C D A := hccw.2.2.1
      _ = sig D A C := sig_rotate _ _ _
      _ = sig A C D := sig_rotate _ _ _
  have hXCD : 0 < sig X C D := by
    rw [hXeq, sig_affine_fst D A B C D dx ax bx hsum]
    simp only [sig_eq13, mul_zero, zero_add, add_zero]
    exact add_pos (mul_pos hax hACD) (mul_pos hbx hccw.2.1)
  calc
    0 < sig X C D := hXCD
    _ = sig C D X := sig_rotate _ _ _

private theorem crossFan_x_quad
    {A B C D P X Q : Point}
    (hccw : CCWQuad A B C D)
    (hPCAbase : 0 < sig P C A)
    (hPDAbase : 0 < sig P D A)
    (hX_DAB : TriHull.InTriStrict X D A B)
    (hX_PCA : TriHull.InTriStrict X P C A)
    (hX_PDA : TriHull.InTriStrict X P D A)
    (hQ_PDA : TriHull.InTriStrict Q P D A)
    (hQ_PCX : TriHull.InTriStrict Q P C X) :
    TriHull.InTriStrict Q P D X := by
  have hPCX := (fan_coordinates_pos hPCAbase hX_PCA).1
  have hPDX : 0 < sig P D X := (fan_coordinates_pos hPDAbase hX_PDA).1
  have hCDX : 0 < sig C D X :=
    orbitI_CD_pos_of_in_DAB_points hccw hX_DAB
  obtain ⟨_, hQXP, _⟩ := TriHull.inTriStrict_fan_pos hPCX hQ_PCX
  obtain ⟨a, b, c, ha, hb, hc, hsum, hQeq⟩ := hQ_PCX
  have hQDX : 0 < sig Q D X := by
    rw [hQeq, sig_affine_fst P C X D X a b c hsum]
    simp only [sig_eq13, mul_zero, zero_add, add_zero]
    exact add_pos (mul_pos ha hPDX) (mul_pos hb hCDX)
  obtain ⟨_, _, hQPD⟩ := TriHull.inTriStrict_fan_pos hPDAbase hQ_PDA
  exact inTriStrict_of_fan_pos hPDX hQDX hQXP hQPD

private theorem crossFan_y
    {P C A D X Q : Point}
    (hPCAbase : 0 < sig P C A)
    (hPDAbase : 0 < sig P D A)
    (hX_PCA : TriHull.InTriStrict X P C A)
    (hX_PDA : TriHull.InTriStrict X P D A)
    (hQ_PDA : TriHull.InTriStrict Q P D A)
    (hQ_XCA : TriHull.InTriStrict Q X C A)
    (hXPQ : sig X P Q ≠ 0)
    (hXDQ : sig X D Q ≠ 0)
    (hXAQ : sig X A Q ≠ 0) :
    TriHull.InTriStrict Q P D X ∨
      TriHull.InTriStrict Q X D A := by
  have hPXA := (fan_coordinates_pos hPCAbase hX_PCA).2.1
  have hXCA := (fan_coordinates_pos hPCAbase hX_PCA).2.2
  have not_j : ¬ TriHull.InTriStrict Q P X A := by
    intro hQ_PXA
    obtain ⟨_, hQAX, _⟩ := TriHull.inTriStrict_fan_pos hXCA hQ_XCA
    obtain ⟨hQXA, _, _⟩ := TriHull.inTriStrict_fan_pos hPXA hQ_PXA
    simp only [sig] at hQAX hQXA
    linarith
  rcases TriHull.strict_fan_partition hX_PDA hQ_PDA
      hXPQ hXDQ hXAQ with hY | hJ | hX
  · exact Or.inr hY
  · exact False.elim (not_j (inTriStrict_rotate_two hJ))
  · exact Or.inl (inTriStrict_rotate hX)

private theorem reciprocal_x_impossible {P D A X Q : Point}
    (hPDAbase : 0 < sig P D A)
    (hX_PDA : TriHull.InTriStrict X P D A)
    (hQ_PDA : TriHull.InTriStrict Q P D A)
    (hQ_PDX : TriHull.InTriStrict Q P D X)
    (hX_PDQ : TriHull.InTriStrict X P D Q) : False := by
  have hPDX := (fan_coordinates_pos hPDAbase hX_PDA).1
  have hPDQ := (fan_coordinates_pos hPDAbase hQ_PDA).1
  obtain ⟨_, hQXP, _⟩ := TriHull.inTriStrict_fan_pos hPDX hQ_PDX
  obtain ⟨_, hXQP, _⟩ := TriHull.inTriStrict_fan_pos hPDQ hX_PDQ
  simp only [sig] at hQXP hXQP
  linarith

/-! ## The cyclic membership packet -/

/-- The ten memberships selected by the unique cyclic one-fan pattern,
together with the central orientation fixed by the slope order. -/
structure OrbitICyclicMembershipCase
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) : Prop where
  T_in_PCS : TriHull.InTriStrict (v h.T) (v h.P) (v C) (v h.S)
  R_in_SCA : TriHull.InTriStrict (v h.R) (v h.S) (v C) (v A)
  T_in_PDS : TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.S)
  R_in_SDA : TriHull.InTriStrict (v h.R) (v h.S) (v D) (v A)
  S_in_PTA : TriHull.InTriStrict (v h.S) (v h.P) (v h.T) (v A)
  R_in_TCA : TriHull.InTriStrict (v h.R) (v h.T) (v C) (v A)
  R_in_TDA : TriHull.InTriStrict (v h.R) (v h.T) (v D) (v A)
  T_in_PCR : TriHull.InTriStrict (v h.T) (v h.P) (v C) (v h.R)
  S_in_PRA : TriHull.InTriStrict (v h.S) (v h.P) (v h.R) (v A)
  T_in_PDR : TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.R)
  STR_pos : 0 < sig (v h.S) (v h.T) (v h.R)

private def onePointOfCommonSlots
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (i j k q : Fin 8)
    (hinj : Function.Injective (orbitIOnePointLabels i j k q))
    (hmem : TriHull.InTriStrict (v (h.labels q))
      (v (h.labels i)) (v (h.labels j)) (v (h.labels k))) :
    OrbitIOnePointWitness v (h.labels i) (h.labels j) (h.labels k) := by
  refine
    { q := h.labels q
      labels_injective := ?_
      q_in_triangle := hmem }
  intro a b hab
  have happ (n : Fin 4) :
      orbitIOnePointLabels (h.labels i) (h.labels j) (h.labels k)
          (h.labels q) n =
        h.labels (orbitIOnePointLabels i j k q n) := by
    fin_cases n <;> rfl
  apply hinj
  apply h.labels_injective
  exact (happ a).symm.trans (hab.trans (happ b))

/-- The ten selected memberships are already the ten one-point witnesses
expected by the analytic cyclic leaf. -/
def OrbitICyclicMembershipCase.lowerWitnesses
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitICommonGeometryCertificate v A B C D}
    (c : OrbitICyclicMembershipCase h) :
    OrbitICyclicLowerWitnesses v h.P C A D h.S h.T h.R := by
  refine
    { Sx := onePointOfCommonSlots h 4 2 5 6 (by decide) ?_
      Sy := onePointOfCommonSlots h 5 2 0 7 (by decide) ?_
      Sx' := onePointOfCommonSlots h 4 3 5 6 (by decide) ?_
      Sy' := onePointOfCommonSlots h 5 3 0 7 (by decide) ?_
      Tj := onePointOfCommonSlots h 4 6 0 5 (by decide) ?_
      Ty := onePointOfCommonSlots h 6 2 0 7 (by decide) ?_
      Ty' := onePointOfCommonSlots h 6 3 0 7 (by decide) ?_
      Rx := onePointOfCommonSlots h 4 2 7 6 (by decide) ?_
      Rj := onePointOfCommonSlots h 4 7 0 5 (by decide) ?_
      Rx' := onePointOfCommonSlots h 4 3 7 6 (by decide) ?_ }
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.T_in_PCS
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.R_in_SCA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.T_in_PDS
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.R_in_SDA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.S_in_PTA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.R_in_TCA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.R_in_TDA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.T_in_PCR
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.S_in_PRA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      c.T_in_PDR

/-- The same ten memberships imply the first eight cyclic orientations;
the slope selector supplies the ninth. -/
def OrbitICyclicMembershipCase.orientationWitnesses
    {v : Fin 8 → Point} {A B C D : Fin 8}
    {h : OrbitICommonGeometryCertificate v A B C D}
    (c : OrbitICyclicMembershipCase h) :
    OrbitICyclicOrientationWitnesses v h.P C A D h.S h.T h.R := by
  have hPCA := (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).2.1
  have hPDA := (TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB).2.2
  have hPCS := (fan_coordinates_pos hPCA h.S_in_PCA).1
  have hPDS := (fan_coordinates_pos hPDA h.S_in_PDA).1
  have hPTA := (fan_coordinates_pos hPCA h.T_in_PCA).2.1
  have hSCA := (fan_coordinates_pos hPCA h.S_in_PCA).2.2
  have hSDA := (fan_coordinates_pos hPDA h.S_in_PDA).2.2
  have hTCA := (fan_coordinates_pos hPCA h.T_in_PCA).2.2
  have hPRA := (fan_coordinates_pos hPCA h.R_in_PCA).2.1
  have hPDR := (fan_coordinates_pos hPDA h.R_in_PDA).1
  obtain ⟨hCST, _, _⟩ := TriHull.inTriStrict_fan_pos hPCS c.T_in_PCS
  obtain ⟨hSTA, _, _⟩ := TriHull.inTriStrict_fan_pos hPTA c.S_in_PTA
  obtain ⟨hTDS, _, _⟩ := TriHull.inTriStrict_fan_pos hPDS c.T_in_PDS
  obtain ⟨_, _, hRSC⟩ := TriHull.inTriStrict_fan_pos hSCA c.R_in_SCA
  obtain ⟨_, _, hSPR⟩ := TriHull.inTriStrict_fan_pos hPRA c.S_in_PRA
  obtain ⟨_, _, hRSD⟩ := TriHull.inTriStrict_fan_pos hSDA c.R_in_SDA
  obtain ⟨_, hRAT, _⟩ := TriHull.inTriStrict_fan_pos hTCA c.R_in_TCA
  obtain ⟨_, hTRP, _⟩ := TriHull.inTriStrict_fan_pos hPDR c.T_in_PDR
  exact
    { CST_pos := by
        calc
          0 < sig (v h.T) (v C) (v h.S) := hCST
          _ = sig (v C) (v h.S) (v h.T) := sig_rotate _ _ _
      AST_pos := by
        calc
          0 < sig (v h.S) (v h.T) (v A) := hSTA
          _ = sig (v h.T) (v A) (v h.S) := sig_rotate _ _ _
          _ = sig (v A) (v h.S) (v h.T) := sig_rotate _ _ _
      DST_pos := by
        calc
          0 < sig (v h.T) (v D) (v h.S) := hTDS
          _ = sig (v D) (v h.S) (v h.T) := sig_rotate _ _ _
      CRS_pos := by
        calc
          0 < sig (v h.R) (v h.S) (v C) := hRSC
          _ = sig (v h.S) (v C) (v h.R) := sig_rotate _ _ _
          _ = sig (v C) (v h.R) (v h.S) := sig_rotate _ _ _
      PRS_pos := by
        calc
          0 < sig (v h.S) (v h.P) (v h.R) := hSPR
          _ = sig (v h.P) (v h.R) (v h.S) := sig_rotate _ _ _
      DRS_pos := by
        calc
          0 < sig (v h.R) (v h.S) (v D) := hRSD
          _ = sig (v h.S) (v D) (v h.R) := sig_rotate _ _ _
          _ = sig (v D) (v h.R) (v h.S) := sig_rotate _ _ _
      ATR_pos := by
        calc
          0 < sig (v h.R) (v A) (v h.T) := hRAT
          _ = sig (v A) (v h.T) (v h.R) := sig_rotate _ _ _
      PTR_pos := by
        calc
          0 < sig (v h.T) (v h.R) (v h.P) := hTRP
          _ = sig (v h.R) (v h.P) (v h.T) := sig_rotate _ _ _
          _ = sig (v h.P) (v h.T) (v h.R) := sig_rotate _ _ _
      STR_pos := c.STR_pos }

/-! ## Common-packet wrappers for the cross-fan lemmas -/

private lemma minTri_sig_ne_zero
    {v : Fin 8 → Point} (hmzero : minTri v ≠ 0)
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  apply hmzero
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [hzero, abs_zero] at hmin
  exact le_antisymm hmin (minTri_nonneg v)

private lemma OrbitICommonGeometryCertificate.slot_sig_ne_zero
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (i j k : Fin 8) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v (h.labels i)) (v (h.labels j)) (v (h.labels k)) ≠ 0 :=
  minTri_sig_ne_zero hmzero
    (h.labels_injective.ne hij) (h.labels_injective.ne hik)
    (h.labels_injective.ne hjk)

private lemma OrbitICommonGeometryCertificate.PCA_pos
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) :
    0 < sig (v h.P) (v C) (v A) :=
  (TriHull.inTriStrict_fan_pos h.ccw.1 h.P_in_ABC).2.1

private lemma OrbitICommonGeometryCertificate.PDA_pos
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) :
    0 < sig (v h.P) (v D) (v A) :=
  (TriHull.inTriStrict_fan_pos h.ccw.2.2.2 h.P_in_DAB).2.2

private theorem OrbitICommonGeometryCertificate.cross_x_S
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hS : TriHull.InTriStrict (v h.S) (v h.P) (v C) (v h.R)) :
    TriHull.InTriStrict (v h.S) (v h.P) (v D) (v h.R) :=
  crossFan_x_quad h.ccw h.PCA_pos h.PDA_pos h.R_in_DAB
    h.R_in_PCA h.R_in_PDA h.S_in_PDA hS

private theorem OrbitICommonGeometryCertificate.cross_x_T
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hT : TriHull.InTriStrict (v h.T) (v h.P) (v C) (v h.R)) :
    TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.R) :=
  crossFan_x_quad h.ccw h.PCA_pos h.PDA_pos h.R_in_DAB
    h.R_in_PCA h.R_in_PDA h.T_in_PDA hT

private theorem OrbitICommonGeometryCertificate.cross_y_S
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (hS : TriHull.InTriStrict (v h.S) (v h.R) (v C) (v A)) :
    TriHull.InTriStrict (v h.S) (v h.P) (v D) (v h.R) ∨
      TriHull.InTriStrict (v h.S) (v h.R) (v D) (v A) := by
  apply crossFan_y h.PCA_pos h.PDA_pos h.R_in_PCA h.R_in_PDA
    h.S_in_PDA hS
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 7 4 5 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 7 3 5 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 7 0 5 (by decide) (by decide) (by decide)

private theorem OrbitICommonGeometryCertificate.cross_y_T
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (hT : TriHull.InTriStrict (v h.T) (v h.R) (v C) (v A)) :
    TriHull.InTriStrict (v h.T) (v h.P) (v D) (v h.R) ∨
      TriHull.InTriStrict (v h.T) (v h.R) (v D) (v A) := by
  apply crossFan_y h.PCA_pos h.PDA_pos h.R_in_PCA h.R_in_PDA
    h.T_in_PDA hT
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 7 4 6 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 7 3 6 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 7 0 6 (by decide) (by decide) (by decide)

private theorem OrbitICommonGeometryCertificate.sameCFan_easy
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) (cell : OrbitIFanCell)
    (hS : cell.Holds (v h.S) (v h.R) (v h.P) (v C) (v A))
    (hT : cell.Holds (v h.T) (v h.R) (v h.P) (v C) (v A)) :
    ∃ h' : OrbitICommonGeometryCertificate v A B C D,
      OrbitIEasyGeometryCase h' := by
  cases cell with
  | x =>
      exact ⟨h, .p_common hS hT (h.cross_x_S hS) (h.cross_x_T hT)⟩
  | j => exact ⟨h, .shared hS hT⟩
  | y =>
      rcases h.cross_y_S hmzero hS with hSDx | hSDy
      · rcases h.cross_y_T hmzero hT with hTDx | hTDy
        · exact ⟨h, .d_p_opposite hS hT hSDx hTDx⟩
        · exact ⟨h, .c_a_d_split hS hT hSDx hTDy⟩
      · rcases h.cross_y_T hmzero hT with hTDx | hTDy
        · let h' := h.relabel orbitIOrder102
          refine ⟨h', .c_a_d_split ?_ ?_ ?_ ?_⟩
          · simpa [OrbitIFanCell.Holds, h',
              OrbitICommonGeometryCertificate.relabel] using hT
          · simpa [OrbitIFanCell.Holds, h',
              OrbitICommonGeometryCertificate.relabel] using hS
          · simpa [h', OrbitICommonGeometryCertificate.relabel] using hTDx
          · simpa [h', OrbitICommonGeometryCertificate.relabel] using hSDy
        · exact ⟨h, .a_common hS hT hSDy hTDy⟩

private lemma cyclic_STR_pos {P C A L M H : Point}
    (hPCA : 0 < sig P C A)
    (hL : TriHull.InTriStrict L P C A)
    (hM : TriHull.InTriStrict M P C A)
    (hH_PLA : TriHull.InTriStrict H P L A)
    (hL_PCM : TriHull.InTriStrict L P C M)
    (hM_LCA : TriHull.InTriStrict M L C A) :
    0 < sig H L M := by
  have hPCM := (fan_coordinates_pos hPCA hM).1
  have hLCA := (fan_coordinates_pos hPCA hL).2.2
  obtain ⟨_, hLMP, _⟩ := TriHull.inTriStrict_fan_pos hPCM hL_PCM
  obtain ⟨_, hMAL, _⟩ := TriHull.inTriStrict_fan_pos hLCA hM_LCA
  have hPLM : 0 < sig P L M := by
    calc
      0 < sig L M P := hLMP
      _ = sig M P L := sig_rotate _ _ _
      _ = sig P L M := sig_rotate _ _ _
  have hALM : 0 < sig A L M := by
    calc
      0 < sig M A L := hMAL
      _ = sig A L M := sig_rotate _ _ _
  obtain ⟨a, b, c, ha, hb, hc, hsum, hHeq⟩ := hH_PLA
  rw [hHeq, sig_affine_fst P L A L M a b c hsum]
  simp only [sig_eq12, mul_zero, zero_add, add_zero]
  exact add_pos (mul_pos ha hPLM) (mul_pos hc hALM)

/-! ## Ordered and total selectors -/

private noncomputable def OrbitICommonGeometryCertificate.orderedPair_ST
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (hslope : fanSlope (v h.P) (v C) (v A) (v h.S) <
      fanSlope (v h.P) (v C) (v A) (v h.T)) :
    OrbitIFanPairType (v h.P) (v C) (v A) (v h.S) (v h.T) := by
  apply ordered_pair_type h.PCA_pos h.S_in_PCA h.T_in_PCA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 5 4 6 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 5 2 6 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 5 0 6 (by decide) (by decide) (by decide)
  · exact hslope

private noncomputable def OrbitICommonGeometryCertificate.orderedPair_SR
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (hslope : fanSlope (v h.P) (v C) (v A) (v h.S) <
      fanSlope (v h.P) (v C) (v A) (v h.R)) :
    OrbitIFanPairType (v h.P) (v C) (v A) (v h.S) (v h.R) := by
  apply ordered_pair_type h.PCA_pos h.S_in_PCA h.R_in_PCA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 5 4 7 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 5 2 7 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 5 0 7 (by decide) (by decide) (by decide)
  · exact hslope

private noncomputable def OrbitICommonGeometryCertificate.orderedPair_TR
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (hslope : fanSlope (v h.P) (v C) (v A) (v h.T) <
      fanSlope (v h.P) (v C) (v A) (v h.R)) :
    OrbitIFanPairType (v h.P) (v C) (v A) (v h.T) (v h.R) := by
  apply ordered_pair_type h.PCA_pos h.T_in_PCA h.R_in_PCA
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 6 4 7 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 6 2 7 (by decide) (by decide) (by decide)
  · simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
      h.slot_sig_ne_zero hmzero 6 0 7 (by decide) (by decide) (by decide)
  · exact hslope

private theorem OrbitICommonGeometryCertificate.easyOrCyclic_of_ordered
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0)
    (hST : fanSlope (v h.P) (v C) (v A) (v h.S) <
      fanSlope (v h.P) (v C) (v A) (v h.T))
    (hTR : fanSlope (v h.P) (v C) (v A) (v h.T) <
      fanSlope (v h.P) (v C) (v A) (v h.R)) :
    ∃ h' : OrbitICommonGeometryCertificate v A B C D,
      OrbitIEasyGeometryCase h' ∨ OrbitICyclicMembershipCase h' := by
  have hSR := lt_trans hST hTR
  let pST := h.orderedPair_ST hmzero hST
  let pSR := h.orderedPair_SR hmzero hSR
  let pTR := h.orderedPair_TR hmzero hTR
  by_cases hlow : pST.tag.lowCell = pSR.tag.lowCell
  · have hm1 := pST.low_mem
    have hm2 : pST.tag.lowCell.Holds (v h.R) (v h.S)
        (v h.P) (v C) (v A) := by
      rw [hlow]
      exact pSR.low_mem
    let h' := h.relabel orbitIOrder120
    obtain ⟨k, hk⟩ := h'.sameCFan_easy hmzero pST.tag.lowCell
      (by simpa [h', OrbitICommonGeometryCertificate.relabel] using hm1)
      (by simpa [h', OrbitICommonGeometryCertificate.relabel] using hm2)
    exact ⟨k, Or.inl hk⟩
  · by_cases hhigh : pSR.tag.highCell = pTR.tag.highCell
    · obtain ⟨k, hk⟩ := h.sameCFan_easy hmzero pSR.tag.highCell
        pSR.high_mem (by rw [hhigh]; exact pTR.high_mem)
      exact ⟨k, Or.inl hk⟩
    · by_cases hmiddle : pST.tag.highCell = pTR.tag.lowCell
      · have hm1 := pST.high_mem
        have hm2 : pST.tag.highCell.Holds (v h.R) (v h.T)
            (v h.P) (v C) (v A) := by
          rw [hmiddle]
          exact pTR.low_mem
        let h' := h.relabel orbitIOrder021
        obtain ⟨k, hk⟩ := h'.sameCFan_easy hmzero pST.tag.highCell
          (by simpa [h', OrbitICommonGeometryCertificate.relabel] using hm1)
          (by simpa [h', OrbitICommonGeometryCertificate.relabel] using hm2)
        exact ⟨k, Or.inl hk⟩
      · rcases five_pair_patterns pST.tag pSR.tag pTR.tag
          hlow hhigh hmiddle with hp | hp | hp | hp | hp
        · rcases hp with ⟨hSTA, hSRC, hTRB⟩
          have hbST := pST.b_forward h.PCA_pos h.S_in_PCA h.T_in_PCA
            (by simpa [hSTA])
          have hbSR := pSR.b_backward h.PCA_pos h.S_in_PCA h.R_in_PCA hSRC
          have hbTR := pTR.b_forward h.PCA_pos h.T_in_PCA h.R_in_PCA
            (by simpa [hTRB])
          have : False := by linarith
          exact this.elim
        · rcases hp with ⟨hSTB, hSRC, hTRB⟩
          have hbST := pST.b_forward h.PCA_pos h.S_in_PCA h.T_in_PCA
            (by simpa [hSTB])
          have hbSR := pSR.b_backward h.PCA_pos h.S_in_PCA h.R_in_PCA hSRC
          have hbTR := pTR.b_forward h.PCA_pos h.T_in_PCA h.R_in_PCA
            (by simpa [hTRB])
          have : False := by linarith
          exact this.elim
        · rcases hp with ⟨hSTC, hSRB, hTRA⟩
          have hcST := pST.c_forward h.PCA_pos h.S_in_PCA h.T_in_PCA
            (by simpa [hSTC])
          have hcSR := pSR.c_backward h.PCA_pos h.S_in_PCA h.R_in_PCA hSRB
          have hcTR := pTR.c_forward h.PCA_pos h.T_in_PCA h.R_in_PCA
            (by simpa [hTRA])
          have : False := by linarith
          exact this.elim
        · rcases hp with ⟨hSTC, hSRB, hTRC⟩
          have hcST := pST.c_forward h.PCA_pos h.S_in_PCA h.T_in_PCA
            (by simpa [hSTC])
          have hcSR := pSR.c_backward h.PCA_pos h.S_in_PCA h.R_in_PCA hSRB
          have hcTR := pTR.c_forward h.PCA_pos h.T_in_PCA h.R_in_PCA
            (by simpa [hTRC])
          have : False := by linarith
          exact this.elim
        · rcases hp with ⟨hSTC, hSRA, hTRB⟩
          have hM_LCA := pST.high_y_of_tag_C hSTC
          have hL_PCM := pST.low_x_of_tag_C hSTC
          have hH_PLA := pSR.high_j_of_tag_A hSRA
          have hL_PCH := pSR.low_x_of_tag_A hSRA
          have hM_HCA := pTR.low_y_of_tag_B hTRB
          have hH_PMA := pTR.high_j_of_tag_B hTRB
          have hL_PDH := crossFan_x_quad h.ccw h.PCA_pos h.PDA_pos
            h.R_in_DAB h.R_in_PCA h.R_in_PDA h.S_in_PDA hL_PCH
          have hL_PDM := crossFan_x_quad h.ccw h.PCA_pos h.PDA_pos
            h.T_in_DAB h.T_in_PCA h.T_in_PDA h.S_in_PDA hL_PCM
          have hM_at_H := crossFan_y h.PCA_pos h.PDA_pos h.R_in_PCA
            h.R_in_PDA h.T_in_PDA hM_HCA
            (by
              simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
                h.slot_sig_ne_zero hmzero 7 4 6
                  (by decide) (by decide) (by decide))
            (by
              simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
                h.slot_sig_ne_zero hmzero 7 3 6
                  (by decide) (by decide) (by decide))
            (by
              simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
                h.slot_sig_ne_zero hmzero 7 0 6
                  (by decide) (by decide) (by decide))
          have hM_at_L := crossFan_y h.PCA_pos h.PDA_pos h.S_in_PCA
            h.S_in_PDA h.T_in_PDA hM_LCA
            (by
              simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
                h.slot_sig_ne_zero hmzero 5 4 6
                  (by decide) (by decide) (by decide))
            (by
              simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
                h.slot_sig_ne_zero hmzero 5 3 6
                  (by decide) (by decide) (by decide))
            (by
              simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
                h.slot_sig_ne_zero hmzero 5 0 6
                  (by decide) (by decide) (by decide))
          rcases hM_at_L with hM_PDL | hM_LDA
          · exact False.elim
              (reciprocal_x_impossible h.PDA_pos h.S_in_PDA h.T_in_PDA
                hM_PDL hL_PDM)
          · rcases hM_at_H with hM_PDH | hM_HDA
            · exact ⟨h, Or.inl (.d_p_split hL_PCH hM_HCA hL_PDH hM_PDH)⟩
            · let h' := h.relabel orbitIOrder201
              refine ⟨h', Or.inr ?_⟩
              refine
                { T_in_PCS := ?_
                  R_in_SCA := ?_
                  T_in_PDS := ?_
                  R_in_SDA := ?_
                  S_in_PTA := ?_
                  R_in_TCA := ?_
                  R_in_TDA := ?_
                  T_in_PCR := ?_
                  S_in_PRA := ?_
                  T_in_PDR := ?_
                  STR_pos := ?_ }
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hL_PCH
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hM_HCA
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hL_PDH
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hM_HDA
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hH_PLA
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hM_LCA
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hM_LDA
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hL_PCM
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hH_PMA
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using hL_PDM
              · simpa [h', OrbitICommonGeometryCertificate.relabel] using
                  cyclic_STR_pos h.PCA_pos h.S_in_PCA h.T_in_PCA
                    hH_PLA hL_PCM hM_LCA

private lemma fanSlope_ne_of_sig_ne {P C A X Y : Point}
    (hPCA : 0 < sig P C A)
    (hX : TriHull.InTriStrict X P C A)
    (hY : TriHull.InTriStrict Y P C A)
    (hPXY : sig P X Y ≠ 0) :
    fanSlope P C A X ≠ fanSlope P C A Y := by
  intro heq
  obtain ⟨_, hjX, _⟩ := fan_coordinates_pos hPCA hX
  obtain ⟨_, hjY, _⟩ := fan_coordinates_pos hPCA hY
  have hcross : fanX P C X * fanJ P A Y =
      fanX P C Y * fanJ P A X :=
    (div_eq_div_iff hjX.ne' hjY.ne').mp heq
  have hid := fan_gap_P P C A X Y
  apply hPXY
  nlinarith

private lemma OrbitICommonGeometryCertificate.slope_ne_ST
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) :
    fanSlope (v h.P) (v C) (v A) (v h.S) ≠
      fanSlope (v h.P) (v C) (v A) (v h.T) := by
  apply fanSlope_ne_of_sig_ne h.PCA_pos h.S_in_PCA h.T_in_PCA
  simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
    h.slot_sig_ne_zero hmzero 4 5 6 (by decide) (by decide) (by decide)

private lemma OrbitICommonGeometryCertificate.slope_ne_SR
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) :
    fanSlope (v h.P) (v C) (v A) (v h.S) ≠
      fanSlope (v h.P) (v C) (v A) (v h.R) := by
  apply fanSlope_ne_of_sig_ne h.PCA_pos h.S_in_PCA h.R_in_PCA
  simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
    h.slot_sig_ne_zero hmzero 4 5 7 (by decide) (by decide) (by decide)

private lemma OrbitICommonGeometryCertificate.slope_ne_TR
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) :
    fanSlope (v h.P) (v C) (v A) (v h.T) ≠
      fanSlope (v h.P) (v C) (v A) (v h.R) := by
  apply fanSlope_ne_of_sig_ne h.PCA_pos h.T_in_PCA h.R_in_PCA
  simpa [OrbitICommonGeometryCertificate.labels, quadLabels] using
    h.slot_sig_ne_zero hmzero 4 6 7 (by decide) (by decide) (by decide)

/-- Total compact selector: after relabelling `S,T,R`, every common Orbit I
packet is either one of the existing easy cases or the unique cyclic
membership packet. -/
theorem OrbitICommonGeometryCertificate.easyOrCyclic
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D)
    (hmzero : minTri v ≠ 0) :
    ∃ h' : OrbitICommonGeometryCertificate v A B C D,
      OrbitIEasyGeometryCase h' ∨ OrbitICyclicMembershipCase h' := by
  rcases lt_or_gt_of_ne (h.slope_ne_ST hmzero) with hST | hTS
  · rcases lt_or_gt_of_ne (h.slope_ne_TR hmzero) with hTR | hRT
    · exact h.easyOrCyclic_of_ordered hmzero hST hTR
    · rcases lt_or_gt_of_ne (h.slope_ne_SR hmzero) with hSR | hRS
      · let h' := h.relabel orbitIOrder021
        apply h'.easyOrCyclic_of_ordered hmzero
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hSR
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hRT
      · let h' := h.relabel orbitIOrder201
        apply h'.easyOrCyclic_of_ordered hmzero
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hRS
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hST
  · rcases lt_or_gt_of_ne (h.slope_ne_SR hmzero) with hSR | hRS
    · let h' := h.relabel orbitIOrder102
      apply h'.easyOrCyclic_of_ordered hmzero
      · simpa [h', OrbitICommonGeometryCertificate.relabel] using hTS
      · simpa [h', OrbitICommonGeometryCertificate.relabel] using hSR
    · rcases lt_or_gt_of_ne (h.slope_ne_TR hmzero) with hTR | hRT
      · let h' := h.relabel orbitIOrder120
        apply h'.easyOrCyclic_of_ordered hmzero
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hTR
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hRS
      · let h' := h.relabel orbitIOrder210
        apply h'.easyOrCyclic_of_ordered hmzero
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hRT
        · simpa [h', OrbitICommonGeometryCertificate.relabel] using hTS

/-- A common Orbit I packet alone supplies the unconditional quadrilateral
certificate.  The cyclic witness payload is reconstructed from geometry. -/
theorem OrbitICommonGeometryCertificate.orbitCertificate
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitICommonGeometryCertificate v A B C D) :
    OrbitCertificate v A B C D := by
  by_cases hmzero : minTri v = 0
  · exact Or.inl hmzero
  · obtain ⟨h', heasy | hcyclic⟩ := h.easyOrCyclic hmzero
    · exact h'.easyOrbitCertificate heasy
    · exact h'.cyclicOrbitCertificate hcyclic.lowerWitnesses
        hcyclic.orientationWitnesses

end Heilbronn8.QuadHull
