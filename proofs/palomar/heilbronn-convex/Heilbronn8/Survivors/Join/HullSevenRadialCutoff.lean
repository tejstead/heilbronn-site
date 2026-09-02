import Heilbronn8.Survivors.Join.HullSevenCutoffReduction
import Heilbronn8.Ident

/-!
# Radial cutoff geometry for a strict seven-wheel

This module supplies the geometric half of the universal hull-seven
classifier.  Strict convexity orders the rays from each hull anchor.  Strict
interiority puts the off-hull point between the two boundary rays, and a
two-dimensional Pluecker identity shows that a negative chord sign can never
be followed by a positive one.  Thus every anchor row is a nonempty proper
positive prefix.
-/

namespace Heilbronn8

set_option maxRecDepth 1000000

noncomputable section

def hullSevenShift (anchor offset : Fin 7) : Fin 7 :=
  anchor + offset

def hullSevenRowOffset (offset : Fin 6) : Fin 7 :=
  ⟨offset.val + 1, by omega⟩

def hullSevenReverseRowOffset (offset : Fin 6) : Fin 6 :=
  ⟨5 - offset.val, by omega⟩

private def HullSevenCyclicOrder (i j k : Fin 7) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)

private theorem hullSevenShift_cyclicOrder
    (anchor i j k : Fin 7) (hij : i < j) (hjk : j < k) :
    HullSevenCyclicOrder (hullSevenShift anchor i)
      (hullSevenShift anchor j) (hullSevenShift anchor k) := by
  fin_cases anchor <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [hullSevenShift, HullSevenCyclicOrder]

private lemma sig_swap_first (a b p : ℝ × ℝ) :
    sig b a p = -sig a b p := by
  simp only [sig]
  ring

/-- Minimal strict geometric input for a seven-cycle and its off-cycle point.
`boundary_pos` is the open supporting-half-plane formulation of strict
interiority.  `chord_ne` is the part of general position involving the point. -/
structure StrictHullSevenInterior
    (cycle : Fin 7 → ℝ × ℝ) (point : ℝ × ℝ) : Prop where
  cycle_pos : ∀ i j k : Fin 7, i < j → j < k →
    0 < sig (cycle i) (cycle j) (cycle k)
  boundary_pos : ∀ i : Fin 7,
    0 < sig (cycle i) (cycle (hullSevenShift i 1)) point
  chord_ne : ∀ i : Fin 7, ∀ offset : Fin 6,
    sig (cycle i) (cycle (hullSevenShift i
      (hullSevenRowOffset offset))) point ≠ 0

def StrictHullSevenInterior.row
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (_X : StrictHullSevenInterior cycle point)
    (anchor : Fin 7) (offset : Fin 6) : ℝ :=
  sig (cycle anchor)
    (cycle (hullSevenShift anchor (hullSevenRowOffset offset))) point

theorem StrictHullSevenInterior.shifted_cycle_pos
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point)
    (anchor i j k : Fin 7) (hij : i < j) (hjk : j < k) :
    0 < sig (cycle (hullSevenShift anchor i))
      (cycle (hullSevenShift anchor j))
      (cycle (hullSevenShift anchor k)) := by
  have horder := hullSevenShift_cyclicOrder anchor i j k hij hjk
  rcases horder with hordered | hordered | hordered
  · exact X.cycle_pos _ _ _ hordered.1 hordered.2
  · rw [sig_rotate]
    exact X.cycle_pos _ _ _ hordered.1 hordered.2
  · rw [sig_rotate, sig_rotate]
    exact X.cycle_pos _ _ _ hordered.1 hordered.2

private theorem hullSevenShift_six_one (anchor : Fin 7) :
    hullSevenShift (hullSevenShift anchor 6) 1 = anchor := by
  fin_cases anchor <;> rfl

/-- The determinant calculation behind monotonicity of one radial sign row. -/
private theorem radialChord_negative_mono
    (A U1 Uj Uk U6 P : ℝ × ℝ)
    (hD : 0 < sig A U1 U6)
    (hBj : 0 < sig A Uj U6)
    (hBk : 0 < sig A Uk U6)
    (hjk : 0 < sig A Uj Uk)
    (hx : 0 < sig A P U6)
    (hTj : sig A Uj P < 0) :
    sig A Uk P < 0 := by
  let D := sig A U1 U6
  let x := sig A P U6
  let y := sig A U1 P
  let Aj := sig A U1 Uj
  let Ak := sig A U1 Uk
  let Bj := sig A Uj U6
  let Bk := sig A Uk U6
  let Tj := sig A Uj P
  let Tk := sig A Uk P
  let Jjk := sig A Uj Uk
  have hjIdentity : D * Tj = y * Bj - x * Aj := by
    simp only [D, x, y, Aj, Bj, Tj, sig]
    ring
  have hkIdentity : D * Tk = y * Bk - x * Ak := by
    simp only [D, x, y, Ak, Bk, Tk, sig]
    ring
  have hcrossIdentity : Ak * Bj - Aj * Bk = D * Jjk := by
    simp only [D, Aj, Ak, Bj, Bk, Jjk, sig]
    ring
  have hDTj : D * Tj < 0 := mul_neg_of_pos_of_neg hD hTj
  rw [hjIdentity] at hDTj
  have hfirst : y * Bj < x * Aj := sub_neg.mp hDTj
  have hcrossPositive : 0 < Ak * Bj - Aj * Bk := by
    rw [hcrossIdentity]
    exact mul_pos hD hjk
  have hsecond : Aj * Bk < Ak * Bj := sub_pos.mp hcrossPositive
  have hfirstMul := mul_lt_mul_of_pos_right hfirst hBk
  have hsecondMul := mul_lt_mul_of_pos_left hsecond hx
  have hcancelProduct : (y * Bk) * Bj < (x * Ak) * Bj := by
    calc
      (y * Bk) * Bj = (y * Bj) * Bk := by ring
      _ < (x * Aj) * Bk := hfirstMul
      _ = x * (Aj * Bk) := by ring
      _ < x * (Ak * Bj) := hsecondMul
      _ = (x * Ak) * Bj := by ring
  have hthreshold : y * Bk < x * Ak :=
    lt_of_mul_lt_mul_right hcancelProduct hBj.le
  have hDTk : D * Tk < 0 := by
    rw [hkIdentity]
    exact sub_neg.mpr hthreshold
  by_contra hnot
  have hTk : 0 ≤ Tk := le_of_not_gt hnot
  have : 0 ≤ D * Tk := mul_nonneg hD.le hTk
  linarith

private theorem StrictHullSevenInterior.row_last_negative
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (anchor : Fin 7) :
    X.row anchor 5 < 0 := by
  have hboundary := X.boundary_pos (hullSevenShift anchor 6)
  rw [hullSevenShift_six_one] at hboundary
  change sig (cycle anchor) (cycle (hullSevenShift anchor 6)) point < 0
  rw [sig_swap_first]
  linarith

private theorem StrictHullSevenInterior.row_negative_mono
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (anchor : Fin 7)
    {j k : Fin 6} (hjk : j < k) (hj : X.row anchor j < 0) :
    X.row anchor k < 0 := by
  by_cases hk : k = 5
  · subst k
    exact X.row_last_negative anchor
  have hk5 : k.val + 1 < 6 := by omega
  let j7 : Fin 7 := ⟨j.val + 1, by omega⟩
  let k7 : Fin 7 := ⟨k.val + 1, by omega⟩
  have h0j : (0 : Fin 7) < j7 := by
    change 0 < j.val + 1
    omega
  have hj6 : j7 < (6 : Fin 7) := by
    change j.val + 1 < 6
    omega
  have h0k : (0 : Fin 7) < k7 := by
    change 0 < k.val + 1
    omega
  have hk6 : k7 < (6 : Fin 7) := by
    change k.val + 1 < 6
    omega
  have hjk7 : j7 < k7 := by
    change j.val + 1 < k.val + 1
    omega
  have hD := X.shifted_cycle_pos anchor 0 1 6 (by decide) (by decide)
  have hBj := X.shifted_cycle_pos anchor 0 j7 6 h0j hj6
  have hBk := X.shifted_cycle_pos anchor 0 k7 6 h0k hk6
  have hjkPos := X.shifted_cycle_pos anchor 0 j7 k7 h0j hjk7
  have hclosing := X.boundary_pos (hullSevenShift anchor 6)
  rw [hullSevenShift_six_one] at hclosing
  have hx : 0 < sig (cycle anchor) point
      (cycle (hullSevenShift anchor 6)) := by
    rw [← sig_rotate]
    exact hclosing
  exact radialChord_negative_mono
    (cycle anchor)
    (cycle (hullSevenShift anchor 1))
    (cycle (hullSevenShift anchor j7))
    (cycle (hullSevenShift anchor k7))
    (cycle (hullSevenShift anchor 6)) point
    (by simpa [hullSevenShift] using hD)
    (by simpa [hullSevenShift] using hBj)
    (by simpa [hullSevenShift] using hBk)
    (by simpa [hullSevenShift] using hjkPos) hx hj

/-- A six-bit row which starts positive, ends negative, and stays negative
after its first negative entry has a unique cutoff in `{1, ..., 5}`. -/
private theorem sixBoolPrefixCutoff :
    ∀ f : Fin 6 → Bool,
      f 0 = true →
      f 5 = false →
      (∀ j k, j < k → f j = false → f k = false) →
      ∃ cutoff : Fin 5, ∀ d : Fin 6,
        f d = decide (d.val ≤ cutoff.val) := by
  decide

private theorem StrictHullSevenInterior.exists_row_cutoff
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (anchor : Fin 7) :
    ∃ cutoff : Fin 5, ∀ d : Fin 6,
      decide (0 < X.row anchor d) = decide (d.val ≤ cutoff.val) := by
  apply sixBoolPrefixCutoff (fun d => decide (0 < X.row anchor d))
  · simpa [StrictHullSevenInterior.row, hullSevenRowOffset] using
      X.boundary_pos anchor
  · simpa only [decide_eq_false_iff_not, not_lt] using
      (le_of_lt (X.row_last_negative anchor))
  · intro j k hjk hj
    have hjNotPos : ¬ 0 < X.row anchor j := by
      simpa using hj
    have hjNeg : X.row anchor j < 0 :=
      lt_of_le_of_ne (le_of_not_gt hjNotPos) (X.chord_ne anchor j)
    have hkNeg := X.row_negative_mono anchor hjk hjNeg
    simpa only [decide_eq_false_iff_not, not_lt] using le_of_lt hkNeg

/-- Simultaneous positive-prefix cutoffs for all seven anchors. -/
theorem StrictHullSevenInterior.exists_cutoffs
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) :
    ∃ cuts : Fin 7 → Fin 5, ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val) := by
  have hall : ∀ i : Fin 7, ∃ cutoff : Fin 5, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ cutoff.val) :=
    fun i => X.exists_row_cutoff i
  choose cuts hcuts using hall
  exact ⟨cuts, hcuts⟩

theorem cutoffDirectedPositive_forward
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (i : Fin 7) (d : Fin 6) :
    hullSevenCutoffDirectedPositive cuts i.val (i.val + d.val + 1) =
      decide (0 < X.row i d) := by
  have h := hcuts i d
  fin_cases i <;> fin_cases d <;>
    simpa [hullSevenCutoffDirectedPositive, hullSevenForwardDistance,
      hullSevenCutoffAt] using h.symm

private theorem cutoffDirectedPositive_reverse
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val))
    (i : Fin 7) (d : Fin 6) :
    hullSevenCutoffDirectedPositive cuts (i.val + d.val + 1) i.val =
      decide (0 < X.row
        (hullSevenShift i (hullSevenRowOffset d))
        (hullSevenReverseRowOffset d)) := by
  have h := hcuts
    (hullSevenShift i (hullSevenRowOffset d))
    (hullSevenReverseRowOffset d)
  calc
    hullSevenCutoffDirectedPositive cuts (i.val + d.val + 1) i.val =
        decide ((hullSevenReverseRowOffset d).val ≤
          (cuts (hullSevenShift i (hullSevenRowOffset d))).val) := by
      fin_cases i <;> fin_cases d <;>
        simp [hullSevenShift, hullSevenRowOffset,
          hullSevenReverseRowOffset, hullSevenCutoffDirectedPositive,
          hullSevenForwardDistance, hullSevenCutoffAt] <;> rfl
    _ = decide (0 < X.row
        (hullSevenShift i (hullSevenRowOffset d))
        (hullSevenReverseRowOffset d)) := h.symm

private theorem StrictHullSevenInterior.row_reverse
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (i : Fin 7) (d : Fin 6) :
    X.row (hullSevenShift i (hullSevenRowOffset d))
        (hullSevenReverseRowOffset d) = -X.row i d := by
  fin_cases i <;> fin_cases d <;>
    simp [StrictHullSevenInterior.row, hullSevenShift,
      hullSevenRowOffset, hullSevenReverseRowOffset, sig] <;> ring

/-- Any cutoffs matching the geometric rows obey chord reversal. -/
theorem StrictHullSevenInterior.cutoffs_complementary
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) (cuts : Fin 7 → Fin 5)
    (hcuts : ∀ i : Fin 7, ∀ d : Fin 6,
      decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val)) :
    HullSevenCutoffComplementary cuts := by
  intro i d
  change hullSevenCutoffDirectedPositive cuts i.val
      (i.val + d.val + 1) ≠
    hullSevenCutoffDirectedPositive cuts (i.val + d.val + 1) i.val
  rw [cutoffDirectedPositive_forward X cuts hcuts i d,
    cutoffDirectedPositive_reverse X cuts hcuts i d,
    X.row_reverse i d]
  have hne := X.chord_ne i d
  by_cases hpos : 0 < X.row i d
  · have hnot : ¬ 0 < -X.row i d := by linarith
    simp [hpos, hnot]
  · have hneg : X.row i d < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hnegated : 0 < -X.row i d := by linarith
    simp [hpos, hnegated]

/-- Geometry supplies the reversal constraint required by the finite
classifier; it is not an extra combinatorial assumption. -/
theorem StrictHullSevenInterior.exists_admissibleCutoffs
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) :
    ∃ cuts : Fin 7 → Fin 5,
      HullSevenCutoffComplementary cuts ∧
      ∀ i : Fin 7, ∀ d : Fin 6,
        decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val) := by
  obtain ⟨cuts, hcuts⟩ := X.exists_cutoffs
  exact ⟨cuts, X.cutoffs_complementary cuts hcuts, hcuts⟩

/-- Every strict seven-wheel produces a concrete dihedral presentation of one
of the eight universal cutoff keys. -/
theorem StrictHullSevenInterior.exists_presentedOrderType
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) :
    ∃ cuts : Fin 7 → Fin 5, ∃ orderType ∈ hullSevenTypes,
      ∃ rotation : Fin 7, ∃ reflected : Bool,
      hullSevenCutoffOrderType cuts = orderType.key ∧
      hullSevenCutoffPresentationKey cuts rotation.val reflected =
        orderType.key ∧
      ∀ i : Fin 7, ∀ d : Fin 6,
        decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val) := by
  obtain ⟨cuts, hcomplementary, hcuts⟩ := X.exists_admissibleCutoffs
  have hok : hullSevenCutoffComplementOK cuts = true :=
    (hullSevenCutoffComplementOK_eq_true_iff cuts).2 hcomplementary
  obtain ⟨orderType, htype, hkey, rotation, reflected, hpresentation⟩ :=
    hullSevenCutoff_classification_reduced_withPresentation cuts hok
  exact ⟨cuts, orderType, htype, rotation, reflected,
    hkey, hpresentation, hcuts⟩

/-- Every strict seven-wheel produces one of the eight universal cutoff keys. -/
theorem StrictHullSevenInterior.exists_orderType
    {cycle : Fin 7 → ℝ × ℝ} {point : ℝ × ℝ}
    (X : StrictHullSevenInterior cycle point) :
    ∃ cuts : Fin 7 → Fin 5, ∃ orderType ∈ hullSevenTypes,
      hullSevenCutoffOrderType cuts = orderType.key ∧
      ∀ i : Fin 7, ∀ d : Fin 6,
        decide (0 < X.row i d) = decide (d.val ≤ (cuts i).val) := by
  obtain ⟨cuts, orderType, htype, _rotation, _reflected,
    hkey, _hpresentation, hcuts⟩ := X.exists_presentedOrderType
  exact ⟨cuts, orderType, htype, hkey, hcuts⟩

end

end Heilbronn8
