import Heil6.PlanarDet

set_option linter.style.header false

/-!
# Radial order from a diameter endpoint

For a general-position six-point configuration, choose a pair of labels whose
Euclidean squared distance is maximal.  Projection on the diameter direction
is strictly positive from one endpoint to every other point.  Sorting the
other five labels by transverse/projection slope therefore gives a relabeling
in which every determinant containing label `0` is positive.

This is the geometric normalization needed by the small ten-bit hull-case
classifier.  It uses no generated certificate and no choice of a supporting
hyperplane.
-/

namespace N6Scratch
namespace AnchorOrder

open PlanarDet

/-- Squared Euclidean distance, written in coordinates so the diameter
argument below is discharged by the ordered-ring normalizer. -/
private def sqDist (A B : ℝ × ℝ) : ℝ :=
  (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2

/-- A fresh copy of `Fin 6`, used only so that the slope-induced order does
not collide with the usual numerical order already installed on `Fin 6`. -/
private structure RadialLabel where
  index : Fin 6
deriving DecidableEq, Fintype

private def radialLabelEquiv : RadialLabel ≃ Fin 6 where
  toFun := RadialLabel.index
  invFun := fun i => ⟨i⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem sqDist_pos_of_ne {A B : ℝ × ℝ} (hAB : A ≠ B) :
    0 < sqDist A B := by
  have hcoord : B.1 - A.1 ≠ 0 ∨ B.2 - A.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hAB
    ext <;> linarith
  rcases hcoord with hx | hy
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hy)

/-- A set of six labels always contains a label different from two prescribed
labels.  Keeping this tiny finite fact separate makes the general-position
to-injectivity conversion transparent. -/
private theorem exists_fin_six_ne_two (i j : Fin 6) :
    ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by
  have hcard : ({i, j} : Finset (Fin 6)).card <
      (Finset.univ : Finset (Fin 6)).card := by
    have hle : ({i, j} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
    simpa using lt_of_le_of_lt hle (by norm_num : 2 < 6)
  obtain ⟨k, _hk_univ, hk_pair⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨k, ?_, ?_⟩
  · intro hki
    apply hk_pair
    simp [hki]
  · intro hkj
    apply hk_pair
    simp [hkj]

private theorem injective_of_general_position
    (v : Fin 6 → ℝ × ℝ)
    (hgp : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      sig (v i) (v j) (v k) ≠ 0) :
    Function.Injective v := by
  intro i j hv
  by_contra hij
  obtain ⟨k, hki, hkj⟩ := exists_fin_six_ne_two i j
  apply hgp i j k hij (Ne.symm hki) (Ne.symm hkj)
  rw [hv]
  simp [sig]

/-- If `AB` is at least as long as `CB`, then the projection of `AC` on
`AB` is positive (provided `A ≠ C`). -/
private theorem longitudinal_pos_of_sqDist_le
    (A B C : ℝ × ℝ) (hAC : A ≠ C)
    (hmax : sqDist C B ≤ sqDist A B) :
    0 < longitudinal (B.1 - A.1) (B.2 - A.2) A C := by
  have hACsq : 0 < sqDist A C := sqDist_pos_of_ne hAC
  simp only [sqDist, longitudinal] at hmax hACsq ⊢
  nlinarith

/-- Every general-position six-point configuration can be relabeled so that
the five nonzero labels occur in increasing radial slope about label `0`.
Equivalently, all ten brackets containing the anchor are positive.

The output convention is exactly the `AnchorPositive` input used by
`FiniteHullCases`: the hypotheses `0 < i < j` select two of the five radial
labels. -/
theorem exists_anchor_positive_relabel
    (v : Fin 6 → ℝ × ℝ)
    (hgp : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      sig (v i) (v j) (v k) ≠ 0) :
    ∃ e : Equiv.Perm (Fin 6),
      ∀ i j : Fin 6, 0 < i → i < j →
        0 < sig (v (e 0)) (v (e i)) (v (e j)) := by
  let pairDist : Fin 6 × Fin 6 → ℝ := fun ij => sqDist (v ij.1) (v ij.2)
  obtain ⟨ab, _hab_mem, hab_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 6 × Fin 6))
      pairDist (by simp)
  obtain ⟨a, b⟩ := ab
  have hmax (i j : Fin 6) : sqDist (v i) (v j) ≤ sqDist (v a) (v b) := by
    exact hab_max (i, j) (by simp)
  have vinj : Function.Injective v := injective_of_general_position v hgp
  have hv01 : v (0 : Fin 6) ≠ v (1 : Fin 6) :=
    vinj.ne (by decide)
  have hab_pos : 0 < sqDist (v a) (v b) :=
    lt_of_lt_of_le (sqDist_pos_of_ne hv01) (hmax 0 1)
  have hab : a ≠ b := by
    intro hab
    subst b
    simp [sqDist] at hab_pos
  let aa : ℝ := (v b).1 - (v a).1
  let bb : ℝ := (v b).2 - (v a).2
  have hlong (i : Fin 6) (hia : i ≠ a) :
      0 < longitudinal aa bb (v a) (v i) := by
    dsimp [aa, bb]
    exact longitudinal_pos_of_sqDist_le (v a) (v b) (v i)
      (vinj.ne hia.symm) (hmax i b)
  have hdet : 0 < aa ^ 2 + bb ^ 2 := by
    exact sum_sq_pos_of_longitudinal_pos aa bb (v a) (v b) (hlong b hab.symm)
  let slope : Fin 6 → ℝ := fun i =>
    transverse aa bb (v a) (v i) / longitudinal aa bb (v a) (v i)
  have hslope_ne (i j : Fin 6) (hia : i ≠ a) (hja : j ≠ a)
      (hij : i ≠ j) : slope i ≠ slope j := by
    apply slope_ne_of_sig_ne aa bb (v a) (v i) (v j) hdet
      (ne_of_gt (hlong i hia)) (ne_of_gt (hlong j hja))
    exact hgp a i j hia.symm hja.symm hij
  let key : RadialLabel → WithBot ℝ := fun z =>
    if z.index = a then ⊥ else (slope z.index : WithBot ℝ)
  have hkey_inj : Function.Injective key := by
    intro x y hxy
    by_cases hxa : x.index = a
    · by_cases hya : y.index = a
      · exact radialLabelEquiv.injective (hxa.trans hya.symm)
      · exfalso
        simpa [key, hxa, hya] using hxy
    · by_cases hya : y.index = a
      · exfalso
        simpa [key, hxa, hya] using hxy
      · have hs : slope x.index = slope y.index := by
          simpa [key, hxa, hya] using hxy
        have hindex : x.index = y.index := by
          by_contra hne
          exact hslope_ne x.index y.index hxa hya hne hs
        exact radialLabelEquiv.injective hindex
  letI : LinearOrder RadialLabel := LinearOrder.lift' key hkey_inj
  have hcard : Fintype.card RadialLabel = 6 := by
    calc
      Fintype.card RadialLabel = Fintype.card (Fin 6) :=
        Fintype.card_congr radialLabelEquiv
      _ = 6 := by simp
  let o : Fin 6 ≃o RadialLabel := monoEquivOfFin RadialLabel hcard
  have hanchor_min (z : RadialLabel) : (⟨a⟩ : RadialLabel) ≤ z := by
    change key ⟨a⟩ ≤ key z
    simp [key]
  have ho0_le : o 0 ≤ (⟨a⟩ : RadialLabel) := by
    have h := o.monotone (Fin.zero_le (o.symm (⟨a⟩ : RadialLabel)))
    simpa using h
  have ho0 : o 0 = (⟨a⟩ : RadialLabel) :=
    le_antisymm ho0_le (hanchor_min (o 0))
  let e : Equiv.Perm (Fin 6) := o.toEquiv.trans radialLabelEquiv
  have he0 : e 0 = a := by
    simp [e, radialLabelEquiv, ho0]
  refine ⟨e, ?_⟩
  intro i j hi hij
  have hei : e i ≠ a := by
    rw [← he0]
    exact e.injective.ne (ne_of_gt hi)
  have hj0 : 0 < j := lt_trans hi hij
  have hej : e j ≠ a := by
    rw [← he0]
    exact e.injective.ne (ne_of_gt hj0)
  have hoi : (o i).index ≠ a := by
    simpa [e, radialLabelEquiv] using hei
  have hoj : (o j).index ≠ a := by
    simpa [e, radialLabelEquiv] using hej
  have hoij : o i < o j := o.lt_iff_lt.mpr hij
  have hkeyij : key (o i) < key (o j) := hoij
  have hslope : slope (e i) < slope (e j) := by
    simpa [key, e, radialLabelEquiv, hoi, hoj] using hkeyij
  rw [he0]
  exact sig_pos_of_slope_lt aa bb (v a) (v (e i)) (v (e j)) hdet
    (hlong (e i) hei) (hlong (e j) hej) hslope

end AnchorOrder
end N6Scratch
