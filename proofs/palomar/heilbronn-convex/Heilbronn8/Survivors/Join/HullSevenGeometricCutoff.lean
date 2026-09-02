import Heilbronn8.HullDispatchGeometry
import Heilbronn8.Ident
import Heilbronn8.Survivors.Join.HullSevenRadialCutoff

/-!
# Geometry-only hull-seven cutoff packet

This module converts a genuine `HullCycleOf` of length seven into the strict
radial wheel consumed by the pure cutoff classifier.  It contains no search
word, retained record, production custody, registry, or generated
certificate.  The unique omitted label is selected only by the cardinality
inequality `7 < 8`.
-/

namespace Heilbronn8

noncomputable section

private lemma hullSevenGeometric_sig_nonneg_of_inTri
    (x a b c r s : ℝ × ℝ) (hx : InTri x a b c)
    (ha : 0 ≤ sig r s a) (hb : 0 ≤ sig r s b)
    (hc : 0 ≤ sig r s c) :
    0 ≤ sig r s x := by
  obtain ⟨u, w, t, hu, hw, ht, huwt, rfl⟩ := hx
  have heq :
      sig r s (u • a + w • b + t • c) =
        u * sig r s a + w * sig r s b + t * sig r s c := by
    rw [sig_rotate r s (u • a + w • b + t • c),
      sig_rotate s (u • a + w • b + t • c) r,
      sig_affine_fst a b c r s u w t huwt,
      sig_rotate a r s, sig_rotate b r s, sig_rotate c r s]
  rw [heq]
  exact add_nonneg
    (add_nonneg (mul_nonneg hu ha) (mul_nonneg hw hb))
    (mul_nonneg ht hc)

private lemma strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
    {v : Configuration} {c : Fin 7 → Fin 8}
    (h : StrictCyclicPos c v) (i j : Fin 7)
    (hij : i.val + 1 = j.val) (k : Fin 7) :
    0 ≤ sig (v (c i)) (v (c j)) (v (c k)) := by
  have hij' : i < j := by omega
  by_cases hki : k < i
  · rw [← sig_rotate (v (c k)) (v (c i)) (v (c j))]
    exact h.1 k i j hki hij'
  by_cases hki' : k = i
  · subst k
    simp [sig]
  by_cases hkj : k = j
  · subst k
    simp [sig]
  have hjk : j < k := by omega
  exact h.1 i j k hij' hjk

private lemma strictCyclicPos_seven_closing_boundary_nonneg_geometric
    {v : Configuration} {c : Fin 7 → Fin 8}
    (h : StrictCyclicPos c v) (k : Fin 7) :
    0 ≤ sig (v (c 6)) (v (c 0)) (v (c k)) := by
  by_cases hk0 : k = 0
  · subst k
    simp [sig]
  by_cases hk6 : k = 6
  · subst k
    simp [sig]
  have h0k : (0 : Fin 7) < k := Fin.pos_iff_ne_zero.mpr hk0
  have hk6' : k < (6 : Fin 7) := by omega
  calc
    0 ≤ sig (v (c 0)) (v (c k)) (v (c 6)) := h.1 0 k 6 h0k hk6'
    _ = sig (v (c 6)) (v (c 0)) (v (c k)) := by
      rw [sig_rotate (v (c 0)) (v (c k)) (v (c 6)),
        sig_rotate (v (c k)) (v (c 6)) (v (c 0))]

private lemma strictCyclicPos_seven_boundary_nonneg_geometric
    {v : Configuration} {c : Fin 7 → Fin 8}
    (h : StrictCyclicPos c v) (i k : Fin 7) :
    0 ≤ sig (v (c i)) (v (c (i + 1))) (v (c k)) := by
  fin_cases i
  · change 0 ≤ sig (v (c 0)) (v (c 1)) (v (c k))
    exact strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
      h 0 1 (by decide) k
  · change 0 ≤ sig (v (c 1)) (v (c 2)) (v (c k))
    exact strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
      h 1 2 (by decide) k
  · change 0 ≤ sig (v (c 2)) (v (c 3)) (v (c k))
    exact strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
      h 2 3 (by decide) k
  · change 0 ≤ sig (v (c 3)) (v (c 4)) (v (c k))
    exact strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
      h 3 4 (by decide) k
  · change 0 ≤ sig (v (c 4)) (v (c 5)) (v (c k))
    exact strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
      h 4 5 (by decide) k
  · change 0 ≤ sig (v (c 5)) (v (c 6)) (v (c k))
    exact strictCyclicPos_seven_consecutive_boundary_nonneg_geometric
      h 5 6 (by decide) k
  · change 0 ≤ sig (v (c 6)) (v (c 0)) (v (c k))
    exact strictCyclicPos_seven_closing_boundary_nonneg_geometric h k

private lemma hullCycleSeven_boundary_nonneg_of_outside_geometric
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h7 : d.cycle.length = 7)
    (p : Fin 8) (hpOutside : p ∉ Set.range (d.castGet h7))
    (i : Fin 7) :
    0 ≤ sig (v (d.castGet h7 i))
      (v (d.castGet h7 (i + 1))) (v p) := by
  have hstrict : StrictCyclicPos (d.castGet h7) v :=
    HullCycleData.strictCyclicPos_cast d h7 hcycle.strictCyclicPos
  have hcover : FanCovers v (d.castGet h7) :=
    HullCycleData.fanCovers_cast d h7 hcycle.fanCovers
  obtain ⟨j, k, _hj, _hjk, htri⟩ := hcover p hpOutside
  exact hullSevenGeometric_sig_nonneg_of_inTri
    (v p) (v (d.castGet h7 0)) (v (d.castGet h7 j))
      (v (d.castGet h7 k))
      (v (d.castGet h7 i)) (v (d.castGet h7 (i + 1))) htri
    (strictCyclicPos_seven_boundary_nonneg_geometric hstrict i 0)
    (strictCyclicPos_seven_boundary_nonneg_geometric hstrict i j)
    (strictCyclicPos_seven_boundary_nonneg_geometric hstrict i k)

/-- Every boundary edge strictly supports the omitted point. -/
theorem hullCycleSeven_boundary_pos_of_minTri_pos_geometric
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h7 : d.cycle.length = 7)
    (p : Fin 8) (hpOutside : p ∉ Set.range (d.castGet h7))
    (hmin : 0 < minTri v) (i : Fin 7) :
    0 < sig (v (d.castGet h7 i))
      (v (d.castGet h7 (i + 1))) (v p) := by
  have hnonneg := hullCycleSeven_boundary_nonneg_of_outside_geometric
    hcycle h7 p hpOutside i
  have hc : Function.Injective (d.castGet h7) :=
    HullCycleData.castGet_injective d h7 hcycle.nodup
  have hiSucc : i ≠ i + 1 := by
    fin_cases i <;> decide
  have hcycleNe : d.castGet h7 i ≠ d.castGet h7 (i + 1) :=
    hc.ne hiSucc
  have hiPoint : d.castGet h7 i ≠ p := by
    intro h
    exact hpOutside ⟨i, h⟩
  have hsuccPoint : d.castGet h7 (i + 1) ≠ p := by
    intro h
    exact hpOutside ⟨i + 1, h⟩
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    hcycleNe hiPoint hsuccPoint
  have hne : sig (v (d.castGet h7 i))
      (v (d.castGet h7 (i + 1))) (v p) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hfloor
    linarith
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- A genuine seven-cycle and an omitted label construct the complete strict
radial geometry packet. -/
theorem strictHullSevenInterior_of_hullCycle_geometric
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h7 : d.cycle.length = 7)
    (p : Fin 8) (hpOutside : p ∉ Set.range (d.castGet h7))
    (hmin : 0 < minTri v) :
    StrictHullSevenInterior
      (fun i => v (d.castGet h7 i)) (v p) := by
  have hstrict : StrictCyclicPos (d.castGet h7) v :=
    HullCycleData.strictCyclicPos_cast d h7 hcycle.strictCyclicPos
  have hc : Function.Injective (d.castGet h7) :=
    HullCycleData.castGet_injective d h7 hcycle.nodup
  constructor
  · intro i j k hij hjk
    exact hstrict.pos i j k hij hjk
  · intro i
    simpa [hullSevenShift] using
      hullCycleSeven_boundary_pos_of_minTri_pos_geometric
        hcycle h7 p hpOutside hmin i
  · intro i offset
    have hindex : i ≠
        hullSevenShift i (hullSevenRowOffset offset) := by
      fin_cases i <;> fin_cases offset <;>
        simp [hullSevenShift, hullSevenRowOffset]
    have hcycleNe : d.castGet h7 i ≠
        d.castGet h7 (hullSevenShift i
          (hullSevenRowOffset offset)) := hc.ne hindex
    have hiPoint : d.castGet h7 i ≠ p := by
      intro h
      exact hpOutside ⟨i, h⟩
    have hjPoint : d.castGet h7
        (hullSevenShift i (hullSevenRowOffset offset)) ≠ p := by
      intro h
      exact hpOutside
        ⟨hullSevenShift i (hullSevenRowOffset offset), h⟩
    have hfloor := minTri_le_abs_sig_of_pairwise_ne v
      hcycleNe hiPoint hjPoint
    intro hzero
    rw [hzero, abs_zero] at hfloor
    linarith

/-- Any map from seven positions to eight labels omits a label. -/
theorem exists_offCycle_finSeven_finEight_geometric
    (c : Fin 7 → Fin 8) :
    ∃ p : Fin 8, p ∉ Set.range c := by
  by_contra hnone
  push_neg at hnone
  have hsurjective : Function.Surjective c := by
    intro p
    exact hnone p
  have hcard := Fintype.card_le_of_surjective c hsurjective
  norm_num at hcard

/-- Geometry-only universal wheel packet; the exact fan-area identity can be
attached by the caller from `HullCycleOf.isHullArea`. -/
theorem exists_strictHullSevenInterior_geometric
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h7 : d.cycle.length = 7)
    (hmin : 0 < minTri v) :
    ∃ p : Fin 8,
      p ∉ Set.range (d.castGet h7) ∧
      StrictHullSevenInterior
        (fun i => v (d.castGet h7 i)) (v p) := by
  obtain ⟨p, hpOutside⟩ := exists_offCycle_finSeven_finEight_geometric
    (d.castGet h7)
  exact ⟨p, hpOutside,
    strictHullSevenInterior_of_hullCycle_geometric
      hcycle h7 p hpOutside hmin⟩

end

end Heilbronn8
