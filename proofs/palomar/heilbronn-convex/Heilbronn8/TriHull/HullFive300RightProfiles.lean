import Heilbronn8.UniversalHullFiveGeometry
import Heilbronn8.TriHull.Bridge
import Heilbronn8.TriHull.HullFive300RightProfilesScalar

/-!
# Geometry wrappers for two right-ear `300` profiles

This module closes the `CCA` and `CAA` constructors of
`HullFive300RightProfilePacket`.  The cyclic chart is the sequential chart
`A-B-X-C-D`.  The remaining `CAB` constructor is deliberately not claimed
here.

The proof uses only the three-point triangle bound in `BXC`, two copies of
the two-point triangle bound, one-point fan floors, and pentagon determinant
identities.  It does not use retained words or generated certificates.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private lemma minTri_le_reindexed_sig_of_pos
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v (e i)) (v (e j)) (v (e k))) :
    minTri v ≤ sig (v (e i)) (v (e j)) (v (e k)) := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v
    (a := e i) (b := e j) (c := e k)
    (fun h ↦ hij (he h)) (fun h ↦ hik (he h))
    (fun h ↦ hjk (he h))
  simpa [abs_of_pos hpos] using hmin

private lemma three_mul_minTri_le_reindexed_sig_of_mem
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    {p a b c : Fin 8}
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpos : 0 < sig (v (e a)) (v (e b)) (v (e c)))
    (hmem : InTriStrict (v (e p))
      (v (e a)) (v (e b)) (v (e c))) :
    3 * minTri v ≤ sig (v (e a)) (v (e b)) (v (e c)) := by
  obtain ⟨hpbc, hpca, hpab⟩ := inTriStrict_fan_pos hpos hmem
  have h1 := minTri_le_reindexed_sig_of_pos v e he
    hpb hpc hbc hpbc
  have h2 := minTri_le_reindexed_sig_of_pos v e he
    hpc hpa hac.symm hpca
  have h3 := minTri_le_reindexed_sig_of_pos v e he
    hpa hpb hab hpab
  have hsum := fan_sum (v (e p)) (v (e a)) (v (e b)) (v (e c))
  nlinarith

private lemma seven_mul_minTri_le_twoPointTriangle
    (v : Configuration) (f : Fin 5 → Fin 8)
    (hf : Function.Injective f) (hm : 0 < minTri v)
    (hpos : 0 < sig (v (f 0)) (v (f 1)) (v (f 2)))
    (hP : InTriStrict (v (f 3)) (v (f 0)) (v (f 1)) (v (f 2)))
    (hQ : InTriStrict (v (f 4)) (v (f 0)) (v (f 1)) (v (f 2))) :
    7 * minTri v ≤ sig (v (f 0)) (v (f 1)) (v (f 2)) := by
  have htwo := twoPointTriangle_normalized_lower_bound
    v f hf hm hpos hP hQ
  have hscaled :
      (4 + 2 * Real.sqrt 3) * minTri v ≤
        sig (v (f 0)) (v (f 1)) (v (f 2)) :=
    (le_div_iff₀ hm).mp htwo
  have hsqrt := MainAux.three_halves_le_sqrt_three
  have hcoef : (7 : ℝ) ≤ 4 + 2 * Real.sqrt 3 := by
    nlinarith
  have hseven :
      7 * minTri v ≤
        (4 + 2 * Real.sqrt 3) * minTri v :=
    mul_le_mul_of_nonneg_right hcoef hm.le
  exact le_trans hseven hscaled

private lemma seventeen_halves_mul_minTri_le_threePointTriangle
    (v : Configuration) (f : Fin 6 → Fin 8)
    (hf : Function.Injective f) (hm : 0 < minTri v)
    (hpos : 0 < sig (v (f 0)) (v (f 1)) (v (f 2)))
    (hP : InTriStrict (v (f 3)) (v (f 0)) (v (f 1)) (v (f 2)))
    (hQ : InTriStrict (v (f 4)) (v (f 0)) (v (f 1)) (v (f 2)))
    (hR : InTriStrict (v (f 5)) (v (f 0)) (v (f 1)) (v (f 2))) :
    (17 / 2 : ℝ) * minTri v ≤
      sig (v (f 0)) (v (f 1)) (v (f 2)) := by
  have hthree := threePointTriangle_normalized_lower_bound_unconditional
    v f hf hm hpos hP hQ hR
  exact (le_div_iff₀ hm).mp hthree

private lemma sequential_cycle_pos
    (v : Configuration) (e : Fin 8 → Fin 8)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
    0 < sig
      (v (e (hullFiveSequentialCycleSlot i)))
      (v (e (hullFiveSequentialCycleSlot j)))
      (v (e (hullFiveSequentialCycleSlot k))) :=
  hcyc.pos i j k hij hjk

/-- The exact `CCA` packet forces the pentagon fan bound. -/
theorem hullFive300_right_cca_packet_bound
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 5)
    (q : HullFiveEndRightProfileC v e 6)
    (r : HullFiveEndRightProfileA v e 7) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let T := sig (v (e 0)) (v (e 1)) (v (e 3))
  let E := sig (v (e 1)) (v (e 2)) (v (e 3))
  let U := sig (v (e 0)) (v (e 1)) (v (e 2))
  let V := sig (v (e 0)) (v (e 2)) (v (e 3))
  let Z := sig (v (e 1)) (v (e 3)) (v (e 4))
  let K := sig (v (e 4)) (v (e 1)) (v (e 2))
  let L := sig (v (e 2)) (v (e 3)) (v (e 4))
  let M := sig (v (e 0)) (v (e 2)) (v (e 4))
  let W := sig (v (e 0)) (v (e 1)) (v (e 4))
  let F := sig (v (e 0)) (v (e 3)) (v (e 4))
  let H := U + V + F

  have hTpos : 0 < T := by
    simpa [T, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 1 3
      (by decide) (by decide)
  have hEpos : 0 < E := by
    simpa [E, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 1 2 3
      (by decide) (by decide)
  have hUpos : 0 < U := by
    simpa [U, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 1 2
      (by decide) (by decide)
  have hVpos : 0 < V := by
    simpa [V, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 2 3
      (by decide) (by decide)
  have hZpos : 0 < Z := by
    simpa [Z, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 1 3 4
      (by decide) (by decide)
  have hKpos : 0 < K := by
    have h := sequential_cycle_pos v e hcyc 1 2 4
      (by decide) (by decide)
    dsimp only [K]
    rw [sig_rotate]
    exact h
  have hLpos : 0 < L := by
    simpa [L, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 2 3 4
      (by decide) (by decide)
  have hWpos : 0 < W := by
    simpa [W, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 1 4
      (by decide) (by decide)
  have hFpos : 0 < F := by
    simpa [F, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 3 4
      (by decide) (by decide)
  have hMpos : 0 < M := by
    simpa [M, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 2 4
      (by decide) (by decide)

  let fE : Fin 6 → Fin 8 := e ∘ ![1, 2, 3, 5, 6, 7]
  have hE : (17 / 2 : ℝ) * minTri v ≤ E := by
    simpa [fE, E] using
      seventeen_halves_mul_minTri_le_threePointTriangle
        v fE (e.injective.comp (by decide)) hm hEpos
        p.bxc q.bxc r.bxc

  let fU : Fin 5 → Fin 8 := e ∘ ![0, 1, 2, 5, 6]
  have hU : 7 * minTri v ≤ U := by
    simpa [fU, U] using
      seven_mul_minTri_le_twoPointTriangle
        v fU (e.injective.comp (by decide)) hm hUpos p.abx q.abx
  let fK : Fin 5 → Fin 8 := e ∘ ![4, 1, 2, 5, 6]
  have hK : 7 * minTri v ≤ K := by
    simpa [fK, K] using
      seven_mul_minTri_le_twoPointTriangle
        v fK (e.injective.comp (by decide)) hm hKpos p.dbx q.dbx
  have hV : 3 * minTri v ≤ V := by
    simpa only [V] using three_mul_minTri_le_reindexed_sig_of_mem
      v e e.injective (p := 7) (a := 0) (b := 2) (c := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hVpos r.axc
  have hL : 3 * minTri v ≤ L := by
    simpa only [L] using three_mul_minTri_le_reindexed_sig_of_mem
      v e e.injective (p := 7) (a := 2) (b := 3) (c := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hLpos r.xcd

  have hT := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide) hTpos
  have hZ := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 1) (j := 3) (k := 4) (by decide) (by decide) (by decide) hZpos
  have hW := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 4) (by decide) (by decide) (by decide) hWpos
  have hF := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 3) (k := 4) (by decide) (by decide) (by decide) hFpos
  have hM := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 2) (k := 4) (by decide) (by decide) (by decide) hMpos

  apply hullFive300_right_cca_scalar
    (m := minTri v) (E := E) (U := U) (V := V)
    (K := K) (L := L) (M := M) (W := W) (F := F) (H := H)
    hm hE hU hK hV hL hM hW hF
  · dsimp [F, M, L, V]
    simp only [sig]
    ring
  · dsimp [W, M, U, K]
    simp only [sig]
    ring
  · dsimp [E, M, V, K, U, L]
    simp only [sig]
    ring
  · dsimp [H, U, M, L, V, F]
    simp only [sig]
    ring

/-- The exact `CAA` packet forces the pentagon fan bound. -/
theorem hullFive300_right_caa_packet_bound
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileA v e 5)
    (q : HullFiveEndRightProfileA v e 6)
    (r : HullFiveEndRightProfileC v e 7) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let T := sig (v (e 0)) (v (e 1)) (v (e 3))
  let E := sig (v (e 1)) (v (e 2)) (v (e 3))
  let U := sig (v (e 0)) (v (e 1)) (v (e 2))
  let V := sig (v (e 0)) (v (e 2)) (v (e 3))
  let Z := sig (v (e 1)) (v (e 3)) (v (e 4))
  let K := sig (v (e 4)) (v (e 1)) (v (e 2))
  let L := sig (v (e 2)) (v (e 3)) (v (e 4))
  let M := sig (v (e 0)) (v (e 2)) (v (e 4))
  let W := sig (v (e 0)) (v (e 1)) (v (e 4))
  let F := sig (v (e 0)) (v (e 3)) (v (e 4))
  let H := U + V + F

  have hTpos : 0 < T := by
    simpa [T, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 1 3
      (by decide) (by decide)
  have hEpos : 0 < E := by
    simpa [E, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 1 2 3
      (by decide) (by decide)
  have hUpos : 0 < U := by
    simpa [U, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 1 2
      (by decide) (by decide)
  have hVpos : 0 < V := by
    simpa [V, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 2 3
      (by decide) (by decide)
  have hZpos : 0 < Z := by
    simpa [Z, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 1 3 4
      (by decide) (by decide)
  have hKpos : 0 < K := by
    have h := sequential_cycle_pos v e hcyc 1 2 4
      (by decide) (by decide)
    dsimp only [K]
    rw [sig_rotate]
    exact h
  have hLpos : 0 < L := by
    simpa [L, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 2 3 4
      (by decide) (by decide)
  have hWpos : 0 < W := by
    simpa [W, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 1 4
      (by decide) (by decide)
  have hFpos : 0 < F := by
    simpa [F, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 3 4
      (by decide) (by decide)
  have hMpos : 0 < M := by
    simpa [M, hullFiveSequentialCycleSlot] using
      sequential_cycle_pos v e hcyc 0 2 4
      (by decide) (by decide)

  let fE : Fin 6 → Fin 8 := e ∘ ![1, 2, 3, 5, 6, 7]
  have hE : (17 / 2 : ℝ) * minTri v ≤ E := by
    simpa [fE, E] using
      seventeen_halves_mul_minTri_le_threePointTriangle
        v fE (e.injective.comp (by decide)) hm hEpos
        p.bxc q.bxc r.bxc

  let fV : Fin 5 → Fin 8 := e ∘ ![0, 2, 3, 5, 6]
  have hV : 7 * minTri v ≤ V := by
    simpa [fV, V] using
      seven_mul_minTri_le_twoPointTriangle
        v fV (e.injective.comp (by decide)) hm hVpos p.axc q.axc
  let fL : Fin 5 → Fin 8 := e ∘ ![2, 3, 4, 5, 6]
  have hL : 7 * minTri v ≤ L := by
    simpa [fL, L] using
      seven_mul_minTri_le_twoPointTriangle
        v fL (e.injective.comp (by decide)) hm hLpos p.xcd q.xcd
  have hU : 3 * minTri v ≤ U := by
    simpa only [U] using three_mul_minTri_le_reindexed_sig_of_mem
      v e e.injective (p := 7) (a := 0) (b := 1) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hUpos r.abx
  have hK : 3 * minTri v ≤ K := by
    simpa only [K] using three_mul_minTri_le_reindexed_sig_of_mem
      v e e.injective (p := 7) (a := 4) (b := 1) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hKpos r.dbx

  have hT := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide) hTpos
  have hZ := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 1) (j := 3) (k := 4) (by decide) (by decide) (by decide) hZpos
  have hW := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 4) (by decide) (by decide) (by decide) hWpos
  have hF := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 3) (k := 4) (by decide) (by decide) (by decide) hFpos
  have hM := minTri_le_reindexed_sig_of_pos v e e.injective
    (i := 0) (j := 2) (k := 4) (by decide) (by decide) (by decide) hMpos

  apply hullFive300_right_caa_scalar
    (m := minTri v) (E := E) (U := U) (V := V)
    (K := K) (L := L) (M := M) (W := W) (F := F) (H := H)
    hm hE hV hL hU hK hM hW hF
  · dsimp [F, M, L, V]
    simp only [sig]
    ring
  · dsimp [W, M, U, K]
    simp only [sig]
    ring
  · dsimp [E, M, V, K, U, L]
    simp only [sig]
    ring
  · dsimp [H, U, M, L, V, F]
    simp only [sig]
    ring

/-- The exact remaining metric seam after the `CCA` and `CAA` Pluecker
arguments: one `A`, one `B`, and one `C` profile, with either order of the
first two inner labels. -/
def HullFive300RightMixedProfileUniversalBound : Prop :=
  ∀ (v : Configuration) (e : Equiv.Perm (Fin 8)),
    0 < minTri v →
    StrictCyclicPos hullFiveSequentialCycleSlot (fun i ↦ v (e i)) →
    ((HullFiveEndRightProfileA v e 5 ∧
        HullFiveEndRightProfileB v e 6) ∨
      (HullFiveEndRightProfileB v e 5 ∧
        HullFiveEndRightProfileA v e 6)) →
    HullFiveEndRightProfileC v e 7 →
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4)))

/-- Therefore a proof of only the mixed `CAB/CBA` seam supplies the full
right-profile contract consumed by `UniversalHullFiveGeometry`. -/
theorem hullFive300RightProfileUniversalBound_of_mixed
    (hmixed : HullFive300RightMixedProfileUniversalBound) :
    HullFive300RightProfileUniversalBound := by
  intro v e hmin hcyc packet
  cases packet with
  | cca p q r =>
      exact hullFive300_right_cca_packet_bound v e hmin hcyc p q r
  | caa p q r =>
      exact hullFive300_right_caa_packet_bound v e hmin hcyc p q r
  | cab p q r =>
      exact hmixed v e hmin hcyc (Or.inl ⟨p, q⟩) r
  | cba p q r =>
      exact hmixed v e hmin hcyc (Or.inr ⟨p, q⟩) r

#print axioms hullFive300_right_cca_packet_bound
#print axioms hullFive300_right_caa_packet_bound
#print axioms hullFive300RightProfileUniversalBound_of_mixed

end Heilbronn8.TriHull
