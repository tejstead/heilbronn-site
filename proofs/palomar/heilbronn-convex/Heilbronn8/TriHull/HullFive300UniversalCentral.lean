import Heilbronn8.TriHull.HullFive300SameSector
import Heilbronn8.TriHull.HullFive300SectorDichotomy
import Heilbronn8.TriHull.HullFive300UniversalAdjacent

set_option maxHeartbeats 0

/-!
# Complete hull-five central dispatcher

The hull labels are fixed as

`A = 0, B = 1, X = 4, C = 2, D = 3`,

and the three points in `ABC` are `P = 5, Q = 6, R = 7`.
The fan-sector dichotomy chooses one of the three interior points as anchor.
A repeated sector is closed by the same-sector adapter; the distinguished
adjacent pair is closed by the full adjacent adapter.  Interior relabellings
are genuine permutations, so `minTri_relabel` transports the result without
reproving any normalized floor.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private lemma sig_ne_zero_of_minTri_pos
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [hzero, abs_zero] at hmin
  linarith

private lemma strictCyclicPos_relabel_of_cycle_fixed
    (v : Fin 8 → Point) (sigma : Equiv.Perm (Fin 8))
    (hfix : ∀ i : Fin 5,
      sigma (![0, 1, 4, 2, 3] i) = ![0, 1, 4, 2, 3] i)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v) :
    StrictCyclicPos ![0, 1, 4, 2, 3] (fun i ↦ v (sigma i)) := by
  refine ⟨?_, ?_⟩
  · intro i j k hij hjk
    simpa only [hfix i, hfix j, hfix k] using
      hcycle.1 i j k hij hjk
  · intro i j k hij hjk
    simpa only [hfix i, hfix j, hfix k] using
      hcycle.2 i j k hij hjk

/-- A point strictly in `ABC` lies on the positive side of all five oriented
edges of the strict pentagon `A-B-X-C-D`. -/
private lemma interior_abc_pentagon_fan_pos
    (v : Fin 8 → Point)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v)
    {S : Point} (hS : InTriStrict S (v 0) (v 1) (v 2)) :
    0 < sig S (v 1) (v 4) ∧
    0 < sig S (v 4) (v 2) ∧
    0 < sig S (v 2) (v 3) ∧
    0 < sig S (v 3) (v 0) ∧
    0 < sig S (v 0) (v 1) := by
  have hABC : 0 < sig (v 0) (v 1) (v 2) := by
    simpa using hcycle.pos 0 1 3 (by decide) (by decide)
  have hABX : 0 < sig (v 0) (v 1) (v 4) := by
    simpa using hcycle.pos 0 1 2 (by decide) (by decide)
  have hAXC : 0 < sig (v 0) (v 4) (v 2) := by
    simpa using hcycle.pos 0 2 3 (by decide) (by decide)
  have hBXC : 0 < sig (v 1) (v 4) (v 2) := by
    simpa using hcycle.pos 1 2 3 (by decide) (by decide)
  have hACD : 0 < sig (v 0) (v 2) (v 3) := by
    simpa using hcycle.pos 0 3 4 (by decide) (by decide)
  have hBCD : 0 < sig (v 1) (v 2) (v 3) := by
    simpa using hcycle.pos 1 3 4 (by decide) (by decide)
  have hABD : 0 < sig (v 0) (v 1) (v 3) := by
    simpa using hcycle.pos 0 1 4 (by decide) (by decide)
  have hCBX : 0 < sig (v 2) (v 1) (v 4) := by
    rwa [sig_rotate (v 2) (v 1) (v 4)]
  have hBDA : 0 < sig (v 1) (v 3) (v 0) := by
    rw [sig_rotate (v 1) (v 3) (v 0),
      sig_rotate (v 3) (v 0) (v 1)]
    exact hABD
  have hCDA : 0 < sig (v 2) (v 3) (v 0) := by
    rw [sig_rotate (v 2) (v 3) (v 0),
      sig_rotate (v 3) (v 0) (v 2)]
    exact hACD
  obtain ⟨hSBC, hSCA, hSAB⟩ := inTriStrict_fan_pos hABC hS

  have pos_of_abc_mul {t : ℝ}
      (hprod : 0 < sig (v 0) (v 1) (v 2) * t) : 0 < t := by
    by_contra hn
    have ht : t ≤ 0 := le_of_not_gt hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hABC.le ht
    linarith

  have hSBXId :
      sig (v 0) (v 1) (v 2) * sig S (v 1) (v 4) =
        sig S (v 1) (v 2) * sig (v 0) (v 1) (v 4) +
        sig S (v 0) (v 1) * sig (v 2) (v 1) (v 4) := by
    simp only [sig]
    ring
  have hSBX : 0 < sig S (v 1) (v 4) := by
    apply pos_of_abc_mul
    rw [hSBXId]
    exact add_pos (mul_pos hSBC hABX) (mul_pos hSAB hCBX)

  have hSXCId :
      sig (v 0) (v 1) (v 2) * sig S (v 4) (v 2) =
        sig S (v 1) (v 2) * sig (v 0) (v 4) (v 2) +
        sig S (v 2) (v 0) * sig (v 1) (v 4) (v 2) := by
    simp only [sig]
    ring
  have hSXC : 0 < sig S (v 4) (v 2) := by
    apply pos_of_abc_mul
    rw [hSXCId]
    exact add_pos (mul_pos hSBC hAXC) (mul_pos hSCA hBXC)

  have hSCDId :
      sig (v 0) (v 1) (v 2) * sig S (v 2) (v 3) =
        sig S (v 1) (v 2) * sig (v 0) (v 2) (v 3) +
        sig S (v 2) (v 0) * sig (v 1) (v 2) (v 3) := by
    simp only [sig]
    ring
  have hSCD : 0 < sig S (v 2) (v 3) := by
    apply pos_of_abc_mul
    rw [hSCDId]
    exact add_pos (mul_pos hSBC hACD) (mul_pos hSCA hBCD)

  have hSDAId :
      sig (v 0) (v 1) (v 2) * sig S (v 3) (v 0) =
        sig S (v 2) (v 0) * sig (v 1) (v 3) (v 0) +
        sig S (v 0) (v 1) * sig (v 2) (v 3) (v 0) := by
    simp only [sig]
    ring
  have hSDA : 0 < sig S (v 3) (v 0) := by
    apply pos_of_abc_mul
    rw [hSDAId]
    exact add_pos (mul_pos hSCA hBDA) (mul_pos hSAB hCDA)

  exact ⟨hSBX, hSXC, hSCD, hSDA, hSAB⟩

private lemma adjacentCell_of_cycle
    (v : Fin 8 → Point)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v)
    (hP : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 7) (v 0) (v 1) (v 2))
    (hQsector : InTriStrict (v 6) (v 5) (v 1) (v 2))
    (hRsector : InTriStrict (v 7) (v 5) (v 2) (v 0)) :
    HullFive300AdjacentCell v := by
  have hABC : 0 < sig (v 0) (v 1) (v 2) := by
    simpa using hcycle.pos 0 1 3 (by decide) (by decide)
  have hBXC : 0 < sig (v 1) (v 4) (v 2) := by
    simpa using hcycle.pos 1 2 3 (by decide) (by decide)
  have hACD : 0 < sig (v 0) (v 2) (v 3) := by
    simpa using hcycle.pos 0 3 4 (by decide) (by decide)
  have hCDA : 0 < sig (v 2) (v 3) (v 0) := by
    rw [sig_rotate (v 2) (v 3) (v 0),
      sig_rotate (v 3) (v 0) (v 2)]
    exact hACD
  obtain ⟨hPBX, hPXC, hPCD, hPDA, _hPAB⟩ :=
    interior_abc_pentagon_fan_pos v hcycle hP
  obtain ⟨hQBX, hQXC, hQCD, _hQDA, _hQAB⟩ :=
    interior_abc_pentagon_fan_pos v hcycle hQ
  obtain ⟨_hRBX, hRXC, hRCD, hRDA, _hRAB⟩ :=
    interior_abc_pentagon_fan_pos v hcycle hR
  exact {
    abc_pos := hABC
    p_in_abc := hP
    q_in_pbc := hQsector
    r_in_pca := hRsector
    qbx_pos := hQBX
    qxc_pos := hQXC
    rcd_pos := hRCD
    rda_pos := hRDA
    pbx_pos := hPBX
    pxc_pos := hPXC
    pcd_pos := hPCD
    pda_pos := hPDA
    bxc_pos := hBXC
    cda_pos := hCDA
    rxc_pos := hRXC
    qcd_pos := hQCD }

private theorem adjacent_ordered_forces_canonical_fan
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v)
    (hP : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 7) (v 0) (v 1) (v 2))
    (hQsector : InTriStrict (v 6) (v 5) (v 1) (v 2))
    (hRsector : InTriStrict (v 7) (v 5) (v 2) (v 0)) :
    minTri v * 25 ≤
      2 * (sig (v 0) (v 1) (v 4) +
        sig (v 0) (v 4) (v 2) + sig (v 0) (v 2) (v 3)) := by
  have hbound := hullFive300_adjacent_forces_fan_bound v hm
    (adjacentCell_of_cycle v hcycle hP hQ hR hQsector hRsector)
  calc
    minTri v * 25 ≤
        2 * (sig (v 5) (v 1) (v 4) +
          sig (v 5) (v 4) (v 2) +
          sig (v 5) (v 2) (v 3) +
          sig (v 5) (v 3) (v 0) +
          sig (v 5) (v 0) (v 1)) := hbound
    _ = 2 * (sig (v 0) (v 1) (v 4) +
        sig (v 0) (v 4) (v 2) + sig (v 0) (v 2) (v 3)) := by
      simp only [sig]
      ring

private lemma swapSixSeven_apply (i : Fin 8) :
    (Equiv.swap (6 : Fin 8) 7) i = ![0, 1, 2, 3, 4, 5, 7, 6] i := by
  fin_cases i <;> simp [Equiv.swap_apply_def]

private theorem adjacent_either_forces_canonical_fan
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v)
    (hP : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 7) (v 0) (v 1) (v 2))
    (hadj : AdjacentABFanSectorsAt
      (v 5) (v 6) (v 7) (v 0) (v 1) (v 2)) :
    minTri v * 25 ≤
      2 * (sig (v 0) (v 1) (v 4) +
        sig (v 0) (v 4) (v 2) + sig (v 0) (v 2) (v 3)) := by
  rcases hadj with hadj | hadj
  · exact adjacent_ordered_forces_canonical_fan v hm hcycle hP hQ hR
      (by simpa [InFanCell] using hadj.1)
      (by simpa [InFanCell] using hadj.2)
  · let sigma : Equiv.Perm (Fin 8) := Equiv.swap 6 7
    let w : Fin 8 → Point := fun i ↦ v (sigma i)
    have hmin : minTri w = minTri v := by
      simpa only [w] using minTri_relabel v sigma
    have hmw : 0 < minTri w := by rw [hmin]; exact hm
    have hwcycle : StrictCyclicPos ![0, 1, 4, 2, 3] w := by
      simpa only [w] using
        strictCyclicPos_relabel_of_cycle_fixed v sigma (by
          intro i
          fin_cases i <;> simp [sigma, swapSixSeven_apply]) hcycle
    have hbound := adjacent_ordered_forces_canonical_fan w hmw hwcycle
      (by simpa [w, sigma, swapSixSeven_apply] using hP)
      (by simpa [w, sigma, swapSixSeven_apply] using hR)
      (by simpa [w, sigma, swapSixSeven_apply] using hQ)
      (by simpa [w, sigma, swapSixSeven_apply, InFanCell] using hadj.2)
      (by simpa [w, sigma, swapSixSeven_apply, InFanCell] using hadj.1)
    rw [hmin] at hbound
    simpa [w, sigma, swapSixSeven_apply] using hbound

private theorem sameSector_forces_canonical_fan
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v)
    (hP : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hsame : SameFanSectorAt
      (v 5) (v 6) (v 7) (v 0) (v 1) (v 2)) :
    minTri v * 25 ≤
      2 * (sig (v 0) (v 1) (v 4) +
        sig (v 0) (v 4) (v 2) + sig (v 0) (v 2) (v 3)) := by
  have hABC : 0 < sig (v 0) (v 1) (v 2) := by
    simpa using hcycle.pos 0 1 3 (by decide) (by decide)
  have hBXC : 0 < sig (v 1) (v 4) (v 2) := by
    simpa using hcycle.pos 1 2 3 (by decide) (by decide)
  have hACD : 0 < sig (v 0) (v 2) (v 3) := by
    simpa using hcycle.pos 0 3 4 (by decide) (by decide)
  have hCDA : 0 < sig (v 2) (v 3) (v 0) := by
    rw [sig_rotate (v 2) (v 3) (v 0),
      sig_rotate (v 3) (v 0) (v 2)]
    exact hACD
  rcases hsame with ⟨i, hQsector, hRsector⟩
  have hsectors :
      (InTriStrict (v 6) (v 5) (v 1) (v 2) ∧
        InTriStrict (v 7) (v 5) (v 1) (v 2)) ∨
      (InTriStrict (v 6) (v 5) (v 2) (v 0) ∧
        InTriStrict (v 7) (v 5) (v 2) (v 0)) ∨
      (InTriStrict (v 6) (v 5) (v 0) (v 1) ∧
        InTriStrict (v 7) (v 5) (v 0) (v 1)) := by
    fin_cases i
    · exact Or.inl ⟨by simpa [InFanCell] using hQsector,
        by simpa [InFanCell] using hRsector⟩
    · exact Or.inr (Or.inl ⟨by simpa [InFanCell] using hQsector,
        by simpa [InFanCell] using hRsector⟩)
    · exact Or.inr (Or.inr ⟨by simpa [InFanCell] using hQsector,
        by simpa [InFanCell] using hRsector⟩)
  have hbound := hullFive300_sameSector_forces_fan_bound v hm {
    abc_pos := hABC
    p_in_abc := hP
    same_sector := hsectors
    bxc_pos := hBXC
    cda_pos := hCDA }
  calc
    minTri v * 25 ≤
        2 * (sig (v 5) (v 1) (v 4) +
          sig (v 5) (v 4) (v 2) +
          sig (v 5) (v 2) (v 3) +
          sig (v 5) (v 3) (v 0) +
          sig (v 5) (v 0) (v 1)) := hbound
    _ = 2 * (sig (v 0) (v 1) (v 4) +
        sig (v 0) (v 4) (v 2) + sig (v 0) (v 2) (v 3)) := by
      simp only [sig]
      ring

private def anchorQPerm : Equiv.Perm (Fin 8) := Equiv.swap 5 6

private def anchorRPerm : Equiv.Perm (Fin 8) :=
  (Equiv.swap 5 7).trans (Equiv.swap 5 6)

private lemma anchorQPerm_apply (i : Fin 8) :
    anchorQPerm i = ![0, 1, 2, 3, 4, 6, 5, 7] i := by
  fin_cases i <;> simp [anchorQPerm, Equiv.swap_apply_def]

private lemma anchorRPerm_apply (i : Fin 8) :
    anchorRPerm i = ![0, 1, 2, 3, 4, 7, 5, 6] i := by
  fin_cases i <;> simp [anchorRPerm, Equiv.swap_apply_def]

/-- Three points in the central triangle of a strict hull pentagon force the
full hull fan bound.  No fan-sector choice or determinant sign is assumed. -/
theorem hullFive300_allCentral_forces_fan_bound
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3] v)
    (hP : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 7) (v 0) (v 1) (v 2)) :
    minTri v * 25 ≤
      2 * (sig (v 0) (v 1) (v 4) +
        sig (v 0) (v 4) (v 2) + sig (v 0) (v 2) (v 3)) := by
  have hABC : 0 < sig (v 0) (v 1) (v 2) := by
    simpa using hcycle.pos 0 1 3 (by decide) (by decide)
  have hPQ : FanPairGeneric (v 5) (v 6) (v 0) (v 1) (v 2) :=
    ⟨sig_ne_zero_of_minTri_pos v hm (i := 5) (j := 0) (k := 6)
        (by decide) (by decide) (by decide),
      sig_ne_zero_of_minTri_pos v hm (i := 5) (j := 1) (k := 6)
        (by decide) (by decide) (by decide),
      sig_ne_zero_of_minTri_pos v hm (i := 5) (j := 2) (k := 6)
        (by decide) (by decide) (by decide)⟩
  have hPR : FanPairGeneric (v 5) (v 7) (v 0) (v 1) (v 2) :=
    ⟨sig_ne_zero_of_minTri_pos v hm (i := 5) (j := 0) (k := 7)
        (by decide) (by decide) (by decide),
      sig_ne_zero_of_minTri_pos v hm (i := 5) (j := 1) (k := 7)
        (by decide) (by decide) (by decide),
      sig_ne_zero_of_minTri_pos v hm (i := 5) (j := 2) (k := 7)
        (by decide) (by decide) (by decide)⟩
  have hQR : FanPairGeneric (v 6) (v 7) (v 0) (v 1) (v 2) :=
    ⟨sig_ne_zero_of_minTri_pos v hm (i := 6) (j := 0) (k := 7)
        (by decide) (by decide) (by decide),
      sig_ne_zero_of_minTri_pos v hm (i := 6) (j := 1) (k := 7)
        (by decide) (by decide) (by decide),
      sig_ne_zero_of_minTri_pos v hm (i := 6) (j := 2) (k := 7)
        (by decide) (by decide) (by decide)⟩
  rcases three_point_fan_sector_dichotomy hABC hP hQ hR hPQ hPR hQR with
      hsame | hadj
  · rcases hsame with hsame | hsame | hsame
    · exact sameSector_forces_canonical_fan v hm hcycle hP hsame
    · let sigma : Equiv.Perm (Fin 8) := anchorQPerm
      let w : Fin 8 → Point := fun i ↦ v (sigma i)
      have hmin : minTri w = minTri v := by
        simpa only [w] using minTri_relabel v sigma
      have hmw : 0 < minTri w := by rw [hmin]; exact hm
      have hwcycle : StrictCyclicPos ![0, 1, 4, 2, 3] w := by
        simpa only [w] using
          strictCyclicPos_relabel_of_cycle_fixed v sigma (by
            intro i
            fin_cases i <;> simp [sigma, anchorQPerm_apply]) hcycle
      have hbound := sameSector_forces_canonical_fan w hmw hwcycle
        (by simpa [w, sigma, anchorQPerm_apply] using hQ)
        (by simpa [w, sigma, anchorQPerm_apply] using hsame)
      rw [hmin] at hbound
      simpa [w, sigma, anchorQPerm_apply] using hbound
    · let sigma : Equiv.Perm (Fin 8) := anchorRPerm
      let w : Fin 8 → Point := fun i ↦ v (sigma i)
      have hmin : minTri w = minTri v := by
        simpa only [w] using minTri_relabel v sigma
      have hmw : 0 < minTri w := by rw [hmin]; exact hm
      have hwcycle : StrictCyclicPos ![0, 1, 4, 2, 3] w := by
        simpa only [w] using
          strictCyclicPos_relabel_of_cycle_fixed v sigma (by
            intro i
            fin_cases i <;> simp [sigma, anchorRPerm_apply]) hcycle
      have hbound := sameSector_forces_canonical_fan w hmw hwcycle
        (by simpa [w, sigma, anchorRPerm_apply] using hR)
        (by simpa [w, sigma, anchorRPerm_apply] using hsame)
      rw [hmin] at hbound
      simpa [w, sigma, anchorRPerm_apply] using hbound
  · rcases hadj with hadj | hadj | hadj
    · exact adjacent_either_forces_canonical_fan v hm hcycle hP hQ hR hadj
    · let sigma : Equiv.Perm (Fin 8) := anchorQPerm
      let w : Fin 8 → Point := fun i ↦ v (sigma i)
      have hmin : minTri w = minTri v := by
        simpa only [w] using minTri_relabel v sigma
      have hmw : 0 < minTri w := by rw [hmin]; exact hm
      have hwcycle : StrictCyclicPos ![0, 1, 4, 2, 3] w := by
        simpa only [w] using
          strictCyclicPos_relabel_of_cycle_fixed v sigma (by
            intro i
            fin_cases i <;> simp [sigma, anchorQPerm_apply]) hcycle
      have hbound := adjacent_either_forces_canonical_fan w hmw hwcycle
        (by simpa [w, sigma, anchorQPerm_apply] using hQ)
        (by simpa [w, sigma, anchorQPerm_apply] using hP)
        (by simpa [w, sigma, anchorQPerm_apply] using hR)
        (by simpa [w, sigma, anchorQPerm_apply] using hadj)
      rw [hmin] at hbound
      simpa [w, sigma, anchorQPerm_apply] using hbound
    · let sigma : Equiv.Perm (Fin 8) := anchorRPerm
      let w : Fin 8 → Point := fun i ↦ v (sigma i)
      have hmin : minTri w = minTri v := by
        simpa only [w] using minTri_relabel v sigma
      have hmw : 0 < minTri w := by rw [hmin]; exact hm
      have hwcycle : StrictCyclicPos ![0, 1, 4, 2, 3] w := by
        simpa only [w] using
          strictCyclicPos_relabel_of_cycle_fixed v sigma (by
            intro i
            fin_cases i <;> simp [sigma, anchorRPerm_apply]) hcycle
      have hbound := adjacent_either_forces_canonical_fan w hmw hwcycle
        (by simpa [w, sigma, anchorRPerm_apply] using hR)
        (by simpa [w, sigma, anchorRPerm_apply] using hP)
        (by simpa [w, sigma, anchorRPerm_apply] using hQ)
        (by simpa [w, sigma, anchorRPerm_apply] using hadj)
      rw [hmin] at hbound
      simpa [w, sigma, anchorRPerm_apply] using hbound

/-- Arbitrary-label form of `hullFive300_allCentral_forces_fan_bound`.
The permutation slots still have the semantic order `A,B,C,D,X,P,Q,R`. -/
theorem hullFive300_allCentral_relabel_forces_fan_bound
    (v : Fin 8 → Point) (sigma : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcycle : StrictCyclicPos ![0, 1, 4, 2, 3]
      (fun i ↦ v (sigma i)))
    (hP : InTriStrict (v (sigma 5))
      (v (sigma 0)) (v (sigma 1)) (v (sigma 2)))
    (hQ : InTriStrict (v (sigma 6))
      (v (sigma 0)) (v (sigma 1)) (v (sigma 2)))
    (hR : InTriStrict (v (sigma 7))
      (v (sigma 0)) (v (sigma 1)) (v (sigma 2))) :
    minTri v * 25 ≤
      2 * (sig (v (sigma 0)) (v (sigma 1)) (v (sigma 4)) +
        sig (v (sigma 0)) (v (sigma 4)) (v (sigma 2)) +
        sig (v (sigma 0)) (v (sigma 2)) (v (sigma 3))) := by
  let w : Fin 8 → Point := fun i ↦ v (sigma i)
  have hmin : minTri w = minTri v := by
    simpa only [w] using minTri_relabel v sigma
  have hmw : 0 < minTri w := by rw [hmin]; exact hm
  have hbound := hullFive300_allCentral_forces_fan_bound w hmw
    (by simpa only [w] using hcycle)
    (by simpa only [w] using hP)
    (by simpa only [w] using hQ)
    (by simpa only [w] using hR)
  rw [hmin] at hbound
  simpa only [w] using hbound

end Heilbronn8.TriHull
