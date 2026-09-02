import Heil6.FiniteHullCases
import Heil6.PentagonGeometry
import Heil6.HexagonGeometry
import Heil6.HexagonGeometryRigidity
import Heil6.HullCases

set_option linter.style.header false

/-!
# Determinant and volume bounds for the four canonical six-point hull packets

This is the thin integration layer between the finite normal form and the
already isolated scalar geometry.  It also records the hull-set equalities
needed to identify each packet's fan expression with `doubledHullArea`.
-/

namespace N6Scratch
namespace HullPacketBounds

open PlanarDet

private theorem inTri_bridge {p a b c : ℝ × ℝ}
    (h : FiniteHullCases.InTri p a b c) : HullBridge.InTri p a b c := by
  simpa only [FiniteHullCases.InTri, HullBridge.InTri] using h

private theorem floor_bridge {v : Fin 6 → ℝ × ℝ} {m : ℝ}
    (h : FiniteHullCases.DistinctTriangleFloor v m) :
    ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |HullBridge.sig (v i) (v j) (v k)| := by
  simpa only [FiniteHullCases.DistinctTriangleFloor,
    PlanarDet.sig, HullBridge.sig] using h

private theorem convexHull_range_eq_of_mem
    (v : Fin 6 → ℝ × ℝ) (s : Set (ℝ × ℝ))
    (hs : s ⊆ Set.range v)
    (hall : ∀ i, v i ∈ convexHull ℝ s) :
    convexHull ℝ (Set.range v) = convexHull ℝ s := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact hall i
    · exact convex_convexHull ℝ s
  · exact convexHull_mono hs

private theorem doubledHullArea_eq_of_volume
    (v : Fin 6 → ℝ × ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (A / 2)) :
    HullBridge.doubledHullArea v = A := by
  rw [HullBridge.doubledHullArea, hvol,
    ENNReal.toReal_ofReal (div_nonneg hA (by norm_num))]
  ring

/-! ## Hull-set and fan identities -/

theorem hull3Packet_doubledHullArea
    (v : Fin 6 → ℝ × ℝ) (P : FiniteHullCases.Hull3Packet v) :
    HullBridge.doubledHullArea v = sig (v 0) (v 1) (v 2) := by
  let s : Set (ℝ × ℝ) := {v 0, v 1, v 2}
  have hs : s ⊆ Set.range v := by
    intro x hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hall : ∀ i, v i ∈ convexHull ℝ s := by
    intro i
    fin_cases i
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact inTri_bridge P.h3 |>.mem_convexHull
    · exact inTri_bridge P.h4 |>.mem_convexHull
    · exact inTri_bridge P.h5 |>.mem_convexHull
  have hhull := convexHull_range_eq_of_mem v s hs hall
  have hpos : 0 < HullBridge.sig (v 0) (v 1) (v 2) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using P.h012
  have hvol : MeasureTheory.volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (sig (v 0) (v 1) (v 2) / 2) := by
    rw [hhull]
    simpa only [s, HullBridge.sig, PlanarDet.sig] using
      HullBridge.volume_convexHull_triangle_pos (v 0) (v 1) (v 2) hpos
  exact doubledHullArea_eq_of_volume v _ (le_of_lt P.h012) hvol

theorem hull4Packet_doubledHullArea
    (v : Fin 6 → ℝ × ℝ) (P : FiniteHullCases.Hull4Packet v) :
    HullBridge.doubledHullArea v =
      sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) := by
  let s : Set (ℝ × ℝ) := {v 0, v 1, v 2, v 3}
  have hs : s ⊆ Set.range v := by
    intro x hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have h012sub : ({v 0, v 1, v 2} : Set (ℝ × ℝ)) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have h023sub : ({v 0, v 2, v 3} : Set (ℝ × ℝ)) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have extra_mem (i : Fin 6)
      (h : FiniteHullCases.InTri (v i) (v 0) (v 1) (v 2) ∨
        FiniteHullCases.InTri (v i) (v 0) (v 2) (v 3)) :
      v i ∈ convexHull ℝ s := by
    rcases h with h | h
    · exact convexHull_mono h012sub (inTri_bridge h).mem_convexHull
    · exact convexHull_mono h023sub (inTri_bridge h).mem_convexHull
  have hall : ∀ i, v i ∈ convexHull ℝ s := by
    intro i
    fin_cases i
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact extra_mem 4 P.h4
    · exact extra_mem 5 P.h5
  have hhull := convexHull_range_eq_of_mem v s hs hall
  have h012 : 0 < HullBridge.sig (v 0) (v 1) (v 2) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using P.h012
  have h013 : 0 < HullBridge.sig (v 0) (v 1) (v 3) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using P.h013
  have h023 : 0 < HullBridge.sig (v 0) (v 2) (v 3) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using P.h023
  have h123 : 0 < HullBridge.sig (v 1) (v 2) (v 3) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using P.h123
  have hvol : MeasureTheory.volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal
        ((sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)) / 2) := by
    rw [hhull]
    simpa only [s, HullBridge.sig, PlanarDet.sig] using
      HullBridge.volume_convexHull_quad
        (v 0) (v 1) (v 2) (v 3) h012 h013 h023 h123
  apply doubledHullArea_eq_of_volume v _ _ hvol
  exact add_nonneg P.h012.le P.h023.le

theorem hull5Packet_doubledHullArea
    (v : Fin 6 → ℝ × ℝ) (P : FiniteHullCases.Hull5Packet v) :
    HullBridge.doubledHullArea v =
      sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) +
        sig (v 0) (v 3) (v 4) := by
  let s : Set (ℝ × ℝ) := {v 0, v 1, v 2, v 3, v 4}
  have hs : s ⊆ Set.range v := by
    intro x hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  have h012sub : ({v 0, v 1, v 2} : Set (ℝ × ℝ)) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have h023sub : ({v 0, v 2, v 3} : Set (ℝ × ℝ)) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have h034sub : ({v 0, v 3, v 4} : Set (ℝ × ℝ)) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have h5mem : v 5 ∈ convexHull ℝ s := by
    rcases P.insideFan with h | h | h
    · exact convexHull_mono h012sub (inTri_bridge h).mem_convexHull
    · exact convexHull_mono h023sub (inTri_bridge h).mem_convexHull
    · exact convexHull_mono h034sub (inTri_bridge h).mem_convexHull
  have hall : ∀ i, v i ∈ convexHull ℝ s := by
    intro i
    fin_cases i
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact subset_convexHull ℝ s (by simp [s])
    · exact h5mem
  have hhull := convexHull_range_eq_of_mem v s hs hall
  have hp (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
      0 < HullBridge.sig (v i.castSucc) (v j.castSucc) (v k.castSucc) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using P.hullStrict i j k hij hjk
  have hvol : MeasureTheory.volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal
        ((sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) +
          sig (v 0) (v 3) (v 4)) / 2) := by
    rw [hhull]
    simpa only [s, HullBridge.sig, PlanarDet.sig] using
      HullBridge.volume_convexHull_pent
        (v 0) (v 1) (v 2) (v 3) (v 4)
        (hp 0 1 2 (by decide) (by decide))
        (hp 0 1 3 (by decide) (by decide))
        (hp 0 1 4 (by decide) (by decide))
        (hp 0 2 3 (by decide) (by decide))
        (hp 0 2 4 (by decide) (by decide))
        (hp 0 3 4 (by decide) (by decide))
        (hp 1 2 3 (by decide) (by decide))
        (hp 1 2 4 (by decide) (by decide))
        (hp 1 3 4 (by decide) (by decide))
        (hp 2 3 4 (by decide) (by decide))
  apply doubledHullArea_eq_of_volume v _ _ hvol
  have h012 := P.hullStrict 0 1 2 (by decide) (by decide)
  have h023 := P.hullStrict 0 2 3 (by decide) (by decide)
  have h034 := P.hullStrict 0 3 4 (by decide) (by decide)
  positivity

theorem hull6Packet_doubledHullArea
    (v : Fin 6 → ℝ × ℝ) (P : FiniteHullCases.Hull6Packet v) :
    HullBridge.doubledHullArea v = HexagonGeometryRigidity.fanArea v := by
  have hvol := HullBridge.volume_convexHull_strictCCW6 v
    (by simpa only [HullBridge.sig, PlanarDet.sig] using P.strict)
  apply doubledHullArea_eq_of_volume v _ _ hvol
  have h012 := P.strict 0 1 2 (by decide) (by decide)
  have h023 := P.strict 0 2 3 (by decide) (by decide)
  have h034 := P.strict 0 3 4 (by decide) (by decide)
  have h045 := P.strict 0 4 5 (by decide) (by decide)
  positivity

/-! ## Packet bounds -/

theorem hull3Packet_strict
    (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (P : FiniteHullCases.Hull3Packet v) :
    6 * m < HullBridge.doubledHullArea v := by
  have h7 := Heil6.hull3_bound v m hm (floor_bridge hmin)
    (by simpa only [HullBridge.sig, PlanarDet.sig] using P.h012)
    (inTri_bridge P.h3) (inTri_bridge P.h4) (inTri_bridge P.h5)
  rw [hull3Packet_doubledHullArea v P]
  have h7' : 7 * m ≤ sig (v 0) (v 1) (v 2) := by
    simpa only [HullBridge.sig, PlanarDet.sig] using h7
  linarith only [h7', hm]

theorem hull4Packet_bound
    (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (P : FiniteHullCases.Hull4Packet v) :
    6 * m ≤ HullBridge.doubledHullArea v := by
  have h6 := Heil6.hull4_bound v m hm (floor_bridge hmin)
    (by simpa only [HullBridge.sig, PlanarDet.sig] using P.h012)
    (by simpa only [HullBridge.sig, PlanarDet.sig] using P.h023)
    (P.h4.imp inTri_bridge inTri_bridge)
    (P.h5.imp inTri_bridge inTri_bridge)
  rw [hull4Packet_doubledHullArea v P]
  simpa only [HullBridge.sig, PlanarDet.sig] using h6

theorem hull5Packet_strict
    (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (P : FiniteHullCases.Hull5Packet v) :
    6 * m < HullBridge.doubledHullArea v := by
  have h6 := PentagonGeometry.interior_pentagon_strict v m hm
    P.hullStrict P.fan01 P.fan12 P.fan23 P.fan34 P.fan40 hmin
  rw [hull5Packet_doubledHullArea v P]
  exact h6

theorem hull6Packet_bound
    (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (P : FiniteHullCases.Hull6Packet v) :
    6 * m ≤ HullBridge.doubledHullArea v := by
  have h6 := HexagonGeometry.strictCCW_cycle_bound v m hm P.strict hmin
  rw [hull6Packet_doubledHullArea v P]
  exact h6

/-- All four packets imply the pointwise six-point upper bound. -/
theorem canonicalHullCase_bound
    (v : Fin 6 → ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m)
    (P : FiniteHullCases.CanonicalHullCase6 v) :
    6 * m ≤ HullBridge.doubledHullArea v := by
  rcases P with P | P | P | P
  · exact (hull3Packet_strict v m hm hmin P).le
  · exact hull4Packet_bound v m hm hmin P
  · exact (hull5Packet_strict v m hm hmin P).le
  · exact hull6Packet_bound v m hm hmin P

/-- Pointwise six-point upper bound from an arbitrary common lower bound on
all distinct labelled triangle areas.  This is the determinant-level theorem
needed by the final `h_convex 6` wrapper. -/
theorem six_mul_floor_le_doubledHullArea
    (v : Fin 6 → ℝ × ℝ) (m : ℝ)
    (hmin : FiniteHullCases.DistinctTriangleFloor v m) :
    6 * m ≤ HullBridge.doubledHullArea v := by
  by_cases hm : 0 < m
  · have hgp : FiniteHullCases.NoDegenerateTriple6 v := by
      intro i j k hij hik hjk hzero
      have hfloor := hmin i j k hij hik hjk
      rw [hzero, abs_zero] at hfloor
      linarith
    obtain ⟨w, hrel, P⟩ :=
      FiniteHullCases.canonicalHullCase6_complete v hgp
    have hwmin := hrel.floor hmin
    have hwbound := canonicalHullCase_bound w m hm hwmin P
    have hrange := hrel.range_eq
    simpa only [HullBridge.doubledHullArea, hrange] using hwbound
  · have hmnonpos : m ≤ 0 := le_of_not_gt hm
    have harea := HullBridge.doubledHullArea_nonneg v
    linarith

end HullPacketBounds
end N6Scratch
