import Solution.N7

/-!
Canonical, corpus-free integration seam for the convex `n = 7` upper bound.

This scratch module is deliberately written against `Solution.N7` and
`HullBridge`, rather than against the separate `proofs/convex-n7/heil7`
development.  In particular, `minTri` below is the challenge's finite-infimum
definition and `doubledHullArea` is twice Lebesgue area.  The eventual four
hull-case proofs can therefore plug into the submitted theorem without a
35-leaf minimum-conversion lemma.

The module contains no assertion of the four open geometric inequalities.  It
packages their exact common interface and proves all downstream bookkeeping.
For a standalone check, put the Palomar directory containing `Solution/` and
`HullBridge.lean` on `LEAN_PATH`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

open MeasureTheory

abbrev Configuration7 := Fin 7 → ℝ × ℝ

/-- The first `h` points are a strictly counter-clockwise convex polygon. -/
def HullCCW (v : Configuration7) (h : ℕ) : Prop :=
  ∀ i j k : Fin 7, i < j → j < k → (k : ℕ) < h →
    0 < sig (v i) (v j) (v k)

/-- Every point after the first `h` labels is strictly behind every directed
boundary edge of the first `h` labels. -/
def InHullN (v : Configuration7) (h : ℕ) (p : Fin 7) : Prop :=
  (∀ i : Fin 7, (i : ℕ) + 1 < h →
      0 < sig (v i) (v (i + 1)) (v p)) ∧
  (∀ j : Fin 7, (j : ℕ) + 1 = h →
      0 < sig (v j) (v 0) (v p))

/-- Doubled polygon area, triangulated from hull vertex zero. -/
def fanArea (v : Configuration7) (h : ℕ) : ℝ :=
  match h with
  | 3 => sig (v 0) (v 1) (v 2)
  | 4 => sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)
  | 5 => sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) +
      sig (v 0) (v 3) (v 4)
  | 6 => sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) +
      sig (v 0) (v 3) (v 4) + sig (v 0) (v 4) (v 5)
  | 7 => sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) +
      sig (v 0) (v 3) (v 4) + sig (v 0) (v 4) (v 5) +
      sig (v 0) (v 5) (v 6)
  | _ => 0

/-! ### The existing hull-seven reduction -/

/-- Cutting the three alternating ears leaves the quadrilateral on
`0, 2, 4, 6`. -/
lemma hept_ear_decomp (v : Configuration7) :
    fanArea v 7 =
      sig (v 0) (v 1) (v 2) + sig (v 2) (v 3) (v 4) +
      sig (v 4) (v 5) (v 6) +
      (sig (v 0) (v 2) (v 4) + sig (v 0) (v 4) (v 6)) := by
  simp only [fanArea, sig]
  ring

/-- The exact open helper currently used by the standalone hull-seven file. -/
def HullSevenQuadBound : Prop :=
  ∀ (v : Configuration7), HullCCW v 7 →
    6 * minTri v ≤
      sig (v 0) (v 2) (v 4) + sig (v 0) (v 4) (v 6)

/-- The alternating-quadrilateral helper implies the required hull-seven
bound. This adapter is lossless at the regular heptagon. -/
theorem hullSeven_of_quad (Q : HullSevenQuadBound) (v : Configuration7)
    (hq : HullCCW v 7) :
    9 * minTri v ≤ fanArea v 7 := by
  have one : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      0 < sig (v i) (v j) (v k) →
      minTri v ≤ sig (v i) (v j) (v k) := by
    intro i j k hij hik hjk hp
    have h := minTri_le_of_distinct v i j k hij hik hjk
    rwa [abs_of_pos hp] at h
  have e012 := one 0 1 2 (by decide) (by decide) (by decide)
    (hq 0 1 2 (by decide) (by decide) (by decide))
  have e234 := one 2 3 4 (by decide) (by decide) (by decide)
    (hq 2 3 4 (by decide) (by decide) (by decide))
  have e456 := one 4 5 6 (by decide) (by decide) (by decide)
    (hq 4 5 6 (by decide) (by decide) (by decide))
  have hquad := Q v hq
  have hid := hept_ear_decomp v
  linarith

/-- Exact insertion points for the hull-size proofs.  `h3` is already closed
in the standalone development.  The other four fields are precisely the four
remaining hull-size conclusions; no certificate or corpus assumption is
hidden in this structure.  In particular, `h7` asks only for the required
whole-polygon bound.  The stronger historical `HullSevenQuadBound` can supply
it through `hullSeven_of_quad`, but is not forced on a future Yang--Zeng
formalization. -/
structure HullCaseBounds : Prop where
  h3 : ∀ (v : Configuration7), HullCCW v 3 →
    (∀ p : Fin 7, 3 ≤ (p : ℕ) → InHullN v 3 p) →
    9 * minTri v ≤ fanArea v 3
  h4 : ∀ (v : Configuration7), HullCCW v 4 →
    (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
    9 * minTri v ≤ fanArea v 4
  h5 : ∀ (v : Configuration7), HullCCW v 5 →
    (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
    9 * minTri v ≤ fanArea v 5
  h6 : ∀ (v : Configuration7), HullCCW v 6 →
    (∀ p : Fin 7, 6 ≤ (p : ℕ) → InHullN v 6 p) →
    9 * minTri v ≤ fanArea v 6
  h7 : ∀ (v : Configuration7), HullCCW v 7 →
    9 * minTri v ≤ fanArea v 7

theorem HullCaseBounds.labelled (B : HullCaseBounds) (v : Configuration7)
    (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 7) (hccw : HullCCW v h)
    (hin : ∀ p : Fin 7, h ≤ (p : ℕ) → InHullN v h p) :
    9 * minTri v ≤ fanArea v h := by
  interval_cases h
  · exact B.h3 v hccw hin
  · exact B.h4 v hccw hin
  · exact B.h5 v hccw hin
  · exact B.h6 v hccw hin
  · exact B.h7 v hccw

/-! ### Relabeling -/

lemma minTri_le_relabel (v : Configuration7) (σ : Equiv.Perm (Fin 7)) :
    minTri v ≤ minTri (v ∘ σ) := by
  apply le_minTri
  rintro ⟨i, j, k⟩ ht
  have hijk : i < j ∧ j < k := by
    simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  exact minTri_le_of_distinct v (σ i) (σ j) (σ k)
    (σ.injective.ne (ne_of_lt hijk.1))
    (σ.injective.ne (ne_of_lt (lt_trans hijk.1 hijk.2)))
    (σ.injective.ne (ne_of_lt hijk.2))

lemma minTri_relabel (v : Configuration7) (σ : Equiv.Perm (Fin 7)) :
    minTri (v ∘ σ) = minTri v := by
  apply le_antisymm
  · have h := minTri_le_relabel (v ∘ σ) σ.symm
    have hcancel : (v ∘ σ) ∘ σ.symm = v := by
      funext i
      simp
    rw [hcancel] at h
    exact h
  · exact minTri_le_relabel v σ

lemma doubledHullArea_relabel (v : Configuration7)
    (σ : Equiv.Perm (Fin 7)) :
    HullBridge.doubledHullArea (v ∘ σ) =
      HullBridge.doubledHullArea v := by
  have hrange : Set.range (v ∘ σ) = Set.range v :=
    σ.surjective.range_comp v
  simp only [HullBridge.doubledHullArea, hrange]

/-! ### Hull classification seam -/

/-- A classifier supplies only standard finite convex geometry: either a zero
triangle already closes the estimate, or a relabeling puts the configuration
in hull-first order and identifies the polygon fan with Lebesgue hull area. -/
def HullClassified (v : Configuration7) : Prop :=
  minTri v = 0 ∨
    ∃ (h : ℕ) (σ : Equiv.Perm (Fin 7)),
      3 ≤ h ∧ h ≤ 7 ∧ HullCCW (v ∘ σ) h ∧
      (∀ p : Fin 7, h ≤ (p : ℕ) → InHullN (v ∘ σ) h p) ∧
      HullBridge.doubledHullArea v = fanArea (v ∘ σ) h

/-- All theorem-specific work is now confined to `HullCaseBounds`; all
configuration bookkeeping is confined to `HullClassified`. -/
theorem nine_minTri_le_doubledHullArea
    (B : HullCaseBounds) (classify : ∀ v : Configuration7, HullClassified v)
    (v : Configuration7) :
    9 * minTri v ≤ HullBridge.doubledHullArea v := by
  rcases classify v with hzero | ⟨h, σ, hlo, hhi, hccw, hin, harea⟩
  · rw [hzero]
    simpa using HullBridge.doubledHullArea_nonneg v
  · have hb := B.labelled (v ∘ σ) h hlo hhi hccw hin
    rw [minTri_relabel v σ, ← harea] at hb
    exact hb

/-- The coordinate-level statement proved by Yang--Zeng, expressed directly
with the canonical finite minimum and doubled Lebesgue hull area.  Formalizing
this one statement directly is an alternative to exposing its hull cases. -/
def SevenPointAreaBound : Prop :=
  ∀ v : Configuration7,
    9 * minTri v ≤ HullBridge.doubledHullArea v

/-- The canonical challenge theorem follows immediately from the universal
doubled-area inequality and the already proved rational attainment witness. -/
theorem heilbronn_convex_seven_of_area_bound
    (bound : SevenPointAreaBound) :
    h_convex 7 = v7 := by
  apply h_convex_eq v7 v7_admissible
  intro r hr
  rcases hr with ⟨_, _, p, hvolume, hmin⟩
  have hub := bound p
  have harea := HullBridge.doubledHullArea_of_unit_volume hvolume
  rw [hmin, harea] at hub
  rw [v7]
  norm_num at hub ⊢
  linarith

/-- Hull-case formalizations feed the same canonical endpoint through the
standard finite hull classifier. -/
theorem heilbronn_convex_seven
    (B : HullCaseBounds) (classify : ∀ v : Configuration7, HullClassified v) :
    h_convex 7 = v7 :=
  heilbronn_convex_seven_of_area_bound
    (fun v => nine_minTri_le_doubledHullArea B classify v)

end HeilbronnChallenge.N7Upper
