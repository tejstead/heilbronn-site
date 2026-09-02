import Heilbronn8.ReferenceQuotient
import Heilbronn8.HullCycleFanCover
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# Honest reflected custody for hull-six `2 + 4` packets

The finite complement-rotation of a `2 x 4` Ferrers table is not a symmetry
inside one fixed geometric frame.  It is, however, realized by an honest
operation on the whole configuration:

* reflect every point by the reference-triangle symmetry `(x,y) |-> (y,x)`;
* reverse the six-cycle, starting at the second upper vertex;
* exchange the two exterior base points.

The reflected cell based at the reversed indices has determinants

```text
(X',Y') = (-Y,-X),
```

so the exact chamber table is `T.rotateComplement`.  This module rebuilds
the complete compact residual on the reflected configuration and exposes
the resulting exact-packet provider transport.  It contains no q-weakening
claim and no same-configuration symmetry premise.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Heilbronn8

/-! ## The physical reflection and the reversed six-cycle -/

/-- The fixed orientation-reversing reflection used by the custody layer. -/
def hullSixReflectionPoint (x : ℝ × ℝ) : ℝ × ℝ :=
  referenceTransform symmetry021 x

/-- Apply the physical reflection without relabelling any configuration slot. -/
def hullSixReflectedConfiguration (cfg : Configuration) : Configuration :=
  fun i => hullSixReflectionPoint (cfg i)

/-- Reverse a six-cycle about the edge ending at `rotation + 1`. -/
def hullSixReverseAt (rotation i : Fin 6) : Fin 6 :=
  rotation + 1 - i

/-- The reflected cycle is reversed so that it is counterclockwise again. -/
def hullSixReflectedCycle
    (cycle : Fin 6 -> Fin 8) (rotation : Fin 6) : Fin 6 -> Fin 8 :=
  fun i => cycle (hullSixReverseAt rotation i)

@[simp] theorem referenceDet_symmetry021 :
    referenceDet symmetry021 = (-1 : ℝ) := by
  change sig (0, 0) (0, 1) (1, 0) = (-1 : ℝ)
  norm_num [sig]

@[simp] theorem sig_hullSixReflectionPoint (P Q R : ℝ × ℝ) :
    sig (hullSixReflectionPoint P) (hullSixReflectionPoint Q)
        (hullSixReflectionPoint R) = -sig P Q R := by
  change sig (referenceTransform symmetry021 P)
      (referenceTransform symmetry021 Q)
      (referenceTransform symmetry021 R) = -sig P Q R
  rw [sig_referenceTransform, referenceDet_symmetry021]
  ring

/-- Reflection and exchange of the first two points cancel their two sign
reversals. -/
theorem sig_hullSixReflectionPoint_swapFirst (P Q R : ℝ × ℝ) :
    sig (hullSixReflectionPoint Q) (hullSixReflectionPoint P)
        (hullSixReflectionPoint R) = sig P Q R := by
  rw [sig_hullSixReflectionPoint, sig_swap_first P Q R]
  ring

@[simp] theorem minTri_hullSixReflectedConfiguration
    (cfg : Configuration) :
    minTri (hullSixReflectedConfiguration cfg) = minTri cfg := by
  change minTri (fun i => referenceTransform symmetry021 (cfg i)) = minTri cfg
  exact minTri_referenceTransform symmetry021 cfg

@[simp] theorem doubledHullArea_hullSixReflectedConfiguration
    (cfg : Configuration) :
    doubledHullArea (hullSixReflectedConfiguration cfg) =
      doubledHullArea cfg := by
  change doubledHullArea (fun i => referenceTransform symmetry021 (cfg i)) =
    doubledHullArea cfg
  exact doubledHullArea_referenceTransform symmetry021 cfg

@[simp] theorem hullSixReverseAt_involutive
    (rotation i : Fin 6) :
    hullSixReverseAt rotation (hullSixReverseAt rotation i) = i := by
  fin_cases rotation <;> fin_cases i <;> decide

theorem hullSixReverseAt_injective (rotation : Fin 6) :
    Function.Injective (hullSixReverseAt rotation) := by
  intro i j hij
  rw [← hullSixReverseAt_involutive rotation i,
    ← hullSixReverseAt_involutive rotation j, hij]

theorem hullSixReverseAt_surjective (rotation : Fin 6) :
    Function.Surjective (hullSixReverseAt rotation) := by
  intro i
  exact ⟨hullSixReverseAt rotation i,
    hullSixReverseAt_involutive rotation i⟩

@[simp] theorem hullSixReflectedCycle_reverseAt
    (cycle : Fin 6 -> Fin 8) (rotation i : Fin 6) :
    hullSixReflectedCycle cycle rotation (hullSixReverseAt rotation i) =
      cycle i := by
  simp [hullSixReflectedCycle]

theorem range_hullSixReflectedCycle
    (cycle : Fin 6 -> Fin 8) (rotation : Fin 6) :
    Set.range (hullSixReflectedCycle cycle rotation) = Set.range cycle := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨hullSixReverseAt rotation i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨hullSixReverseAt rotation i, by simp⟩

@[simp] theorem hullSixReverseAt_succ
    (rotation i : Fin 6) :
    hullSixReverseAt rotation (i + 1) + 1 =
      hullSixReverseAt rotation i := by
  fin_cases rotation <;> fin_cases i <;> decide

@[simp] theorem hullSixReverseAt_upperOffset
    (rotation : Fin 6) (i : Fin 2) :
    hullSixReverseAt rotation (hullSixTwoFourUpperOffset i) =
      rotation + hullSixTwoFourUpperOffset (hullSixReverseFinTwo i) := by
  fin_cases rotation <;> fin_cases i <;> decide

@[simp] theorem hullSixReverseAt_lowerOffset
    (rotation : Fin 6) (j : Fin 4) :
    hullSixReverseAt rotation (hullSixTwoFourLowerOffset j) =
      rotation + hullSixTwoFourLowerOffset (hullSixReverseFinFour j) := by
  fin_cases rotation <;> fin_cases j <;> decide

/-- Total cyclic variation is invariant under the negated cycle reversal. -/
theorem cyclicVariationFinSix_neg_reverseAt
    (g : Fin 6 -> ℝ) (rotation : Fin 6) :
    cyclicVariationFinSix
        (fun i => -g (hullSixReverseAt rotation i)) =
      cyclicVariationFinSix g := by
  fin_cases rotation <;>
    simp [cyclicVariationFinSix, hullSixReverseAt, Fin.neg_def] <;> ring

/-! ## Strict cyclicity and fan containment after reflection -/

/-- Three indices occur in positive cyclic order on a six-cycle. -/
private def HullSixCyclicOrder (i j k : Fin 6) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)

private theorem StrictCyclicPos.pos_of_hullSixCyclicOrder
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8}
    (h : StrictCyclicPos cycle cfg) {i j k : Fin 6}
    (horder : HullSixCyclicOrder i j k) :
    0 < sig (cfg (cycle i)) (cfg (cycle j)) (cfg (cycle k)) := by
  rcases horder with hijk | hjki | hkij
  · exact h.pos i j k hijk.1 hijk.2
  · rw [sig_rotate]
    exact h.pos j k i hjki.1 hjki.2
  · rw [sig_rotate, sig_rotate]
    exact h.pos k i j hkij.1 hkij.2

private theorem hullSixReverseAt_cyclicOrder :
    ∀ (rotation i j k : Fin 6), i < j -> j < k ->
      HullSixCyclicOrder
        (hullSixReverseAt rotation i)
        (hullSixReverseAt rotation k)
        (hullSixReverseAt rotation j) := by
  intro rotation i j k hij hjk
  fin_cases rotation <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [HullSixCyclicOrder, hullSixReverseAt, Fin.neg_def]

/-- Reflection and cycle reversal together preserve strict counterclockwise
cyclicity. -/
theorem StrictCyclicPos.hullSixReflectionReverse
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8}
    (h : StrictCyclicPos cycle cfg) (rotation : Fin 6) :
    StrictCyclicPos
      (hullSixReflectedCycle cycle rotation)
      (hullSixReflectedConfiguration cfg) := by
  have hpos (i j k : Fin 6) (hij : i < j) (hjk : j < k) :
      0 < sig
        ((hullSixReflectedConfiguration cfg)
          (hullSixReflectedCycle cycle rotation i))
        ((hullSixReflectedConfiguration cfg)
          (hullSixReflectedCycle cycle rotation j))
        ((hullSixReflectedConfiguration cfg)
          (hullSixReflectedCycle cycle rotation k)) := by
    have hsource := h.pos_of_hullSixCyclicOrder
      (hullSixReverseAt_cyclicOrder rotation i j k hij hjk)
    calc
      0 < sig
          (cfg (cycle (hullSixReverseAt rotation i)))
          (cfg (cycle (hullSixReverseAt rotation k)))
          (cfg (cycle (hullSixReverseAt rotation j))) := hsource
      _ = -sig
          (cfg (cycle (hullSixReverseAt rotation i)))
          (cfg (cycle (hullSixReverseAt rotation j)))
          (cfg (cycle (hullSixReverseAt rotation k))) := by
            rw [sig_swap]
      _ = sig
          ((hullSixReflectedConfiguration cfg)
            (hullSixReflectedCycle cycle rotation i))
          ((hullSixReflectedConfiguration cfg)
            (hullSixReflectedCycle cycle rotation j))
          ((hullSixReflectedConfiguration cfg)
            (hullSixReflectedCycle cycle rotation k)) := by
            simp [hullSixReflectedConfiguration,
              hullSixReflectedCycle]
  refine ⟨?_, ?_⟩
  · intro i j k hij hjk
    exact (hpos i j k hij hjk).le
  · intro i j k hij hjk
    exact ne_of_gt (hpos i j k hij hjk)

/-- Barycentric triangle membership is preserved by every reference
symmetry, including the reflection used here. -/
private theorem inTri_referenceTransform
    (g : ReferenceSymmetry) {P A B C : ℝ × ℝ}
    (h : InTri P A B C) :
    InTri (referenceTransform g P)
      (referenceTransform g A) (referenceTransform g B)
      (referenceTransform g C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hP⟩ := h
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  have hxcoeff : x = 1 - y - z := by linarith
  have hsource :
      x • A + y • B + z • C =
        affineCombination (y, z) A B C := by
    rw [hxcoeff]
    apply Prod.ext <;>
      simp [affineCombination, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
      ring
  have htarget :
      affineCombination (y, z) (referenceTransform g A)
          (referenceTransform g B) (referenceTransform g C) =
        x • referenceTransform g A + y • referenceTransform g B +
          z • referenceTransform g C := by
    rw [hxcoeff]
    apply Prod.ext <;>
      simp [affineCombination, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
      ring
  rw [hP, hsource, referenceTransform_affineCombination, htarget]

/-- Source fan containment transports to convex-hull containment for the
reflected and reversed cycle. -/
private theorem reflected_range_subset_cycle_convexHull
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8}
    (hcover : FanCovers cfg cycle) (rotation : Fin 6) :
    Set.range (hullSixReflectedConfiguration cfg) ⊆
      convexHull ℝ
        (Set.range
          (hullSixReflectedConfiguration cfg ∘
            hullSixReflectedCycle cycle rotation)) := by
  rintro _ ⟨p, rfl⟩
  by_cases hp : p ∈ Set.range cycle
  · obtain ⟨i, hi⟩ := hp
    apply subset_convexHull
    refine ⟨hullSixReverseAt rotation i, ?_⟩
    simp [Function.comp_apply, hi]
  · obtain ⟨i, j, _hi, _hij, htri⟩ := hcover p hp
    have htri' := inTri_referenceTransform symmetry021 htri
    have hmem := (inTri_iff_mem_convexHull _ _ _ _).1 htri'
    apply convexHull_mono ?_ hmem
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff,
      Set.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨hullSixReverseAt rotation 0, by
        simp [Function.comp_apply, hullSixReflectedConfiguration,
          hullSixReflectionPoint]⟩
    · exact ⟨hullSixReverseAt rotation i, by
        simp [Function.comp_apply, hullSixReflectedConfiguration,
          hullSixReflectionPoint]⟩
    · exact ⟨hullSixReverseAt rotation j, by
        simp [Function.comp_apply, hullSixReflectedConfiguration,
          hullSixReflectionPoint]⟩

/-- A raw strict six-cycle and its fan cover orient every boundary triangle
based at an off-cycle label. -/
private theorem sixCycle_boundary_pos_of_strict_fan
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8}
    (hinj : Function.Injective cycle)
    (hstrict : StrictCyclicPos cycle cfg)
    (hcover : FanCovers cfg cycle)
    (p : Fin 8) (hp : p ∉ Set.range cycle)
    (hmin : 0 < minTri cfg) (i : Fin 6) :
    0 < sig (cfg p) (cfg (cycle i)) (cfg (cycle (i + 1))) := by
  obtain ⟨j, k, _hj, _hjk, htri⟩ := hcover p hp
  have hnonnegCycle :
      0 ≤ sig (cfg (cycle i)) (cfg (cycle (i + 1))) (cfg p) :=
    sig_nonneg_of_inTri
      (cfg p) (cfg (cycle 0)) (cfg (cycle j)) (cfg (cycle k))
      (cfg (cycle i)) (cfg (cycle (i + 1))) htri
      (strictCyclicPos_six_boundary_nonneg hstrict i 0)
      (strictCyclicPos_six_boundary_nonneg hstrict i j)
      (strictCyclicPos_six_boundary_nonneg hstrict i k)
  have hnonneg :
      0 ≤ sig (cfg p) (cfg (cycle i)) (cfg (cycle (i + 1))) := by
    rwa [sig_rotate]
  have hsucc : i ≠ i + 1 := by
    fin_cases i <;> decide
  have hp0 : p ≠ cycle i := by
    intro h
    exact hp ⟨i, h.symm⟩
  have hp1 : p ≠ cycle (i + 1) := by
    intro h
    exact hp ⟨i + 1, h.symm⟩
  have h01 : cycle i ≠ cycle (i + 1) := hinj.ne hsucc
  have hfloor := minTri_le_abs_sig_of_pairwise_ne cfg hp0 hp1 h01
  have hne :
      sig (cfg p) (cfg (cycle i)) (cfg (cycle (i + 1))) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hfloor
    exact (not_le_of_gt hmin) hfloor
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-! ## Reconstruction of the complete compact residual -/

namespace HullSixCompactCrossChordResidual

/-- Rebuild the compact residual on the reflected configuration and reversed
cycle.  All labels are retained verbatim. -/
noncomputable def reflectReverse
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (rotation : Fin 6) :
    HullSixCompactCrossChordResidual
      (hullSixReflectedConfiguration cfg)
      (hullSixReflectedCycle cycle rotation) p q := by
  let cfg' := hullSixReflectedConfiguration cfg
  let cycle' := hullSixReflectedCycle cycle rotation
  have hinj : Function.Injective cycle' :=
    R.cycle_injective.comp (hullSixReverseAt_injective rotation)
  have hstrict : StrictCyclicPos cycle' cfg' := by
    simpa [cfg', cycle'] using R.cycle_strict.hullSixReflectionReverse rotation
  have hcontain :
      Set.range cfg' ⊆ convexHull ℝ (Set.range (cfg' ∘ cycle')) := by
    simpa [cfg', cycle'] using
      reflected_range_subset_cycle_convexHull R.cycle_covers rotation
  have hcover : FanCovers cfg' cycle' :=
    fanCovers_of_strictCyclicPos_of_convexHull
      cfg' cycle' (by norm_num) hinj hstrict hcontain
  have hHullArea : doubledHullArea cfg' = fanSum cfg' cycle' :=
    doubledHullArea_eq_of_isHullArea
      (IsHullArea.hull6 cycle' hinj hstrict hcover rfl :
        IsHullArea cfg' (fanSum cfg' cycle'))
  have hpOutside : p ∉ Set.range cycle' := by
    rw [show Set.range cycle' = Set.range cycle by
      simpa [cycle'] using range_hullSixReflectedCycle cycle rotation]
    exact R.p_outside
  have hqOutside : q ∉ Set.range cycle' := by
    rw [show Set.range cycle' = Set.range cycle by
      simpa [cycle'] using range_hullSixReflectedCycle cycle rotation]
    exact R.q_outside
  have hareaEq : doubledHullArea cfg' = doubledHullArea cfg := by
    simp [cfg']
  have hminEq : minTri cfg' = minTri cfg := by
    simp [cfg']
  have hpPos : ∀ i,
      0 < sig (cfg' p) (cfg' (cycle' i)) (cfg' (cycle' (i + 1))) := by
    intro i
    exact sixCycle_boundary_pos_of_strict_fan
      hinj hstrict hcover p hpOutside (by
        rw [hminEq]
        exact R.minTri_pos) i
  have hqPos : ∀ i,
      0 < sig (cfg' q) (cfg' (cycle' i)) (cfg' (cycle' (i + 1))) := by
    intro i
    exact sixCycle_boundary_pos_of_strict_fan
      hinj hstrict hcover q hqOutside (by
        rw [hminEq]
        exact R.minTri_pos) i
  have hpSum :
      sumFinSix (fun i =>
        sig (cfg' p) (cfg' (cycle' i)) (cfg' (cycle' (i + 1)))) =
        doubledHullArea cfg' := by
    calc
      sumFinSix (fun i =>
          sig (cfg' p) (cfg' (cycle' i)) (cfg' (cycle' (i + 1)))) =
          fanSum cfg' cycle' := sumFinSix_boundary_eq_fanSum cfg' cycle' p
      _ = doubledHullArea cfg' := hHullArea.symm
  have hqSum :
      sumFinSix (fun i =>
        sig (cfg' q) (cfg' (cycle' i)) (cfg' (cycle' (i + 1)))) =
        doubledHullArea cfg' := by
    calc
      sumFinSix (fun i =>
          sig (cfg' q) (cfg' (cycle' i)) (cfg' (cycle' (i + 1)))) =
          fanSum cfg' cycle' := sumFinSix_boundary_eq_fanSum cfg' cycle' q
      _ = doubledHullArea cfg' := hHullArea.symm
  have hlevel (i : Fin 6) :
      minTri cfg' ≤ |sig (cfg' p) (cfg' q) (cfg' (cycle' i))| := by
    apply minTri_le_abs_sig_of_pairwise_ne cfg' R.p_ne_q
    · intro h
      exact hpOutside ⟨i, h.symm⟩
    · intro h
      exact hqOutside ⟨i, h.symm⟩
  have hlevelFun :
      (fun i => sig (cfg' p) (cfg' q) (cfg' (cycle' i))) =
        (fun i => -sig (cfg p) (cfg q)
          (cfg (cycle (hullSixReverseAt rotation i)))) := by
    funext i
    simp [cfg', cycle', hullSixReflectedConfiguration,
      hullSixReflectedCycle]
  have hvariation :
      cyclicVariationFinSix
          (fun i => sig (cfg' p) (cfg' q) (cfg' (cycle' i))) <
        13 * minTri cfg' := by
    rw [hlevelFun,
      cyclicVariationFinSix_neg_reverseAt
        (fun i => sig (cfg p) (cfg q) (cfg (cycle i))) rotation]
    rw [hminEq]
    exact R.variation_lt
  have hspread (iLo iHi : Fin 6) :
      sig (cfg' p) (cfg' q) (cfg' (cycle' iHi)) -
          sig (cfg' p) (cfg' q) (cfg' (cycle' iLo)) <
        13 * minTri cfg' / 2 := by
    have harcs := two_mul_sub_le_cyclicVariationFinSix
      (fun i => sig (cfg' p) (cfg' q) (cfg' (cycle' i))) iLo iHi
    linarith
  have hstraddles := sixCycle_lineLevels_straddle_minTri
    cfg' cycle' hcover p q R.p_ne_q hpOutside hqOutside
  refine
    { cycle_injective := hinj
      cycle_strict := hstrict
      cycle_covers := hcover
      hull_area_eq := hHullArea
      p_ne_q := R.p_ne_q
      p_outside := hpOutside
      q_outside := hqOutside
      hullArea_pos := by
        rw [hareaEq]
        exact R.hullArea_pos
      cut_margin := by
        rw [hareaEq, hminEq]
        exact R.cut_margin
      minTri_pos := by
        rw [hminEq]
        exact R.minTri_pos
      p_boundary_pos := hpPos
      q_boundary_pos := hqPos
      p_fan_sum := hpSum
      q_fan_sum := hqSum
      lineLevel_floor := hlevel
      variation_lt := hvariation
      lineLevel_spread_lt := hspread
      straddles := hstraddles
      crossChord := by
        intro i j hij
        have hpi : p ≠ cycle' i := by
          intro h
          exact hpOutside ⟨i, h.symm⟩
        have hpj : p ≠ cycle' j := by
          intro h
          exact hpOutside ⟨j, h.symm⟩
        have hqi : q ≠ cycle' i := by
          intro h
          exact hqOutside ⟨i, h.symm⟩
        have hqj : q ≠ cycle' j := by
          intro h
          exact hqOutside ⟨j, h.symm⟩
        have hcij : cycle' i ≠ cycle' j := hinj.ne hij
        have hconstraint := sixCycle_crossChord_constraint
          cfg' cycle' hinj p q hpOutside hqOutside i j hij
        exact ⟨minTri_le_abs_sig_of_pairwise_ne cfg' hpi hpj hcij,
          minTri_le_abs_sig_of_pairwise_ne cfg' hqi hqj hcij,
          hconstraint.1, hconstraint.2⟩
      plucker := by
        intro i0 i1 j0 j1
        exact sig_crossChord_plucker
          (cfg' p) (cfg' (cycle' i0)) (cfg' (cycle' i1))
          (cfg' (cycle' j0)) (cfg' (cycle' j1)) }

end HullSixCompactCrossChordResidual

/-! ## Reflected oriented frame and exact table transport -/

private theorem hullSixIsOrientedPair_swap
    {p q P Q : Fin 8} (h : HullSixIsOrientedPair p q P Q) :
    HullSixIsOrientedPair p q Q P := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

private noncomputable def orientedViewOfPair
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (h : HullSixIsOrientedPair p q P Q) :
    HullSixOrientedView cfg cycle P Q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact R.forwardOrientedView
  · exact R.swappedOrientedView

namespace HullSixTwoFourGeometricFrame

/-- The honest reflected frame realizing finite complement-rotation. -/
noncomputable def reflectedRotateComplement
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    HullSixTwoFourGeometricFrame (R.reflectReverse F.rotation) where
  P := F.Q
  Q := F.P
  pair := hullSixIsOrientedPair_swap F.pair
  view := orientedViewOfPair (R.reflectReverse F.rotation)
    (hullSixIsOrientedPair_swap F.pair)
  rotation := 0
  upper_pos := by
    intro i
    have h := F.upper_pos (hullSixReverseFinTwo i)
    simp only [hullSixReflectedConfiguration, hullSixReflectedCycle,
      zero_add]
    rw [sig_hullSixReflectionPoint_swapFirst,
      hullSixReverseAt_upperOffset]
    exact h
  lower_neg := by
    intro j
    have h := F.lower_neg (hullSixReverseFinFour j)
    simp only [hullSixReflectedConfiguration, hullSixReflectedCycle,
      zero_add]
    rw [sig_hullSixReflectionPoint_swapFirst,
      hullSixReverseAt_lowerOffset]
    exact h

@[simp] theorem reflectedRotateComplement_P
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    F.reflectedRotateComplement.P = F.Q := rfl

@[simp] theorem reflectedRotateComplement_Q
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    F.reflectedRotateComplement.Q = F.P := rfl

@[simp] theorem reflectedRotateComplement_rotation
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    F.reflectedRotateComplement.rotation = 0 := rfl

/-- Exact realization transports to the complement-rotated table in the
reflected configuration. -/
theorem tableHolds_reflectedRotateComplement
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    {T : HullSixTwoFourCuts} (hLegal : T.Legal)
    (hTable : F.TableHolds T) :
    F.reflectedRotateComplement.TableHolds T.rotateComplement := by
  intro i j
  rw [HullSixTwoFourCuts.table_rotateComplement T hLegal i j]
  have hsource := hTable
    (hullSixReverseFinTwo i) (hullSixReverseFinFour j)
  have hcomplement :=
    (HullSixChamberLabel.holds_complement_neg_swap_iff
      (T.table (hullSixReverseFinTwo i) (hullSixReverseFinFour j))
      (minTri cfg)
      (sig (cfg F.P)
        (cfg (cycle (F.rotation +
          hullSixTwoFourUpperOffset (hullSixReverseFinTwo i))))
        (cfg (cycle (F.rotation +
          hullSixTwoFourLowerOffset (hullSixReverseFinFour j)))))
      (sig (cfg F.Q)
        (cfg (cycle (F.rotation +
          hullSixTwoFourUpperOffset (hullSixReverseFinTwo i))))
        (cfg (cycle (F.rotation +
          hullSixTwoFourLowerOffset (hullSixReverseFinFour j)))))).2 hsource
  simpa [TableHolds, reflectedRotateComplement,
    hullSixReflectedConfiguration, hullSixReflectedCycle] using hcomplement

end HullSixTwoFourGeometricFrame

/-! ## Provider-level exact symmetry -/

/-- Pull an exact packet provider back through honest physical reflection.
This is the sound replacement for same-configuration symmetry custody. -/
theorem hullSixTwoFourExactPacketProvider_rotateComplement
    {Packet : HullSixTwoFourCuts -> Prop}
    (hPacket : HullSixTwoFourExactPacketProvider Packet) :
    HullSixTwoFourExactPacketProvider
      (fun T => Packet T.rotateComplement) := by
  intro cfg cycle p q R F
  intro T hLegal hTarget hTable
  exact hPacket F.reflectedRotateComplement T.rotateComplement
    (HullSixTwoFourCuts.legal_rotateComplement T hLegal)
    hTarget
    (F.tableHolds_reflectedRotateComplement hLegal hTable)

end Heilbronn8
