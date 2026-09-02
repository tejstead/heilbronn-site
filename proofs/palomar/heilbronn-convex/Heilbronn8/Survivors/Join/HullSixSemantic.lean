import Heilbronn8.HullSixVariation
import Heilbronn8.HullDispatch
import Heilbronn8.PolyVolumeGen

/-!
# Semantic exclusion for a six-vertex hull

This file is the semantic bridge from an emitted six-cycle to the variation
estimate in `HullSixVariation`.  The two labels outside the cycle are used as
fan centres.  If their signed levels on the joining line have spread at least
`13 * minTri / 2`, the variation estimate gives

`25 * minTri <= 2 * doubledHullArea`.

Since `2 / 25 < v8`, this rules out `Beats doubledHullArea v8`.

The final section records the coordinate-free cross-chord translation and
Plucker identities.  These are the nonlinear constraints left in the compact
case, where every pair of line levels has spread less than `13 * minTri / 2`.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The explicitly unrolled boundary sum agrees with the existing six-cycle
fan expression, independently of the choice of fan centre. -/
lemma sumFinSix_boundary_eq_fanSum
    (v : Configuration) (c : Fin 6 -> Fin 8) (p : Fin 8) :
    sumFinSix (fun i => sig (v p) (v (c i)) (v (c (i + 1)))) =
      fanSum v c := by
  have h0 : (0 : Fin 6) + 1 = 1 := by decide
  have h1 : (1 : Fin 6) + 1 = 2 := by decide
  have h2 : (2 : Fin 6) + 1 = 3 := by decide
  have h3 : (3 : Fin 6) + 1 = 4 := by decide
  have h4 : (4 : Fin 6) + 1 = 5 := by decide
  have h5 : (5 : Fin 6) + 1 = 0 := by decide
  rw [fanSum_six_eq_boundary v c (v p)]
  simp only [sumFinSix, h0, h1, h2, h3, h4, h5]

/-- A positively oriented triangle with three distinct configuration labels
is bounded below by `minTri` without first sorting its labels. -/
lemma minTri_le_pos_sig_of_pairwise_ne
    (v : Configuration) {a b c : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpos : 0 < sig (v a) (v b) (v c)) :
    minTri v <= sig (v a) (v b) (v c) := by
  have h := minTri_le_abs_sig_of_pairwise_ne v hab hac hbc
  rwa [abs_of_pos hpos] at h

private lemma finSix_ne_succ (i : Fin 6) : i ≠ i + 1 := by
  fin_cases i <;> decide

/-- Every positive boundary fan triangle based at a label outside an
injective six-cycle is at least `minTri`. -/
lemma minTri_le_sixCycle_boundary_sig
    (v : Configuration) (c : Fin 6 -> Fin 8)
    (hc : Function.Injective c) (p : Fin 8)
    (hp : p ∉ Set.range c) (i : Fin 6)
    (hpos : 0 < sig (v p) (v (c i)) (v (c (i + 1)))) :
    minTri v <= sig (v p) (v (c i)) (v (c (i + 1))) := by
  apply minTri_le_pos_sig_of_pairwise_ne v
  · intro h
    exact hp ⟨i, h.symm⟩
  · intro h
    exact hp ⟨i + 1, h.symm⟩
  · intro h
    exact finSix_ne_succ i (hc h)
  · exact hpos

/-- A signed half-plane inequality propagates from the three vertices of a
containing triangle to every point of that triangle. -/
lemma sig_nonneg_of_inTri
    (x a b c r s : ℝ × ℝ) (hx : InTri x a b c)
    (ha : 0 <= sig r s a) (hb : 0 <= sig r s b)
    (hc : 0 <= sig r s c) :
    0 <= sig r s x := by
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

private lemma strictCyclicPos_consecutive_boundary_nonneg
    {m : ℕ} {v : Configuration} {c : Fin m -> Fin 8}
    (h : StrictCyclicPos c v) (i j : Fin m)
    (hij : i.val + 1 = j.val) (k : Fin m) :
    0 <= sig (v (c i)) (v (c j)) (v (c k)) := by
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

private lemma strictCyclicPos_six_closing_boundary_nonneg
    {v : Configuration} {c : Fin 6 -> Fin 8}
    (h : StrictCyclicPos c v) (k : Fin 6) :
    0 <= sig (v (c 5)) (v (c 0)) (v (c k)) := by
  by_cases hk0 : k = 0
  · subst k
    simp [sig]
  by_cases hk5 : k = 5
  · subst k
    simp [sig]
  have h0k : (0 : Fin 6) < k := Fin.pos_iff_ne_zero.mpr hk0
  have hk5' : k < (5 : Fin 6) := by omega
  calc
    0 <= sig (v (c 0)) (v (c k)) (v (c 5)) := h.1 0 k 5 h0k hk5'
    _ = sig (v (c 5)) (v (c 0)) (v (c k)) := by
      rw [sig_rotate (v (c 0)) (v (c k)) (v (c 5)),
        sig_rotate (v (c k)) (v (c 5)) (v (c 0))]

/-- Every cyclic boundary edge of a strict six-cycle supports all six cycle
vertices in its closed left half-plane. -/
lemma strictCyclicPos_six_boundary_nonneg
    {v : Configuration} {c : Fin 6 -> Fin 8}
    (h : StrictCyclicPos c v) (i k : Fin 6) :
    0 <= sig (v (c i)) (v (c (i + 1))) (v (c k)) := by
  fin_cases i
  · change 0 <= sig (v (c 0)) (v (c 1)) (v (c k))
    exact strictCyclicPos_consecutive_boundary_nonneg h 0 1 (by decide) k
  · change 0 <= sig (v (c 1)) (v (c 2)) (v (c k))
    exact strictCyclicPos_consecutive_boundary_nonneg h 1 2 (by decide) k
  · change 0 <= sig (v (c 2)) (v (c 3)) (v (c k))
    exact strictCyclicPos_consecutive_boundary_nonneg h 2 3 (by decide) k
  · change 0 <= sig (v (c 3)) (v (c 4)) (v (c k))
    exact strictCyclicPos_consecutive_boundary_nonneg h 3 4 (by decide) k
  · change 0 <= sig (v (c 4)) (v (c 5)) (v (c k))
    exact strictCyclicPos_consecutive_boundary_nonneg h 4 5 (by decide) k
  · change 0 <= sig (v (c 5)) (v (c 0)) (v (c k))
    exact strictCyclicPos_six_closing_boundary_nonneg h k

/-- `HullCycleOf.covers` upgrades to all six boundary half-planes after the
declared cycle is cast to arity six. -/
lemma hullCycleSix_boundary_nonneg_of_outside
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p : Fin 8) (hpOutside : p ∉ Set.range (d.castGet h6))
    (i : Fin 6) :
    0 <= sig (v (d.castGet h6 i))
      (v (d.castGet h6 (i + 1))) (v p) := by
  have hstrict : StrictCyclicPos (d.castGet h6) v :=
    HullCycleData.strictCyclicPos_cast d h6 hcycle.strictCyclicPos
  have hcover : FanCovers v (d.castGet h6) :=
    HullCycleData.fanCovers_cast d h6 hcycle.fanCovers
  obtain ⟨j, k, _hj, _hjk, htri⟩ := hcover p hpOutside
  exact sig_nonneg_of_inTri
    (v p) (v (d.castGet h6 0)) (v (d.castGet h6 j))
      (v (d.castGet h6 k))
      (v (d.castGet h6 i)) (v (d.castGet h6 (i + 1))) htri
    (strictCyclicPos_six_boundary_nonneg hstrict i 0)
    (strictCyclicPos_six_boundary_nonneg hstrict i j)
    (strictCyclicPos_six_boundary_nonneg hstrict i k)

/-- Positivity of `minTri` makes the preceding supporting-half-plane
inequality strict for an off-cycle configuration label. -/
lemma hullCycleSix_boundary_pos_of_minTri_pos
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p : Fin 8) (hpOutside : p ∉ Set.range (d.castGet h6))
    (hmin : 0 < minTri v) (i : Fin 6) :
    0 < sig (v p) (v (d.castGet h6 i))
      (v (d.castGet h6 (i + 1))) := by
  have hnonneg :
      0 <= sig (v p) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))) := by
    rw [sig_rotate]
    exact hullCycleSix_boundary_nonneg_of_outside
      hcycle h6 p hpOutside i
  have hc : Function.Injective (d.castGet h6) :=
    HullCycleData.castGet_injective d h6 hcycle.nodup
  have hp0 : p ≠ d.castGet h6 i := by
    intro h
    exact hpOutside ⟨i, h.symm⟩
  have hp1 : p ≠ d.castGet h6 (i + 1) := by
    intro h
    exact hpOutside ⟨i + 1, h.symm⟩
  have h01 : d.castGet h6 i ≠ d.castGet h6 (i + 1) := by
    intro h
    exact finSix_ne_succ i (hc h)
  have habs :
      0 < |sig (v p) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1)))| :=
    lt_of_lt_of_le hmin
      (minTri_le_abs_sig_of_pairwise_ne v hp0 hp1 h01)
  have hne :
      sig (v p) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at habs
    exact lt_irrefl 0 habs
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The target-shaped doubled-area estimate for an arbitrary injective
six-cycle and two off-cycle fan centres.  Convexity is used only through the
positive boundary-fan hypotheses and the exact hull-area equality. -/
theorem twentyFive_minTri_le_twice_hullArea_of_sixPairSpread
    (v : Configuration) (c : Fin 6 -> Fin 8) (p q : Fin 8)
    (hc : Function.Injective c)
    (hpOutside : p ∉ Set.range c) (hqOutside : q ∉ Set.range c)
    (hHullArea : doubledHullArea v = fanSum v c)
    (hpPos : ∀ i, 0 < sig (v p) (v (c i)) (v (c (i + 1))))
    (hqPos : ∀ i, 0 < sig (v q) (v (c i)) (v (c (i + 1))))
    (iLo iHi : Fin 6)
    (hspread :
      13 * minTri v / 2 <=
        sig (v p) (v q) (v (c iHi)) -
          sig (v p) (v q) (v (c iLo))) :
    25 * minTri v <= 2 * doubledHullArea v := by
  have hpFloor : ∀ i,
      minTri v <= sig (v p) (v (c i)) (v (c (i + 1))) := by
    intro i
    exact minTri_le_sixCycle_boundary_sig v c hc p hpOutside i (hpPos i)
  have hqFloor : ∀ i,
      minTri v <= sig (v q) (v (c i)) (v (c (i + 1))) := by
    intro i
    exact minTri_le_sixCycle_boundary_sig v c hc q hqOutside i (hqPos i)
  have hpSum :
      sumFinSix (fun i => sig (v p) (v (c i)) (v (c (i + 1)))) =
        doubledHullArea v := by
    calc
      sumFinSix (fun i => sig (v p) (v (c i)) (v (c (i + 1)))) =
          fanSum v c := sumFinSix_boundary_eq_fanSum v c p
      _ = doubledHullArea v := hHullArea.symm
  have hqSum :
      sumFinSix (fun i => sig (v q) (v (c i)) (v (c (i + 1)))) =
        doubledHullArea v := by
    calc
      sumFinSix (fun i => sig (v q) (v (c i)) (v (c (i + 1)))) =
          fanSum v c := sumFinSix_boundary_eq_fanSum v c q
      _ = doubledHullArea v := hHullArea.symm
  have hrange := geometricSixFanPairRange_bound
    (p := v p) (q := v q) (v := fun i => v (c i))
    (m := minTri v) (H := doubledHullArea v)
    hpFloor hqFloor hpSum hqSum iLo iHi
  linarith

/-- A certified emitted hull cycle supplies the exact area equality needed by
the semantic six-fan theorem. -/
theorem twentyFive_minTri_le_twice_hullArea_of_hullCycleSixPairSpread
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hpPos : ∀ i,
      0 < sig (v p) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))))
    (hqPos : ∀ i,
      0 < sig (v q) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))))
    (iLo iHi : Fin 6)
    (hspread :
      13 * minTri v / 2 <=
        sig (v p) (v q) (v (d.castGet h6 iHi)) -
          sig (v p) (v q) (v (d.castGet h6 iLo))) :
    25 * minTri v <= 2 * doubledHullArea v := by
  have hcertified : doubledHullArea v = d.fanExpr v :=
    doubledHullArea_eq_of_isHullArea hcycle.isHullArea
  have hcast : fanSum v (d.castGet h6) = d.fanExpr v :=
    HullCycleData.fanSum_castGet d h6
  have hHullArea : doubledHullArea v = fanSum v (d.castGet h6) :=
    hcertified.trans hcast.symm
  exact twentyFive_minTri_le_twice_hullArea_of_sixPairSpread
    v (d.castGet h6) p q
    (HullCycleData.castGet_injective d h6 hcycle.nodup)
    hpOutside hqOutside hHullArea hpPos hqPos iLo iHi hspread

/-- The rational cutoff delivered by the six-fan estimate is strictly below
the certified optimum. -/
theorem two_div_twentyFive_lt_v8 : (2 / 25 : ℝ) < v8 := by
  calc
    (2 / 25 : ℝ) < (80000139329466 : ℝ) / 10 ^ 15 := by norm_num
    _ < v8 := v8_lb

/-- Semantic h=6 exclusion in the exact `Beats` language used by the strict
residual spine. -/
theorem not_Beats_v8_of_hullCycleSixPairSpread_of_boundaryPos
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hpPos : ∀ i,
      0 < sig (v p) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))))
    (hqPos : ∀ i,
      0 < sig (v q) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))))
    (iLo iHi : Fin 6)
    (hspread :
      13 * minTri v / 2 <=
        sig (v p) (v q) (v (d.castGet h6 iHi)) -
          sig (v p) (v q) (v (d.castGet h6 iLo))) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  have hbound :=
    twentyFive_minTri_le_twice_hullArea_of_hullCycleSixPairSpread
      hcycle h6 p q hpOutside hqOutside hpPos hqPos iLo iHi
        hspread
  have hcut :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    lt_trans
      (mul_lt_mul_of_pos_right two_div_twentyFive_lt_v8 hbeat.1)
      hbeat.2
  nlinarith

/-- Compact semantic h=6 exclusion.  Boundary positivity is not additional
generated data: it follows from `HullCycleOf.covers`, and `Beats` makes it
strict by forcing `minTri` to be positive. -/
theorem not_Beats_v8_of_hullCycleSixPairSpread
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (iLo iHi : Fin 6)
    (hspread :
      13 * minTri v / 2 <=
        sig (v p) (v q) (v (d.castGet h6 iHi)) -
          sig (v p) (v q) (v (d.castGet h6 iLo))) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  have hscaled : 0 < v8 * doubledHullArea v :=
    mul_pos v8_pos hbeat.1
  have hmin : 0 < minTri v := lt_trans hscaled hbeat.2
  have hpPos : ∀ i,
      0 < sig (v p) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))) := by
    intro i
    exact hullCycleSix_boundary_pos_of_minTri_pos
      hcycle h6 p hpOutside hmin i
  have hqPos : ∀ i,
      0 < sig (v q) (v (d.castGet h6 i))
        (v (d.castGet h6 (i + 1))) := by
    intro i
    exact hullCycleSix_boundary_pos_of_minTri_pos
      hcycle h6 q hqOutside hmin i
  exact (not_Beats_v8_of_hullCycleSixPairSpread_of_boundaryPos
    hcycle h6 p q hpOutside hqOutside hpPos hqPos iLo iHi
      hspread) hbeat

/-- Sign-oracle form of the semantic exclusion theorem.  This is the form an
emitted strict hull branch can discharge without restating determinant
inequalities by hand. -/
theorem not_Beats_v8_of_hullCycleSixPairSpread_signs
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hpSigns : ∀ i,
      S.ccw p (d.castGet h6 i) (d.castGet h6 (i + 1)) = true)
    (hqSigns : ∀ i,
      S.ccw q (d.castGet h6 i) (d.castGet h6 (i + 1)) = true)
    (iLo iHi : Fin 6)
    (hspread :
      13 * minTri v / 2 <=
        sig (v p) (v q) (v (d.castGet h6 iHi)) -
          sig (v p) (v q) (v (d.castGet h6 iLo))) :
    ¬ Beats doubledHullArea v8 v := by
  exact not_Beats_v8_of_hullCycleSixPairSpread_of_boundaryPos
    hcycle h6 p q hpOutside hqOutside
    (fun i => S.pos_of_eq_true _ _ _ (hpSigns i))
    (fun i => S.pos_of_eq_true _ _ _ (hqSigns i))
    iLo iHi hspread

/-! ## The compact cross-chord residual -/

/-- Changing the base point of a cross chord translates it by the two line
levels.  In coordinates with `p = (0,0)` and `q = (1,0)`, this is the usual
formula `X' = X + u + v` for an upper/lower pair. -/
lemma sig_crossChord_base_change (p q u l : ℝ × ℝ) :
    sig q u l = sig p u l + sig p q u - sig p q l := by
  simp only [sig]
  ring

/-- Every adjacent `2 x 2` cross-chord minor is the product of the two
same-side chord areas.  This is the Plucker constraint absent from the linear
fan-variation relaxation. -/
lemma sig_crossChord_plucker
    (p u0 u1 l0 l1 : ℝ × ℝ) :
    sig p u0 l0 * sig p u1 l1 -
        sig p u0 l1 * sig p u1 l0 =
      sig p u0 u1 * sig p l0 l1 := by
  simp only [sig]
  ring

/-- The three possible separated cross-chord chambers.  `left` means the
chord is positive from the first base point, `right` means it is negative
from the second, and `middle` means the two base points see opposite signs. -/
inductive CrossChordChamber (m x y : ℝ) : Prop
  | left (hx : m <= x)
  | middle (hx : x <= -m) (hy : m <= y)
  | right (hy : y <= -m)

/-- Two absolute lower bounds put a cross chord in one of the three chambers.
This is an exhaustive trichotomy.  For an oriented upper-to-lower chord in
the line-through-the-two-interior-points normalization, base change by the
positive line-level sum makes the L/M/R alternatives exclusive as well. -/
lemma crossChordChamber_of_abs_bounds
    {m x y : ℝ} (hx : m <= |x|) (hy : m <= |y|) :
    CrossChordChamber m x y := by
  by_cases hx0 : 0 <= x
  · apply CrossChordChamber.left
    rwa [abs_of_nonneg hx0] at hx
  · have hxnonpos : x <= 0 := le_of_not_ge hx0
    have hxneg : x <= -m := by
      rw [abs_of_nonpos hxnonpos] at hx
      linarith
    by_cases hy0 : 0 <= y
    · apply CrossChordChamber.middle hxneg
      rwa [abs_of_nonneg hy0] at hy
    · apply CrossChordChamber.right
      have hynonpos : y <= 0 := le_of_not_ge hy0
      rw [abs_of_nonpos hynonpos] at hy
      linarith

/-- Configuration-label form of the chamber trichotomy. -/
lemma crossChordChamber_of_configuration
    (v : Configuration) {p q u l : Fin 8}
    (hpu : p ≠ u) (hpl : p ≠ l) (hul : u ≠ l)
    (hqu : q ≠ u) (hql : q ≠ l) :
    CrossChordChamber (minTri v)
      (sig (v p) (v u) (v l))
      (sig (v q) (v u) (v l)) := by
  exact crossChordChamber_of_abs_bounds
    (minTri_le_abs_sig_of_pairwise_ne v hpu hpl hul)
    (minTri_le_abs_sig_of_pairwise_ne v hqu hql hul)

/-!
The remaining normalization theorem must use convexity of the six-cycle to
show that the signs along the line `pq` form two nonempty contiguous cyclic
blocks.  After cyclic rotation and exchanging the sides, these blocks have
sizes `k` and `6-k`, with `k = 1, 2, 3`.  Write

* `u_i = sig p q U_i >= minTri`,
* `v_j = -sig p q L_j >= minTri`, and
* `X_ij = sig p U_i L_j`.

Then the exact unresolved compact problem is finite: every entry satisfies

`|X_ij| >= minTri`, `|X_ij + u_i + v_j| >= minTri`,

so it lies in one of the L/M/R chambers above, while every adjacent matrix
minor satisfies

`X_ij * X_(i+1,j+1) - X_(i,j+1) * X_(i+1,j)
  = sig p U_i U_(i+1) * sig p L_j L_(j+1)`.

The universal two-arc theorem now proves that the variation branch closes
whenever the line-level range is at least `13 * minTri / 2`.  Thus the exact
remaining work is the sign-block normalization followed by the `1 x 5`,
`2 x 4`, and `3 x 3` chamber theorems at smaller range.  Their same-side
chord factors are positive and at least `minTri`, so the displayed Plucker
minors are at least `minTri ^ 2`.
-/

end Heilbronn8
