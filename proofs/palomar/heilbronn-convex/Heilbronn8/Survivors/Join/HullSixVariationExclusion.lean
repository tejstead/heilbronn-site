import Heilbronn8.Survivors.Join.HullSixSemantic

/-!
# Sharp semantic use of the six fan variation estimate

`HullSixSemantic` exposes a convenient sufficient condition using one pair of
line levels.  The underlying estimate is slightly stronger: it closes a
six-vertex hull whenever the full cyclic variation of the six line levels is
at least `13 * minTri`.

This file records that sharp linear consequence and packages a lossless
geometric residual for the compact branch.  In addition to the derived
line-level and cross-chord facts, the residual retains the rational cut,
strict cyclic geometry, hull containment, and exact hull-area identity.  The
remaining work can therefore normalize the two line-level sign blocks without
having to reconstruct facts discarded by the variation argument.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The sharp target-shaped consequence of the six-fan estimate.  Unlike the
pair-spread wrapper, this consumes the full variation and loses no linear
information. -/
theorem twentyFive_minTri_le_twice_hullArea_of_hullCycleSixVariation
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
    (hvariation :
      13 * minTri v <= cyclicVariationFinSix
        (fun i => sig (v p) (v q) (v (d.castGet h6 i)))) :
    25 * minTri v <= 2 * doubledHullArea v := by
  let c : Fin 6 -> Fin 8 := d.castGet h6
  have hc : Function.Injective c :=
    HullCycleData.castGet_injective d h6 hcycle.nodup
  have hpFloor : ∀ i,
      minTri v <= sig (v p) (v (c i)) (v (c (i + 1))) := by
    intro i
    exact minTri_le_sixCycle_boundary_sig
      v c hc p hpOutside i (hpPos i)
  have hqFloor : ∀ i,
      minTri v <= sig (v q) (v (c i)) (v (c (i + 1))) := by
    intro i
    exact minTri_le_sixCycle_boundary_sig
      v c hc q hqOutside i (hqPos i)
  have hcertified : doubledHullArea v = d.fanExpr v :=
    doubledHullArea_eq_of_isHullArea hcycle.isHullArea
  have hcast : fanSum v c = d.fanExpr v :=
    HullCycleData.fanSum_castGet d h6
  have hHullArea : doubledHullArea v = fanSum v c :=
    hcertified.trans hcast.symm
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
  have hfan := geometricSixFanVariation_bound
    (p := v p) (q := v q) (v := fun i => v (c i))
    (m := minTri v) (H := doubledHullArea v)
    hpFloor hqFloor hpSum hqSum
  change 13 * minTri v <= cyclicVariationFinSix
    (fun i => sig (v p) (v q) (v (c i))) at hvariation
  linarith

/-- Sharp semantic exclusion in the sign-oracle interface used by emitted
strict hull branches. -/
theorem not_Beats_v8_of_hullCycleSixVariation_signs
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hpSigns : ∀ i,
      S.ccw p (d.castGet h6 i) (d.castGet h6 (i + 1)) = true)
    (hqSigns : ∀ i,
      S.ccw q (d.castGet h6 i) (d.castGet h6 (i + 1)) = true)
    (hvariation :
      13 * minTri v <= cyclicVariationFinSix
        (fun i => sig (v p) (v q) (v (d.castGet h6 i)))) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  have hbound :=
    twentyFive_minTri_le_twice_hullArea_of_hullCycleSixVariation
      hcycle h6 p q hpOutside hqOutside
      (fun i => S.pos_of_eq_true _ _ _ (hpSigns i))
      (fun i => S.pos_of_eq_true _ _ _ (hqSigns i))
      hvariation
  have hcut :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    lt_trans
      (mul_lt_mul_of_pos_right two_div_twentyFive_lt_v8 hbeat.1)
      hbeat.2
  nlinarith

/-- Strongest compact semantic interface: hull containment supplies boundary
positivity, so the full-variation exclusion needs no emitted boundary signs. -/
theorem not_Beats_v8_of_hullCycleSixVariation
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hvariation :
      13 * minTri v <= cyclicVariationFinSix
        (fun i => sig (v p) (v q) (v (d.castGet h6 i)))) :
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
  have hbound :=
    twentyFive_minTri_le_twice_hullArea_of_hullCycleSixVariation
      hcycle h6 p q hpOutside hqOutside hpPos hqPos hvariation
  have hcut :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    lt_trans
      (mul_lt_mul_of_pos_right two_div_twentyFive_lt_v8 hbeat.1)
      hbeat.2
  nlinarith

/-- If a point lies in a triangle, every line through that point has triangle
vertices on both closed sides.  This elementary convex-combination fact is
the only geometric input needed to show that the two interior labels see
both signs among the six hull vertices. -/
lemma lineLevels_straddle_of_inTri
    (p q a b c : Real × Real) (htri : InTri p a b c) :
    (sig p q a <= 0 ∨ sig p q b <= 0 ∨ sig p q c <= 0) ∧
    (0 <= sig p q a ∨ 0 <= sig p q b ∨ 0 <= sig p q c) := by
  rcases htri with ⟨x, y, z, hx, hy, hz, hsum, hp⟩
  have hrotate (r : Real × Real) : sig p q r = sig r p q := by
    calc
      sig p q r = sig q r p := sig_rotate p q r
      _ = sig r p q := sig_rotate q r p
  have haffine := sig_affine_fst a b c p q x y z hsum
  rw [← hp] at haffine
  have hlinear :
      x * sig p q a + y * sig p q b + z * sig p q c = 0 := by
    rw [hrotate a, hrotate b, hrotate c]
    simpa only [sig, sub_self, zero_mul, mul_zero, sub_zero] using
      haffine.symm
  have hcoeff : 0 < x ∨ 0 < y ∨ 0 < z := by
    by_contra h
    push_neg at h
    rcases h with ⟨hx', hy', hz'⟩
    linarith
  constructor
  · by_contra h
    push_neg at h
    rcases hcoeff with hxpos | hypos | hzpos
    · have hxa : 0 < x * sig p q a := mul_pos hxpos h.1
      have hyb : 0 <= y * sig p q b := mul_nonneg hy h.2.1.le
      have hzc : 0 <= z * sig p q c := mul_nonneg hz h.2.2.le
      linarith
    · have hxa : 0 <= x * sig p q a := mul_nonneg hx h.1.le
      have hyb : 0 < y * sig p q b := mul_pos hypos h.2.1
      have hzc : 0 <= z * sig p q c := mul_nonneg hz h.2.2.le
      linarith
    · have hxa : 0 <= x * sig p q a := mul_nonneg hx h.1.le
      have hyb : 0 <= y * sig p q b := mul_nonneg hy h.2.1.le
      have hzc : 0 < z * sig p q c := mul_pos hzpos h.2.2
      linarith
  · by_contra h
    push_neg at h
    rcases hcoeff with hxpos | hypos | hzpos
    · have hxa : x * sig p q a < 0 := mul_neg_of_pos_of_neg hxpos h.1
      have hyb : y * sig p q b <= 0 := mul_nonpos_of_nonneg_of_nonpos hy h.2.1.le
      have hzc : z * sig p q c <= 0 := mul_nonpos_of_nonneg_of_nonpos hz h.2.2.le
      linarith
    · have hxa : x * sig p q a <= 0 := mul_nonpos_of_nonneg_of_nonpos hx h.1.le
      have hyb : y * sig p q b < 0 := mul_neg_of_pos_of_neg hypos h.2.1
      have hzc : z * sig p q c <= 0 := mul_nonpos_of_nonneg_of_nonpos hz h.2.2.le
      linarith
    · have hxa : x * sig p q a <= 0 := mul_nonpos_of_nonneg_of_nonpos hx h.1.le
      have hyb : y * sig p q b <= 0 := mul_nonpos_of_nonneg_of_nonpos hy h.2.1.le
      have hzc : z * sig p q c < 0 := mul_neg_of_pos_of_neg hzpos h.2.2
      linarith

/-- The line through two distinct off-cycle labels has a hull vertex at
level at most `-minTri` and another at level at least `minTri`. -/
theorem sixCycle_lineLevels_straddle_minTri
    (v : Configuration) (c : Fin 6 -> Fin 8)
    (hcover : FanCovers v c)
    (p q : Fin 8) (hpq : p ≠ q)
    (hpOutside : p ∉ Set.range c) (hqOutside : q ∉ Set.range c) :
    ∃ iNeg iPos : Fin 6,
      sig (v p) (v q) (v (c iNeg)) <= -minTri v ∧
      minTri v <= sig (v p) (v q) (v (c iPos)) := by
  obtain ⟨i, j, _hi, _hij, htri⟩ := hcover p hpOutside
  have hstraddle := lineLevels_straddle_of_inTri
    (v p) (v q) (v (c 0)) (v (c i)) (v (c j)) htri
  have hlevel (k : Fin 6) :
      minTri v <= |sig (v p) (v q) (v (c k))| := by
    apply minTri_le_abs_sig_of_pairwise_ne v hpq
    · intro h
      exact hpOutside ⟨k, h.symm⟩
    · intro h
      exact hqOutside ⟨k, h.symm⟩
  obtain ⟨iNeg, hneg0⟩ :
      ∃ k : Fin 6, sig (v p) (v q) (v (c k)) <= 0 := by
    rcases hstraddle.1 with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨i, h⟩
    · exact ⟨j, h⟩
  obtain ⟨iPos, hpos0⟩ :
      ∃ k : Fin 6, 0 <= sig (v p) (v q) (v (c k)) := by
    rcases hstraddle.2 with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨i, h⟩
    · exact ⟨j, h⟩
  have hnegFloor := hlevel iNeg
  rw [abs_of_nonpos hneg0] at hnegFloor
  have hposFloor := hlevel iPos
  rw [abs_of_nonneg hpos0] at hposFloor
  exact ⟨iNeg, iPos, by linarith, hposFloor⟩

/-- Every chord between two distinct hull vertices lies in one of the three
cross-chord chambers, and changing the interior base point translates the
chord by the corresponding line-level difference. -/
theorem sixCycle_crossChord_constraint
    (v : Configuration) (c : Fin 6 -> Fin 8)
    (hc : Function.Injective c) (p q : Fin 8)
    (hpOutside : p ∉ Set.range c) (hqOutside : q ∉ Set.range c)
    (i j : Fin 6) (hij : i ≠ j) :
    CrossChordChamber (minTri v)
        (sig (v p) (v (c i)) (v (c j)))
        (sig (v q) (v (c i)) (v (c j))) ∧
      sig (v q) (v (c i)) (v (c j)) =
        sig (v p) (v (c i)) (v (c j)) +
          sig (v p) (v q) (v (c i)) -
          sig (v p) (v q) (v (c j)) := by
  have hpi : p ≠ c i := by
    intro h
    exact hpOutside ⟨i, h.symm⟩
  have hpj : p ≠ c j := by
    intro h
    exact hpOutside ⟨j, h.symm⟩
  have hqi : q ≠ c i := by
    intro h
    exact hqOutside ⟨i, h.symm⟩
  have hqj : q ≠ c j := by
    intro h
    exact hqOutside ⟨j, h.symm⟩
  have hcij : c i ≠ c j := hc.ne hij
  refine ⟨crossChordChamber_of_abs_bounds ?_ ?_, ?_⟩
  · exact minTri_le_abs_sig_of_pairwise_ne v hpi hpj hcij
  · exact minTri_le_abs_sig_of_pairwise_ne v hqi hqj hcij
  · exact sig_crossChord_base_change
      (v p) (v q) (v (c i)) (v (c j))

/-- Lossless geometric custody, plus a cache of the useful algebraic facts,
left by a beating h=6 configuration after the sharp linear variation
exclusion has been applied. -/
structure HullSixCompactCrossChordResidual
    (v : Configuration) (c : Fin 6 -> Fin 8) (p q : Fin 8) : Prop where
  cycle_injective : Function.Injective c
  cycle_strict : StrictCyclicPos c v
  cycle_covers : FanCovers v c
  hull_area_eq : doubledHullArea v = fanSum v c
  p_ne_q : p ≠ q
  p_outside : p ∉ Set.range c
  q_outside : q ∉ Set.range c
  hullArea_pos : 0 < doubledHullArea v
  cut_margin : (2 / 25 : ℝ) * doubledHullArea v < minTri v
  minTri_pos : 0 < minTri v
  p_boundary_pos : ∀ i,
    0 < sig (v p) (v (c i)) (v (c (i + 1)))
  q_boundary_pos : ∀ i,
    0 < sig (v q) (v (c i)) (v (c (i + 1)))
  p_fan_sum :
    sumFinSix (fun i => sig (v p) (v (c i)) (v (c (i + 1)))) =
      doubledHullArea v
  q_fan_sum :
    sumFinSix (fun i => sig (v q) (v (c i)) (v (c (i + 1)))) =
      doubledHullArea v
  lineLevel_floor : ∀ i,
    minTri v <= |sig (v p) (v q) (v (c i))|
  variation_lt :
    cyclicVariationFinSix (fun i => sig (v p) (v q) (v (c i))) <
      13 * minTri v
  lineLevel_spread_lt : ∀ iLo iHi,
    sig (v p) (v q) (v (c iHi)) - sig (v p) (v q) (v (c iLo)) <
      13 * minTri v / 2
  straddles : ∃ iNeg iPos,
    sig (v p) (v q) (v (c iNeg)) <= -minTri v ∧
    minTri v <= sig (v p) (v q) (v (c iPos))
  crossChord : ∀ i j, i ≠ j →
    minTri v <= |sig (v p) (v (c i)) (v (c j))| ∧
    minTri v <= |sig (v q) (v (c i)) (v (c j))| ∧
    CrossChordChamber (minTri v)
      (sig (v p) (v (c i)) (v (c j)))
      (sig (v q) (v (c i)) (v (c j))) ∧
    sig (v q) (v (c i)) (v (c j)) =
      sig (v p) (v (c i)) (v (c j)) +
        sig (v p) (v q) (v (c i)) -
        sig (v p) (v q) (v (c j))
  plucker : ∀ i0 i1 j0 j1,
    sig (v p) (v (c i0)) (v (c j0)) *
          sig (v p) (v (c i1)) (v (c j1)) -
        sig (v p) (v (c i0)) (v (c j1)) *
          sig (v p) (v (c i1)) (v (c j0)) =
      sig (v p) (v (c i0)) (v (c i1)) *
        sig (v p) (v (c j0)) (v (c j1))

/-- Any configuration beyond the closed rational hull bound in a certified
six-cycle branch must satisfy the compact nonlinear residual exactly. -/
theorem hullSixCompactCrossChordResidual_of_cutMargin
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8) (hpq : p ≠ q)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hcut : (2 / 25 : ℝ) * doubledHullArea v < minTri v) :
    HullSixCompactCrossChordResidual v (d.castGet h6) p q := by
  let c : Fin 6 -> Fin 8 := d.castGet h6
  have hc : Function.Injective c :=
    HullCycleData.castGet_injective d h6 hcycle.nodup
  have hstrict : StrictCyclicPos c v :=
    HullCycleData.strictCyclicPos_cast d h6 hcycle.strictCyclicPos
  have hcover : FanCovers v c :=
    HullCycleData.fanCovers_cast d h6 hcycle.fanCovers
  have hscaledNonneg :
      0 ≤ (2 / 25 : ℝ) * doubledHullArea v :=
    mul_nonneg (by norm_num) (doubledHullArea_nonneg v)
  have hminPos : 0 < minTri v :=
    lt_of_le_of_lt hscaledNonneg hcut
  have hpPos : ∀ i,
      0 < sig (v p) (v (c i)) (v (c (i + 1))) := by
    intro i
    exact hullCycleSix_boundary_pos_of_minTri_pos
      hcycle h6 p hpOutside hminPos i
  have hqPos : ∀ i,
      0 < sig (v q) (v (c i)) (v (c (i + 1))) := by
    intro i
    exact hullCycleSix_boundary_pos_of_minTri_pos
      hcycle h6 q hqOutside hminPos i
  have hcertified : doubledHullArea v = d.fanExpr v :=
    doubledHullArea_eq_of_isHullArea hcycle.isHullArea
  have hcast : fanSum v c = d.fanExpr v :=
    HullCycleData.fanSum_castGet d h6
  have hHullArea : doubledHullArea v = fanSum v c :=
    hcertified.trans hcast.symm
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
  have hareaPos : 0 < doubledHullArea v := by
    have hp0 : 0 < sig (v p) (v (c 0)) (v (c 1)) := by
      simpa using hpPos 0
    have hp1 : 0 < sig (v p) (v (c 1)) (v (c 2)) := by
      simpa using hpPos 1
    have hp2 : 0 < sig (v p) (v (c 2)) (v (c 3)) := by
      simpa using hpPos 2
    have hp3 : 0 < sig (v p) (v (c 3)) (v (c 4)) := by
      simpa using hpPos 3
    have hp4 : 0 < sig (v p) (v (c 4)) (v (c 5)) := by
      simpa using hpPos 4
    have hp5 : 0 < sig (v p) (v (c 5)) (v (c 0)) := by
      simpa using hpPos 5
    rw [← hpSum]
    dsimp [sumFinSix]
    linarith
  have hlevel (i : Fin 6) :
      minTri v <= |sig (v p) (v q) (v (c i))| := by
    apply minTri_le_abs_sig_of_pairwise_ne v hpq
    · intro h
      exact hpOutside ⟨i, h.symm⟩
    · intro h
      exact hqOutside ⟨i, h.symm⟩
  have hvariation :
      cyclicVariationFinSix (fun i => sig (v p) (v q) (v (c i))) <
        13 * minTri v := by
    by_contra h
    have hge :
        13 * minTri v <=
          cyclicVariationFinSix
            (fun i => sig (v p) (v q) (v (d.castGet h6 i))) := by
      dsimp [c] at h
      exact le_of_not_gt h
    have hbound :=
      twentyFive_minTri_le_twice_hullArea_of_hullCycleSixVariation
        hcycle h6 p q hpOutside hqOutside
        (by simpa only [c] using hpPos)
        (by simpa only [c] using hqPos)
        hge
    nlinarith only [hbound, hcut]
  have hspread (iLo iHi : Fin 6) :
      sig (v p) (v q) (v (c iHi)) - sig (v p) (v q) (v (c iLo)) <
        13 * minTri v / 2 := by
    have harcs := two_mul_sub_le_cyclicVariationFinSix
      (fun i => sig (v p) (v q) (v (c i))) iLo iHi
    linarith
  have hstraddle := sixCycle_lineLevels_straddle_minTri
    v c hcover p q hpq hpOutside hqOutside
  refine
    { cycle_injective := hc
      cycle_strict := hstrict
      cycle_covers := hcover
      hull_area_eq := hHullArea
      p_ne_q := hpq
      p_outside := hpOutside
      q_outside := hqOutside
      hullArea_pos := hareaPos
      cut_margin := hcut
      minTri_pos := hminPos
      p_boundary_pos := hpPos
      q_boundary_pos := hqPos
      p_fan_sum := hpSum
      q_fan_sum := hqSum
      lineLevel_floor := hlevel
      variation_lt := hvariation
      lineLevel_spread_lt := hspread
      straddles := hstraddle
      crossChord := ?_
      plucker := ?_ }
  · intro i j hij
    have hpi : p ≠ c i := by
      intro h
      exact hpOutside ⟨i, h.symm⟩
    have hpj : p ≠ c j := by
      intro h
      exact hpOutside ⟨j, h.symm⟩
    have hqi : q ≠ c i := by
      intro h
      exact hqOutside ⟨i, h.symm⟩
    have hqj : q ≠ c j := by
      intro h
      exact hqOutside ⟨j, h.symm⟩
    have hcij : c i ≠ c j := hc.ne hij
    have hpFloor := minTri_le_abs_sig_of_pairwise_ne v hpi hpj hcij
    have hqFloor := minTri_le_abs_sig_of_pairwise_ne v hqi hqj hcij
    obtain ⟨hchamber, hbase⟩ := sixCycle_crossChord_constraint
      v c hc p q hpOutside hqOutside i j hij
    exact ⟨hpFloor, hqFloor, hchamber, hbase⟩
  · intro i0 i1 j0 j1
    exact sig_crossChord_plucker
      (v p) (v (c i0)) (v (c i1)) (v (c j0)) (v (c j1))

/-- Compatibility constructor for optimizer-facing callers. -/
theorem hullSixCompactCrossChordResidual_of_Beats
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8) (hpq : p ≠ q)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6))
    (hbeat : Beats doubledHullArea v8 v) :
    HullSixCompactCrossChordResidual v (d.castGet h6) p q := by
  apply hullSixCompactCrossChordResidual_of_cutMargin
    hcycle h6 p q hpq hpOutside hqOutside
  exact lt_trans
    (mul_lt_mul_of_pos_right two_div_twentyFive_lt_v8 hbeat.1)
    hbeat.2

/-- The exact remaining h=6 obligation after the sharp variation branch.
Its proof may normalize the cyclic sign blocks into the `1 x 5`, `2 x 4`,
and `3 x 3` cross-chord systems, but no geometric or numerical custody is
hidden outside this proposition. -/
def HullSixCompactCrossChordClosed : Prop :=
  ∀ (v : Configuration) (c : Fin 6 -> Fin 8) (p q : Fin 8),
    HullSixCompactCrossChordResidual v c p q → False

/-- The completed compact closure yields the optimizer-independent rational
hull-six estimate. -/
theorem twentyFive_minTri_le_twice_hullArea_of_hullCycleSix_of_compactClosed
    (hclose : HullSixCompactCrossChordClosed)
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8) (hpq : p ≠ q)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6)) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  by_contra hnot
  have hstrict :
      2 * doubledHullArea v < 25 * minTri v :=
    lt_of_not_ge hnot
  have hcut :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v := by
    nlinarith only [hstrict]
  exact hclose v (d.castGet h6) p q
    (hullSixCompactCrossChordResidual_of_cutMargin
      hcycle h6 p q hpq hpOutside hqOutside hcut)

/-- Closing the compact residual excludes every beat in a certified h=6
branch. -/
theorem not_Beats_v8_of_hullCycleSix_of_compactClosed
    (hclose : HullSixCompactCrossChordClosed)
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h6 : d.cycle.length = 6)
    (p q : Fin 8) (hpq : p ≠ q)
    (hpOutside : p ∉ Set.range (d.castGet h6))
    (hqOutside : q ∉ Set.range (d.castGet h6)) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  exact hclose v (d.castGet h6) p q
    (hullSixCompactCrossChordResidual_of_Beats
      hcycle h6 p q hpq hpOutside hqOutside hbeat)

end Heilbronn8
