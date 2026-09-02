import Heilbronn8.HullSixOneFiveResidualAdapter
import Heilbronn8.Survivors.Join.HullSixSignBlocks

/-!
# Rotation and line-orientation transport for the hull-six `1 + 5` chamber

`HullSixOneFiveResidualAdapter` closes a frame in which the isolated positive
line level is stored at cycle position zero.  A compact residual supplies that
frame only up to cyclic rotation and reversal of the oriented line `PQ`.

This file performs exactly that transport.  It deliberately avoids building a
new `HullSixCompactCrossChordResidual` after rotation: doing so would require
reproving global fields such as `FanCovers` which the `1 + 5` argument never
uses.  Instead, `HullSixOrientedView` retains just the six symmetric facts used
by the adapter.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Heilbronn8

/-- Swapping the first two arguments reverses signed area. -/
lemma sig_swap_first (a b c : Real × Real) :
    sig b a c = -sig a b c := by
  simp only [sig]
  ring

/-- The small part of a compact residual which changes when the two interior
points are exchanged. -/
structure HullSixOrientedView
    (v : Configuration) (cycle : Fin 6 → Fin 8) (P Q : Fin 8) : Prop where
  P_outside : P ∉ Set.range cycle
  Q_outside : Q ∉ Set.range cycle
  P_boundary_pos : ∀ i,
    0 < sig (v P) (v (cycle i)) (v (cycle (i + 1)))
  Q_boundary_pos : ∀ i,
    0 < sig (v Q) (v (cycle i)) (v (cycle (i + 1)))
  P_fan_sum :
    sumFinSix (fun i => sig (v P) (v (cycle i)) (v (cycle (i + 1)))) =
      doubledHullArea v
  lineLevel_floor : ∀ i,
    minTri v ≤ |sig (v P) (v Q) (v (cycle i))|

namespace HullSixCompactCrossChordResidual

/-- Keep the stored orientation of the two interior points. -/
def forwardOrientedView
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    HullSixOrientedView v cycle p q where
  P_outside := R.p_outside
  Q_outside := R.q_outside
  P_boundary_pos := R.p_boundary_pos
  Q_boundary_pos := R.q_boundary_pos
  P_fan_sum := R.p_fan_sum
  lineLevel_floor := R.lineLevel_floor

/-- Reverse the oriented line by exchanging its two defining points. -/
def swappedOrientedView
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    HullSixOrientedView v cycle q p where
  P_outside := R.q_outside
  Q_outside := R.p_outside
  P_boundary_pos := R.q_boundary_pos
  Q_boundary_pos := R.p_boundary_pos
  P_fan_sum := R.q_fan_sum
  lineLevel_floor := by
    intro i
    have h := R.lineLevel_floor i
    rw [sig_swap_first, abs_neg]
    exact h

end HullSixCompactCrossChordResidual

/-- An unrolled six-term sum is invariant under cyclic translation. -/
lemma sumFinSix_add_left (f : Fin 6 → ℝ) (rotation : Fin 6) :
    sumFinSix (fun i => f (rotation + i)) = sumFinSix f := by
  fin_cases rotation <;> simp [sumFinSix] <;> ring

namespace HullSixOneFiveRawData

/-- Pure raw-data closure.  Geometry only has to provide the two crossed
edges, the three omitted positive quantities, and the exact hull identity. -/
theorem twentyFive_mul_m_le_two_mul_hull
    (R : HullSixOneFiveRawData)
    (H U leftCap rightCap : ℝ)
    (hU : R.m ≤ U) (hleftCap : R.m ≤ leftCap)
    (hrightCap : R.m ≤ rightCap)
    (k l : Fin 4) (hkl : k ≤ l)
    (SPleft SPright TQleft TQright : ℝ)
    (hSPleft : R.m ≤ SPleft) (hSPright : SPright ≤ -R.m)
    (hTQleft : R.m ≤ TQleft) (hTQright : TQright ≤ -R.m)
    (hpluckerP : U * R.aRawAt k =
      R.bRawAt k.succ * SPleft - R.bRawAt k.castSucc * SPright)
    (hpluckerQ : U * R.cRawAt l =
      R.bRawAt l.succ * TQleft - R.bRawAt l.castSucc * TQright)
    (hHull : H / R.m =
      R.normalize.area + R.normalize.b₅ +
        leftCap / R.m + rightCap / R.m + U / R.m) :
    25 * R.m ≤ 2 * H := by
  let D := R.normalize
  let u := U / R.m
  let left := leftCap / R.m
  let right := rightCap / R.m
  have hcrossA : D.adjacentSum k ≤ u * D.aAt k := by
    have h := raw_crossing_le R.hm
      (R.hBRawAt k.castSucc) (R.hBRawAt k.succ)
      hSPleft hSPright hpluckerP
    fin_cases k <;>
      simpa [D, u, normalize, HullSixOneFiveData.adjacentSum,
        HullSixOneFiveData.aAt, aRawAt, bRawAt] using h
  have hcrossC : D.adjacentSum l ≤ u * D.cAt l := by
    have h := raw_crossing_le R.hm
      (R.hBRawAt l.castSucc) (R.hBRawAt l.succ)
      hTQleft hTQright hpluckerQ
    rw [show D.cAt l = R.cRawAt l / R.m by
      simpa [D] using R.normalize_cAt l]
    fin_cases l <;>
      simpa [D, u, normalize, HullSixOneFiveData.adjacentSum,
        bRawAt] using h
  have hu : 1 ≤ u := (le_div_iff₀ R.hm).2 (by simpa using hU)
  have hleft : 1 ≤ left :=
    (le_div_iff₀ R.hm).2 (by simpa using hleftCap)
  have hright : 1 ≤ right :=
    (le_div_iff₀ R.hm).2 (by simpa using hrightCap)
  have hExpr := D.hullExpression_ge_twenty_five_halves_orderFree
    k l hkl u left right hu hleft hright hcrossA hcrossC
  have hratio : 25 / 2 ≤ H / R.m := by
    calc
      25 / 2 ≤ D.area + D.b₅ + left + right + u := hExpr
      _ = H / R.m := by simpa [D, u, left, right] using hHull.symm
  have hmul : (25 / 2) * R.m ≤ H := (le_div_iff₀ R.hm).1 hratio
  nlinarith only [hmul]

end HullSixOneFiveRawData

/-! ## Shifted geometric floors -/

private lemma shiftedBoundary_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : ∀ i, 0 < sig (v base) (v (cycle i)) (v (cycle (i + 1))))
    (rotation i : Fin 6) :
    minTri v ≤
      sig (v base) (v (cycle (rotation + i)))
        (v (cycle (rotation + (i + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective
    base hOutside (rotation + i) (hpos (rotation + i))
  have hnext : (rotation + i) + 1 = rotation + (i + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

private def oneFiveEarFirst (i : Fin 3) : Fin 6 :=
  ⟨i.val + 1, by omega⟩

private def oneFiveEarSecond (i : Fin 3) : Fin 6 :=
  ⟨i.val + 2, by omega⟩

private def oneFiveEarThird (i : Fin 3) : Fin 6 :=
  ⟨i.val + 3, by omega⟩

private lemma shiftedEar_pos
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (rotation : Fin 6) (i : Fin 3) :
    0 < sig
      (v (cycle (rotation + oneFiveEarFirst i)))
      (v (cycle (rotation + oneFiveEarSecond i)))
      (v (cycle (rotation + oneFiveEarThird i))) := by
  have h012 := R.cycle_strict.pos 0 1 2 (by decide) (by decide)
  have h123 := R.cycle_strict.pos 1 2 3 (by decide) (by decide)
  have h234 := R.cycle_strict.pos 2 3 4 (by decide) (by decide)
  have h345 := R.cycle_strict.pos 3 4 5 (by decide) (by decide)
  have h045 := R.cycle_strict.pos 0 4 5 (by decide) (by decide)
  have h015 := R.cycle_strict.pos 0 1 5 (by decide) (by decide)
  have h450 : 0 <
      sig (v (cycle 4)) (v (cycle 5)) (v (cycle 0)) := by
    rw [← sig_rotate]
    exact h045
  have h501 : 0 <
      sig (v (cycle 5)) (v (cycle 0)) (v (cycle 1)) := by
    rw [← sig_rotate, ← sig_rotate]
    exact h015
  fin_cases rotation <;> fin_cases i <;>
    first
    | simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using h012
    | simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using h123
    | simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using h234
    | simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using h345
    | simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using h450
    | simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using h501

private lemma shiftedEar_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (rotation : Fin 6) (i : Fin 3) :
    minTri v ≤ sig
      (v (cycle (rotation + oneFiveEarFirst i)))
      (v (cycle (rotation + oneFiveEarSecond i)))
      (v (cycle (rotation + oneFiveEarThird i))) := by
  have h01 : rotation + oneFiveEarFirst i ≠
      rotation + oneFiveEarSecond i := by
    intro h
    have h' := add_left_cancel h
    fin_cases i <;> norm_num [oneFiveEarFirst, oneFiveEarSecond] at h'
  have h02 : rotation + oneFiveEarFirst i ≠
      rotation + oneFiveEarThird i := by
    intro h
    have h' := add_left_cancel h
    fin_cases i <;> norm_num [oneFiveEarFirst, oneFiveEarThird] at h'
  have h12 : rotation + oneFiveEarSecond i ≠
      rotation + oneFiveEarThird i := by
    intro h
    have h' := add_left_cancel h
    fin_cases i <;> norm_num [oneFiveEarSecond, oneFiveEarThird] at h'
  exact minTri_le_pos_sig_of_pairwise_ne v
    (R.cycle_injective.ne h01) (R.cycle_injective.ne h02)
    (R.cycle_injective.ne h12) (shiftedEar_pos R rotation i)

namespace HullSixCompactCrossChordResidual

private lemma shiftedLowerLevel_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (rotation : Fin 6)
    (hlower : ∀ i : Fin 5,
      sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0)
    (i : Fin 5) :
    minTri v ≤
      -sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) := by
  have h := V.lineLevel_floor
    (rotation + hullSixOneFiveLowerIndex i)
  rw [abs_of_neg (hlower i)] at h
  exact h

/-- Raw scalar data at an arbitrary cyclic origin and with an arbitrary
orientation of the two interior points. -/
noncomputable def oneFiveRawDataAt
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (rotation : Fin 6)
    (hlower : ∀ i : Fin 5,
      sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0) :
    HullSixOneFiveRawData where
  m := minTri v
  A₁ := sig (v P) (v (cycle (rotation + 1)))
    (v (cycle (rotation + 2)))
  A₂ := sig (v P) (v (cycle (rotation + 2)))
    (v (cycle (rotation + 3)))
  A₃ := sig (v P) (v (cycle (rotation + 3)))
    (v (cycle (rotation + 4)))
  A₄ := sig (v P) (v (cycle (rotation + 4)))
    (v (cycle (rotation + 5)))
  B₁ := -sig (v P) (v Q) (v (cycle (rotation + 1)))
  B₂ := -sig (v P) (v Q) (v (cycle (rotation + 2)))
  B₃ := -sig (v P) (v Q) (v (cycle (rotation + 3)))
  B₄ := -sig (v P) (v Q) (v (cycle (rotation + 4)))
  B₅ := -sig (v P) (v Q) (v (cycle (rotation + 5)))
  E₂ := sig (v (cycle (rotation + 1)))
    (v (cycle (rotation + 2))) (v (cycle (rotation + 3)))
  E₃ := sig (v (cycle (rotation + 2)))
    (v (cycle (rotation + 3))) (v (cycle (rotation + 4)))
  E₄ := sig (v (cycle (rotation + 3)))
    (v (cycle (rotation + 4))) (v (cycle (rotation + 5)))
  hm := R.minTri_pos
  hA₁ := by
    simpa using shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
      rotation 1
  hA₂ := by
    simpa using shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
      rotation 2
  hA₃ := by
    simpa using shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
      rotation 3
  hA₄ := by
    simpa using shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos
      rotation 4
  hB₁ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.shiftedLowerLevel_floor V rotation hlower 0
  hB₂ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.shiftedLowerLevel_floor V rotation hlower 1
  hB₃ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.shiftedLowerLevel_floor V rotation hlower 2
  hB₄ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.shiftedLowerLevel_floor V rotation hlower 3
  hB₅ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.shiftedLowerLevel_floor V rotation hlower 4
  hC₁ := by
    have h : minTri v ≤
        sig (v Q) (v (cycle (rotation + 1)))
          (v (cycle (rotation + 2))) := by
      simpa using shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 1
    have hbase := sig_crossChord_base_change
      (v P) (v Q) (v (cycle (rotation + 1)))
        (v (cycle (rotation + 2)))
    nlinarith only [h, hbase]
  hC₂ := by
    have h : minTri v ≤
        sig (v Q) (v (cycle (rotation + 2)))
          (v (cycle (rotation + 3))) := by
      simpa using shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 2
    have hbase := sig_crossChord_base_change
      (v P) (v Q) (v (cycle (rotation + 2)))
        (v (cycle (rotation + 3)))
    nlinarith only [h, hbase]
  hC₃ := by
    have h : minTri v ≤
        sig (v Q) (v (cycle (rotation + 3)))
          (v (cycle (rotation + 4))) := by
      simpa using shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 3
    have hbase := sig_crossChord_base_change
      (v P) (v Q) (v (cycle (rotation + 3)))
        (v (cycle (rotation + 4)))
    nlinarith only [h, hbase]
  hC₄ := by
    have h : minTri v ≤
        sig (v Q) (v (cycle (rotation + 4)))
          (v (cycle (rotation + 5))) := by
      simpa using shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 4
    have hbase := sig_crossChord_base_change
      (v P) (v Q) (v (cycle (rotation + 4)))
        (v (cycle (rotation + 5)))
    nlinarith only [h, hbase]
  hE₂ := by
    simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using
      shiftedEar_floor R rotation 0
  hE₃ := by
    simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using
      shiftedEar_floor R rotation 1
  hE₄ := by
    simpa [oneFiveEarFirst, oneFiveEarSecond, oneFiveEarThird] using
      shiftedEar_floor R rotation 2
  ear₂_identity := sig_oneFive_ear_identity
    (v P) (v Q) (v (cycle (rotation + 1)))
      (v (cycle (rotation + 2))) (v (cycle (rotation + 3)))
  ear₃_identity := sig_oneFive_ear_identity
    (v P) (v Q) (v (cycle (rotation + 2)))
      (v (cycle (rotation + 3))) (v (cycle (rotation + 4)))
  ear₄_identity := sig_oneFive_ear_identity
    (v P) (v Q) (v (cycle (rotation + 3)))
      (v (cycle (rotation + 4))) (v (cycle (rotation + 5)))

private lemma shiftedSpoke_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (rotation : Fin 6) (i : Fin 5) :
    minTri v ≤
      |sig (v base) (v (cycle rotation))
        (v (cycle (rotation + hullSixOneFiveLowerIndex i)))| := by
  apply minTri_le_abs_sig_of_pairwise_ne v
  · intro h
    exact hOutside ⟨rotation, h.symm⟩
  · intro h
    exact hOutside
      ⟨rotation + hullSixOneFiveLowerIndex i, h.symm⟩
  · apply R.cycle_injective.ne
    intro h
    have h' : rotation + 0 =
        rotation + hullSixOneFiveLowerIndex i := by simpa using h
    have hoff := add_left_cancel h'
    have hval := congrArg Fin.val hoff
    simp [hullSixOneFiveLowerIndex] at hval

/-- At a shifted `1 + 5` frame, the first `P` and `Q` spoke sign changes
produce ordered crossed edges exactly as in the position-zero adapter. -/
theorem oneFive_orderedSpokeCrossingsAt
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (rotation : Fin 6)
    (hisolated :
      0 < sig (v P) (v Q) (v (cycle rotation)))
    (hlower : ∀ i : Fin 5,
      sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0) :
    ∃ k l : Fin 4, k ≤ l ∧
      minTri v ≤ sig (v P) (v (cycle rotation))
        (v (cycle (rotation +
          hullSixOneFiveLowerIndex k.castSucc))) ∧
      sig (v P) (v (cycle rotation))
        (v (cycle (rotation + hullSixOneFiveLowerIndex k.succ))) ≤
          -minTri v ∧
      minTri v ≤ sig (v Q) (v (cycle rotation))
        (v (cycle (rotation +
          hullSixOneFiveLowerIndex l.castSucc))) ∧
      sig (v Q) (v (cycle rotation))
        (v (cycle (rotation + hullSixOneFiveLowerIndex l.succ))) ≤
          -minTri v := by
  let raw := R.oneFiveRawDataAt V rotation hlower
  let U := sig (v P) (v Q) (v (cycle rotation))
  let S : Fin 5 → ℝ := fun i =>
    sig (v P) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex i)))
  let T : Fin 5 → ℝ := fun i =>
    sig (v Q) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex i)))
  have hU : minTri v ≤ U := by
    have hfloor := V.lineLevel_floor rotation
    rw [abs_of_pos hisolated] at hfloor
    simpa [U] using hfloor
  have hSfirst : minTri v ≤ S 0 := by
    simpa [S, hullSixOneFiveLowerIndex] using
      shiftedBoundary_floor R V P V.P_outside V.P_boundary_pos rotation 0
  have hwrap : rotation + ((5 : Fin 6) + 1) = rotation := by simp
  have hSlast : S 4 ≤ -minTri v := by
    have hfloor := shiftedBoundary_floor R V P V.P_outside
      V.P_boundary_pos rotation 5
    have hfloor₀ : minTri v ≤
        sig (v P) (v (cycle (rotation + 5)))
          (v (cycle rotation)) := by
      simpa only [hwrap] using hfloor
    have hid : S 4 =
        -sig (v P) (v (cycle (rotation + 5)))
          (v (cycle rotation)) := by
      dsimp [S, hullSixOneFiveLowerIndex]
      simp only [sig]
      ring
    rw [hid]
    linarith only [hfloor₀]
  have hTfirst : minTri v ≤ T 0 := by
    simpa [T, hullSixOneFiveLowerIndex] using
      shiftedBoundary_floor R V Q V.Q_outside V.Q_boundary_pos rotation 0
  have hTlast : T 4 ≤ -minTri v := by
    have hfloor := shiftedBoundary_floor R V Q V.Q_outside
      V.Q_boundary_pos rotation 5
    have hfloor₀ : minTri v ≤
        sig (v Q) (v (cycle (rotation + 5)))
          (v (cycle rotation)) := by
      simpa only [hwrap] using hfloor
    have hid : T 4 =
        -sig (v Q) (v (cycle (rotation + 5)))
          (v (cycle rotation)) := by
      dsimp [T, hullSixOneFiveLowerIndex]
      simp only [sig]
      ring
    rw [hid]
    linarith only [hfloor₀]
  obtain ⟨k, hSprefix, hSk, hSnext⟩ :=
    finFive_firstTransition R.minTri_pos S
      (shiftedSpoke_floor R V P V.P_outside rotation) hSfirst hSlast
  obtain ⟨l, _hTprefix, hTl, hTnext⟩ :=
    finFive_firstTransition R.minTri_pos T
      (shiftedSpoke_floor R V Q V.Q_outside rotation) hTfirst hTlast
  have hbRaw (i : Fin 5) : raw.bRawAt i =
      -sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) := by
    fin_cases i <;>
      simp [raw, oneFiveRawDataAt, HullSixOneFiveRawData.bRawAt,
        hullSixOneFiveLowerIndex]
  have hshift : ∀ i, T i = S i + U + raw.bRawAt i := by
    intro i
    have hbase := sig_crossChord_base_change
      (v P) (v Q) (v (cycle rotation))
        (v (cycle (rotation + hullSixOneFiveLowerIndex i)))
    calc
      T i = S i + U -
          sig (v P) (v Q)
            (v (cycle (rotation + hullSixOneFiveLowerIndex i))) := by
        simpa [T, S, U] using hbase
      _ = S i + U + raw.bRawAt i := by rw [hbRaw i] <;> ring
  have hUraw : raw.m ≤ U := by
    change minTri v ≤ U
    exact hU
  have hkl : k ≤ l := raw.ordered_crossings_of_shift U hUraw
    S T hshift k l hSprefix hTnext
  exact ⟨k, l, hkl, hSk, hSnext, hTl, hTnext⟩

/-- Exact normalized hull identity at an arbitrary cyclic origin. -/
theorem oneFive_hullArea_div_eqAt
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (rotation : Fin 6)
    (hlower : ∀ i : Fin 5,
      sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0) :
    let raw := R.oneFiveRawDataAt V rotation hlower
    doubledHullArea v / minTri v =
      raw.normalize.area + raw.normalize.b₅ +
        sig (v P) (v (cycle rotation))
            (v (cycle (rotation + 1))) / minTri v +
        sig (v Q) (v (cycle (rotation + 5)))
            (v (cycle rotation)) / minTri v +
        sig (v P) (v Q) (v (cycle rotation)) / minTri v := by
  dsimp
  let f : Fin 6 → ℝ := fun i =>
    sig (v P) (v (cycle i)) (v (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i =>
        sig (v P) (v (cycle (rotation + i)))
          (v (cycle (rotation + (i + 1))))) = doubledHullArea v := by
    have hfun : (fun i =>
          sig (v P) (v (cycle (rotation + i)))
            (v (cycle (rotation + (i + 1))))) =
        (fun i => f (rotation + i)) := by
      funext i
      simp [f, add_assoc]
    rw [hfun, sumFinSix_add_left]
    exact V.P_fan_sum
  have hSum : doubledHullArea v =
      sig (v P) (v (cycle rotation)) (v (cycle (rotation + 1))) +
      sig (v P) (v (cycle (rotation + 1))) (v (cycle (rotation + 2))) +
      sig (v P) (v (cycle (rotation + 2))) (v (cycle (rotation + 3))) +
      sig (v P) (v (cycle (rotation + 3))) (v (cycle (rotation + 4))) +
      sig (v P) (v (cycle (rotation + 4))) (v (cycle (rotation + 5))) +
      sig (v P) (v (cycle (rotation + 5))) (v (cycle rotation)) := by
    rw [← hshifted]
    simp [sumFinSix] <;> ring
  have hbase := sig_crossChord_base_change
    (v P) (v Q) (v (cycle (rotation + 5))) (v (cycle rotation))
  dsimp [oneFiveRawDataAt, HullSixOneFiveRawData.normalize,
    HullSixOneFiveData.area]
  field_simp [ne_of_gt R.minTri_pos]
  nlinarith only [hbase, hSum]

/-- The `1 + 5` hull bound at an arbitrary cyclic origin and oriented view. -/
theorem oneFiveAt_twentyFive_minTri_le_twice_hullArea
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (rotation : Fin 6)
    (hisolated :
      0 < sig (v P) (v Q) (v (cycle rotation)))
    (hlower : ∀ i : Fin 5,
      sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  let raw := R.oneFiveRawDataAt V rotation hlower
  let U := sig (v P) (v Q) (v (cycle rotation))
  let leftCap := sig (v P) (v (cycle rotation))
    (v (cycle (rotation + 1)))
  let rightCap := sig (v Q) (v (cycle (rotation + 5)))
    (v (cycle rotation))
  obtain ⟨k, l, hkl, hPk, hPkNext, hQl, hQlNext⟩ :=
    R.oneFive_orderedSpokeCrossingsAt V rotation hisolated hlower
  have hpluckerP : U * raw.aRawAt k =
      raw.bRawAt k.succ *
          sig (v P) (v (cycle rotation))
            (v (cycle (rotation +
              hullSixOneFiveLowerIndex k.castSucc))) -
        raw.bRawAt k.castSucc *
          sig (v P) (v (cycle rotation))
            (v (cycle (rotation +
              hullSixOneFiveLowerIndex k.succ))) := by
    have hid := sig_oneFive_crossing_identity
      (v P) (v Q) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex k.castSucc)))
      (v (cycle (rotation + hullSixOneFiveLowerIndex k.succ)))
    fin_cases k <;>
      simpa [raw, U, oneFiveRawDataAt, HullSixOneFiveRawData.aRawAt,
        HullSixOneFiveRawData.bRawAt, hullSixOneFiveLowerIndex] using hid
  have hpluckerQ : U * raw.cRawAt l =
      raw.bRawAt l.succ *
          sig (v Q) (v (cycle rotation))
            (v (cycle (rotation +
              hullSixOneFiveLowerIndex l.castSucc))) -
        raw.bRawAt l.castSucc *
          sig (v Q) (v (cycle rotation))
            (v (cycle (rotation +
              hullSixOneFiveLowerIndex l.succ))) := by
    have hid := sig_oneFive_crossing_identity_q
      (v P) (v Q) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex l.castSucc)))
      (v (cycle (rotation + hullSixOneFiveLowerIndex l.succ)))
    fin_cases l <;>
      simpa [raw, U, oneFiveRawDataAt, HullSixOneFiveRawData.cRawAt,
        HullSixOneFiveRawData.bRawAt, hullSixOneFiveLowerIndex] using hid
  have hU : raw.m ≤ U := by
    have hfloor := V.lineLevel_floor rotation
    rw [abs_of_pos hisolated] at hfloor
    change minTri v ≤ U
    exact hfloor
  have hleftCap : raw.m ≤ leftCap := by
    change minTri v ≤ leftCap
    simpa [leftCap] using shiftedBoundary_floor R V P V.P_outside
      V.P_boundary_pos rotation 0
  have hrightCap : raw.m ≤ rightCap := by
    change minTri v ≤ rightCap
    have hfloor := shiftedBoundary_floor R V Q V.Q_outside
      V.Q_boundary_pos rotation 5
    have hwrap : rotation + ((5 : Fin 6) + 1) = rotation := by simp
    dsimp only [rightCap]
    simpa only [hwrap] using hfloor
  have hHull : doubledHullArea v / raw.m =
      raw.normalize.area + raw.normalize.b₅ +
        leftCap / raw.m + rightCap / raw.m + U / raw.m := by
    change doubledHullArea v / minTri v =
      raw.normalize.area + raw.normalize.b₅ +
        leftCap / minTri v + rightCap / minTri v + U / minTri v
    simpa [raw, U, leftCap, rightCap] using
      R.oneFive_hullArea_div_eqAt V rotation hlower
  exact raw.twentyFive_mul_m_le_two_mul_hull
    (doubledHullArea v) U leftCap rightCap hU hleftCap hrightCap
    k l hkl
    (sig (v P) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex k.castSucc))))
    (sig (v P) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex k.succ))))
    (sig (v Q) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex l.castSucc))))
    (sig (v Q) (v (cycle rotation))
      (v (cycle (rotation + hullSixOneFiveLowerIndex l.succ))))
    hPk hPkNext hQl hQlNext hpluckerP hpluckerQ hHull

/-- No beating compact residual has an oriented `1 + 5` block at any cyclic
origin. -/
theorem oneFiveAt_false
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (V : HullSixOrientedView v cycle P Q)
    (rotation : Fin 6)
    (hisolated :
      0 < sig (v P) (v Q) (v (cycle rotation)))
    (hlower : ∀ i : Fin 5,
      sig (v P) (v Q)
        (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0) :
    False := by
  have hbound := R.oneFiveAt_twentyFive_minTri_le_twice_hullArea
    V rotation hisolated hlower
  have hcut : (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    R.cut_margin
  nlinarith only [hbound, hcut]

/-- The `last = 0` branch of `FinSixLineSignBlock` is exactly the `1 + 5`
case, independently of the Boolean orientation witness. -/
theorem oneFive_false_of_lineSignBlock_last_zero
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (rotation : Fin 6) (flip : Bool)
    (hpositive : ∀ i : Fin 6, i.val ≤ 0 →
      0 < orientedFinSixLevel
        (fun j => sig (v p) (v q) (v (cycle j)))
        flip (rotation + i))
    (hnegative : ∀ i : Fin 6, 0 < i.val →
      orientedFinSixLevel
        (fun j => sig (v p) (v q) (v (cycle j)))
        flip (rotation + i) < 0) :
    False := by
  cases flip with
  | false =>
      let V := R.forwardOrientedView
      have hisolated : 0 < sig (v p) (v q) (v (cycle rotation)) := by
        simpa [orientedFinSixLevel] using hpositive 0 (by norm_num)
      have hlower : ∀ i : Fin 5,
          sig (v p) (v q)
            (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0 := by
        intro i
        have h := hnegative (hullSixOneFiveLowerIndex i) (by
          simp [hullSixOneFiveLowerIndex])
        simpa [orientedFinSixLevel] using h
      exact R.oneFiveAt_false V rotation hisolated hlower
  | true =>
      let V := R.swappedOrientedView
      have hisolated : 0 < sig (v q) (v p) (v (cycle rotation)) := by
        have h : 0 < -sig (v p) (v q) (v (cycle rotation)) := by
          simpa [orientedFinSixLevel] using hpositive 0 (by norm_num)
        rw [sig_swap_first]
        exact h
      have hlower : ∀ i : Fin 5,
          sig (v q) (v p)
            (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0 := by
        intro i
        have h : -sig (v p) (v q)
            (v (cycle (rotation + hullSixOneFiveLowerIndex i))) < 0 := by
          simpa [orientedFinSixLevel] using
            hnegative (hullSixOneFiveLowerIndex i) (by
              simp [hullSixOneFiveLowerIndex])
        rw [sig_swap_first]
        exact h
      exact R.oneFiveAt_false V rotation hisolated hlower

/-- Direct adapter for witnesses extracted from `R.lineSignBlock`. -/
theorem oneFive_false_of_lineSignBlock_witness
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (rotation : Fin 6) (flip : Bool) (last : Fin 3)
    (hpositive : ∀ i : Fin 6, i.val ≤ last.val →
      0 < orientedFinSixLevel
        (fun j => sig (v p) (v q) (v (cycle j)))
        flip (rotation + i))
    (hnegative : ∀ i : Fin 6, last.val < i.val →
      orientedFinSixLevel
        (fun j => sig (v p) (v q) (v (cycle j)))
        flip (rotation + i) < 0)
    (hlast : last = 0) :
    False := by
  subst last
  exact R.oneFive_false_of_lineSignBlock_last_zero rotation flip
    hpositive hnegative

/-- After the `1 + 5` closure, every sign-block witness for a compact
residual is honestly in one of the still-separate `2 + 4` or `3 + 3`
branches. -/
theorem lineSignBlock_witness_with_last_ne_zero
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    ∃ rotation : Fin 6, ∃ flip : Bool, ∃ last : Fin 3,
      last ≠ 0 ∧
      (∀ i : Fin 6, i.val ≤ last.val →
        0 < orientedFinSixLevel
          (fun j => sig (v p) (v q) (v (cycle j)))
          flip (rotation + i)) ∧
      (∀ i : Fin 6, last.val < i.val →
        orientedFinSixLevel
          (fun j => sig (v p) (v q) (v (cycle j)))
          flip (rotation + i) < 0) := by
  obtain ⟨rotation, flip, last, hpositive, hnegative⟩ := R.lineSignBlock
  refine ⟨rotation, flip, last, ?_, hpositive, hnegative⟩
  intro hlast
  exact R.oneFive_false_of_lineSignBlock_witness
    rotation flip last hpositive hnegative hlast

end HullSixCompactCrossChordResidual

end Heilbronn8
