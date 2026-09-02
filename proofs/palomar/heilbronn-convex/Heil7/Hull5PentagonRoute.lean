import Heil7.Hull45Core

/-!
# Pentagon common-ear and hull-five route

This module contains the common-empty-ear geometry and the hull-five adapter.
The shared determinant inputs and quadrilateral estimate live in
`Hull45Core`; `Hull45Route` remains the compatibility facade.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-! ## A common empty pentagon ear -/

lemma sig_ne_zero_of_minTri (v : Configuration7) (hm : 0 < minTri v)
    (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  have hfloor := minTri_le_of_distinct v i j k hij hik hjk
  intro hz
  rw [hz, abs_zero] at hfloor
  linarith

lemma inTri_halfplane_n7 {x u v w l r : Point}
    (hx : HullBridge.InTri x u v w)
    (hu : 0 ≤ sig l r u) (hv : 0 ≤ sig l r v)
    (hw : 0 ≤ sig l r w) :
    0 ≤ sig l r x := by
  obtain ⟨a, b, c, ha, hb, hc, habc, hxe⟩ := hx
  rw [hxe, n7_sig_affine_third l r u v w a b c habc]
  exact add_nonneg (add_nonneg (mul_nonneg ha hu) (mul_nonneg hb hv))
    (mul_nonneg hc hw)

lemma inTri_opposite_halfplanes_n7
    {x u v w u' v' w' l r : Point}
    (hne : sig l r x ≠ 0)
    (hleft : HullBridge.InTri x u v w)
    (hright : HullBridge.InTri x u' v' w')
    (hu : 0 ≤ sig l r u) (hv : 0 ≤ sig l r v)
    (hw : 0 ≤ sig l r w)
    (hu' : 0 ≤ sig r l u') (hv' : 0 ≤ sig r l v')
    (hw' : 0 ≤ sig r l w') : False := by
  have hlr := inTri_halfplane_n7 hleft hu hv hw
  have hrl := inTri_halfplane_n7 hright hu' hv' hw'
  rw [n7_sig_reverse l r x] at hrl
  apply hne
  linarith

lemma chord_pos_of_not_in_ear_n7 {x u v w : Point}
    (huvw : 0 < sig u v w)
    (huvx : 0 < sig u v x) (hvwx : 0 < sig v w x)
    (hne : sig u w x ≠ 0)
    (hout : ¬ HullBridge.InTri x u v w) :
    0 < sig u w x := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exfalso
    apply hout
    apply HullBridge.inTri_of_sig x u v w
    · change 0 < sig u v w
      exact huvw
    · change 0 ≤ sig x v w
      rw [n7_sig_rotate x v w]
      exact hvwx.le
    · change 0 ≤ sig u x w
      rw [n7_sig_swap_last u w x]
      linarith
    · change 0 ≤ sig u v x
      exact huvx.le
  · exact hpos

set_option maxHeartbeats 800000 in
/-- Among the five ears of a strict convex pentagon, two interior points miss
a common ear.  Deleting that ear's middle vertex produces one of the five
displayed strict complementary quadrilaterals containing both points. -/
lemma pentagon_common_complementary_quad
    (v : Configuration7) (hull : HullCCW v 5)
    (h5 : InHullN v 5 5) (h6 : InHullN v 5 6)
    (hm : 0 < minTri v) :
    (StrictInQuad (v 5) (v 1) (v 2) (v 3) (v 4) ∧
      StrictInQuad (v 6) (v 1) (v 2) (v 3) (v 4)) ∨
    (StrictInQuad (v 5) (v 0) (v 2) (v 3) (v 4) ∧
      StrictInQuad (v 6) (v 0) (v 2) (v 3) (v 4)) ∨
    (StrictInQuad (v 5) (v 0) (v 1) (v 3) (v 4) ∧
      StrictInQuad (v 6) (v 0) (v 1) (v 3) (v 4)) ∨
    (StrictInQuad (v 5) (v 0) (v 1) (v 2) (v 4) ∧
      StrictInQuad (v 6) (v 0) (v 1) (v 2) (v 4)) ∨
    (StrictInQuad (v 5) (v 0) (v 1) (v 2) (v 3) ∧
      StrictInQuad (v 6) (v 0) (v 1) (v 2) (v 3)) := by
  classical
  have h012 := hull 0 1 2 (by decide) (by decide) (by norm_num)
  have h013 := hull 0 1 3 (by decide) (by decide) (by norm_num)
  have h014 := hull 0 1 4 (by decide) (by decide) (by norm_num)
  have h023 := hull 0 2 3 (by decide) (by decide) (by norm_num)
  have h024 := hull 0 2 4 (by decide) (by decide) (by norm_num)
  have h034 := hull 0 3 4 (by decide) (by decide) (by norm_num)
  have h123 := hull 1 2 3 (by decide) (by decide) (by norm_num)
  have h124 := hull 1 2 4 (by decide) (by decide) (by norm_num)
  have h134 := hull 1 3 4 (by decide) (by decide) (by norm_num)
  have h234 := hull 2 3 4 (by decide) (by decide) (by norm_num)
  have hEAB : 0 < sig (v 4) (v 0) (v 1) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h014)
  have hDEA : 0 < sig (v 3) (v 4) (v 0) := n7_sig_pos_rotate h034
  have hBEA : 0 < sig (v 1) (v 4) (v 0) := n7_sig_pos_rotate h014
  have hEBC : 0 < sig (v 4) (v 1) (v 2) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h124)
  have hEBD : 0 < sig (v 4) (v 1) (v 3) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h134)
  have hCEA : 0 < sig (v 2) (v 4) (v 0) := n7_sig_pos_rotate h024
  have hCEB : 0 < sig (v 2) (v 4) (v 1) := n7_sig_pos_rotate h124
  have hECD : 0 < sig (v 4) (v 2) (v 3) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h234)
  have hCAB : 0 < sig (v 2) (v 0) (v 1) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h012)
  have hDAB : 0 < sig (v 3) (v 0) (v 1) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h013)
  have hDAC : 0 < sig (v 3) (v 0) (v 2) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h023)
  have hBDA : 0 < sig (v 1) (v 3) (v 0) := n7_sig_pos_rotate h013
  have hDBC : 0 < sig (v 3) (v 1) (v 2) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h123)
  obtain ⟨h5e, h5c⟩ := h5
  obtain ⟨h6e, h6c⟩ := h6
  have p01 := h5e 0 (by norm_num)
  have p12 := h5e 1 (by norm_num)
  have p23 := h5e 2 (by norm_num)
  have p34 := h5e 3 (by norm_num)
  have p40 := h5c 4 (by norm_num)
  have q01 := h6e 0 (by norm_num)
  have q12 := h6e 1 (by norm_num)
  have q23 := h6e 2 (by norm_num)
  have q34 := h6e 3 (by norm_num)
  have q40 := h6c 4 (by norm_num)
  have pBE := sig_ne_zero_of_minTri v hm 1 4 5
    (by decide) (by decide) (by decide)
  have pEB := sig_ne_zero_of_minTri v hm 4 1 5
    (by decide) (by decide) (by decide)
  have pAC := sig_ne_zero_of_minTri v hm 0 2 5
    (by decide) (by decide) (by decide)
  have pBD := sig_ne_zero_of_minTri v hm 1 3 5
    (by decide) (by decide) (by decide)
  have pCE := sig_ne_zero_of_minTri v hm 2 4 5
    (by decide) (by decide) (by decide)
  have pDA := sig_ne_zero_of_minTri v hm 3 0 5
    (by decide) (by decide) (by decide)
  have qBE := sig_ne_zero_of_minTri v hm 1 4 6
    (by decide) (by decide) (by decide)
  have qEB := sig_ne_zero_of_minTri v hm 4 1 6
    (by decide) (by decide) (by decide)
  have qAC := sig_ne_zero_of_minTri v hm 0 2 6
    (by decide) (by decide) (by decide)
  have qBD := sig_ne_zero_of_minTri v hm 1 3 6
    (by decide) (by decide) (by decide)
  have qCE := sig_ne_zero_of_minTri v hm 2 4 6
    (by decide) (by decide) (by decide)
  have qDA := sig_ne_zero_of_minTri v hm 3 0 6
    (by decide) (by decide) (by decide)
  let e0 : Point → Prop := fun x => HullBridge.InTri x (v 4) (v 0) (v 1)
  let e1 : Point → Prop := fun x => HullBridge.InTri x (v 0) (v 1) (v 2)
  let e2 : Point → Prop := fun x => HullBridge.InTri x (v 1) (v 2) (v 3)
  let e3 : Point → Prop := fun x => HullBridge.InTri x (v 2) (v 3) (v 4)
  let e4 : Point → Prop := fun x => HullBridge.InTri x (v 3) (v 4) (v 0)
  have no02 : ∀ x : Point, sig (v 1) (v 4) x ≠ 0 →
      ¬(e0 x ∧ e2 x) := by
    intro x hne h
    exact inTri_opposite_halfplanes_n7 (l := v 1) (r := v 4)
      hne h.1 h.2
      (by simp [sig]) hBEA.le (by simp [sig])
      (by simp [sig]) hEBC.le hEBD.le
  have no03 : ∀ x : Point, sig (v 2) (v 4) x ≠ 0 →
      ¬(e0 x ∧ e3 x) := by
    intro x hne h
    exact inTri_opposite_halfplanes_n7 (l := v 2) (r := v 4)
      hne h.1 h.2
      (by simp [sig]) hCEA.le hCEB.le
      (by simp [sig]) hECD.le (by simp [sig])
  have no13 : ∀ x : Point, sig (v 0) (v 2) x ≠ 0 →
      ¬(e1 x ∧ e3 x) := by
    intro x hne h
    exact inTri_opposite_halfplanes_n7 (l := v 0) (r := v 2)
      hne h.2 h.1
      (by simp [sig]) h023.le h024.le
      (by simp [sig]) hCAB.le (by simp [sig])
  have no14 : ∀ x : Point, sig (v 3) (v 0) x ≠ 0 →
      ¬(e1 x ∧ e4 x) := by
    intro x hne h
    exact inTri_opposite_halfplanes_n7 (l := v 3) (r := v 0)
      hne h.1 h.2
      (by simp [sig]) hDAB.le hDAC.le
      (by simp [sig]) h034.le (by simp [sig])
  have no24 : ∀ x : Point, sig (v 1) (v 3) x ≠ 0 →
      ¬(e2 x ∧ e4 x) := by
    intro x hne h
    exact inTri_opposite_halfplanes_n7 (l := v 1) (r := v 3)
      hne h.2 h.1
      (by simp [sig]) h134.le hBDA.le
      (by simp [sig]) hDBC.le (by simp [sig])
  have hp02 := no02 (v 5) pBE
  have hp03 := no03 (v 5) pCE
  have hp13 := no13 (v 5) pAC
  have hp14 := no14 (v 5) pDA
  have hp24 := no24 (v 5) pBD
  have hq02 := no02 (v 6) qBE
  have hq03 := no03 (v 6) qCE
  have hq13 := no13 (v 6) qAC
  have hq14 := no14 (v 6) qDA
  have hq24 := no24 (v 6) qBD
  have hmiss :
      (¬e0 (v 5) ∧ ¬e0 (v 6)) ∨
      (¬e1 (v 5) ∧ ¬e1 (v 6)) ∨
      (¬e2 (v 5) ∧ ¬e2 (v 6)) ∨
      (¬e3 (v 5) ∧ ¬e3 (v 6)) ∨
      (¬e4 (v 5) ∧ ¬e4 (v 6)) := by
    by_cases hp0 : e0 (v 5)
    · have hp2 : ¬e2 (v 5) := fun hp => hp02 ⟨hp0, hp⟩
      have hp3 : ¬e3 (v 5) := fun hp => hp03 ⟨hp0, hp⟩
      by_cases hq2 : e2 (v 6)
      · have hq0 : ¬e0 (v 6) := fun hq => hq02 ⟨hq, hq2⟩
        have hq4 : ¬e4 (v 6) := fun hq => hq24 ⟨hq2, hq⟩
        by_cases hq3 : e3 (v 6)
        · have hq1 : ¬e1 (v 6) := fun hq => hq13 ⟨hq, hq3⟩
          by_cases hp1 : e1 (v 5)
          · have hp4 : ¬e4 (v 5) := fun hp => hp14 ⟨hp1, hp⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp4, hq4⟩)))
          · exact Or.inr (Or.inl ⟨hp1, hq1⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, hq3⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hp2, hq2⟩))
    · by_cases hq0 : e0 (v 6)
      · have hq2 : ¬e2 (v 6) := fun hq => hq02 ⟨hq0, hq⟩
        have hq3 : ¬e3 (v 6) := fun hq => hq03 ⟨hq0, hq⟩
        by_cases hp2 : e2 (v 5)
        · have hp4 : ¬e4 (v 5) := fun hp => hp24 ⟨hp2, hp⟩
          by_cases hp3 : e3 (v 5)
          · have hp1 : ¬e1 (v 5) := fun hp => hp13 ⟨hp, hp3⟩
            by_cases hq4 : e4 (v 6)
            · have hq1 : ¬e1 (v 6) := fun hq => hq14 ⟨hq, hq4⟩
              exact Or.inr (Or.inl ⟨hp1, hq1⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp4, hq4⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, hq3⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨hp2, hq2⟩))
      · exact Or.inl ⟨hp0, hq0⟩
  rcases hmiss with h0 | h1 | h2 | h3 | h4
  · left
    exact ⟨⟨p12, p23, p34,
        chord_pos_of_not_in_ear_n7 hEAB p40 p01 pEB h0.1⟩,
      ⟨q12, q23, q34,
        chord_pos_of_not_in_ear_n7 hEAB q40 q01 qEB h0.2⟩⟩
  · right; left
    exact ⟨⟨chord_pos_of_not_in_ear_n7 h012 p01 p12 pAC h1.1,
        p23, p34, p40⟩,
      ⟨chord_pos_of_not_in_ear_n7 h012 q01 q12 qAC h1.2,
        q23, q34, q40⟩⟩
  · right; right; left
    exact ⟨⟨p01,
        chord_pos_of_not_in_ear_n7 h123 p12 p23 pBD h2.1,
        p34, p40⟩,
      ⟨q01,
        chord_pos_of_not_in_ear_n7 h123 q12 q23 qBD h2.2,
        q34, q40⟩⟩
  · right; right; right; left
    exact ⟨⟨p01, p12,
        chord_pos_of_not_in_ear_n7 h234 p23 p34 pCE h3.1, p40⟩,
      ⟨q01, q12,
        chord_pos_of_not_in_ear_n7 h234 q23 q34 qCE h3.2, q40⟩⟩
  · right; right; right; right
    exact ⟨⟨p01, p12, p23,
        chord_pos_of_not_in_ear_n7 hDEA p34 p40 pDA h4.1⟩,
      ⟨q01, q12, q23,
        chord_pos_of_not_in_ear_n7 hDEA q34 q40 qDA h4.2⟩⟩

/-! ## Hull five -/

/-- `TriangleTwoSeven` supplies the quadrilateral estimate, while the common
empty-ear lemma supplies the required complementary quadrilateral.  This is
the canonical `HullCaseBounds.h5` signature. -/
theorem hullFive_of_triangleTwo (two : TriangleTwoSeven) :
    ∀ (v : Configuration7), HullCCW v 5 →
      (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
      9 * minTri v ≤ fanArea v 5 := by
  intro v hull hin
  rcases eq_or_lt_of_le (minTri_nonneg v) with hzero | hm
  · have h012 := hull 0 1 2 (by decide) (by decide) (by norm_num)
    have h023 := hull 0 2 3 (by decide) (by decide) (by norm_num)
    have h034 := hull 0 3 4 (by decide) (by decide) (by norm_num)
    rw [← hzero]
    simp only [zero_mul, fanArea]
    linarith
  · let m := minTri v
    have hfloor : AllTrianglesFloor v m := allTrianglesFloor_minTri v
    have h012 := hull 0 1 2 (by decide) (by decide) (by norm_num)
    have h013 := hull 0 1 3 (by decide) (by decide) (by norm_num)
    have h014 := hull 0 1 4 (by decide) (by decide) (by norm_num)
    have h023 := hull 0 2 3 (by decide) (by decide) (by norm_num)
    have h024 := hull 0 2 4 (by decide) (by decide) (by norm_num)
    have h034 := hull 0 3 4 (by decide) (by decide) (by norm_num)
    have h123 := hull 1 2 3 (by decide) (by decide) (by norm_num)
    have h124 := hull 1 2 4 (by decide) (by decide) (by norm_num)
    have h134 := hull 1 3 4 (by decide) (by decide) (by norm_num)
    have h234 := hull 2 3 4 (by decide) (by decide) (by norm_num)
    have hEAB : 0 < sig (v 4) (v 0) (v 1) :=
      n7_sig_pos_rotate (n7_sig_pos_rotate h014)
    have hDEA : 0 < sig (v 3) (v 4) (v 0) := n7_sig_pos_rotate h034
    rcases pentagon_common_complementary_quad v hull
      (hin 5 (by norm_num)) (hin 6 (by norm_num)) hm with
      h0 | h1 | h2 | h3 | h4
    · have hq := quadrilateralTwoEight two v m ![1, 2, 3, 4, 5, 6]
          (by decide) hm hfloor ⟨h123, h124, h134, h234⟩ h0.1 h0.2
      change 8 * m ≤ sig (v 1) (v 2) (v 3) +
        sig (v 1) (v 3) (v 4) at hq
      have hear := hfloor 4 0 1 (by decide) (by decide) (by decide)
      rw [abs_of_pos hEAB] at hear
      have hid : fanArea v 5 =
          (sig (v 1) (v 2) (v 3) + sig (v 1) (v 3) (v 4)) +
            sig (v 4) (v 0) (v 1) := by
        simp only [fanArea, sig]
        ring
      rw [hid]
      linarith
    · have hq := quadrilateralTwoEight two v m ![0, 2, 3, 4, 5, 6]
          (by decide) hm hfloor ⟨h023, h024, h034, h234⟩ h1.1 h1.2
      change 8 * m ≤ sig (v 0) (v 2) (v 3) +
        sig (v 0) (v 3) (v 4) at hq
      have hear := hfloor 0 1 2 (by decide) (by decide) (by decide)
      rw [abs_of_pos h012] at hear
      simp only [fanArea]
      linarith
    · have hq := quadrilateralTwoEight two v m ![0, 1, 3, 4, 5, 6]
          (by decide) hm hfloor ⟨h013, h014, h034, h134⟩ h2.1 h2.2
      change 8 * m ≤ sig (v 0) (v 1) (v 3) +
        sig (v 0) (v 3) (v 4) at hq
      have hear := hfloor 1 2 3 (by decide) (by decide) (by decide)
      rw [abs_of_pos h123] at hear
      have hid : fanArea v 5 =
          (sig (v 0) (v 1) (v 3) + sig (v 0) (v 3) (v 4)) +
            sig (v 1) (v 2) (v 3) := by
        simp only [fanArea, sig]
        ring
      rw [hid]
      linarith
    · have hq := quadrilateralTwoEight two v m ![0, 1, 2, 4, 5, 6]
          (by decide) hm hfloor ⟨h012, h014, h024, h124⟩ h3.1 h3.2
      change 8 * m ≤ sig (v 0) (v 1) (v 2) +
        sig (v 0) (v 2) (v 4) at hq
      have hear := hfloor 2 3 4 (by decide) (by decide) (by decide)
      rw [abs_of_pos h234] at hear
      have hid : fanArea v 5 =
          (sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 4)) +
            sig (v 2) (v 3) (v 4) := by
        simp only [fanArea, sig]
        ring
      rw [hid]
      linarith
    · have hq := quadrilateralTwoEight two v m ![0, 1, 2, 3, 5, 6]
          (by decide) hm hfloor ⟨h012, h013, h023, h123⟩ h4.1 h4.2
      change 8 * m ≤ sig (v 0) (v 1) (v 2) +
        sig (v 0) (v 2) (v 3) at hq
      have hear := hfloor 3 4 0 (by decide) (by decide) (by decide)
      rw [abs_of_pos hDEA] at hear
      have hid : fanArea v 5 =
          (sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)) +
            sig (v 3) (v 4) (v 0) := by
        simp only [fanArea, sig]
        ring
      rw [hid]
      linarith

/-- Package the two closed adapters into the canonical hull-case fields. -/
theorem hull45_fields (two : TriangleTwoSeven)
    (three : TriangleThreeSeventeen) :
    (∀ (v : Configuration7), HullCCW v 4 →
      (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
      9 * minTri v ≤ fanArea v 4) ∧
    (∀ (v : Configuration7), HullCCW v 5 →
      (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
      9 * minTri v ≤ fanArea v 5) :=
  ⟨hullFour_of_triangleInputs two three, hullFive_of_triangleTwo two⟩

end HeilbronnChallenge.N7Upper

