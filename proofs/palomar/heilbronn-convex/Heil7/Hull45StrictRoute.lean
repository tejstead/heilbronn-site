import Heil7.Hull45Strict

/-!
# Strict hull-four and hull-five routes

This module applies the sharp two-point packet and the crossed-equality
exclusion from `Hull45Strict` to the canonical hull-four and hull-five
carriers.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-! ## Strict hull-four route -/

/-- The hull-four route is uniformly away from equality when `m > 0`.
The all-on-one-side cases give `19*m/2`; every mixed case gives the still
larger `(7 + 2*sqrt 3)*m`. -/
theorem hullFour_strict_of_triangleInputs
    (two : TriangleTwoSharp) (three : TriangleThreeSeventeen) :
    ∀ (v : Configuration7), HullCCW v 4 →
      (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
      0 < minTri v → 9 * minTri v < fanArea v 4 := by
  intro v hccw hin hm
  let m := minTri v
  have hfloor : AllTrianglesFloor v m := allTrianglesFloor_minTri v
  have h012 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
  have h023 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
  have h012floor := hfloor 0 1 2 (by decide) (by decide) (by decide)
  have h023floor := hfloor 0 2 3 (by decide) (by decide) (by decide)
  rw [abs_of_pos h012] at h012floor
  rw [abs_of_pos h023] at h023floor
  have hi4 := hin 4 (by norm_num)
  have hi5 := hin 5 (by norm_num)
  have hi6 := hin 6 (by norm_num)
  have left4 (hd : sig (v 0) (v 2) (v 4) < 0) :
      InTriStrict (v 4) (v 0) (v 1) (v 2) := by
    apply inTriStrict_of_orientations h012
    · exact hi4.1 0 (by norm_num)
    · exact hi4.1 1 (by norm_num)
    · rw [n7_sig_reverse]
      linarith
  have left5 (hd : sig (v 0) (v 2) (v 5) < 0) :
      InTriStrict (v 5) (v 0) (v 1) (v 2) := by
    apply inTriStrict_of_orientations h012
    · exact hi5.1 0 (by norm_num)
    · exact hi5.1 1 (by norm_num)
    · rw [n7_sig_reverse]
      linarith
  have left6 (hd : sig (v 0) (v 2) (v 6) < 0) :
      InTriStrict (v 6) (v 0) (v 1) (v 2) := by
    apply inTriStrict_of_orientations h012
    · exact hi6.1 0 (by norm_num)
    · exact hi6.1 1 (by norm_num)
    · rw [n7_sig_reverse]
      linarith
  have right4 (hd : 0 < sig (v 0) (v 2) (v 4)) :
      InTriStrict (v 4) (v 0) (v 2) (v 3) :=
    inTriStrict_of_orientations h023 hd
      (hi4.1 2 (by norm_num)) (hi4.2 3 (by norm_num))
  have right5 (hd : 0 < sig (v 0) (v 2) (v 5)) :
      InTriStrict (v 5) (v 0) (v 2) (v 3) :=
    inTriStrict_of_orientations h023 hd
      (hi5.1 2 (by norm_num)) (hi5.2 3 (by norm_num))
  have right6 (hd : 0 < sig (v 0) (v 2) (v 6)) :
      InTriStrict (v 6) (v 0) (v 2) (v 3) :=
    inTriStrict_of_orientations h023 hd
      (hi6.1 2 (by norm_num)) (hi6.2 3 (by norm_num))
  have d4floor := hfloor 0 2 4 (by decide) (by decide) (by decide)
  have d5floor := hfloor 0 2 5 (by decide) (by decide) (by decide)
  have d6floor := hfloor 0 2 6 (by decide) (by decide) (by decide)
  have d4ne : sig (v 0) (v 2) (v 4) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at d4floor
    linarith
  have d5ne : sig (v 0) (v 2) (v 5) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at d5floor
    linarith
  have d6ne : sig (v 0) (v 2) (v 6) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at d6floor
    linarith
  have hcoefm :
      7 * m < (4 + 2 * Real.sqrt 3) * m :=
    mul_lt_mul_of_pos_right seven_lt_twoPointCoefficient hm
  by_cases d4 : 0 < sig (v 0) (v 2) (v 4)
  · by_cases d5 : 0 < sig (v 0) (v 2) (v 5)
    · by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
      · have h3 := three v m ![0, 2, 3, 4, 5, 6] (by decide) hm
          hfloor h023 (right4 d4) (right5 d5) (right6 d6)
        change 17 * m ≤ 2 * sig (v 0) (v 2) (v 3) at h3
        simp only [fanArea]
        nlinarith
      · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
          lt_of_le_of_ne (le_of_not_gt d6) d6ne
        have h2 := two v m ![0, 2, 3, 4, 5] (by decide) hm hfloor
          h023 (right4 d4) (right5 d5)
        have h1 := oneInterior_three v m ![0, 1, 2, 6] (by decide)
          hfloor h012 (left6 d6')
        change (4 + 2 * Real.sqrt 3) * m ≤
          sig (v 0) (v 2) (v 3) at h2
        change 3 * m ≤ sig (v 0) (v 1) (v 2) at h1
        simp only [fanArea]
        linarith
    · have d5' : sig (v 0) (v 2) (v 5) < 0 :=
        lt_of_le_of_ne (le_of_not_gt d5) d5ne
      by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
      · have h2 := two v m ![0, 2, 3, 4, 6] (by decide) hm hfloor
          h023 (right4 d4) (right6 d6)
        have h1 := oneInterior_three v m ![0, 1, 2, 5] (by decide)
          hfloor h012 (left5 d5')
        change (4 + 2 * Real.sqrt 3) * m ≤
          sig (v 0) (v 2) (v 3) at h2
        change 3 * m ≤ sig (v 0) (v 1) (v 2) at h1
        simp only [fanArea]
        linarith
      · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
          lt_of_le_of_ne (le_of_not_gt d6) d6ne
        have h2 := two v m ![0, 1, 2, 5, 6] (by decide) hm hfloor
          h012 (left5 d5') (left6 d6')
        have h1 := oneInterior_three v m ![0, 2, 3, 4] (by decide)
          hfloor h023 (right4 d4)
        change (4 + 2 * Real.sqrt 3) * m ≤
          sig (v 0) (v 1) (v 2) at h2
        change 3 * m ≤ sig (v 0) (v 2) (v 3) at h1
        simp only [fanArea]
        linarith
  · have d4' : sig (v 0) (v 2) (v 4) < 0 :=
      lt_of_le_of_ne (le_of_not_gt d4) d4ne
    by_cases d5 : 0 < sig (v 0) (v 2) (v 5)
    · by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
      · have h2 := two v m ![0, 2, 3, 5, 6] (by decide) hm hfloor
          h023 (right5 d5) (right6 d6)
        have h1 := oneInterior_three v m ![0, 1, 2, 4] (by decide)
          hfloor h012 (left4 d4')
        change (4 + 2 * Real.sqrt 3) * m ≤
          sig (v 0) (v 2) (v 3) at h2
        change 3 * m ≤ sig (v 0) (v 1) (v 2) at h1
        simp only [fanArea]
        linarith
      · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
          lt_of_le_of_ne (le_of_not_gt d6) d6ne
        have h2 := two v m ![0, 1, 2, 4, 6] (by decide) hm hfloor
          h012 (left4 d4') (left6 d6')
        have h1 := oneInterior_three v m ![0, 2, 3, 5] (by decide)
          hfloor h023 (right5 d5)
        change (4 + 2 * Real.sqrt 3) * m ≤
          sig (v 0) (v 1) (v 2) at h2
        change 3 * m ≤ sig (v 0) (v 2) (v 3) at h1
        simp only [fanArea]
        linarith
    · have d5' : sig (v 0) (v 2) (v 5) < 0 :=
        lt_of_le_of_ne (le_of_not_gt d5) d5ne
      by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
      · have h2 := two v m ![0, 1, 2, 4, 5] (by decide) hm hfloor
          h012 (left4 d4') (left5 d5')
        have h1 := oneInterior_three v m ![0, 2, 3, 6] (by decide)
          hfloor h023 (right6 d6)
        change (4 + 2 * Real.sqrt 3) * m ≤
          sig (v 0) (v 1) (v 2) at h2
        change 3 * m ≤ sig (v 0) (v 2) (v 3) at h1
        simp only [fanArea]
        linarith
      · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
          lt_of_le_of_ne (le_of_not_gt d6) d6ne
        have h3 := three v m ![0, 1, 2, 4, 5, 6] (by decide) hm
          hfloor h012 (left4 d4') (left5 d5') (left6 d6')
        change 17 * m ≤ 2 * sig (v 0) (v 1) (v 2) at h3
        simp only [fanArea]
        nlinarith

/-! ## Strict hull-five route -/

/-- The common-ear hull-five route is strict.  Equality in its
quadrilateral sub-bound is excluded using the actual fifth hull vertex. -/
theorem hullFive_strict_of_triangleTwo (two : TriangleTwoSharp) :
    ∀ (v : Configuration7), HullCCW v 5 →
      (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
      0 < minTri v → 9 * minTri v < fanArea v 5 := by
  intro v hull hin hm
  let m := minTri v
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
  have h120 : 0 < sig (v 1) (v 2) (v 0) :=
    n7_sig_pos_rotate h012
  have h230 : 0 < sig (v 2) (v 3) (v 0) :=
    n7_sig_pos_rotate h023
  have h240 : 0 < sig (v 2) (v 4) (v 0) :=
    n7_sig_pos_rotate h024
  have h340 : 0 < sig (v 3) (v 4) (v 0) :=
    n7_sig_pos_rotate h034
  have h401 : 0 < sig (v 4) (v 0) (v 1) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h014)
  have h341 : 0 < sig (v 3) (v 4) (v 1) :=
    n7_sig_pos_rotate h134
  have h301 : 0 < sig (v 3) (v 0) (v 1) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h013)
  have h402 : 0 < sig (v 4) (v 0) (v 2) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h024)
  have h412 : 0 < sig (v 4) (v 1) (v 2) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h124)
  have h342 : 0 < sig (v 3) (v 4) (v 2) :=
    n7_sig_pos_rotate h234
  have h403 : 0 < sig (v 4) (v 0) (v 3) :=
    n7_sig_pos_rotate (n7_sig_pos_rotate h034)
  rcases pentagon_common_complementary_quad v hull
      (hin 5 (by norm_num)) (hin 6 (by norm_num)) hm with
    h0 | h1 | h2 | h3 | h4
  · have hs := quadrilateralTwo_with_lastEar_strict two v m
        ![1, 2, 3, 4, 0, 5, 6] (by decide) hm hfloor
        ⟨h123, h124, h134, h234⟩ h0.1 h0.2 h120 h340 h401
    change 9 * m <
      (sig (v 1) (v 2) (v 3) + sig (v 1) (v 3) (v 4)) +
        sig (v 4) (v 0) (v 1) at hs
    have hid :
        (sig (v 1) (v 2) (v 3) + sig (v 1) (v 3) (v 4)) +
          sig (v 4) (v 0) (v 1) = fanArea v 5 := by
      simp only [fanArea, sig]
      ring
    exact hs.trans_eq hid
  · have hp : StrictInQuad (v 5) (v 2) (v 3) (v 4) (v 0) := by
      rcases h1.1 with ⟨h02, h23, h34, h40⟩
      exact ⟨h23, h34, h40, h02⟩
    have hq : StrictInQuad (v 6) (v 2) (v 3) (v 4) (v 0) := by
      rcases h1.2 with ⟨h02, h23, h34, h40⟩
      exact ⟨h23, h34, h40, h02⟩
    have h231 : 0 < sig (v 2) (v 3) (v 1) :=
      n7_sig_pos_rotate h123
    have hs := quadrilateralTwo_with_lastEar_strict two v m
      ![2, 3, 4, 0, 1, 5, 6] (by decide) hm hfloor
      ⟨h234, h230, h240, h340⟩ hp hq h231 h401 h012
    change 9 * m <
      (sig (v 2) (v 3) (v 4) + sig (v 2) (v 4) (v 0)) +
        sig (v 0) (v 1) (v 2) at hs
    have hid :
        (sig (v 2) (v 3) (v 4) + sig (v 2) (v 4) (v 0)) +
          sig (v 0) (v 1) (v 2) = fanArea v 5 := by
      simp only [fanArea, sig]
      ring
    exact hs.trans_eq hid
  · have hp : StrictInQuad (v 5) (v 3) (v 4) (v 0) (v 1) := by
      rcases h2.1 with ⟨h01, h13, h34, h40⟩
      exact ⟨h34, h40, h01, h13⟩
    have hq : StrictInQuad (v 6) (v 3) (v 4) (v 0) (v 1) := by
      rcases h2.2 with ⟨h01, h13, h34, h40⟩
      exact ⟨h34, h40, h01, h13⟩
    have hs := quadrilateralTwo_with_lastEar_strict two v m
      ![3, 4, 0, 1, 2, 5, 6] (by decide) hm hfloor
      ⟨h340, h341, h301, h401⟩ hp hq h342 h012 h123
    change 9 * m <
      (sig (v 3) (v 4) (v 0) + sig (v 3) (v 0) (v 1)) +
        sig (v 1) (v 2) (v 3) at hs
    have hid :
        (sig (v 3) (v 4) (v 0) + sig (v 3) (v 0) (v 1)) +
          sig (v 1) (v 2) (v 3) = fanArea v 5 := by
      simp only [fanArea, sig]
      ring
    exact hs.trans_eq hid
  · have hp : StrictInQuad (v 5) (v 4) (v 0) (v 1) (v 2) := by
      rcases h3.1 with ⟨h01, h12, h24, h40⟩
      exact ⟨h40, h01, h12, h24⟩
    have hq : StrictInQuad (v 6) (v 4) (v 0) (v 1) (v 2) := by
      rcases h3.2 with ⟨h01, h12, h24, h40⟩
      exact ⟨h40, h01, h12, h24⟩
    have hs := quadrilateralTwo_with_lastEar_strict two v m
      ![4, 0, 1, 2, 3, 5, 6] (by decide) hm hfloor
      ⟨h401, h402, h412, h012⟩ hp hq h403 h123 h234
    change 9 * m <
      (sig (v 4) (v 0) (v 1) + sig (v 4) (v 1) (v 2)) +
        sig (v 2) (v 3) (v 4) at hs
    have hid :
        (sig (v 4) (v 0) (v 1) + sig (v 4) (v 1) (v 2)) +
          sig (v 2) (v 3) (v 4) = fanArea v 5 := by
      simp only [fanArea, sig]
      ring
    exact hs.trans_eq hid
  · have hs := quadrilateralTwo_with_lastEar_strict two v m
      ![0, 1, 2, 3, 4, 5, 6] (by decide) hm hfloor
      ⟨h012, h013, h023, h123⟩ h4.1 h4.2 h014 h234 h340
    change 9 * m <
      (sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)) +
        sig (v 3) (v 4) (v 0) at hs
    have hid :
        (sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3)) +
          sig (v 3) (v 4) (v 0) = fanArea v 5 := by
      simp only [fanArea, sig]
      ring
    exact hs.trans_eq hid

/-- Unconditional strict hull-four and hull-five fields, under the only
necessary nondegeneracy hypothesis `0 < minTri v`. -/
theorem hull45_strict_fields :
    (∀ (v : Configuration7), HullCCW v 4 →
      (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
      0 < minTri v → 9 * minTri v < fanArea v 4) ∧
    (∀ (v : Configuration7), HullCCW v 5 →
      (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
      0 < minTri v → 9 * minTri v < fanArea v 5) :=
  ⟨hullFour_strict_of_triangleInputs triangleTwoSharp_holds
      triangleThreeSeventeen_holds,
    hullFive_strict_of_triangleTwo triangleTwoSharp_holds⟩

end HeilbronnChallenge.N7Upper
