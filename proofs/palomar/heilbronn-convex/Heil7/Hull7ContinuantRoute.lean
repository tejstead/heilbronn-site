import Heil7.CanonicalUpper
import Heil7.Hull7ContinuantScalar

/-!
# Direct hull-seven route through fan minors

This file connects the rational continuant theorem to the canonical
`HullCCW`/`minTri` interface.  It uses only positivity of the ordered triangle
minors, the elementary four-point area identities, and six two-dimensional
Pluecker identities.  In particular, it does not use an analytic extremizer,
the Renyi--Sulanke product comparison, or trigonometry.

The conclusion is the canonical hull-seven triangle bound.  A separate lemma
would still be required to replace the `minTri` floor below by a floor assumed
only for the seven ears.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The direct continuant supplies the hull-seven field needed by the
canonical upper-bound assembly. -/
theorem hullSeven_of_continuant :
    ∀ (v : Configuration7), HullCCW v 7 →
      9 * minTri v ≤ fanArea v 7 := by
  intro v hull
  let a : ℝ := sig (v 0) (v 1) (v 2)
  let b : ℝ := sig (v 0) (v 2) (v 3)
  let c : ℝ := sig (v 0) (v 3) (v 4)
  let d : ℝ := sig (v 0) (v 4) (v 5)
  let e : ℝ := sig (v 0) (v 5) (v 6)
  let p16 : ℝ := sig (v 0) (v 1) (v 6)
  let q2 : ℝ := sig (v 0) (v 1) (v 3)
  let q3 : ℝ := sig (v 0) (v 2) (v 4)
  let q4 : ℝ := sig (v 0) (v 3) (v 5)
  let q5 : ℝ := sig (v 0) (v 4) (v 6)
  let r14 : ℝ := sig (v 0) (v 1) (v 4)
  let r15 : ℝ := sig (v 0) (v 1) (v 5)
  let r25 : ℝ := sig (v 0) (v 2) (v 5)
  let r26 : ℝ := sig (v 0) (v 2) (v 6)
  let r36 : ℝ := sig (v 0) (v 3) (v 6)

  have haPos : 0 < a := by
    exact hull 0 1 2 (by decide) (by decide) (by norm_num)
  have hbPos : 0 < b := by
    exact hull 0 2 3 (by decide) (by decide) (by norm_num)
  have hcPos : 0 < c := by
    exact hull 0 3 4 (by decide) (by decide) (by norm_num)
  have hdPos : 0 < d := by
    exact hull 0 4 5 (by decide) (by decide) (by norm_num)
  have hePos : 0 < e := by
    exact hull 0 5 6 (by decide) (by decide) (by norm_num)
  have hp16Pos : 0 < p16 := by
    exact hull 0 1 6 (by decide) (by decide) (by norm_num)
  have hq2Pos : 0 < q2 := by
    exact hull 0 1 3 (by decide) (by decide) (by norm_num)
  have hq3Pos : 0 < q3 := by
    exact hull 0 2 4 (by decide) (by decide) (by norm_num)
  have hq4Pos : 0 < q4 := by
    exact hull 0 3 5 (by decide) (by decide) (by norm_num)
  have hq5Pos : 0 < q5 := by
    exact hull 0 4 6 (by decide) (by decide) (by norm_num)
  have hr14Pos : 0 < r14 := by
    exact hull 0 1 4 (by decide) (by decide) (by norm_num)
  have hr15Pos : 0 < r15 := by
    exact hull 0 1 5 (by decide) (by decide) (by norm_num)
  have hr25Pos : 0 < r25 := by
    exact hull 0 2 5 (by decide) (by decide) (by norm_num)
  have hr26Pos : 0 < r26 := by
    exact hull 0 2 6 (by decide) (by decide) (by norm_num)
  have hr36Pos : 0 < r36 := by
    exact hull 0 3 6 (by decide) (by decide) (by norm_num)

  have hmin : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      0 < sig (v i) (v j) (v k) →
      minTri v ≤ sig (v i) (v j) (v k) := by
    intro i j k hij hik hjk hpos
    have h := minTri_le_of_distinct v i j k hij hik hjk
    rwa [abs_of_pos hpos] at h

  have ha : minTri v ≤ a :=
    hmin 0 1 2 (by decide) (by decide) (by decide) haPos
  have hb : minTri v ≤ b :=
    hmin 0 2 3 (by decide) (by decide) (by decide) hbPos
  have hc : minTri v ≤ c :=
    hmin 0 3 4 (by decide) (by decide) (by decide) hcPos
  have hd : minTri v ≤ d :=
    hmin 0 4 5 (by decide) (by decide) (by decide) hdPos
  have he : minTri v ≤ e :=
    hmin 0 5 6 (by decide) (by decide) (by decide) hePos
  have hp16 : minTri v ≤ p16 :=
    hmin 0 1 6 (by decide) (by decide) (by decide) hp16Pos

  have hear2 : minTri v ≤ sig (v 1) (v 2) (v 3) := by
    apply hmin 1 2 3 (by decide) (by decide) (by decide)
    exact hull 1 2 3 (by decide) (by decide) (by norm_num)
  have hear3 : minTri v ≤ sig (v 2) (v 3) (v 4) := by
    apply hmin 2 3 4 (by decide) (by decide) (by decide)
    exact hull 2 3 4 (by decide) (by decide) (by norm_num)
  have hear4 : minTri v ≤ sig (v 3) (v 4) (v 5) := by
    apply hmin 3 4 5 (by decide) (by decide) (by decide)
    exact hull 3 4 5 (by decide) (by decide) (by norm_num)
  have hear5 : minTri v ≤ sig (v 4) (v 5) (v 6) := by
    apply hmin 4 5 6 (by decide) (by decide) (by decide)
    exact hull 4 5 6 (by decide) (by decide) (by norm_num)

  have hcap2 : q2 ≤ a + b - minTri v := by
    have hid :
        q2 + sig (v 1) (v 2) (v 3) = a + b := by
      dsimp [q2, a, b]
      simp only [sig]
      ring
    linarith
  have hcap3 : q3 ≤ b + c - minTri v := by
    have hid :
        q3 + sig (v 2) (v 3) (v 4) = b + c := by
      dsimp [q3, b, c]
      simp only [sig]
      ring
    linarith
  have hcap4 : q4 ≤ c + d - minTri v := by
    have hid :
        q4 + sig (v 3) (v 4) (v 5) = c + d := by
      dsimp [q4, c, d]
      simp only [sig]
      ring
    linarith
  have hcap5 : q5 ≤ d + e - minTri v := by
    have hid :
        q5 + sig (v 4) (v 5) (v 6) = d + e := by
      dsimp [q5, d, e]
      simp only [sig]
      ring
    linarith

  have h14 : b * r14 = q2 * q3 - a * c := by
    dsimp [a, b, c, q2, q3, r14]
    simp only [sig]
    ring
  have h15 : c * r15 = r14 * q4 - q2 * d := by
    dsimp [c, d, q2, q4, r14, r15]
    simp only [sig]
    ring
  have h16 : d * p16 = r15 * q5 - r14 * e := by
    dsimp [d, e, p16, q5, r14, r15]
    simp only [sig]
    ring
  have h25 : c * r25 = q3 * q4 - b * d := by
    dsimp [b, c, d, q3, q4, r25]
    simp only [sig]
    ring
  have h26 : d * r26 = r25 * q5 - q3 * e := by
    dsimp [d, e, q3, q5, r25, r26]
    simp only [sig]
    ring
  have h36 : d * r36 = q4 * q5 - c * e := by
    dsimp [c, d, e, q4, q5, r36]
    simp only [sig]
    ring

  rcases eq_or_lt_of_le (minTri_nonneg v) with hm | hm
  · rw [← hm]
    norm_num
    simpa [a, b, c, d, e, fanArea] using
      (add_nonneg
        (add_nonneg
          (add_nonneg (add_nonneg haPos.le hbPos.le) hcPos.le) hdPos.le)
        hePos.le)
  · have hscalar := nine_mul_le_fanSum_of_hullSeven_continuant
      (minTri v) a b c d e p16 q2 q3 q4 q5 r14 r15 r25 r26 r36
      hm ha hb hc hd he hp16
      hq2Pos.le hq3Pos.le hq4Pos.le hq5Pos.le
      hr14Pos.le hr15Pos.le hr25Pos.le hr26Pos.le hr36Pos.le
      hcap2 hcap3 hcap4 hcap5 h14 h15 h16 h25 h26 h36
    simpa [a, b, c, d, e, fanArea] using hscalar

end HeilbronnChallenge.N7Upper
