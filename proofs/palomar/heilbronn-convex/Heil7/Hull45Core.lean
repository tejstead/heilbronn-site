import Heil7.CanonicalUpper

/-!
# Compact hull-four and hull-five determinant routes

This source-only module states the two homogeneous triangle estimates in the
normalization actually consumed by the seven-point problem and develops their
finite determinant adapters.  A selected `Fin 5` or `Fin 6` packet is passed
directly to each scalar input; no dummy point is appended, so the packet's
minimum cannot be lowered by padding.

All areas below are doubled signed areas.  `TriangleTwoSeven` is a rational
weakening of TH8 Lemma 1.  `TriangleThreeSeventeen` is the exact homogeneous
form of `th8_lemma3`: `17*m <= 2*[ABC]`.  Neither proposition is asserted in
this file.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

abbrev Point := ℝ × ℝ

/-- Strict barycentric membership.  This is definitionally the same notion
used by the proved n=8 triangle-hull estimates. -/
def InTriStrict (p a b c : Point) : Prop :=
  ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧
    p = x • a + y • b + z • c

/-- Strict membership behind the four cyclic boundary edges. -/
def StrictInQuad (p a b c d : Point) : Prop :=
  0 < sig a b p ∧ 0 < sig b c p ∧
  0 < sig c d p ∧ 0 < sig d a p

/-- Every triangle on an ambient finite labelled family has doubled area at
least `m`.  Repeated labels are deliberately excluded. -/
def AllTrianglesFloor {n : ℕ} (w : Fin n → Point) (m : ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    m ≤ |sig (w i) (w j) (w k)|

/-- Homogeneous rational consequence of TH8 Lemma 1, on the selected
five-point packet `A,B,C,P,Q`. -/
def TriangleTwoSeven : Prop :=
  ∀ {n : ℕ} (w : Fin n → Point) (m : ℝ) (e : Fin 5 → Fin n),
    Function.Injective e → 0 < m → AllTrianglesFloor w m →
    0 < sig (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 3)) (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 4)) (w (e 0)) (w (e 1)) (w (e 2)) →
    7 * m ≤ sig (w (e 0)) (w (e 1)) (w (e 2))

/-- Homogeneous form of `th8_lemma3`, on the selected six-point packet
`A,B,C,P,Q,R`. -/
def TriangleThreeSeventeen : Prop :=
  ∀ {n : ℕ} (w : Fin n → Point) (m : ℝ) (e : Fin 6 → Fin n),
    Function.Injective e → 0 < m → AllTrianglesFloor w m →
    0 < sig (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 3)) (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 4)) (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 5)) (w (e 0)) (w (e 1)) (w (e 2)) →
    17 * m ≤ 2 * sig (w (e 0)) (w (e 1)) (w (e 2))

lemma n7_sig_rotate (a b c : Point) : sig a b c = sig b c a := by
  simp only [sig]
  ring

lemma n7_sig_reverse (a b c : Point) : sig b a c = -sig a b c := by
  simp only [sig]
  ring

lemma n7_sig_swap_last (a b c : Point) : sig a c b = -sig a b c := by
  simp only [sig]
  ring

lemma n7_sig_pos_rotate {a b c : Point} (h : 0 < sig a b c) :
    0 < sig b c a := by
  rwa [← n7_sig_rotate a b c]

lemma n7_sig_affine_third (a b p q r : Point) (x y z : ℝ)
    (hsum : x + y + z = 1) :
    sig a b (x • p + y • q + z • r) =
      x * sig a b p + y * sig a b q + z * sig a b r := by
  have hz : z = 1 - x - y := by linarith
  rw [hz]
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

/-- Orientation inequalities give strict barycentric coordinates. -/
lemma inTriStrict_of_orientations {p a b c : Point}
    (habc : 0 < sig a b c)
    (habp : 0 < sig a b p) (hbcp : 0 < sig b c p)
    (hcap : 0 < sig c a p) :
    InTriStrict p a b c := by
  have hpbc : 0 < sig p b c := by
    rw [n7_sig_rotate p b c]
    exact hbcp
  have hapc : 0 < sig a p c := by
    rw [n7_sig_rotate a p c, n7_sig_rotate p c a]
    exact hcap
  have hne : sig a b c ≠ 0 := habc.ne'
  refine ⟨sig p b c / sig a b c, sig a p c / sig a b c,
    sig a b p / sig a b c, div_pos hpbc habc, div_pos hapc habc,
    div_pos habp habc, ?_, ?_⟩
  · field_simp [hne]
    simp only [sig]
    ring
  · apply Prod.ext
    · simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
      field_simp [hne]
      simp only [sig]
      ring
    · simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      field_simp [hne]
      simp only [sig]
      ring

/-- The three positive fan cells of a strict interior point. -/
lemma inTriStrict_fan_pos {p a b c : Point}
    (habc : 0 < sig a b c) (hp : InTriStrict p a b c) :
    0 < sig p b c ∧ 0 < sig p c a ∧ 0 < sig p a b := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hpe⟩ := hp
  have hz' : z = 1 - x - y := by linarith
  have h1 : sig p b c = x * sig a b c := by
    rw [hpe, hz']
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul]
    ring
  have h2 : sig p c a = y * sig a b c := by
    rw [hpe, hz']
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul]
    ring
  have h3 : sig p a b = z * sig a b c := by
    rw [hpe, hz']
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul]
    ring
  exact ⟨by rw [h1]; positivity, by rw [h2]; positivity,
    by rw [h3]; positivity⟩

lemma allTrianglesFloor_minTri (v : Configuration7) :
    AllTrianglesFloor v (minTri v) := by
  intro i j k hij hik hjk
  exact minTri_le_of_distinct v i j k hij hik hjk

/-- A single strict interior point divides its containing triangle into three
positive triangles of floor `m`. -/
lemma oneInterior_three {n : ℕ} (w : Fin n → Point) (m : ℝ)
    (e : Fin 4 → Fin n) (he : Function.Injective e)
    (hfloor : AllTrianglesFloor w m)
    (habc : 0 < sig (w (e 0)) (w (e 1)) (w (e 2)))
    (hp : InTriStrict (w (e 3)) (w (e 0)) (w (e 1)) (w (e 2))) :
    3 * m ≤ sig (w (e 0)) (w (e 1)) (w (e 2)) := by
  obtain ⟨hpbc, hpca, hpab⟩ := inTriStrict_fan_pos habc hp
  have h1 := hfloor (e 3) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have h2 := hfloor (e 3) (e 2) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have h3 := hfloor (e 3) (e 0) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rw [abs_of_pos hpbc] at h1
  rw [abs_of_pos hpca] at h2
  rw [abs_of_pos hpab] at h3
  have hfan :
      sig (w (e 3)) (w (e 1)) (w (e 2)) +
        sig (w (e 3)) (w (e 2)) (w (e 0)) +
        sig (w (e 3)) (w (e 0)) (w (e 1)) =
          sig (w (e 0)) (w (e 1)) (w (e 2)) := by
    simp only [sig]
    ring
  linarith

/-! ## Hull four -/

/-- The two triangle inputs close the canonical hull-four field.  The all-on-
one-side branch actually gives `19*m/2`; a mixed branch gives `10*m`. -/
theorem hullFour_of_triangleInputs
    (two : TriangleTwoSeven) (three : TriangleThreeSeventeen) :
    ∀ (v : Configuration7), HullCCW v 4 →
      (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
      9 * minTri v ≤ fanArea v 4 := by
  intro v hccw hin
  rcases eq_or_lt_of_le (minTri_nonneg v) with hzero | hm
  · have h012 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    have h023 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
    rw [← hzero]
    simp only [zero_mul, fanArea]
    linarith
  · let m := minTri v
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
          change 7 * m ≤ sig (v 0) (v 2) (v 3) at h2
          change 3 * m ≤ sig (v 0) (v 1) (v 2) at h1
          simpa only [fanArea] using (show 9 * m ≤
            sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) by linarith)
      · have d5' : sig (v 0) (v 2) (v 5) < 0 :=
          lt_of_le_of_ne (le_of_not_gt d5) d5ne
        by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
        · have h2 := two v m ![0, 2, 3, 4, 6] (by decide) hm hfloor
            h023 (right4 d4) (right6 d6)
          have h1 := oneInterior_three v m ![0, 1, 2, 5] (by decide)
            hfloor h012 (left5 d5')
          change 7 * m ≤ sig (v 0) (v 2) (v 3) at h2
          change 3 * m ≤ sig (v 0) (v 1) (v 2) at h1
          simpa only [fanArea] using (show 9 * m ≤
            sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) by linarith)
        · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
            lt_of_le_of_ne (le_of_not_gt d6) d6ne
          have h2 := two v m ![0, 1, 2, 5, 6] (by decide) hm hfloor
            h012 (left5 d5') (left6 d6')
          have h1 := oneInterior_three v m ![0, 2, 3, 4] (by decide)
            hfloor h023 (right4 d4)
          change 7 * m ≤ sig (v 0) (v 1) (v 2) at h2
          change 3 * m ≤ sig (v 0) (v 2) (v 3) at h1
          simpa only [fanArea] using (show 9 * m ≤
            sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) by linarith)
    · have d4' : sig (v 0) (v 2) (v 4) < 0 :=
        lt_of_le_of_ne (le_of_not_gt d4) d4ne
      by_cases d5 : 0 < sig (v 0) (v 2) (v 5)
      · by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
        · have h2 := two v m ![0, 2, 3, 5, 6] (by decide) hm hfloor
            h023 (right5 d5) (right6 d6)
          have h1 := oneInterior_three v m ![0, 1, 2, 4] (by decide)
            hfloor h012 (left4 d4')
          change 7 * m ≤ sig (v 0) (v 2) (v 3) at h2
          change 3 * m ≤ sig (v 0) (v 1) (v 2) at h1
          simpa only [fanArea] using (show 9 * m ≤
            sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) by linarith)
        · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
            lt_of_le_of_ne (le_of_not_gt d6) d6ne
          have h2 := two v m ![0, 1, 2, 4, 6] (by decide) hm hfloor
            h012 (left4 d4') (left6 d6')
          have h1 := oneInterior_three v m ![0, 2, 3, 5] (by decide)
            hfloor h023 (right5 d5)
          change 7 * m ≤ sig (v 0) (v 1) (v 2) at h2
          change 3 * m ≤ sig (v 0) (v 2) (v 3) at h1
          simpa only [fanArea] using (show 9 * m ≤
            sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) by linarith)
      · have d5' : sig (v 0) (v 2) (v 5) < 0 :=
          lt_of_le_of_ne (le_of_not_gt d5) d5ne
        by_cases d6 : 0 < sig (v 0) (v 2) (v 6)
        · have h2 := two v m ![0, 1, 2, 4, 5] (by decide) hm hfloor
            h012 (left4 d4') (left5 d5')
          have h1 := oneInterior_three v m ![0, 2, 3, 6] (by decide)
            hfloor h023 (right6 d6)
          change 7 * m ≤ sig (v 0) (v 1) (v 2) at h2
          change 3 * m ≤ sig (v 0) (v 2) (v 3) at h1
          simpa only [fanArea] using (show 9 * m ≤
            sig (v 0) (v 1) (v 2) + sig (v 0) (v 2) (v 3) by linarith)
        · have d6' : sig (v 0) (v 2) (v 6) < 0 :=
            lt_of_le_of_ne (le_of_not_gt d6) d6ne
          have h3 := three v m ![0, 1, 2, 4, 5, 6] (by decide) hm
            hfloor h012 (left4 d4') (left5 d5') (left6 d6')
          change 17 * m ≤ 2 * sig (v 0) (v 1) (v 2) at h3
          simp only [fanArea]
          nlinarith

/-! ## The two-point quadrilateral estimate -/

/-- The four increasing hull triples of a cyclic quadrilateral. -/
def StrictCCWQuad (a b c d : Point) : Prop :=
  0 < sig a b c ∧ 0 < sig a b d ∧
  0 < sig a c d ∧ 0 < sig b c d

/-- In the genuinely crossed diagonal cell, the point on the `DA` side lies
strictly in `PDA`.  This is the only geometric fact needed by the Pluecker
calculation. -/
lemma crossed_opposite_contains {a b c d p q : Point}
    (hccw : StrictCCWQuad a b c d)
    (hp : StrictInQuad p a b c d)
    (hq : StrictInQuad q a b c d)
    (hacp : sig a c p < 0) (hbdp : sig b d p < 0)
    (hacq : 0 < sig a c q) (hbdq : 0 < sig b d q) :
    InTriStrict q p d a := by
  rcases hccw with ⟨habc, habd, hacd, hbcd⟩
  rcases hp with ⟨habp, hbcp, hcdp, hdap⟩
  rcases hq with ⟨habq, hbcq, hcdq, hdaq⟩
  have hdab : 0 < sig d a b :=
    n7_sig_pos_rotate (n7_sig_pos_rotate habd)
  have hqinACD : InTriStrict q a c d :=
    inTriStrict_of_orientations hacd hacq hcdq hdaq
  have hqinDAB : InTriStrict q d a b :=
    inTriStrict_of_orientations hdab hdaq habq hbdq
  have hpda : 0 < sig p d a := by
    rw [n7_sig_rotate p d a]
    exact hdap
  have hpdb : 0 < sig p d b := by
    rw [n7_sig_rotate p d b, n7_sig_reverse b d p]
    linarith
  have hapc : 0 < sig a p c := by
    rw [n7_sig_rotate a p c, n7_sig_rotate p c a,
      n7_sig_reverse a c p]
    linarith
  have hapd : 0 < sig a p d := by
    rw [n7_sig_rotate a p d]
    exact hpda
  obtain ⟨x, y, z, hx, hy, hz, hxyz, hqDAB⟩ := hqinDAB
  have hpdq : 0 < sig p d q := by
    have hid : sig p d q = y * sig p d a + z * sig p d b := by
      rw [hqDAB, n7_sig_affine_third p d d a b x y z hxyz]
      simp only [sig]
      ring
    rw [hid]
    positivity
  obtain ⟨u, v, w, hu, hv, hw, huvw, hqACD⟩ := hqinACD
  have hapq : 0 < sig a p q := by
    have hid : sig a p q = v * sig a p c + w * sig a p d := by
      rw [hqACD, n7_sig_affine_third a p a c d u v w huvw]
      simp only [sig]
      ring
    rw [hid]
    positivity
  exact inTriStrict_of_orientations hpda hpdq hdaq hapq

/-- The exact crossed-cell calculation.  Labels in `e` are
`A,B,C,D,P,Q`.  Its hypotheses spell out the two crossed diagonal signs; the
containment consumed by the `3*m` estimate is proved above, not assumed. -/
lemma crossedQuadEight {n : ℕ} (w : Fin n → Point) (m : ℝ)
    (e : Fin 6 → Fin n) (he : Function.Injective e)
    (hm : 0 < m) (hfloor : AllTrianglesFloor w m)
    (hccw : StrictCCWQuad (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hp : StrictInQuad (w (e 4))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hq : StrictInQuad (w (e 5))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hacp : sig (w (e 0)) (w (e 2)) (w (e 4)) < 0)
    (hbdp : sig (w (e 1)) (w (e 3)) (w (e 4)) < 0)
    (hacq : 0 < sig (w (e 0)) (w (e 2)) (w (e 5)))
    (hbdq : 0 < sig (w (e 1)) (w (e 3)) (w (e 5))) :
    8 * m ≤
      sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3)) := by
  let A := w (e 0)
  let B := w (e 1)
  let C := w (e 2)
  let D := w (e 3)
  let P := w (e 4)
  let Q := w (e 5)
  have hQin : InTriStrict Q P D A :=
    crossed_opposite_contains hccw hp hq hacp hbdp hacq hbdq
  rcases hp with ⟨hABP, hBCP, hCDP, hDAP⟩
  have hPAB : 0 < sig P A B := by
    rw [n7_sig_rotate P A B]
    exact hABP
  have hPBC : 0 < sig P B C := by
    rw [n7_sig_rotate P B C]
    exact hBCP
  have hPCD : 0 < sig P C D := by
    rw [n7_sig_rotate P C D]
    exact hCDP
  have hPDA : 0 < sig P D A := by
    rw [n7_sig_rotate P D A]
    exact hDAP
  have hPCA : 0 < sig P C A := by
    rw [n7_sig_rotate P C A, n7_sig_reverse A C P]
    linarith
  have hPDB : 0 < sig P D B := by
    rw [n7_sig_rotate P D B, n7_sig_reverse B D P]
    linarith
  have hdelta := oneInterior_three w m (e ∘ ![4, 3, 0, 5])
    (he.comp (by decide)) hfloor hPDA hQin
  have hbeta := hfloor (e 4) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hu := hfloor (e 4) (e 2) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hv := hfloor (e 4) (e 3) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rw [abs_of_pos hPBC] at hbeta
  rw [abs_of_pos hPCA] at hu
  rw [abs_of_pos hPDB] at hv
  let alpha := sig P A B
  let beta := sig P B C
  let gamma := sig P C D
  let delta := sig P D A
  let u := sig P C A
  let z := sig P D B
  have hbeta' : m ≤ beta := by
    simpa only [beta, P, B, C] using hbeta
  have hdelta' : 3 * m ≤ delta := by
    change 3 * m ≤ sig P D A at hdelta
    simpa only [delta] using hdelta
  have hprodIdentity : alpha * gamma = beta * delta + u * z := by
    simp only [alpha, beta, gamma, delta, u, z, sig]
    ring
  have hbetadelta : 3 * m ^ 2 ≤ beta * delta := by
    have hbeta0 : 0 ≤ beta := hm.le.trans hbeta'
    have hthree0 : 0 ≤ 3 * m := mul_nonneg (by norm_num) hm.le
    calc
      3 * m ^ 2 = m * (3 * m) := by ring
      _ ≤ beta * (3 * m) :=
        mul_le_mul_of_nonneg_right hbeta' hthree0
      _ ≤ beta * delta :=
        mul_le_mul_of_nonneg_left hdelta' hbeta0
  have huz : m ^ 2 ≤ u * z := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
    dsimp [u, z] at hnonneg ⊢
    nlinarith
  have hprod : 4 * m ^ 2 ≤ alpha * gamma := by
    rw [hprodIdentity]
    linarith
  have halpha : 0 < alpha := hPAB
  have hgamma : 0 < gamma := hPCD
  have halphagamma : 4 * m ≤ alpha + gamma := by
    nlinarith [sq_nonneg (alpha - gamma)]
  have hfan :
      sig (w (e 0)) (w (e 1)) (w (e 2)) +
          sig (w (e 0)) (w (e 2)) (w (e 3)) =
        alpha + beta + gamma + delta := by
    simp only [A, B, C, D, P, alpha, beta, gamma, delta, sig]
    ring
  rw [hfan]
  linarith [hbeta', hdelta']

/-- Two strict interior points in a cyclic quadrilateral force eight minimum
triangles.  A shared diagonal half is `7+1`; when both diagonals separate the
points, `crossedQuadEight` handles one opposite pattern and a cyclic rotation
handles the other. -/
theorem quadrilateralTwoEight (two : TriangleTwoSeven)
    {n : ℕ} (w : Fin n → Point) (m : ℝ) (e : Fin 6 → Fin n)
    (he : Function.Injective e) (hm : 0 < m)
    (hfloor : AllTrianglesFloor w m)
    (hccw : StrictCCWQuad (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hp : StrictInQuad (w (e 4))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hq : StrictInQuad (w (e 5))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3))) :
    8 * m ≤
      sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3)) := by
  let A := w (e 0)
  let B := w (e 1)
  let C := w (e 2)
  let D := w (e 3)
  let P := w (e 4)
  let Q := w (e 5)
  rcases hccw with ⟨hABC, hABD, hACD, hBCD⟩
  rcases hp with ⟨hABP, hBCP, hCDP, hDAP⟩
  rcases hq with ⟨hABQ, hBCQ, hCDQ, hDAQ⟩
  have hABCfloor := hfloor (e 0) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hACDfloor := hfloor (e 0) (e 2) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hBCDfloor := hfloor (e 1) (e 2) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hDAB : 0 < sig D A B :=
    n7_sig_pos_rotate (n7_sig_pos_rotate hABD)
  have hDABfloor := hfloor (e 3) (e 0) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rw [abs_of_pos hABC] at hABCfloor
  rw [abs_of_pos hACD] at hACDfloor
  rw [abs_of_pos hBCD] at hBCDfloor
  rw [abs_of_pos hDAB] at hDABfloor
  have hdiagSum : sig A B C + sig A C D = sig B C D + sig D A B := by
    simp only [A, B, C, D, sig]
    ring
  have acPfloor := hfloor (e 0) (e 2) (e 4)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have acQfloor := hfloor (e 0) (e 2) (e 5)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have bdPfloor := hfloor (e 1) (e 3) (e 4)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have bdQfloor := hfloor (e 1) (e 3) (e 5)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have acPne : sig A C P ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at acPfloor
    linarith
  have acQne : sig A C Q ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at acQfloor
    linarith
  have bdPne : sig B D P ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at bdPfloor
    linarith
  have bdQne : sig B D Q ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at bdQfloor
    linarith
  by_cases acP : 0 < sig A C P
  · by_cases acQ : 0 < sig A C Q
    · have pACD := inTriStrict_of_orientations hACD acP hCDP hDAP
      have qACD := inTriStrict_of_orientations hACD acQ hCDQ hDAQ
      have ht := two w m (e ∘ ![0, 2, 3, 4, 5])
        (he.comp (by decide)) hm hfloor hACD pACD qACD
      change 7 * m ≤ sig A C D at ht
      change 8 * m ≤ sig A B C + sig A C D
      linarith
    · have acQ' : sig A C Q < 0 :=
        lt_of_le_of_ne (le_of_not_gt acQ) acQne
      by_cases bdP : 0 < sig B D P
      · by_cases bdQ : 0 < sig B D Q
        · have pDAB := inTriStrict_of_orientations hDAB hDAP hABP bdP
          have qDAB := inTriStrict_of_orientations hDAB hDAQ hABQ bdQ
          have ht := two w m (e ∘ ![3, 0, 1, 4, 5])
            (he.comp (by decide)) hm hfloor hDAB pDAB qDAB
          change 7 * m ≤ sig D A B at ht
          change 8 * m ≤ sig A B C + sig A C D
          linarith
        · have bdQ' : sig B D Q < 0 :=
              lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          exact crossedQuadEight w m (e ∘ ![0, 1, 2, 3, 5, 4])
            (he.comp (by decide)) hm hfloor
            ⟨hABC, hABD, hACD, hBCD⟩
            ⟨hABQ, hBCQ, hCDQ, hDAQ⟩
            ⟨hABP, hBCP, hCDP, hDAP⟩
            acQ' bdQ' acP bdP
      · have bdP' : sig B D P < 0 :=
            lt_of_le_of_ne (le_of_not_gt bdP) bdPne
        by_cases bdQ : 0 < sig B D Q
        · have hrotCCW : StrictCCWQuad B C D A := by
            exact ⟨hBCD,
              by rw [← n7_sig_rotate A B C]; exact hABC,
              by rw [← n7_sig_rotate A B D]; exact hABD,
              by rw [← n7_sig_rotate A C D]; exact hACD⟩
          have hrotP : StrictInQuad P B C D A :=
            ⟨hBCP, hCDP, hDAP, hABP⟩
          have hrotQ : StrictInQuad Q B C D A :=
            ⟨hBCQ, hCDQ, hDAQ, hABQ⟩
          have hc := crossedQuadEight w m (e ∘ ![1, 2, 3, 0, 4, 5])
            (he.comp (by decide)) hm hfloor hrotCCW hrotP hrotQ
            bdP' (by
              change sig C A P < 0
              rw [n7_sig_reverse]
              linarith [acP]) bdQ
            (by
              change 0 < sig C A Q
              rw [n7_sig_reverse]
              linarith [acQ'])
          change 8 * m ≤ sig A B C + sig A C D
          have hid : sig B C D + sig B D A = sig A B C + sig A C D := by
            simp only [A, B, C, D, sig]
            ring
          norm_num at hc
          change 8 * m ≤ sig B C D + sig B D A at hc
          exact hc.trans_eq hid
        · have bdQ' : sig B D Q < 0 :=
              lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          have pBCD := inTriStrict_of_orientations hBCD hBCP hCDP
            (by rw [n7_sig_reverse]; linarith)
          have qBCD := inTriStrict_of_orientations hBCD hBCQ hCDQ
            (by rw [n7_sig_reverse]; linarith)
          have ht := two w m (e ∘ ![1, 2, 3, 4, 5])
            (he.comp (by decide)) hm hfloor hBCD pBCD qBCD
          change 7 * m ≤ sig B C D at ht
          change 8 * m ≤ sig A B C + sig A C D
          linarith
  · have acP' : sig A C P < 0 :=
      lt_of_le_of_ne (le_of_not_gt acP) acPne
    by_cases acQ : 0 < sig A C Q
    · by_cases bdP : 0 < sig B D P
      · by_cases bdQ : 0 < sig B D Q
        · have pDAB := inTriStrict_of_orientations hDAB hDAP hABP bdP
          have qDAB := inTriStrict_of_orientations hDAB hDAQ hABQ bdQ
          have ht := two w m (e ∘ ![3, 0, 1, 4, 5])
            (he.comp (by decide)) hm hfloor hDAB pDAB qDAB
          change 7 * m ≤ sig D A B at ht
          change 8 * m ≤ sig A B C + sig A C D
          linarith
        · have bdQ' : sig B D Q < 0 :=
              lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          have hrotCCW : StrictCCWQuad B C D A := by
            exact ⟨hBCD,
              by rw [← n7_sig_rotate A B C]; exact hABC,
              by rw [← n7_sig_rotate A B D]; exact hABD,
              by rw [← n7_sig_rotate A C D]; exact hACD⟩
          have hrotP : StrictInQuad P B C D A :=
            ⟨hBCP, hCDP, hDAP, hABP⟩
          have hrotQ : StrictInQuad Q B C D A :=
            ⟨hBCQ, hCDQ, hDAQ, hABQ⟩
          have hc := crossedQuadEight w m (e ∘ ![1, 2, 3, 0, 5, 4])
            (he.comp (by decide)) hm hfloor hrotCCW hrotQ hrotP
            bdQ' (by
              change sig C A Q < 0
              rw [n7_sig_reverse]
              linarith [acQ]) bdP
            (by
              change 0 < sig C A P
              rw [n7_sig_reverse]
              linarith [acP'])
          change 8 * m ≤ sig A B C + sig A C D
          have hid : sig B C D + sig B D A = sig A B C + sig A C D := by
            simp only [A, B, C, D, sig]
            ring
          norm_num at hc
          change 8 * m ≤ sig B C D + sig B D A at hc
          exact hc.trans_eq hid
      · have bdP' : sig B D P < 0 :=
            lt_of_le_of_ne (le_of_not_gt bdP) bdPne
        by_cases bdQ : 0 < sig B D Q
        · exact crossedQuadEight w m e he hm hfloor
              ⟨hABC, hABD, hACD, hBCD⟩
              ⟨hABP, hBCP, hCDP, hDAP⟩
              ⟨hABQ, hBCQ, hCDQ, hDAQ⟩
              acP' bdP' acQ bdQ
        · have bdQ' : sig B D Q < 0 :=
              lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          have pBCD := inTriStrict_of_orientations hBCD hBCP hCDP
            (by rw [n7_sig_reverse]; linarith)
          have qBCD := inTriStrict_of_orientations hBCD hBCQ hCDQ
            (by rw [n7_sig_reverse]; linarith)
          have ht := two w m (e ∘ ![1, 2, 3, 4, 5])
            (he.comp (by decide)) hm hfloor hBCD pBCD qBCD
          change 7 * m ≤ sig B C D at ht
          change 8 * m ≤ sig A B C + sig A C D
          linarith
    · have acQ' : sig A C Q < 0 :=
          lt_of_le_of_ne (le_of_not_gt acQ) acQne
      have pABC := inTriStrict_of_orientations hABC hABP hBCP
        (by rw [n7_sig_reverse]; linarith)
      have qABC := inTriStrict_of_orientations hABC hABQ hBCQ
        (by rw [n7_sig_reverse]; linarith)
      have ht := two w m (e ∘ ![0, 1, 2, 4, 5])
        (he.comp (by decide)) hm hfloor hABC pABC qABC
      change 7 * m ≤ sig A B C at ht
      change 8 * m ≤ sig A B C + sig A C D
      linarith

end HeilbronnChallenge.N7Upper

