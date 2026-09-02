import Heilbronn8.TriHull.Main

/-!
# The opposite-cell `2 + 1` quadrilateral estimate

This is the compact hull-five estimate for the following local picture.
The selected quadrilateral is `A-B-X-C`, the triangle `ABC` is maximal,
two selected points lie in `RAB`, and `R` lies in `BXC`.  In the usual
diagonal-sector description, the first two points lie in `ABO` and `R`
lies in the opposite cell `XCO`; the displayed containments are the direct
strict-triangle consequences consumed here.

All areas are doubled.  The proof uses one Grassmann-Plucker identity and
the existing two-interior-point triangle estimate.  In particular, it has
no finite certificate payload.
-/

namespace Heilbronn8.TriHull

/-- Strict membership in the relative interior of a segment. -/
def InSegStrict (P A B : Point) : Prop :=
  ∃ x y : ℝ,
    0 < x ∧ 0 < y ∧ x + y = 1 ∧ P = x • A + y • B

/-- Strict segment membership is symmetric in its endpoints. -/
lemma inSegStrict_symm {P A B : Point}
    (hP : InSegStrict P A B) : InSegStrict P B A := by
  obtain ⟨x, y, hx, hy, hxy, hPe⟩ := hP
  refine ⟨y, x, hy, hx, by linarith, ?_⟩
  rw [hPe]
  module

/-- Substituting a strict interior point for the third triangle vertex. -/
lemma inTriStrict_replace_third
    {P A B O R : Point}
    (hP : InTriStrict P A B O)
    (hO : InTriStrict O R A B) :
    InTriStrict P R A B := by
  obtain ⟨p, q, t, hp, hq, ht, hpqt, hPe⟩ := hP
  obtain ⟨u, v, w, hu, hv, hw, huv, hOe⟩ := hO
  refine ⟨t * u, p + t * v, q + t * w,
    mul_pos ht hu, add_pos hp (mul_pos ht hv),
    add_pos hq (mul_pos ht hw), ?_, ?_⟩
  · have htu : t * (u + v + w) = t := by rw [huv]; ring
    nlinarith
  · rw [hPe, hOe]
    module

/-- A strict triangle remains strict when a segment-interior endpoint is
expanded into the two endpoints of that segment. -/
lemma inTriStrict_replace_third_segment
    {R X C O B : Point}
    (hR : InTriStrict R X C O)
    (hO : InSegStrict O B C) :
    InTriStrict R B X C := by
  obtain ⟨u, v, w, hu, hv, hw, huv, hRe⟩ := hR
  obtain ⟨b, c, hb, hc, hbc, hOe⟩ := hO
  refine ⟨w * b, u, v + w * c,
    mul_pos hw hb, hu, add_pos hv (mul_pos hw hc), ?_, ?_⟩
  · have hwbc : w * (b + c) = w := by rw [hbc]; ring
    nlinarith
  · rw [hRe, hOe]
    module

/-- The reflected segment expansion used by the `CAO/BXO` opposite cells. -/
lemma inTriStrict_replace_third_segment_reflected
    {R B X O C : Point}
    (hR : InTriStrict R B X O)
    (hO : InSegStrict O B C) :
    InTriStrict R B X C := by
  obtain ⟨u, v, w, hu, hv, hw, huv, hRe⟩ := hR
  obtain ⟨b, c, hb, hc, hbc, hOe⟩ := hO
  refine ⟨u + w * b, v, w * c,
    add_pos hu (mul_pos hw hb), hv, mul_pos hw hc, ?_, ?_⟩
  · have hwbc : w * (b + c) = w := by rw [hbc]; ring
    nlinarith
  · rw [hRe, hOe]
    module

/--
If `O` is the strict intersection of `AX` and `BC`, then a point of the
opposite sector `XCO` puts `O` strictly inside `RAB`.
-/
lemma diagonalIntersection_in_opposite_triangle
    {A B X C O R : Point}
    (hOAX : InSegStrict O A X)
    (hOBC : InSegStrict O B C)
    (hR : InTriStrict R X C O) :
    InTriStrict O R A B := by
  obtain ⟨a, x, ha, hx, hax, hOAXe⟩ := hOAX
  obtain ⟨b, c, hb, hc, hbc, hOBCe⟩ := hOBC
  obtain ⟨u, v, w, hu, hv, hw, huv, hRe⟩ := hR
  let D : ℝ := u * c + v * x + w * x * c
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos (add_pos (mul_pos hu hc) (mul_pos hv hx))
      (mul_pos (mul_pos hw hx) hc)
  have hnum :
      x * c + u * a * c + v * b * x = D := by
    have ha' : a = 1 - x := by linarith
    have hb' : b = 1 - c := by linarith
    have hw' : w = 1 - u - v := by linarith
    dsimp [D]
    rw [ha', hb', hw']
    ring
  have hxX : x • X = O - a • A := by
    rw [hOAXe]
    module
  have hcC : c • C = O - b • B := by
    rw [hOBCe]
    module
  have hscaled :
      D • O =
        (x * c) • R + (u * a * c) • A + (v * b * x) • B := by
    symm
    calc
      (x * c) • R + (u * a * c) • A + (v * b * x) • B =
          (u * c) • (x • X) + (v * x) • (c • C) +
            (w * x * c) • O + (u * a * c) • A +
            (v * b * x) • B := by
        rw [hRe]
        module
      _ = (u * c) • (O - a • A) +
            (v * x) • (O - b • B) +
            (w * x * c) • O + (u * a * c) • A +
            (v * b * x) • B := by rw [hxX, hcC]
      _ = D • O := by
        dsimp [D]
        module
  refine ⟨x * c / D, u * a * c / D, v * b * x / D,
    div_pos (mul_pos hx hc) hD,
    div_pos (mul_pos (mul_pos hu ha) hc) hD,
    div_pos (mul_pos (mul_pos hv hb) hx) hD, ?_, ?_⟩
  · calc
      x * c / D + u * a * c / D + v * b * x / D =
          (x * c + u * a * c + v * b * x) / D := by ring
      _ = D / D := by rw [hnum]
      _ = 1 := div_self hD.ne'
  · calc
      O = (1 / D) • (D • O) := by
        simp [smul_smul, hD.ne']
      _ = (1 / D) •
          ((x * c) • R + (u * a * c) • A + (v * b * x) • B) := by
        rw [hscaled]
      _ = (x * c / D) • R + (u * a * c / D) • A +
          (v * b * x / D) • B := by
        module

/--
The reflected opposite-sector fact: a point of `BXO` puts the diagonal
intersection strictly inside `RCA`.
-/
lemma diagonalIntersection_in_opposite_triangle_reflected
    {A B X C O R : Point}
    (hOAX : InSegStrict O A X)
    (hOBC : InSegStrict O B C)
    (hR : InTriStrict R B X O) :
    InTriStrict O R C A := by
  exact diagonalIntersection_in_opposite_triangle
    (A := C) (B := A) (X := B) (C := X)
    (inSegStrict_symm hOBC) hOAX hR

/-- The complete barycentric adapter from the three raw diagonal sectors. -/
lemma hullFive_opposite_sector_containments
    {A B X C O P Q R : Point}
    (hOAX : InSegStrict O A X)
    (hOBC : InSegStrict O B C)
    (hP : InTriStrict P A B O)
    (hQ : InTriStrict Q A B O)
    (hR : InTriStrict R X C O) :
    InTriStrict P R A B ∧
      InTriStrict Q R A B ∧
      InTriStrict R B X C := by
  have hORAB := diagonalIntersection_in_opposite_triangle hOAX hOBC hR
  exact ⟨inTriStrict_replace_third hP hORAB,
    inTriStrict_replace_third hQ hORAB,
    inTriStrict_replace_third_segment hR hOBC⟩

/-- The complete barycentric adapter for the reflected `CAO/BXO` sectors. -/
lemma hullFive_opposite_sector_containments_reflected
    {A B X C O P Q R : Point}
    (hOAX : InSegStrict O A X)
    (hOBC : InSegStrict O B C)
    (hP : InTriStrict P C A O)
    (hQ : InTriStrict Q C A O)
    (hR : InTriStrict R B X O) :
    InTriStrict P R C A ∧
      InTriStrict Q R C A ∧
      InTriStrict R B X C := by
  have hORCA :=
    diagonalIntersection_in_opposite_triangle_reflected hOAX hOBC hR
  exact ⟨inTriStrict_replace_third hP hORCA,
    inTriStrict_replace_third hQ hORCA,
    inTriStrict_replace_third_segment_reflected hR hOBC⟩

/-- The five-point product identity behind the opposite-cell estimate. -/
lemma hullFive_opposite_product_identity (A B X C R : Point) :
    sig B X C * sig A B C =
      sig B X C * sig R A B +
      sig A B C * sig R X C +
      (sig A B C - sig A B X) * sig B R C := by
  simp only [sig]
  ring

/-- The product identity with the opposite cells reflected across the axes. -/
lemma hullFive_opposite_product_identity_reflected (A B X C R : Point) :
    sig B X C * sig A B C =
      sig B X C * sig R C A +
      sig A B C * sig R B X +
      (sig A B C - sig A X C) * sig B R C := by
  simp only [sig]
  ring

/-- A square-root-free scalar finish for the product estimate. -/
lemma hullFive_product_gap_forces_sum
    {T E alpha gamma : ℝ}
    (hT : 0 < T) (hE : 0 < E)
    (halpha : 12 < alpha) (hgamma : 2 ≤ gamma)
    (hproduct : E * alpha + T * gamma ≤ E * T) :
    23 < T + E := by
  have hmain : 12 * E + 2 * T < E * T := by
    have hEalpha : 12 * E < E * alpha :=
      by simpa [mul_comm] using mul_lt_mul_of_pos_left halpha hE
    have hTgamma : 2 * T ≤ T * gamma :=
      by simpa [mul_comm] using mul_le_mul_of_nonneg_left hgamma hT.le
    nlinarith
  have hTwelve : 12 < T := by
    by_contra h
    have hle : T ≤ 12 := le_of_not_gt h
    have hmul : E * T ≤ E * 12 :=
      mul_le_mul_of_nonneg_left hle hE.le
    nlinarith
  have hTwo : 2 < E := by
    by_contra h
    have hle : E ≤ 2 := le_of_not_gt h
    have hmul : T * E ≤ T * 2 :=
      mul_le_mul_of_nonneg_left hle hT.le
    nlinarith
  let x : ℝ := T - 12
  let y : ℝ := E - 2
  have hx : 0 < x := by
    dsimp [x]
    linarith
  have hy : 0 < y := by
    dsimp [y]
    linarith
  have hxy : 24 < x * y := by
    dsimp [x, y]
    nlinarith
  by_contra hsum
  have hsum_le : x + y ≤ 9 := by
    dsimp [x, y]
    linarith [le_of_not_gt hsum]
  have hminus : 0 ≤ 9 - (x + y) := by linarith
  have hplus : 0 ≤ 9 + (x + y) := by linarith
  have hupper :
      0 ≤ (9 - (x + y)) * (9 + (x + y)) :=
    mul_nonneg hminus hplus
  have hsquare := sq_nonneg (x - y)
  nlinarith

/--
The normalized opposite-cell `2 + 1` estimate.

The labels supplied by `e` are, in order, `A,B,X,C,P,Q,R`.  The two
strict `RAB` memberships and the strict `BXC` membership are precisely the
containment facts produced by the opposite diagonal sectors.  Maximality of
`ABC` is used only through its comparison with the selected triangle `ABX`.
-/
theorem hullFive_opposite_cell_210
    (v : Fin 8 → Point) (e : Fin 7 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABCmaxABX :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hRAB : 0 < sig (v (e 6)) (v (e 0)) (v (e 1)))
    (hP : InTriStrict (v (e 4)) (v (e 6)) (v (e 0)) (v (e 1)))
    (hQ : InTriStrict (v (e 5)) (v (e 6)) (v (e 0)) (v (e 1)))
    (hR : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3))) :
    23 < sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  have hfloor : 2 ≤ minTri v := by
    apply le_minTri
    intro i j k hij hjk
    exact hmin (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk))
      (ne_of_lt hjk)
  have hm : 0 < minTri v := lt_of_lt_of_le (by norm_num) hfloor

  let f : Fin 5 → Fin 8 := e ∘ ![6, 0, 1, 4, 5]
  have hf : Function.Injective f := he.comp (by decide)
  have htwo := twoPointTriangle_normalized_lower_bound
    v f hf hm (by simpa [f] using hRAB)
      (by simpa [f] using hP) (by simpa [f] using hQ)
  have hsqrt : (1 : ℝ) < Real.sqrt 3 := by
    exact lt_trans (by norm_num : (1 : ℝ) < 69 / 40)
      sixty_nine_fortieths_lt_sqrt_three
  have hcoef : (6 : ℝ) < 4 + 2 * Real.sqrt 3 := by
    nlinarith
  have hscaled :
      (12 : ℝ) < (4 + 2 * Real.sqrt 3) * minTri v := by
    have hleft : (12 : ℝ) ≤ 6 * minTri v := by nlinarith
    have hright :
        6 * minTri v < (4 + 2 * Real.sqrt 3) * minTri v :=
      mul_lt_mul_of_pos_right hcoef hm
    exact lt_of_le_of_lt hleft hright
  have halpha :
      (12 : ℝ) < sig (v (e 6)) (v (e 0)) (v (e 1)) := by
    have hmul := (le_div_iff₀ hm).mp htwo
    exact lt_of_lt_of_le hscaled hmul

  obtain ⟨hgamma_pos, hRCB, _hRBX⟩ :=
    inTriStrict_fan_pos hBXC hR
  have hzeta : 0 < sig (v (e 1)) (v (e 6)) (v (e 3)) := by
    rw [sig_rotate (v (e 1)) (v (e 6)) (v (e 3))]
    exact hRCB
  have hlocal : AllTrianglesMinAreaOne (v ∘ e) := hmin.comp e he
  have hgamma_min := hlocal (i := 6) (j := 2) (k := 3)
    (by decide) (by decide) (by decide)
  change 2 ≤ |sig (v (e 6)) (v (e 2)) (v (e 3))| at hgamma_min
  rw [abs_of_pos hgamma_pos] at hgamma_min

  have hid := hullFive_opposite_product_identity
    (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3)) (v (e 6))
  have hremainder :
      0 ≤
        (sig (v (e 0)) (v (e 1)) (v (e 3)) -
          sig (v (e 0)) (v (e 1)) (v (e 2))) *
        sig (v (e 1)) (v (e 6)) (v (e 3)) :=
    mul_nonneg (sub_nonneg.mpr hABCmaxABX) hzeta.le
  have hproduct :
      sig (v (e 1)) (v (e 2)) (v (e 3)) *
          sig (v (e 6)) (v (e 0)) (v (e 1)) +
        sig (v (e 0)) (v (e 1)) (v (e 3)) *
          sig (v (e 6)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 1)) (v (e 2)) (v (e 3)) *
          sig (v (e 0)) (v (e 1)) (v (e 3)) := by
    nlinarith [hid, hremainder]
  exact hullFive_product_gap_forces_sum
    hABC hBXC halpha hgamma_min hproduct

/--
The reflected normalized opposite-cell estimate.  Here `P,Q` lie in
`RCA`, `R` lies in `BXC`, and maximality is used in the sound direction
`AXC ≤ ABC`.
-/
theorem hullFive_opposite_cell_210_reflected
    (v : Fin 8 → Point) (e : Fin 7 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABCmaxAXC :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hRCA : 0 < sig (v (e 6)) (v (e 3)) (v (e 0)))
    (hP : InTriStrict (v (e 4)) (v (e 6)) (v (e 3)) (v (e 0)))
    (hQ : InTriStrict (v (e 5)) (v (e 6)) (v (e 3)) (v (e 0)))
    (hR : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3))) :
    23 < sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  have hfloor : 2 ≤ minTri v := by
    apply le_minTri
    intro i j k hij hjk
    exact hmin (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk))
      (ne_of_lt hjk)
  have hm : 0 < minTri v := lt_of_lt_of_le (by norm_num) hfloor

  let f : Fin 5 → Fin 8 := e ∘ ![6, 3, 0, 4, 5]
  have hf : Function.Injective f := he.comp (by decide)
  have htwo := twoPointTriangle_normalized_lower_bound
    v f hf hm (by simpa [f] using hRCA)
      (by simpa [f] using hP) (by simpa [f] using hQ)
  have hsqrt : (1 : ℝ) < Real.sqrt 3 := by
    exact lt_trans (by norm_num : (1 : ℝ) < 69 / 40)
      sixty_nine_fortieths_lt_sqrt_three
  have hcoef : (6 : ℝ) < 4 + 2 * Real.sqrt 3 := by
    nlinarith
  have hscaled :
      (12 : ℝ) < (4 + 2 * Real.sqrt 3) * minTri v := by
    have hleft : (12 : ℝ) ≤ 6 * minTri v := by nlinarith
    have hright :
        6 * minTri v < (4 + 2 * Real.sqrt 3) * minTri v :=
      mul_lt_mul_of_pos_right hcoef hm
    exact lt_of_le_of_lt hleft hright
  have halpha :
      (12 : ℝ) < sig (v (e 6)) (v (e 3)) (v (e 0)) := by
    have hmul := (le_div_iff₀ hm).mp htwo
    exact lt_of_lt_of_le hscaled hmul

  obtain ⟨_hRXC, hRCB, hgamma_pos⟩ :=
    inTriStrict_fan_pos hBXC hR
  have hzeta : 0 < sig (v (e 1)) (v (e 6)) (v (e 3)) := by
    rw [sig_rotate (v (e 1)) (v (e 6)) (v (e 3))]
    exact hRCB
  have hlocal : AllTrianglesMinAreaOne (v ∘ e) := hmin.comp e he
  have hgamma_min := hlocal (i := 6) (j := 1) (k := 2)
    (by decide) (by decide) (by decide)
  change 2 ≤ |sig (v (e 6)) (v (e 1)) (v (e 2))| at hgamma_min
  rw [abs_of_pos hgamma_pos] at hgamma_min

  have hid := hullFive_opposite_product_identity_reflected
    (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3)) (v (e 6))
  have hremainder :
      0 ≤
        (sig (v (e 0)) (v (e 1)) (v (e 3)) -
          sig (v (e 0)) (v (e 2)) (v (e 3))) *
        sig (v (e 1)) (v (e 6)) (v (e 3)) :=
    mul_nonneg (sub_nonneg.mpr hABCmaxAXC) hzeta.le
  have hproduct :
      sig (v (e 1)) (v (e 2)) (v (e 3)) *
          sig (v (e 6)) (v (e 3)) (v (e 0)) +
        sig (v (e 0)) (v (e 1)) (v (e 3)) *
          sig (v (e 6)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 1)) (v (e 2)) (v (e 3)) *
          sig (v (e 0)) (v (e 1)) (v (e 3)) := by
    nlinarith [hid, hremainder]
  exact hullFive_product_gap_forces_sum
    hABC hBXC halpha hgamma_min hproduct

/--
The same estimate with the raw diagonal-sector hypotheses.  The labels are
again `A,B,X,C,P,Q,R`; `O` is the strict intersection of `AX` and `BC`.
-/
theorem hullFive_opposite_diagonal_cells_210
    (v : Fin 8 → Point) (e : Fin 7 → Fin 8) (O : Point)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABCmaxABX :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hRAB : 0 < sig (v (e 6)) (v (e 0)) (v (e 1)))
    (hOAX : InSegStrict O (v (e 0)) (v (e 2)))
    (hOBC : InSegStrict O (v (e 1)) (v (e 3)))
    (hP : InTriStrict (v (e 4)) (v (e 0)) (v (e 1)) O)
    (hQ : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) O)
    (hR : InTriStrict (v (e 6)) (v (e 2)) (v (e 3)) O) :
    23 < sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  obtain ⟨hP', hQ', hR'⟩ :=
    hullFive_opposite_sector_containments hOAX hOBC hP hQ hR
  exact hullFive_opposite_cell_210 v e he hmin hABC hBXC
    hABCmaxABX hRAB hP' hQ' hR'

/--
The reflected estimate from raw diagonal sectors: `P,Q ∈ CAO` and
`R ∈ BXO`.  This is deliberately separate from the unreflected theorem,
because only the comparison `AXC ≤ ABC` has the required sign.
-/
theorem hullFive_opposite_diagonal_cells_210_reflected
    (v : Fin 8 → Point) (e : Fin 7 → Fin 8) (O : Point)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABCmaxAXC :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hRCA : 0 < sig (v (e 6)) (v (e 3)) (v (e 0)))
    (hOAX : InSegStrict O (v (e 0)) (v (e 2)))
    (hOBC : InSegStrict O (v (e 1)) (v (e 3)))
    (hP : InTriStrict (v (e 4)) (v (e 3)) (v (e 0)) O)
    (hQ : InTriStrict (v (e 5)) (v (e 3)) (v (e 0)) O)
    (hR : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) O) :
    23 < sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  obtain ⟨hP', hQ', hR'⟩ :=
    hullFive_opposite_sector_containments_reflected hOAX hOBC hP hQ hR
  exact hullFive_opposite_cell_210_reflected v e he hmin hABC hBXC
    hABCmaxAXC hRCA hP' hQ' hR'

end Heilbronn8.TriHull
