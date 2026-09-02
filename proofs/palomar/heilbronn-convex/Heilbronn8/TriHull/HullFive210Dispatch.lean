import Heilbronn8.TriHull.HullFive300
import Heilbronn8.TriHull.HullFiveOpposite
import Heilbronn8.TriHull.HullFiveSingleton

/-!
# The hull-five mixed `2 + 1` dispatch seam

This module contains the geometry adapter for the three-sector branch of a
mixed `2 + 1` diagonal split.  In the quadrilateral `A-B-X-C`, the selected
points occupy the strict cells `ABO`, `ACO`, and `XCO`: equivalently,

* `P` lies in both `ABC` and `ABX`;
* `R` lies in both `ABC` and `AXC`;
* `Q` lies in both `AXC` and `BXC`.

The two fan disjunctions required by `hullFive_singleton_fan_cells_210` are
not extra sign assumptions.  They follow from `strict_fan_partition`; its
common `RCA` outcome is excluded for `P` by the diagonal `AX`, and for `Q`
by the diagonal `BC`.

A single diagonal having occupancy `2 + 1` does not imply an
opposite-or-singleton dichotomy: the other diagonal can have occupancy
`3 + 0`.  The two membership-only outer dispatchers at the end of this
module therefore return that genuine third branch as `HullFive300Cell`.
-/

namespace Heilbronn8.TriHull

/-- A point in the strict interior of a segment does not create a new
collinearity with a point off the supporting line. -/
lemma inSegStrict_left_sig_ne
    {O A B P : Point}
    (hO : InSegStrict O A B) (hABP : sig A B P ≠ 0) :
    sig A O P ≠ 0 := by
  obtain ⟨x, y, hx, hy, hxy, hOe⟩ := hO
  have hid : sig A O P = y * sig A B P := by
    rw [hOe]
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul]
    have hx' : x = 1 - y := by linarith
    rw [hx']
    ring
  rw [hid]
  exact mul_ne_zero hy.ne' hABP

/-- The two diagonals of a strictly oriented quadrilateral meet in their
relative interiors.  This explicit affine construction keeps downstream
dispatchers independent of an externally supplied intersection witness. -/
theorem strictQuad_diagonal_intersection
    {A B X C : Point}
    (hABC : 0 < sig A B C) (hBXC : 0 < sig B X C)
    (hABX : 0 < sig A B X) (hAXC : 0 < sig A X C) :
    ∃ O : Point, InSegStrict O A X ∧ InSegStrict O B C := by
  let T : ℝ := sig A B C
  let E : ℝ := sig B X C
  let U : ℝ := sig A B X
  let V : ℝ := sig A X C
  let S : ℝ := T + E
  let O : Point := (E / S) • A + (T / S) • X
  have hT : 0 < T := by simpa [T] using hABC
  have hE : 0 < E := by simpa [E] using hBXC
  have hU : 0 < U := by simpa [U] using hABX
  have hV : 0 < V := by simpa [V] using hAXC
  have hS : 0 < S := by dsimp [S]; positivity
  have hsum : T + E = U + V := by
    simpa [T, E, U, V] using
      hullFive_singleton_quadrilateral_sum A B X C
  have hvector : E • A + T • X = V • B + U • C := by
    dsimp [T, E, U, V]
    apply Prod.ext <;>
      simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
        Prod.snd_add, smul_eq_mul] <;> ring
  refine ⟨O, ?_, ?_⟩
  · refine ⟨E / S, T / S, div_pos hE hS, div_pos hT hS, ?_, rfl⟩
    field_simp [hS.ne']
    dsimp [S]
    ring
  · refine ⟨V / S, U / S, div_pos hV hS, div_pos hU hS, ?_, ?_⟩
    · calc
        V / S + U / S = (U + V) / S := by ring
        _ = (T + E) / S := by rw [hsum]
        _ = 1 := by dsimp [S]; field_simp [hS.ne']
    · dsimp [O]
      calc
        (E / S) • A + (T / S) • X =
            (1 / S) • (E • A + T • X) := by module
        _ = (1 / S) • (V • B + U • C) := by rw [hvector]
        _ = (V / S) • B + (U / S) • C := by module

/-- Splitting a strict triangle through a strict point of the opposite edge.
The noncollinearity hypothesis excludes the separating segment itself. -/
lemma inTriStrict_split_through_edge
    {P A B X O : Point}
    (hP : InTriStrict P A B X)
    (hO : InSegStrict O A X)
    (hne : sig B O P ≠ 0) :
    InTriStrict P A B O ∨ InTriStrict P B X O := by
  obtain ⟨p, q, r, hp, hq, hr, hpqr, hPe⟩ := hP
  obtain ⟨a, x, ha, hx, hax, hOe⟩ := hO
  have hseparator : p * x ≠ r * a := by
    intro heq
    apply hne
    have hid : sig B O P = (a * r - x * p) * sig B A X := by
      have ha' : a = 1 - x := by linarith
      have hr' : r = 1 - p - q := by linarith
      rw [hOe, hPe, ha', hr']
      simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
        Prod.snd_add, smul_eq_mul]
      ring
    rw [hid]
    have : a * r - x * p = 0 := by nlinarith
    rw [this, zero_mul]
  rcases lt_or_gt_of_ne hseparator with hlt | hgt
  · right
    have hmiddle : 0 < r - p * x / a := by
      rw [sub_pos, div_lt_iff₀ ha]
      nlinarith
    refine ⟨q, r - p * x / a, p / a,
      hq, hmiddle, div_pos hp ha, ?_, ?_⟩
    · calc
        q + (r - p * x / a) + p / a =
            q + r + p * ((1 - x) / a) := by ring
        _ = q + r + p * (a / a) := by rw [show 1 - x = a by linarith]
        _ = 1 := by rw [div_self ha.ne', mul_one]; linarith
    · rw [hPe, hOe]
      symm
      have hA : (p / a) * a = p := div_mul_cancel₀ p ha.ne'
      have hX : r - p * x / a + (p / a) * x = r := by ring
      calc
        q • B + (r - p * x / a) • X +
              (p / a) • (a • A + x • X) =
            ((p / a) * a) • A + q • B +
              (r - p * x / a + (p / a) * x) • X := by module
        _ = p • A + q • B + r • X := by rw [hA, hX]
  · left
    have hfirst : 0 < p - r * a / x := by
      rw [sub_pos, div_lt_iff₀ hx]
      nlinarith
    refine ⟨p - r * a / x, q, r / x,
      hfirst, hq, div_pos hr hx, ?_, ?_⟩
    · calc
        (p - r * a / x) + q + r / x =
            p + q + r * ((1 - a) / x) := by ring
        _ = p + q + r * (x / x) := by rw [show 1 - a = x by linarith]
        _ = 1 := by rw [div_self hx.ne', mul_one]; linarith
    · rw [hPe, hOe]
      symm
      have hA : p - r * a / x + (r / x) * a = p := by ring
      have hX : (r / x) * x = r := div_mul_cancel₀ r hx.ne'
      calc
        (p - r * a / x) • A + q • B +
              (r / x) • (a • A + x • X) =
            (p - r * a / x + (r / x) * a) • A + q • B +
              ((r / x) * x) • X := by module
        _ = p • A + q • B + r • X := by rw [hA, hX]

/-- If the double cell of a mixed `2 + 1` pattern lies in the right ear
`BXC`, the two-point triangle estimate is already stronger than the desired
quadrilateral bound.  Keeping the comparison against the original maximal
triangle `ABC` avoids needing the additional quadrilateral-sum transfer used
by the equally sound cyclic-relabelling route through the opposite endpoint.

Labels supplied by `e` are `A,B,X,C,P,Q = 0,1,2,3,4,5`.
-/
theorem hullFive_two_in_right_ear_210
    (v : Fin 8 → Point) (e : Fin 6 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hBXCmax :
      sig (v (e 1)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hP : InTriStrict (v (e 4))
      (v (e 1)) (v (e 2)) (v (e 3)))
    (hQ : InTriStrict (v (e 5))
      (v (e 1)) (v (e 2)) (v (e 3))) :
    23 < sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  have hfloor : 2 ≤ minTri v := by
    apply le_minTri
    intro i j k hij hjk
    exact hmin (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk))
      (ne_of_lt hjk)
  have hm : 0 < minTri v := lt_of_lt_of_le (by norm_num) hfloor

  let f : Fin 5 → Fin 8 := e ∘ ![1, 2, 3, 4, 5]
  have hf : Function.Injective f := he.comp (by decide)
  have htwo := twoPointTriangle_normalized_lower_bound
    v f hf hm (by simpa [f] using hBXC)
      (by simpa [f] using hP) (by simpa [f] using hQ)
  have hscaled :
      (4 + 2 * Real.sqrt 3) * minTri v ≤
        sig (v (e 1)) (v (e 2)) (v (e 3)) :=
    (le_div_iff₀ hm).mp htwo
  have hsqrt : (1 : ℝ) < Real.sqrt 3 := by
    exact lt_trans (by norm_num : (1 : ℝ) < 69 / 40)
      sixty_nine_fortieths_lt_sqrt_three
  have hcoef : 0 ≤ (4 + 2 * Real.sqrt 3 : ℝ) := by positivity
  have hmul :
      (4 + 2 * Real.sqrt 3) * 2 ≤
        (4 + 2 * Real.sqrt 3) * minTri v :=
    mul_le_mul_of_nonneg_left hfloor hcoef
  have hBright :
      12 < sig (v (e 1)) (v (e 2)) (v (e 3)) := by
    nlinarith [hmul, hscaled, hsqrt]
  nlinarith

/-- A strict convex combination is strictly on a chosen side of a line when
its first vertex is strictly on that side and its other vertices are weakly
on that side. -/
private lemma inTriStrict_sig_pos_of_first_vertex
    {P U V W L M : Point}
    (hP : InTriStrict P U V W)
    (hU : 0 < sig L M U)
    (hV : 0 ≤ sig L M V)
    (hW : 0 ≤ sig L M W) :
    0 < sig L M P := by
  obtain ⟨x, y, z, hx, hy, hz, hxyz, hPe⟩ := hP
  rw [hPe, sig_affine_thd L M U V W x y z hxyz]
  have hxU : 0 < x * sig L M U := mul_pos hx hU
  have hyV : 0 ≤ y * sig L M V := mul_nonneg hy.le hV
  have hzW : 0 ≤ z * sig L M W := mul_nonneg hz.le hW
  linarith

/-- A strict segment point stays strictly on a half-plane when both
endpoints are weakly on that side and at least one is strictly on it. -/
private lemma inSegStrict_sig_pos_of_sides
    {O A B L M : Point}
    (hO : InSegStrict O A B)
    (hA : 0 ≤ sig L M A) (hB : 0 ≤ sig L M B)
    (hstrict : 0 < sig L M A ∨ 0 < sig L M B) :
    0 < sig L M O := by
  obtain ⟨x, y, hx, hy, hxy, hOe⟩ := hO
  have hid : sig L M O = x * sig L M A + y * sig L M B := by
    rw [hOe]
    simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul]
    have hx' : x = 1 - y := by linarith
    rw [hx']
    ring
  rw [hid]
  rcases hstrict with hA' | hB'
  · have := mul_pos hx hA'
    have := mul_nonneg hy.le hB
    linarith
  · have := mul_nonneg hx.le hA
    have := mul_pos hy hB'
    linarith

private lemma inTriStrict_rotate_dispatch {P A B C : Point}
    (h : InTriStrict P A B C) : InTriStrict P B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := h
  exact ⟨y, z, x, hy, hz, hx, by linarith, by module⟩

private lemma sig_pos_rotate_dispatch {A B C : Point}
    (h : 0 < sig A B C) : 0 < sig B C A := by
  rwa [← sig_rotate A B C]

private lemma cellABO_in_ABC
    {P A B C O : Point}
    (hP : InTriStrict P A B O) (hO : InSegStrict O B C) :
    InTriStrict P A B C := by
  have h := inTriStrict_replace_third_segment
    (R := P) (X := A) (C := B) (B := C)
    hP (inSegStrict_symm hO)
  exact inTriStrict_rotate_dispatch h

private lemma cellBXO_in_BXC
    {P B X C O : Point}
    (hP : InTriStrict P B X O) (hO : InSegStrict O B C) :
    InTriStrict P B X C :=
  inTriStrict_replace_third_segment_reflected hP hO

private lemma cellXCO_in_BXC
    {P B X C O : Point}
    (hP : InTriStrict P X C O) (hO : InSegStrict O B C) :
    InTriStrict P B X C :=
  inTriStrict_replace_third_segment hP hO

private lemma cellCAO_in_ABC
    {P A B C O : Point}
    (hP : InTriStrict P C A O) (hO : InSegStrict O B C) :
    InTriStrict P A B C := by
  have h := inTriStrict_replace_third_segment_reflected
    (R := P) (B := C) (X := A) (C := B)
    hP (inSegStrict_symm hO)
  exact inTriStrict_rotate_dispatch h

/-- The canonical three-sector singleton branch.

Labels are `A,B,X,C,P,Q,R = 0,1,2,3,4,5,6`.  The six membership hypotheses
are the intersection descriptions of the strict diagonal cells `ABO`,
`XCO`, and `ACO`; no determinant involving two of `P,Q,R` is supplied.
-/
theorem hullFive_singleton_three_diagonal_cells_210
    (v : Fin 7 → Point)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v 0) (v 1) (v 3))
    (hBXC : 0 < sig (v 1) (v 2) (v 3))
    (hABX : 0 < sig (v 0) (v 1) (v 2))
    (hAXC : 0 < sig (v 0) (v 2) (v 3))
    (hPABC : InTriStrict (v 4) (v 0) (v 1) (v 3))
    (hPABX : InTriStrict (v 4) (v 0) (v 1) (v 2))
    (hQAXC : InTriStrict (v 5) (v 0) (v 2) (v 3))
    (hQBXC : InTriStrict (v 5) (v 1) (v 2) (v 3))
    (hRABC : InTriStrict (v 6) (v 0) (v 1) (v 3))
    (hRAXC : InTriStrict (v 6) (v 0) (v 2) (v 3)) :
    23 ≤ sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3) := by
  obtain ⟨_hRXC, _hRCA, hRAX⟩ :=
    inTriStrict_fan_pos hAXC hRAXC
  have hAXR : 0 < sig (v 0) (v 2) (v 6) := by
    rw [sig_rotate (v 6) (v 0) (v 2)] at hRAX
    exact hRAX
  have hAXA : 0 ≤ sig (v 0) (v 2) (v 0) := by
    rw [sig_eq13]

  obtain ⟨_hPBX, hPXA, _hPAB⟩ :=
    inTriStrict_fan_pos hABX hPABX
  have hAXPneg : sig (v 0) (v 2) (v 4) < 0 := by
    have hid :
        sig (v 0) (v 2) (v 4) = -sig (v 4) (v 2) (v 0) := by
      simp only [sig]
      ring
    rw [hid]
    linarith

  have hPpartition := strict_fan_partition hRABC hPABC
    (hmin.sig_ne_zero (i := 6) (j := 0) (k := 4)
      (by decide) (by decide) (by decide))
    (hmin.sig_ne_zero (i := 6) (j := 1) (k := 4)
      (by decide) (by decide) (by decide))
    (hmin.sig_ne_zero (i := 6) (j := 3) (k := 4)
      (by decide) (by decide) (by decide))
  have hPfan :
      InTriStrict (v 4) (v 6) (v 0) (v 1) ∨
        InTriStrict (v 4) (v 6) (v 1) (v 3) := by
    rcases hPpartition with hPBC | hPCA | hPAB
    · exact Or.inr hPBC
    · have hAXPpos : 0 < sig (v 0) (v 2) (v 4) :=
        inTriStrict_sig_pos_of_first_vertex
          hPCA hAXR hAXC.le hAXA
      linarith
    · exact Or.inl hPAB

  obtain ⟨hRBC, _hRCA', _hRAB⟩ :=
    inTriStrict_fan_pos hABC hRABC
  have hBCR : 0 < sig (v 1) (v 3) (v 6) := by
    rw [sig_rotate (v 6) (v 1) (v 3)] at hRBC
    exact hRBC
  have hBCC : 0 ≤ sig (v 1) (v 3) (v 3) := by
    rw [sig_eq23]
  have hBCA : 0 < sig (v 1) (v 3) (v 0) := by
    rw [sig_rotate (v 1) (v 3) (v 0),
      sig_rotate (v 3) (v 0) (v 1)]
    exact hABC

  obtain ⟨_hQXC, hQCB, _hQBX⟩ :=
    inTriStrict_fan_pos hBXC hQBXC
  have hBCQneg : sig (v 1) (v 3) (v 5) < 0 := by
    have hid :
        sig (v 1) (v 3) (v 5) = -sig (v 5) (v 3) (v 1) := by
      simp only [sig]
      ring
    rw [hid]
    linarith

  have hQpartition := strict_fan_partition hRAXC hQAXC
    (hmin.sig_ne_zero (i := 6) (j := 0) (k := 5)
      (by decide) (by decide) (by decide))
    (hmin.sig_ne_zero (i := 6) (j := 2) (k := 5)
      (by decide) (by decide) (by decide))
    (hmin.sig_ne_zero (i := 6) (j := 3) (k := 5)
      (by decide) (by decide) (by decide))
  have hQfan :
      InTriStrict (v 5) (v 6) (v 2) (v 3) ∨
        InTriStrict (v 5) (v 6) (v 0) (v 2) := by
    rcases hQpartition with hQXC | hQCA | hQAX
    · exact Or.inl hQXC
    · have hBCQpos : 0 < sig (v 1) (v 3) (v 5) :=
        inTriStrict_sig_pos_of_first_vertex
          hQCA hBCR hBCC hBCA.le
      linarith
    · exact Or.inr hQAX

  exact hullFive_singleton_fan_cells_210
    v hmin hABC hBXC hABX hAXC hRABC hRAXC hPABX hQBXC
      hPfan hQfan

/-! ## The other three cyclic singleton charts -/

/-- The singleton chart in which `XCO` is empty.  Here `P,Q,R` occupy
`BXO,ACO,ABO`, respectively. -/
theorem hullFive_singleton_cells_missing_xco_210
    (v : Fin 7 → Point)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v 0) (v 1) (v 3))
    (hBXC : 0 < sig (v 1) (v 2) (v 3))
    (hABX : 0 < sig (v 0) (v 1) (v 2))
    (hAXC : 0 < sig (v 0) (v 2) (v 3))
    (hPABX : InTriStrict (v 4) (v 0) (v 1) (v 2))
    (hPBXC : InTriStrict (v 4) (v 1) (v 2) (v 3))
    (hQABC : InTriStrict (v 5) (v 0) (v 1) (v 3))
    (hQAXC : InTriStrict (v 5) (v 0) (v 2) (v 3))
    (hRABC : InTriStrict (v 6) (v 0) (v 1) (v 3))
    (hRABX : InTriStrict (v 6) (v 0) (v 1) (v 2)) :
    23 ≤ sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3) := by
  let r : Fin 7 → Fin 7 := ![1, 2, 3, 0, 4, 5, 6]
  let w : Fin 7 → Point := v ∘ r
  have hr : Function.Injective r := by decide
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp r hr
  have hbound := hullFive_singleton_three_diagonal_cells_210
    w hwmin
      (by simpa [w, r] using sig_pos_rotate_dispatch hABX)
      (by simpa [w, r] using sig_pos_rotate_dispatch hAXC)
      (by simpa [w, r] using hBXC)
      (by simpa [w, r] using sig_pos_rotate_dispatch hABC)
      (by simpa [w, r] using inTriStrict_rotate_dispatch hPABX)
      (by simpa [w, r] using hPBXC)
      (by simpa [w, r] using inTriStrict_rotate_dispatch hQABC)
      (by simpa [w, r] using inTriStrict_rotate_dispatch hQAXC)
      (by simpa [w, r] using inTriStrict_rotate_dispatch hRABX)
      (by simpa [w, r] using inTriStrict_rotate_dispatch hRABC)
  have hquad :=
    hullFive_singleton_quadrilateral_sum (v 0) (v 1) (v 2) (v 3)
  simp [w, r] at hbound
  rw [sig_rotate (v 1) (v 2) (v 0),
    sig_rotate (v 2) (v 0) (v 1),
    sig_rotate (v 2) (v 3) (v 0),
    sig_rotate (v 3) (v 0) (v 2)] at hbound
  nlinarith [hquad]

/-- The singleton chart in which `ACO` is empty.  Here `P,Q,R` occupy
`XCO,ABO,BXO`, respectively. -/
theorem hullFive_singleton_cells_missing_aco_210
    (v : Fin 7 → Point)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v 0) (v 1) (v 3))
    (hBXC : 0 < sig (v 1) (v 2) (v 3))
    (hABX : 0 < sig (v 0) (v 1) (v 2))
    (hAXC : 0 < sig (v 0) (v 2) (v 3))
    (hPAXC : InTriStrict (v 4) (v 0) (v 2) (v 3))
    (hPBXC : InTriStrict (v 4) (v 1) (v 2) (v 3))
    (hQABC : InTriStrict (v 5) (v 0) (v 1) (v 3))
    (hQABX : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hRABX : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hRBXC : InTriStrict (v 6) (v 1) (v 2) (v 3)) :
    23 ≤ sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3) := by
  let r : Fin 7 → Fin 7 := ![2, 3, 0, 1, 4, 5, 6]
  let w : Fin 7 → Point := v ∘ r
  have hr : Function.Injective r := by decide
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp r hr
  have hbound := hullFive_singleton_three_diagonal_cells_210
    w hwmin
      (by simpa [w, r] using sig_pos_rotate_dispatch hBXC)
      (by simpa [w, r] using
        sig_pos_rotate_dispatch (sig_pos_rotate_dispatch hABC))
      (by simpa [w, r] using sig_pos_rotate_dispatch hAXC)
      (by simpa [w, r] using
        sig_pos_rotate_dispatch (sig_pos_rotate_dispatch hABX))
      (by simpa [w, r] using inTriStrict_rotate_dispatch hPBXC)
      (by simpa [w, r] using inTriStrict_rotate_dispatch hPAXC)
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hQABX))
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hQABC))
      (by simpa [w, r] using inTriStrict_rotate_dispatch hRBXC)
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hRABX))
  simp [w, r] at hbound
  rw [sig_rotate (v 2) (v 3) (v 1),
    sig_rotate (v 3) (v 1) (v 2),
    sig_rotate (v 3) (v 0) (v 1)] at hbound
  nlinarith

/-- The singleton chart in which `ABO` is empty.  Here `P,Q,R` occupy
`ACO,BXO,XCO`, respectively. -/
theorem hullFive_singleton_cells_missing_abo_210
    (v : Fin 7 → Point)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v 0) (v 1) (v 3))
    (hBXC : 0 < sig (v 1) (v 2) (v 3))
    (hABX : 0 < sig (v 0) (v 1) (v 2))
    (hAXC : 0 < sig (v 0) (v 2) (v 3))
    (hPABC : InTriStrict (v 4) (v 0) (v 1) (v 3))
    (hPAXC : InTriStrict (v 4) (v 0) (v 2) (v 3))
    (hQABX : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hQBXC : InTriStrict (v 5) (v 1) (v 2) (v 3))
    (hRAXC : InTriStrict (v 6) (v 0) (v 2) (v 3))
    (hRBXC : InTriStrict (v 6) (v 1) (v 2) (v 3)) :
    23 ≤ sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3) := by
  let r : Fin 7 → Fin 7 := ![3, 0, 1, 2, 4, 5, 6]
  let w : Fin 7 → Point := v ∘ r
  have hr : Function.Injective r := by decide
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp r hr
  have hbound := hullFive_singleton_three_diagonal_cells_210
    w hwmin
      (by simpa [w, r] using
        sig_pos_rotate_dispatch (sig_pos_rotate_dispatch hAXC))
      (by simpa [w, r] using hABX)
      (by simpa [w, r] using
        sig_pos_rotate_dispatch (sig_pos_rotate_dispatch hABC))
      (by simpa [w, r] using
        sig_pos_rotate_dispatch (sig_pos_rotate_dispatch hBXC))
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hPAXC))
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hPABC))
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hQBXC))
      (by simpa [w, r] using hQABX)
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hRAXC))
      (by simpa [w, r] using
        inTriStrict_rotate_dispatch (inTriStrict_rotate_dispatch hRBXC))
  have hquad :=
    hullFive_singleton_quadrilateral_sum (v 0) (v 1) (v 2) (v 3)
  simp [w, r] at hbound
  rw [sig_rotate (v 3) (v 0) (v 2)] at hbound
  nlinarith [hquad]

/-! ## Finite cell-pattern dispatcher -/

/-- The four possible three-cell supports in the diagonal `2 + 1`/`2 + 1`
branch.  Point labels are selected cyclically so each constructor feeds one
of the four compact singleton charts above. -/
inductive HullFiveSingletonCellPattern (v : Fin 7 → Point) : Prop
  | missingBXO
      (hPABC : InTriStrict (v 4) (v 0) (v 1) (v 3))
      (hPABX : InTriStrict (v 4) (v 0) (v 1) (v 2))
      (hQAXC : InTriStrict (v 5) (v 0) (v 2) (v 3))
      (hQBXC : InTriStrict (v 5) (v 1) (v 2) (v 3))
      (hRABC : InTriStrict (v 6) (v 0) (v 1) (v 3))
      (hRAXC : InTriStrict (v 6) (v 0) (v 2) (v 3))
  | missingXCO
      (hPABX : InTriStrict (v 4) (v 0) (v 1) (v 2))
      (hPBXC : InTriStrict (v 4) (v 1) (v 2) (v 3))
      (hQABC : InTriStrict (v 5) (v 0) (v 1) (v 3))
      (hQAXC : InTriStrict (v 5) (v 0) (v 2) (v 3))
      (hRABC : InTriStrict (v 6) (v 0) (v 1) (v 3))
      (hRABX : InTriStrict (v 6) (v 0) (v 1) (v 2))
  | missingACO
      (hPAXC : InTriStrict (v 4) (v 0) (v 2) (v 3))
      (hPBXC : InTriStrict (v 4) (v 1) (v 2) (v 3))
      (hQABC : InTriStrict (v 5) (v 0) (v 1) (v 3))
      (hQABX : InTriStrict (v 5) (v 0) (v 1) (v 2))
      (hRABX : InTriStrict (v 6) (v 0) (v 1) (v 2))
      (hRBXC : InTriStrict (v 6) (v 1) (v 2) (v 3))
  | missingABO
      (hPABC : InTriStrict (v 4) (v 0) (v 1) (v 3))
      (hPAXC : InTriStrict (v 4) (v 0) (v 2) (v 3))
      (hQABX : InTriStrict (v 5) (v 0) (v 1) (v 2))
      (hQBXC : InTriStrict (v 5) (v 1) (v 2) (v 3))
      (hRAXC : InTriStrict (v 6) (v 0) (v 2) (v 3))
      (hRBXC : InTriStrict (v 6) (v 1) (v 2) (v 3))

/-- Every three-cell support in the mixed diagonal branch is discharged by
the singleton endpoint, after at most a cyclic relabelling of the four hull
vertices. -/
theorem hullFive_singleton_cell_pattern_210
    (v : Fin 7 → Point)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v 0) (v 1) (v 3))
    (hBXC : 0 < sig (v 1) (v 2) (v 3))
    (hABX : 0 < sig (v 0) (v 1) (v 2))
    (hAXC : 0 < sig (v 0) (v 2) (v 3))
    (hpattern : HullFiveSingletonCellPattern v) :
    23 ≤ sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3) := by
  cases hpattern with
  | missingBXO hPABC hPABX hQAXC hQBXC hRABC hRAXC =>
      exact hullFive_singleton_three_diagonal_cells_210
        v hmin hABC hBXC hABX hAXC
          hPABC hPABX hQAXC hQBXC hRABC hRAXC
  | missingXCO hPABX hPBXC hQABC hQAXC hRABC hRABX =>
      exact hullFive_singleton_cells_missing_xco_210
        v hmin hABC hBXC hABX hAXC
          hPABX hPBXC hQABC hQAXC hRABC hRABX
  | missingACO hPAXC hPBXC hQABC hQABX hRABX hRBXC =>
      exact hullFive_singleton_cells_missing_aco_210
        v hmin hABC hBXC hABX hAXC
          hPAXC hPBXC hQABC hQABX hRABX hRBXC
  | missingABO hPABC hPAXC hQABX hQBXC hRAXC hRBXC =>
      exact hullFive_singleton_cells_missing_abo_210
        v hmin hABC hBXC hABX hAXC
          hPABC hPAXC hQABX hQBXC hRAXC hRBXC

/-! ## Membership-only outer dispatch -/

/-- The `ABX,ABX,AXC` orientation of the outer `210` split.  The diagonal
intersection partitions all three input triangles internally, so no `BC`
sign assignment is required.  The only non-bound leaves are the two genuine
`300` cells already represented by `HullFive300Cell`.

Labels are `A,B,X,C,D,P,Q,R = 0,1,2,3,4,5,6,7`.
-/
theorem hullFive_ax_major_membership_dispatch_210
    (w : Fin 8 → Point) (O : Point)
    (hmin : AllTrianglesMinAreaOne w)
    (hABC : 0 < sig (w 0) (w 1) (w 3))
    (hBXC : 0 < sig (w 1) (w 2) (w 3))
    (hABX : 0 < sig (w 0) (w 1) (w 2))
    (hAXC : 0 < sig (w 0) (w 2) (w 3))
    (hABXmax : sig (w 0) (w 1) (w 2) ≤ sig (w 0) (w 1) (w 3))
    (hAXCmax : sig (w 0) (w 2) (w 3) ≤ sig (w 0) (w 1) (w 3))
    (hOAX : InSegStrict O (w 0) (w 2))
    (hOBC : InSegStrict O (w 1) (w 3))
    (hPABX : InTriStrict (w 5) (w 0) (w 1) (w 2))
    (hQABX : InTriStrict (w 6) (w 0) (w 1) (w 2))
    (hRAXC : InTriStrict (w 7) (w 0) (w 2) (w 3)) :
    HullFive300Cell w id ∨
      23 ≤ sig (w 0) (w 1) (w 3) + sig (w 1) (w 2) (w 3) := by
  have hPsplit := inTriStrict_split_through_edge hPABX hOAX
    (inSegStrict_left_sig_ne hOBC
      (hmin.sig_ne_zero (i := 1) (j := 3) (k := 5)
        (by decide) (by decide) (by decide)))
  have hQsplit := inTriStrict_split_through_edge hQABX hOAX
    (inSegStrict_left_sig_ne hOBC
      (hmin.sig_ne_zero (i := 1) (j := 3) (k := 6)
        (by decide) (by decide) (by decide)))
  have hRsplitRaw := inTriStrict_split_through_edge
    (inTriStrict_rotate_dispatch hRAXC) (inSegStrict_symm hOAX)
    (inSegStrict_left_sig_ne (inSegStrict_symm hOBC)
      (hmin.sig_ne_zero (i := 3) (j := 1) (k := 7)
        (by decide) (by decide) (by decide)))
  have hRsplit :
      InTriStrict (w 7) (w 3) (w 0) O ∨
        InTriStrict (w 7) (w 2) (w 3) O := by
    rcases hRsplitRaw with hRXCO | hRCAO
    · exact Or.inr hRXCO
    · exact Or.inl hRCAO

  rcases hPsplit with hPABO | hPBXO
  · rcases hQsplit with hQABO | hQBXO
    · rcases hRsplit with hRCAO | hRXCO
      · left
        exact .central
          (cellABO_in_ABC hPABO hOBC)
          (cellABO_in_ABC hQABO hOBC)
          (cellCAO_in_ABC hRCAO hOBC)
      · right
        have hABA : 0 ≤ sig (w 0) (w 1) (w 0) := by rw [sig_eq13]
        have hABO : 0 < sig (w 0) (w 1) O :=
          inSegStrict_sig_pos_of_sides hOAX hABA hABX.le (Or.inr hABX)
        have hABR : 0 < sig (w 0) (w 1) (w 7) :=
          inTriStrict_sig_pos_of_first_vertex
            hRXCO hABX hABC.le hABO.le
        have hRAB := sig_pos_rotate_dispatch
          (sig_pos_rotate_dispatch hABR)
        let e : Fin 7 → Fin 8 := ![0, 1, 2, 3, 5, 6, 7]
        have he : Function.Injective e := by decide
        exact (hullFive_opposite_diagonal_cells_210
          w e O he hmin
            (by simpa [e] using hABC) (by simpa [e] using hBXC)
            (by simpa [e] using hABXmax) (by simpa [e] using hRAB)
            (by simpa [e] using hOAX) (by simpa [e] using hOBC)
            (by simpa [e] using hPABO) (by simpa [e] using hQABO)
            (by simpa [e] using hRXCO)).le
    · rcases hRsplit with hRCAO | hRXCO
      · right
        have hPABC := cellABO_in_ABC hPABO hOBC
        have hQBXC := cellBXO_in_BXC hQBXO hOBC
        have hRABC := cellCAO_in_ABC hRCAO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 6, 7, 5]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 6, 7, 5] (by decide)
        have hb := hullFive_singleton_cells_missing_xco_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hQABX) (by simpa [s] using hQBXC)
            (by simpa [s] using hRABC) (by simpa [s] using hRAXC)
            (by simpa [s] using hPABC) (by simpa [s] using hPABX)
        simpa [s] using hb
      · right
        have hPABC := cellABO_in_ABC hPABO hOBC
        have hQBXC := cellBXO_in_BXC hQBXO hOBC
        have hRBXC := cellXCO_in_BXC hRXCO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 7, 5, 6]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 7, 5, 6] (by decide)
        have hb := hullFive_singleton_cells_missing_aco_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hRAXC) (by simpa [s] using hRBXC)
            (by simpa [s] using hPABC) (by simpa [s] using hPABX)
            (by simpa [s] using hQABX) (by simpa [s] using hQBXC)
        simpa [s] using hb
  · rcases hQsplit with hQABO | hQBXO
    · rcases hRsplit with hRCAO | hRXCO
      · right
        have hPBXC := cellBXO_in_BXC hPBXO hOBC
        have hQABC := cellABO_in_ABC hQABO hOBC
        have hRABC := cellCAO_in_ABC hRCAO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 5, 7, 6]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 5, 7, 6] (by decide)
        have hb := hullFive_singleton_cells_missing_xco_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hPABX) (by simpa [s] using hPBXC)
            (by simpa [s] using hRABC) (by simpa [s] using hRAXC)
            (by simpa [s] using hQABC) (by simpa [s] using hQABX)
        simpa [s] using hb
      · right
        have hPBXC := cellBXO_in_BXC hPBXO hOBC
        have hQABC := cellABO_in_ABC hQABO hOBC
        have hRBXC := cellXCO_in_BXC hRXCO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 7, 6, 5]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 7, 6, 5] (by decide)
        have hb := hullFive_singleton_cells_missing_aco_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hRAXC) (by simpa [s] using hRBXC)
            (by simpa [s] using hQABC) (by simpa [s] using hQABX)
            (by simpa [s] using hPABX) (by simpa [s] using hPBXC)
        simpa [s] using hb
    · rcases hRsplit with hRCAO | hRXCO
      · right
        have hBXA := sig_pos_rotate_dispatch hABX
        have hXCA := sig_pos_rotate_dispatch hAXC
        have hBXB : 0 ≤ sig (w 1) (w 2) (w 1) := by rw [sig_eq13]
        have hBXO : 0 < sig (w 1) (w 2) O :=
          inSegStrict_sig_pos_of_sides hOBC hBXB hBXC.le (Or.inr hBXC)
        have hBXR : 0 < sig (w 1) (w 2) (w 7) :=
          inTriStrict_sig_pos_of_first_vertex
            hRCAO hBXC hBXA.le hBXO.le
        have hRBX := sig_pos_rotate_dispatch
          (sig_pos_rotate_dispatch hBXR)
        have hquad :=
          hullFive_singleton_quadrilateral_sum (w 0) (w 1) (w 2) (w 3)
        have hEmaxU : sig (w 1) (w 2) (w 3) ≤
            sig (w 1) (w 2) (w 0) := by
          rw [sig_rotate (w 1) (w 2) (w 0),
            sig_rotate (w 2) (w 0) (w 1)]
          nlinarith
        let e : Fin 7 → Fin 8 := ![1, 2, 3, 0, 5, 6, 7]
        have he : Function.Injective e := by decide
        have hb := (hullFive_opposite_diagonal_cells_210
          w e O he hmin
            (by simpa [e] using hBXA) (by simpa [e] using hXCA)
            (by simpa [e] using hEmaxU) (by simpa [e] using hRBX)
            (by simpa [e] using hOBC)
            (by simpa [e] using inSegStrict_symm hOAX)
            (by simpa [e] using hPBXO) (by simpa [e] using hQBXO)
            (by simpa [e] using hRCAO)).le
        simp [e] at hb
        rw [sig_rotate (w 1) (w 2) (w 0),
          sig_rotate (w 2) (w 0) (w 1),
          sig_rotate (w 2) (w 3) (w 0),
          sig_rotate (w 3) (w 0) (w 2)] at hb
        nlinarith [hquad]
      · left
        exact .right
          (cellBXO_in_BXC hPBXO hOBC)
          (cellBXO_in_BXC hQBXO hOBC)
          (cellXCO_in_BXC hRXCO hOBC)

/-- The symmetric `AXC,AXC,ABX` orientation of the outer `210` split.
Together with `hullFive_ax_major_membership_dispatch_210`, this covers every
labelled `2 + 1` assignment across the diagonal `AX`. -/
theorem hullFive_axc_major_membership_dispatch_210
    (w : Fin 8 → Point) (O : Point)
    (hmin : AllTrianglesMinAreaOne w)
    (hABC : 0 < sig (w 0) (w 1) (w 3))
    (hBXC : 0 < sig (w 1) (w 2) (w 3))
    (hABX : 0 < sig (w 0) (w 1) (w 2))
    (hAXC : 0 < sig (w 0) (w 2) (w 3))
    (hABXmax : sig (w 0) (w 1) (w 2) ≤ sig (w 0) (w 1) (w 3))
    (hAXCmax : sig (w 0) (w 2) (w 3) ≤ sig (w 0) (w 1) (w 3))
    (hOAX : InSegStrict O (w 0) (w 2))
    (hOBC : InSegStrict O (w 1) (w 3))
    (hPAXC : InTriStrict (w 5) (w 0) (w 2) (w 3))
    (hQAXC : InTriStrict (w 6) (w 0) (w 2) (w 3))
    (hRABX : InTriStrict (w 7) (w 0) (w 1) (w 2)) :
    HullFive300Cell w id ∨
      23 ≤ sig (w 0) (w 1) (w 3) + sig (w 1) (w 2) (w 3) := by
  have hPsplitRaw := inTriStrict_split_through_edge
    (inTriStrict_rotate_dispatch hPAXC) (inSegStrict_symm hOAX)
    (inSegStrict_left_sig_ne (inSegStrict_symm hOBC)
      (hmin.sig_ne_zero (i := 3) (j := 1) (k := 5)
        (by decide) (by decide) (by decide)))
  have hQsplitRaw := inTriStrict_split_through_edge
    (inTriStrict_rotate_dispatch hQAXC) (inSegStrict_symm hOAX)
    (inSegStrict_left_sig_ne (inSegStrict_symm hOBC)
      (hmin.sig_ne_zero (i := 3) (j := 1) (k := 6)
        (by decide) (by decide) (by decide)))
  have hPsplit :
      InTriStrict (w 5) (w 3) (w 0) O ∨
        InTriStrict (w 5) (w 2) (w 3) O := by
    rcases hPsplitRaw with hPXCO | hPCAO
    · exact Or.inr hPXCO
    · exact Or.inl hPCAO
  have hQsplit :
      InTriStrict (w 6) (w 3) (w 0) O ∨
        InTriStrict (w 6) (w 2) (w 3) O := by
    rcases hQsplitRaw with hQXCO | hQCAO
    · exact Or.inr hQXCO
    · exact Or.inl hQCAO
  have hRsplit := inTriStrict_split_through_edge hRABX hOAX
    (inSegStrict_left_sig_ne hOBC
      (hmin.sig_ne_zero (i := 1) (j := 3) (k := 7)
        (by decide) (by decide) (by decide)))

  rcases hPsplit with hPCAO | hPXCO
  · rcases hQsplit with hQCAO | hQXCO
    · rcases hRsplit with hRABO | hRBXO
      · left
        exact .central
          (cellCAO_in_ABC hPCAO hOBC)
          (cellCAO_in_ABC hQCAO hOBC)
          (cellABO_in_ABC hRABO hOBC)
      · right
        have hCAX := sig_pos_rotate_dispatch
          (sig_pos_rotate_dispatch hAXC)
        have hCAA : 0 ≤ sig (w 3) (w 0) (w 0) := by rw [sig_eq23]
        have hCAO : 0 < sig (w 3) (w 0) O :=
          inSegStrict_sig_pos_of_sides hOAX hCAA hCAX.le (Or.inr hCAX)
        have hCAB := sig_pos_rotate_dispatch
          (sig_pos_rotate_dispatch hABC)
        have hCAR : 0 < sig (w 3) (w 0) (w 7) :=
          inTriStrict_sig_pos_of_first_vertex
            hRBXO hCAB hCAX.le hCAO.le
        have hRCA := sig_pos_rotate_dispatch
          (sig_pos_rotate_dispatch hCAR)
        let e : Fin 7 → Fin 8 := ![0, 1, 2, 3, 5, 6, 7]
        have he : Function.Injective e := by decide
        exact (hullFive_opposite_diagonal_cells_210_reflected
          w e O he hmin
            (by simpa [e] using hABC) (by simpa [e] using hBXC)
            (by simpa [e] using hAXCmax) (by simpa [e] using hRCA)
            (by simpa [e] using hOAX) (by simpa [e] using hOBC)
            (by simpa [e] using hPCAO) (by simpa [e] using hQCAO)
            (by simpa [e] using hRBXO)).le
    · rcases hRsplit with hRABO | hRBXO
      · right
        have hPABC := cellCAO_in_ABC hPCAO hOBC
        have hQBXC := cellXCO_in_BXC hQXCO hOBC
        have hRABC := cellABO_in_ABC hRABO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 7, 6, 5]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 7, 6, 5] (by decide)
        have hb := hullFive_singleton_three_diagonal_cells_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hRABC) (by simpa [s] using hRABX)
            (by simpa [s] using hQAXC) (by simpa [s] using hQBXC)
            (by simpa [s] using hPABC) (by simpa [s] using hPAXC)
        simpa [s] using hb
      · right
        have hPBXC := cellXCO_in_BXC hQXCO hOBC
        have hRBXC := cellBXO_in_BXC hRBXO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 5, 7, 6]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 5, 7, 6] (by decide)
        have hb := hullFive_singleton_cells_missing_abo_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using cellCAO_in_ABC hPCAO hOBC)
            (by simpa [s] using hPAXC)
            (by simpa [s] using hRABX) (by simpa [s] using hRBXC)
            (by simpa [s] using hQAXC) (by simpa [s] using hPBXC)
        simpa [s] using hb
  · rcases hQsplit with hQCAO | hQXCO
    · rcases hRsplit with hRABO | hRBXO
      · right
        have hPBXC := cellXCO_in_BXC hPXCO hOBC
        have hQABC := cellCAO_in_ABC hQCAO hOBC
        have hRABC := cellABO_in_ABC hRABO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 7, 5, 6]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 7, 5, 6] (by decide)
        have hb := hullFive_singleton_three_diagonal_cells_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hRABC) (by simpa [s] using hRABX)
            (by simpa [s] using hPAXC) (by simpa [s] using hPBXC)
            (by simpa [s] using hQABC) (by simpa [s] using hQAXC)
        simpa [s] using hb
      · right
        have hPBXC := cellXCO_in_BXC hPXCO hOBC
        have hQABC := cellCAO_in_ABC hQCAO hOBC
        have hRBXC := cellBXO_in_BXC hRBXO hOBC
        let s : Fin 7 → Point := w ∘ ![0, 1, 2, 3, 6, 7, 5]
        have hsmin : AllTrianglesMinAreaOne s :=
          hmin.comp ![0, 1, 2, 3, 6, 7, 5] (by decide)
        have hb := hullFive_singleton_cells_missing_abo_210
          s hsmin
            (by simpa [s] using hABC) (by simpa [s] using hBXC)
            (by simpa [s] using hABX) (by simpa [s] using hAXC)
            (by simpa [s] using hQABC) (by simpa [s] using hQAXC)
            (by simpa [s] using hRABX) (by simpa [s] using hRBXC)
            (by simpa [s] using hPAXC) (by simpa [s] using hPBXC)
        simpa [s] using hb
    · rcases hRsplit with hRABO | hRBXO
      · right
        have hXCA := sig_pos_rotate_dispatch hAXC
        have hXCB := sig_pos_rotate_dispatch hBXC
        have hXCC : 0 ≤ sig (w 2) (w 3) (w 3) := by rw [sig_eq23]
        have hXCO : 0 < sig (w 2) (w 3) O :=
          inSegStrict_sig_pos_of_sides hOBC hXCB.le hXCC (Or.inl hXCB)
        have hXCR : 0 < sig (w 2) (w 3) (w 7) :=
          inTriStrict_sig_pos_of_first_vertex
            hRABO hXCA hXCB.le hXCO.le
        have hRXC := sig_pos_rotate_dispatch
          (sig_pos_rotate_dispatch hXCR)
        have hquad :=
          hullFive_singleton_quadrilateral_sum (w 0) (w 1) (w 2) (w 3)
        have hEmaxV : sig (w 1) (w 2) (w 3) ≤
            sig (w 2) (w 3) (w 0) := by
          rw [sig_rotate (w 2) (w 3) (w 0),
            sig_rotate (w 3) (w 0) (w 2)]
          nlinarith
        have hEmaxV' : sig (w 3) (w 1) (w 2) ≤
            sig (w 3) (w 0) (w 2) := by
          calc
            sig (w 3) (w 1) (w 2) = sig (w 1) (w 2) (w 3) :=
              sig_rotate _ _ _
            _ ≤ sig (w 2) (w 3) (w 0) := hEmaxV
            _ = sig (w 3) (w 0) (w 2) := sig_rotate _ _ _
        let e : Fin 7 → Fin 8 := ![3, 0, 1, 2, 5, 6, 7]
        have he : Function.Injective e := by decide
        have hb := (hullFive_opposite_diagonal_cells_210_reflected
          w e O he hmin
            (by simpa [e] using
              sig_pos_rotate_dispatch (sig_pos_rotate_dispatch hAXC))
            (by simpa [e] using hABX)
            (by simpa [e] using hEmaxV') (by simpa [e] using hRXC)
            (by simpa [e] using inSegStrict_symm hOBC)
            (by simpa [e] using hOAX)
            (by simpa [e] using hPXCO) (by simpa [e] using hQXCO)
            (by simpa [e] using hRABO)).le
        simp [e] at hb
        rw [sig_rotate (w 3) (w 0) (w 2)] at hb
        nlinarith [hquad]
      · left
        exact .right
          (cellXCO_in_BXC hPXCO hOBC)
          (cellXCO_in_BXC hQXCO hOBC)
          (cellBXO_in_BXC hRBXO hOBC)

/-- Reindexed form of the `ABX`-major membership dispatcher. -/
theorem hullFive_ax_major_membership_dispatch_210_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8) (O : Point)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hABXmax :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hAXCmax :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hOAX : InSegStrict O (v (e 0)) (v (e 2)))
    (hOBC : InSegStrict O (v (e 1)) (v (e 3)))
    (hPABX : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQABX : InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hRAXC : InTriStrict (v (e 7))
      (v (e 0)) (v (e 2)) (v (e 3))) :
    HullFive300Cell v e ∨
      23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
        sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  let w : Fin 8 → Point := v ∘ e
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp e he
  have hd := hullFive_ax_major_membership_dispatch_210
    w O hwmin
      (by simpa [w] using hABC) (by simpa [w] using hBXC)
      (by simpa [w] using hABX) (by simpa [w] using hAXC)
      (by simpa [w] using hABXmax) (by simpa [w] using hAXCmax)
      (by simpa [w] using hOAX) (by simpa [w] using hOBC)
      (by simpa [w] using hPABX) (by simpa [w] using hQABX)
      (by simpa [w] using hRAXC)
  rcases hd with hcell | hbound
  · left
    cases hcell with
    | central hP hQ hR =>
        exact .central (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
    | right hP hQ hR =>
        exact .right (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
  · exact Or.inr (by simpa [w] using hbound)

/-- Reindexed form of the `AXC`-major membership dispatcher. -/
theorem hullFive_axc_major_membership_dispatch_210_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8) (O : Point)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hABXmax :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hAXCmax :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hOAX : InSegStrict O (v (e 0)) (v (e 2)))
    (hOBC : InSegStrict O (v (e 1)) (v (e 3)))
    (hPAXC : InTriStrict (v (e 5))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hQAXC : InTriStrict (v (e 6))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hRABX : InTriStrict (v (e 7))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    HullFive300Cell v e ∨
      23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
        sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  let w : Fin 8 → Point := v ∘ e
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp e he
  have hd := hullFive_axc_major_membership_dispatch_210
    w O hwmin
      (by simpa [w] using hABC) (by simpa [w] using hBXC)
      (by simpa [w] using hABX) (by simpa [w] using hAXC)
      (by simpa [w] using hABXmax) (by simpa [w] using hAXCmax)
      (by simpa [w] using hOAX) (by simpa [w] using hOBC)
      (by simpa [w] using hPAXC) (by simpa [w] using hQAXC)
      (by simpa [w] using hRABX)
  rcases hd with hcell | hbound
  · left
    cases hcell with
    | central hP hQ hR =>
        exact .central (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
    | right hP hQ hR =>
        exact .right (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
  · exact Or.inr (by simpa [w] using hbound)

/-! ## Witness-free outer API -/

/-- Reindexed `ABX`-major dispatch with the diagonal intersection constructed
internally from the four strict quadrilateral orientations.  This is the
membership-only API intended for the hull-five outer dispatcher: callers do
not need to manufacture or transport an auxiliary point `O`. -/
theorem hullFive_ax_major_membership_dispatch_210_of_orientations
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hABXmax :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hAXCmax :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hPABX : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQABX : InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hRAXC : InTriStrict (v (e 7))
      (v (e 0)) (v (e 2)) (v (e 3))) :
    HullFive300Cell v e ∨
      23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
        sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  obtain ⟨O, hOAX, hOBC⟩ :=
    strictQuad_diagonal_intersection hABC hBXC hABX hAXC
  exact hullFive_ax_major_membership_dispatch_210_reindex
    v e O he hmin hABC hBXC hABX hAXC hABXmax hAXCmax
      hOAX hOBC hPABX hQABX hRAXC

/-- Reindexed `AXC`-major dispatch with the diagonal intersection constructed
internally from the four strict quadrilateral orientations. -/
theorem hullFive_axc_major_membership_dispatch_210_of_orientations
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hABXmax :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hAXCmax :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hPAXC : InTriStrict (v (e 5))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hQAXC : InTriStrict (v (e 6))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hRABX : InTriStrict (v (e 7))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    HullFive300Cell v e ∨
      23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
        sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  obtain ⟨O, hOAX, hOBC⟩ :=
    strictQuad_diagonal_intersection hABC hBXC hABX hAXC
  exact hullFive_axc_major_membership_dispatch_210_reindex
    v e O he hmin hABC hBXC hABX hAXC hABXmax hAXCmax
      hOAX hOBC hPAXC hQAXC hRABX

end Heilbronn8.TriHull
