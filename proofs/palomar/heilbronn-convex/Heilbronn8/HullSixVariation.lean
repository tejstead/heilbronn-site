import Heilbronn8.Defs

/-!
# A six-edge fan variation bound

This file isolates the algebra behind a convex hexagon with two interior
points.  If `A i` and `B i` are the six fan-triangle areas based at the two
points, and `G i` is their signed level at the `i`th hull vertex, then

`A i - B i = G (i + 1) - G i`.

Thus a common lower bound `m` on all twelve fan triangles forces the sum of
the two fan areas to pay both `12 * m` and the full cyclic variation of `G`.
The first part of the file is purely an inequality about six real numbers;
the last part supplies the signed-area identity needed by geometry.
-/

namespace Heilbronn8

/-- The explicitly unrolled sum of a function on six indices. -/
def sumFinSix (f : Fin 6 → ℝ) : ℝ :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5

/-- Total variation around the six-cycle, including the closing edge. -/
def cyclicVariationFinSix (g : Fin 6 → ℝ) : ℝ :=
  |g 1 - g 0| + |g 2 - g 1| + |g 3 - g 2| +
    |g 4 - g 3| + |g 5 - g 4| + |g 0 - g 5|

/-- Every pair of levels is joined by two complementary arcs of the
six-cycle.  Each arc has variation at least the absolute difference of its
endpoints, so the full cyclic variation pays for that difference twice. -/
theorem two_mul_abs_sub_le_cyclicVariationFinSix
    (g : Fin 6 → ℝ) (i j : Fin 6) :
    2 * |g j - g i| ≤ cyclicVariationFinSix g := by
  let V : ℝ := cyclicVariationFinSix g
  have hV : V =
      |g 1 - g 0| + |g 2 - g 1| + |g 3 - g 2| +
        |g 4 - g 3| + |g 5 - g 4| + |g 0 - g 5| := rfl
  have hVnonneg : 0 ≤ V := by
    rw [hV]
    positivity
  have h01p : g 1 - g 0 ≤ |g 1 - g 0| := le_abs_self _
  have h01n : g 0 - g 1 ≤ |g 1 - g 0| := by
    calc
      g 0 - g 1 = -(g 1 - g 0) := by ring
      _ ≤ |g 1 - g 0| := neg_le_abs _
  have h12p : g 2 - g 1 ≤ |g 2 - g 1| := le_abs_self _
  have h12n : g 1 - g 2 ≤ |g 2 - g 1| := by
    calc
      g 1 - g 2 = -(g 2 - g 1) := by ring
      _ ≤ |g 2 - g 1| := neg_le_abs _
  have h23p : g 3 - g 2 ≤ |g 3 - g 2| := le_abs_self _
  have h23n : g 2 - g 3 ≤ |g 3 - g 2| := by
    calc
      g 2 - g 3 = -(g 3 - g 2) := by ring
      _ ≤ |g 3 - g 2| := neg_le_abs _
  have h34p : g 4 - g 3 ≤ |g 4 - g 3| := le_abs_self _
  have h34n : g 3 - g 4 ≤ |g 4 - g 3| := by
    calc
      g 3 - g 4 = -(g 4 - g 3) := by ring
      _ ≤ |g 4 - g 3| := neg_le_abs _
  have h45p : g 5 - g 4 ≤ |g 5 - g 4| := le_abs_self _
  have h45n : g 4 - g 5 ≤ |g 5 - g 4| := by
    calc
      g 4 - g 5 = -(g 5 - g 4) := by ring
      _ ≤ |g 5 - g 4| := neg_le_abs _
  have h50p : g 0 - g 5 ≤ |g 0 - g 5| := le_abs_self _
  have h50n : g 5 - g 0 ≤ |g 0 - g 5| := by
    calc
      g 5 - g 0 = -(g 0 - g 5) := by ring
      _ ≤ |g 0 - g 5| := neg_le_abs _
  have absBound (x : ℝ) (hp : 2 * x ≤ V) (hn : 2 * (-x) ≤ V) :
      2 * |x| ≤ V := by
    rcases le_total 0 x with hx | hx
    · rwa [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      exact hn
  have h01 : 2 * |g 1 - g 0| ≤ V :=
    absBound (g 1 - g 0) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h02 : 2 * |g 2 - g 0| ≤ V :=
    absBound (g 2 - g 0) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h03 : 2 * |g 3 - g 0| ≤ V :=
    absBound (g 3 - g 0) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h04 : 2 * |g 4 - g 0| ≤ V :=
    absBound (g 4 - g 0) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h05 : 2 * |g 5 - g 0| ≤ V :=
    absBound (g 5 - g 0) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h12 : 2 * |g 2 - g 1| ≤ V :=
    absBound (g 2 - g 1) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h13 : 2 * |g 3 - g 1| ≤ V :=
    absBound (g 3 - g 1) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h14 : 2 * |g 4 - g 1| ≤ V :=
    absBound (g 4 - g 1) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h15 : 2 * |g 5 - g 1| ≤ V :=
    absBound (g 5 - g 1) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h23 : 2 * |g 3 - g 2| ≤ V :=
    absBound (g 3 - g 2) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h24 : 2 * |g 4 - g 2| ≤ V :=
    absBound (g 4 - g 2) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h25 : 2 * |g 5 - g 2| ≤ V :=
    absBound (g 5 - g 2) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h34 : 2 * |g 4 - g 3| ≤ V :=
    absBound (g 4 - g 3) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h35 : 2 * |g 5 - g 3| ≤ V :=
    absBound (g 5 - g 3) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have h45 : 2 * |g 5 - g 4| ≤ V :=
    absBound (g 5 - g 4) (by rw [hV]; linarith) (by rw [hV]; linarith)
  have hordered (a b : Fin 6) (hab : a < b) :
      2 * |g b - g a| ≤ V := by
    fin_cases a <;> fin_cases b
    all_goals simp only [Fin.mk_lt_mk, id_eq] at hab ⊢
    all_goals first | omega | assumption | (rw [abs_sub_comm]; assumption)
  have habs : 2 * |g j - g i| ≤ V := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hordered i j hij
    · subst j
      simpa only [sub_self, abs_zero, mul_zero] using hVnonneg
    · simpa only [abs_sub_comm] using hordered j i hij
  change 2 * |g j - g i| ≤ V
  exact habs

/-- Signed form of `two_mul_abs_sub_le_cyclicVariationFinSix`. -/
theorem two_mul_sub_le_cyclicVariationFinSix
    (g : Fin 6 → ℝ) (i j : Fin 6) :
    2 * (g j - g i) ≤ cyclicVariationFinSix g := by
  exact le_trans
    (mul_le_mul_of_nonneg_left (le_abs_self (g j - g i)) (by norm_num))
    (two_mul_abs_sub_le_cyclicVariationFinSix g i j)

/-- Two numbers above the same floor pay for their absolute difference. -/
lemma two_mul_floor_add_abs_sub_le_add {a b m : ℝ}
    (ha : m ≤ a) (hb : m ≤ b) :
    2 * m + |a - b| ≤ a + b := by
  have habs : |a - b| ≤ a + b - 2 * m := by
    apply (abs_le).2
    constructor <;> linarith
  linarith

/--
The abstract six-fan inequality.  No geometric or convexity assumptions are
needed after the six difference identities and the two equal fan sums have
been exposed.
-/
theorem sixFanVariation_bound (A B G : Fin 6 → ℝ) (m H : ℝ)
    (hA : ∀ i, m ≤ A i) (hB : ∀ i, m ≤ B i)
    (hASum : sumFinSix A = H) (hBSum : sumFinSix B = H)
    (hDiff : ∀ i, A i - B i = G (i + 1) - G i) :
    12 * m + cyclicVariationFinSix G ≤ 2 * H := by
  have hpair (i : Fin 6) :
      2 * m + |A i - B i| ≤ A i + B i :=
    two_mul_floor_add_abs_sub_le_add (hA i) (hB i)
  have hpairG (i : Fin 6) :
      2 * m + |G (i + 1) - G i| ≤ A i + B i := by
    rw [← hDiff i]
    exact hpair i
  have h0 := hpairG (0 : Fin 6)
  have h1 := hpairG (1 : Fin 6)
  have h2 := hpairG (2 : Fin 6)
  have h3 := hpairG (3 : Fin 6)
  have h4 := hpairG (4 : Fin 6)
  have h5 := hpairG (5 : Fin 6)
  change 2 * m + |G 1 - G 0| ≤ A 0 + B 0 at h0
  change 2 * m + |G 2 - G 1| ≤ A 1 + B 1 at h1
  change 2 * m + |G 3 - G 2| ≤ A 2 + B 2 at h2
  change 2 * m + |G 4 - G 3| ≤ A 3 + B 3 at h3
  change 2 * m + |G 5 - G 4| ≤ A 4 + B 4 at h4
  change 2 * m + |G 0 - G 5| ≤ A 5 + B 5 at h5
  simp only [sumFinSix] at hASum hBSum
  simp only [cyclicVariationFinSix]
  linarith

/-
A selected pair range follows once its elementary two-arc variation bound is
supplied.  Keeping that finite index selection outside this generic module
avoids a large `Fin 6` case split in every downstream import.
-/
theorem sixFanPairRange_bound_of_variation
    (A B G : Fin 6 → ℝ) (m H : ℝ)
    (hA : ∀ i, m ≤ A i) (hB : ∀ i, m ≤ B i)
    (hASum : sumFinSix A = H) (hBSum : sumFinSix B = H)
    (hDiff : ∀ i, A i - B i = G (i + 1) - G i)
    (iLo iHi : Fin 6)
    (hvariation : 2 * (G iHi - G iLo) ≤ cyclicVariationFinSix G) :
    6 * m + (G iHi - G iLo) ≤ H := by
  have hfan := sixFanVariation_bound A B G m H
    hA hB hASum hBSum hDiff
  linarith

/-- Pair-range consequence with the two-arc inequality discharged once and
for all by the six-cycle geometry of the index set. -/
theorem sixFanPairRange_bound
    (A B G : Fin 6 → ℝ) (m H : ℝ)
    (hA : ∀ i, m ≤ A i) (hB : ∀ i, m ≤ B i)
    (hASum : sumFinSix A = H) (hBSum : sumFinSix B = H)
    (hDiff : ∀ i, A i - B i = G (i + 1) - G i)
    (iLo iHi : Fin 6) :
    6 * m + (G iHi - G iLo) ≤ H := by
  exact sixFanPairRange_bound_of_variation A B G m H
    hA hB hASum hBSum hDiff iLo iHi
      (two_mul_sub_le_cyclicVariationFinSix G iLo iHi)

/-! ## Signed-area realization -/

/-- Difference of two fan triangles is a difference of cross-line levels. -/
lemma sig_fan_difference (p q a b : ℝ × ℝ) :
    sig p a b - sig q a b = sig p q b - sig p q a := by
  simp only [sig]
  ring

/-- The six-fan variation bound specialized to signed triangle areas. -/
theorem geometricSixFanVariation_bound
    (p q : ℝ × ℝ) (v : Fin 6 → ℝ × ℝ) (m H : ℝ)
    (hp : ∀ i, m ≤ sig p (v i) (v (i + 1)))
    (hq : ∀ i, m ≤ sig q (v i) (v (i + 1)))
    (hpSum : sumFinSix (fun i => sig p (v i) (v (i + 1))) = H)
    (hqSum : sumFinSix (fun i => sig q (v i) (v (i + 1))) = H) :
    12 * m + cyclicVariationFinSix (fun i => sig p q (v i)) ≤ 2 * H := by
  refine sixFanVariation_bound
    (A := fun i => sig p (v i) (v (i + 1)))
    (B := fun i => sig q (v i) (v (i + 1)))
    (G := fun i => sig p q (v i))
    (m := m) (H := H) hp hq hpSum hqSum ?_
  intro i
  exact sig_fan_difference p q (v i) (v (i + 1))

/-- Pair-range consequence for two geometric six-fans, given the elementary
two-arc variation inequality for the selected concrete indices. -/
theorem geometricSixFanPairRange_bound_of_variation
    (p q : ℝ × ℝ) (v : Fin 6 → ℝ × ℝ) (m H : ℝ)
    (hp : ∀ i, m ≤ sig p (v i) (v (i + 1)))
    (hq : ∀ i, m ≤ sig q (v i) (v (i + 1)))
    (hpSum : sumFinSix (fun i => sig p (v i) (v (i + 1))) = H)
    (hqSum : sumFinSix (fun i => sig q (v i) (v (i + 1))) = H)
    (iLo iHi : Fin 6)
    (hvariation :
      2 * (sig p q (v iHi) - sig p q (v iLo)) ≤
        cyclicVariationFinSix (fun i => sig p q (v i))) :
    6 * m + (sig p q (v iHi) - sig p q (v iLo)) ≤ H := by
  refine sixFanPairRange_bound_of_variation
    (A := fun i => sig p (v i) (v (i + 1)))
    (B := fun i => sig q (v i) (v (i + 1)))
    (G := fun i => sig p q (v i))
    (m := m) (H := H) hp hq hpSum hqSum ?_ iLo iHi hvariation
  intro i
  exact sig_fan_difference p q (v i) (v (i + 1))

/-- Geometric pair-range consequence with no extra generated variation
obligation. -/
theorem geometricSixFanPairRange_bound
    (p q : ℝ × ℝ) (v : Fin 6 → ℝ × ℝ) (m H : ℝ)
    (hp : ∀ i, m ≤ sig p (v i) (v (i + 1)))
    (hq : ∀ i, m ≤ sig q (v i) (v (i + 1)))
    (hpSum : sumFinSix (fun i => sig p (v i) (v (i + 1))) = H)
    (hqSum : sumFinSix (fun i => sig q (v i) (v (i + 1))) = H)
    (iLo iHi : Fin 6) :
    6 * m + (sig p q (v iHi) - sig p q (v iLo)) ≤ H := by
  exact geometricSixFanPairRange_bound_of_variation
    p q v m H hp hq hpSum hqSum iLo iHi
      (two_mul_sub_le_cyclicVariationFinSix
        (fun i => sig p q (v i)) iLo iHi)

end Heilbronn8
