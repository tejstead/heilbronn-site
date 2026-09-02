import Heilbronn8.TriHull.MainFive

namespace Heilbronn8.TriHull

private lemma sig_swap_first (p q r : Point) :
    sig p q r = -sig q p r := by
  simp only [sig]
  ring

private lemma minTri_le_abs_sig_of_ne (v : Fin 8 → Point)
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    minTri v ≤ |sig (v i) (v j) (v k)| := by
  by_cases hijlt : i < j
  · by_cases hjklt : j < k
    · exact minTri_le v hijlt hjklt
    · have hkj : k < j :=
        lt_of_le_of_ne (le_of_not_gt hjklt) (Ne.symm hjk)
      by_cases hiklt : i < k
      · calc
          minTri v ≤ |sig (v i) (v k) (v j)| :=
            minTri_le v hiklt hkj
          _ = |sig (v i) (v j) (v k)| := by
            rw [sig_swap (v i) (v k) (v j), abs_neg]
      · have hki : k < i :=
          lt_of_le_of_ne (le_of_not_gt hiklt) (Ne.symm hik)
        calc
          minTri v ≤ |sig (v k) (v i) (v j)| :=
            minTri_le v hki hijlt
          _ = |sig (v i) (v j) (v k)| := by
            rw [sig_rotate (v k) (v i) (v j)]
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt hijlt) (Ne.symm hij)
    by_cases hiklt : i < k
    · calc
        minTri v ≤ |sig (v j) (v i) (v k)| :=
          minTri_le v hji hiklt
        _ = |sig (v i) (v j) (v k)| := by
          rw [sig_swap_first (v j) (v i) (v k), abs_neg]
    · have hki : k < i :=
        lt_of_le_of_ne (le_of_not_gt hiklt) (Ne.symm hik)
      by_cases hjklt : j < k
      · calc
          minTri v ≤ |sig (v j) (v k) (v i)| :=
            minTri_le v hjklt hki
          _ = |sig (v i) (v j) (v k)| := by
            rw [sig_rotate (v j) (v k) (v i),
              sig_rotate (v k) (v i) (v j)]
      · have hkj : k < j :=
          lt_of_le_of_ne (le_of_not_gt hjklt) (Ne.symm hjk)
        calc
          minTri v ≤ |sig (v k) (v j) (v i)| :=
            minTri_le v hkj hji
          _ = |sig (v i) (v j) (v k)| := by
            rw [sig_swap_first (v k) (v j) (v i), abs_neg,
              sig_rotate (v j) (v k) (v i),
              sig_rotate (v k) (v i) (v j)]

private def scaleFirst (r : ℝ) (p : Point) : Point :=
  (r * p.1, p.2)

private lemma sig_scaleFirst (r : ℝ) (p q s : Point) :
    sig (scaleFirst r p) (scaleFirst r q) (scaleFirst r s) =
      r * sig p q s := by
  simp only [scaleFirst, sig]
  ring

private lemma inTriStrict_scaleFirst (r : ℝ) {P A B C : Point}
    (hP : InTriStrict P A B C) :
    InTriStrict (scaleFirst r P)
      (scaleFirst r A) (scaleFirst r B) (scaleFirst r C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hPe⟩ := hP
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hPe]
  simp only [scaleFirst, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  apply Prod.ext <;> simp <;> ring

private lemma normalized_minimum (v : Fin 8 → Point)
    (hm : 0 < minTri v) :
    AllTrianglesMinAreaOne
      (fun i => scaleFirst (2 / minTri v) (v i)) := by
  intro i j k hij hik hjk
  have hle := minTri_le_abs_sig_of_ne v hij hik hjk
  have hrpos : 0 < 2 / minTri v := div_pos (by norm_num) hm
  have hrm : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hrm.symm
    _ ≤ (2 / minTri v) * |sig (v i) (v j) (v k)| :=
      mul_le_mul_of_nonneg_left hle hrpos.le
    _ = |sig
        (scaleFirst (2 / minTri v) (v i))
        (scaleFirst (2 / minTri v) (v j))
        (scaleFirst (2 / minTri v) (v k))| := by
      rw [sig_scaleFirst, abs_mul, abs_of_pos hrpos]

/--
Scale-free form of the two-interior-point triangle estimate.  This is the
piece of `th8_lemma1` needed by the balanced-diagonal branch of QuadHull8:
after normalizing the doubled minimum triangle area to two, the containing
triangle has ordinary area at least `4 + 2 * sqrt 3`.
-/
theorem twoPointTriangle_normalized_lower_bound
    (v : Fin 8 → Point) (e : Fin 5 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    4 + 2 * Real.sqrt 3 ≤
      sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
  let r : ℝ := 2 / minTri v
  let w : Fin 8 → Point := fun i => scaleFirst r (v i)
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have hwmin : AllTrianglesMinAreaOne w := by
    simpa [w, r] using normalized_minimum v hm
  have hwpos : 0 < sig (w (e 0)) (w (e 1)) (w (e 2)) := by
    rw [show sig (w (e 0)) (w (e 1)) (w (e 2)) =
      r * sig (v (e 0)) (v (e 1)) (v (e 2)) by
        simp only [w, sig_scaleFirst]]
    exact mul_pos hrpos hpos
  have hwP : InTriStrict (w (e 3))
      (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [w] using inTriStrict_scaleFirst r hP
  have hwQ : InTriStrict (w (e 4))
      (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [w] using inTriStrict_scaleFirst r hQ
  have hbound := MainAux.two_point_bound hwmin e he hwpos hwP hwQ
  have hsig : sig (w (e 0)) (w (e 1)) (w (e 2)) =
      r * sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simp only [w, sig_scaleFirst]
  calc
    4 + 2 * Real.sqrt 3 ≤
        (r * sig (v (e 0)) (v (e 1)) (v (e 2))) / 2 := by
      rw [hsig] at hbound
      exact hbound
    _ = sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
      dsimp [r]
      field_simp [ne_of_gt hm]

/-
Scale-free form of the three-interior-point triangle estimate.  The
normalization is the same as in `twoPointTriangle_normalized_lower_bound`:
the doubled minimum triangle area becomes two, so the containing triangle's
ordinary area is its original signed area divided by `minTri v`.
-/
theorem threePointTriangle_normalized_lower_bound
    (surcharge1 : Surcharge1Statement)
    (v : Fin 8 → Point) (e : Fin 6 → Fin 8)
    (he : Function.Injective e)
    (hm : 0 < minTri v)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    (17 : ℝ) / 2 ≤
      sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
  let r : ℝ := 2 / minTri v
  let w : Fin 8 → Point := fun i => scaleFirst r (v i)
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have hwmin : AllTrianglesMinAreaOne w := by
    simpa [w, r] using normalized_minimum v hm
  have hwpos : 0 < sig (w (e 0)) (w (e 1)) (w (e 2)) := by
    rw [show sig (w (e 0)) (w (e 1)) (w (e 2)) =
      r * sig (v (e 0)) (v (e 1)) (v (e 2)) by
        simp only [w, sig_scaleFirst]]
    exact mul_pos hrpos hpos
  have hwP : InTriStrict (w (e 3))
      (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [w] using inTriStrict_scaleFirst r hP
  have hwQ : InTriStrict (w (e 4))
      (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [w] using inTriStrict_scaleFirst r hQ
  have hwR : InTriStrict (w (e 5))
      (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [w] using inTriStrict_scaleFirst r hR
  have hbound := MainAux.lemma3_bound surcharge1 hwmin e he hwpos hwP hwQ hwR
  have hsig : sig (w (e 0)) (w (e 1)) (w (e 2)) =
      r * sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simp only [w, sig_scaleFirst]
  calc
    (17 : ℝ) / 2 ≤
        (r * sig (v (e 0)) (v (e 1)) (v (e 2))) / 2 := by
      rw [hsig] at hbound
      exact hbound
    _ = sig (v (e 0)) (v (e 1)) (v (e 2)) / minTri v := by
      dsimp [r]
      field_simp [ne_of_gt hm]

/--
A labelled strict triangular-hull certificate. The first three labels are
the counterclockwise hull vertices, labels 3 through 7 are strictly inside,
and H is the doubled hull area, in the convention of Defs and HullArea.
-/
structure StrictTriangleHullCertificate (v : Fin 8 → Point) (H : ℝ) :
    Prop where
  hull_pos : 0 < sig (v 0) (v 1) (v 2)
  point3 : InTriStrict (v 3) (v 0) (v 1) (v 2)
  point4 : InTriStrict (v 4) (v 0) (v 1) (v 2)
  point5 : InTriStrict (v 5) (v 0) (v 1) (v 2)
  point6 : InTriStrict (v 6) (v 0) (v 1) (v 2)
  point7 : InTriStrict (v 7) (v 0) (v 1) (v 2)
  hull_area : H = sig (v 0) (v 1) (v 2)

/--
TriangleHull8 in doubled-area form. This form composes directly with
minTri and the real-valued hull-area certificates; the ENNReal volume
translation can be performed later with volume_convexHull_triple.
-/
theorem triangleHull8
    (surcharge1 : Surcharge1Statement)
    (surcharge2 : Surcharge2Statement)
    (v : Fin 8 → Point) (H : ℝ)
    (hHull : StrictTriangleHullCertificate v H) :
    minTri v * 25 ≤ 2 * H := by
  by_cases hm0 : minTri v = 0
  · nlinarith [hHull.hull_pos, hHull.hull_area]
  · have hm : 0 < minTri v :=
      lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hm0)
    let r : ℝ := 2 / minTri v
    let w : Fin 8 → Point := fun i => scaleFirst r (v i)
    have hrpos : 0 < r := by
      dsimp [r]
      exact div_pos (by norm_num) hm
    have hrm : r * minTri v = 2 := by
      dsimp [r]
      field_simp [ne_of_gt hm]
    have hwmin : AllTrianglesMinAreaOne w := by
      simpa [w, r] using normalized_minimum v hm
    have hwpos : 0 < sig (w 0) (w 1) (w 2) := by
      rw [show sig (w 0) (w 1) (w 2) =
        r * sig (v 0) (v 1) (v 2) by
          simp only [w, sig_scaleFirst]]
      exact mul_pos hrpos hHull.hull_pos
    have hw3 : InTriStrict (w 3) (w 0) (w 1) (w 2) := by
      simpa only [w] using inTriStrict_scaleFirst r hHull.point3
    have hw4 : InTriStrict (w 4) (w 0) (w 1) (w 2) := by
      simpa only [w] using inTriStrict_scaleFirst r hHull.point4
    have hw5 : InTriStrict (w 5) (w 0) (w 1) (w 2) := by
      simpa only [w] using inTriStrict_scaleFirst r hHull.point5
    have hw6 : InTriStrict (w 6) (w 0) (w 1) (w 2) := by
      simpa only [w] using inTriStrict_scaleFirst r hHull.point6
    have hw7 : InTriStrict (w 7) (w 0) (w 1) (w 2) := by
      simpa only [w] using inTriStrict_scaleFirst r hHull.point7
    have hmain := th8_lemma5 surcharge1 surcharge2 w
      hwpos hw3 hw4 hw5 hw6 hw7 hwmin
    have hsig :
        sig (w 0) (w 1) (w 2) =
          r * sig (v 0) (v 1) (v 2) := by
      simp only [w, sig_scaleFirst]
    rw [hsig, ← hHull.hull_area] at hmain
    have hdouble : (25 : ℝ) ≤ r * H := by
      linarith
    have hmr : minTri v * r = 2 := by
      nlinarith [hrm]
    calc
      minTri v * 25 ≤ minTri v * (r * H) :=
        mul_le_mul_of_nonneg_left hdouble hm.le
      _ = 2 * H := by rw [← mul_assoc, hmr]


end Heilbronn8.TriHull
