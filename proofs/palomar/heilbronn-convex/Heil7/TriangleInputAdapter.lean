import Heil7.Hull45Route
import Heilbronn8.TriHull.Bridge

/-!
# Direct packet adapters for the n = 7 hull-four and hull-five inputs

The proved TH8 triangle lemmas are normalized to ordinary minimum triangle
area one, hence doubled minimum area two.  This module rescales only the
selected five- or six-point packet by the positive horizontal factor `2 / m`
and applies those lemmas directly.  In particular, no dummy labels are added
to make a `Fin 8` configuration, so no ambient minimum can be made smaller by
padding.

`MainAux.two_point_bound` is the public arbitrary-two-point consequence of
`th8_lemma1`; it performs the fan-cell split that the raw theorem needs.
`th8_lemma3` is already stated directly on a six-point packet, and its only
abstract input is discharged by the proved theorem `surcharge1_holds`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Scale one coordinate.  Doubled signed areas are multiplied by `r`, rather
than by `r ^ 2`, which keeps the normalization algebra especially small. -/
private def packetScale (r : ℝ) (p : Point) : Point :=
  (r * p.1, p.2)

private lemma n8_sig_packetScale (r : ℝ) (p q s : Point) :
    Heilbronn8.sig (packetScale r p) (packetScale r q) (packetScale r s) =
      r * HeilbronnChallenge.sig p q s := by
  simp only [packetScale, Heilbronn8.sig, HeilbronnChallenge.sig]
  ring

/-- Strict barycentric membership is preserved by the packet scaling.  The
target is deliberately the TH8 namespace's copy of the predicate. -/
private lemma n8_inTriStrict_packetScale (r : ℝ) {P A B C : Point}
    (hP : InTriStrict P A B C) :
    Heilbronn8.TriHull.InTriStrict (packetScale r P)
      (packetScale r A) (packetScale r B) (packetScale r C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hPe⟩ := hP
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hPe]
  apply Prod.ext
  · simp only [packetScale, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
    ring
  · simp only [packetScale, Prod.smul_snd, Prod.snd_add, smul_eq_mul]

/-- A floor `m > 0` on a selected packet becomes the TH8 normalization after
horizontal scaling by `2 / m`. -/
private lemma selectedPacket_minimum {s n : ℕ}
    (w : Fin n → Point) (m : ℝ) (e : Fin s → Fin n)
    (he : Function.Injective e) (hm : 0 < m)
    (hfloor : AllTrianglesFloor w m) :
    Heilbronn8.TriHull.AllTrianglesMinAreaOne
      (fun i ↦ packetScale (2 / m) (w (e i))) := by
  intro i j k hij hik hjk
  have hraw := hfloor (e i) (e j) (e k)
    (he.ne hij) (he.ne hik) (he.ne hjk)
  have hrpos : 0 < (2 : ℝ) / m := div_pos (by norm_num) hm
  rw [n8_sig_packetScale, abs_mul, abs_of_pos hrpos]
  calc
    (2 : ℝ) = (2 / m) * m := by field_simp [ne_of_gt hm]
    _ ≤ (2 / m) * |HeilbronnChallenge.sig (w (e i)) (w (e j)) (w (e k))| :=
      mul_le_mul_of_nonneg_left hraw hrpos.le

/-- The homogeneous two-interior-point input used by the n = 7 hull-four and
hull-five geometry, obtained on the exact selected `Fin 5` packet. -/
theorem triangleTwoSeven_holds : TriangleTwoSeven := by
  unfold TriangleTwoSeven
  intro n w m e he hm hfloor hABC hP hQ
  let r : ℝ := 2 / m
  let u : Fin 5 → Point := fun i ↦ packetScale r (w (e i))
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have huMin : Heilbronn8.TriHull.AllTrianglesMinAreaOne u := by
    simpa [u, r] using selectedPacket_minimum w m e he hm hfloor
  have hscale :
      Heilbronn8.sig (u 0) (u 1) (u 2) =
        r * HeilbronnChallenge.sig (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [u] using n8_sig_packetScale r
      (w (e 0)) (w (e 1)) (w (e 2))
  have huPos : 0 < Heilbronn8.sig (u 0) (u 1) (u 2) := by
    rw [hscale]
    exact mul_pos hrpos hABC
  have huP : Heilbronn8.TriHull.InTriStrict (u 3) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_packetScale r hP
  have huQ : Heilbronn8.TriHull.InTriStrict (u 4) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_packetScale r hQ
  have hb :
      4 + 2 * Real.sqrt 3 ≤ Heilbronn8.sig (u 0) (u 1) (u 2) / 2 := by
    simpa using Heilbronn8.TriHull.MainAux.two_point_bound
      (v := u) huMin (fun i : Fin 5 ↦ i) (by intro a b hab; exact hab)
        huPos huP huQ
  have hcoef : (7 : ℝ) ≤ 4 + 2 * Real.sqrt 3 := by
    nlinarith [Heilbronn8.TriHull.MainAux.three_halves_le_sqrt_three]
  have hnorm : (7 : ℝ) ≤ Heilbronn8.sig (u 0) (u 1) (u 2) / 2 :=
    hcoef.trans hb
  have hmul := mul_le_mul_of_nonneg_right hnorm hm.le
  calc
    7 * m ≤ (Heilbronn8.sig (u 0) (u 1) (u 2) / 2) * m := hmul
    _ = HeilbronnChallenge.sig (w (e 0)) (w (e 1)) (w (e 2)) := by
      rw [hscale]
      dsimp [r]
      field_simp [ne_of_gt hm]

/-- The homogeneous three-interior-point input used by the n = 7 hull-four
geometry, obtained on the exact selected `Fin 6` packet. -/
theorem triangleThreeSeventeen_holds : TriangleThreeSeventeen := by
  unfold TriangleThreeSeventeen
  intro n w m e he hm hfloor hABC hP hQ hR
  let r : ℝ := 2 / m
  let u : Fin 6 → Point := fun i ↦ packetScale r (w (e i))
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have huMin : Heilbronn8.TriHull.AllTrianglesMinAreaOne u := by
    simpa [u, r] using selectedPacket_minimum w m e he hm hfloor
  have hscale :
      Heilbronn8.sig (u 0) (u 1) (u 2) =
        r * HeilbronnChallenge.sig (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [u] using n8_sig_packetScale r
      (w (e 0)) (w (e 1)) (w (e 2))
  have huPos : 0 < Heilbronn8.sig (u 0) (u 1) (u 2) := by
    rw [hscale]
    exact mul_pos hrpos hABC
  have huP : Heilbronn8.TriHull.InTriStrict (u 3) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_packetScale r hP
  have huQ : Heilbronn8.TriHull.InTriStrict (u 4) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_packetScale r hQ
  have huR : Heilbronn8.TriHull.InTriStrict (u 5) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_packetScale r hR
  have hb :
      (17 : ℝ) / 2 ≤ Heilbronn8.sig (u 0) (u 1) (u 2) / 2 :=
    Heilbronn8.TriHull.th8_lemma3
      Heilbronn8.TriHull.surcharge1_holds u huPos huP huQ huR huMin
  have hmul := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (2 : ℝ) * m by positivity)
  calc
    17 * m = ((17 : ℝ) / 2) * (2 * m) := by ring
    _ ≤ (Heilbronn8.sig (u 0) (u 1) (u 2) / 2) * (2 * m) := hmul
    _ = 2 * HeilbronnChallenge.sig (w (e 0)) (w (e 1)) (w (e 2)) := by
      rw [hscale]
      dsimp [r]
      field_simp [ne_of_gt hm]

/-- Consequently the previously conditional hull-four and hull-five source
adapters have no remaining triangle-estimate hypotheses. -/
theorem hull45_fields_unconditional :
    (∀ (v : Configuration7), HullCCW v 4 →
      (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
      9 * minTri v ≤ fanArea v 4) ∧
    (∀ (v : Configuration7), HullCCW v 5 →
      (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
      9 * minTri v ≤ fanArea v 5) :=
  hull45_fields triangleTwoSeven_holds triangleThreeSeventeen_holds

end HeilbronnChallenge.N7Upper
