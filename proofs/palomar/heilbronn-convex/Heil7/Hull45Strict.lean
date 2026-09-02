import Heil7.TriangleInputAdapter

/-!
# Strict hull-four and hull-five bounds

The public `TriangleTwoSeven` interface deliberately weakens the proved
two-interior-point coefficient from `4 + 2 * sqrt 3` to `7`.  That weakening
is harmless for the weak hull bounds, but it hides the strict margin needed
when equality is classified.  This file keeps the sharp coefficient and
uses it only where the margin is needed.

The crossed-diagonal quadrilateral calculation really can attain `8 * m`.
The equality data are therefore extracted rather than discarded.  The
seventh point, in the missing pentagon ear, is then incompatible with the
triangle floor.  Everything below is homogeneous in the doubled-area floor
`m`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-! ## The unweakened two-point packet input -/

/-- The exact homogeneous consequence of the proved TH8 two-point estimate. -/
def TriangleTwoSharp : Prop :=
  ∀ {n : ℕ} (w : Fin n → Point) (m : ℝ) (e : Fin 5 → Fin n),
    Function.Injective e → 0 < m → AllTrianglesFloor w m →
    0 < sig (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 3)) (w (e 0)) (w (e 1)) (w (e 2)) →
    InTriStrict (w (e 4)) (w (e 0)) (w (e 1)) (w (e 2)) →
    (4 + 2 * Real.sqrt 3) * m ≤
      sig (w (e 0)) (w (e 1)) (w (e 2))

private def sharpPacketScale (r : ℝ) (p : Point) : Point :=
  (r * p.1, p.2)

private lemma n8_sig_sharpPacketScale (r : ℝ) (p q s : Point) :
    Heilbronn8.sig (sharpPacketScale r p)
        (sharpPacketScale r q) (sharpPacketScale r s) =
      r * HeilbronnChallenge.sig p q s := by
  simp only [sharpPacketScale, Heilbronn8.sig, HeilbronnChallenge.sig]
  ring

private lemma n8_inTriStrict_sharpPacketScale (r : ℝ)
    {P A B C : Point} (hP : InTriStrict P A B C) :
    Heilbronn8.TriHull.InTriStrict (sharpPacketScale r P)
      (sharpPacketScale r A) (sharpPacketScale r B)
      (sharpPacketScale r C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hPe⟩ := hP
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hPe]
  apply Prod.ext
  · simp only [sharpPacketScale, Prod.smul_fst, Prod.fst_add,
      smul_eq_mul]
    ring
  · simp only [sharpPacketScale, Prod.smul_snd, Prod.snd_add,
      smul_eq_mul]

private lemma sharpPacket_minimum {s n : ℕ}
    (w : Fin n → Point) (m : ℝ) (e : Fin s → Fin n)
    (he : Function.Injective e) (hm : 0 < m)
    (hfloor : AllTrianglesFloor w m) :
    Heilbronn8.TriHull.AllTrianglesMinAreaOne
      (fun i ↦ sharpPacketScale (2 / m) (w (e i))) := by
  intro i j k hij hik hjk
  have hraw := hfloor (e i) (e j) (e k)
    (he.ne hij) (he.ne hik) (he.ne hjk)
  have hrpos : 0 < (2 : ℝ) / m := div_pos (by norm_num) hm
  rw [n8_sig_sharpPacketScale, abs_mul, abs_of_pos hrpos]
  calc
    (2 : ℝ) = (2 / m) * m := by field_simp [ne_of_gt hm]
    _ ≤ (2 / m) *
        |HeilbronnChallenge.sig (w (e i)) (w (e j)) (w (e k))| :=
      mul_le_mul_of_nonneg_left hraw hrpos.le

theorem triangleTwoSharp_holds : TriangleTwoSharp := by
  unfold TriangleTwoSharp
  intro n w m e he hm hfloor hABC hP hQ
  let r : ℝ := 2 / m
  let u : Fin 5 → Point := fun i ↦ sharpPacketScale r (w (e i))
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by norm_num) hm
  have huMin : Heilbronn8.TriHull.AllTrianglesMinAreaOne u := by
    simpa [u, r] using sharpPacket_minimum w m e he hm hfloor
  have hscale :
      Heilbronn8.sig (u 0) (u 1) (u 2) =
        r * HeilbronnChallenge.sig (w (e 0)) (w (e 1)) (w (e 2)) := by
    simpa only [u] using n8_sig_sharpPacketScale r
      (w (e 0)) (w (e 1)) (w (e 2))
  have huPos : 0 < Heilbronn8.sig (u 0) (u 1) (u 2) := by
    rw [hscale]
    exact mul_pos hrpos hABC
  have huP : Heilbronn8.TriHull.InTriStrict
      (u 3) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_sharpPacketScale r hP
  have huQ : Heilbronn8.TriHull.InTriStrict
      (u 4) (u 0) (u 1) (u 2) := by
    simpa only [u] using n8_inTriStrict_sharpPacketScale r hQ
  have hb :
      4 + 2 * Real.sqrt 3 ≤
        Heilbronn8.sig (u 0) (u 1) (u 2) / 2 := by
    simpa using Heilbronn8.TriHull.MainAux.two_point_bound
      (v := u) huMin (fun i : Fin 5 ↦ i)
        (by intro a b hab; exact hab) huPos huP huQ
  have hmul := mul_le_mul_of_nonneg_right hb hm.le
  calc
    (4 + 2 * Real.sqrt 3) * m ≤
        (Heilbronn8.sig (u 0) (u 1) (u 2) / 2) * m := hmul
    _ = HeilbronnChallenge.sig
        (w (e 0)) (w (e 1)) (w (e 2)) := by
      rw [hscale]
      dsimp [r]
      field_simp [ne_of_gt hm]

lemma seven_lt_twoPointCoefficient :
    (7 : ℝ) < 4 + 2 * Real.sqrt 3 := by
  nlinarith [Heilbronn8.TriHull.sixty_nine_fortieths_lt_sqrt_three]

/-! ## Linear forms forced by crossed-quadrilateral equality -/

private lemma base_pluecker (O A B U V : Point) :
    sig O A B * sig O U V =
      sig O U B * sig O A V + sig O A U * sig O B V := by
  simp only [sig]
  ring

private lemma triangle_base_sum (O A B C : Point) :
    sig A B C = sig O A B + sig O B C + sig O C A := by
  simp only [sig]
  ring

/-- Once the six-point crossed equality data are fixed, every determinant
involving an extra point `E` is an affine-linear form in
`s = sig B P E`. -/
private lemma crossedEquality_linear_forms
    {A B C D P Q E : Point} {m : ℝ} (hm : 0 < m)
    (hAB : sig P A B = 2 * m)
    (hBC : sig P B C = m) (hCA : sig P C A = m)
    (hDA : sig P D A = 3 * m) (hDB : sig P D B = m)
    (hQAP : sig Q A P = m) (hQPD : sig Q P D = m) :
    let s := sig B P E
    sig P B E = -s ∧
    2 * sig P C E = -sig P A E + s ∧
    2 * sig P D E = sig P A E + 3 * s ∧
    sig P A Q = -m ∧ sig P B Q = -m ∧
    2 * sig P Q E = sig P A E + s := by
  let s := sig B P E
  have hs : sig P B E = -s := by
    dsimp [s]
    simp only [sig]
    ring
  have hCB : sig P C B = -m := by
    rw [n7_sig_swap_last]
    linarith
  have hAC : sig P A C = -m := by
    rw [n7_sig_swap_last]
    linarith
  have hAD : sig P A D = -3 * m := by
    rw [n7_sig_swap_last]
    linarith
  have cancel_m : ∀ {x : ℝ}, m * x = 0 → x = 0 := by
    intro x hx
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt hm)
  have hCEraw := base_pluecker P A B C E
  have hCEfactor :
      m * (2 * sig P C E + sig P A E + sig P B E) = 0 := by
    calc
      m * (2 * sig P C E + sig P A E + sig P B E) =
          sig P A B * sig P C E -
            (sig P C B * sig P A E + sig P A C * sig P B E) := by
              rw [hAB, hCB, hAC]
              ring
      _ = 0 := by rw [hCEraw]; ring
  have hCEzero := cancel_m hCEfactor
  have hCE : 2 * sig P C E = -sig P A E + s := by
    rw [hs] at hCEzero
    linarith
  have hDEraw := base_pluecker P A B D E
  have hDEfactor :
      m * (2 * sig P D E - sig P A E + 3 * sig P B E) = 0 := by
    calc
      m * (2 * sig P D E - sig P A E + 3 * sig P B E) =
          sig P A B * sig P D E -
            (sig P D B * sig P A E + sig P A D * sig P B E) := by
              rw [hAB, hDB, hAD]
              ring
      _ = 0 := by rw [hDEraw]; ring
  have hDEzero := cancel_m hDEfactor
  have hDE : 2 * sig P D E = sig P A E + 3 * s := by
    rw [hs] at hDEzero
    linarith
  have hAQ : sig P A Q = -m := by
    have hid : sig P A Q = -sig Q A P := by
      simp only [sig]
      ring
    rw [hid, hQAP]
  have hDQ : sig P D Q = m := by
    have hid : sig P D Q = sig Q P D := by
      simp only [sig]
      ring
    rw [hid, hQPD]
  have hBQraw := base_pluecker P A B D Q
  have hBQfactor : m * (3 * m + 3 * sig P B Q) = 0 := by
    calc
      m * (3 * m + 3 * sig P B Q) =
          sig P A B * sig P D Q -
            (sig P D B * sig P A Q + sig P A D * sig P B Q) := by
              rw [hAB, hDQ, hDB, hAQ, hAD]
              ring
      _ = 0 := by rw [hBQraw]; ring
  have hBQzero := cancel_m hBQfactor
  have hBQ : sig P B Q = -m := by linarith
  have hQB : sig P Q B = m := by
    rw [n7_sig_swap_last]
    linarith
  have hQEraw := base_pluecker P A B Q E
  have hQEfactor :
      m * (2 * sig P Q E - sig P A E - s) = 0 := by
    calc
      m * (2 * sig P Q E - sig P A E - s) =
          sig P A B * sig P Q E -
            (sig P Q B * sig P A E + sig P A Q * sig P B E) := by
              rw [hAB, hQB, hAQ, hs]
              ring
      _ = 0 := by rw [hQEraw]; ring
  have hQEzero := cancel_m hQEfactor
  exact ⟨hs, hCE, hDE, hAQ, hBQ, by linarith⟩

/-! ## The extra pentagon vertex excludes both crossed equality patterns -/

private lemma crossedEquality_lastEar_impossible
    {A B C D E P Q : Point} {m : ℝ} (hm : 0 < m)
    (hAB : sig P A B = 2 * m)
    (hBC : sig P B C = m) (hCA : sig P C A = m)
    (hCD : sig P C D = 2 * m)
    (hDA : sig P D A = 3 * m) (hDB : sig P D B = m)
    (hQAP : sig Q A P = m) (hQPD : sig Q P D = m)
    (hDEA : sig D E A = m)
    (hABEpos : 0 < sig A B E) (hCDEpos : 0 < sig C D E)
    (hPQEfloor : m ≤ |sig P Q E|) : False := by
  let s := sig B P E
  rcases crossedEquality_linear_forms hm hAB hBC hCA hDA hDB
      hQAP hQPD (E := E) with
    ⟨hBE, hCE, hDE, _hAQ, _hBQ, hQE⟩
  have hAD : sig P A D = -3 * m := by
    rw [n7_sig_swap_last]
    linarith
  have hearSum := triangle_base_sum P D E A
  have hAE : sig P A E = 3 * s - 8 * m := by
    have hEA : sig P E A = -sig P A E := by
      rw [n7_sig_swap_last]
    rw [hDEA, hEA, hAD] at hearSum
    linarith
  have hABEform : sig A B E = 10 * m - 4 * s := by
    have hsum := triangle_base_sum P A B E
    have hEA : sig P E A = -sig P A E := by
      rw [n7_sig_swap_last]
    rw [hAB, hBE, hEA, hAE] at hsum
    linarith
  have hCDEform : sig C D E = 4 * s - 6 * m := by
    have hsum := triangle_base_sum P C D E
    have hEC : sig P E C = -sig P C E := by
      rw [n7_sig_swap_last]
    rw [hCD, hEC] at hsum
    linarith
  have hPQEform : sig P Q E = 2 * s - 4 * m := by
    rw [hAE] at hQE
    linarith
  have hslo : 3 * m < 2 * s := by
    rw [hCDEform] at hCDEpos
    nlinarith
  have hshi : 2 * s < 5 * m := by
    rw [hABEform] at hABEpos
    nlinarith
  have hpqLo : -m < sig P Q E := by
    rw [hPQEform]
    linarith
  have hpqHi : sig P Q E < m := by
    rw [hPQEform]
    linarith
  have habs : |sig P Q E| < m := (abs_lt).2 ⟨hpqLo, hpqHi⟩
  exact (not_lt_of_ge hPQEfloor) habs

/-- This is the rotated crossed pattern.  In the standardized equality
packet, the missing pentagon vertex lies between `C` and `D`. -/
private lemma crossedEquality_middleEar_impossible
    {A B C D E P Q : Point} {m : ℝ} (hm : 0 < m)
    (hAB : sig P A B = 2 * m)
    (hBC : sig P B C = m) (hCA : sig P C A = m)
    (hCD : sig P C D = 2 * m)
    (hDA : sig P D A = 3 * m) (hDB : sig P D B = m)
    (hQAP : sig Q A P = m) (hQPD : sig Q P D = m)
    (hCED : sig C E D = m)
    (hBCEpos : 0 < sig B C E) (hAEDpos : 0 < sig A E D)
    (hBPEfloor : m ≤ |sig B P E|)
    (hAQEfloor : m ≤ |sig A Q E|) : False := by
  let s := sig B P E
  rcases crossedEquality_linear_forms hm hAB hBC hCA hDA hDB
      hQAP hQPD (E := E) with
    ⟨hBE, hCE, hDE, hAQ, _hBQ, hQE⟩
  have hDC : sig P D C = -2 * m := by
    rw [n7_sig_swap_last]
    linarith
  have hearSum := triangle_base_sum P C E D
  have hAE : sig P A E = -s - 3 * m := by
    have hED : sig P E D = -sig P D E := by
      rw [n7_sig_swap_last]
    rw [hCED, hED, hDC] at hearSum
    linarith
  have hBCEform : 2 * sig B C E = 4 * s + 5 * m := by
    have hsum := triangle_base_sum P B C E
    have hEB : sig P E B = s := by
      rw [n7_sig_swap_last, hBE]
      ring
    rw [hBC, hEB] at hsum
    linarith
  have hAEDform : 2 * sig A E D = 3 * m - 4 * s := by
    have hsum := triangle_base_sum P A E D
    have hED : sig P E D = -sig P D E := by
      rw [n7_sig_swap_last]
    rw [hDA, hED] at hsum
    linarith
  have hAQEform : 2 * sig A Q E = 2 * s + m := by
    have hsum := triangle_base_sum P A Q E
    have hEA : sig P E A = -sig P A E := by
      rw [n7_sig_swap_last]
    rw [hAQ, hEA] at hsum
    rw [hAE] at hQE
    linarith
  have hslo : -5 * m < 4 * s := by
    nlinarith [hBCEpos, hBCEform]
  have hshi : 4 * s < 3 * m := by
    nlinarith [hAEDpos, hAEDform]
  have hsFloor : m ≤ |s| := by simpa only [s] using hBPEfloor
  have hsle : s ≤ -m := by
    by_cases hs0 : 0 ≤ s
    · rw [abs_of_nonneg hs0] at hsFloor
      nlinarith
    · have hsneg : s < 0 := lt_of_not_ge hs0
      rw [abs_of_neg hsneg] at hsFloor
      linarith
  have haqLo : -m < sig A Q E := by
    nlinarith [hAQEform, hslo]
  have haqHi : sig A Q E < m := by
    nlinarith [hAQEform, hsle, hm]
  have habs : |sig A Q E| < m := (abs_lt).2 ⟨haqLo, haqHi⟩
  exact (not_lt_of_ge hAQEfloor) habs

/-! ## Equality extraction from the crossed calculation -/

/-- Equality in `crossedQuadEight` forces the displayed affine normal form.
These nine determinant equalities are the coordinate-free version of

`P=(0,0), A=(1,0), B=(0,2), C=(-1/2,-1), D=(1/2,-3), Q=(1/2,-1)`

after an orientation-preserving affine normalization with `m = 1`. -/
private lemma crossedQuadEight_equality_data
    {A B C D P Q : Point} {m : ℝ} (hm : 0 < m)
    (hccw : StrictCCWQuad A B C D)
    (hp : StrictInQuad P A B C D)
    (hq : StrictInQuad Q A B C D)
    (hacp : sig A C P < 0) (hbdp : sig B D P < 0)
    (hacq : 0 < sig A C Q) (hbdq : 0 < sig B D Q)
    (hPBCfloor : m ≤ |sig P B C|)
    (hPCAfloor : m ≤ |sig P C A|)
    (hPDBfloor : m ≤ |sig P D B|)
    (hQDAfloor : m ≤ |sig Q D A|)
    (hQAPfloor : m ≤ |sig Q A P|)
    (hQPDfloor : m ≤ |sig Q P D|)
    (hquad : sig A B C + sig A C D = 8 * m) :
    sig P A B = 2 * m ∧ sig P B C = m ∧
    sig P C A = m ∧ sig P C D = 2 * m ∧
    sig P D A = 3 * m ∧ sig P D B = m ∧
    sig Q D A = m ∧ sig Q A P = m ∧ sig Q P D = m := by
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
  have hbeta : m ≤ sig P B C := by
    rwa [abs_of_pos hPBC] at hPBCfloor
  have hu : m ≤ sig P C A := by
    rwa [abs_of_pos hPCA] at hPCAfloor
  have hz : m ≤ sig P D B := by
    rwa [abs_of_pos hPDB] at hPDBfloor
  obtain ⟨hQDA, hQAP, hQPD⟩ := inTriStrict_fan_pos hPDA hQin
  have hqDA : m ≤ sig Q D A := by
    rwa [abs_of_pos hQDA] at hQDAfloor
  have hqAP : m ≤ sig Q A P := by
    rwa [abs_of_pos hQAP] at hQAPfloor
  have hqPD : m ≤ sig Q P D := by
    rwa [abs_of_pos hQPD] at hQPDfloor
  have hqfan :
      sig Q D A + sig Q A P + sig Q P D = sig P D A := by
    simp only [sig]
    ring
  have hdelta : 3 * m ≤ sig P D A := by linarith
  have hprodIdentity :
      sig P A B * sig P C D =
        sig P B C * sig P D A + sig P C A * sig P D B := by
    simp only [sig]
    ring
  have hbetadelta :
      3 * m ^ 2 ≤ sig P B C * sig P D A := by
    have hbeta0 : 0 ≤ sig P B C := hPBC.le
    have hthree0 : 0 ≤ 3 * m := mul_nonneg (by norm_num) hm.le
    calc
      3 * m ^ 2 = m * (3 * m) := by ring
      _ ≤ sig P B C * (3 * m) :=
        mul_le_mul_of_nonneg_right hbeta hthree0
      _ ≤ sig P B C * sig P D A :=
        mul_le_mul_of_nonneg_left hdelta hbeta0
  have huz : m ^ 2 ≤ sig P C A * sig P D B := by
    have hnonneg :=
      mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hz)
    nlinarith
  have hprod :
      4 * m ^ 2 ≤ sig P A B * sig P C D := by
    rw [hprodIdentity]
    linarith
  have hsum : 4 * m ≤ sig P A B + sig P C D := by
    nlinarith [sq_nonneg (sig P A B - sig P C D)]
  have hfan :
      sig A B C + sig A C D =
        sig P A B + sig P B C + sig P C D + sig P D A := by
    simp only [sig]
    ring
  have hbetaEq : sig P B C = m := by
    linarith only [hquad, hfan, hsum, hdelta, hbeta]
  have hdeltaEq : sig P D A = 3 * m := by
    linarith only [hquad, hfan, hsum, hdelta, hbeta]
  have hsumEq : sig P A B + sig P C D = 4 * m := by
    linarith only [hquad, hfan, hsum, hdelta, hbeta]
  have hsumSq := congrArg (fun x : ℝ ↦ x ^ 2) hsumEq
  have hdiffSq : (sig P A B - sig P C D) ^ 2 = 0 := by
    nlinarith only [hprod, hsumSq,
      sq_nonneg (sig P A B - sig P C D)]
  have hdiff : sig P A B - sig P C D = 0 :=
    (sq_eq_zero_iff).mp hdiffSq
  have halphaEq : sig P A B = 2 * m := by
    linarith only [hsumEq, hdiff]
  have hgammaEq : sig P C D = 2 * m := by
    linarith only [hsumEq, halphaEq]
  have hprodIdentity' := hprodIdentity
  rw [halphaEq, hgammaEq, hbetaEq, hdeltaEq] at hprodIdentity'
  have huzEq : sig P C A * sig P D B = m ^ 2 := by
    nlinarith only [hprodIdentity']
  have hu0 : 0 ≤ sig P C A := hPCA.le
  have hz0 : 0 ≤ sig P D B := hPDB.le
  have humul : sig P C A * m ≤ m * m := by
    have hle := mul_le_mul_of_nonneg_left hz (show 0 ≤ sig P C A from hu0)
    nlinarith only [hle, huzEq]
  have hule : sig P C A ≤ m := by
    exact le_of_mul_le_mul_right humul hm
  have huEq : sig P C A = m := le_antisymm hule hu
  have hzEq : sig P D B = m := by
    rw [huEq] at huzEq
    have hzero : m * (sig P D B - m) = 0 := by
      nlinarith only [huzEq]
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hm))
  have hqDAEq : sig Q D A = m := by
    linarith only [hqfan, hdeltaEq, hqDA, hqAP, hqPD]
  have hqAPEq : sig Q A P = m := by
    linarith only [hqfan, hdeltaEq, hqDA, hqAP, hqPD]
  have hqPDEq : sig Q P D = m := by
    linarith only [hqfan, hdeltaEq, hqDA, hqAP, hqPD]
  exact ⟨halphaEq, hbetaEq, huEq, hgammaEq, hdeltaEq, hzEq,
    hqDAEq, hqAPEq, hqPDEq⟩

/-! ## Strict crossed quadrilateral plus its pentagon ear -/

/-- Standard crossed signs, with the omitted pentagon vertex in the last
ear `DEA`. -/
private theorem crossedQuad_lastEar_strict {n : ℕ}
    (w : Fin n → Point) (m : ℝ) (e : Fin 7 → Fin n)
    (he : Function.Injective e) (hm : 0 < m)
    (hfloor : AllTrianglesFloor w m)
    (hccw : StrictCCWQuad (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hp : StrictInQuad (w (e 5))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hq : StrictInQuad (w (e 6))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hacp : sig (w (e 0)) (w (e 2)) (w (e 5)) < 0)
    (hbdp : sig (w (e 1)) (w (e 3)) (w (e 5)) < 0)
    (hacq : 0 < sig (w (e 0)) (w (e 2)) (w (e 6)))
    (hbdq : 0 < sig (w (e 1)) (w (e 3)) (w (e 6)))
    (hABE : 0 < sig (w (e 0)) (w (e 1)) (w (e 4)))
    (hCDE : 0 < sig (w (e 2)) (w (e 3)) (w (e 4)))
    (hDEA : 0 < sig (w (e 3)) (w (e 4)) (w (e 0))) :
    9 * m <
      (sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3))) +
          sig (w (e 3)) (w (e 4)) (w (e 0)) := by
  let e6 : Fin 6 → Fin n := e ∘ ![0, 1, 2, 3, 5, 6]
  have he6 : Function.Injective e6 := he.comp (by decide)
  have hquad := crossedQuadEight w m e6 he6 hm hfloor hccw hp hq
    hacp hbdp hacq hbdq
  change 8 * m ≤
    sig (w (e 0)) (w (e 1)) (w (e 2)) +
      sig (w (e 0)) (w (e 2)) (w (e 3)) at hquad
  have hear := hfloor (e 3) (e 4) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rw [abs_of_pos hDEA] at hear
  by_contra hn
  have hupper := le_of_not_gt hn
  have hquadEq :
      sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3)) = 8 * m := by
    linarith
  have hearEq : sig (w (e 3)) (w (e 4)) (w (e 0)) = m := by
    linarith
  have floorPBC := hfloor (e 5) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorPCA := hfloor (e 5) (e 2) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorPDB := hfloor (e 5) (e 3) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorQDA := hfloor (e 6) (e 3) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorQAP := hfloor (e 6) (e 0) (e 5)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorQPD := hfloor (e 6) (e 5) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rcases crossedQuadEight_equality_data hm hccw hp hq hacp hbdp hacq hbdq
      floorPBC floorPCA floorPDB floorQDA floorQAP floorQPD hquadEq with
    ⟨hAB, hBC, hCA, hCD, hDA, hDB, _hQDA, hQAP, hQPD⟩
  have floorPQE := hfloor (e 5) (e 6) (e 4)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  exact crossedEquality_lastEar_impossible hm hAB hBC hCA hCD hDA hDB
    hQAP hQPD hearEq hABE hCDE floorPQE

/-- Standard crossed signs after a one-step cyclic rotation.  The omitted
pentagon vertex then lies in the middle ear `CED`. -/
private theorem crossedQuad_middleEar_strict {n : ℕ}
    (w : Fin n → Point) (m : ℝ) (e : Fin 7 → Fin n)
    (he : Function.Injective e) (hm : 0 < m)
    (hfloor : AllTrianglesFloor w m)
    (hccw : StrictCCWQuad (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hp : StrictInQuad (w (e 5))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hq : StrictInQuad (w (e 6))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hacp : sig (w (e 0)) (w (e 2)) (w (e 5)) < 0)
    (hbdp : sig (w (e 1)) (w (e 3)) (w (e 5)) < 0)
    (hacq : 0 < sig (w (e 0)) (w (e 2)) (w (e 6)))
    (hbdq : 0 < sig (w (e 1)) (w (e 3)) (w (e 6)))
    (hBCE : 0 < sig (w (e 1)) (w (e 2)) (w (e 4)))
    (hAED : 0 < sig (w (e 0)) (w (e 4)) (w (e 3)))
    (hCED : 0 < sig (w (e 2)) (w (e 4)) (w (e 3))) :
    9 * m <
      (sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3))) +
          sig (w (e 2)) (w (e 4)) (w (e 3)) := by
  let e6 : Fin 6 → Fin n := e ∘ ![0, 1, 2, 3, 5, 6]
  have he6 : Function.Injective e6 := he.comp (by decide)
  have hquad := crossedQuadEight w m e6 he6 hm hfloor hccw hp hq
    hacp hbdp hacq hbdq
  change 8 * m ≤
    sig (w (e 0)) (w (e 1)) (w (e 2)) +
      sig (w (e 0)) (w (e 2)) (w (e 3)) at hquad
  have hear := hfloor (e 2) (e 4) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rw [abs_of_pos hCED] at hear
  by_contra hn
  have hupper := le_of_not_gt hn
  have hquadEq :
      sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3)) = 8 * m := by
    linarith
  have hearEq : sig (w (e 2)) (w (e 4)) (w (e 3)) = m := by
    linarith
  have floorPBC := hfloor (e 5) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorPCA := hfloor (e 5) (e 2) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorPDB := hfloor (e 5) (e 3) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorQDA := hfloor (e 6) (e 3) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorQAP := hfloor (e 6) (e 0) (e 5)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorQPD := hfloor (e 6) (e 5) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rcases crossedQuadEight_equality_data hm hccw hp hq hacp hbdp hacq hbdq
      floorPBC floorPCA floorPDB floorQDA floorQAP floorQPD hquadEq with
    ⟨hAB, hBC, hCA, hCD, hDA, hDB, _hQDA, hQAP, hQPD⟩
  have floorBPE := hfloor (e 1) (e 5) (e 4)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have floorAQE := hfloor (e 0) (e 6) (e 4)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  exact crossedEquality_middleEar_impossible hm hAB hBC hCA hCD hDA hDB
    hQAP hQPD hearEq hBCE hAED floorBPE floorAQE

/-! ## A strict quadrilateral-plus-ear estimate -/

/-- Two points strictly inside `ABCD`, together with the next pentagon ear
`DEA`, force a strict total of nine floors.  Shared-diagonal cells use the
unweakened TH8 coefficient.  The two genuinely crossed cells use the two
equality exclusions above. -/
theorem quadrilateralTwo_with_lastEar_strict (two : TriangleTwoSharp)
    {n : ℕ} (w : Fin n → Point) (m : ℝ) (e : Fin 7 → Fin n)
    (he : Function.Injective e) (hm : 0 < m)
    (hfloor : AllTrianglesFloor w m)
    (hccw : StrictCCWQuad (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hp : StrictInQuad (w (e 5))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hq : StrictInQuad (w (e 6))
      (w (e 0)) (w (e 1)) (w (e 2)) (w (e 3)))
    (hABE : 0 < sig (w (e 0)) (w (e 1)) (w (e 4)))
    (hCDE : 0 < sig (w (e 2)) (w (e 3)) (w (e 4)))
    (hDEA : 0 < sig (w (e 3)) (w (e 4)) (w (e 0))) :
    9 * m <
      (sig (w (e 0)) (w (e 1)) (w (e 2)) +
        sig (w (e 0)) (w (e 2)) (w (e 3))) +
          sig (w (e 3)) (w (e 4)) (w (e 0)) := by
  let A := w (e 0)
  let B := w (e 1)
  let C := w (e 2)
  let D := w (e 3)
  let E := w (e 4)
  let P := w (e 5)
  let Q := w (e 6)
  rcases hccw with ⟨hABC, hABD, hACD, hBCD⟩
  rcases hp with ⟨hABP, hBCP, hCDP, hDAP⟩
  rcases hq with ⟨hABQ, hBCQ, hCDQ, hDAQ⟩
  have hDAB : 0 < sig D A B :=
    n7_sig_pos_rotate (n7_sig_pos_rotate hABD)
  have hABCfloor := hfloor (e 0) (e 1) (e 2)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hACDfloor := hfloor (e 0) (e 2) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hBCDfloor := hfloor (e 1) (e 2) (e 3)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hDABfloor := hfloor (e 3) (e 0) (e 1)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hDEAfloor := hfloor (e 3) (e 4) (e 0)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  rw [abs_of_pos hABC] at hABCfloor
  rw [abs_of_pos hACD] at hACDfloor
  rw [abs_of_pos hBCD] at hBCDfloor
  rw [abs_of_pos hDAB] at hDABfloor
  rw [abs_of_pos hDEA] at hDEAfloor
  have hdiagSum : sig A B C + sig A C D = sig B C D + sig D A B := by
    simp only [A, B, C, D, sig]
    ring
  have hBEA : 0 < sig B E A := by
    rw [n7_sig_rotate B E A, n7_sig_rotate E A B]
    exact hABE
  have acPfloor := hfloor (e 0) (e 2) (e 5)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have acQfloor := hfloor (e 0) (e 2) (e 6)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have bdPfloor := hfloor (e 1) (e 3) (e 5)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have bdQfloor := hfloor (e 1) (e 3) (e 6)
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
  have hcoefm :
      7 * m < (4 + 2 * Real.sqrt 3) * m :=
    mul_lt_mul_of_pos_right seven_lt_twoPointCoefficient hm
  by_cases acP : 0 < sig A C P
  · by_cases acQ : 0 < sig A C Q
    · have pACD := inTriStrict_of_orientations hACD acP hCDP hDAP
      have qACD := inTriStrict_of_orientations hACD acQ hCDQ hDAQ
      have ht := two w m (e ∘ ![0, 2, 3, 5, 6])
        (he.comp (by decide)) hm hfloor hACD pACD qACD
      change (4 + 2 * Real.sqrt 3) * m ≤ sig A C D at ht
      change 9 * m < (sig A B C + sig A C D) + sig D E A
      linarith
    · have acQ' : sig A C Q < 0 :=
        lt_of_le_of_ne (le_of_not_gt acQ) acQne
      by_cases bdP : 0 < sig B D P
      · by_cases bdQ : 0 < sig B D Q
        · have pDAB := inTriStrict_of_orientations hDAB hDAP hABP bdP
          have qDAB := inTriStrict_of_orientations hDAB hDAQ hABQ bdQ
          have ht := two w m (e ∘ ![3, 0, 1, 5, 6])
            (he.comp (by decide)) hm hfloor hDAB pDAB qDAB
          change (4 + 2 * Real.sqrt 3) * m ≤ sig D A B at ht
          change 9 * m < (sig A B C + sig A C D) + sig D E A
          linarith [hdiagSum]
        · have bdQ' : sig B D Q < 0 :=
            lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          exact crossedQuad_lastEar_strict w m
            (e ∘ ![0, 1, 2, 3, 4, 6, 5]) (he.comp (by decide)) hm hfloor
            ⟨hABC, hABD, hACD, hBCD⟩
            ⟨hABQ, hBCQ, hCDQ, hDAQ⟩
            ⟨hABP, hBCP, hCDP, hDAP⟩
            acQ' bdQ' acP bdP hABE hCDE hDEA
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
          have hc := crossedQuad_middleEar_strict w m
            (e ∘ ![1, 2, 3, 0, 4, 5, 6]) (he.comp (by decide)) hm hfloor
            hrotCCW hrotP hrotQ bdP'
            (by
              change sig C A P < 0
              rw [n7_sig_reverse]
              linarith [acP]) bdQ
            (by
              change 0 < sig C A Q
              rw [n7_sig_reverse]
              linarith [acQ']) hCDE hBEA hDEA
          change 9 * m < (sig A B C + sig A C D) + sig D E A
          change 9 * m < (sig B C D + sig B D A) + sig D E A at hc
          have hBDA : sig B D A = sig D A B := n7_sig_rotate B D A
          linarith only [hc, hdiagSum, hBDA]
        · have bdQ' : sig B D Q < 0 :=
            lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          have pBCD := inTriStrict_of_orientations hBCD hBCP hCDP
            (by rw [n7_sig_reverse]; linarith)
          have qBCD := inTriStrict_of_orientations hBCD hBCQ hCDQ
            (by rw [n7_sig_reverse]; linarith)
          have ht := two w m (e ∘ ![1, 2, 3, 5, 6])
            (he.comp (by decide)) hm hfloor hBCD pBCD qBCD
          change (4 + 2 * Real.sqrt 3) * m ≤ sig B C D at ht
          change 9 * m < (sig A B C + sig A C D) + sig D E A
          linarith [hdiagSum]
  · have acP' : sig A C P < 0 :=
      lt_of_le_of_ne (le_of_not_gt acP) acPne
    by_cases acQ : 0 < sig A C Q
    · by_cases bdP : 0 < sig B D P
      · by_cases bdQ : 0 < sig B D Q
        · have pDAB := inTriStrict_of_orientations hDAB hDAP hABP bdP
          have qDAB := inTriStrict_of_orientations hDAB hDAQ hABQ bdQ
          have ht := two w m (e ∘ ![3, 0, 1, 5, 6])
            (he.comp (by decide)) hm hfloor hDAB pDAB qDAB
          change (4 + 2 * Real.sqrt 3) * m ≤ sig D A B at ht
          change 9 * m < (sig A B C + sig A C D) + sig D E A
          linarith [hdiagSum]
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
          have hc := crossedQuad_middleEar_strict w m
            (e ∘ ![1, 2, 3, 0, 4, 6, 5]) (he.comp (by decide)) hm hfloor
            hrotCCW hrotQ hrotP bdQ'
            (by
              change sig C A Q < 0
              rw [n7_sig_reverse]
              linarith [acQ]) bdP
            (by
              change 0 < sig C A P
              rw [n7_sig_reverse]
              linarith [acP']) hCDE hBEA hDEA
          change 9 * m < (sig A B C + sig A C D) + sig D E A
          change 9 * m < (sig B C D + sig B D A) + sig D E A at hc
          have hBDA : sig B D A = sig D A B := n7_sig_rotate B D A
          linarith only [hc, hdiagSum, hBDA]
      · have bdP' : sig B D P < 0 :=
          lt_of_le_of_ne (le_of_not_gt bdP) bdPne
        by_cases bdQ : 0 < sig B D Q
        · exact crossedQuad_lastEar_strict w m e he hm hfloor
            ⟨hABC, hABD, hACD, hBCD⟩
            ⟨hABP, hBCP, hCDP, hDAP⟩
            ⟨hABQ, hBCQ, hCDQ, hDAQ⟩
            acP' bdP' acQ bdQ hABE hCDE hDEA
        · have bdQ' : sig B D Q < 0 :=
            lt_of_le_of_ne (le_of_not_gt bdQ) bdQne
          have pBCD := inTriStrict_of_orientations hBCD hBCP hCDP
            (by rw [n7_sig_reverse]; linarith)
          have qBCD := inTriStrict_of_orientations hBCD hBCQ hCDQ
            (by rw [n7_sig_reverse]; linarith)
          have ht := two w m (e ∘ ![1, 2, 3, 5, 6])
            (he.comp (by decide)) hm hfloor hBCD pBCD qBCD
          change (4 + 2 * Real.sqrt 3) * m ≤ sig B C D at ht
          change 9 * m < (sig A B C + sig A C D) + sig D E A
          linarith [hdiagSum]
    · have acQ' : sig A C Q < 0 :=
        lt_of_le_of_ne (le_of_not_gt acQ) acQne
      have pABC := inTriStrict_of_orientations hABC hABP hBCP
        (by rw [n7_sig_reverse]; linarith)
      have qABC := inTriStrict_of_orientations hABC hABQ hBCQ
        (by rw [n7_sig_reverse]; linarith)
      have ht := two w m (e ∘ ![0, 1, 2, 5, 6])
        (he.comp (by decide)) hm hfloor hABC pABC qABC
      change (4 + 2 * Real.sqrt 3) * m ≤ sig A B C at ht
      change 9 * m < (sig A B C + sig A C D) + sig D E A
      linarith

end HeilbronnChallenge.N7Upper
