import Heilbronn8.TriHull.HullFive300UniversalScalar
import Heilbronn8.TriHull.HullFive300UniversalPMPartial

set_option maxHeartbeats 0

/-!
# A complete rational closure of the `+++- / ++-+` outer orbit

The fourth outer sign is not needed.  The already-proved `AQR ≤ e` branch is
combined with a new `e < AQR` argument.  The latter first forces
`b + e > 15 / 2`, then uses a compact four-variable polynomial certificate to
force `a + d + x + w ≥ 23 / 2`.

Everything in this file is division-free after clearing the displayed rational
constants.  In particular, it does not use the invalid sibling-cover module.
-/

namespace Heilbronn8.TriHull

/-- The polynomial certificate behind the four-atom estimate.

Here `A = a - 2`, `u = d - 2`, and `v = w - 2`.  The cap
`A + u + v ≤ 7 / 2` is what remains after assuming
`a + d + w + x < 23 / 2` and using `x ≥ 2`.
-/
lemma hullFive300_four_atom_certificate
    {A u v : ℝ}
    (hA : 0 ≤ A) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcap : A + u + v ≤ 7 / 2) :
    (11 / 2 - A - (u + v)) *
        ((A + 2) * (2 + 2 * u + v + u * v / 2) - 4) ≤
      8 * (A + 4) := by
  let s : ℝ := u + v
  let q : ℝ := 11 / 2 - A - s
  let F : ℝ := 2 + 2 * u + v + u * v / 2
  let M : ℝ := (A + 2) * F - 4
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith
  have hAs : A + s ≤ 7 / 2 := by
    dsimp [s]
    linarith
  have hq2 : 2 ≤ q := by
    dsimp [q]
    linarith
  have hA2 : 0 ≤ A + 2 := by linarith
  change q * M ≤ 8 * (A + 4)

  by_cases hsTwo : s ≤ 2
  · have huTwo : u ≤ 2 := by
      dsimp [s] at hsTwo
      linarith
    have huv : u * v ≤ 2 * v :=
      mul_le_mul_of_nonneg_right huTwo hv
    have hFupper : F ≤ 2 + 2 * s := by
      dsimp [F, s]
      nlinarith
    let G : ℝ := A + (A + 2) * s
    have hMupper : M ≤ 2 * G := by
      have hscaled := mul_le_mul_of_nonneg_left hFupper hA2
      dsimp [M, G]
      nlinarith

    have hqG : q * G ≤ 4 * A + 16 := by
      let C : ℝ := 3 / 2 + (5 / 2) * s - s ^ 2
      have hexpand :
          q * G - 4 * A =
            (11 * s - 2 * s ^ 2) + C * A - (1 + s) * A ^ 2 := by
        dsimp [q, G, C]
        ring
      by_cases hsOne : s ≤ 1
      · have hbaseFactor : 0 ≤ (1 - s) * (9 - 2 * s) := by
          exact mul_nonneg (sub_nonneg.mpr hsOne) (by linarith)
        have hbase : 11 * s - 2 * s ^ 2 ≤ 9 := by
          nlinarith
        have hCFactor : 0 ≤ (1 - s) * (3 / 2 - s) := by
          exact mul_nonneg (sub_nonneg.mpr hsOne) (by linarith)
        have hC : C ≤ 3 := by
          dsimp [C]
          nlinarith
        have hCA : C * A ≤ 3 * A :=
          mul_le_mul_of_nonneg_right hC hA
        have hsA : 0 ≤ s * A ^ 2 :=
          mul_nonneg hs0 (sq_nonneg A)
        have hquad : C * A - (1 + s) * A ^ 2 ≤ 9 / 4 := by
          nlinarith [sq_nonneg (2 * A - 3)]
        nlinarith
      · have hsOne' : 1 < s := lt_of_not_ge hsOne
        have hbaseFactor : 0 ≤ (2 - s) * (7 - 2 * s) := by
          exact mul_nonneg (sub_nonneg.mpr hsTwo) (by linarith)
        have hbase : 11 * s - 2 * s ^ 2 ≤ 14 := by
          nlinarith
        have hC : C ≤ 4 := by
          dsimp [C]
          nlinarith [sq_nonneg (2 * s - 5 / 2)]
        have hCA : C * A ≤ 4 * A :=
          mul_le_mul_of_nonneg_right hC hA
        have hsA : 2 * A ^ 2 ≤ (1 + s) * A ^ 2 := by
          have := mul_le_mul_of_nonneg_right
            (show (2 : ℝ) ≤ 1 + s by linarith) (sq_nonneg A)
          nlinarith
        have hquad : C * A - (1 + s) * A ^ 2 ≤ 2 := by
          nlinarith [sq_nonneg (A - 1)]
        nlinarith

    have hq0 : 0 ≤ q := by linarith
    have hqM := mul_le_mul_of_nonneg_left hMupper hq0
    nlinarith

  · have hsTwo' : 2 < s := lt_of_not_ge hsTwo
    let h : ℝ := 7 / 2 - s
    have hh0 : 0 ≤ h := by
      dsimp [h]
      linarith
    have hhCap : h ≤ 3 / 2 := by
      dsimp [h]
      linarith
    have hAle : A ≤ h := by
      dsimp [h]
      linarith
    let J : ℝ := (297 - 76 * h + 4 * h ^ 2) / 32
    have hJF : J - F = (2 * u - (s + 2)) ^ 2 / 8 := by
      dsimp [J, F, h, s]
      ring
    have hFupper : F ≤ J := by
      nlinarith [sq_nonneg (2 * u - (s + 2))]
    have hMupper : M ≤ (A + 2) * J - 4 := by
      have hscaled := mul_le_mul_of_nonneg_left hFupper hA2
      dsimp [M]
      nlinarith
    have hqRewrite : q = 2 + h - A := by
      dsimp [q, h]
      ring
    have hq0 : 0 ≤ q := by linarith
    let B0 : ℝ := (2 + h) * (2 * J - 4)
    let C : ℝ := h * J - 4
    have hexpand :
        q * ((A + 2) * J - 4) - 8 * A =
          B0 + C * A - J * A ^ 2 := by
      rw [hqRewrite]
      dsimp [B0, C]
      ring

    by_cases hhOne : h ≤ 1
    · have hfirst : 0 ≤ 68 * h ^ 2 - 85 * h + 30 := by
        nlinarith [sq_nonneg (136 * h - 85)]
      have hOnePlus : 0 ≤ 1 + h := by linarith
      have hOneMinusSq : 0 ≤ 1 - h ^ 2 := by
        have hfactor := mul_nonneg (sub_nonneg.mpr hhOne) hOnePlus
        nlinarith
      have hsecond : 0 ≤ 4 * h * (1 - h ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) hh0) hOneMinusSq
      have hBidentity :
          16 * (31 - B0) =
            (68 * h ^ 2 - 85 * h + 30) + 4 * h * (1 - h ^ 2) := by
        dsimp [B0, J]
        ring
      have hB0 : B0 ≤ 31 := by nlinarith

      have hJfactor : 0 ≤ (1 - h) * (72 - 4 * h) :=
        mul_nonneg (sub_nonneg.mpr hhOne) (by linarith)
      have hJidentity :
          32 * (J - 7) = (1 - h) * (72 - 4 * h) + 1 := by
        dsimp [J]
        ring
      have hJ : 7 ≤ J := by nlinarith

      have hQpositive : 0 ≤ 4 * h ^ 2 - 72 * h + 225 := by
        nlinarith [sq_nonneg h]
      have hCfactor : 0 ≤ (1 - h) * (4 * h ^ 2 - 72 * h + 225) :=
        mul_nonneg (sub_nonneg.mpr hhOne) hQpositive
      have hCidentity :
          32 * (8 - h * J) =
            31 + (1 - h) * (4 * h ^ 2 - 72 * h + 225) := by
        dsimp [J]
        ring
      have hC : C ≤ 4 := by
        dsimp [C]
        nlinarith

      have hCA : C * A ≤ 4 * A :=
        mul_le_mul_of_nonneg_right hC hA
      have hJA : 7 * A ^ 2 ≤ J * A ^ 2 :=
        mul_le_mul_of_nonneg_right hJ (sq_nonneg A)
      have hterm : C * A - J * A ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (7 * A - 2)]
      have hupper :
          q * ((A + 2) * J - 4) ≤ 8 * (A + 4) := by
        nlinarith [hexpand]
      have hqM := mul_le_mul_of_nonneg_left hMupper hq0
      nlinarith

    · have hhOne' : 1 < h := lt_of_not_ge hhOne
      have hhLinear : 0 ≤ -4 * h ^ 2 + 64 * h - 17 := by
        have hhSquareCap : h ^ 2 ≤ (3 / 2) * h := by
          have hfactor := mul_nonneg hh0 (sub_nonneg.mpr hhCap)
          nlinarith
        nlinarith
      have hBfactor : 0 ≤ (h - 1) * (-4 * h ^ 2 + 64 * h - 17) :=
        mul_nonneg (by linarith) hhLinear
      have hBidentity :
          16 * (61 / 2 - B0) =
            5 + (h - 1) * (-4 * h ^ 2 + 64 * h - 17) := by
        dsimp [B0, J]
        ring
      have hB0 : B0 ≤ 61 / 2 := by nlinarith

      have hJfactor : 0 ≤ (3 - 2 * h) * (35 - 2 * h) :=
        mul_nonneg (by linarith) (by linarith)
      have hJidentity :
          32 * (J - 6) = (3 - 2 * h) * (35 - 2 * h) := by
        dsimp [J]
        ring
      have hJ : 6 ≤ J := by nlinarith

      have hQpositive : 0 ≤ 2 * h ^ 2 - 35 * h + 96 := by
        nlinarith [sq_nonneg h]
      have hCfactor : 0 ≤ (3 - 2 * h) * (2 * h ^ 2 - 35 * h + 96) :=
        mul_nonneg (by linarith) hQpositive
      have hCidentity :
          32 * (9 - h * J) =
            (3 - 2 * h) * (2 * h ^ 2 - 35 * h + 96) := by
        dsimp [J]
        ring
      have hC : C ≤ 5 := by
        dsimp [C]
        nlinarith

      have hCA : C * A ≤ 5 * A :=
        mul_le_mul_of_nonneg_right hC hA
      have hJA : 6 * A ^ 2 ≤ J * A ^ 2 :=
        mul_le_mul_of_nonneg_right hJ (sq_nonneg A)
      have hterm : C * A - J * A ^ 2 ≤ 3 / 2 := by
        nlinarith [sq_nonneg (12 * A - 5)]
      have hupper :
          q * ((A + 2) * J - 4) ≤ 8 * (A + 4) := by
        nlinarith [hexpand]
      have hqM := mul_le_mul_of_nonneg_left hMupper hq0
      nlinarith

/-- A division-free four-atom consequence used in the positive-`AQR-e`
branch. -/
lemma hullFive300_four_atom_sum
    {a d w x : ℝ}
    (ha : 2 ≤ a) (hd : 2 ≤ d) (hw : 2 ≤ w) (hx : 2 ≤ x)
    (hproduct :
      8 * (a + 2) ≤ x * (a * (d - 2 + d * w / 2) - 4)) :
    23 / 2 ≤ a + d + w + x := by
  by_contra hnot
  have hsum : a + d + w + x < 23 / 2 := lt_of_not_ge hnot
  let A : ℝ := a - 2
  let u : ℝ := d - 2
  let v : ℝ := w - 2
  let F : ℝ := 2 + 2 * u + v + u * v / 2
  let M : ℝ := (A + 2) * F - 4
  let q : ℝ := 11 / 2 - A - (u + v)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hcap : A + u + v ≤ 7 / 2 := by
    dsimp [A, u, v]
    linarith
  have hxq : x < q := by
    dsimp [q, A, u, v]
    linarith
  have hproduct' : 8 * (A + 4) ≤ x * M := by
    dsimp [M, F, A, u, v]
    convert hproduct using 1 <;> ring
  have hMpos : 0 < M := by
    by_contra hMnot
    have hMnonpos : M ≤ 0 := le_of_not_gt hMnot
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx
    have hxM := mul_nonpos_of_nonneg_of_nonpos hx0 hMnonpos
    nlinarith
  have hcert := hullFive300_four_atom_certificate hA hu hv hcap
  have hcert' : q * M ≤ 8 * (A + 4) := by
    simpa [q, M, F] using hcert
  have hxMlt : x * M < q * M :=
    mul_lt_mul_of_pos_right hxq hMpos
  nlinarith

/-- The `delta,tau,AXR > 0` branch with `e < AQR` forces the normalized
target.  As in the complementary branch, the fourth outer sign is unused. -/
theorem hullFive300_ppp_aqr_gt_e_scalar
    {alpha beta a b c d e f g x y z w p R delta tau axr u v earF H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hp : 2 ≤ p) (hR : 2 ≤ R)
    (hdelta : 2 ≤ delta) (htau : 2 ≤ tau) (haxr : 2 ≤ axr)
    (hv : 2 ≤ v) (hearF : 2 ≤ earF)
    (hAlpha : alpha = a + b + c) (hBeta : beta = d + e + f)
    (hu : u = a + x + delta) (hvDef : v = b + y - delta)
    (hearFDef : earF = z + w - f)
    (hH : H = a + b + d + e + x + y + z + w + g)
    (hAPQ : 2 * alpha ≤ a * beta - b * g)
    (hCentral : beta * (R - e) = b * e - p * (e + f))
    (hAXRrow :
      b * axr = b * R + y * (R - e) - delta * (R + f))
    (hfanQ : b * x = a * y + c * delta)
    (hfanR : d * w = e * z + f * tau)
    (hRgt : e < R) :
    25 ≤ H := by
  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have he0 : 0 ≤ e := le_trans (by norm_num) he
  have hf0 : 0 ≤ f := le_trans (by norm_num) hf
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv
  have hbeta6 : 6 ≤ beta := by rw [hBeta]; linarith
  have hbeta0 : 0 ≤ beta := le_trans (by norm_num) hbeta6
  have ht0 : 0 < R - e := by linarith

  let R0 : ℝ := e * (b - 2) - 2 * f
  have hep0 : 0 ≤ e + f := by linarith
  have hpScaled := mul_le_mul_of_nonneg_right hp hep0
  have htBound : beta * (R - e) ≤ R0 := by
    rw [hCentral]
    dsimp [R0]
    nlinarith
  have htProduct : 0 < beta * (R - e) :=
    mul_pos (lt_of_lt_of_le (by norm_num) hbeta6) ht0
  have hR0pos : 0 < R0 := lt_of_lt_of_le htProduct htBound

  have hrowRewrite :
      b * axr = v * (R - e) + b * e - delta * (e + f) := by
    rw [hAXRrow, hvDef]
    ring
  have hdeltaScaled := mul_le_mul_of_nonneg_right hdelta hep0
  have hrowUpper : b * axr ≤ v * (R - e) + R0 := by
    rw [hrowRewrite]
    dsimp [R0]
    nlinarith
  have haxrScaled := mul_le_mul_of_nonneg_left haxr hb0
  have hlocal : 2 * b ≤ v * (R - e) + R0 := by
    nlinarith
  have hlocalScaled := mul_le_mul_of_nonneg_left hlocal hbeta0
  have htScaled := mul_le_mul_of_nonneg_left htBound hv0
  have hhard : 2 * b * beta ≤ R0 * (beta + v) := by
    nlinarith

  have hu6 : 6 ≤ u := by rw [hu]; linarith
  have hbetaVIdentity : beta + v = H - (g + u + earF) := by
    rw [hBeta, hvDef, hu, hearFDef, hH]
    ring
  have hbetaVlt : beta + v < 15 := by
    rw [hbetaVIdentity]
    linarith
  have hupper := mul_lt_mul_of_pos_left hbetaVlt hR0pos
  have hhardStrict : 2 * b * beta < 15 * R0 :=
    lt_of_le_of_lt hhard (by nlinarith)
  have hbetaLower : e + 4 ≤ beta := by rw [hBeta]; linarith
  have hbetaScaled := mul_le_mul_of_nonneg_left hbetaLower (by nlinarith : 0 ≤ 2 * b)
  have hpoly : 60 < 13 * b * e - 30 * e - 8 * b := by
    dsimp [R0] at hhardStrict
    nlinarith

  let B : ℝ := b - 2
  let E : ℝ := e - 2
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hE0 : 0 ≤ E := by dsimp [E]; linarith
  have hpolyShift : 84 < 13 * B * E + 18 * B - 4 * E := by
    dsimp [B, E]
    nlinarith
  have hbeSum : 15 / 2 < b + e := by
    by_contra hsumNot
    have hsum : B + E ≤ 7 / 2 := by
      have := le_of_not_gt hsumNot
      dsimp [B, E]
      linarith
    have hEcap : E ≤ 7 / 2 - B := by linarith
    have hBE := mul_le_mul_of_nonneg_left hEcap (by positivity : 0 ≤ 13 * B)
    have hquadratic : B * (127 / 2 - 13 * B) ≤ 78 := by
      nlinarith [sq_nonneg (52 * B - 127)]
    have hupperPoly : 13 * B * E + 18 * B - 4 * E ≤ 78 := by
      nlinarith
    nlinarith

  have hfanRLeft : 2 * e ≤ e * z := by
    have hmul := mul_le_mul_of_nonneg_left hz he0
    nlinarith
  have hfanRRight : 2 * f ≤ f * tau := by
    have hmul := mul_le_mul_of_nonneg_left htau hf0
    nlinarith
  have hEF : 2 * (e + f) ≤ d * w := by
    rw [hfanR]
    nlinarith

  have hbg : 2 * b ≤ b * g := by
    have hmul := mul_le_mul_of_nonneg_left hg hb0
    nlinarith
  have hpCleared : 4 * b + 4 ≤ a * (d + e + f - 2) := by
    rw [hAlpha, hBeta] at hAPQ
    nlinarith
  have hEFhalf : e + f ≤ d * w / 2 := by nlinarith
  have hpUpper := mul_le_mul_of_nonneg_left hEFhalf ha0
  let M : ℝ := a * (d - 2 + d * w / 2) - 4
  have hM : 4 * b ≤ M := by
    dsimp [M]
    nlinarith

  have hay : 2 * a ≤ a * y := by
    have hmul := mul_le_mul_of_nonneg_left hy ha0
    nlinarith
  have hcdelta : 4 ≤ c * delta := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hdelta)]
  have hbx : 2 * (a + 2) ≤ b * x := by
    rw [hfanQ]
    nlinarith
  have hMx := mul_le_mul_of_nonneg_right hM hx0
  have hbxScaled := mul_le_mul_of_nonneg_left hbx (by norm_num : (0 : ℝ) ≤ 4)
  have hfourProduct : 8 * (a + 2) ≤ x * M := by
    nlinarith
  have hfour : 23 / 2 ≤ a + d + w + x := by
    apply hullFive300_four_atom_sum ha hd hw hx
    simpa [M] using hfourProduct
  nlinarith [hH]

/-- Complete scalar interface for the three positive outer signs.  It combines
the two signs of `AQR - e`; no assumption on the fourth outer sign appears. -/
theorem hullFive300_ppp_scalar
    {alpha beta a b c d e f g x y z w p R delta tau axr u v earF H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hp : 2 ≤ p) (hR : 2 ≤ R)
    (hdelta : 2 ≤ delta) (htau : 2 ≤ tau) (haxr : 2 ≤ axr)
    (hv : 2 ≤ v) (hearF : 2 ≤ earF)
    (hAlpha : alpha = a + b + c) (hBeta : beta = d + e + f)
    (hu : u = a + x + delta) (hvDef : v = b + y - delta)
    (hearFDef : earF = z + w - f)
    (hH : H = a + b + d + e + x + y + z + w + g)
    (hAPQ : 2 * alpha ≤ a * beta - b * g)
    (hCentral : beta * (R - e) = b * e - p * (e + f))
    (hAXRrow :
      b * axr = b * R + y * (R - e) - delta * (R + f))
    (hfanQ : b * x = a * y + c * delta)
    (hfanR : d * w = e * z + f * tau) :
    25 ≤ H := by
  by_cases hRle : R ≤ e
  · have hearR : f * tau = d * w - e * z := by
      nlinarith [hfanR]
    exact hullFive300_ppp_aqr_le_e_scalar
      ha hb hd he hf hg hx hy hz hw hR hdelta htau haxr hRle
      hAXRrow hearR hH
  · exact hullFive300_ppp_aqr_gt_e_scalar
      ha hb hc hd he hf hg hx hy hz hw hp hR hdelta htau haxr hv hearF
      hAlpha hBeta hu hvDef hearFDef hH hAPQ hCentral hAXRrow hfanQ hfanR
      (lt_of_not_ge hRle)

end Heilbronn8.TriHull
