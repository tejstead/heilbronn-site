import Mathlib

/-!
# A compact scalar closure for the hard hull-five `3 + 0 + 0` sign cell

This file contains only the normalized area algebra.  Every selected triangle
has magnitude at least `2`; the geometric adapter is responsible for supplying
the fan decompositions and the two cleared cross-triangle inequalities.
-/

namespace Heilbronn8.TriHull

set_option maxHeartbeats 0

/-- The rational two-variable estimate used twice in the hard sign cell. -/
lemma hullFive300_pair_sum_gt
    {r s : ℝ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hproduct : 4 + (4 / 5 : ℝ) * r < s * (r - 2)) :
    15 / 2 < r + s := by
  by_contra hnot
  have hrs : r + s ≤ 15 / 2 := le_of_not_gt hnot
  let X := r - 2
  let Y := s - 4 / 5
  have hX : 0 ≤ X := by
    dsimp [X]
    linarith
  have hY : 0 ≤ Y := by
    dsimp [Y]
    linarith
  have hXY : 28 / 5 < X * Y := by
    dsimp [X, Y]
    nlinarith
  have hsum : X + Y ≤ 47 / 10 := by
    dsimp [X, Y]
    linarith
  have hsum0 : 0 ≤ X + Y := add_nonneg hX hY
  have hcap0 : 0 ≤ 47 / 10 - (X + Y) := sub_nonneg.mpr hsum
  have hplus0 : 0 ≤ 47 / 10 + (X + Y) := by linarith
  have hcapProduct := mul_nonneg hcap0 hplus0
  have hsquare := sq_nonneg (X - Y)
  nlinarith

/-- Normalized closure of the hard six-sign central `3 + 0 + 0` cell.

The variables are doubled areas after rescaling the minimum selected-triangle
magnitude to `2`.  In the intended geometry

* `A = [PBC] = a + b + c` and `B = [PCA] = d + e + f`;
* `g = [PAB]`;
* `u,v,k,l` are the four `P`-fan pieces of the pentagon;
* `delta = -[QPX]` and `tau = [RPD]`.

The last two hypotheses are the cleared `AXR` and `-BDQ` area floors.  The
proof is division-free and uses only rational polynomial inequalities.
-/
theorem hullFive300_six_sign_scalar
    {A B a b c d e f g x y z w delta tau u v k l H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hdelta : 2 ≤ delta) (htau : 2 ≤ tau)
    (hv : 2 ≤ v) (hk : 2 ≤ k)
    (hA : A = a + b + c) (hB : B = d + e + f)
    (hu : u = a + x + delta) (hvDef : v = b + y - delta)
    (hkDef : k = d + z - tau) (hl : l = e + w + tau)
    (hH : H = u + v + k + l + g)
    (hAPQ : 2 * A ≤ a * B - b * g)
    (hBPR : 2 * B ≤ e * A - d * g)
    (hfanQ : b * u - a * v = A * delta)
    (hfanR : d * l - e * k = B * tau)
    (hAXR :
      2 * A * B ≤
        A * e * (B + v) - (B - d) * (B * u - g * v))
    (hBDQ :
      2 * A * B ≤
        a * B * (A + k) - (A - b) * (A * l - g * k)) :
    25 ≤ H := by
  have hA6 : 6 ≤ A := by rw [hA]; linarith
  have hB6 : 6 ≤ B := by rw [hB]; linarith
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA6
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB6
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hu6 : 6 ≤ u := by rw [hu]; linarith
  have hl6 : 6 ≤ l := by rw [hl]; linarith
  have hHexpanded : H = a + b + d + e + x + y + z + w + g := by
    rw [hH, hu, hvDef, hkDef, hl]
    ring

  let D1 := B * u - g * v
  have hD1Identity :
      b * D1 = v * (a * B - b * g) + A * B * delta := by
    calc
      b * D1 = B * (b * u - a * v) + v * (a * B - b * g) := by
        dsimp [D1]
        ring
      _ = B * (A * delta) + v * (a * B - b * g) := by rw [hfanQ]
      _ = v * (a * B - b * g) + A * B * delta := by ring
  have hAPQscaled : 0 ≤ v * ((a * B - b * g) - 2 * A) :=
    mul_nonneg (le_trans (by norm_num) hv) (sub_nonneg.mpr hAPQ)
  have hdeltaScaled : 0 ≤ A * B * (delta - 2) :=
    mul_nonneg (mul_nonneg hApos.le hBpos.le) (sub_nonneg.mpr hdelta)
  have hD1lower : 2 * A * (B + v) ≤ b * D1 := by
    rw [hD1Identity]
    nlinarith
  have hBminus : B - d = e + f := by rw [hB]; ring
  have hBminus0 : 0 ≤ B - d := by rw [hBminus]; linarith
  have hD1multiplied := mul_le_mul_of_nonneg_right hD1lower hBminus0
  have hAXR' :
      2 * A * B ≤ A * e * (B + v) - (B - d) * D1 := by
    simpa [D1] using hAXR
  have hAXRmultiplied := mul_le_mul_of_nonneg_left hAXR' hbpos.le
  rw [hBminus] at hD1multiplied hAXRmultiplied
  have hIpre :
      A * (2 * b * B) ≤ A * ((e * (b - 2) - 2 * f) * (B + v)) := by
    nlinarith
  have hI :
      2 * b * B ≤ (e * (b - 2) - 2 * f) * (B + v) :=
    le_of_mul_le_mul_left hIpre hApos

  let D2 := A * l - g * k
  have hD2Identity :
      d * D2 = k * (e * A - d * g) + A * B * tau := by
    calc
      d * D2 = A * (d * l - e * k) + k * (e * A - d * g) := by
        dsimp [D2]
        ring
      _ = A * (B * tau) + k * (e * A - d * g) := by rw [hfanR]
      _ = k * (e * A - d * g) + A * B * tau := by ring
  have hBPRscaled : 0 ≤ k * ((e * A - d * g) - 2 * B) :=
    mul_nonneg (le_trans (by norm_num) hk) (sub_nonneg.mpr hBPR)
  have htauScaled : 0 ≤ A * B * (tau - 2) :=
    mul_nonneg (mul_nonneg hApos.le hBpos.le) (sub_nonneg.mpr htau)
  have hD2lower : 2 * B * (A + k) ≤ d * D2 := by
    rw [hD2Identity]
    nlinarith
  have hAminus : A - b = a + c := by rw [hA]; ring
  have hAminus0 : 0 ≤ A - b := by rw [hAminus]; linarith
  have hD2multiplied := mul_le_mul_of_nonneg_right hD2lower hAminus0
  have hBDQ' :
      2 * A * B ≤ a * B * (A + k) - (A - b) * D2 := by
    simpa [D2] using hBDQ
  have hBDQmultiplied := mul_le_mul_of_nonneg_left hBDQ' hdpos.le
  rw [hAminus] at hD2multiplied hBDQmultiplied
  have hIIpre :
      B * (2 * d * A) ≤ B * ((a * (d - 2) - 2 * c) * (A + k)) := by
    nlinarith
  have hII :
      2 * d * A ≤ (a * (d - 2) - 2 * c) * (A + k) :=
    le_of_mul_le_mul_left hIIpre hBpos

  by_contra hnot
  have hHlt : H < 25 := lt_of_not_ge hnot
  have hv9 : v < 9 := by nlinarith [hH, hu6, hl6, hk, hg]
  have hk9 : k < 9 := by nlinarith [hH, hu6, hl6, hv, hg]

  have hbe : 4 + (4 / 5 : ℝ) * b < e * (b - 2) := by
    by_contra hnotProduct
    have hfactor : e * (b - 2) - 2 * f ≤ (4 / 5 : ℝ) * b := by
      have := le_of_not_gt hnotProduct
      nlinarith
    have hsum0 : 0 ≤ B + v := by linarith
    have hupper := mul_le_mul_of_nonneg_right hfactor hsum0
    have hchain := hI.trans hupper
    have hratio : 2 * B ≤ (4 / 5 : ℝ) * (B + v) := by
      refine le_of_mul_le_mul_left ?_ hbpos
      convert hchain using 1 <;> ring
    nlinarith

  have hda : 4 + (4 / 5 : ℝ) * d < a * (d - 2) := by
    by_contra hnotProduct
    have hfactor : a * (d - 2) - 2 * c ≤ (4 / 5 : ℝ) * d := by
      have := le_of_not_gt hnotProduct
      nlinarith
    have hsum0 : 0 ≤ A + k := by linarith
    have hupper := mul_le_mul_of_nonneg_right hfactor hsum0
    have hchain := hII.trans hupper
    have hratio : 2 * A ≤ (4 / 5 : ℝ) * (A + k) := by
      refine le_of_mul_le_mul_left ?_ hdpos
      convert hchain using 1 <;> ring
    nlinarith

  have hbeSum : 15 / 2 < b + e :=
    hullFive300_pair_sum_gt hb he hbe
  have hdaSum : 15 / 2 < d + a :=
    hullFive300_pair_sum_gt hd ha hda
  nlinarith [hHexpanded]

end Heilbronn8.TriHull
